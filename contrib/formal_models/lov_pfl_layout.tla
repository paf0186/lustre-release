---------------------------- MODULE lov_pfl_layout ----------------------------
(*
 * PlusCal/TLA+ model of LOV/LOD PFL layout change and pool membership races.
 *
 * PFL (Progressive File Layout) allows files to have multiple layout
 * components that activate as the file grows.  Layout changes (component
 * add/del/mirror) must be atomic with respect to I/O.  Pool membership
 * changes can invalidate layout component targets mid-I/O.
 *
 * Models three concurrent actors on a file with 2 PFL components:
 *   - Writer:       writes data, activating PFL components as needed.
 *                    Takes lo_type_guard (shared) briefly to read layout
 *                    and increment lo_active_ios, then releases shared
 *                    lock. Actual write happens with only active_ios > 0
 *                    protecting it (no lock held).
 *   - LayoutChanger: adds/removes a PFL component (e.g. MDS-driven
 *                    instantiation).  Takes lo_type_guard (exclusive),
 *                    waits for lo_active_ios == 0, bumps layout_gen.
 *   - PoolChanger:  removes an OST from the pool that backs a component,
 *                    changing pool membership without layout lock.
 *
 * Real code flow (from lov_object.c, lov_io.c, llite/file.c):
 *
 *   Writer I/O:
 *     1. lov_conf_freeze()         -- down_read(&lo_type_guard)
 *     2. lov_io_init_composite()   -- capture layout_gen, select component
 *     3. atomic_inc(&lo_active_ios)
 *     4. lov_conf_thaw()           -- up_read(&lo_type_guard)
 *     5. cl_io_loop()              -- actual write (NO lock held)
 *     6. atomic_dec(&lo_active_ios)
 *
 *   Layout change (lov_conf_set):
 *     1. set_bit(LO_LAYOUT_INVALID)  -- lock-free (blocking AST)
 *     2. lov_conf_lock()              -- down_write(&lo_type_guard)
 *     3. lov_layout_wait()            -- wait for lo_active_ios == 0
 *     4. lov_layout_change()          -- modify layout, bump gen
 *     5. clear LO_LAYOUT_INVALID
 *     6. lov_conf_unlock()            -- up_write(&lo_type_guard)
 *
 *   Pool change (lu_tgt_pool_remove):
 *     1. down_write(&pool->op_rw_sem) -- pool-level lock only
 *     2. remove OST from pool->op_array
 *     3. up_write(&pool->op_rw_sem)
 *     (No interaction with lo_type_guard or lo_active_ios)
 *
 * Known bugs modeled:
 *
 *   LU-9839: lo_active_ios assertion failure during layout change.
 *            lov_layout_change() asserts lo_active_ios == 0 before proceeding,
 *            but if the layout changer skips the drain wait (InjectBug9839),
 *            the assertion fires because I/O is still in flight.
 *            Fix: always drain lo_active_ios before layout change.
 *
 *   LU-18435: Layout generation reset on replay.
 *            When a PFL layout creation is replayed, the MDS resets
 *            layout_gen to 0 instead of preserving/incrementing it.
 *            This violates the monotonically-increasing invariant and
 *            causes the client to loop trying to refresh the layout
 *            (it expects gen to increase, but it goes backwards).
 *            Fix: layout_gen must always increase (never reset to 0).
 *
 * Novel race explored:
 *   Pool membership change during active I/O: an admin removes an OST
 *   from the pool while I/O is targeting a component backed by that OST.
 *   The I/O proceeds to write to a target that is no longer a pool member,
 *   violating pool placement semantics.  The pool lock (op_rw_sem) does
 *   not coordinate with lo_type_guard or lo_active_ios.
 *
 * Source (lustre-release master 47638add78):
 *   lustre/lov/lov_object.c
 *     lov_conf_freeze/thaw   1253-1267 down_read/up_read(lo_type_guard)
 *     LOV_2DISPATCH_MAYLOCK  1269-1281 freeze around llo_io_init
 *     lov_conf_lock/unlock   1295-1311 down_write/up_write + lo_owner
 *     lov_layout_wait        1313-1326 wait_event lo_active_ios == 0
 *     lov_layout_change      1328-1397 LASSERT(lo_active_ios == 0) 1368
 *     lov_conf_set           1441-1537 OBJECT_CONF_INVALIDATE: lock-free
 *                                     set_bit(LO_LAYOUT_INVALID) 1460-1462;
 *                                     OBJECT_CONF_WAIT: lov_layout_wait
 *                                     1466-1472; old-gen skip 1487-1499;
 *                                     -EBUSY if lo_active_ios > 0
 *                                     1512-1515; layout_change 1521-1525
 *     lov_io_init            1583-1599 MAYLOCK unless CIT_MISC+ignore
 *   lustre/lov/lov_io.c
 *     lov_io_mirror_init      467-     ci_layout_version captured 491-492
 *     lov_io_fini             ~900-918 atomic_dec_and_test(lo_active_ios)
 *                                     + wake_up 914-917
 *     lov_io_init_composite  2174-2197 atomic_inc(lo_active_ios) 2192
 *                                     (LU-9839 condition)
 *   lustre/lov/lov_cl_internal.h
 *     LO_LAYOUT_INVALID 223, lo_type_guard 250, lo_active_ios 263
 *   lustre/llite/file.c
 *     ll_layout_conf         6800-     cl_conf_set wrapper
 *     ll_layout_lock_set     6927-     OBJECT_CONF_SET 6975; on -EBUSY
 *                                     OBJECT_CONF_WAIT 6996 then retry
 *     ll_layout_refresh      7097-
 *   lustre/llite/namei.c
 *     ll_md_blocking_ast      ~307     OBJECT_CONF_INVALIDATE (BL AST)
 *   lustre/obdclass/lu_tgt_pool.c
 *     lu_tgt_pool_remove      161-182  down_write(op_rw_sem) only
 *   lustre/lod/lod_qos.c
 *     lod_use_defined_striping ~2744/2754 ldo_layout_gen from the
 *                                     layout-specific field (LU-18435
 *                                     fix c66a7dea85)
 *
 * Validated against: lustre-release master 47638add78 (2026-09-06)
 * Validation notes:
 *   - Lock/counter protocol matches: lo_type_guard shared around IO
 *     init with atomic_inc(lo_active_ios) under it, exclusive for
 *     lov_conf_set, lo_active_ios drained by lov_layout_wait.
 *   - lov_conf_set itself never waits: with active IOs it sets
 *     LO_LAYOUT_INVALID and returns -EBUSY (1512-1515); the caller
 *     (ll_layout_lock_set) then issues OBJECT_CONF_WAIT, which drops
 *     and retakes lo_type_guard around lov_layout_wait, and retries.
 *     LC_DrainActiveIOs + LC_PerformChange collapse that WAIT+SET
 *     retry loop into one exclusive hold; that is conservative for
 *     the invariants checked here.
 *   - InjectBug9839 (skip the drain) is an abstraction of the real
 *     LU-9839 bug (5bc1dd825b): some CIT_MISC IOs incremented
 *     lo_active_ios without holding lo_type_guard, so the active_ios
 *     check in lov_conf_set could pass and a new IO could start
 *     before the LASSERT in lov_layout_change.  The model has no
 *     unlocked incrementer; the injection reproduces the same
 *     end state (layout change with active_ios > 0).
 *   - InjectBug18435 abstracts a server-side (lod) bug: the MDT
 *     returned a reset layout generation after replay.  The client
 *     side defense is the newgen < oldgen skip in lov_conf_set
 *     (1487-1499); the model's LayoutChanger stands in for the
 *     MDT-supplied layout.
 *   - io_hit_invalid is recorded but not used by any invariant; no
 *     IO-path code checks LO_LAYOUT_INVALID directly (lov_conf_set
 *     with coc_try returns -ERESTARTSYS instead).
 *)

EXTENDS Integers, TLC

CONSTANTS
    InjectBug9839,    \* TRUE = layout changer skips lo_active_ios drain
    InjectBug18435,   \* TRUE = layout change can reset gen to 0 (replay bug)
    NumComponents     \* Number of PFL components (2 for baseline)

ASSUME NumComponents \in 1..4
ASSUME InjectBug9839 \in BOOLEAN
ASSUME InjectBug18435 \in BOOLEAN

Comps == 1..NumComponents

(* --algorithm lov_pfl_layout

variables
    \* ---- PFL component state ----
    \* comp_active[c]: whether component c is initialized/active
    comp_active = [c \in Comps |-> IF c = 1 THEN TRUE ELSE FALSE],

    \* comp_pool_target[c]: whether the OST backing component c is in the pool
    comp_pool_target = [c \in Comps |-> TRUE],

    \* ---- Layout versioning ----
    layout_gen = 1,             \* Current layout generation (starts at 1)
    layout_invalid = FALSE,     \* LO_LAYOUT_INVALID flag (set lock-free by BL AST)

    \* ---- Concurrency control ----
    \* lo_type_guard: "free", "shared", or "exclusive"
    type_guard = "free",
    type_guard_readers = 0,     \* Number of shared holders
    active_ios = 0,             \* lo_active_ios counter

    \* ---- Writer state ----
    io_captured_gen = 0,        \* Writer's snapshot of layout_gen
    io_target_comp = 0,         \* Which component the writer is targeting
    io_hit_invalid = FALSE,     \* Writer detected layout_invalid during I/O

    \* ---- Violation trackers ----
    \* Set TRUE when writer writes to a component whose pool target was removed.
    wrote_to_removed_target = FALSE,
    \* Set TRUE when active_ios > 0 while layout change executes (LU-9839).
    layout_change_with_active_io = FALSE,
    \* Track layout_gen history for monotonicity checking
    prev_layout_gen = 0,
    gen_went_backwards = FALSE,

    \* ---- Per-process completion flags ----
    thread_done = [t \in {"writer", "layout_changer", "pool_changer"} |-> FALSE];

define
    TypeOK ==
        /\ \A c \in Comps: comp_active[c] \in BOOLEAN
        /\ \A c \in Comps: comp_pool_target[c] \in BOOLEAN
        /\ layout_gen \in Nat
        /\ layout_invalid \in BOOLEAN
        /\ type_guard \in {"free", "shared", "exclusive"}
        /\ type_guard_readers \in Nat
        /\ active_ios \in Nat
        /\ io_captured_gen \in Nat
        /\ io_target_comp \in 0..NumComponents

    \* INV-a: I/O never targets a component whose OST left the pool.
    \* If the writer completed an I/O to a component, that component's
    \* pool target must still be present.
    NoWriteToRemovedTarget == ~wrote_to_removed_target

    \* INV-b: Layout version monotonically increases.
    \* layout_gen must never decrease (LU-18435 violation).
    LayoutGenMonotonic == ~gen_went_backwards

    \* INV-c: No write to inactive component.
    \* The writer must only target active components.
    NoWriteToInactive ==
        (io_target_comp > 0 /\ io_target_comp \in Comps)
            => comp_active[io_target_comp]

    \* INV-d: Layout change must not proceed with active I/Os (LU-9839).
    NoLayoutChangeWithActiveIO == ~layout_change_with_active_io

end define;

\* ================================================================
\* Writer: ll_file_io_generic -> lov_io_init_composite -> I/O
\*
\* Models a single write I/O:
\* 1. Take lo_type_guard shared (lov_conf_freeze)
\* 2. Check layout_invalid, capture layout_gen, select component
\* 3. Increment lo_active_ios (under shared lock)
\* 4. Release lo_type_guard shared (lov_conf_thaw)
\* 5. Perform write (NO lock held, only active_ios protects)
\* 6. Decrement lo_active_ios
\*
\* The pool_changer can remove the target between steps 4 and 5.
\* The layout_changer is blocked by active_ios > 0 during step 5.
\* ================================================================
fair process WriterThread = "writer"
begin
W_AcquireShared:
    \* lov_conf_freeze: take lo_type_guard in shared mode.
    \* Must wait if exclusive holder (layout changer) has it.
    await type_guard /= "exclusive";
    type_guard := "shared" ||
    type_guard_readers := type_guard_readers + 1;

W_CheckInvalid:
    \* Check LO_LAYOUT_INVALID at I/O init time.
    \* If set, real code returns -ERESTARTSYS to retry.
    if layout_invalid then
        io_hit_invalid := TRUE;
    end if;

W_CaptureGen:
    \* lov_io_mirror_init: capture layout_gen into ci_layout_version.
    io_captured_gen := layout_gen;

W_SelectComponent:
    \* Select first active component to write to.
    \* In PFL, the writer targets the component covering its byte range.
    if comp_active[1] then
        io_target_comp := 1;
    elsif NumComponents >= 2 /\ comp_active[2] then
        io_target_comp := 2;
    else
        io_target_comp := 0;
    end if;

W_IncActiveIOs:
    \* Increment lo_active_ios while still holding shared lock.
    \* This ensures layout changer sees active_ios > 0 once it
    \* acquires the exclusive lock.
    active_ios := active_ios + 1;

W_ReleaseShared:
    \* lov_conf_thaw: release lo_type_guard shared.
    \* From here, the writer has NO lock -- only active_ios > 0.
    type_guard_readers := type_guard_readers - 1;
    if type_guard_readers = 0 then
        type_guard := "free";
    end if;

W_PerformWrite:
    \* The actual write operation (cl_io_loop). NO lock held.
    \* This is the window where pool_changer can have removed the OST.
    if io_target_comp > 0 /\ io_target_comp \in Comps then
        if ~comp_pool_target[io_target_comp] then
            wrote_to_removed_target := TRUE;
        end if;
    end if;

W_DecActiveIOs:
    \* Decrement lo_active_ios. Layout changer may now proceed.
    active_ios := active_ios - 1 ||
    io_target_comp := 0;

W_Done:
    thread_done["writer"] := TRUE;
end process;

\* ================================================================
\* LayoutChanger: lov_conf_set -> lov_layout_change
\*
\* Models a layout change that:
\* 1. Sets layout_invalid (blocking AST, lock-free)
\* 2. Takes lo_type_guard exclusive
\* 3. Waits for lo_active_ios == 0 (unless bug 9839 injected)
\* 4. Performs layout change (activate component 2, bump gen)
\* 5. Clears layout_invalid
\* 6. Releases lo_type_guard exclusive
\*
\* LU-9839 BUG: skipping the lo_active_ios drain allows the layout
\*   change to proceed while I/O is in flight.
\*
\* LU-18435 BUG: on replay, layout_gen can be reset to 0.
\* ================================================================
fair process LayoutChangerThread = "layout_changer"
begin
LC_Invalidate:
    \* Blocking AST callback: set LO_LAYOUT_INVALID (lock-free).
    \* This can race with the writer's W_CheckInvalid.
    layout_invalid := TRUE;

LC_AcquireExclusive:
    \* lov_conf_lock: take lo_type_guard in exclusive mode.
    \* Must wait for all shared holders to release.
    await type_guard = "free";
    type_guard := "exclusive";

LC_DrainActiveIOs:
    \* lov_layout_wait: wait for lo_active_ios == 0.
    \* LU-9839 BUG: skip the drain, proceed even with active I/Os.
    if InjectBug9839 then
        if active_ios > 0 then
            layout_change_with_active_io := TRUE;
        end if;
    else
        await active_ios = 0;
    end if;

LC_PerformChange:
    \* lov_layout_change: activate component 2, bump layout_gen.
    if NumComponents >= 2 then
        comp_active[2] := TRUE;
    end if;
    prev_layout_gen := layout_gen;
    if InjectBug18435 then
        \* BUG: replay resets layout_gen to 0 instead of incrementing.
        layout_gen := 0;
    else
        layout_gen := layout_gen + 1;
    end if;

LC_CheckMonotonic:
    \* Check if layout_gen went backwards (LU-18435 invariant).
    if layout_gen < prev_layout_gen then
        gen_went_backwards := TRUE;
    end if;

LC_ClearInvalid:
    \* Clear LO_LAYOUT_INVALID now that layout is updated.
    layout_invalid := FALSE;

LC_ReleaseExclusive:
    \* lov_conf_unlock: release lo_type_guard exclusive.
    type_guard := "free";

LC_Done:
    thread_done["layout_changer"] := TRUE;
end process;

\* ================================================================
\* PoolChanger: admin removes an OST from the pool
\*
\* Models a pool membership change via lu_tgt_pool_remove().
\* This takes pool->op_rw_sem in write mode but does NOT interact
\* with the layout lock (lo_type_guard) or lo_active_ios.
\*
\* The race: between the writer releasing shared lock (W_ReleaseShared)
\* and performing the write (W_PerformWrite), the pool changer can
\* remove the OST from the pool. The writer then writes to a target
\* no longer in the pool.
\* ================================================================
fair process PoolChangerThread = "pool_changer"
begin
PC_RemoveFromPool:
    \* Admin removes the OST backing component 1 from the pool.
    \* This happens without any coordination with the layout layer.
    comp_pool_target[1] := FALSE;

PC_Done:
    thread_done["pool_changer"] := TRUE;
end process;

end algorithm; *)

\* BEGIN TRANSLATION
VARIABLES comp_active, comp_pool_target, layout_gen, layout_invalid,
          type_guard, type_guard_readers, active_ios, io_captured_gen,
          io_target_comp, io_hit_invalid, wrote_to_removed_target,
          layout_change_with_active_io, prev_layout_gen,
          gen_went_backwards, thread_done, pc

(* define statement *)
TypeOK ==
    /\ \A c \in Comps: comp_active[c] \in BOOLEAN
    /\ \A c \in Comps: comp_pool_target[c] \in BOOLEAN
    /\ layout_gen \in Nat
    /\ layout_invalid \in BOOLEAN
    /\ type_guard \in {"free", "shared", "exclusive"}
    /\ type_guard_readers \in Nat
    /\ active_ios \in Nat
    /\ io_captured_gen \in Nat
    /\ io_target_comp \in 0..NumComponents

NoWriteToRemovedTarget == ~wrote_to_removed_target

LayoutGenMonotonic == ~gen_went_backwards

NoWriteToInactive ==
    (io_target_comp > 0 /\ io_target_comp \in Comps)
        => comp_active[io_target_comp]

NoLayoutChangeWithActiveIO == ~layout_change_with_active_io


vars == << comp_active, comp_pool_target, layout_gen, layout_invalid,
           type_guard, type_guard_readers, active_ios, io_captured_gen,
           io_target_comp, io_hit_invalid, wrote_to_removed_target,
           layout_change_with_active_io, prev_layout_gen,
           gen_went_backwards, thread_done, pc >>

ProcSet == {"writer"} \cup {"layout_changer"} \cup {"pool_changer"}

Init == (* Global variables *)
        /\ comp_active = [c \in Comps |-> IF c = 1 THEN TRUE ELSE FALSE]
        /\ comp_pool_target = [c \in Comps |-> TRUE]
        /\ layout_gen = 1
        /\ layout_invalid = FALSE
        /\ type_guard = "free"
        /\ type_guard_readers = 0
        /\ active_ios = 0
        /\ io_captured_gen = 0
        /\ io_target_comp = 0
        /\ io_hit_invalid = FALSE
        /\ wrote_to_removed_target = FALSE
        /\ layout_change_with_active_io = FALSE
        /\ prev_layout_gen = 0
        /\ gen_went_backwards = FALSE
        /\ thread_done = [t \in {"writer", "layout_changer", "pool_changer"} |-> FALSE]
        /\ pc = [self \in ProcSet |->
                    CASE self = "writer" -> "W_AcquireShared"
                      [] self = "layout_changer" -> "LC_Invalidate"
                      [] self = "pool_changer" -> "PC_RemoveFromPool"]

\* ---- Writer actions ----

W_AcquireShared == /\ pc["writer"] = "W_AcquireShared"
                   /\ type_guard /= "exclusive"
                   /\ type_guard' = "shared"
                   /\ type_guard_readers' = type_guard_readers + 1
                   /\ pc' = [pc EXCEPT !["writer"] = "W_CheckInvalid"]
                   /\ UNCHANGED << comp_active, comp_pool_target, layout_gen,
                                   layout_invalid, active_ios, io_captured_gen,
                                   io_target_comp, io_hit_invalid,
                                   wrote_to_removed_target, layout_change_with_active_io,
                                   prev_layout_gen, gen_went_backwards, thread_done >>

W_CheckInvalid == /\ pc["writer"] = "W_CheckInvalid"
                  /\ IF layout_invalid
                        THEN /\ io_hit_invalid' = TRUE
                        ELSE /\ UNCHANGED io_hit_invalid
                  /\ pc' = [pc EXCEPT !["writer"] = "W_CaptureGen"]
                  /\ UNCHANGED << comp_active, comp_pool_target, layout_gen,
                                  layout_invalid, type_guard, type_guard_readers,
                                  active_ios, io_captured_gen, io_target_comp,
                                  wrote_to_removed_target, layout_change_with_active_io,
                                  prev_layout_gen, gen_went_backwards, thread_done >>

W_CaptureGen == /\ pc["writer"] = "W_CaptureGen"
                /\ io_captured_gen' = layout_gen
                /\ pc' = [pc EXCEPT !["writer"] = "W_SelectComponent"]
                /\ UNCHANGED << comp_active, comp_pool_target, layout_gen,
                                layout_invalid, type_guard, type_guard_readers,
                                active_ios, io_target_comp, io_hit_invalid,
                                wrote_to_removed_target, layout_change_with_active_io,
                                prev_layout_gen, gen_went_backwards, thread_done >>

W_SelectComponent == /\ pc["writer"] = "W_SelectComponent"
                     /\ IF comp_active[1]
                           THEN /\ io_target_comp' = 1
                           ELSE /\ IF NumComponents >= 2 /\ comp_active[2]
                                      THEN /\ io_target_comp' = 2
                                      ELSE /\ io_target_comp' = 0
                     /\ pc' = [pc EXCEPT !["writer"] = "W_IncActiveIOs"]
                     /\ UNCHANGED << comp_active, comp_pool_target, layout_gen,
                                     layout_invalid, type_guard, type_guard_readers,
                                     active_ios, io_captured_gen, io_hit_invalid,
                                     wrote_to_removed_target, layout_change_with_active_io,
                                     prev_layout_gen, gen_went_backwards, thread_done >>

W_IncActiveIOs == /\ pc["writer"] = "W_IncActiveIOs"
                  /\ active_ios' = active_ios + 1
                  /\ pc' = [pc EXCEPT !["writer"] = "W_ReleaseShared"]
                  /\ UNCHANGED << comp_active, comp_pool_target, layout_gen,
                                  layout_invalid, type_guard, type_guard_readers,
                                  io_captured_gen, io_target_comp, io_hit_invalid,
                                  wrote_to_removed_target, layout_change_with_active_io,
                                  prev_layout_gen, gen_went_backwards, thread_done >>

W_ReleaseShared == /\ pc["writer"] = "W_ReleaseShared"
                   /\ type_guard_readers' = type_guard_readers - 1
                   /\ IF type_guard_readers - 1 = 0
                         THEN /\ type_guard' = "free"
                         ELSE /\ UNCHANGED type_guard
                   /\ pc' = [pc EXCEPT !["writer"] = "W_PerformWrite"]
                   /\ UNCHANGED << comp_active, comp_pool_target, layout_gen,
                                   layout_invalid, active_ios, io_captured_gen,
                                   io_target_comp, io_hit_invalid,
                                   wrote_to_removed_target, layout_change_with_active_io,
                                   prev_layout_gen, gen_went_backwards, thread_done >>

W_PerformWrite == /\ pc["writer"] = "W_PerformWrite"
                  /\ IF io_target_comp > 0 /\ io_target_comp \in Comps
                        THEN /\ IF ~comp_pool_target[io_target_comp]
                                    THEN /\ wrote_to_removed_target' = TRUE
                                    ELSE /\ UNCHANGED wrote_to_removed_target
                        ELSE /\ UNCHANGED wrote_to_removed_target
                  /\ pc' = [pc EXCEPT !["writer"] = "W_DecActiveIOs"]
                  /\ UNCHANGED << comp_active, comp_pool_target, layout_gen,
                                  layout_invalid, type_guard, type_guard_readers,
                                  active_ios, io_captured_gen, io_target_comp,
                                  io_hit_invalid, layout_change_with_active_io,
                                  prev_layout_gen, gen_went_backwards, thread_done >>

W_DecActiveIOs == /\ pc["writer"] = "W_DecActiveIOs"
                  /\ active_ios' = active_ios - 1
                  /\ io_target_comp' = 0
                  /\ pc' = [pc EXCEPT !["writer"] = "W_Done"]
                  /\ UNCHANGED << comp_active, comp_pool_target, layout_gen,
                                  layout_invalid, type_guard, type_guard_readers,
                                  io_captured_gen, io_hit_invalid,
                                  wrote_to_removed_target, layout_change_with_active_io,
                                  prev_layout_gen, gen_went_backwards, thread_done >>

W_Done == /\ pc["writer"] = "W_Done"
          /\ thread_done' = [thread_done EXCEPT !["writer"] = TRUE]
          /\ pc' = [pc EXCEPT !["writer"] = "Done"]
          /\ UNCHANGED << comp_active, comp_pool_target, layout_gen,
                          layout_invalid, type_guard, type_guard_readers,
                          active_ios, io_captured_gen, io_target_comp,
                          io_hit_invalid, wrote_to_removed_target,
                          layout_change_with_active_io, prev_layout_gen,
                          gen_went_backwards >>

WriterThread == W_AcquireShared \/ W_CheckInvalid \/ W_CaptureGen
                  \/ W_SelectComponent \/ W_IncActiveIOs \/ W_ReleaseShared
                  \/ W_PerformWrite \/ W_DecActiveIOs \/ W_Done

\* ---- LayoutChanger actions ----

LC_Invalidate == /\ pc["layout_changer"] = "LC_Invalidate"
                 /\ layout_invalid' = TRUE
                 /\ pc' = [pc EXCEPT !["layout_changer"] = "LC_AcquireExclusive"]
                 /\ UNCHANGED << comp_active, comp_pool_target, layout_gen,
                                 type_guard, type_guard_readers, active_ios,
                                 io_captured_gen, io_target_comp, io_hit_invalid,
                                 wrote_to_removed_target, layout_change_with_active_io,
                                 prev_layout_gen, gen_went_backwards, thread_done >>

LC_AcquireExclusive == /\ pc["layout_changer"] = "LC_AcquireExclusive"
                       /\ type_guard = "free"
                       /\ type_guard' = "exclusive"
                       /\ pc' = [pc EXCEPT !["layout_changer"] = "LC_DrainActiveIOs"]
                       /\ UNCHANGED << comp_active, comp_pool_target, layout_gen,
                                       layout_invalid, type_guard_readers, active_ios,
                                       io_captured_gen, io_target_comp, io_hit_invalid,
                                       wrote_to_removed_target, layout_change_with_active_io,
                                       prev_layout_gen, gen_went_backwards, thread_done >>

LC_DrainActiveIOs == /\ pc["layout_changer"] = "LC_DrainActiveIOs"
                     /\ IF InjectBug9839
                           THEN /\ IF active_ios > 0
                                      THEN /\ layout_change_with_active_io' = TRUE
                                      ELSE /\ UNCHANGED layout_change_with_active_io
                                /\ pc' = [pc EXCEPT !["layout_changer"] = "LC_PerformChange"]
                           ELSE /\ active_ios = 0
                                /\ pc' = [pc EXCEPT !["layout_changer"] = "LC_PerformChange"]
                                /\ UNCHANGED layout_change_with_active_io
                     /\ UNCHANGED << comp_active, comp_pool_target, layout_gen,
                                     layout_invalid, type_guard, type_guard_readers,
                                     active_ios, io_captured_gen, io_target_comp,
                                     io_hit_invalid, wrote_to_removed_target,
                                     prev_layout_gen, gen_went_backwards, thread_done >>

LC_PerformChange == /\ pc["layout_changer"] = "LC_PerformChange"
                    /\ IF NumComponents >= 2
                          THEN /\ comp_active' = [comp_active EXCEPT ![2] = TRUE]
                          ELSE /\ UNCHANGED comp_active
                    /\ prev_layout_gen' = layout_gen
                    /\ IF InjectBug18435
                          THEN /\ layout_gen' = 0
                          ELSE /\ layout_gen' = layout_gen + 1
                    /\ pc' = [pc EXCEPT !["layout_changer"] = "LC_CheckMonotonic"]
                    /\ UNCHANGED << comp_pool_target, layout_invalid, type_guard,
                                    type_guard_readers, active_ios, io_captured_gen,
                                    io_target_comp, io_hit_invalid,
                                    wrote_to_removed_target, layout_change_with_active_io,
                                    gen_went_backwards, thread_done >>

LC_CheckMonotonic == /\ pc["layout_changer"] = "LC_CheckMonotonic"
                     /\ IF layout_gen < prev_layout_gen
                           THEN /\ gen_went_backwards' = TRUE
                           ELSE /\ UNCHANGED gen_went_backwards
                     /\ pc' = [pc EXCEPT !["layout_changer"] = "LC_ClearInvalid"]
                     /\ UNCHANGED << comp_active, comp_pool_target, layout_gen,
                                     layout_invalid, type_guard, type_guard_readers,
                                     active_ios, io_captured_gen, io_target_comp,
                                     io_hit_invalid, wrote_to_removed_target,
                                     layout_change_with_active_io, prev_layout_gen,
                                     thread_done >>

LC_ClearInvalid == /\ pc["layout_changer"] = "LC_ClearInvalid"
                   /\ layout_invalid' = FALSE
                   /\ pc' = [pc EXCEPT !["layout_changer"] = "LC_ReleaseExclusive"]
                   /\ UNCHANGED << comp_active, comp_pool_target, layout_gen,
                                   type_guard, type_guard_readers, active_ios,
                                   io_captured_gen, io_target_comp, io_hit_invalid,
                                   wrote_to_removed_target, layout_change_with_active_io,
                                   prev_layout_gen, gen_went_backwards, thread_done >>

LC_ReleaseExclusive == /\ pc["layout_changer"] = "LC_ReleaseExclusive"
                       /\ type_guard' = "free"
                       /\ pc' = [pc EXCEPT !["layout_changer"] = "LC_Done"]
                       /\ UNCHANGED << comp_active, comp_pool_target, layout_gen,
                                       layout_invalid, type_guard_readers, active_ios,
                                       io_captured_gen, io_target_comp, io_hit_invalid,
                                       wrote_to_removed_target, layout_change_with_active_io,
                                       prev_layout_gen, gen_went_backwards, thread_done >>

LC_Done == /\ pc["layout_changer"] = "LC_Done"
           /\ thread_done' = [thread_done EXCEPT !["layout_changer"] = TRUE]
           /\ pc' = [pc EXCEPT !["layout_changer"] = "Done"]
           /\ UNCHANGED << comp_active, comp_pool_target, layout_gen,
                           layout_invalid, type_guard, type_guard_readers,
                           active_ios, io_captured_gen, io_target_comp,
                           io_hit_invalid, wrote_to_removed_target,
                           layout_change_with_active_io, prev_layout_gen,
                           gen_went_backwards >>

LayoutChangerThread == LC_Invalidate \/ LC_AcquireExclusive \/ LC_DrainActiveIOs
                         \/ LC_PerformChange \/ LC_CheckMonotonic \/ LC_ClearInvalid
                         \/ LC_ReleaseExclusive \/ LC_Done

\* ---- PoolChanger actions ----

PC_RemoveFromPool == /\ pc["pool_changer"] = "PC_RemoveFromPool"
                     /\ comp_pool_target' = [comp_pool_target EXCEPT ![1] = FALSE]
                     /\ pc' = [pc EXCEPT !["pool_changer"] = "PC_Done"]
                     /\ UNCHANGED << comp_active, layout_gen, layout_invalid,
                                     type_guard, type_guard_readers, active_ios,
                                     io_captured_gen, io_target_comp, io_hit_invalid,
                                     wrote_to_removed_target, layout_change_with_active_io,
                                     prev_layout_gen, gen_went_backwards, thread_done >>

PC_Done == /\ pc["pool_changer"] = "PC_Done"
           /\ thread_done' = [thread_done EXCEPT !["pool_changer"] = TRUE]
           /\ pc' = [pc EXCEPT !["pool_changer"] = "Done"]
           /\ UNCHANGED << comp_active, comp_pool_target, layout_gen,
                           layout_invalid, type_guard, type_guard_readers,
                           active_ios, io_captured_gen, io_target_comp,
                           io_hit_invalid, wrote_to_removed_target,
                           layout_change_with_active_io, prev_layout_gen,
                           gen_went_backwards >>

PoolChangerThread == PC_RemoveFromPool \/ PC_Done

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == WriterThread \/ LayoutChangerThread \/ PoolChangerThread \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(WriterThread)
        /\ WF_vars(LayoutChangerThread)
        /\ WF_vars(PoolChangerThread)

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

\* ================================================================
\* Liveness: all threads eventually complete
\* ================================================================
AllComplete == <>(\A t \in {"writer", "layout_changer", "pool_changer"} : thread_done[t])

=============================================================================
