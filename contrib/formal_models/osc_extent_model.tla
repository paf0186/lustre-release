--------------------------- MODULE osc_extent_model ---------------------------
(*
 * PlusCal/TLA+ specification of the OSC extent state machine.
 *
 * Models state transitions in lustre/osc/osc_cache.c, focusing on:
 *   - OES_* state transitions and their valid source/destination states
 *   - oo_lock acquisition/release correctness
 *   - oe_users refcount invariant (ACTIVE iff users > 0)
 *   - Truncate vs write races (oe_trunc_pending)
 *   - Transfer pin atomicity (LU-19956)
 *   - Object refcount from extent (LU-7164)
 *   - Page lock ordering vs extent wait (LU-15477)
 *   - oe_urgent + oe_trunc_pending interaction (LU-1755, LU-4852)
 *
 * State machine from osc_cache.c:
 *   INV -> CACHE (alloc), INV -> LOCK_DONE (DIO)
 *   CACHE -> ACTIVE (hold), CACHE -> LOCKING (write RPC)
 *   CACHE -> TRUNC (truncate), CACHE -> INV (destroy)
 *   ACTIVE -> CACHE (release, users->0), ACTIVE -> TRUNC (trunc_pending)
 *   LOCKING -> RPC (make_ready)
 *   LOCK_DONE -> RPC (send)
 *   RPC -> INV (finish)
 *   TRUNC -> CACHE (partial trunc end), TRUNC -> INV (full trunc)
 *
 * Lock order: page lock -> cl_loi_list_lock -> oo_lock
 *             (lustre_osc.h:875, osc_cache.c:2234-2235)
 *
 * Known bugs modeled:
 *   LU-19956: ops_transfer_pinned cleared before cl_page_put,
 *             race with concurrent osc_page_delete.
 *   LU-7164:  osc_extent did not hold refcount on its osc_object,
 *             allowing use-after-free when object destroyed first.
 *   LU-15477: Page lock held across osc_extent_find/wait, deadlock
 *             with make_ready needing page lock.
 *   LU-1755:  TRUNC->CACHE without setting oe_urgent when
 *             oe_fsync_wait was pending.
 *   LU-4852:  osc_extent_wait set oe_urgent without checking
 *             oe_trunc_pending, hitting assertion in truncate.
 *
 * Source (lustre-release master 47638add78, lustre/osc/osc_cache.c
 * unless noted):
 *   __osc_extent_sanity_check  157-244  ACTIVE && users==0 -> rc 40
 *                                       (182-184); ACTIVE fsync_wait &&
 *                                       !urgent -> 55; CACHE fsync_wait
 *                                       && !urgent && !hp -> 65 (193-194)
 *   osc_extent_state_set       296-307
 *   osc_extent_alloc           309-330  cl_object_get(osc2cl(obj)) 319
 *                                       (LU-7164)
 *   osc_extent_put             364-374  cl_object_put 371 on last ref
 *   osc_extent_hold            475-488  CACHE->ACTIVE 482, users++
 *   __osc_extent_remove        490-498  -> OES_INV 496
 *   osc_extent_release         593-687  atomic_dec_and_lock 606;
 *                                       trunc_pending -> OES_TRUNC 623
 *                                       (does not clear oe_urgent);
 *                                       ACTIVE->CACHE 629
 *   osc_extent_find            689-889  alloc + INV->CACHE 854; waits
 *                                       (osc_extent_wait) on conflicts
 *                                       at 870
 *   osc_extent_finish          891-966  osc_completion per page 925,
 *                                       osc_extent_remove 962
 *   osc_extent_wait            968-1022 sets oe_urgent on ACTIVE/CACHE
 *                                       when waiting for INV (979-986);
 *                                       NO oe_trunc_pending check
 *   osc_extent_truncate       1024-     LASSERT(!oe_urgent) 1046
 *   osc_extent_make_ready     1158-1226 osc_make_ready per page 1185
 *                                       (-> cl_page_make_ready, lock_page
 *                                       cl_page.c:1163); LOCKING->RPC 1222
 *   osc_completion            1398-1451 direct ops_transfer_pinned clear
 *                                       1421, cl_page_complete 1446,
 *                                       cl_page_put 1448 (LU-19956 shape)
 *   osc_send_write_rpc         ~2215-   CACHE->LOCKING 2229,
 *                                       LOCK_DONE->RPC 2231
 *   get_write/read_extents     2280/2290 LOCK_DONE->RPC
 *   osc_queue_async_io        2509-     folio batch flushed (page locks
 *                                       dropped) before osc_enter_cache /
 *                                       osc_extent_find 2653-2667
 *                                       (LU-15477 fix 821a8d7b48)
 *   osc_queue_sync_pages      2929-     INV->LOCK_DONE 3005
 *   osc_cache_truncate_start  3078-3207 wait if state > CACHE || urgent
 *                                       (3103-3110); ACTIVE ->
 *                                       trunc_pending=1 (3118-3124);
 *                                       CACHE->TRUNC 3127; wait TRUNC
 *                                       3153
 *   osc_cache_truncate_end    3209-3233 TRUNC->CACHE 3221; oe_fsync_wait
 *                                       -> oe_urgent 3222-3226 (LU-1755)
 *   osc_cache_writeback_range 3316-     fsync_wait=1 3347; CACHE ->
 *                                       urgent 3366-3368; ACTIVE ->
 *                                       oe_urgent=1 unconditionally 3407
 *   lustre/osc/osc_page.c osc_page_transfer_get/put 36-54,
 *                          osc_page_delete 129 (transfer_put 140),
 *                          osc_page_submit 288 (transfer_get 308)
 *
 * Validated against: lustre-release master 47638add78 (2026-09-06)
 * Validation notes:
 *   - DISCREPANCY-OPEN (LU-4852): full trace in
 *     lu4852_truncate_fsync_analysis.md.  The fix commit 28de66844b ("LU-4852
 *     osc: osc_extent_truncate()) ASSERTION( !ext->oe_urgent )
 *     failed", review 10204) adds "&& !ext->oe_trunc_pending" to the
 *     kick guard in osc_extent_wait.  It exists only on origin/b2_5
 *     and is NOT an ancestor of master 47638add78: master's
 *     osc_extent_wait (979-986) and osc_cache_writeback_range's
 *     OES_ACTIVE case (3407) set oe_urgent on an ACTIVE extent with
 *     no oe_trunc_pending check, osc_extent_release (619-624) then
 *     moves it to OES_TRUNC without clearing oe_urgent, and
 *     osc_extent_truncate asserts !oe_urgent (1046).  So master
 *     corresponds to InjectBug4852 = TRUE; the InjectBug4852 = FALSE
 *     variant is the b2_5 fix, not master code.  The model was left
 *     unchanged; this looks like a live (rare) race in master and
 *     should be raised on LU-4852.
 *   - LU-19956 has NOT landed (Gerrit 64440 NEW, 64472 ABANDONED);
 *     master's osc_completion matches InjectBug19956 = TRUE.  The
 *     RC_FixedTransferPut variant is the proposed 64440 shape.
 *   - LU-7164 (319/371), LU-1755 (3222-3226) and LU-15477 (2653-2657)
 *     fixes are present as modeled.
 *   - Abstractions to be aware of: TR_Check's CACHE branch clears
 *     oe_urgent on CACHE->TRUNC, whereas the code never truncates an
 *     urgent CACHE extent (it waits for it to reach INV, 3103-3110);
 *     the Fsync process stands for osc_cache_writeback_range and the
 *     LU-4852 injection point is really in osc_extent_wait; a page
 *     RPC_Send transfer pin is taken at osc_page_cache_add time in
 *     the code, not at RPC formation.
 *)

EXTENDS Integers, FiniteSets, TLC

CONSTANTS
    InjectBug19956,
    InjectBug7164,
    InjectBug15477,
    InjectBug1755,
    InjectBug4852

(* --algorithm PlusCal
variables
    \* === Extent state (protected by oo_lock) ===
    oe_state = "INV";
    oe_users = 0;           \* active writers holding extent
    oe_trunc_pending = FALSE;
    oe_urgent = FALSE;      \* LU-1755/4852: writeback urgency flag
    oe_fsync_wait = FALSE;  \* LU-1755/4852: fsync waiting for INV
    writer_pass = 0;        \* LU-15477: writer does 2 passes to create deadlock

    \* === Transfer pin state (LU-19956) ===
    \* Models the ops_transfer_pinned flag + cl_page reference pair.
    transfer_pinned = FALSE;
    page_ref = 0;           \* simplified: 0=freed, 1=held, 2=double-held

    \* === Object refcount (LU-7164) ===
    \* Models cl_object reference held by extent.
    \* obj_ref tracks how many references exist on the osc_object.
    \* extent_holds_obj_ref tracks whether this extent took one.
    obj_ref = 1;            \* object starts with 1 base ref
    extent_holds_obj_ref = FALSE;
    obj_freed = FALSE;      \* set when obj_ref hits 0

    \* === Page lock (LU-15477) ===
    \* Models the page lock held by writer during commit path.
    page_lock_holder = "none";

    \* === oo_lock spinlock ===
    oo_lock_holder = "none";

    \* === Thread completion tracking ===
    thread_done = [t \in {"writer", "rpc_send", "rpc_complete",
                          "truncate", "page_delete", "fsync",
                          "obj_destroy"} |-> FALSE];

define
    ValidStates == {"INV", "ACTIVE", "CACHE", "LOCKING",
                    "LOCK_DONE", "RPC", "TRUNC"}

    StateIsValid == oe_state \in ValidStates

    \* oo_lock not held by terminated thread
    LockNotHeldByDone ==
        \A t \in DOMAIN thread_done:
            thread_done[t] => oo_lock_holder /= t

    \* OES_ACTIVE requires users > 0 (__osc_extent_sanity_check rc=40, osc_cache.c:182-184)
    ActiveImpliesUsers ==
        oe_state = "ACTIVE" => oe_users > 0

    \* OES_INV requires users = 0
    InvImpliesNoUsers ==
        oe_state = "INV" => oe_users = 0

    \* Transfer pin and page ref must be consistent
    TransferPinConsistency ==
        transfer_pinned => page_ref > 0

    \* Page ref should never go negative
    PageRefNonNegative == page_ref >= 0

    \* LU-7164: Object must not be freed while extent is alive.
    \* The extent accesses oe_obj in state transitions, so the
    \* object must remain live as long as the extent is not INV.
    ObjNotFreedWhileExtentLive ==
        (oe_state /= "INV") => ~obj_freed

    \* LU-7164: Object ref must never go negative
    ObjRefNonNegative == obj_ref >= 0

    \* LU-1755: CACHE + fsync_wait implies urgent or hp
    \* (__osc_extent_sanity_check rc=65, osc_cache.c:193-194)
    CacheFsyncImpliesUrgent ==
        (oe_state = "CACHE" /\ oe_fsync_wait) => oe_urgent

    \* LU-4852: TRUNC must never have oe_urgent set
    \* (LASSERT in osc_extent_truncate)
    TruncNotUrgent ==
        oe_state = "TRUNC" => ~oe_urgent

    \* LU-15477: No deadlock - page lock holder must not be
    \* the same as a thread waiting for extent state change.
    \* Modeled via AllThreadsTerminate temporal property.

    \* === Novel invariants for unknown bug discovery ===

    \* Urgent and trunc_pending are mutually exclusive.
    \* LU-4852 fix guards against setting both, but a future
    \* code change could re-introduce this.  Violation means
    \* ACTIVE -> TRUNC with oe_urgent -> LASSERT.
    UrgentNotTruncPending ==
        ~(oe_urgent /\ oe_trunc_pending)

    \* trunc_pending is only meaningful in ACTIVE state.
    \* Set by truncate on ACTIVE extent (TR_Check), cleared
    \* when writer releases (WR_Release: ACTIVE -> TRUNC).
    TruncPendingImpliesActive ==
        oe_trunc_pending => oe_state = "ACTIVE"

    \* LOCKING is reached from CACHE (no active holders),
    \* so no writer can be holding the extent.
    LockingImpliesNoUsers ==
        oe_state = "LOCKING" => oe_users = 0

    \* RPC is reached from LOCKING or LOCK_DONE, neither
    \* of which has active holders.
    RPCImpliesNoUsers ==
        oe_state = "RPC" => oe_users = 0

    \* When extent is in flight (LOCKING or RPC), the
    \* LU-7164 fix guarantees it holds an object reference.
    \* Catches any future path that reaches RPC without
    \* taking an obj ref.
    InFlightImpliesObjRef ==
        oe_state \in {"LOCKING", "RPC"} => extent_holds_obj_ref

    \* Transfer pin only exists while extent is in RPC or
    \* has just completed (INV with cleanup pending).
    \* Should never be pinned in CACHE/ACTIVE/TRUNC.
    TransferPinImpliesRPCOrInv ==
        transfer_pinned =>
            oe_state \in {"RPC", "INV"}

    \* Valid state transitions
    ValidTransition(from, to) ==
        \/ from = "INV"       /\ to \in {"CACHE", "LOCK_DONE"}
        \/ from = "CACHE"     /\ to \in {"ACTIVE", "LOCKING", "TRUNC", "INV"}
        \/ from = "ACTIVE"    /\ to \in {"CACHE", "TRUNC"}
        \/ from = "LOCKING"   /\ to \in {"RPC"}
        \/ from = "LOCK_DONE" /\ to \in {"RPC"}
        \/ from = "RPC"       /\ to \in {"INV"}
        \/ from = "TRUNC"     /\ to \in {"CACHE", "INV"}
end define;

\* ================================================================
\* Writer: osc_extent_find() + osc_extent_hold() + osc_extent_release()
\* INV -> CACHE, CACHE -> ACTIVE, ACTIVE -> CACHE
\*
\* LU-15477: Writer holds page lock while calling extent_find.
\* In the buggy version, page lock is held across extent_find/wait.
\* In the fixed version, page lock is released before extent_find.
\* ================================================================
fair process Writer = "writer"
begin
WR_PageLock:
    \* Writer locks the page (vvp_io_write_commit -> lock_page)
    await page_lock_holder = "none";
    page_lock_holder := "writer";
WR_PreExtent:
    if InjectBug15477 then
        \* BUG: Keep page lock held, proceed to extent_find
        skip;
    else
        \* FIXED: Release page lock before extent_find (LU-15477)
        \* Pagevec flushed unconditionally before osc_extent_find
        page_lock_holder := "none";
    end if;
WR_AllocLock:
    await oo_lock_holder = "none";
    oo_lock_holder := "writer";
WR_ExtentFind:
    \* osc_extent_find() may need to wait for existing extent
    \* LU-15477: If extent is LOCKING, wait for it (osc_extent_wait).
    \* This is where the deadlock manifests - writer holds page lock
    \* while waiting, but make_ready needs the page lock.
    if oe_state = "LOCKING" then
        oo_lock_holder := "none";
WR_WaitExtent:
        \* Wait for extent to leave LOCKING state (blocks here)
        await oe_state /= "LOCKING";
WR_ReacquireLock:
        await oo_lock_holder = "none";
        oo_lock_holder := "writer";
    end if;
WR_Alloc:
    \* osc_extent_find() allocates extent: INV -> CACHE (osc_cache.c:854)
    if oe_state = "INV" then
        oe_state := "CACHE";
        \* New extent: reset per-extent flags from any prior lifecycle
        oe_fsync_wait := FALSE;
        oe_urgent := FALSE;
        oe_trunc_pending := FALSE;
        \* LU-7164: Take object reference when allocating extent
        if InjectBug7164 then
            \* BUG: No object ref taken
            skip;
        else
            \* FIXED: cl_object_get(osc2cl(obj))
            obj_ref := obj_ref + 1;
            extent_holds_obj_ref := TRUE;
        end if;
    end if;
WR_Hold:
    \* osc_extent_hold(): CACHE -> ACTIVE (osc_cache.c:482)
    if oe_state = "CACHE" then
        oe_state := "ACTIVE";
        oe_users := oe_users + 1;
        oo_lock_holder := "none";
    elsif oe_state = "ACTIVE" then
        \* Already active, just bump users
        oe_users := oe_users + 1;
        oo_lock_holder := "none";
    else
        \* Can't hold extent in other states
        oo_lock_holder := "none";
        goto WR_ReleasePageLock;
    end if;
WR_Work:
    \* Writer does work (adds pages, etc.) without lock
    \* Release page lock if still held (bug path)
    if page_lock_holder = "writer" then
        page_lock_holder := "none";
    end if;
WR_ReleaseLock:
    \* osc_extent_release() uses atomic_dec_and_lock (osc_cache.c:606)
    await oo_lock_holder = "none";
    oo_lock_holder := "writer";
WR_Release:
    oe_users := oe_users - 1;
    if oe_users = 0 then
        if oe_trunc_pending then
            \* Truncate was waiting: ACTIVE -> TRUNC (osc_extent_release, osc_cache.c:623)
            \* Real code does NOT clear oe_urgent here - it relies
            \* on the invariant that oe_urgent is never set when
            \* oe_trunc_pending (enforced by LU-4852 fix).
            oe_state := "TRUNC";
            oe_trunc_pending := FALSE;
        elsif oe_state = "ACTIVE" then
            \* Normal release: ACTIVE -> CACHE (osc_extent_release, osc_cache.c:629)
            oe_state := "CACHE";
        end if;
    end if;
    oo_lock_holder := "none";
WR_MaybeLoop:
    \* LU-15477: Writer may do a second write to same extent.
    \* First pass: creates extent (INV->CACHE->ACTIVE->CACHE).
    \* Second pass: finds extent in LOCKING, waits (with page lock
    \* if bug injected), creating deadlock with make_ready.
    if writer_pass < 1 then
        writer_pass := writer_pass + 1;
        goto WR_PageLock;
    end if;
WR_ReleasePageLock:
    \* Ensure page lock released
    if page_lock_holder = "writer" then
        page_lock_holder := "none";
    end if;
WR_Done:
    thread_done["writer"] := TRUE;
end process;

\* ================================================================
\* RPCSend: osc_send_write_rpc() + osc_extent_make_ready()
\* CACHE -> LOCKING -> RPC, or LOCK_DONE -> RPC
\* Also sets transfer pin on pages.
\*
\* LU-15477: make_ready needs to lock pages (__lock_page).
\* If writer holds page lock and waits on extent, deadlock.
\* ================================================================
fair process RPCSend = "rpc_send"
begin
RS_Lock:
    await oo_lock_holder = "none";
    oo_lock_holder := "rpc_send";
RS_Check:
    if oe_state = "CACHE" then
        \* CACHE -> LOCKING (osc_send_write_rpc, osc_cache.c:2229)
        oe_state := "LOCKING";
        oo_lock_holder := "none";
        goto RS_MakeReady;
    elsif oe_state = "LOCK_DONE" then
        \* LOCK_DONE -> RPC direct (osc_send_write_rpc, osc_cache.c:2231)
        oe_state := "RPC";
        \* Set transfer pin (osc_page_submit sets ops_transfer_pinned)
        transfer_pinned := TRUE;
        page_ref := page_ref + 1;
        oo_lock_holder := "none";
        goto RS_Done;
    else
        oo_lock_holder := "none";
        goto RS_Done;
    end if;
RS_MakeReady:
    \* osc_extent_make_ready() needs to lock pages
    \* LU-15477: This is where the deadlock manifests.
    \* make_ready calls osc_make_ready -> cl_page_make_ready -> lock_page (cl_page.c:1163)
    await page_lock_holder = "none";
    page_lock_holder := "rpc_send";
RS_MakeReadyLock:
    await oo_lock_holder = "none";
    oo_lock_holder := "rpc_send";
RS_SetRPC:
    if oe_state = "LOCKING" then
        oe_state := "RPC";
        \* Set transfer pin on pages
        transfer_pinned := TRUE;
        page_ref := page_ref + 1;
    end if;
    oo_lock_holder := "none";
    page_lock_holder := "none";
RS_Done:
    thread_done["rpc_send"] := TRUE;
end process;

\* ================================================================
\* RPCComplete: osc_extent_finish() + osc_completion()
\* RPC -> INV, clears transfer pin
\* This is where LU-19956 lives.
\* ================================================================
fair process RPCComplete = "rpc_complete"
begin
RC_WaitRPC:
    \* Wait until extent is in RPC state, or all other threads done
    await oe_state = "RPC"
       \/ (thread_done["writer"] /\ thread_done["rpc_send"] /\ thread_done["truncate"]);
RC_CheckSkip:
    if oe_state /= "RPC" then
        goto RC_Done;
    end if;
RC_Complete:
    \* osc_completion() (osc_cache.c:1398-1451) - runs without oo_lock
    if InjectBug19956 then
        \* BUG: Clear pin flag BEFORE dropping page ref.
RC_BugClearPin:
        transfer_pinned := FALSE;
        \* <<< RACE WINDOW: page_delete can run here >>>
RC_BugDropRef:
        page_ref := page_ref - 1;
    else
        \* FIXED: osc_page_transfer_put() clears flag + drops ref
        \* together atomically (test-and-clear + put).
RC_FixedTransferPut:
        if transfer_pinned then
            transfer_pinned := FALSE ||
            page_ref := page_ref - 1;
        end if;
    end if;
RC_Finish:
    \* osc_extent_finish() -> osc_extent_remove(): RPC -> INV
    await oo_lock_holder = "none";
    oo_lock_holder := "rpc_complete";
RC_SetInv:
    if oe_state = "RPC" then
        oe_state := "INV";
        oe_users := 0;
    end if;
    oo_lock_holder := "none";
RC_ExtentPut:
    \* osc_extent_put() - if this was last ref, drop obj ref
    \* LU-7164: Only safe if extent held obj ref
    if extent_holds_obj_ref then
        obj_ref := obj_ref - 1;
        extent_holds_obj_ref := FALSE;
        if obj_ref = 0 then
            obj_freed := TRUE;
        end if;
    end if;
RC_Done:
    thread_done["rpc_complete"] := TRUE;
end process;

\* ================================================================
\* Truncate: osc_cache_truncate_start/end
\* CACHE -> TRUNC -> {CACHE, INV}
\* Also races with ACTIVE extents via trunc_pending
\*
\* LU-1755: truncate_end must propagate oe_urgent when
\*          oe_fsync_wait is set on TRUNC -> CACHE transition.
\* LU-4852: oe_urgent must not be set while oe_trunc_pending,
\*          or LASSERT fires in osc_extent_truncate().
\* ================================================================
fair process Truncate = "truncate"
begin
TR_Lock:
    await oo_lock_holder = "none";
    oo_lock_holder := "truncate";
TR_Check:
    if oe_state = "ACTIVE" /\ ~oe_urgent then
        \* osc_cache_truncate_start: extent is ACTIVE and not urgent
        \* Set trunc_pending and wait (osc_cache_truncate_start, osc_cache.c:3124)
        \* (if oe_urgent, truncate_start waits for flush first,
        \* modeled by not entering this branch at all)
        oe_trunc_pending := TRUE;
        oo_lock_holder := "none";
TR_WaitActive:
        \* Wait for writer to release -> TRUNC (osc_cache_truncate_start, osc_cache.c:3153)
        await oe_state = "TRUNC";
        goto TR_DoTrunc;
    elsif oe_state = "CACHE" then
        \* Direct: CACHE -> TRUNC (osc_cache_truncate_start, osc_cache.c:3127)
        oe_state := "TRUNC";
        \* Abstraction: the code never truncates an urgent CACHE extent (it waits, osc_cache.c:3103-3110); here urgency is dropped instead
        oe_urgent := FALSE;
        oo_lock_holder := "none";
        goto TR_DoTrunc;
    else
        \* Extent in LOCKING/LOCK_DONE/RPC: must wait for INV
        oo_lock_holder := "none";
        goto TR_Done;
    end if;
TR_DoTrunc:
    \* osc_extent_truncate() - removes pages from extent
    \* Then either full truncate (remove) or partial (keep)
    either
        \* Full truncate: TRUNC -> INV
        await oo_lock_holder = "none";
        oo_lock_holder := "truncate";
TR_FullTrunc:
        if oe_state = "TRUNC" then
            oe_state := "INV";
            oe_urgent := FALSE;
        end if;
        oo_lock_holder := "none";
    or
        \* Partial truncate end: TRUNC -> CACHE (osc_cache_truncate_end, osc_cache.c:3221)
        await oo_lock_holder = "none";
        oo_lock_holder := "truncate";
TR_PartialTrunc:
        if oe_state = "TRUNC" then
            oe_state := "CACHE";
            \* LU-1755: Must set oe_urgent if oe_fsync_wait is pending
            if InjectBug1755 then
                \* BUG: No check for oe_fsync_wait, oe_urgent stays FALSE
                skip;
            else
                \* FIXED: Propagate urgency on TRUNC -> CACHE
                if oe_fsync_wait then
                    oe_urgent := TRUE;
                end if;
            end if;
        end if;
        oo_lock_holder := "none";
    end either;
TR_Done:
    thread_done["truncate"] := TRUE;
end process;

\* ================================================================
\* PageDelete: osc_page_delete() - concurrent with RPC completion
\* Races with transfer pin clearing (LU-19956)
\* ================================================================
fair process PageDelete = "page_delete"
begin
PD_WaitRPC:
    \* Only relevant during/after RPC when transfer pin exists
    await oe_state = "RPC"
       \/ (oe_state = "INV" /\ page_ref > 0)
       \/ (thread_done["writer"] /\ thread_done["rpc_send"] /\ thread_done["truncate"]);
PD_CheckSkip:
    if oe_state /= "RPC" /\ ~transfer_pinned /\ page_ref = 0 then
        goto PD_Done;
    end if;
PD_CheckPin:
    \* osc_page_delete checks transfer_pinned (idempotent safety net)
    if transfer_pinned then
        transfer_pinned := FALSE ||
        page_ref := page_ref - 1;
    end if;
PD_Done:
    thread_done["page_delete"] := TRUE;
end process;

\* ================================================================
\* Fsync: osc_cache_writeback_range() - sets oe_fsync_wait
\* Races with truncate (LU-1755, LU-4852)
\* ================================================================
fair process Fsync = "fsync"
begin
FS_Lock:
    await oo_lock_holder = "none";
    oo_lock_holder := "fsync";
FS_Check:
    \* osc_cache_writeback_range() iterates extents
    if oe_state = "CACHE" then
        \* CACHE: set fsync_wait + urgent, add to oo_urgent_exts
        oe_fsync_wait := TRUE;
        oe_urgent := TRUE;
        oo_lock_holder := "none";
    elsif oe_state = "ACTIVE" then
        \* ACTIVE: set fsync_wait. Must also set urgent UNLESS
        \* trunc_pending is set (LU-4852 fix).
        oe_fsync_wait := TRUE;
        if InjectBug4852 then
            \* BUG: Set oe_urgent unconditionally, even with
            \* oe_trunc_pending. When writer releases, extent goes
            \* ACTIVE -> TRUNC with oe_urgent=TRUE -> LASSERT!
            oe_urgent := TRUE;
        else
            \* FIXED: Don't set urgent if trunc_pending
            if ~oe_trunc_pending then
                oe_urgent := TRUE;
            end if;
        end if;
        oo_lock_holder := "none";
    elsif oe_state = "TRUNC" then
        \* TRUNC: set fsync_wait only, do NOT set urgent
        \* (urgent on TRUNC violates LASSERT)
        oe_fsync_wait := TRUE;
        oo_lock_holder := "none";
    else
        oo_lock_holder := "none";
    end if;
FS_Wait:
    \* Wait for extent to reach INV (all pages written + completed)
    \* Or skip if nothing to do
    if oe_fsync_wait then
        await oe_state = "INV"
           \/ (thread_done["writer"] /\ thread_done["rpc_send"]
               /\ thread_done["truncate"] /\ thread_done["rpc_complete"]);
    end if;
FS_Done:
    thread_done["fsync"] := TRUE;
end process;

\* ================================================================
\* ObjDestroy: cl_object lifecycle - drops last object ref
\* LU-7164: If extent didn't take obj ref, object can be freed
\* while extent still exists.
\* ================================================================
fair process ObjDestroy = "obj_destroy"
begin
OD_Wait:
    \* Object destroy happens after all client I/O is done
    \* (inode eviction, etc.)
    await thread_done["writer"];
OD_DropRef:
    \* Drop the base object reference (from initial creation)
    obj_ref := obj_ref - 1;
    if obj_ref = 0 then
        obj_freed := TRUE;
    end if;
OD_Done:
    thread_done["obj_destroy"] := TRUE;
end process;

end algorithm; *)

\* BEGIN TRANSLATION
VARIABLES oe_state, oe_users, oe_trunc_pending, oe_urgent, oe_fsync_wait,
          writer_pass, transfer_pinned, page_ref, obj_ref,
          extent_holds_obj_ref, obj_freed, page_lock_holder, oo_lock_holder,
          thread_done, pc

(* define statement *)
ValidStates == {"INV", "ACTIVE", "CACHE", "LOCKING",
                "LOCK_DONE", "RPC", "TRUNC"}

StateIsValid == oe_state \in ValidStates


LockNotHeldByDone ==
    \A t \in DOMAIN thread_done:
        thread_done[t] => oo_lock_holder /= t


ActiveImpliesUsers ==
    oe_state = "ACTIVE" => oe_users > 0


InvImpliesNoUsers ==
    oe_state = "INV" => oe_users = 0


TransferPinConsistency ==
    transfer_pinned => page_ref > 0


PageRefNonNegative == page_ref >= 0




ObjNotFreedWhileExtentLive ==
    (oe_state /= "INV") => ~obj_freed


ObjRefNonNegative == obj_ref >= 0



CacheFsyncImpliesUrgent ==
    (oe_state = "CACHE" /\ oe_fsync_wait) => oe_urgent



TruncNotUrgent ==
    oe_state = "TRUNC" => ~oe_urgent


UrgentNotTruncPending ==
    ~(oe_urgent /\ oe_trunc_pending)

TruncPendingImpliesActive ==
    oe_trunc_pending => oe_state = "ACTIVE"

LockingImpliesNoUsers ==
    oe_state = "LOCKING" => oe_users = 0

RPCImpliesNoUsers ==
    oe_state = "RPC" => oe_users = 0

InFlightImpliesObjRef ==
    oe_state \in {"LOCKING", "RPC"} => extent_holds_obj_ref

TransferPinImpliesRPCOrInv ==
    transfer_pinned =>
        oe_state \in {"RPC", "INV"}




ValidTransition(from, to) ==
    \/ from = "INV"       /\ to \in {"CACHE", "LOCK_DONE"}
    \/ from = "CACHE"     /\ to \in {"ACTIVE", "LOCKING", "TRUNC", "INV"}
    \/ from = "ACTIVE"    /\ to \in {"CACHE", "TRUNC"}
    \/ from = "LOCKING"   /\ to \in {"RPC"}
    \/ from = "LOCK_DONE" /\ to \in {"RPC"}
    \/ from = "RPC"       /\ to \in {"INV"}
    \/ from = "TRUNC"     /\ to \in {"CACHE", "INV"}


vars == << oe_state, oe_users, oe_trunc_pending, oe_urgent, oe_fsync_wait,
           writer_pass, transfer_pinned, page_ref, obj_ref,
           extent_holds_obj_ref, obj_freed, page_lock_holder, oo_lock_holder,
           thread_done, pc >>

ProcSet == {"writer"} \cup {"rpc_send"} \cup {"rpc_complete"} \cup {"truncate"} \cup {"page_delete"} \cup {"fsync"} \cup {"obj_destroy"}

Init == (* Global variables *)
        /\ oe_state = "INV"
        /\ oe_users = 0
        /\ oe_trunc_pending = FALSE
        /\ oe_urgent = FALSE
        /\ oe_fsync_wait = FALSE
        /\ writer_pass = 0
        /\ transfer_pinned = FALSE
        /\ page_ref = 0
        /\ obj_ref = 1
        /\ extent_holds_obj_ref = FALSE
        /\ obj_freed = FALSE
        /\ page_lock_holder = "none"
        /\ oo_lock_holder = "none"
        /\ thread_done = [t \in {"writer", "rpc_send", "rpc_complete",
                                 "truncate", "page_delete", "fsync",
                                 "obj_destroy"} |-> FALSE]
        /\ pc = [self \in ProcSet |-> CASE self = "writer" -> "WR_PageLock"
                                        [] self = "rpc_send" -> "RS_Lock"
                                        [] self = "rpc_complete" -> "RC_WaitRPC"
                                        [] self = "truncate" -> "TR_Lock"
                                        [] self = "page_delete" -> "PD_WaitRPC"
                                        [] self = "fsync" -> "FS_Lock"
                                        [] self = "obj_destroy" -> "OD_Wait"]

WR_PageLock == /\ pc["writer"] = "WR_PageLock"
               /\ page_lock_holder = "none"
               /\ page_lock_holder' = "writer"
               /\ pc' = [pc EXCEPT !["writer"] = "WR_PreExtent"]
               /\ UNCHANGED << oe_state, oe_users, oe_trunc_pending, oe_urgent,
                               oe_fsync_wait, writer_pass, transfer_pinned,
                               page_ref, obj_ref, extent_holds_obj_ref,
                               obj_freed, oo_lock_holder, thread_done >>

WR_PreExtent == /\ pc["writer"] = "WR_PreExtent"
                /\ IF InjectBug15477
                      THEN /\ TRUE
                           /\ UNCHANGED page_lock_holder
                      ELSE /\ page_lock_holder' = "none"
                /\ pc' = [pc EXCEPT !["writer"] = "WR_AllocLock"]
                /\ UNCHANGED << oe_state, oe_users, oe_trunc_pending,
                                oe_urgent, oe_fsync_wait, writer_pass,
                                transfer_pinned, page_ref, obj_ref,
                                extent_holds_obj_ref, obj_freed,
                                oo_lock_holder, thread_done >>

WR_AllocLock == /\ pc["writer"] = "WR_AllocLock"
                /\ oo_lock_holder = "none"
                /\ oo_lock_holder' = "writer"
                /\ pc' = [pc EXCEPT !["writer"] = "WR_ExtentFind"]
                /\ UNCHANGED << oe_state, oe_users, oe_trunc_pending,
                                oe_urgent, oe_fsync_wait, writer_pass,
                                transfer_pinned, page_ref, obj_ref,
                                extent_holds_obj_ref, obj_freed,
                                page_lock_holder, thread_done >>

WR_ExtentFind == /\ pc["writer"] = "WR_ExtentFind"
                 /\ IF oe_state = "LOCKING"
                       THEN /\ oo_lock_holder' = "none"
                            /\ pc' = [pc EXCEPT !["writer"] = "WR_WaitExtent"]
                       ELSE /\ pc' = [pc EXCEPT !["writer"] = "WR_Alloc"]
                            /\ UNCHANGED oo_lock_holder
                 /\ UNCHANGED << oe_state, oe_users, oe_trunc_pending,
                                 oe_urgent, oe_fsync_wait, writer_pass,
                                 transfer_pinned, page_ref, obj_ref,
                                 extent_holds_obj_ref, obj_freed,
                                 page_lock_holder, thread_done >>

WR_WaitExtent == /\ pc["writer"] = "WR_WaitExtent"
                 /\ oe_state /= "LOCKING"
                 /\ pc' = [pc EXCEPT !["writer"] = "WR_ReacquireLock"]
                 /\ UNCHANGED << oe_state, oe_users, oe_trunc_pending,
                                 oe_urgent, oe_fsync_wait, writer_pass,
                                 transfer_pinned, page_ref, obj_ref,
                                 extent_holds_obj_ref, obj_freed,
                                 page_lock_holder, oo_lock_holder, thread_done >>

WR_ReacquireLock == /\ pc["writer"] = "WR_ReacquireLock"
                    /\ oo_lock_holder = "none"
                    /\ oo_lock_holder' = "writer"
                    /\ pc' = [pc EXCEPT !["writer"] = "WR_Alloc"]
                    /\ UNCHANGED << oe_state, oe_users, oe_trunc_pending,
                                    oe_urgent, oe_fsync_wait, writer_pass,
                                    transfer_pinned, page_ref, obj_ref,
                                    extent_holds_obj_ref, obj_freed,
                                    page_lock_holder, thread_done >>

WR_Alloc == /\ pc["writer"] = "WR_Alloc"
            /\ IF oe_state = "INV"
                  THEN /\ oe_state' = "CACHE"
                       /\ oe_fsync_wait' = FALSE
                       /\ oe_urgent' = FALSE
                       /\ oe_trunc_pending' = FALSE
                       /\ IF InjectBug7164
                             THEN /\ TRUE
                                  /\ UNCHANGED << obj_ref,
                                                  extent_holds_obj_ref >>
                             ELSE /\ obj_ref' = obj_ref + 1
                                  /\ extent_holds_obj_ref' = TRUE
                  ELSE /\ TRUE
                       /\ UNCHANGED << oe_state, oe_trunc_pending, oe_urgent,
                                       oe_fsync_wait, obj_ref,
                                       extent_holds_obj_ref >>
            /\ pc' = [pc EXCEPT !["writer"] = "WR_Hold"]
            /\ UNCHANGED << oe_users, writer_pass, transfer_pinned, page_ref,
                            obj_freed, page_lock_holder, oo_lock_holder,
                            thread_done >>

WR_Hold == /\ pc["writer"] = "WR_Hold"
           /\ IF oe_state = "CACHE"
                 THEN /\ oe_state' = "ACTIVE"
                      /\ oe_users' = oe_users + 1
                      /\ oo_lock_holder' = "none"
                      /\ pc' = [pc EXCEPT !["writer"] = "WR_Work"]
                 ELSE /\ IF oe_state = "ACTIVE"
                            THEN /\ oe_users' = oe_users + 1
                                 /\ oo_lock_holder' = "none"
                                 /\ pc' = [pc EXCEPT !["writer"] = "WR_Work"]
                            ELSE /\ oo_lock_holder' = "none"
                                 /\ pc' = [pc EXCEPT !["writer"] = "WR_ReleasePageLock"]
                                 /\ UNCHANGED oe_users
                      /\ UNCHANGED oe_state
           /\ UNCHANGED << oe_trunc_pending, oe_urgent, oe_fsync_wait,
                           writer_pass, transfer_pinned, page_ref, obj_ref,
                           extent_holds_obj_ref, obj_freed, page_lock_holder,
                           thread_done >>

WR_Work == /\ pc["writer"] = "WR_Work"
           /\ IF page_lock_holder = "writer"
                 THEN /\ page_lock_holder' = "none"
                 ELSE /\ TRUE
                      /\ UNCHANGED page_lock_holder
           /\ pc' = [pc EXCEPT !["writer"] = "WR_ReleaseLock"]
           /\ UNCHANGED << oe_state, oe_users, oe_trunc_pending, oe_urgent,
                           oe_fsync_wait, writer_pass, transfer_pinned,
                           page_ref, obj_ref, extent_holds_obj_ref, obj_freed,
                           oo_lock_holder, thread_done >>

WR_ReleaseLock == /\ pc["writer"] = "WR_ReleaseLock"
                  /\ oo_lock_holder = "none"
                  /\ oo_lock_holder' = "writer"
                  /\ pc' = [pc EXCEPT !["writer"] = "WR_Release"]
                  /\ UNCHANGED << oe_state, oe_users, oe_trunc_pending,
                                  oe_urgent, oe_fsync_wait, writer_pass,
                                  transfer_pinned, page_ref, obj_ref,
                                  extent_holds_obj_ref, obj_freed,
                                  page_lock_holder, thread_done >>

WR_Release == /\ pc["writer"] = "WR_Release"
              /\ oe_users' = oe_users - 1
              /\ IF oe_users' = 0
                    THEN /\ IF oe_trunc_pending
                               THEN /\ oe_state' = "TRUNC"
                                    /\ oe_trunc_pending' = FALSE
                               ELSE /\ IF oe_state = "ACTIVE"
                                          THEN /\ oe_state' = "CACHE"
                                          ELSE /\ TRUE
                                               /\ UNCHANGED oe_state
                                    /\ UNCHANGED oe_trunc_pending
                    ELSE /\ TRUE
                         /\ UNCHANGED << oe_state, oe_trunc_pending >>
              /\ oo_lock_holder' = "none"
              /\ pc' = [pc EXCEPT !["writer"] = "WR_MaybeLoop"]
              /\ UNCHANGED << oe_urgent, oe_fsync_wait, writer_pass,
                              transfer_pinned, page_ref, obj_ref,
                              extent_holds_obj_ref, obj_freed,
                              page_lock_holder, thread_done >>

WR_MaybeLoop == /\ pc["writer"] = "WR_MaybeLoop"
                /\ IF writer_pass < 1
                      THEN /\ writer_pass' = writer_pass + 1
                           /\ pc' = [pc EXCEPT !["writer"] = "WR_PageLock"]
                      ELSE /\ pc' = [pc EXCEPT !["writer"] = "WR_ReleasePageLock"]
                           /\ UNCHANGED writer_pass
                /\ UNCHANGED << oe_state, oe_users, oe_trunc_pending,
                                oe_urgent, oe_fsync_wait, transfer_pinned,
                                page_ref, obj_ref, extent_holds_obj_ref,
                                obj_freed, page_lock_holder, oo_lock_holder,
                                thread_done >>

WR_ReleasePageLock == /\ pc["writer"] = "WR_ReleasePageLock"
                      /\ IF page_lock_holder = "writer"
                            THEN /\ page_lock_holder' = "none"
                            ELSE /\ TRUE
                                 /\ UNCHANGED page_lock_holder
                      /\ pc' = [pc EXCEPT !["writer"] = "WR_Done"]
                      /\ UNCHANGED << oe_state, oe_users, oe_trunc_pending,
                                      oe_urgent, oe_fsync_wait, writer_pass,
                                      transfer_pinned, page_ref, obj_ref,
                                      extent_holds_obj_ref, obj_freed,
                                      oo_lock_holder, thread_done >>

WR_Done == /\ pc["writer"] = "WR_Done"
           /\ thread_done' = [thread_done EXCEPT !["writer"] = TRUE]
           /\ pc' = [pc EXCEPT !["writer"] = "Done"]
           /\ UNCHANGED << oe_state, oe_users, oe_trunc_pending, oe_urgent,
                           oe_fsync_wait, writer_pass, transfer_pinned,
                           page_ref, obj_ref, extent_holds_obj_ref, obj_freed,
                           page_lock_holder, oo_lock_holder >>

Writer == WR_PageLock \/ WR_PreExtent \/ WR_AllocLock \/ WR_ExtentFind
             \/ WR_WaitExtent \/ WR_ReacquireLock \/ WR_Alloc \/ WR_Hold
             \/ WR_Work \/ WR_ReleaseLock \/ WR_Release \/ WR_MaybeLoop
             \/ WR_ReleasePageLock \/ WR_Done

RS_Lock == /\ pc["rpc_send"] = "RS_Lock"
           /\ oo_lock_holder = "none"
           /\ oo_lock_holder' = "rpc_send"
           /\ pc' = [pc EXCEPT !["rpc_send"] = "RS_Check"]
           /\ UNCHANGED << oe_state, oe_users, oe_trunc_pending, oe_urgent,
                           oe_fsync_wait, writer_pass, transfer_pinned,
                           page_ref, obj_ref, extent_holds_obj_ref, obj_freed,
                           page_lock_holder, thread_done >>

RS_Check == /\ pc["rpc_send"] = "RS_Check"
            /\ IF oe_state = "CACHE"
                  THEN /\ oe_state' = "LOCKING"
                       /\ oo_lock_holder' = "none"
                       /\ pc' = [pc EXCEPT !["rpc_send"] = "RS_MakeReady"]
                       /\ UNCHANGED << transfer_pinned, page_ref >>
                  ELSE /\ IF oe_state = "LOCK_DONE"
                             THEN /\ oe_state' = "RPC"
                                  /\ transfer_pinned' = TRUE
                                  /\ page_ref' = page_ref + 1
                                  /\ oo_lock_holder' = "none"
                                  /\ pc' = [pc EXCEPT !["rpc_send"] = "RS_Done"]
                             ELSE /\ oo_lock_holder' = "none"
                                  /\ pc' = [pc EXCEPT !["rpc_send"] = "RS_Done"]
                                  /\ UNCHANGED << oe_state, transfer_pinned,
                                                  page_ref >>
            /\ UNCHANGED << oe_users, oe_trunc_pending, oe_urgent,
                            oe_fsync_wait, writer_pass, obj_ref,
                            extent_holds_obj_ref, obj_freed, page_lock_holder,
                            thread_done >>

RS_MakeReady == /\ pc["rpc_send"] = "RS_MakeReady"
                /\ page_lock_holder = "none"
                /\ page_lock_holder' = "rpc_send"
                /\ pc' = [pc EXCEPT !["rpc_send"] = "RS_MakeReadyLock"]
                /\ UNCHANGED << oe_state, oe_users, oe_trunc_pending,
                                oe_urgent, oe_fsync_wait, writer_pass,
                                transfer_pinned, page_ref, obj_ref,
                                extent_holds_obj_ref, obj_freed,
                                oo_lock_holder, thread_done >>

RS_MakeReadyLock == /\ pc["rpc_send"] = "RS_MakeReadyLock"
                    /\ oo_lock_holder = "none"
                    /\ oo_lock_holder' = "rpc_send"
                    /\ pc' = [pc EXCEPT !["rpc_send"] = "RS_SetRPC"]
                    /\ UNCHANGED << oe_state, oe_users, oe_trunc_pending,
                                    oe_urgent, oe_fsync_wait, writer_pass,
                                    transfer_pinned, page_ref, obj_ref,
                                    extent_holds_obj_ref, obj_freed,
                                    page_lock_holder, thread_done >>

RS_SetRPC == /\ pc["rpc_send"] = "RS_SetRPC"
             /\ IF oe_state = "LOCKING"
                   THEN /\ oe_state' = "RPC"
                        /\ transfer_pinned' = TRUE
                        /\ page_ref' = page_ref + 1
                   ELSE /\ TRUE
                        /\ UNCHANGED << oe_state, transfer_pinned, page_ref >>
             /\ oo_lock_holder' = "none"
             /\ page_lock_holder' = "none"
             /\ pc' = [pc EXCEPT !["rpc_send"] = "RS_Done"]
             /\ UNCHANGED << oe_users, oe_trunc_pending, oe_urgent,
                             oe_fsync_wait, writer_pass, obj_ref,
                             extent_holds_obj_ref, obj_freed, thread_done >>

RS_Done == /\ pc["rpc_send"] = "RS_Done"
           /\ thread_done' = [thread_done EXCEPT !["rpc_send"] = TRUE]
           /\ pc' = [pc EXCEPT !["rpc_send"] = "Done"]
           /\ UNCHANGED << oe_state, oe_users, oe_trunc_pending, oe_urgent,
                           oe_fsync_wait, writer_pass, transfer_pinned,
                           page_ref, obj_ref, extent_holds_obj_ref, obj_freed,
                           page_lock_holder, oo_lock_holder >>

RPCSend == RS_Lock \/ RS_Check \/ RS_MakeReady \/ RS_MakeReadyLock
              \/ RS_SetRPC \/ RS_Done

RC_WaitRPC == /\ pc["rpc_complete"] = "RC_WaitRPC"
              /\    oe_state = "RPC"
                 \/ (thread_done["writer"] /\ thread_done["rpc_send"] /\ thread_done["truncate"])
              /\ pc' = [pc EXCEPT !["rpc_complete"] = "RC_CheckSkip"]
              /\ UNCHANGED << oe_state, oe_users, oe_trunc_pending, oe_urgent,
                              oe_fsync_wait, writer_pass, transfer_pinned,
                              page_ref, obj_ref, extent_holds_obj_ref,
                              obj_freed, page_lock_holder, oo_lock_holder,
                              thread_done >>

RC_CheckSkip == /\ pc["rpc_complete"] = "RC_CheckSkip"
                /\ IF oe_state /= "RPC"
                      THEN /\ pc' = [pc EXCEPT !["rpc_complete"] = "RC_Done"]
                      ELSE /\ pc' = [pc EXCEPT !["rpc_complete"] = "RC_Complete"]
                /\ UNCHANGED << oe_state, oe_users, oe_trunc_pending,
                                oe_urgent, oe_fsync_wait, writer_pass,
                                transfer_pinned, page_ref, obj_ref,
                                extent_holds_obj_ref, obj_freed,
                                page_lock_holder, oo_lock_holder, thread_done >>

RC_Complete == /\ pc["rpc_complete"] = "RC_Complete"
               /\ IF InjectBug19956
                     THEN /\ pc' = [pc EXCEPT !["rpc_complete"] = "RC_BugClearPin"]
                     ELSE /\ pc' = [pc EXCEPT !["rpc_complete"] = "RC_FixedTransferPut"]
               /\ UNCHANGED << oe_state, oe_users, oe_trunc_pending, oe_urgent,
                               oe_fsync_wait, writer_pass, transfer_pinned,
                               page_ref, obj_ref, extent_holds_obj_ref,
                               obj_freed, page_lock_holder, oo_lock_holder,
                               thread_done >>

RC_BugClearPin == /\ pc["rpc_complete"] = "RC_BugClearPin"
                  /\ transfer_pinned' = FALSE
                  /\ pc' = [pc EXCEPT !["rpc_complete"] = "RC_BugDropRef"]
                  /\ UNCHANGED << oe_state, oe_users, oe_trunc_pending,
                                  oe_urgent, oe_fsync_wait, writer_pass,
                                  page_ref, obj_ref, extent_holds_obj_ref,
                                  obj_freed, page_lock_holder, oo_lock_holder,
                                  thread_done >>

RC_BugDropRef == /\ pc["rpc_complete"] = "RC_BugDropRef"
                 /\ page_ref' = page_ref - 1
                 /\ pc' = [pc EXCEPT !["rpc_complete"] = "RC_Finish"]
                 /\ UNCHANGED << oe_state, oe_users, oe_trunc_pending,
                                 oe_urgent, oe_fsync_wait, writer_pass,
                                 transfer_pinned, obj_ref,
                                 extent_holds_obj_ref, obj_freed,
                                 page_lock_holder, oo_lock_holder, thread_done >>

RC_FixedTransferPut == /\ pc["rpc_complete"] = "RC_FixedTransferPut"
                       /\ IF transfer_pinned
                             THEN /\ /\ page_ref' = page_ref - 1
                                     /\ transfer_pinned' = FALSE
                             ELSE /\ TRUE
                                  /\ UNCHANGED << transfer_pinned, page_ref >>
                       /\ pc' = [pc EXCEPT !["rpc_complete"] = "RC_Finish"]
                       /\ UNCHANGED << oe_state, oe_users, oe_trunc_pending,
                                       oe_urgent, oe_fsync_wait, writer_pass,
                                       obj_ref, extent_holds_obj_ref,
                                       obj_freed, page_lock_holder,
                                       oo_lock_holder, thread_done >>

RC_Finish == /\ pc["rpc_complete"] = "RC_Finish"
             /\ oo_lock_holder = "none"
             /\ oo_lock_holder' = "rpc_complete"
             /\ pc' = [pc EXCEPT !["rpc_complete"] = "RC_SetInv"]
             /\ UNCHANGED << oe_state, oe_users, oe_trunc_pending, oe_urgent,
                             oe_fsync_wait, writer_pass, transfer_pinned,
                             page_ref, obj_ref, extent_holds_obj_ref,
                             obj_freed, page_lock_holder, thread_done >>

RC_SetInv == /\ pc["rpc_complete"] = "RC_SetInv"
             /\ IF oe_state = "RPC"
                   THEN /\ oe_state' = "INV"
                        /\ oe_users' = 0
                   ELSE /\ TRUE
                        /\ UNCHANGED << oe_state, oe_users >>
             /\ oo_lock_holder' = "none"
             /\ pc' = [pc EXCEPT !["rpc_complete"] = "RC_ExtentPut"]
             /\ UNCHANGED << oe_trunc_pending, oe_urgent, oe_fsync_wait,
                             writer_pass, transfer_pinned, page_ref, obj_ref,
                             extent_holds_obj_ref, obj_freed, page_lock_holder,
                             thread_done >>

RC_ExtentPut == /\ pc["rpc_complete"] = "RC_ExtentPut"
                /\ IF extent_holds_obj_ref
                      THEN /\ obj_ref' = obj_ref - 1
                           /\ extent_holds_obj_ref' = FALSE
                           /\ IF obj_ref' = 0
                                 THEN /\ obj_freed' = TRUE
                                 ELSE /\ TRUE
                                      /\ UNCHANGED obj_freed
                      ELSE /\ TRUE
                           /\ UNCHANGED << obj_ref, extent_holds_obj_ref,
                                           obj_freed >>
                /\ pc' = [pc EXCEPT !["rpc_complete"] = "RC_Done"]
                /\ UNCHANGED << oe_state, oe_users, oe_trunc_pending,
                                oe_urgent, oe_fsync_wait, writer_pass,
                                transfer_pinned, page_ref, page_lock_holder,
                                oo_lock_holder, thread_done >>

RC_Done == /\ pc["rpc_complete"] = "RC_Done"
           /\ thread_done' = [thread_done EXCEPT !["rpc_complete"] = TRUE]
           /\ pc' = [pc EXCEPT !["rpc_complete"] = "Done"]
           /\ UNCHANGED << oe_state, oe_users, oe_trunc_pending, oe_urgent,
                           oe_fsync_wait, writer_pass, transfer_pinned,
                           page_ref, obj_ref, extent_holds_obj_ref, obj_freed,
                           page_lock_holder, oo_lock_holder >>

RPCComplete == RC_WaitRPC \/ RC_CheckSkip \/ RC_Complete \/ RC_BugClearPin
                  \/ RC_BugDropRef \/ RC_FixedTransferPut \/ RC_Finish
                  \/ RC_SetInv \/ RC_ExtentPut \/ RC_Done

TR_Lock == /\ pc["truncate"] = "TR_Lock"
           /\ oo_lock_holder = "none"
           /\ oo_lock_holder' = "truncate"
           /\ pc' = [pc EXCEPT !["truncate"] = "TR_Check"]
           /\ UNCHANGED << oe_state, oe_users, oe_trunc_pending, oe_urgent,
                           oe_fsync_wait, writer_pass, transfer_pinned,
                           page_ref, obj_ref, extent_holds_obj_ref, obj_freed,
                           page_lock_holder, thread_done >>

TR_Check == /\ pc["truncate"] = "TR_Check"
            /\ IF oe_state = "ACTIVE" /\ ~oe_urgent
                  THEN /\ oe_trunc_pending' = TRUE
                       /\ oo_lock_holder' = "none"
                       /\ pc' = [pc EXCEPT !["truncate"] = "TR_WaitActive"]
                       /\ UNCHANGED << oe_state, oe_urgent >>
                  ELSE /\ IF oe_state = "CACHE"
                             THEN /\ oe_state' = "TRUNC"
                                  /\ oe_urgent' = FALSE
                                  /\ oo_lock_holder' = "none"
                                  /\ pc' = [pc EXCEPT !["truncate"] = "TR_DoTrunc"]
                             ELSE /\ oo_lock_holder' = "none"
                                  /\ pc' = [pc EXCEPT !["truncate"] = "TR_Done"]
                                  /\ UNCHANGED << oe_state, oe_urgent >>
                       /\ UNCHANGED oe_trunc_pending
            /\ UNCHANGED << oe_users, oe_fsync_wait, writer_pass,
                            transfer_pinned, page_ref, obj_ref,
                            extent_holds_obj_ref, obj_freed, page_lock_holder,
                            thread_done >>

TR_WaitActive == /\ pc["truncate"] = "TR_WaitActive"
                 /\ oe_state = "TRUNC"
                 /\ pc' = [pc EXCEPT !["truncate"] = "TR_DoTrunc"]
                 /\ UNCHANGED << oe_state, oe_users, oe_trunc_pending,
                                 oe_urgent, oe_fsync_wait, writer_pass,
                                 transfer_pinned, page_ref, obj_ref,
                                 extent_holds_obj_ref, obj_freed,
                                 page_lock_holder, oo_lock_holder, thread_done >>

TR_DoTrunc == /\ pc["truncate"] = "TR_DoTrunc"
              /\ \/ /\ oo_lock_holder = "none"
                    /\ oo_lock_holder' = "truncate"
                    /\ pc' = [pc EXCEPT !["truncate"] = "TR_FullTrunc"]
                 \/ /\ oo_lock_holder = "none"
                    /\ oo_lock_holder' = "truncate"
                    /\ pc' = [pc EXCEPT !["truncate"] = "TR_PartialTrunc"]
              /\ UNCHANGED << oe_state, oe_users, oe_trunc_pending, oe_urgent,
                              oe_fsync_wait, writer_pass, transfer_pinned,
                              page_ref, obj_ref, extent_holds_obj_ref,
                              obj_freed, page_lock_holder, thread_done >>

TR_FullTrunc == /\ pc["truncate"] = "TR_FullTrunc"
                /\ IF oe_state = "TRUNC"
                      THEN /\ oe_state' = "INV"
                           /\ oe_urgent' = FALSE
                      ELSE /\ TRUE
                           /\ UNCHANGED << oe_state, oe_urgent >>
                /\ oo_lock_holder' = "none"
                /\ pc' = [pc EXCEPT !["truncate"] = "TR_Done"]
                /\ UNCHANGED << oe_users, oe_trunc_pending, oe_fsync_wait,
                                writer_pass, transfer_pinned, page_ref,
                                obj_ref, extent_holds_obj_ref, obj_freed,
                                page_lock_holder, thread_done >>

TR_PartialTrunc == /\ pc["truncate"] = "TR_PartialTrunc"
                   /\ IF oe_state = "TRUNC"
                         THEN /\ oe_state' = "CACHE"
                              /\ IF InjectBug1755
                                    THEN /\ TRUE
                                         /\ UNCHANGED oe_urgent
                                    ELSE /\ IF oe_fsync_wait
                                               THEN /\ oe_urgent' = TRUE
                                               ELSE /\ TRUE
                                                    /\ UNCHANGED oe_urgent
                         ELSE /\ TRUE
                              /\ UNCHANGED << oe_state, oe_urgent >>
                   /\ oo_lock_holder' = "none"
                   /\ pc' = [pc EXCEPT !["truncate"] = "TR_Done"]
                   /\ UNCHANGED << oe_users, oe_trunc_pending, oe_fsync_wait,
                                   writer_pass, transfer_pinned, page_ref,
                                   obj_ref, extent_holds_obj_ref, obj_freed,
                                   page_lock_holder, thread_done >>

TR_Done == /\ pc["truncate"] = "TR_Done"
           /\ thread_done' = [thread_done EXCEPT !["truncate"] = TRUE]
           /\ pc' = [pc EXCEPT !["truncate"] = "Done"]
           /\ UNCHANGED << oe_state, oe_users, oe_trunc_pending, oe_urgent,
                           oe_fsync_wait, writer_pass, transfer_pinned,
                           page_ref, obj_ref, extent_holds_obj_ref, obj_freed,
                           page_lock_holder, oo_lock_holder >>

Truncate == TR_Lock \/ TR_Check \/ TR_WaitActive \/ TR_DoTrunc
               \/ TR_FullTrunc \/ TR_PartialTrunc \/ TR_Done

PD_WaitRPC == /\ pc["page_delete"] = "PD_WaitRPC"
              /\    oe_state = "RPC"
                 \/ (oe_state = "INV" /\ page_ref > 0)
                 \/ (thread_done["writer"] /\ thread_done["rpc_send"] /\ thread_done["truncate"])
              /\ pc' = [pc EXCEPT !["page_delete"] = "PD_CheckSkip"]
              /\ UNCHANGED << oe_state, oe_users, oe_trunc_pending, oe_urgent,
                              oe_fsync_wait, writer_pass, transfer_pinned,
                              page_ref, obj_ref, extent_holds_obj_ref,
                              obj_freed, page_lock_holder, oo_lock_holder,
                              thread_done >>

PD_CheckSkip == /\ pc["page_delete"] = "PD_CheckSkip"
                /\ IF oe_state /= "RPC" /\ ~transfer_pinned /\ page_ref = 0
                      THEN /\ pc' = [pc EXCEPT !["page_delete"] = "PD_Done"]
                      ELSE /\ pc' = [pc EXCEPT !["page_delete"] = "PD_CheckPin"]
                /\ UNCHANGED << oe_state, oe_users, oe_trunc_pending,
                                oe_urgent, oe_fsync_wait, writer_pass,
                                transfer_pinned, page_ref, obj_ref,
                                extent_holds_obj_ref, obj_freed,
                                page_lock_holder, oo_lock_holder, thread_done >>

PD_CheckPin == /\ pc["page_delete"] = "PD_CheckPin"
               /\ IF transfer_pinned
                     THEN /\ /\ page_ref' = page_ref - 1
                             /\ transfer_pinned' = FALSE
                     ELSE /\ TRUE
                          /\ UNCHANGED << transfer_pinned, page_ref >>
               /\ pc' = [pc EXCEPT !["page_delete"] = "PD_Done"]
               /\ UNCHANGED << oe_state, oe_users, oe_trunc_pending, oe_urgent,
                               oe_fsync_wait, writer_pass, obj_ref,
                               extent_holds_obj_ref, obj_freed,
                               page_lock_holder, oo_lock_holder, thread_done >>

PD_Done == /\ pc["page_delete"] = "PD_Done"
           /\ thread_done' = [thread_done EXCEPT !["page_delete"] = TRUE]
           /\ pc' = [pc EXCEPT !["page_delete"] = "Done"]
           /\ UNCHANGED << oe_state, oe_users, oe_trunc_pending, oe_urgent,
                           oe_fsync_wait, writer_pass, transfer_pinned,
                           page_ref, obj_ref, extent_holds_obj_ref, obj_freed,
                           page_lock_holder, oo_lock_holder >>

PageDelete == PD_WaitRPC \/ PD_CheckSkip \/ PD_CheckPin \/ PD_Done

FS_Lock == /\ pc["fsync"] = "FS_Lock"
           /\ oo_lock_holder = "none"
           /\ oo_lock_holder' = "fsync"
           /\ pc' = [pc EXCEPT !["fsync"] = "FS_Check"]
           /\ UNCHANGED << oe_state, oe_users, oe_trunc_pending, oe_urgent,
                           oe_fsync_wait, writer_pass, transfer_pinned,
                           page_ref, obj_ref, extent_holds_obj_ref, obj_freed,
                           page_lock_holder, thread_done >>

FS_Check == /\ pc["fsync"] = "FS_Check"
            /\ IF oe_state = "CACHE"
                  THEN /\ oe_fsync_wait' = TRUE
                       /\ oe_urgent' = TRUE
                       /\ oo_lock_holder' = "none"
                  ELSE /\ IF oe_state = "ACTIVE"
                             THEN /\ oe_fsync_wait' = TRUE
                                  /\ IF InjectBug4852
                                        THEN /\ oe_urgent' = TRUE
                                        ELSE /\ IF ~oe_trunc_pending
                                                   THEN /\ oe_urgent' = TRUE
                                                   ELSE /\ TRUE
                                                        /\ UNCHANGED oe_urgent
                                  /\ oo_lock_holder' = "none"
                             ELSE /\ IF oe_state = "TRUNC"
                                        THEN /\ oe_fsync_wait' = TRUE
                                             /\ oo_lock_holder' = "none"
                                        ELSE /\ oo_lock_holder' = "none"
                                             /\ UNCHANGED oe_fsync_wait
                                  /\ UNCHANGED oe_urgent
            /\ pc' = [pc EXCEPT !["fsync"] = "FS_Wait"]
            /\ UNCHANGED << oe_state, oe_users, oe_trunc_pending, writer_pass,
                            transfer_pinned, page_ref, obj_ref,
                            extent_holds_obj_ref, obj_freed, page_lock_holder,
                            thread_done >>

FS_Wait == /\ pc["fsync"] = "FS_Wait"
           /\ IF oe_fsync_wait
                 THEN /\    oe_state = "INV"
                         \/ (thread_done["writer"] /\ thread_done["rpc_send"]
                             /\ thread_done["truncate"] /\ thread_done["rpc_complete"])
                 ELSE /\ TRUE
           /\ pc' = [pc EXCEPT !["fsync"] = "FS_Done"]
           /\ UNCHANGED << oe_state, oe_users, oe_trunc_pending, oe_urgent,
                           oe_fsync_wait, writer_pass, transfer_pinned,
                           page_ref, obj_ref, extent_holds_obj_ref, obj_freed,
                           page_lock_holder, oo_lock_holder, thread_done >>

FS_Done == /\ pc["fsync"] = "FS_Done"
           /\ thread_done' = [thread_done EXCEPT !["fsync"] = TRUE]
           /\ pc' = [pc EXCEPT !["fsync"] = "Done"]
           /\ UNCHANGED << oe_state, oe_users, oe_trunc_pending, oe_urgent,
                           oe_fsync_wait, writer_pass, transfer_pinned,
                           page_ref, obj_ref, extent_holds_obj_ref, obj_freed,
                           page_lock_holder, oo_lock_holder >>

Fsync == FS_Lock \/ FS_Check \/ FS_Wait \/ FS_Done

OD_Wait == /\ pc["obj_destroy"] = "OD_Wait"
           /\ thread_done["writer"]
           /\ pc' = [pc EXCEPT !["obj_destroy"] = "OD_DropRef"]
           /\ UNCHANGED << oe_state, oe_users, oe_trunc_pending, oe_urgent,
                           oe_fsync_wait, writer_pass, transfer_pinned,
                           page_ref, obj_ref, extent_holds_obj_ref, obj_freed,
                           page_lock_holder, oo_lock_holder, thread_done >>

OD_DropRef == /\ pc["obj_destroy"] = "OD_DropRef"
              /\ obj_ref' = obj_ref - 1
              /\ IF obj_ref' = 0
                    THEN /\ obj_freed' = TRUE
                    ELSE /\ TRUE
                         /\ UNCHANGED obj_freed
              /\ pc' = [pc EXCEPT !["obj_destroy"] = "OD_Done"]
              /\ UNCHANGED << oe_state, oe_users, oe_trunc_pending, oe_urgent,
                              oe_fsync_wait, writer_pass, transfer_pinned,
                              page_ref, extent_holds_obj_ref, page_lock_holder,
                              oo_lock_holder, thread_done >>

OD_Done == /\ pc["obj_destroy"] = "OD_Done"
           /\ thread_done' = [thread_done EXCEPT !["obj_destroy"] = TRUE]
           /\ pc' = [pc EXCEPT !["obj_destroy"] = "Done"]
           /\ UNCHANGED << oe_state, oe_users, oe_trunc_pending, oe_urgent,
                           oe_fsync_wait, writer_pass, transfer_pinned,
                           page_ref, obj_ref, extent_holds_obj_ref, obj_freed,
                           page_lock_holder, oo_lock_holder >>

ObjDestroy == OD_Wait \/ OD_DropRef \/ OD_Done

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == Writer \/ RPCSend \/ RPCComplete \/ Truncate \/ PageDelete \/ Fsync
           \/ ObjDestroy
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Writer)
        /\ WF_vars(RPCSend)
        /\ WF_vars(RPCComplete)
        /\ WF_vars(Truncate)
        /\ WF_vars(PageDelete)
        /\ WF_vars(Fsync)
        /\ WF_vars(ObjDestroy)

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

\* Temporal properties
AllThreadsTerminate == <>(\A t \in DOMAIN thread_done : thread_done[t])
LockEventuallyFree == []<>(oo_lock_holder = "none")

=============================================================================
