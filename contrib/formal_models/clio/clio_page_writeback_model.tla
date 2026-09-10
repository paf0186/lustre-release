------------------ MODULE clio_page_writeback_model ------------------
(*
 * Focused model of the CLIO page writeback vs truncation race.
 *
 * Models a single cl_page with:
 *   - page_state in {CACHE, WRITEBACK, FREEABLE}
 *   - in_flight boolean (TRUE while write I/O is outstanding)
 *
 * Two concurrent threads:
 *   WritebackThread: CACHE -> WRITEBACK (submit write I/O)
 *                         -> CACHE       (I/O completes)
 *   TruncateThread:  -> FREEABLE  (with or without checking
 *                                   page_state != WRITEBACK)
 *
 * Invariant:
 *   NoStaleWrite -- page never becomes FREEABLE while in_flight = TRUE.
 *   A violation means the page could be reclaimed or reused while an
 *   outstanding write I/O still references it: data corruption.
 *
 * Bug injection:
 *   INJECT_TRUNCATE_NO_WAIT = TRUE  -- TruncateThread sets FREEABLE
 *     unconditionally (pre-LU-4581: no PageWriteback guard in delete).
 *   INJECT_TRUNCATE_NO_WAIT = FALSE -- TruncateThread atomically
 *     checks page_state != WRITEBACK before setting FREEABLE.
 *     The atomicity models the page lock that prevents new writebacks
 *     from starting between the check and the state change.
 *
 * Design note -- why TR_SetFreeable is one atomic step in fix mode:
 *   A two-phase approach (check in step 1, transition in step 2)
 *   would allow WritebackThread to start a new write I/O between
 *   the check and the state change -- a TOCTOU race.  In real C code
 *   (LU-4581 fix), the page lock held by cl_page_own prevents new
 *   writes from starting once the check has passed.  Modeling the
 *   guard and transition as a single atomic TLA+ action captures
 *   this mutual exclusion without explicitly modeling the lock.
 *
 * Related: LU-4581 (delete/truncate without PageWriteback check races
 * async write -- lock cancel path could own a PAGEOUT page).
 *
 * Source (lustre-release master 47638add78):
 *   lustre/obdclass/cl_page.c
 *     __cl_page_own          705-770  the guard: nonblock own returns
 *                                     -EAGAIN if PageWriteback (731-734);
 *                                     blocking own does lock_page +
 *                                     wait_on_page_writeback (737-738)
 *     cl_page_assume         806-839  wait_on_page_writeback at 820
 *     cl_page_make_ready    1152-1205 lock_page 1163, set_page_writeback
 *                                     1170, cl_page_io_start 1187
 *                                     (CPS_PAGEOUT), unlock_page 1191
 *     cl_page_complete      1106-1149 CPS_CACHED at 1121, then
 *                                     cpo_complete bottom-up
 *     __cl_page_delete       934-960  CPS_FREEING at 950
 *   lustre/llite/vvp_page.c
 *     vvp_page_complete_write 159-183 end_page_writeback at 180
 *   lustre/llite/rw26.c
 *     ll_invalidate_folio     48-87   VM truncate path; asserts
 *                                     !folio_test_writeback (55, 75)
 *                                     because truncate_inode_pages
 *                                     already waited; cl_page_delete 76
 *     do_release_page        147-198  reclaim path; refuses
 *                                     PageWriteback/PageDirty (159)
 *   lustre/osc/osc_cache.c
 *     osc_completion        1398-1451 RPC completion; cl_page_complete
 *                                     at 1446
 *     osc_discard_cb        3672-3700 lock-cancel discard: cl_page_own
 *                                     (3683) then cl_page_discard (3690)
 *     osc_extent_wait        968-1022 uninterruptible wait used by
 *                                     osc_lock_flush before discard
 *   lustre/osc/osc_lock.c
 *     osc_lock_flush         347-393  writeback_range, then
 *                                     osc_lock_discard_pages (381)
 *
 * Validated against: lustre-release master 47638add78 (2026-09-06)
 * Validation notes:
 *   - The historical LU-4581 crash (discard_cb LASSERT(!PageWriteback))
 *     was resolved by review 5419 = commit 26345bee6b "LU-2779 osc:
 *     osc_extent_wait() shouldn't be interruptible", which makes
 *     osc_lock_flush wait for in-flight extents before discarding
 *     pages.  The "guard" abstracted by TR_Truncate therefore
 *     corresponds in this tree to (a) that uninterruptible extent
 *     wait, (b) __cl_page_own waiting on / rejecting PageWriteback
 *     (cl_page.c:731-738, moved here from vvp_page_own by LU-10994),
 *     and (c) the VM's own writeback wait before ll_invalidate_folio.
 *     The model's guard+transition semantics are unchanged; only the
 *     C-analog comments below were corrected.
 *
 * This is a standalone focused model separate from ClPage.tla.
 * ClPage models the full cl_page lifecycle including reference
 * counting, seqlocks, and vmpage flags.  This model isolates the
 * truncation/writeback ordering race for clarity and quick iteration.
 *
 * Target state space: < 5K states.
 *)

EXTENDS Naturals, TLC

CONSTANTS INJECT_TRUNCATE_NO_WAIT

(* ---- Type sets ---- *)

PageStates == {"CACHE", "WRITEBACK", "FREEABLE"}
WB_PCs     == {"wb_start", "wb_complete", "wb_done"}
TR_PCs     == {"tr_start", "tr_done"}

(* ---- State variables ---- *)

VARIABLES
    page_state,    \* current page state
    in_flight,     \* TRUE while write I/O is outstanding
    wb_pc,         \* WritebackThread program counter
    tr_pc          \* TruncateThread program counter

vars == <<page_state, in_flight, wb_pc, tr_pc>>

TypeOK ==
    /\ page_state \in PageStates
    /\ in_flight  \in BOOLEAN
    /\ wb_pc      \in WB_PCs
    /\ tr_pc      \in TR_PCs

(* ---- WritebackThread ---- *)

(*
 * Step 1: Begin writeback.
 *   Precondition: page is CACHE (quiescent, not already being written).
 *   Effect: page_state -> WRITEBACK, in_flight := TRUE.
 *   C analog: cl_page_make_ready (cl_page.c:1152-1205): lock_page,
 *             set_page_writeback (1170, sets PageWriteback vmpage
 *             flag), cl_page_io_start (1187, CPS_PAGEOUT).  The
 *             transfer pin (osc_page_transfer_get, osc_page.c:36-43)
 *             was already taken at osc_page_cache_add time.
 *)
WB_Start ==
    /\ wb_pc      = "wb_start"
    /\ page_state = "CACHE"
    /\ page_state' = "WRITEBACK"
    /\ in_flight'  = TRUE
    /\ wb_pc'      = "wb_complete"
    /\ UNCHANGED tr_pc

(*
 * Step 2: Write I/O completes.
 *   Effect: page_state -> CACHE, in_flight := FALSE.
 *   C analog: osc_completion (osc_cache.c:1398-1451) -> cl_page_complete
 *             (cl_page.c:1106-1149, CPS_CACHED) -> vvp_page_complete_write
 *             -> end_page_writeback (vvp_page.c:180, clears PageWriteback)
 *             -> cl_page_put (osc_cache.c:1448, drops transfer ref; in
 *             this tree the pin flag is cleared directly at 1421, see
 *             TransferPin.tla / LU-19956)
 *)
WB_Complete ==
    /\ wb_pc = "wb_complete"
    /\ page_state' = "CACHE"
    /\ in_flight'  = FALSE
    /\ wb_pc'      = "wb_done"
    /\ UNCHANGED tr_pc

(* ---- TruncateThread ---- *)

(*
 * Truncate -- atomically check (if fix) and mark page FREEABLE.
 *
 *   BUG:  set FREEABLE unconditionally, even if write I/O is in flight.
 *         Models the pre-LU-4581 lock-cancel path: osc_lock_flush could
 *         return early (interruptible osc_extent_wait) and discard_cb
 *         then owned a page that was still PageWriteback.
 *
 *   FIX:  set FREEABLE only when page_state != WRITEBACK.  The guard
 *         and transition are ONE atomic step, modeling the page lock
 *         (cl_page_own) that prevents WB_Start from re-firing between
 *         the check and the state change.
 *
 *   C analog (lock cancel): osc_lock_flush (osc_lock.c:347) ->
 *             osc_extent_wait (uninterruptible, osc_cache.c:968) ->
 *             osc_lock_discard_pages -> osc_discard_cb (osc_cache.c:3672)
 *             -> cl_page_own (waits on PageWriteback, cl_page.c:737-738)
 *             -> cl_page_discard -> cl_page_delete (CPS_FREEING)
 *   C analog (truncate): truncate_inode_pages (waits for writeback) ->
 *             ll_invalidate_folio (rw26.c:48, LASSERT !writeback) ->
 *             cl_page_delete (CPS_FREEING); the VM holds the page lock.
 *)
TR_Truncate ==
    /\ tr_pc = "tr_start"
    /\ IF INJECT_TRUNCATE_NO_WAIT
       THEN TRUE                        \* BUG: no guard
       ELSE page_state # "WRITEBACK"    \* FIX: writeback-complete check
    /\ page_state' = "FREEABLE"
    /\ tr_pc' = "tr_done"
    /\ UNCHANGED <<in_flight, wb_pc>>

(* ---- Specification ---- *)

Init ==
    /\ page_state = "CACHE"
    /\ in_flight  = FALSE
    /\ wb_pc      = "wb_start"
    /\ tr_pc      = "tr_start"

Next ==
    \/ WB_Start
    \/ WB_Complete
    \/ TR_Truncate

Spec == Init /\ [][Next]_vars

(* ---- Invariants ---- *)

(*
 * Safety: Page must not be FREEABLE while a write I/O is still in flight.
 *
 * Violation scenario (bug injected):
 *   1. WritebackThread: CACHE -> WRITEBACK, in_flight := TRUE
 *   2. TruncateThread:  no guard, sets FREEABLE while in_flight = TRUE
 *   3. State: page_state = FREEABLE, in_flight = TRUE  <-- violation
 *
 * The page has been reclaimed (FREEABLE) but the write RPC is still
 * referencing its data buffer.  On completion the RPC callback writes
 * into a potentially reused page -- data corruption.
 *)
NoStaleWrite ==
    ~(page_state = "FREEABLE" /\ in_flight = TRUE)

=============================================================================
