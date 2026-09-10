------------------------------- MODULE ClPage --------------------------------
(*
 * TLA+ model of the cl_page lifecycle in Lustre.
 *
 * Models the full reference counting, state machine, and vmpage
 * flag interactions for a single cacheable cl_page.
 *
 * Processes modeled:
 *   - WriteIO:    own -> make_ready -> submit -> complete -> disown
 *                 OR: own -> disown (flush failure, error)
 *   - ReadIO:     own -> prep(pagein) -> complete -> (set uptodate) -> disown
 *                 OR: own -> disown (error before submit)
 *   - ReadErrorIO: own -> submit -> error_complete -> discard -> disown
 *                 Models read completion with rc!=0: state goes to CPS_CACHED
 *                 but SetPageUptodate is NOT called.  On error the caller
 *                 (ll_io_read_page, rw.c:1722) calls cl_page_discard, which
 *                 calls cl_page_delete -> vvp_page_delete directly
 *                 (cl_page.c:920) and then generic_error_remove_folio
 *                 (cl_page.c:925).  The vvp_page_delete path bumps the
 *                 seqlock if the page was uptodate.
 *                 (LU-16935: this seqlock bump can cause infinite fault retry)
 *   - Delete:     own -> __cl_page_delete(FREEING) -> vvp_page_delete
 *                 (drop ref, clear private, seqlock+clear uptodate)
 *                 -> osc_page_delete (transfer_put) -> unlock
 *   - Fault:      read vmpage under seqlock, retry if invalidated
 *   - BL_AST:    blocking AST callback holds cl_page ref + vmpage ref
 *                 across the releasepage window (LU-16276 race)
 *
 * Reference sources:
 *   - alloc_ref:     from cl_page_alloc (initial ref, always 1)
 *   - vvp_ref:       from vvp_page_init (+1 for cacheable, dropped in delete)
 *   - transfer_ref:  from osc_page_transfer_get (during IO, dropped on complete)
 *   - bl_ast_ref:    from BL AST cl_page_get (held during lock callback)
 *
 * vmpage refcount tracking (vmpage_ref):
 *   Extra vmpage references beyond the page cache ref.
 *   BL AST callbacks do get_page(vmpage) which elevates the vmpage
 *   refcount.  This prevents __remove_mapping from freeing the page.
 *
 * vmpage flags modeled:
 *   - PagePrivate:   vmpage->private points to cl_page
 *   - PageUptodate:  page data is valid
 *   - PageLocked:    vmpage is locked (ownership implies this)
 *
 * Synchronization:
 *   - lli_page_inv_lock (seqlock): protects fault from stale uptodate
 *   - vmpage lock: required for ownership, prevents concurrent own/delete
 *
 * DELETE PATH IS SPLIT INTO FINE-GRAINED STEPS to expose races
 * between delete sub-operations and concurrent IO/faults.
 * The real execution order in __cl_page_delete is:
 *   1. cl_page_owner_clear + __cl_page_state_set(CPS_FREEING)
 *   2. vvp_page_delete: refcount_dec (drop vvp ref)
 *   3. vvp_page_delete: ClearPagePrivate + vmpage->private = 0
 *   4. vvp_page_delete: write_seqlock (seq -> odd)
 *   5. vvp_page_delete: ClearPageUptodate
 *   6. vvp_page_delete: write_sequnlock (seq -> even)
 *   7. osc_page_delete: osc_page_transfer_put
 *   8. unlock vmpage
 *
 * Lives:   formal_models/clio/
 *
 * Source (lustre-release master 47638add78):
 *   lustre/obdclass/cl_page.c
 *     __cl_page_state_set    470-527  allowed_transitions[][] 477-511
 *     cl_page_put            596-600  -> cl_batch_put
 *     __cl_page_disown       651-672  CPS_CACHED 665, unlock_page 669
 *     __cl_page_own          705-770  -ENOENT if FREEING (717-720);
 *                                     nonblock: trylock + PageWriteback
 *                                     -> -EAGAIN (726-735); blocking:
 *                                     lock_page + wait_on_page_writeback
 *                                     (737-738); CPS_OWNED at 756
 *     cl_page_assume         806-839  PageLocked precondition, waits on
 *                                     writeback (820), CPS_OWNED 822
 *     cl_page_discard        900-932  cpo_discard, then cl_page_delete
 *                                     (920), then generic_error_remove_folio
 *                                     (925)
 *     __cl_page_delete       934-960  CPS_FREEING 950, cpo_delete bottom-up
 *     cl_page_delete         984-991
 *     cl_page_io_start      1016-1024 owner_clear + PAGEIN/PAGEOUT
 *     cl_page_prep          1037-1071 read: -EALREADY if uptodate; write:
 *                                     set_page_writeback (1059) if async
 *     cl_page_complete      1106-1149 CPS_CACHED 1121, cpo_complete
 *                                     bottom-up (1123-1128)
 *     cl_page_make_ready    1152-1205 lock_page 1163, set_page_writeback
 *                                     1170, cl_page_io_start 1187,
 *                                     unlock_page 1191 (post LU-16612)
 *   lustre/llite/vvp_page.c
 *     vvp_page_discard        33-42   RA stats only (no delete here)
 *     vvp_page_delete         44-79   refcount_dec 58, ClearPagePrivate
 *                                     60, write_seqlock/ClearPageUptodate/
 *                                     write_sequnlock 69-73 only if
 *                                     PageUptodate (LU-16160, LU-16935)
 *     vvp_page_complete_read 118-157  SetPageUptodate 140 on rc==0
 *     vvp_page_complete_write 159-183 end_page_writeback 180
 *     vvp_page_init          201-225  refcount_inc 218, SetPagePrivate 219
 *   lustre/llite/llite_mmap.c
 *     ll_filemap_fault       245-261  read_seqbegin/read_seqretry loop
 *   lustre/llite/vvp_io.c
 *     vvp_io_read_start       ~880-921 seqlock retry around
 *                                     generic_file_read_iter (LU-16649)
 *   lustre/llite/rw26.c
 *     ll_invalidate_folio     48-87   LASSERT(!writeback), cl_page_delete
 *     do_release_page        147-198  PageWriteback/Dirty -> 0 (159);
 *                                     cl_page_in_use refcount check (170)
 *                                     before cl_page_delete
 *   lustre/llite/rw.c
 *     ll_io_read_page       1603-1740 cl_page_discard on !PageUptodate 1722
 *   lustre/osc/osc_page.c
 *     osc_page_transfer_get   36-43,  osc_page_transfer_put 45-54,
 *     osc_page_cache_add      56-70,  osc_page_delete 129-165 (put 140)
 *   lustre/osc/osc_cache.c
 *     osc_completion        1398-1451 direct ops_transfer_pinned clear
 *                                     1421, cl_page_complete 1446,
 *                                     cl_page_put 1448 (LU-19956 shape)
 *   lustre/include/cl_object.h
 *     __page_in_use/cl_page_in_use 981-993 (cp_ref > refc + 1)
 *
 * Validated against: lustre-release master 47638add78 (2026-09-06)
 * Validation notes:
 *   - The module previously defined PageoutHasWriteback and
 *     WritebackWindowConsistency twice (once in the base invariant
 *     block and again in the three-way race block), which SANY rejects
 *     ("Parsing or semantic analysis failed"), so none of the 34 cfgs
 *     could run.  The duplicate (identical) definitions were removed;
 *     no invariant semantics changed.
 *   - LU-19956 has NOT landed: Gerrit 64440 is NEW (ps14), 64472 is
 *     ABANDONED.  osc_completion in this tree still clears the pin
 *     directly and does an unconditional cl_page_put, i.e. the
 *     INJECT_BUGGY_TRANSFER=TRUE shape.  Note the model takes the
 *     transfer pin at make_ready (WriteMakeReady); in the code the
 *     pin for async writes is taken earlier, at osc_page_cache_add,
 *     and is held while the page sits CPS_CACHED in the extent.
 *     TransferPinOnlyDuringIO is therefore a model-level invariant.
 *   - LU-16276 is still Open.  The page_count()-based releasepage
 *     check (c524079f4f) was reverted by e3cfb688ed; the guard in
 *     this tree is do_release_page's cl_page_in_use() (cl_page
 *     refcount, rw26.c:170).  DeleteAbortVmref checks vmpage_ref,
 *     which is equivalent here only because BlAstGetRef raises
 *     cp_ref and vmpage_ref together.
 *   - LU-16935 fix (f5564c35ed) = bump the seqlock only when the page
 *     is PageUptodate (vvp_page.c:69-73) plus ci_tried_all_mirrors in
 *     cl_io_loop; there is no ci_dont_repeat.  DeleteSeqlockAcquire /
 *     RerrSeqlockAcquire already model the uptodate-only bump.
 *     INJECT_NO_ERROR_SEQLOCK is a hypothetical variant (drop the bump
 *     on the error path), not the historical LU-16935 code.
 *   - LU-4581's historical fix is 26345bee6b (LU-2779, uninterruptible
 *     osc_extent_wait so osc_lock_flush waits before discarding);
 *     in this tree __cl_page_own also waits on / rejects PageWriteback
 *     (cl_page.c:731-738) and ll_invalidate_folio asserts !writeback,
 *     which is what DeleteOwn's ~pg_writeback guard abstracts.
 *   - LU-16612 (d03b038d0d), LU-16160 (b4da788a81), LU-16649
 *     (1d98e5c32b), LU-14541 (f2a16793fa, b3d2114e53) are all present
 *     at the lines cited above.
 *
 * Bugs verified:
 *   LU-19956  - transfer pin race (see TransferPin.tla)
 *   LU-14541  - no ClearPageUptodate in delete (stale data after reclaim)
 *   LU-15815  - ClearPageUptodate without seqlock (fault races with delete)
 *   LU-16160  - seqlock fix for fault vs delete race
 *   LU-16935  - fault retry infinite loop when error path bumps seqlock
 *   LU-4581   - delete during PageWriteback (lock cancel vs async write)
 *   LU-16649  - buffered read without seqlock retry (EIO on page reclaim race)
 *   LU-16612  - cl_page_make_ready early unlock (readahead assume on CPS_OWNED)
 *   LU-19956  - transfer pin flag clear decoupled from ref drop (double-put)
 *   LU-16276  - BL AST holds vmpage ref across releasepage (__remove_mapping fail)
 *
 * Writeback+truncate+fault exploration (at9.30):
 *   Added 5 novel invariants targeting three-way race between write
 *   completion, truncate/delete, and page fault:
 *     PageoutHasWriteback          - CPS_PAGEOUT => PageWriteback set
 *     WritebackWindowConsistency   - wb_clearing => writeback + transfer pin held
 *     TruncateSeqlockProtectsFault - seqlock write-held => fault detects change
 *     NoWritebackDuringFreeing     - CPS_FREEING => PageWriteback clear
 *     FaultUptodateSeqlockConsistency - uptodate cleared => seqlock bumped for fault
 *   All 5 pass with correct code (5602 states, explore_wb_truncate_fault.cfg).
 *   Bug injection cfgs verify detection of LU-4581, LU-16160, LU-16935 via
 *   these new invariants. No novel bugs found -- existing fix code is correct.
 *)

EXTENDS Integers, TLC

CONSTANTS
    MAX_WRITES,     \* Number of write cycles to model
    MAX_READS,      \* Number of read cycles to model
    ENABLE_FAULT,   \* TRUE to model concurrent page faults
    ENABLE_ERROR,   \* TRUE to model read error completion path
    INJECT_NO_SEQLOCK,  \* TRUE to inject LU-16160 bug: no seqlock in delete
    INJECT_NO_WB_CHECK, \* TRUE to inject LU-4581 bug: delete without writeback check
    INJECT_NO_CLEAR_UPTODATE, \* TRUE to inject pre-LU-14541 bug: no ClearPageUptodate in delete
    INJECT_NO_ERROR_SEQLOCK,  \* TRUE to inject LU-16935 variant: error discard skips seqlock
    INJECT_NO_READ_SEQLOCK,   \* TRUE to inject LU-16649 bug: read() without seqlock retry
    INJECT_EARLY_UNLOCK,      \* TRUE to inject LU-16612 bug: unlock vmpage before io_start
    INJECT_BUGGY_TRANSFER,    \* TRUE to inject LU-19956 bug: flag clear decoupled from ref drop
    ENABLE_BL_AST,            \* TRUE to model BL AST callback holding vmpage ref
    INJECT_NO_VMREF_CHECK     \* TRUE to inject LU-16276 bug: releasepage ignores vmpage refcount

VARIABLES
    \* cl_page state
    page_state,         \* CPS_CACHED, CPS_OWNED, CPS_PAGEOUT, CPS_PAGEIN, CPS_FREEING
    cp_ref,             \* cl_page reference count

    \* Reference tracking (boolean: is this ref currently held?)
    vvp_ref,            \* vvp_page_init ref (cacheable pages)
    transfer_pinned,    \* ops_transfer_pinned flag + ref

    \* vmpage flags
    pg_private,         \* PagePrivate (vmpage->private = cl_page)
    pg_uptodate,        \* PageUptodate (page data valid)
    pg_locked,          \* PageLocked (vmpage lock held)
    pg_writeback,       \* PageWriteback (async write in progress)

    \* Seqlock counter (even = unlocked, odd = write-locked)
    inv_seq,            \* lli_page_inv_lock sequence number

    \* Process program counters
    write_pc,
    read_pc,
    delete_pc,
    fault_pc,
    rerr_pc,            \* Read error completion process

    \* Counters for bounding
    write_count,
    read_count,

    \* Fault-local state
    fault_seq,          \* Sequence number captured by fault at read_seqbegin
    fault_private,      \* pg_private value captured when fault "reads" the page

    \* BL AST callback state
    vmpage_ref,         \* Extra vmpage references beyond page cache (e.g., from BL AST)
    bl_ast_pc           \* BL AST process program counter

vars == <<page_state, cp_ref, vvp_ref, transfer_pinned,
          pg_private, pg_uptodate, pg_locked, pg_writeback,
          inv_seq, write_pc, read_pc, delete_pc, fault_pc,
          rerr_pc, write_count, read_count, fault_seq,
          fault_private, vmpage_ref, bl_ast_pc>>

(* ================================================================
 * Initial state: page just allocated and initialized.
 * cl_page_alloc gives ref=1, vvp_page_init adds ref+1 and sets
 * PagePrivate.  Page starts in CPS_CACHED.
 * ================================================================ *)
Init ==
    /\ page_state = "CPS_CACHED"
    /\ cp_ref = 2              \* alloc(1) + vvp_init(+1)
    /\ vvp_ref = TRUE
    /\ transfer_pinned = FALSE
    /\ pg_private = TRUE       \* vvp_page_init: SetPagePrivate
    /\ pg_uptodate = FALSE     \* Fresh page, not yet read
    /\ pg_locked = FALSE
    /\ pg_writeback = FALSE
    /\ inv_seq = 0             \* Even = unlocked
    /\ write_pc = "idle"
    /\ read_pc = "idle"
    /\ delete_pc = "idle"
    /\ fault_pc = "idle"
    /\ rerr_pc = "idle"
    /\ write_count = 0
    /\ read_count = 0
    /\ fault_seq = 0
    /\ fault_private = TRUE
    /\ vmpage_ref = 0
    /\ bl_ast_pc = "idle"

(* ================================================================
 * WRITE IO: own -> make_ready(PAGEOUT) -> complete(CACHED) -> put
 *           OR: own -> disown (error/abort before submission)
 *
 * Models the async write path: page is owned, prepared for
 * write-out, submitted with transfer pin, completed on RPC
 * return, then released.
 *
 * The disown path models cl_page_disown: CPS_OWNED -> CPS_CACHED,
 * unlock vmpage.  This happens when cl_page_flush fails or when
 * the page cannot be submitted for any reason.
 * (Source: __cl_page_disown in cl_page.c:651-672)
 * ================================================================ *)

\* Step 1: cl_page_own - lock vmpage, set CPS_OWNED
WriteOwn ==
    /\ write_pc = "idle"
    /\ write_count < MAX_WRITES
    /\ page_state = "CPS_CACHED"
    /\ ~pg_locked                 \* vmpage must be unlocked
    /\ pg_private                 \* Must still be a Lustre page
    /\ pg_locked' = TRUE          \* lock_page()
    /\ page_state' = "CPS_OWNED"
    /\ write_pc' = "owned"
    /\ write_count' = write_count + 1
    /\ UNCHANGED <<cp_ref, vvp_ref, transfer_pinned, pg_private,
                   pg_uptodate, pg_writeback, inv_seq, read_pc, delete_pc,
                   fault_pc, rerr_pc, read_count, fault_seq, fault_private,
                   vmpage_ref, bl_ast_pc>>

\* Step 2a: cl_page_make_ready -> CPS_PAGEOUT (normal path, fix)
\* Also does osc_page_transfer_get (pin + ref)
\* SetPageWriteback is called during submission (before unlock_page)
\*
\* After LU-16612 fix: vmpage stays locked until AFTER cl_page_io_start
\* sets CPS_PAGEOUT.  This prevents readahead from locking the vmpage
\* while the page is still CPS_OWNED.
\*
\* INJECT_EARLY_UNLOCK splits this into two steps:
\*   WriteMakeReadyEarlyUnlock: unlock vmpage while still CPS_OWNED (bug)
\*   WriteMakeReadySubmit: set CPS_PAGEOUT + transfer pin + writeback
WriteMakeReady ==
    /\ ~INJECT_EARLY_UNLOCK       \* Only when fix is active
    /\ write_pc = "owned"
    /\ page_state = "CPS_OWNED"
    /\ ~transfer_pinned
    /\ page_state' = "CPS_PAGEOUT"
    /\ transfer_pinned' = TRUE
    /\ cp_ref' = cp_ref + 1      \* transfer pin ref
    /\ pg_locked' = FALSE         \* unlock_page after io_start (fix)
    /\ pg_writeback' = TRUE       \* SetPageWriteback
    /\ write_pc' = "pageout"
    /\ UNCHANGED <<vvp_ref, pg_private, pg_uptodate, inv_seq,
                   read_pc, delete_pc, fault_pc, rerr_pc, write_count,
                   read_count, fault_seq, fault_private,
                   vmpage_ref, bl_ast_pc>>

\* Step 2a-bug: LU-16612 early unlock (pre-fix cl_page_make_ready)
\* Before the fix, cl_page_make_ready called unlock_page(vmpage)
\* BEFORE cl_page_io_start.  This created a window where the page
\* is CPS_OWNED but the vmpage is unlocked.  During this window,
\* readahead (ll_read_ahead_page) can lock the vmpage and call
\* cl_page_assume, which LBUGs on the CPS_OWNED -> CPS_OWNED
\* invalid state transition.
\*
\* Source: cl_page_make_ready (cl_page.c) before fix d03b038d0d; the
\* fixed function is cl_page.c:1152-1205 (unlock_page at 1191, after
\* cl_page_io_start at 1187)
WriteMakeReadyEarlyUnlock ==
    /\ INJECT_EARLY_UNLOCK        \* Only in bug-injection mode
    /\ write_pc = "owned"
    /\ page_state = "CPS_OWNED"
    /\ ~transfer_pinned
    /\ pg_locked' = FALSE         \* BUG: unlock_page BEFORE io_start
    /\ write_pc' = "unlocked_early"
    /\ UNCHANGED <<page_state, cp_ref, vvp_ref, transfer_pinned,
                   pg_private, pg_uptodate, pg_writeback, inv_seq,
                   read_pc, delete_pc, fault_pc, rerr_pc, write_count,
                   read_count, fault_seq, fault_private,
                   vmpage_ref, bl_ast_pc>>

\* Step 2a-bug continued: cl_page_io_start after early unlock
\* Sets CPS_PAGEOUT + transfer pin + writeback.  But by now,
\* readahead may have already locked the vmpage and called assume.
WriteMakeReadySubmit ==
    /\ INJECT_EARLY_UNLOCK
    /\ write_pc = "unlocked_early"
    /\ page_state = "CPS_OWNED"  \* Still OWNED (if no race happened)
    /\ page_state' = "CPS_PAGEOUT"
    /\ transfer_pinned' = TRUE
    /\ cp_ref' = cp_ref + 1
    /\ pg_writeback' = TRUE
    /\ write_pc' = "pageout"
    /\ UNCHANGED <<vvp_ref, pg_private, pg_uptodate, pg_locked, inv_seq,
                   read_pc, delete_pc, fault_pc, rerr_pc, write_count,
                   read_count, fault_seq, fault_private,
                   vmpage_ref, bl_ast_pc>>

\* Step 2b: Disown without IO (error/abort path)
\* cl_page_disown: CPS_OWNED -> CPS_CACHED, unlock vmpage
\* This happens when cl_page_flush() fails, or the page cannot be
\* submitted.  No transfer pin was taken, no state change to PAGEOUT.
WriteDisown ==
    /\ write_pc = "owned"
    /\ page_state = "CPS_OWNED"
    /\ page_state' = "CPS_CACHED"
    /\ pg_locked' = FALSE         \* unlock_page in __cl_page_disown
    /\ write_pc' = "done"
    /\ UNCHANGED <<cp_ref, vvp_ref, transfer_pinned, pg_private,
                   pg_uptodate, pg_writeback, inv_seq, read_pc, delete_pc,
                   fault_pc, rerr_pc, write_count, read_count,
                   fault_seq, fault_private,
                   vmpage_ref, bl_ast_pc>>

\* Step 3a: cl_page_complete (RPC done) -> CPS_CACHED
\* osc_completion calls cl_page_complete which sets CPS_CACHED.
\* end_page_writeback is called separately in vvp_page_complete_write.
\* There is a window between these where page_state = CPS_CACHED
\* but PageWriteback is still set.  This is the LU-4581 race window.
WriteComplete ==
    /\ write_pc = "pageout"
    /\ page_state = "CPS_PAGEOUT"
    /\ page_state' = "CPS_CACHED"
    /\ write_pc' = "wb_clearing"
    /\ UNCHANGED <<cp_ref, vvp_ref, transfer_pinned, pg_private,
                   pg_uptodate, pg_locked, pg_writeback, inv_seq, read_pc,
                   delete_pc, fault_pc, rerr_pc, write_count, read_count,
                   fault_seq, fault_private,
                   vmpage_ref, bl_ast_pc>>

\* Step 3b: end_page_writeback (clears PageWriteback)
\* vvp_page_complete_write calls end_page_writeback after cl_page_complete.
WriteEndWriteback ==
    /\ write_pc = "wb_clearing"
    /\ pg_writeback' = FALSE      \* end_page_writeback()
    /\ write_pc' = "completed"
    /\ UNCHANGED <<page_state, cp_ref, vvp_ref, transfer_pinned, pg_private,
                   pg_uptodate, pg_locked, inv_seq, read_pc,
                   delete_pc, fault_pc, rerr_pc, write_count, read_count,
                   fault_seq, fault_private,
                   vmpage_ref, bl_ast_pc>>

\* Step 4: osc_page_transfer_put (clear pin + drop ref)
\* Post-LU-19956 fix (v64440): idempotent transfer_put.
\* Flag and ref are dropped together atomically.
WriteTransferPut ==
    /\ ~INJECT_BUGGY_TRANSFER     \* Only in fix mode
    /\ write_pc = "completed"
    /\ IF transfer_pinned
       THEN /\ transfer_pinned' = FALSE
            /\ cp_ref' = cp_ref - 1
       ELSE /\ UNCHANGED <<transfer_pinned, cp_ref>>
    /\ write_pc' = "done"
    /\ UNCHANGED <<page_state, vvp_ref, pg_private, pg_uptodate,
                   pg_locked, pg_writeback, inv_seq, read_pc, delete_pc,
                   fault_pc, rerr_pc, write_count, read_count,
                   fault_seq, fault_private,
                   vmpage_ref, bl_ast_pc>>

\* Step 4-bug: LU-19956 buggy completion (pre-fix osc_completion)
\*
\* Original code:
\*   opg->ops_transfer_pinned = 0;   // store A (can be delayed)
\*   cl_page_complete(page);          // store B (state -> CACHED)
\*   cl_page_put(page);              // unconditional ref drop
\*
\* On weakly-ordered architectures (aarch64), store A can be
\* reordered after store B.  The model captures this by making
\* the flag clear a separate step that can interleave with
\* delete.  Delete sees CPS_CACHED + transfer_pinned=TRUE,
\* calls transfer_put (drops ref), then completion's
\* unconditional put double-drops the ref.
\*
\* In the model, WriteComplete already set CPS_CACHED (store B
\* happened).  Now the flag clear (store A) becomes visible.
WriteBuggyFlagClear ==
    /\ INJECT_BUGGY_TRANSFER
    /\ write_pc = "completed"
    /\ transfer_pinned' = FALSE
    /\ write_pc' = "buggy_flag_cleared"
    /\ UNCHANGED <<page_state, cp_ref, vvp_ref, pg_private,
                   pg_uptodate, pg_locked, pg_writeback, inv_seq,
                   read_pc, delete_pc, fault_pc, rerr_pc,
                   write_count, read_count, fault_seq, fault_private,
                   vmpage_ref, bl_ast_pc>>

\* Step 4-bug continued: unconditional cl_page_put
\* The original code always dropped a ref here, regardless of
\* whether transfer_put already ran.  If delete interleaved
\* and called transfer_put first, this is a double-drop.
WriteBuggyPut ==
    /\ INJECT_BUGGY_TRANSFER
    /\ write_pc = "buggy_flag_cleared"
    /\ cp_ref' = cp_ref - 1          \* Unconditional: always drops ref
    /\ write_pc' = "done"
    /\ UNCHANGED <<page_state, vvp_ref, transfer_pinned, pg_private,
                   pg_uptodate, pg_locked, pg_writeback, inv_seq,
                   read_pc, delete_pc, fault_pc, rerr_pc,
                   write_count, read_count, fault_seq, fault_private,
                   vmpage_ref, bl_ast_pc>>

WriteReset ==
    /\ write_pc = "done"
    /\ write_pc' = "idle"
    /\ UNCHANGED <<page_state, cp_ref, vvp_ref, transfer_pinned,
                   pg_private, pg_uptodate, pg_locked, pg_writeback, inv_seq,
                   read_pc, delete_pc, fault_pc, rerr_pc, write_count,
                   read_count, fault_seq, fault_private,
                   vmpage_ref, bl_ast_pc>>

(* ================================================================
 * READ IO: own -> prep(PAGEIN) -> complete(CACHED, set uptodate)
 *          -> transfer_put -> disown
 *          OR: own -> disown (error before submit)
 *
 * Models the synchronous read path.  Transfer pin is taken at
 * submit time (osc_page_submit), completed in osc_completion.
 * Read completion sets PageUptodate on success.
 *
 * The disown path models early error: page is owned but submission
 * fails, so it goes straight back to CPS_CACHED.
 * ================================================================ *)

ReadOwn ==
    /\ read_pc = "idle"
    /\ read_count < MAX_READS
    /\ page_state = "CPS_CACHED"
    /\ ~pg_locked
    /\ pg_private
    /\ ~pg_uptodate              \* Only read if not already uptodate
    /\ pg_locked' = TRUE
    /\ page_state' = "CPS_OWNED"
    /\ read_pc' = "owned"
    /\ read_count' = read_count + 1
    /\ UNCHANGED <<cp_ref, vvp_ref, transfer_pinned, pg_private,
                   pg_uptodate, pg_writeback, inv_seq, write_pc, delete_pc,
                   fault_pc, rerr_pc, write_count, fault_seq, fault_private,
                   vmpage_ref, bl_ast_pc>>

\* Prep + submit: OWNED -> PAGEIN, take transfer pin
ReadSubmit ==
    /\ read_pc = "owned"
    /\ page_state = "CPS_OWNED"
    /\ ~transfer_pinned
    /\ page_state' = "CPS_PAGEIN"
    /\ transfer_pinned' = TRUE
    /\ cp_ref' = cp_ref + 1
    /\ pg_locked' = FALSE         \* Unlock after submit
    /\ read_pc' = "pagein"
    /\ UNCHANGED <<vvp_ref, pg_private, pg_uptodate, pg_writeback, inv_seq,
                   write_pc, delete_pc, fault_pc, rerr_pc, write_count,
                   read_count, fault_seq, fault_private,
                   vmpage_ref, bl_ast_pc>>

\* Disown without IO (error before submit)
ReadDisown ==
    /\ read_pc = "owned"
    /\ page_state = "CPS_OWNED"
    /\ page_state' = "CPS_CACHED"
    /\ pg_locked' = FALSE
    /\ read_pc' = "done"
    /\ UNCHANGED <<cp_ref, vvp_ref, transfer_pinned, pg_private,
                   pg_uptodate, pg_writeback, inv_seq, write_pc, delete_pc,
                   fault_pc, rerr_pc, write_count, read_count,
                   fault_seq, fault_private,
                   vmpage_ref, bl_ast_pc>>

\* Complete: PAGEIN -> CACHED, set PageUptodate (success path)
ReadComplete ==
    /\ read_pc = "pagein"
    /\ page_state = "CPS_PAGEIN"
    /\ page_state' = "CPS_CACHED"
    /\ pg_uptodate' = TRUE        \* SetPageUptodate (non-RA path)
    /\ read_pc' = "completed"
    /\ UNCHANGED <<cp_ref, vvp_ref, transfer_pinned, pg_private,
                   pg_locked, pg_writeback, inv_seq, write_pc, delete_pc,
                   fault_pc, rerr_pc, write_count, read_count,
                   fault_seq, fault_private,
                   vmpage_ref, bl_ast_pc>>

\* Transfer put after complete
ReadTransferPut ==
    /\ read_pc = "completed"
    /\ IF transfer_pinned
       THEN /\ transfer_pinned' = FALSE
            /\ cp_ref' = cp_ref - 1
       ELSE /\ UNCHANGED <<transfer_pinned, cp_ref>>
    /\ read_pc' = "done"
    /\ UNCHANGED <<page_state, vvp_ref, pg_private, pg_uptodate,
                   pg_locked, pg_writeback, inv_seq, write_pc, delete_pc,
                   fault_pc, rerr_pc, write_count, read_count,
                   fault_seq, fault_private,
                   vmpage_ref, bl_ast_pc>>

ReadReset ==
    /\ read_pc = "done"
    /\ read_pc' = "idle"
    /\ UNCHANGED <<page_state, cp_ref, vvp_ref, transfer_pinned,
                   pg_private, pg_uptodate, pg_locked, pg_writeback, inv_seq,
                   write_pc, delete_pc, fault_pc, rerr_pc, write_count,
                   read_count, fault_seq, fault_private,
                   vmpage_ref, bl_ast_pc>>

(* ================================================================
 * READ ERROR COMPLETION: models read with rc != 0
 *
 * When read completes with error:
 *   1. cl_page_complete: PAGEIN -> CACHED (always, regardless of rc)
 *   2. vvp_page_complete_read: does NOT call SetPageUptodate
 *   3. osc_page_transfer_put: clears pin, drops ref
 *   4. Caller discovers !PageUptodate, calls cl_page_discard
 *   5. cl_page_discard runs cpo_discard (vvp_page_discard: RA stats
 *      only) then calls cl_page_delete directly (cl_page.c:920)
 *   6. cl_page_delete -> vvp_page_delete bumps seqlock (if uptodate)
 *   7. cl_page_discard then calls generic_error_remove_folio
 *      (cl_page.c:925); ll_invalidate_folio finds no cl_page
 *
 * LU-16935: This seqlock bump during error discard creates a
 * bug where ll_filemap_fault's seqlock retry loop becomes
 * infinite: every retry triggers the same error, which discards
 * the page, which bumps the seqlock, which triggers another retry.
 *
 * The model tracks this as a separate process because the error
 * path has fundamentally different behavior from the success path
 * (no SetPageUptodate, triggers discard chain).
 *
 * Source: vvp_page_complete_read (vvp_page.c:118-157)
 *         ll_io_read_page error path (rw.c:1603-1740, discard at 1722)
 *         cl_page_discard (cl_page.c:900-932)
 * ================================================================ *)

\* Step 1: Own page for error read
\* NOTE: ~pg_uptodate NOT required. Error reads can happen on
\* previously-uptodate pages (FLR mirror switching, eviction re-read).
\* This is key for LU-16935: fault starts on uptodate page, error
\* re-read fails, discard bumps seqlock.
RerrOwn ==
    /\ ENABLE_ERROR
    /\ rerr_pc = "idle"
    /\ read_count < MAX_READS
    /\ page_state = "CPS_CACHED"
    /\ ~pg_locked
    /\ pg_private
    /\ pg_locked' = TRUE
    /\ page_state' = "CPS_OWNED"
    /\ rerr_pc' = "owned"
    /\ read_count' = read_count + 1
    /\ UNCHANGED <<cp_ref, vvp_ref, transfer_pinned, pg_private,
                   pg_uptodate, pg_writeback, inv_seq, write_pc, read_pc, delete_pc,
                   fault_pc, write_count, fault_seq, fault_private,
                   vmpage_ref, bl_ast_pc>>

\* Step 2: Submit read (OWNED -> PAGEIN, take transfer pin)
RerrSubmit ==
    /\ ENABLE_ERROR
    /\ rerr_pc = "owned"
    /\ page_state = "CPS_OWNED"
    /\ ~transfer_pinned
    /\ page_state' = "CPS_PAGEIN"
    /\ transfer_pinned' = TRUE
    /\ cp_ref' = cp_ref + 1
    /\ pg_locked' = FALSE
    /\ rerr_pc' = "pagein"
    /\ UNCHANGED <<vvp_ref, pg_private, pg_uptodate, pg_writeback, inv_seq,
                   write_pc, read_pc, delete_pc, fault_pc, write_count,
                   read_count, fault_seq, fault_private,
                   vmpage_ref, bl_ast_pc>>

\* Step 3: Error completion: PAGEIN -> CACHED, but NO SetPageUptodate
\* cl_page_complete unconditionally sets CPS_CACHED (cl_page.c:1121)
\* vvp_page_complete_read skips SetPageUptodate on error
RerrComplete ==
    /\ ENABLE_ERROR
    /\ rerr_pc = "pagein"
    /\ page_state = "CPS_PAGEIN"
    /\ page_state' = "CPS_CACHED"
    \* NOTE: pg_uptodate NOT set (error path)
    /\ rerr_pc' = "completed"
    /\ UNCHANGED <<cp_ref, vvp_ref, transfer_pinned, pg_private,
                   pg_uptodate, pg_locked, pg_writeback, inv_seq, write_pc, read_pc,
                   delete_pc, fault_pc, write_count, read_count,
                   fault_seq, fault_private,
                   vmpage_ref, bl_ast_pc>>

\* Step 4: Transfer put after error completion
RerrTransferPut ==
    /\ ENABLE_ERROR
    /\ rerr_pc = "completed"
    /\ IF transfer_pinned
       THEN /\ transfer_pinned' = FALSE
            /\ cp_ref' = cp_ref - 1
       ELSE /\ UNCHANGED <<transfer_pinned, cp_ref>>
    /\ rerr_pc' = "put_done"
    /\ UNCHANGED <<page_state, vvp_ref, pg_private, pg_uptodate,
                   pg_locked, pg_writeback, inv_seq, write_pc, read_pc,
                   delete_pc, fault_pc, write_count, read_count,
                   fault_seq, fault_private,
                   vmpage_ref, bl_ast_pc>>

\* Step 5: Caller discovers !PageUptodate, calls cl_page_discard
\* -> cl_page_delete -> vvp_page_delete (cl_page.c:920), then
\* generic_error_remove_folio (cl_page.c:925)
\*
\* This is a delete-via-discard: it calls vvp_page_delete which
\* drops the vvp ref, clears PagePrivate, and bumps the seqlock
\* to clear PageUptodate.
\*
\* We model this as: own the page (already owned from read context),
\* set CPS_FREEING, then run through vvp_page_delete steps.
\*
\* In the real code, the page is already locked (from the read path),
\* so we go straight to CPS_FREEING.
RerrSetFreeing ==
    /\ ENABLE_ERROR
    /\ rerr_pc = "put_done"
    /\ page_state = "CPS_CACHED"  \* After complete, page is CACHED
    /\ pg_locked = FALSE           \* Need to lock for delete
    /\ IF ~INJECT_NO_WB_CHECK
       THEN ~pg_writeback          \* VFS: !PageWriteback required
       ELSE TRUE                   \* BUG: skip writeback check
    /\ pg_locked' = TRUE
    /\ page_state' = "CPS_FREEING"
    /\ rerr_pc' = "err_freeing"
    /\ UNCHANGED <<cp_ref, vvp_ref, transfer_pinned, pg_private,
                   pg_uptodate, pg_writeback, inv_seq, write_pc, read_pc,
                   delete_pc, fault_pc, write_count, read_count,
                   fault_seq, fault_private,
                   vmpage_ref, bl_ast_pc>>

\* Step 6: vvp_page_delete - drop vvp ref
RerrVvpDropRef ==
    /\ ENABLE_ERROR
    /\ rerr_pc = "err_freeing"
    /\ vvp_ref = TRUE
    /\ vvp_ref' = FALSE
    /\ cp_ref' = cp_ref - 1
    /\ rerr_pc' = "err_vvp_dropped"
    /\ UNCHANGED <<page_state, transfer_pinned, pg_private,
                   pg_uptodate, pg_locked, pg_writeback, inv_seq, write_pc,
                   read_pc, delete_pc, fault_pc, write_count,
                   read_count, fault_seq, fault_private,
                   vmpage_ref, bl_ast_pc>>

\* Step 7: vvp_page_delete - ClearPagePrivate
RerrClearPrivate ==
    /\ ENABLE_ERROR
    /\ rerr_pc = "err_vvp_dropped"
    /\ pg_private' = FALSE
    /\ rerr_pc' = "err_private_cleared"
    /\ UNCHANGED <<page_state, cp_ref, vvp_ref, transfer_pinned,
                   pg_uptodate, pg_locked, pg_writeback, inv_seq, write_pc,
                   read_pc, delete_pc, fault_pc, write_count,
                   read_count, fault_seq, fault_private,
                   vmpage_ref, bl_ast_pc>>

\* Step 8: vvp_page_delete - seqlock acquire/skip
\* Takes seqlock if page is uptodate (to protect concurrent faults).
\* INJECT_NO_ERROR_SEQLOCK: skips seqlock in error path, allowing
\* fault to miss the invalidation (LU-16935 demonstrates why the
\* seqlock bump is necessary for safety).
RerrSeqlockAcquire ==
    /\ ENABLE_ERROR
    /\ rerr_pc = "err_private_cleared"
    /\ IF INJECT_NO_ERROR_SEQLOCK
       THEN \* BUG: skip seqlock in error path
            /\ IF pg_uptodate
               THEN /\ rerr_pc' = "err_seqlock_held"
               ELSE /\ rerr_pc' = "err_uptodate_cleared"
            /\ UNCHANGED inv_seq
       ELSE IF pg_uptodate
            THEN /\ inv_seq' = inv_seq + 1
                 /\ rerr_pc' = "err_seqlock_held"
            ELSE /\ rerr_pc' = "err_uptodate_cleared"
                 /\ UNCHANGED inv_seq
    /\ UNCHANGED <<page_state, cp_ref, vvp_ref, transfer_pinned,
                   pg_private, pg_uptodate, pg_locked, pg_writeback, write_pc,
                   read_pc, delete_pc, fault_pc, write_count,
                   read_count, fault_seq, fault_private,
                   vmpage_ref, bl_ast_pc>>

\* Step 9: ClearPageUptodate
RerrClearUptodate ==
    /\ ENABLE_ERROR
    /\ rerr_pc = "err_seqlock_held"
    /\ IF INJECT_NO_CLEAR_UPTODATE
       THEN /\ UNCHANGED pg_uptodate
       ELSE /\ pg_uptodate' = FALSE
    /\ rerr_pc' = "err_seqlock_clearing"
    /\ UNCHANGED <<page_state, cp_ref, vvp_ref, transfer_pinned,
                   pg_private, pg_locked, pg_writeback, inv_seq, write_pc,
                   read_pc, delete_pc, fault_pc, write_count,
                   read_count, fault_seq, fault_private,
                   vmpage_ref, bl_ast_pc>>

\* Step 10: write_sequnlock
\* INJECT_NO_ERROR_SEQLOCK: no unlock (seqlock was never taken)
RerrSeqlockRelease ==
    /\ ENABLE_ERROR
    /\ rerr_pc = "err_seqlock_clearing"
    /\ IF INJECT_NO_ERROR_SEQLOCK
       THEN /\ UNCHANGED inv_seq
       ELSE /\ inv_seq' = inv_seq + 1
    /\ rerr_pc' = "err_uptodate_cleared"
    /\ UNCHANGED <<page_state, cp_ref, vvp_ref, transfer_pinned,
                   pg_private, pg_uptodate, pg_locked, pg_writeback, write_pc,
                   read_pc, delete_pc, fault_pc, write_count,
                   read_count, fault_seq, fault_private,
                   vmpage_ref, bl_ast_pc>>

\* Step 11: osc_page_delete transfer_put (idempotent)
RerrOscTransferPut ==
    /\ ENABLE_ERROR
    /\ rerr_pc = "err_uptodate_cleared"
    /\ IF transfer_pinned
       THEN /\ transfer_pinned' = FALSE
            /\ cp_ref' = cp_ref - 1
       ELSE /\ UNCHANGED <<transfer_pinned, cp_ref>>
    /\ rerr_pc' = "err_osc_done"
    /\ UNCHANGED <<page_state, vvp_ref, pg_private, pg_uptodate,
                   pg_locked, pg_writeback, inv_seq, write_pc, read_pc,
                   delete_pc, fault_pc, write_count, read_count,
                   fault_seq, fault_private,
                   vmpage_ref, bl_ast_pc>>

\* Step 12: Unlock vmpage
RerrUnlock ==
    /\ ENABLE_ERROR
    /\ rerr_pc = "err_osc_done"
    /\ pg_locked' = FALSE
    /\ rerr_pc' = "done"
    /\ UNCHANGED <<page_state, cp_ref, vvp_ref, transfer_pinned,
                   pg_private, pg_uptodate, pg_writeback, inv_seq, write_pc,
                   read_pc, delete_pc, fault_pc, write_count,
                   read_count, fault_seq, fault_private,
                   vmpage_ref, bl_ast_pc>>

RerrReset ==
    /\ ENABLE_ERROR
    /\ rerr_pc = "done"
    /\ rerr_pc' = "idle"
    /\ UNCHANGED <<page_state, cp_ref, vvp_ref, transfer_pinned,
                   pg_private, pg_uptodate, pg_locked, pg_writeback, inv_seq,
                   write_pc, read_pc, delete_pc, fault_pc,
                   write_count, read_count, fault_seq, fault_private,
                   vmpage_ref, bl_ast_pc>>

(* ================================================================
 * DELETE: cl_page_own -> __cl_page_delete -> vvp_page_delete
 *         -> osc_page_delete -> unlock
 *
 * Split into fine-grained steps to expose races between delete
 * sub-operations and concurrent IO completion / page faults.
 *
 * Real execution order (all on same CPU, vmpage locked):
 *   1. __cl_page_delete: owner_clear + set CPS_FREEING
 *   2. vvp_page_delete: refcount_dec (drop vvp ref)
 *   3. vvp_page_delete: ClearPagePrivate + vmpage->private = 0
 *   4. vvp_page_delete: if (PageUptodate) write_seqlock
 *   5. vvp_page_delete: ClearPageUptodate
 *   6. vvp_page_delete: write_sequnlock
 *   7. osc_page_delete: osc_page_transfer_put
 *   (vmpage remains locked throughout -- unlocked by caller)
 *
 * NOTE: vmpage is locked throughout delete, so no other thread
 * can own the page or start a new IO.  But:
 * - A fault can read vmpage state without holding the page lock
 * - IO completion runs on a different CPU and doesn't need the lock
 * - The seqlock is the only thing protecting faults from seeing
 *   stale uptodate after delete clears it.
 * ================================================================ *)

\* Step 1: Own for delete (lock vmpage, CPS_CACHED -> CPS_OWNED)
\* VFS guarantees: LASSERT(!PageWriteback(vmpage)) in ll_invalidatepage
DeleteOwn ==
    /\ delete_pc = "idle"
    /\ page_state = "CPS_CACHED"
    /\ ~pg_locked
    /\ IF ~INJECT_NO_WB_CHECK
       THEN ~pg_writeback         \* VFS: !PageWriteback required
       ELSE TRUE                  \* BUG: skip writeback check
    /\ pg_private
    /\ pg_locked' = TRUE
    /\ page_state' = "CPS_OWNED"
    /\ delete_pc' = "owned"
    /\ UNCHANGED <<cp_ref, vvp_ref, transfer_pinned, pg_private,
                   pg_uptodate, pg_writeback, inv_seq, write_pc, read_pc,
                   fault_pc, rerr_pc, write_count, read_count,
                   fault_seq, fault_private,
                   vmpage_ref, bl_ast_pc>>

\* Step 2: __cl_page_delete sets CPS_FREEING
\* cl_page_owner_clear + __cl_page_state_set(CPS_FREEING)
\* After this, no new ownership can be acquired (cl_page_own
\* checks state != CPS_FREEING).
DeleteSetFreeing ==
    /\ delete_pc = "owned"
    /\ page_state = "CPS_OWNED"
    /\ IF ~INJECT_NO_VMREF_CHECK
       THEN vmpage_ref = 0          \* FIX: check page_count before delete
       ELSE TRUE                    \* BUG: no vmpage refcount check
    /\ page_state' = "CPS_FREEING"
    /\ delete_pc' = "freeing"
    /\ UNCHANGED <<cp_ref, vvp_ref, transfer_pinned, pg_private,
                   pg_uptodate, pg_locked, pg_writeback, inv_seq, write_pc,
                   read_pc, fault_pc, rerr_pc, write_count, read_count,
                   fault_seq, fault_private,
                   vmpage_ref, bl_ast_pc>>

\* Step 3: vvp_page_delete - drop vvp ref
\* refcount_dec(&cp->cp_ref)
DeleteVvpDropRef ==
    /\ delete_pc = "freeing"
    /\ vvp_ref = TRUE
    /\ vvp_ref' = FALSE
    /\ cp_ref' = cp_ref - 1
    /\ delete_pc' = "vvp_ref_dropped"
    /\ UNCHANGED <<page_state, transfer_pinned, pg_private,
                   pg_uptodate, pg_locked, pg_writeback, inv_seq, write_pc,
                   read_pc, fault_pc, rerr_pc, write_count, read_count,
                   fault_seq, fault_private,
                   vmpage_ref, bl_ast_pc>>

\* Step 4: vvp_page_delete - ClearPagePrivate + vmpage->private = 0
\* Severs the vmpage -> cl_page association.  After this,
\* cl_vmpage_page() returns NULL for this vmpage.
DeleteClearPrivate ==
    /\ delete_pc = "vvp_ref_dropped"
    /\ pg_private' = FALSE
    /\ delete_pc' = "private_cleared"
    /\ UNCHANGED <<page_state, cp_ref, vvp_ref, transfer_pinned,
                   pg_uptodate, pg_locked, pg_writeback, inv_seq, write_pc,
                   read_pc, fault_pc, rerr_pc, write_count, read_count,
                   fault_seq, fault_private,
                   vmpage_ref, bl_ast_pc>>

\* Step 5: vvp_page_delete - write_seqlock (seq becomes odd)
\* Only taken if page was uptodate.  If not uptodate, skip to
\* osc_page_delete.
\* INJECT_NO_SEQLOCK: skips seqlock entirely (pre-LU-16160 bug)
DeleteSeqlockAcquire ==
    /\ delete_pc = "private_cleared"
    /\ IF INJECT_NO_SEQLOCK
       THEN \* BUG: no seqlock, go straight to clearing uptodate
            /\ delete_pc' = "seqlock_held"  \* Reuse label, but no seq bump
            /\ UNCHANGED inv_seq
       ELSE IF pg_uptodate
            THEN /\ inv_seq' = inv_seq + 1   \* seq -> odd (write-locked)
                 /\ delete_pc' = "seqlock_held"
            ELSE \* Skip seqlock entirely if not uptodate
                 /\ delete_pc' = "uptodate_cleared"
                 /\ UNCHANGED inv_seq
    /\ UNCHANGED <<page_state, cp_ref, vvp_ref, transfer_pinned,
                   pg_private, pg_uptodate, pg_locked, pg_writeback, write_pc,
                   read_pc, fault_pc, rerr_pc, write_count, read_count,
                   fault_seq, fault_private,
                   vmpage_ref, bl_ast_pc>>

\* Step 6: vvp_page_delete - ClearPageUptodate
\* INJECT_NO_CLEAR_UPTODATE: skips ClearPageUptodate entirely
\* (pre-LU-14541: vvp_page_delete did not clear uptodate)
DeleteClearUptodate ==
    /\ delete_pc = "seqlock_held"
    /\ IF INJECT_NO_CLEAR_UPTODATE
       THEN /\ UNCHANGED pg_uptodate  \* BUG: stale uptodate after delete
       ELSE /\ pg_uptodate' = FALSE
    /\ delete_pc' = "seqlock_clearing"
    /\ UNCHANGED <<page_state, cp_ref, vvp_ref, transfer_pinned,
                   pg_private, pg_locked, pg_writeback, inv_seq, write_pc,
                   read_pc, fault_pc, rerr_pc, write_count, read_count,
                   fault_seq, fault_private,
                   vmpage_ref, bl_ast_pc>>

\* Step 7: vvp_page_delete - write_sequnlock (seq becomes even)
\* INJECT_NO_SEQLOCK: no unlock (seqlock was never taken)
DeleteSeqlockRelease ==
    /\ delete_pc = "seqlock_clearing"
    /\ IF INJECT_NO_SEQLOCK
       THEN /\ UNCHANGED inv_seq
       ELSE /\ inv_seq' = inv_seq + 1   \* seq -> even (unlocked)
    /\ delete_pc' = "uptodate_cleared"
    /\ UNCHANGED <<page_state, cp_ref, vvp_ref, transfer_pinned,
                   pg_private, pg_uptodate, pg_locked, pg_writeback, write_pc,
                   read_pc, fault_pc, rerr_pc, write_count, read_count,
                   fault_seq, fault_private,
                   vmpage_ref, bl_ast_pc>>

\* Step 8: osc_page_delete - osc_page_transfer_put (idempotent)
DeleteTransferPut ==
    /\ delete_pc = "uptodate_cleared"
    /\ IF transfer_pinned
       THEN /\ transfer_pinned' = FALSE
            /\ cp_ref' = cp_ref - 1
       ELSE /\ UNCHANGED <<transfer_pinned, cp_ref>>
    /\ delete_pc' = "osc_done"
    /\ UNCHANGED <<page_state, vvp_ref, pg_private, pg_uptodate,
                   pg_locked, pg_writeback, inv_seq, write_pc, read_pc,
                   fault_pc, rerr_pc, write_count, read_count,
                   fault_seq, fault_private,
                   vmpage_ref, bl_ast_pc>>

\* Step 9: Unlock vmpage (caller of cl_page_delete)
DeleteUnlock ==
    /\ delete_pc = "osc_done"
    /\ pg_locked' = FALSE
    /\ delete_pc' = "done"
    /\ UNCHANGED <<page_state, cp_ref, vvp_ref, transfer_pinned,
                   pg_private, pg_uptodate, pg_writeback, inv_seq, write_pc,
                   read_pc, fault_pc, rerr_pc, write_count, read_count,
                   fault_seq, fault_private,
                   vmpage_ref, bl_ast_pc>>

DeleteReset ==
    /\ delete_pc = "done"
    /\ delete_pc' = "idle"
    /\ UNCHANGED <<page_state, cp_ref, vvp_ref, transfer_pinned,
                   pg_private, pg_uptodate, pg_locked, pg_writeback, inv_seq,
                   write_pc, read_pc, fault_pc, rerr_pc, write_count,
                   read_count, fault_seq, fault_private,
                   vmpage_ref, bl_ast_pc>>

(* ================================================================
 * FAULT / BUFFERED READ: page fault or read() reads vmpage data
 *
 * Uses lli_page_inv_lock seqlock to detect page invalidation.
 * If page is deleted during fault (seq changes), retry.
 *
 * Models two code paths:
 *   - ll_filemap_fault (mmap): always uses seqlock (LU-16160)
 *   - vvp_io_read (buffered read): pre-LU-16649, no seqlock retry
 *     so concurrent delete causes short read or EIO to userspace
 *
 * INJECT_NO_READ_SEQLOCK models the pre-LU-16649 buffered read()
 * path that lacks seqlock protection.  With the injection, the
 * reader never captures/checks the seqlock, so concurrent delete
 * invalidation goes undetected -> stale data / EIO.
 *
 * NOTE: faults/reads do NOT hold the vmpage lock.  filemap_fault
 * finds the vmpage in the page cache, then reads its data.
 * The seqlock is the only protection against concurrent delete.
 * ================================================================ *)

\* Step 1: read_seqbegin - capture sequence number
\* Page must still be in the page cache (pg_private) and uptodate.
\* INJECT_NO_READ_SEQLOCK: skip seqlock capture (pre-LU-16649 read())
FaultBegin ==
    /\ ENABLE_FAULT
    /\ fault_pc = "idle"
    /\ pg_private                 \* Page must still be Lustre-managed
    /\ pg_uptodate                \* Page must have valid data
    /\ IF INJECT_NO_READ_SEQLOCK
       THEN \* BUG: no seqlock in read() path (pre-LU-16649)
            /\ fault_seq' = -1    \* Sentinel: seqlock not used
            /\ fault_pc' = "reading"
       ELSE \* Normal: read_seqbegin captures sequence
            /\ inv_seq % 2 = 0   \* read_seqbegin spins until seq is even
            /\ fault_seq' = inv_seq
            /\ fault_pc' = "reading"
    /\ UNCHANGED <<page_state, cp_ref, vvp_ref, transfer_pinned,
                   pg_private, pg_uptodate, pg_locked, pg_writeback, inv_seq,
                   write_pc, read_pc, delete_pc, rerr_pc, write_count,
                   read_count, fault_private,
                   vmpage_ref, bl_ast_pc>>

\* Step 2: Read page data
\* The fault reads the page DATA (via filemap_fault -> page cache).
\* What matters is whether the data was valid = page was uptodate.
\* We snapshot pg_uptodate here as fault_private (reusing the variable
\* to track "was the page data valid when fault read it").
\* If delete clears uptodate concurrently, the seqlock will catch it.
FaultRead ==
    /\ ENABLE_FAULT
    /\ fault_pc = "reading"
    /\ fault_private' = pg_uptodate  \* Snapshot: was data valid?
    /\ fault_pc' = "checking"
    /\ UNCHANGED <<page_state, cp_ref, vvp_ref, transfer_pinned,
                   pg_private, pg_uptodate, pg_locked, pg_writeback, inv_seq,
                   write_pc, read_pc, delete_pc, rerr_pc, write_count,
                   read_count, fault_seq,
                   vmpage_ref, bl_ast_pc>>

\* Step 3: read_seqretry - check if sequence changed
\* INJECT_NO_READ_SEQLOCK: always accept result (no retry),
\* which means if delete cleared uptodate concurrently, we
\* return stale/invalid data to userspace (LU-16649).
FaultCheck ==
    /\ ENABLE_FAULT
    /\ fault_pc = "checking"
    /\ IF INJECT_NO_READ_SEQLOCK
       THEN \* BUG: no seqlock check, always accept
            /\ fault_pc' = "done"
       ELSE IF inv_seq # fault_seq
            THEN \* Sequence changed: page was invalidated, retry
                 /\ fault_pc' = "idle"
            ELSE \* Sequence unchanged: data is valid
                 /\ fault_pc' = "done"
    /\ UNCHANGED <<page_state, cp_ref, vvp_ref, transfer_pinned,
                   pg_private, pg_uptodate, pg_locked, pg_writeback, inv_seq,
                   write_pc, read_pc, delete_pc, rerr_pc, write_count,
                   read_count, fault_seq, fault_private,
                   vmpage_ref, bl_ast_pc>>

FaultReset ==
    /\ ENABLE_FAULT
    /\ fault_pc = "done"
    /\ fault_pc' = "idle"
    /\ UNCHANGED <<page_state, cp_ref, vvp_ref, transfer_pinned,
                   pg_private, pg_uptodate, pg_locked, pg_writeback, inv_seq,
                   write_pc, read_pc, delete_pc, rerr_pc, write_count,
                   read_count, fault_seq, fault_private,
                   vmpage_ref, bl_ast_pc>>

(* ================================================================
 * DELETE ABORT (vmpage refcount check - LU-16276 fix)
 *
 * When ll_releasepage detects extra vmpage references (e.g., from
 * BL AST holding a get_page ref), it must abort the delete and
 * return 0 (can't release).  Otherwise, cl_page_delete clears
 * PagePrivate but __remove_mapping fails due to elevated refcount,
 * leaving the vmpage in the page cache with no Lustre cl_page.
 *
 * This action is only enabled in fix mode (INJECT_NO_VMREF_CHECK=FALSE).
 * In bug mode, DeleteSetFreeing proceeds regardless of vmpage_ref.
 * ================================================================ *)

\* Abort releasepage: vmpage has extra refs, __remove_mapping would fail
\* Disown the page (OWNED -> CACHED, unlock) without deleting
DeleteAbortVmref ==
    /\ ~INJECT_NO_VMREF_CHECK      \* Only in fix mode
    /\ delete_pc = "owned"
    /\ page_state = "CPS_OWNED"
    /\ vmpage_ref > 0               \* Extra refs detected
    /\ page_state' = "CPS_CACHED"  \* Disown: OWNED -> CACHED
    /\ pg_locked' = FALSE           \* Unlock vmpage
    /\ delete_pc' = "done"          \* Skip delete, return 0
    /\ UNCHANGED <<cp_ref, vvp_ref, transfer_pinned, pg_private,
                   pg_uptodate, pg_writeback, inv_seq, write_pc, read_pc,
                   fault_pc, rerr_pc, write_count, read_count,
                   fault_seq, fault_private, vmpage_ref, bl_ast_pc>>

(* ================================================================
 * BL AST: blocking AST callback holds cl_page + vmpage refs
 *
 * Models the LDLM blocking AST callback path where the lock holder
 * finds a cl_page (via cl_page_find / PagePrivate) and takes a
 * cl_page reference (cl_page_get) plus an implicit vmpage reference
 * (get_page).  The callback holds these references while processing
 * (e.g., flushing dirty data, waiting for lock cancel completion).
 *
 * The race (LU-16276): while BL AST holds these refs, the VM calls
 * ll_releasepage which proceeds with cl_page_delete (clearing
 * PagePrivate).  After releasepage returns, __remove_mapping fails
 * because the vmpage refcount is elevated by BL AST's get_page.
 * The vmpage stays in the page cache with no Lustre cl_page backing.
 *
 * The fix: ll_releasepage checks page_count(vmpage) after locking
 * the vmpage.  If extra refs exist, it aborts (returns 0) without
 * deleting the cl_page.
 *
 * Guard: pg_private (cl_page_find needs PagePrivate) and ~pg_locked
 * (vmpage lock serializes with releasepage's page_count check).
 * ================================================================ *)

\* Step 1: BL AST callback finds cl_page, takes refs
\* cl_page_find -> cl_page_get (cp_ref++) + get_page(vmpage) (vmpage_ref++)
BlAstGetRef ==
    /\ ENABLE_BL_AST
    /\ bl_ast_pc = "idle"
    /\ pg_private                 \* cl_page_find needs PagePrivate
    /\ ~pg_locked                 \* vmpage lock serializes with releasepage check
    /\ cp_ref' = cp_ref + 1      \* cl_page_get
    /\ vmpage_ref' = vmpage_ref + 1  \* get_page(vmpage)
    /\ bl_ast_pc' = "holding"
    /\ UNCHANGED <<page_state, vvp_ref, transfer_pinned, pg_private,
                   pg_uptodate, pg_locked, pg_writeback, inv_seq,
                   write_pc, read_pc, delete_pc, fault_pc, rerr_pc,
                   write_count, read_count, fault_seq, fault_private>>

\* Step 2: BL AST callback completes, releases refs
\* cl_page_put (cp_ref--) + put_page(vmpage) (vmpage_ref--)
BlAstRelease ==
    /\ ENABLE_BL_AST
    /\ bl_ast_pc = "holding"
    /\ cp_ref' = cp_ref - 1      \* cl_page_put
    /\ vmpage_ref' = vmpage_ref - 1  \* put_page(vmpage)
    /\ bl_ast_pc' = "done"
    /\ UNCHANGED <<page_state, vvp_ref, transfer_pinned, pg_private,
                   pg_uptodate, pg_locked, pg_writeback, inv_seq,
                   write_pc, read_pc, delete_pc, fault_pc, rerr_pc,
                   write_count, read_count, fault_seq, fault_private>>

BlAstReset ==
    /\ ENABLE_BL_AST
    /\ bl_ast_pc = "done"
    /\ bl_ast_pc' = "idle"
    /\ UNCHANGED <<page_state, cp_ref, vvp_ref, transfer_pinned,
                   pg_private, pg_uptodate, pg_locked, pg_writeback, inv_seq,
                   write_pc, read_pc, delete_pc, fault_pc, rerr_pc,
                   write_count, read_count, fault_seq, fault_private,
                   vmpage_ref>>

(* ================================================================
 * Terminal state
 * ================================================================ *)
Done ==
    /\ page_state = "CPS_FREEING"
    /\ UNCHANGED vars

(* ================================================================
 * Next-state relation
 * ================================================================ *)
Next ==
    \* Write IO
    \/ WriteOwn
    \/ WriteMakeReady
    \/ WriteMakeReadyEarlyUnlock
    \/ WriteMakeReadySubmit
    \/ WriteDisown
    \/ WriteComplete
    \/ WriteEndWriteback
    \/ WriteTransferPut
    \/ WriteBuggyFlagClear
    \/ WriteBuggyPut
    \/ WriteReset
    \* Read IO
    \/ ReadOwn
    \/ ReadSubmit
    \/ ReadDisown
    \/ ReadComplete
    \/ ReadTransferPut
    \/ ReadReset
    \* Read error completion
    \/ RerrOwn
    \/ RerrSubmit
    \/ RerrComplete
    \/ RerrTransferPut
    \/ RerrSetFreeing
    \/ RerrVvpDropRef
    \/ RerrClearPrivate
    \/ RerrSeqlockAcquire
    \/ RerrClearUptodate
    \/ RerrSeqlockRelease
    \/ RerrOscTransferPut
    \/ RerrUnlock
    \/ RerrReset
    \* Delete (fine-grained)
    \/ DeleteOwn
    \/ DeleteSetFreeing
    \/ DeleteVvpDropRef
    \/ DeleteClearPrivate
    \/ DeleteSeqlockAcquire
    \/ DeleteClearUptodate
    \/ DeleteSeqlockRelease
    \/ DeleteTransferPut
    \/ DeleteUnlock
    \/ DeleteReset
    \* Fault
    \/ FaultBegin
    \/ FaultRead
    \/ FaultCheck
    \/ FaultReset
    \* BL AST
    \/ BlAstGetRef
    \/ BlAstRelease
    \/ BlAstReset
    \* Delete abort (vmpage refcount, LU-16276 fix)
    \/ DeleteAbortVmref
    \* Terminal
    \/ Done

(* ================================================================
 * INVARIANTS
 * ================================================================ *)

\* Reference count must never go negative
NoNegativeRef ==
    cp_ref >= 0

\* Alive pages (not freeing) must have at least the base refs
AlivePageHasRef ==
    (page_state # "CPS_FREEING") => (cp_ref >= 1)

\* After delete fully completes, ref accounting must be clean:
\* only the alloc ref (1) remains, all flags clear
CleanAfterDelete ==
    (page_state = "CPS_FREEING" /\ delete_pc = "done"
     /\ write_pc \in {"idle", "done"}
     /\ read_pc \in {"idle", "done"}
     /\ rerr_pc \in {"idle", "done"}
     /\ bl_ast_pc \in {"idle", "done"}) =>
        /\ cp_ref = 1
        /\ transfer_pinned = FALSE
        /\ vvp_ref = FALSE
        /\ pg_private = FALSE
        /\ pg_uptodate = FALSE

\* After error-delete fully completes, same cleanliness
CleanAfterErrorDelete ==
    (page_state = "CPS_FREEING" /\ rerr_pc = "done"
     /\ write_pc \in {"idle", "done"}
     /\ read_pc \in {"idle", "done"}
     /\ delete_pc \in {"idle", "done"}
     /\ bl_ast_pc \in {"idle", "done"}) =>
        /\ cp_ref = 1
        /\ transfer_pinned = FALSE
        /\ vvp_ref = FALSE
        /\ pg_private = FALSE
        /\ pg_uptodate = FALSE

\* Transfer pin is only set during IO (PAGEOUT/PAGEIN)
\* or in the completion window
TransferPinOnlyDuringIO ==
    (page_state = "CPS_CACHED"
     /\ write_pc \in {"idle", "done"}
     /\ read_pc \in {"idle", "done"}
     /\ rerr_pc \in {"idle", "done"}) =>
        (transfer_pinned = FALSE)

\* PageUptodate can only be TRUE when PagePrivate is TRUE.
\* Exception: during delete, private is cleared before uptodate
\* (steps are split), so we only check when delete is not
\* in the middle of clearing.  Same exception for error delete.
UptodateRequiresPrivate ==
    (delete_pc \notin {"private_cleared", "seqlock_held",
                       "seqlock_clearing"}
     /\ rerr_pc \notin {"err_private_cleared", "err_seqlock_held",
                         "err_seqlock_clearing"}) =>
        (pg_uptodate => pg_private)

\* Seqlock detects page invalidation: if a fault completes
\* successfully (seqlock matched, fault_pc = "done"), the data
\* the fault read must have been from a valid (uptodate) page.
\*
\* We check fault_private (which captures pg_uptodate at FaultRead
\* time), not current pg_uptodate.  This models the real guarantee:
\* the seqlock ensures the page data was valid when the fault read it.
\*
\* In real code, ll_filemap_fault retries on SIGBUS if seqlock
\* detects invalidation.  The seqlock protects against reading
\* stale data after ClearPageUptodate (LU-16160).
FaultSeesConsistentState ==
    (fault_pc = "done") => (fault_private = TRUE)

\* PageWriteback is only set during async write (CPS_PAGEOUT).
\* It is set in WriteMakeReady (SetPageWriteback) and cleared in
\* WriteComplete (end_page_writeback).  Outside this window, the
\* VFS requires PageWriteback to be clear.
WritebackOnlyDuringIO ==
    pg_writeback =>
        (page_state = "CPS_PAGEOUT" \/ write_pc = "wb_clearing")

\* Delete must not own a page while PageWriteback is set.
\* This models the LASSERT(!PageWriteback) in discard_cb (LU-4581/LU-2779):
\* lock cancel discard encounters pages in radix tree and asserts
\* they don't have writeback set.
DeleteOwnImpliesNoWriteback ==
    (delete_pc = "owned") => ~pg_writeback

\* CPS_OWNED pages must have their vmpage locked.
\* cl_page_own and cl_page_assume both lock the vmpage before
\* setting CPS_OWNED.  If the vmpage is unlocked while the page
\* is still CPS_OWNED, another thread (readahead via cl_page_assume)
\* can lock it and attempt an invalid CPS_OWNED -> CPS_OWNED state
\* transition, causing LBUG.  (LU-16612)
\*
\* This invariant directly captures the safety property violated by
\* the pre-fix cl_page_make_ready which called unlock_page() before
\* cl_page_io_start().
OwnedImpliesLocked ==
    (page_state = "CPS_OWNED") => pg_locked

\* vmpage must not have PagePrivate cleared (delete completed) while
\* external vmpage references exist.  If pg_private is cleared during
\* CPS_FREEING and vmpage_ref > 0, __remove_mapping will fail because
\* the vmpage refcount is elevated.  The vmpage stays in the page cache
\* with no Lustre cl_page backing -- an inconsistent state.  (LU-16276)
VmpageNotRemovedWhileReferenced ==
    (~pg_private /\ page_state = "CPS_FREEING") => (vmpage_ref = 0)

\* A fault that completes successfully must have captured an even
\* sequence number.  read_seqbegin spins until seq is even, so
\* fault_seq is always even at capture time.  This invariant
\* verifies that our FaultBegin guard correctly models this.
SeqlockOddMeansRetry ==
    (fault_pc = "done") =>
        (fault_seq % 2 = 0)

\* When the transfer pin is held, the ref count must be at least 2.
\* Rationale: transfer_pinned means osc_page_transfer_get added a ref
\* on top of the alloc_ref (which is always 1), so minimum is 2.
\* This catches double-drop bugs where the transfer ref is dropped
\* more than once (would bring cp_ref below 2 while transfer_pinned).
\*
\* Covers race (1) from task at9.4: page referenced after PageWriteback
\* clear but before transfer completion -- ensures the ref accounting
\* stays consistent during the write_pc = "completed" window.
TransferPinImpliesRef ==
    transfer_pinned => cp_ref >= 2

\* When vvp_ref is still held (page not yet in delete path), there
\* must be at least 2 refs: alloc_ref (1) + vvp_ref (1).
\* vvp_page_init takes a ref; it is dropped only in vvp_page_delete.
VvpRefImpliesRef ==
    vvp_ref => cp_ref >= 2

\* During the window between WriteComplete (write_pc = "wb_clearing")
\* and WriteEndWriteback (write_pc = "completed"), two properties hold:
\*   - pg_writeback is still TRUE (WriteEndWriteback hasn't fired yet)
\*   - transfer_pinned is still TRUE (delete cannot start while
\*     pg_writeback is set, so nothing has cleared the pin yet)
\* This directly checks the coherence of the completion window at the
\* center of the writeback+truncate+fault three-way race.
WritebackWindowConsistency ==
    (write_pc = "wb_clearing") => (pg_writeback /\ transfer_pinned)

\* While a page is in CPS_PAGEOUT, SetPageWriteback has already been
\* called (in WriteMakeReady) and end_page_writeback has not yet been
\* called (that happens in WriteEndWriteback after WriteComplete moves
\* state to CPS_CACHED).  So CPS_PAGEOUT => pg_writeback.
\* Verifies that the writeback flag is set atomically with PAGEOUT.
PageoutHasWriteback ==
    (page_state = "CPS_PAGEOUT") => pg_writeback

\* A page in CPS_FREEING must not have PageWriteback set.
\* Both DeleteOwn and RerrSetFreeing guard on ~pg_writeback before
\* setting CPS_FREEING, and no path sets pg_writeback after entering
\* CPS_FREEING.  This cross-checks that delete never races with an
\* async write -- the VFS !PageWriteback LASSERT in ll_invalidatepage.
FreeingImpliesNoWriteback ==
    (page_state = "CPS_FREEING") => ~pg_writeback

(* ================================================================
 * THREE-WAY RACE INVARIANTS
 *
 * Verify safety properties when writeback completion, truncate
 * (delete), and page fault execute concurrently on the same page.
 *
 * The three-way race window:
 *   - Write IO completes (PAGEOUT->CACHED), clears PageWriteback,
 *     but hasn't dropped its transfer ref yet
 *   - Delete (truncate/lock cancel) sees CPS_CACHED + !PageWriteback,
 *     takes ownership and begins freeing the page
 *   - Fault is reading the page under seqlock protection
 *
 * The existing processes (Write, Delete, Fault) model these three
 * concurrent actors.  These invariants verify the specific safety
 * properties of their three-way interleaving.
 * ================================================================ *)

\* (a) After end_page_writeback but before transfer_put, the page's
\* transfer ref is still held.  If truncate starts in this window,
\* the ref count must still properly account for the pending drop.
\*
\* Specifically: when write_pc = "completed" (WB cleared, transfer_put
\* pending) and transfer_pinned is TRUE, cp_ref must be >= 2 (at least
\* alloc_ref + transfer_ref).  This catches use-after-free scenarios
\* where truncate starts in the WB-clear->transfer-put window and the
\* ref accounting is inconsistent.
WritebackClearRefSafe ==
    (write_pc = "completed" /\ transfer_pinned) =>
        cp_ref >= 2

\* (b) After truncate severs the vmpage->cl_page link (ClearPagePrivate)
\* and invalidates the page data (ClearPageUptodate), a fault must not
\* successfully complete with stale data.  Any fault in progress must
\* be forced to retry by the seqlock change.  A retried fault cannot
\* re-start on this page (pg_private=FALSE blocks FaultBegin).
\*
\* This unifies the seqlock protection properties from LU-16160 and
\* LU-16935: both the delete path and error-discard path must bump
\* the seqlock to invalidate concurrent faults.
NoFaultRestartDuringTruncate ==
    (page_state = "CPS_FREEING" /\ ~pg_private /\ ~pg_uptodate) =>
        \/ fault_pc \in {"idle", "done"}
        \/ (fault_pc \in {"reading", "checking"} /\ fault_seq # inv_seq)

\* (c) Writeback completion is not re-entrant: after WriteComplete
\* transitions CPS_PAGEOUT->CPS_CACHED, the page cannot re-enter
\* CPS_PAGEOUT during the same write cycle.  This prevents double
\* completion bugs where the RPC callback fires twice or where
\* truncate re-triggers the write path on a completing page.
NoDoubleCompletion ==
    (write_pc \in {"wb_clearing", "completed", "done"}) =>
        page_state # "CPS_PAGEOUT"

\* (d) PageoutHasWriteback: when page_state = CPS_PAGEOUT, the vmpage
\* must have PageWriteback set.  SetPageWriteback is called atomically
\* with the CPS_PAGEOUT transition in cl_page_make_ready, and
\* end_page_writeback is called AFTER cl_page_complete transitions away
\* from CPS_PAGEOUT.  Defined once above (a second, identical copy here
\* was removed: TLA+ does not allow operator redefinition).
\*
\* (e) WritebackWindowConsistency: during the wb_clearing window
\* (between cl_page_complete and end_page_writeback), the writeback
\* flag and transfer pin must still be held.  Also defined once above.

\* (f) When the seqlock is write-held (inv_seq is odd), any fault in
\* the reading/checking phase must have captured a different (earlier
\* even) sequence number.  This guarantees the fault will detect the
\* concurrent page invalidation and retry.
\*
\* This is the core safety property of the truncate-vs-fault race:
\* write_seqlock in vvp_page_delete (or error discard) makes the
\* sequence number odd, which is guaranteed to differ from any value
\* captured by read_seqbegin (which waits for even).
TruncateSeqlockProtectsFault ==
    (inv_seq % 2 = 1 /\ fault_pc \in {"reading", "checking"}) =>
        fault_seq # inv_seq

\* (g) When page_state = CPS_FREEING, PageWriteback must be FALSE.
\* The truncate/invalidate path requires writeback to complete before
\* proceeding with page destruction.  A CPS_FREEING page with
\* PageWriteback set would mean truncate raced past writeback without
\* waiting, leading to data loss or filesystem corruption.
NoWritebackDuringFreeing ==
    (page_state = "CPS_FREEING") => ~pg_writeback

\* (h) If a fault is in the reading/checking phase and PageUptodate
\* has been cleared since the fault started (the page was invalidated),
\* the seqlock must have been bumped to force the fault to retry.
\* Violation means the page data was invalidated without seqlock
\* protection, so the fault would silently return stale/invalid data.
\*
\* FaultBegin requires pg_uptodate=TRUE, so if pg_uptodate is FALSE
\* while a fault is reading, something cleared it concurrently.
\* The seqlock mechanism must detect this.
FaultUptodateSeqlockConsistency ==
    (fault_pc \in {"reading", "checking"} /\ ~pg_uptodate) =>
        fault_seq # inv_seq

\* (i) Reference count must exactly equal the sum of known ref holders:
\*   alloc_ref (always 1) + vvp_ref (0 or 1) + transfer_ref (0 or 1)
\*
\* Any deviation indicates a ref leak (too high) or double-drop (too
\* low).  This catches ref-counting bugs in the three-way race earlier
\* and more precisely than CleanAfterDelete, which only checks at the
\* end of the delete lifecycle.
\*
\* NOTE: Only valid when INJECT_BUGGY_TRANSFER = FALSE.  The buggy
\* transfer path intentionally decouples the flag clear from the ref
\* drop, which temporarily violates this invariant by design.
\* When ENABLE_BL_AST is TRUE, the BL AST callback holds an additional
\* cl_page ref while bl_ast_pc = "holding".
RefcountSanity ==
    cp_ref = 1 + (IF vvp_ref THEN 1 ELSE 0)
               + (IF transfer_pinned THEN 1 ELSE 0)
               + (IF bl_ast_pc = "holding" THEN 1 ELSE 0)

(* ================================================================
 * SPEC
 * ================================================================ *)
Spec == Init /\ [][Next]_vars

=============================================================================
