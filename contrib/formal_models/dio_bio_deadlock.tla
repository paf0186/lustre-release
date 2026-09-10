---------------------------- MODULE dio_bio_deadlock ----------------------------
(*
 * PlusCal/TLA+ model of the LU-19427 four-way deadlock between
 * DIO, BIO, LDLM AST, and RPC slot pool subsystems.
 *
 * The deadlock (from sanity-pcc test_99b):
 *
 *   T1d-T8d (DIO reads): consume all RPC slots, waiting for
 *     server reply.  Server needs to revoke extent lock L1 before
 *     it can grant the read lock, so it sends a BL_AST callback.
 *
 *   T2 (AST handler): osc_dlm_blocking_ast0 -> osc_lock_flush ->
 *     osc_lock_discard_pages -> exclusive invalidate_lock.
 *     Blocked because BIO/FastRead hold shared.
 *
 *   T3 (FastRead): generic_file_read_iter holds shared
 *     invalidate_lock, waiting for page/folio lock held by T4.
 *
 *   T4 (BIO buffered read): holds shared invalidate_lock AND
 *     page lock.  lov_io_submit -> osc_io_submit needs an RPC
 *     slot.  All slots consumed by DIO.
 *
 * Cycle: DIO(slots) -> Server(AST) -> AST(excl inv_lock)
 *                    -> BIO(shared inv_lock, needs slot) -> DIO
 *
 * Bug injection: InjectBug19427 = TRUE
 *   DIO threads can exhaust all RPC slots (threshold > 0).
 *   This starves BIO of slots, which holds shared inv_lock,
 *   blocking AST from acquiring exclusive, creating the cycle.
 *
 * Fix: InjectBug19427 = FALSE
 *   DIO threads reserve 1 RPC slot for non-DIO use (threshold > 1).
 *   BIO can always acquire a slot, complete, and release inv_lock,
 *   allowing AST to proceed and breaking the cycle.
 *
 * Processes modeled:
 *   DIO \in DioThreads  -- direct I/O read threads
 *   BIO = "bio"         -- buffered read thread
 *   AST = "ast"         -- LDLM blocking AST handler
 *   FastRead = "fread"  -- fast buffered read (page lock waiter)
 *
 * Resources modeled:
 *   rpc_slots_avail     -- bounded RPC slot pool (0..MAX_SLOTS)
 *   inv_lock_readers    -- shared invalidate_lock holder count
 *   inv_lock_writer     -- exclusive invalidate_lock held
 *   page_lock           -- per-page folio lock (mutex)
 *
 * Source (lustre-release master 47638add78):
 *   lustre/llite/file.c
 *     ll_file_io_generic     2061-     BIO/DIO entry (cl_io_loop)
 *   lustre/llite/rw.c
 *     ll_readpage            1847-     buffered read page submission
 *     ll_read_folio          2118-     (folio variant)
 *   lustre/llite/vvp_io.c
 *     vvp_io_init            1813-1899 filemap_invalidate_lock (1894)
 *                                     when ci_invalidate_page_cache
 *     vvp_io_fini             287-     filemap_invalidate_unlock (308)
 *   lustre/osc/osc_io.c
 *     osc_io_submit           103-     read submission (BIO path)
 *   lustre/osc/osc_request.c
 *     osc_build_rpc          2793-     cl_r_in_flight/cl_w_in_flight++
 *                                     (2957-2971); RPC "slot" accounting
 *   lustre/osc/osc_internal.h
 *     rpcs_in_flight          108-111  cl_r_in_flight + cl_w_in_flight
 *   lustre/osc/osc_cache.c
 *     osc_max_rpc_in_flight  1836-1840 max_rpcs_in_flight check
 *     osc_check_rpcs         2383-2452 HP extents bypass the limit
 *                                     (2396-2402, LU-13131/LU-17190)
 *     osc_lock_discard_pages 3721-3749 sets ci_invalidate_page_cache
 *                                     (3733) -> exclusive invalidate_lock
 *     osc_ldlm_hp_handle     3751-     LU-17190: promote conflicting
 *                                     buffered-read extents to HP when
 *                                     all slots are used by DIO
 *   lustre/osc/osc_lock.c
 *     osc_lock_flush          347-393  osc_ldlm_hp_handle (367), then
 *                                     osc_lock_discard_pages (381)
 *     __osc_dlm_blocking_ast  405-     (was osc_dlm_blocking_ast0)
 *     osc_ldlm_blocking_ast   524-
 *   lustre/ldlm/ldlm_lock.c
 *     ldlm_cancel_callback   2459-     AST dispatch
 *
 * Bugs verified:
 *   LU-19427 -- invalidate_lock deadlock with mixed BIO/DIO
 *
 * Validated against: lustre-release master 47638add78 (2026-09-06)
 * Validation notes:
 *   - DISCREPANCY-OPEN: the "fix" variant (InjectBug19427 = FALSE,
 *     DIO reserves one RPC slot for non-DIO use) does not correspond
 *     to any code in this tree.  There is no DIO slot reservation:
 *     osc_max_rpc_in_flight counts all BRW RPCs equally.  The landed
 *     LU-19427 fix (56e59cbb11: trylock on invalidate_lock in the
 *     blocking AST + promote pending buffered-read extents to the HP
 *     list) was reverted by 7e0ccbf241 ("multiple threads can
 *     deadlock in invalidate_lock()"); LU-19427 is Reopened and the
 *     follow-up is Gerrit 63132 (LU-19721, NEW).  The closest in-tree
 *     mechanism is LU-17190 (61a01fd9b6): osc_lock_flush calls
 *     osc_ldlm_hp_handle, which moves buffered-read extents that
 *     conflict with the lock being cancelled to oo_hp_read_exts, and
 *     osc_check_rpcs lets HP extents exceed max_rpcs_in_flight.  That
 *     is the effect the model's reserved slot abstracts (BIO can
 *     always get a slot), but it is keyed on the conflicting lock, not
 *     on a global reservation, and the sanity-pcc/99b deadlock still
 *     reproduces with it.  The bug variant (InjectBug19427 = TRUE)
 *     matches the current code.  Model left unchanged.
 *   - The exclusive invalidate_lock is taken in vvp_io_init via
 *     ci_invalidate_page_cache (set by osc_lock_discard_pages), not
 *     inside osc_lock_discard_pages itself.
 *)

EXTENDS Integers, FiniteSets, TLC

CONSTANTS
    MAX_SLOTS,        \* RPC slot pool size (max_rpcs_in_flight)
    NUM_DIO,          \* Number of concurrent DIO read threads
    InjectBug19427    \* TRUE = DIO can exhaust all slots (bug)
                      \* FALSE = DIO reserves 1 slot for BIO (fix)

ASSUME MAX_SLOTS \in 1..8
ASSUME NUM_DIO \in 1..8
ASSUME NUM_DIO >= MAX_SLOTS  \* DIO must be able to exhaust slots

DioNums == 1..NUM_DIO

(* --algorithm dio_bio_deadlock

variables
    \* ---- RPC slot pool (osc_request.c: max_rpcs_in_flight) ----
    rpc_slots_avail = MAX_SLOTS,

    \* ---- invalidate_lock (rw_semaphore on mapping) ----
    \* Shared (down_read): BIO and FastRead for page cache access
    \* Exclusive (down_write): AST handler for page invalidation
    inv_lock_readers = 0,
    inv_lock_writer = FALSE,

    \* ---- Page/folio lock (per-page mutex) ----
    \* BIO acquires for buffered I/O, FastRead waits for it
    page_lock = "free",

    \* ---- Server-side AST dependency ----
    \* Server sends BL_AST when DIO RPCs need a conflicting lock.
    \* DIO RPCs cannot complete until AST handler revokes the lock.
    ast_needed = FALSE,
    ast_complete = FALSE;

define
    DioThreads == {ToString(i) : i \in DioNums}

    \* Minimum available slots before DIO can acquire one.
    \* BUG:  0 -- DIO can exhaust all slots, starving BIO
    \* FIX:  1 -- DIO reserves 1 slot for non-DIO (BIO) use
    DioSlotThreshold == IF InjectBug19427 THEN 0 ELSE 1

    \* ========== TYPE INVARIANT ==========
    TypeOK ==
        /\ rpc_slots_avail \in 0..MAX_SLOTS
        /\ inv_lock_readers \in 0..3
        /\ inv_lock_writer \in BOOLEAN
        /\ page_lock \in {"free", "bio", "fread"}
        /\ ast_needed \in BOOLEAN
        /\ ast_complete \in BOOLEAN

    \* ========== SAFETY: NO CIRCULAR-WAIT DEADLOCK ==========
    \* The deadlock state: three actors stuck in a cycle.
    \*
    \*   DIO threads: all waiting for server reply (needs ast_complete)
    \*   BIO: waiting for RPC slot (slots exhausted by DIO)
    \*   AST: waiting for exclusive inv_lock (BIO holds shared)
    \*
    \* Additionally: slots must be 0 (exhausted) and inv_lock must
    \* have readers (blocking AST).  These resource conditions confirm
    \* the actors are truly stuck, not just transiently at those PCs.
    NoDeadlock ==
        ~( /\ \A d \in DioThreads : pc[d] = "DIO_WaitReply"
           /\ pc["bio"] = "BIO_AcquireSlot"
           /\ pc["ast"] = "AST_AcquireExcl"
           /\ rpc_slots_avail = 0
           /\ inv_lock_readers > 0
         )

    \* ========== LIVENESS ==========
    AllComplete ==
        <>( /\ \A d \in DioThreads : pc[d] = "Done"
            /\ pc["bio"] = "Done"
            /\ pc["ast"] = "Done"
            /\ pc["fread"] = "Done"
          )

    \* All DIO threads eventually finish (verifies no DIO starvation under load)
    DIOComplete == <>(\A d \in DioThreads : pc[d] = "Done")
end define;

\* ================================================================
\* DIO threads: direct I/O read RPCs.
\*
\* Each DIO thread acquires an RPC slot, sends a read RPC to the
\* server, and waits for the reply.  The server cannot reply until
\* it grants the read lock, which requires revoking the conflicting
\* extent lock L1 via BL_AST.  So DIO waits for ast_complete.
\*
\* BUG:  await rpc_slots_avail > 0  (can take last slot)
\* FIX:  await rpc_slots_avail > 1  (reserves 1 for BIO)
\*
\* Source: osc_build_rpc (osc_request.c:2793; in-flight counters at
\*         2957-2971), osc_max_rpc_in_flight (osc_cache.c:1836)
\* ================================================================
fair process DIO \in DioThreads
begin
DIO_AcquireSlot:
    \* Wait for an available RPC slot (threshold varies by bug/fix)
    await rpc_slots_avail > DioSlotThreshold;
    rpc_slots_avail := rpc_slots_avail - 1;

DIO_SendRPC:
    \* RPC sent to server; server discovers lock conflict with L1
    \* and triggers BL_AST callback to client
    ast_needed := TRUE;

DIO_WaitReply:
    \* Server blocked on lock revocation; reply comes only after
    \* AST handler completes and revokes L1
    await ast_complete;

DIO_ReleaseSlot:
    rpc_slots_avail := rpc_slots_avail + 1;
end process;

\* ================================================================
\* BIO thread: buffered read via generic_file_read_iter.
\*
\* Acquires shared invalidate_lock (down_read), acquires page lock,
\* then submits a read RPC via osc_io_submit.  The RPC submission
\* requires an available RPC slot.
\*
\* In the bug case, DIO has consumed all slots, so BIO blocks at
\* BIO_AcquireSlot while holding shared inv_lock -- forming the
\* circular dependency that creates the deadlock.
\*
\* Source: ll_file_io_generic (llite/file.c:2061) -> ll_readpage
\*         (llite/rw.c:1847) -> osc_io_submit (osc/osc_io.c:103);
\*         shared invalidate_lock is taken by the kernel's
\*         filemap_fault/read paths on the mapping
\* ================================================================
fair process BIO = "bio"
begin
BIO_AcquireInvLock:
    \* down_read(&mapping->invalidate_lock)
    await ~inv_lock_writer;
    inv_lock_readers := inv_lock_readers + 1;

BIO_AcquirePageLock:
    \* lock_page / folio_lock -- acquire page lock for read
    await page_lock = "free";
    page_lock := "bio";

BIO_AcquireSlot:
    \* osc_io_submit: wait for available RPC slot
    await rpc_slots_avail > 0;
    rpc_slots_avail := rpc_slots_avail - 1;

BIO_WaitReply:
    \* BIO read RPC does not need AST completion (different lock)
    skip;

BIO_ReleaseSlot:
    rpc_slots_avail := rpc_slots_avail + 1;

BIO_ReleasePageLock:
    page_lock := "free";

BIO_ReleaseInvLock:
    \* up_read(&mapping->invalidate_lock)
    inv_lock_readers := inv_lock_readers - 1;
end process;

\* ================================================================
\* LDLM AST handler: blocking AST callback for lock L1.
\*
\* Triggered when the server sends a BL_AST to revoke extent lock
\* L1 (conflicting with DIO reads).  The handler must invalidate
\* cached pages under L1, which requires exclusive invalidate_lock.
\*
\* Source: osc_ldlm_blocking_ast -> __osc_dlm_blocking_ast
\*         (osc/osc_lock.c:524, 405) -> osc_lock_flush (osc_lock.c:347)
\*         -> osc_lock_discard_pages (osc/osc_cache.c:3721) -> cl_io_init
\*         -> vvp_io_init filemap_invalidate_lock (llite/vvp_io.c:1894)
\* ================================================================
fair process AST = "ast"
begin
AST_WaitTrigger:
    \* Wait for server to send BL_AST (triggered by DIO RPCs)
    await ast_needed;

AST_AcquireExcl:
    \* down_write(&mapping->invalidate_lock)
    \* Blocks until all shared holders release
    await inv_lock_readers = 0 /\ ~inv_lock_writer;
    inv_lock_writer := TRUE;

AST_RunCallback:
    \* Invalidate pages, flush data under lock L1
    skip;

AST_Release:
    \* up_write(&mapping->invalidate_lock)
    \* Mark AST as complete -- server can now grant lock and reply
    inv_lock_writer := FALSE;
    ast_complete := TRUE;
end process;

\* ================================================================
\* FastRead thread: fast buffered read path.
\*
\* Acquires shared invalidate_lock, then waits for page lock held
\* by BIO.  This adds another shared holder that blocks AST.
\*
\* Source: generic_file_read_iter (mm/filemap.c)
\* ================================================================
fair process FastRead = "fread"
begin
FR_AcquireInvLock:
    \* down_read(&mapping->invalidate_lock)
    await ~inv_lock_writer;
    inv_lock_readers := inv_lock_readers + 1;

FR_WaitPageLock:
    \* Wait for page lock held by BIO
    await page_lock = "free";
    page_lock := "fread";

FR_Read:
    \* Read page contents
    skip;

FR_ReleasePageLock:
    page_lock := "free";

FR_ReleaseInvLock:
    \* up_read(&mapping->invalidate_lock)
    inv_lock_readers := inv_lock_readers - 1;
end process;

end algorithm; *)

\* BEGIN TRANSLATION
VARIABLES rpc_slots_avail, inv_lock_readers, inv_lock_writer, page_lock,
          ast_needed, ast_complete, pc

(* define statement *)
DioThreads == {ToString(i) : i \in DioNums}




DioSlotThreshold == IF InjectBug19427 THEN 0 ELSE 1


TypeOK ==
    /\ rpc_slots_avail \in 0..MAX_SLOTS
    /\ inv_lock_readers \in 0..3
    /\ inv_lock_writer \in BOOLEAN
    /\ page_lock \in {"free", "bio", "fread"}
    /\ ast_needed \in BOOLEAN
    /\ ast_complete \in BOOLEAN











NoDeadlock ==
    ~( /\ \A d \in DioThreads : pc[d] = "DIO_WaitReply"
       /\ pc["bio"] = "BIO_AcquireSlot"
       /\ pc["ast"] = "AST_AcquireExcl"
       /\ rpc_slots_avail = 0
       /\ inv_lock_readers > 0
     )


AllComplete ==
    <>( /\ \A d \in DioThreads : pc[d] = "Done"
        /\ pc["bio"] = "Done"
        /\ pc["ast"] = "Done"
        /\ pc["fread"] = "Done"
      )


DIOComplete == <>(\A d \in DioThreads : pc[d] = "Done")


vars == << rpc_slots_avail, inv_lock_readers, inv_lock_writer, page_lock,
           ast_needed, ast_complete, pc >>

ProcSet == (DioThreads) \cup {"bio"} \cup {"ast"} \cup {"fread"}

Init == (* Global variables *)
        /\ rpc_slots_avail = MAX_SLOTS
        /\ inv_lock_readers = 0
        /\ inv_lock_writer = FALSE
        /\ page_lock = "free"
        /\ ast_needed = FALSE
        /\ ast_complete = FALSE
        /\ pc = [self \in ProcSet |-> CASE self \in DioThreads -> "DIO_AcquireSlot"
                                        [] self = "bio" -> "BIO_AcquireInvLock"
                                        [] self = "ast" -> "AST_WaitTrigger"
                                        [] self = "fread" -> "FR_AcquireInvLock"]

DIO_AcquireSlot(self) == /\ pc[self] = "DIO_AcquireSlot"
                         /\ rpc_slots_avail > DioSlotThreshold
                         /\ rpc_slots_avail' = rpc_slots_avail - 1
                         /\ pc' = [pc EXCEPT ![self] = "DIO_SendRPC"]
                         /\ UNCHANGED << inv_lock_readers, inv_lock_writer,
                                         page_lock, ast_needed, ast_complete >>

DIO_SendRPC(self) == /\ pc[self] = "DIO_SendRPC"
                     /\ ast_needed' = TRUE
                     /\ pc' = [pc EXCEPT ![self] = "DIO_WaitReply"]
                     /\ UNCHANGED << rpc_slots_avail, inv_lock_readers,
                                     inv_lock_writer, page_lock, ast_complete >>

DIO_WaitReply(self) == /\ pc[self] = "DIO_WaitReply"
                       /\ ast_complete
                       /\ pc' = [pc EXCEPT ![self] = "DIO_ReleaseSlot"]
                       /\ UNCHANGED << rpc_slots_avail, inv_lock_readers,
                                       inv_lock_writer, page_lock, ast_needed,
                                       ast_complete >>

DIO_ReleaseSlot(self) == /\ pc[self] = "DIO_ReleaseSlot"
                         /\ rpc_slots_avail' = rpc_slots_avail + 1
                         /\ pc' = [pc EXCEPT ![self] = "Done"]
                         /\ UNCHANGED << inv_lock_readers, inv_lock_writer,
                                         page_lock, ast_needed, ast_complete >>

DIO(self) == DIO_AcquireSlot(self) \/ DIO_SendRPC(self)
                \/ DIO_WaitReply(self) \/ DIO_ReleaseSlot(self)

BIO_AcquireInvLock == /\ pc["bio"] = "BIO_AcquireInvLock"
                      /\ ~inv_lock_writer
                      /\ inv_lock_readers' = inv_lock_readers + 1
                      /\ pc' = [pc EXCEPT !["bio"] = "BIO_AcquirePageLock"]
                      /\ UNCHANGED << rpc_slots_avail, inv_lock_writer,
                                      page_lock, ast_needed, ast_complete >>

BIO_AcquirePageLock == /\ pc["bio"] = "BIO_AcquirePageLock"
                       /\ page_lock = "free"
                       /\ page_lock' = "bio"
                       /\ pc' = [pc EXCEPT !["bio"] = "BIO_AcquireSlot"]
                       /\ UNCHANGED << rpc_slots_avail, inv_lock_readers,
                                       inv_lock_writer, ast_needed,
                                       ast_complete >>

BIO_AcquireSlot == /\ pc["bio"] = "BIO_AcquireSlot"
                   /\ rpc_slots_avail > 0
                   /\ rpc_slots_avail' = rpc_slots_avail - 1
                   /\ pc' = [pc EXCEPT !["bio"] = "BIO_WaitReply"]
                   /\ UNCHANGED << inv_lock_readers, inv_lock_writer,
                                   page_lock, ast_needed, ast_complete >>

BIO_WaitReply == /\ pc["bio"] = "BIO_WaitReply"
                 /\ TRUE
                 /\ pc' = [pc EXCEPT !["bio"] = "BIO_ReleaseSlot"]
                 /\ UNCHANGED << rpc_slots_avail, inv_lock_readers,
                                 inv_lock_writer, page_lock, ast_needed,
                                 ast_complete >>

BIO_ReleaseSlot == /\ pc["bio"] = "BIO_ReleaseSlot"
                   /\ rpc_slots_avail' = rpc_slots_avail + 1
                   /\ pc' = [pc EXCEPT !["bio"] = "BIO_ReleasePageLock"]
                   /\ UNCHANGED << inv_lock_readers, inv_lock_writer,
                                   page_lock, ast_needed, ast_complete >>

BIO_ReleasePageLock == /\ pc["bio"] = "BIO_ReleasePageLock"
                       /\ page_lock' = "free"
                       /\ pc' = [pc EXCEPT !["bio"] = "BIO_ReleaseInvLock"]
                       /\ UNCHANGED << rpc_slots_avail, inv_lock_readers,
                                       inv_lock_writer, ast_needed,
                                       ast_complete >>

BIO_ReleaseInvLock == /\ pc["bio"] = "BIO_ReleaseInvLock"
                      /\ inv_lock_readers' = inv_lock_readers - 1
                      /\ pc' = [pc EXCEPT !["bio"] = "Done"]
                      /\ UNCHANGED << rpc_slots_avail, inv_lock_writer,
                                      page_lock, ast_needed, ast_complete >>

BIO == BIO_AcquireInvLock \/ BIO_AcquirePageLock \/ BIO_AcquireSlot
          \/ BIO_WaitReply \/ BIO_ReleaseSlot \/ BIO_ReleasePageLock
          \/ BIO_ReleaseInvLock

AST_WaitTrigger == /\ pc["ast"] = "AST_WaitTrigger"
                   /\ ast_needed
                   /\ pc' = [pc EXCEPT !["ast"] = "AST_AcquireExcl"]
                   /\ UNCHANGED << rpc_slots_avail, inv_lock_readers,
                                   inv_lock_writer, page_lock, ast_needed,
                                   ast_complete >>

AST_AcquireExcl == /\ pc["ast"] = "AST_AcquireExcl"
                   /\ inv_lock_readers = 0 /\ ~inv_lock_writer
                   /\ inv_lock_writer' = TRUE
                   /\ pc' = [pc EXCEPT !["ast"] = "AST_RunCallback"]
                   /\ UNCHANGED << rpc_slots_avail, inv_lock_readers,
                                   page_lock, ast_needed, ast_complete >>

AST_RunCallback == /\ pc["ast"] = "AST_RunCallback"
                   /\ TRUE
                   /\ pc' = [pc EXCEPT !["ast"] = "AST_Release"]
                   /\ UNCHANGED << rpc_slots_avail, inv_lock_readers,
                                   inv_lock_writer, page_lock, ast_needed,
                                   ast_complete >>

AST_Release == /\ pc["ast"] = "AST_Release"
               /\ inv_lock_writer' = FALSE
               /\ ast_complete' = TRUE
               /\ pc' = [pc EXCEPT !["ast"] = "Done"]
               /\ UNCHANGED << rpc_slots_avail, inv_lock_readers, page_lock,
                               ast_needed >>

AST == AST_WaitTrigger \/ AST_AcquireExcl \/ AST_RunCallback \/ AST_Release

FR_AcquireInvLock == /\ pc["fread"] = "FR_AcquireInvLock"
                     /\ ~inv_lock_writer
                     /\ inv_lock_readers' = inv_lock_readers + 1
                     /\ pc' = [pc EXCEPT !["fread"] = "FR_WaitPageLock"]
                     /\ UNCHANGED << rpc_slots_avail, inv_lock_writer,
                                     page_lock, ast_needed, ast_complete >>

FR_WaitPageLock == /\ pc["fread"] = "FR_WaitPageLock"
                   /\ page_lock = "free"
                   /\ page_lock' = "fread"
                   /\ pc' = [pc EXCEPT !["fread"] = "FR_Read"]
                   /\ UNCHANGED << rpc_slots_avail, inv_lock_readers,
                                   inv_lock_writer, ast_needed, ast_complete >>

FR_Read == /\ pc["fread"] = "FR_Read"
           /\ TRUE
           /\ pc' = [pc EXCEPT !["fread"] = "FR_ReleasePageLock"]
           /\ UNCHANGED << rpc_slots_avail, inv_lock_readers, inv_lock_writer,
                           page_lock, ast_needed, ast_complete >>

FR_ReleasePageLock == /\ pc["fread"] = "FR_ReleasePageLock"
                      /\ page_lock' = "free"
                      /\ pc' = [pc EXCEPT !["fread"] = "FR_ReleaseInvLock"]
                      /\ UNCHANGED << rpc_slots_avail, inv_lock_readers,
                                      inv_lock_writer, ast_needed,
                                      ast_complete >>

FR_ReleaseInvLock == /\ pc["fread"] = "FR_ReleaseInvLock"
                     /\ inv_lock_readers' = inv_lock_readers - 1
                     /\ pc' = [pc EXCEPT !["fread"] = "Done"]
                     /\ UNCHANGED << rpc_slots_avail, inv_lock_writer,
                                     page_lock, ast_needed, ast_complete >>

FastRead == FR_AcquireInvLock \/ FR_WaitPageLock \/ FR_Read
               \/ FR_ReleasePageLock \/ FR_ReleaseInvLock

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == BIO \/ AST \/ FastRead
           \/ (\E self \in DioThreads: DIO(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in DioThreads : WF_vars(DIO(self))
        /\ WF_vars(BIO)
        /\ WF_vars(AST)
        /\ WF_vars(FastRead)

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

=============================================================================
