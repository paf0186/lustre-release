---------------------------- MODULE dio_bio_deadlock_eviction ----------------------------
(*
 * Extended PlusCal/TLA+ model of LU-19427 deadlock with concurrent eviction.
 *
 * Base model: dio_bio_deadlock.tla
 *   Four-way deadlock between DIO slots, BIO lock, LDLM AST, invalidate_lock.
 *   Fix: reserve RPC slots so DIO cannot exhaust the entire pool.
 *
 * Extension: concurrent eviction
 *   Server evicts the client, cancelling all locks simultaneously. Each
 *   cancelled lock triggers a BL_AST callback that the AST handler must
 *   process. AST processing requires sending an RPC (lock cancel reply)
 *   back to the server, which needs an RPC slot.
 *
 *   Question: does the reserved-slot fix hold when eviction triggers a
 *   burst of AST callbacks that all need RPC slots?
 *
 *   Scenario:
 *     - DIO threads hold non-reserved RPC slots, waiting for server reply
 *     - Server sends eviction, cancelling NUM_EVICT_LOCKS locks
 *     - Each cancelled lock triggers a BL_AST callback
 *     - Each AST handler needs an RPC slot to send cancel reply
 *     - BIO still needs a slot too (holds shared inv_lock)
 *     - Only RESERVED_SLOTS slots are reserved for non-DIO use
 *     - If NUM_EVICT_LOCKS + 1 (BIO) > RESERVED_SLOTS, potential exhaustion
 *
 * Processes:
 *   DIO \in DioThreads     -- direct I/O read threads (consume non-reserved slots)
 *   BIO = "bio"            -- buffered read thread (needs 1 slot)
 *   AST = "ast"            -- LDLM blocking AST for lock conflict (existing)
 *   FastRead = "fread"     -- fast buffered read (page lock waiter)
 *   Eviction = "evict"     -- server-side eviction trigger
 *   EvictAST \in EvictASTThreads -- AST handlers for evicted locks
 *
 * New resources:
 *   eviction_triggered     -- server has initiated eviction
 *   evict_ast_slots_needed -- how many eviction ASTs still need slots
 *
 * Bugs verified:
 *   LU-19427 -- invalidate_lock deadlock with mixed BIO/DIO
 *   (extension) -- eviction slot exhaustion under reserved-slot fix
 *
 * Source (lustre-release master 47638add78; see dio_bio_deadlock.tla
 * for the base DIO/BIO/AST references):
 *   lustre/osc/osc_request.c
 *     osc_build_rpc          2793-     BRW RPC in-flight accounting
 *                                     (2957-2971: cl_r/cl_w/cl_d_in_flight)
 *     osc_import_event       IMP_EVENT_INVALIDATE 3921-3940:
 *                                     ldlm_namespace_cleanup(ns,
 *                                     LDLM_FL_LOCAL_ONLY) (3926, 3937)
 *   lustre/osc/osc_cache.c
 *     osc_max_rpc_in_flight  1836-1840
 *   lustre/osc/osc_internal.h
 *     rpcs_in_flight          108-111
 *   lustre/ldlm/ldlm_request.c
 *     ldlm_cli_cancel_req    1518-     lock cancel RPC (plain ptlrpc
 *                                     request, not a BRW slot)
 *   lustre/ldlm/ldlm_resource.c
 *     ldlm_namespace_cleanup 1222-1235
 *
 * Validated against: lustre-release master 47638add78 (2026-09-06)
 * Validation notes:
 *   - DISCREPANCY-OPEN (inherited): RESERVED_SLOTS / the reserved-slot
 *     fix does not exist in this tree; see dio_bio_deadlock.tla.  The
 *     landed LU-19427 fix was reverted (7e0ccbf241) and LU-19427 is
 *     Reopened.
 *   - The eviction premise is hypothetical with respect to the code:
 *     (a) on eviction the client cancels its locks locally
 *         (ldlm_namespace_cleanup with LDLM_FL_LOCAL_ONLY from
 *         osc_import_event, osc_request.c:3926/3937) and sends no
 *         cancel RPCs; (b) a lock cancel RPC (ldlm_cli_cancel_req) is
 *         an ordinary ptlrpc request and is never counted against
 *         max_rpcs_in_flight, which only counts BRW RPCs
 *         (rpcs_in_flight = cl_r_in_flight + cl_w_in_flight); (c) BRW
 *         RPCs of an invalidated import fail immediately, freeing the
 *         DIO "slots".  So EvictAST competing with BIO for BRW slots
 *         has no code analog.  The model is kept as an exploration of
 *         the reserved-slot idea; do not read its PASS results as
 *         statements about the current code.
 *)

EXTENDS Integers, FiniteSets, Sequences, TLC

CONSTANTS
    MAX_SLOTS,          \* RPC slot pool size (max_rpcs_in_flight)
    NUM_DIO,            \* Number of concurrent DIO read threads
    RESERVED_SLOTS,     \* Slots reserved for non-DIO use (fix parameter)
    NUM_EVICT_LOCKS,    \* Number of locks cancelled by eviction (each needs AST + slot)
    InjectBug19427      \* TRUE = DIO ignores reserved slots (original bug)
                        \* FALSE = DIO respects reserved slots (fix)

ASSUME MAX_SLOTS \in 1..8
ASSUME NUM_DIO \in 1..8
ASSUME RESERVED_SLOTS \in 0..MAX_SLOTS
ASSUME NUM_EVICT_LOCKS \in 1..4
ASSUME NUM_DIO >= MAX_SLOTS - RESERVED_SLOTS  \* DIO can exhaust non-reserved slots

DioNums == 1..NUM_DIO
EvictNums == 1..NUM_EVICT_LOCKS

(* --algorithm dio_bio_deadlock_eviction

variables
    \* ---- RPC slot pool (osc_request.c: max_rpcs_in_flight) ----
    rpc_slots_avail = MAX_SLOTS,

    \* ---- invalidate_lock (rw_semaphore on mapping) ----
    inv_lock_readers = 0,
    inv_lock_writer = FALSE,

    \* ---- Page/folio lock (per-page mutex) ----
    page_lock = "free",

    \* ---- Server-side AST dependency (existing conflict) ----
    ast_needed = FALSE,
    ast_complete = FALSE,

    \* ---- Eviction state ----
    eviction_triggered = FALSE,    \* Server has sent eviction notice
    evict_asts_done = 0;           \* Count of completed eviction ASTs

define
    DioThreads == {ToString(i) : i \in DioNums}
    EvictASTThreads == {"evast_" \o ToString(i) : i \in EvictNums}

    \* Minimum available slots before DIO can acquire one.
    \* BUG:  0 -- DIO can exhaust all slots
    \* FIX:  RESERVED_SLOTS -- DIO reserves slots for non-DIO use
    DioSlotThreshold == IF InjectBug19427 THEN 0 ELSE RESERVED_SLOTS

    \* ========== TYPE INVARIANT ==========
    TypeOK ==
        /\ rpc_slots_avail \in 0..MAX_SLOTS
        /\ inv_lock_readers \in 0..(3 + NUM_EVICT_LOCKS)
        /\ inv_lock_writer \in BOOLEAN
        /\ page_lock \in {"free", "bio", "fread"}
        /\ ast_needed \in BOOLEAN
        /\ ast_complete \in BOOLEAN
        /\ eviction_triggered \in BOOLEAN
        /\ evict_asts_done \in 0..NUM_EVICT_LOCKS

    \* ========== SAFETY: NO CIRCULAR-WAIT DEADLOCK ==========
    \* Original LU-19427 deadlock pattern
    NoDeadlock ==
        ~( /\ \A d \in DioThreads : pc[d] = "DIO_WaitReply"
           /\ pc["bio"] = "BIO_AcquireSlot"
           /\ pc["ast"] = "AST_AcquireExcl"
           /\ rpc_slots_avail = 0
           /\ inv_lock_readers > 0
         )

    \* ========== EVICTION DEADLOCK ==========
    \* Eviction-induced deadlock: DIO holds non-reserved slots waiting
    \* for AST. Eviction ASTs need slots from the reserved pool but
    \* there aren't enough. BIO also needs a slot, holding inv_lock
    \* shared, blocking the conflict AST from getting exclusive.
    \*
    \* Deadlock if:
    \*   - All DIO threads waiting for AST completion (holding slots)
    \*   - BIO waiting for a slot (holding shared inv_lock)
    \*   - Conflict AST waiting for exclusive inv_lock
    \*   - Some eviction ASTs waiting for slots
    \*   - No slots available (all exhausted)
    NoEvictionDeadlock ==
        ~( /\ \A d \in DioThreads : pc[d] = "DIO_WaitReply"
           /\ pc["bio"] = "BIO_AcquireSlot"
           /\ pc["ast"] = "AST_AcquireExcl"
           /\ \E e \in EvictASTThreads : pc[e] = "EA_AcquireSlot"
           /\ rpc_slots_avail = 0
           /\ inv_lock_readers > 0
         )

    \* Combined: neither deadlock pattern can occur
    NoAnyDeadlock == NoDeadlock /\ NoEvictionDeadlock

    \* ========== SLOT EXHAUSTION SAFETY ==========
    \* When the fix is active, non-DIO consumers should always be able
    \* to eventually get a slot (i.e., slots never permanently 0 with
    \* waiters). This is captured via the liveness property below.

    \* ========== LIVENESS ==========
    AllComplete ==
        <>( /\ \A d \in DioThreads : pc[d] = "Done"
            /\ pc["bio"] = "Done"
            /\ pc["ast"] = "Done"
            /\ pc["fread"] = "Done"
            /\ pc["evict"] = "Done"
            /\ \A e \in EvictASTThreads : pc[e] = "Done"
          )

    DIOComplete == <>(\A d \in DioThreads : pc[d] = "Done")

    EvictionComplete == <>(pc["evict"] = "Done" /\ \A e \in EvictASTThreads : pc[e] = "Done")
end define;

\* ================================================================
\* DIO threads: direct I/O read RPCs.
\*
\* Each DIO thread acquires an RPC slot (respecting reserved-slot
\* threshold when fix is active), sends a read RPC, waits for
\* server reply. Server reply requires AST completion.
\* ================================================================
fair process DIO \in DioThreads
begin
DIO_AcquireSlot:
    await rpc_slots_avail > DioSlotThreshold;
    rpc_slots_avail := rpc_slots_avail - 1;

DIO_SendRPC:
    ast_needed := TRUE;

DIO_WaitReply:
    await ast_complete;

DIO_ReleaseSlot:
    rpc_slots_avail := rpc_slots_avail + 1;
end process;

\* ================================================================
\* BIO thread: buffered read.
\*
\* Acquires shared invalidate_lock, page lock, then needs an RPC slot.
\* In the deadlock scenario, holds shared inv_lock while waiting for
\* a slot -- blocking AST from getting exclusive inv_lock.
\* ================================================================
fair process BIO = "bio"
begin
BIO_AcquireInvLock:
    await ~inv_lock_writer;
    inv_lock_readers := inv_lock_readers + 1;

BIO_AcquirePageLock:
    await page_lock = "free";
    page_lock := "bio";

BIO_AcquireSlot:
    await rpc_slots_avail > 0;
    rpc_slots_avail := rpc_slots_avail - 1;

BIO_WaitReply:
    skip;

BIO_ReleaseSlot:
    rpc_slots_avail := rpc_slots_avail + 1;

BIO_ReleasePageLock:
    page_lock := "free";

BIO_ReleaseInvLock:
    inv_lock_readers := inv_lock_readers - 1;
end process;

\* ================================================================
\* LDLM AST handler: blocking AST for lock conflict (existing).
\*
\* Triggered by DIO RPCs. Needs exclusive invalidate_lock to
\* invalidate cached pages.
\* ================================================================
fair process AST = "ast"
begin
AST_WaitTrigger:
    await ast_needed;

AST_AcquireExcl:
    await inv_lock_readers = 0 /\ ~inv_lock_writer;
    inv_lock_writer := TRUE;

AST_RunCallback:
    skip;

AST_Release:
    inv_lock_writer := FALSE;
    ast_complete := TRUE;
end process;

\* ================================================================
\* FastRead thread: fast buffered read path.
\*
\* Acquires shared invalidate_lock, waits for page lock held by BIO.
\* ================================================================
fair process FastRead = "fread"
begin
FR_AcquireInvLock:
    await ~inv_lock_writer;
    inv_lock_readers := inv_lock_readers + 1;

FR_WaitPageLock:
    await page_lock = "free";
    page_lock := "fread";

FR_Read:
    skip;

FR_ReleasePageLock:
    page_lock := "free";

FR_ReleaseInvLock:
    inv_lock_readers := inv_lock_readers - 1;
end process;

\* ================================================================
\* Eviction process: server evicts the client.
\*
\* Eviction cancels all client locks simultaneously, triggering
\* BL_AST callbacks for each. This sets eviction_triggered which
\* unblocks the EvictAST threads.
\*
\* In the real system, eviction is driven by the server (e.g.,
\* client timeout, admin action). The client must process all the
\* AST callbacks to release locks and send cancel RPCs.
\* ================================================================
fair process Eviction = "evict"
begin
EVICT_Trigger:
    \* Server decides to evict -- all client locks are cancelled
    eviction_triggered := TRUE;

EVICT_WaitComplete:
    \* Wait for all eviction ASTs to finish processing
    await evict_asts_done = NUM_EVICT_LOCKS;
end process;

\* ================================================================
\* Eviction AST handlers: one per cancelled lock.
\*
\* Each eviction AST handler must:
\*   1. Acquire shared invalidate_lock (to flush pages under the lock)
\*   2. Acquire an RPC slot (to send lock cancel reply to server)
\*   3. Send the cancel RPC
\*   4. Release resources
\*
\* The critical question: when DIO holds non-reserved slots and
\* eviction triggers NUM_EVICT_LOCKS ASTs, each needing a slot,
\* plus BIO also needs a slot -- are RESERVED_SLOTS enough?
\*
\* These model the ldlm_cancel_callback -> osc_lock_flush path
\* that eviction triggers for each cancelled extent lock.
\* ================================================================
fair process EvictAST \in EvictASTThreads
begin
EA_WaitTrigger:
    \* Wait for eviction to trigger this AST
    await eviction_triggered;

EA_AcquireInvLock:
    \* Eviction AST needs shared invalidate_lock to flush pages
    \* (same as BIO path -- osc_lock_flush -> invalidate pages)
    await ~inv_lock_writer;
    inv_lock_readers := inv_lock_readers + 1;

EA_AcquireSlot:
    \* Need an RPC slot to send lock cancel reply to server.
    \* This is the critical contention point: eviction ASTs
    \* compete with BIO for the reserved slots.
    await rpc_slots_avail > 0;
    rpc_slots_avail := rpc_slots_avail - 1;

EA_SendCancel:
    \* Send lock cancel RPC to server
    skip;

EA_ReleaseSlot:
    rpc_slots_avail := rpc_slots_avail + 1;

EA_ReleaseInvLock:
    inv_lock_readers := inv_lock_readers - 1;

EA_Done:
    evict_asts_done := evict_asts_done + 1;
end process;

end algorithm; *)

\* BEGIN TRANSLATION
VARIABLES rpc_slots_avail, inv_lock_readers, inv_lock_writer, page_lock,
          ast_needed, ast_complete, eviction_triggered, evict_asts_done, pc

(* define statement *)
DioThreads == {ToString(i) : i \in DioNums}
EvictASTThreads == {"evast_" \o ToString(i) : i \in EvictNums}




DioSlotThreshold == IF InjectBug19427 THEN 0 ELSE RESERVED_SLOTS


TypeOK ==
    /\ rpc_slots_avail \in 0..MAX_SLOTS
    /\ inv_lock_readers \in 0..(3 + NUM_EVICT_LOCKS)
    /\ inv_lock_writer \in BOOLEAN
    /\ page_lock \in {"free", "bio", "fread"}
    /\ ast_needed \in BOOLEAN
    /\ ast_complete \in BOOLEAN
    /\ eviction_triggered \in BOOLEAN
    /\ evict_asts_done \in 0..NUM_EVICT_LOCKS



NoDeadlock ==
    ~( /\ \A d \in DioThreads : pc[d] = "DIO_WaitReply"
       /\ pc["bio"] = "BIO_AcquireSlot"
       /\ pc["ast"] = "AST_AcquireExcl"
       /\ rpc_slots_avail = 0
       /\ inv_lock_readers > 0
     )










NoEvictionDeadlock ==
    ~( /\ \A d \in DioThreads : pc[d] = "DIO_WaitReply"
       /\ pc["bio"] = "BIO_AcquireSlot"
       /\ pc["ast"] = "AST_AcquireExcl"
       /\ \E e \in EvictASTThreads : pc[e] = "EA_AcquireSlot"
       /\ rpc_slots_avail = 0
       /\ inv_lock_readers > 0
     )


NoAnyDeadlock == NoDeadlock /\ NoEvictionDeadlock




AllComplete ==
    <>( /\ \A d \in DioThreads : pc[d] = "Done"
        /\ pc["bio"] = "Done"
        /\ pc["ast"] = "Done"
        /\ pc["fread"] = "Done"
        /\ pc["evict"] = "Done"
        /\ \A e \in EvictASTThreads : pc[e] = "Done"
      )

DIOComplete == <>(\A d \in DioThreads : pc[d] = "Done")

EvictionComplete == <>(pc["evict"] = "Done" /\ \A e \in EvictASTThreads : pc[e] = "Done")


vars == << rpc_slots_avail, inv_lock_readers, inv_lock_writer, page_lock,
           ast_needed, ast_complete, eviction_triggered, evict_asts_done, pc >>

ProcSet == (DioThreads) \cup {"bio"} \cup {"ast"} \cup {"fread"} \cup {"evict"} \cup (EvictASTThreads)

Init == (* Global variables *)
        /\ rpc_slots_avail = MAX_SLOTS
        /\ inv_lock_readers = 0
        /\ inv_lock_writer = FALSE
        /\ page_lock = "free"
        /\ ast_needed = FALSE
        /\ ast_complete = FALSE
        /\ eviction_triggered = FALSE
        /\ evict_asts_done = 0
        /\ pc = [self \in ProcSet |-> CASE self \in DioThreads -> "DIO_AcquireSlot"
                                        [] self = "bio" -> "BIO_AcquireInvLock"
                                        [] self = "ast" -> "AST_WaitTrigger"
                                        [] self = "fread" -> "FR_AcquireInvLock"
                                        [] self = "evict" -> "EVICT_Trigger"
                                        [] self \in EvictASTThreads -> "EA_WaitTrigger"]

DIO_AcquireSlot(self) == /\ pc[self] = "DIO_AcquireSlot"
                         /\ rpc_slots_avail > DioSlotThreshold
                         /\ rpc_slots_avail' = rpc_slots_avail - 1
                         /\ pc' = [pc EXCEPT ![self] = "DIO_SendRPC"]
                         /\ UNCHANGED << inv_lock_readers, inv_lock_writer,
                                         page_lock, ast_needed, ast_complete,
                                         eviction_triggered, evict_asts_done >>

DIO_SendRPC(self) == /\ pc[self] = "DIO_SendRPC"
                     /\ ast_needed' = TRUE
                     /\ pc' = [pc EXCEPT ![self] = "DIO_WaitReply"]
                     /\ UNCHANGED << rpc_slots_avail, inv_lock_readers,
                                     inv_lock_writer, page_lock, ast_complete,
                                     eviction_triggered, evict_asts_done >>

DIO_WaitReply(self) == /\ pc[self] = "DIO_WaitReply"
                       /\ ast_complete
                       /\ pc' = [pc EXCEPT ![self] = "DIO_ReleaseSlot"]
                       /\ UNCHANGED << rpc_slots_avail, inv_lock_readers,
                                       inv_lock_writer, page_lock, ast_needed,
                                       ast_complete, eviction_triggered,
                                       evict_asts_done >>

DIO_ReleaseSlot(self) == /\ pc[self] = "DIO_ReleaseSlot"
                         /\ rpc_slots_avail' = rpc_slots_avail + 1
                         /\ pc' = [pc EXCEPT ![self] = "Done"]
                         /\ UNCHANGED << inv_lock_readers, inv_lock_writer,
                                         page_lock, ast_needed, ast_complete,
                                         eviction_triggered, evict_asts_done >>

DIO(self) == DIO_AcquireSlot(self) \/ DIO_SendRPC(self)
                \/ DIO_WaitReply(self) \/ DIO_ReleaseSlot(self)

BIO_AcquireInvLock == /\ pc["bio"] = "BIO_AcquireInvLock"
                      /\ ~inv_lock_writer
                      /\ inv_lock_readers' = inv_lock_readers + 1
                      /\ pc' = [pc EXCEPT !["bio"] = "BIO_AcquirePageLock"]
                      /\ UNCHANGED << rpc_slots_avail, inv_lock_writer,
                                      page_lock, ast_needed, ast_complete,
                                      eviction_triggered, evict_asts_done >>

BIO_AcquirePageLock == /\ pc["bio"] = "BIO_AcquirePageLock"
                       /\ page_lock = "free"
                       /\ page_lock' = "bio"
                       /\ pc' = [pc EXCEPT !["bio"] = "BIO_AcquireSlot"]
                       /\ UNCHANGED << rpc_slots_avail, inv_lock_readers,
                                       inv_lock_writer, ast_needed,
                                       ast_complete, eviction_triggered,
                                       evict_asts_done >>

BIO_AcquireSlot == /\ pc["bio"] = "BIO_AcquireSlot"
                   /\ rpc_slots_avail > 0
                   /\ rpc_slots_avail' = rpc_slots_avail - 1
                   /\ pc' = [pc EXCEPT !["bio"] = "BIO_WaitReply"]
                   /\ UNCHANGED << inv_lock_readers, inv_lock_writer,
                                   page_lock, ast_needed, ast_complete,
                                   eviction_triggered, evict_asts_done >>

BIO_WaitReply == /\ pc["bio"] = "BIO_WaitReply"
                 /\ TRUE
                 /\ pc' = [pc EXCEPT !["bio"] = "BIO_ReleaseSlot"]
                 /\ UNCHANGED << rpc_slots_avail, inv_lock_readers,
                                 inv_lock_writer, page_lock, ast_needed,
                                 ast_complete, eviction_triggered,
                                 evict_asts_done >>

BIO_ReleaseSlot == /\ pc["bio"] = "BIO_ReleaseSlot"
                   /\ rpc_slots_avail' = rpc_slots_avail + 1
                   /\ pc' = [pc EXCEPT !["bio"] = "BIO_ReleasePageLock"]
                   /\ UNCHANGED << inv_lock_readers, inv_lock_writer,
                                   page_lock, ast_needed, ast_complete,
                                   eviction_triggered, evict_asts_done >>

BIO_ReleasePageLock == /\ pc["bio"] = "BIO_ReleasePageLock"
                       /\ page_lock' = "free"
                       /\ pc' = [pc EXCEPT !["bio"] = "BIO_ReleaseInvLock"]
                       /\ UNCHANGED << rpc_slots_avail, inv_lock_readers,
                                       inv_lock_writer, ast_needed,
                                       ast_complete, eviction_triggered,
                                       evict_asts_done >>

BIO_ReleaseInvLock == /\ pc["bio"] = "BIO_ReleaseInvLock"
                      /\ inv_lock_readers' = inv_lock_readers - 1
                      /\ pc' = [pc EXCEPT !["bio"] = "Done"]
                      /\ UNCHANGED << rpc_slots_avail, inv_lock_writer,
                                      page_lock, ast_needed, ast_complete,
                                      eviction_triggered, evict_asts_done >>

BIO == BIO_AcquireInvLock \/ BIO_AcquirePageLock \/ BIO_AcquireSlot
          \/ BIO_WaitReply \/ BIO_ReleaseSlot \/ BIO_ReleasePageLock
          \/ BIO_ReleaseInvLock

AST_WaitTrigger == /\ pc["ast"] = "AST_WaitTrigger"
                   /\ ast_needed
                   /\ pc' = [pc EXCEPT !["ast"] = "AST_AcquireExcl"]
                   /\ UNCHANGED << rpc_slots_avail, inv_lock_readers,
                                   inv_lock_writer, page_lock, ast_needed,
                                   ast_complete, eviction_triggered,
                                   evict_asts_done >>

AST_AcquireExcl == /\ pc["ast"] = "AST_AcquireExcl"
                   /\ inv_lock_readers = 0 /\ ~inv_lock_writer
                   /\ inv_lock_writer' = TRUE
                   /\ pc' = [pc EXCEPT !["ast"] = "AST_RunCallback"]
                   /\ UNCHANGED << rpc_slots_avail, inv_lock_readers,
                                   page_lock, ast_needed, ast_complete,
                                   eviction_triggered, evict_asts_done >>

AST_RunCallback == /\ pc["ast"] = "AST_RunCallback"
                   /\ TRUE
                   /\ pc' = [pc EXCEPT !["ast"] = "AST_Release"]
                   /\ UNCHANGED << rpc_slots_avail, inv_lock_readers,
                                   inv_lock_writer, page_lock, ast_needed,
                                   ast_complete, eviction_triggered,
                                   evict_asts_done >>

AST_Release == /\ pc["ast"] = "AST_Release"
               /\ inv_lock_writer' = FALSE
               /\ ast_complete' = TRUE
               /\ pc' = [pc EXCEPT !["ast"] = "Done"]
               /\ UNCHANGED << rpc_slots_avail, inv_lock_readers, page_lock,
                               ast_needed, eviction_triggered, evict_asts_done >>

AST == AST_WaitTrigger \/ AST_AcquireExcl \/ AST_RunCallback \/ AST_Release

FR_AcquireInvLock == /\ pc["fread"] = "FR_AcquireInvLock"
                     /\ ~inv_lock_writer
                     /\ inv_lock_readers' = inv_lock_readers + 1
                     /\ pc' = [pc EXCEPT !["fread"] = "FR_WaitPageLock"]
                     /\ UNCHANGED << rpc_slots_avail, inv_lock_writer,
                                     page_lock, ast_needed, ast_complete,
                                     eviction_triggered, evict_asts_done >>

FR_WaitPageLock == /\ pc["fread"] = "FR_WaitPageLock"
                   /\ page_lock = "free"
                   /\ page_lock' = "fread"
                   /\ pc' = [pc EXCEPT !["fread"] = "FR_Read"]
                   /\ UNCHANGED << rpc_slots_avail, inv_lock_readers,
                                   inv_lock_writer, ast_needed, ast_complete,
                                   eviction_triggered, evict_asts_done >>

FR_Read == /\ pc["fread"] = "FR_Read"
           /\ TRUE
           /\ pc' = [pc EXCEPT !["fread"] = "FR_ReleasePageLock"]
           /\ UNCHANGED << rpc_slots_avail, inv_lock_readers, inv_lock_writer,
                           page_lock, ast_needed, ast_complete,
                           eviction_triggered, evict_asts_done >>

FR_ReleasePageLock == /\ pc["fread"] = "FR_ReleasePageLock"
                      /\ page_lock' = "free"
                      /\ pc' = [pc EXCEPT !["fread"] = "FR_ReleaseInvLock"]
                      /\ UNCHANGED << rpc_slots_avail, inv_lock_readers,
                                      inv_lock_writer, ast_needed,
                                      ast_complete, eviction_triggered,
                                      evict_asts_done >>

FR_ReleaseInvLock == /\ pc["fread"] = "FR_ReleaseInvLock"
                     /\ inv_lock_readers' = inv_lock_readers - 1
                     /\ pc' = [pc EXCEPT !["fread"] = "Done"]
                     /\ UNCHANGED << rpc_slots_avail, inv_lock_writer,
                                     page_lock, ast_needed, ast_complete,
                                     eviction_triggered, evict_asts_done >>

FastRead == FR_AcquireInvLock \/ FR_WaitPageLock \/ FR_Read
               \/ FR_ReleasePageLock \/ FR_ReleaseInvLock

EVICT_Trigger == /\ pc["evict"] = "EVICT_Trigger"
                 /\ eviction_triggered' = TRUE
                 /\ pc' = [pc EXCEPT !["evict"] = "EVICT_WaitComplete"]
                 /\ UNCHANGED << rpc_slots_avail, inv_lock_readers,
                                 inv_lock_writer, page_lock, ast_needed,
                                 ast_complete, evict_asts_done >>

EVICT_WaitComplete == /\ pc["evict"] = "EVICT_WaitComplete"
                      /\ evict_asts_done = NUM_EVICT_LOCKS
                      /\ pc' = [pc EXCEPT !["evict"] = "Done"]
                      /\ UNCHANGED << rpc_slots_avail, inv_lock_readers,
                                      inv_lock_writer, page_lock, ast_needed,
                                      ast_complete, eviction_triggered,
                                      evict_asts_done >>

Eviction == EVICT_Trigger \/ EVICT_WaitComplete

EA_WaitTrigger(self) == /\ pc[self] = "EA_WaitTrigger"
                        /\ eviction_triggered
                        /\ pc' = [pc EXCEPT ![self] = "EA_AcquireInvLock"]
                        /\ UNCHANGED << rpc_slots_avail, inv_lock_readers,
                                        inv_lock_writer, page_lock, ast_needed,
                                        ast_complete, eviction_triggered,
                                        evict_asts_done >>

EA_AcquireInvLock(self) == /\ pc[self] = "EA_AcquireInvLock"
                           /\ ~inv_lock_writer
                           /\ inv_lock_readers' = inv_lock_readers + 1
                           /\ pc' = [pc EXCEPT ![self] = "EA_AcquireSlot"]
                           /\ UNCHANGED << rpc_slots_avail, inv_lock_writer,
                                           page_lock, ast_needed, ast_complete,
                                           eviction_triggered, evict_asts_done >>

EA_AcquireSlot(self) == /\ pc[self] = "EA_AcquireSlot"
                        /\ rpc_slots_avail > 0
                        /\ rpc_slots_avail' = rpc_slots_avail - 1
                        /\ pc' = [pc EXCEPT ![self] = "EA_SendCancel"]
                        /\ UNCHANGED << inv_lock_readers, inv_lock_writer,
                                        page_lock, ast_needed, ast_complete,
                                        eviction_triggered, evict_asts_done >>

EA_SendCancel(self) == /\ pc[self] = "EA_SendCancel"
                       /\ TRUE
                       /\ pc' = [pc EXCEPT ![self] = "EA_ReleaseSlot"]
                       /\ UNCHANGED << rpc_slots_avail, inv_lock_readers,
                                       inv_lock_writer, page_lock, ast_needed,
                                       ast_complete, eviction_triggered,
                                       evict_asts_done >>

EA_ReleaseSlot(self) == /\ pc[self] = "EA_ReleaseSlot"
                        /\ rpc_slots_avail' = rpc_slots_avail + 1
                        /\ pc' = [pc EXCEPT ![self] = "EA_ReleaseInvLock"]
                        /\ UNCHANGED << inv_lock_readers, inv_lock_writer,
                                        page_lock, ast_needed, ast_complete,
                                        eviction_triggered, evict_asts_done >>

EA_ReleaseInvLock(self) == /\ pc[self] = "EA_ReleaseInvLock"
                           /\ inv_lock_readers' = inv_lock_readers - 1
                           /\ pc' = [pc EXCEPT ![self] = "EA_Done"]
                           /\ UNCHANGED << rpc_slots_avail, inv_lock_writer,
                                           page_lock, ast_needed, ast_complete,
                                           eviction_triggered, evict_asts_done >>

EA_Done(self) == /\ pc[self] = "EA_Done"
                 /\ evict_asts_done' = evict_asts_done + 1
                 /\ pc' = [pc EXCEPT ![self] = "Done"]
                 /\ UNCHANGED << rpc_slots_avail, inv_lock_readers,
                                 inv_lock_writer, page_lock, ast_needed,
                                 ast_complete, eviction_triggered >>

EvictAST(self) == EA_WaitTrigger(self) \/ EA_AcquireInvLock(self)
                     \/ EA_AcquireSlot(self) \/ EA_SendCancel(self)
                     \/ EA_ReleaseSlot(self) \/ EA_ReleaseInvLock(self)
                     \/ EA_Done(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == BIO \/ AST \/ FastRead \/ Eviction
           \/ (\E self \in DioThreads: DIO(self))
           \/ (\E self \in EvictASTThreads: EvictAST(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in DioThreads : WF_vars(DIO(self))
        /\ WF_vars(BIO)
        /\ WF_vars(AST)
        /\ WF_vars(FastRead)
        /\ WF_vars(Eviction)
        /\ \A self \in EvictASTThreads : WF_vars(EvictAST(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

=============================================================================
