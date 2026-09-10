------------------------ MODULE ldlm_dual_reprocess ------------------------
(*
 * Model: LDLM dual concurrent reprocessing race
 *
 * Two threads call ldlm_reprocess_all() concurrently on the same
 * resource.  This happens when:
 *   - Two exports disconnect, each cancelling a granted lock and
 *     calling ldlm_reprocess_all (ldlm_cancel_lock_for_export)
 *   - A lock convert and a cancel race (ldlm_handle_convert0 vs
 *     ldlm_handle_cancel)
 *   - ldlm_handle_enqueue error path + normal path (ldlm_lockd.c:1579, 1585)
 *
 * Scenario:
 *   - Resource R has holders H1 (EX) and H2 (EX) -- impossible
 *     simultaneously, so we model holders H1 and H2 as sequential
 *     EX holders being cancelled by export disconnect.
 *
 * Actually: model a single EX holder with waiters W1, W2, W3.
 * Two cancel threads (CancelA, CancelB) race to cancel the holder
 * and call reprocess_all.  Only one cancel succeeds (the holder is
 * a single lock), but both threads call reprocess_all.
 *
 * Alternatively: H1 holds EX, W1/W2/W3 wait.  BL_AST sent to H1.
 * H1 sends CANCEL.  Server thread T1 handles the cancel:
 *   - ldlm_lock_cancel(H1) under lr_lock
 *   - ldlm_reprocess_all(res)  <- reprocessor A
 * Meanwhile, a lock convert arrives from another client for a
 * DIFFERENT lock on the same resource.  Server thread T2:
 *   - ldlm_handle_convert0 -> ldlm_inodebits_drop + reprocess_all
 *   <- reprocessor B
 *
 * Simplified model:
 *   - H1 holds EX.  W1, W2 wait for EX (or W1 PR, W2 PR).
 *   - CancelThread: cancels H1, then calls reprocess_all (RP_A)
 *   - ReprocessThread: external trigger, calls reprocess_all (RP_B)
 *   - Both RP_A and RP_B can be in their BL_AST window at different
 *     times, and both iterate the waiting queue under lr_lock.
 *
 * Key question: can the interleaving of two reprocess_all calls
 * cause a waiting lock to get stuck (never granted)?
 *
 * The fix relies on lr_lock serializing the grant checks and
 * ERESTART re-scanning.  If correct, no waiting lock should be
 * stuck at termination.
 *
 * Additional race: A granted lock's export can disconnect during
 * or after reprocessing (LU-14522).  If the lock is destroyed
 * without calling ldlm_reprocess_all, remaining waiters get stuck.
 * The FailedLock process models this race.
 *
 * Source (lustre-release master 47638add78):
 *   ldlm_cancel_lock_for_export  ldlm_lock.c:2566-2585
 *   ldlm_request_cancel          ldlm_lockd.c:1716-1810
 *     (ldlm_reprocess_all per resource at 1774 and 1805)
 *   ldlm_handle_convert0         ldlm_lockd.c:1625-1708
 *     (ldlm_inodebits_drop 1687, ldlm_reprocess_all 1695)
 *   ldlm_handle_enqueue          ldlm_lockd.c:1248-1595
 *     (failed-enqueue path 1569-1581, LU-14522; success path
 *      ldlm_reprocess_all 1583-1586)
 *   ldlm_reprocess_all           ldlm_lock.c:2430-2433
 *   __ldlm_reprocess_all         ldlm_lock.c:2383-2428
 *   ldlm_reprocess_queue         ldlm_lock.c:1958-2020
 *     (unlock_res 2006, ldlm_run_ast_work 2008, lock_res 2011,
 *      GOTO restart on -ERESTART 2013)
 *   ldlm_reprocess_inodebits_queue ldlm_inodebits.c:47-124
 *   ldlm_lock_cancel             ldlm_lock.c:2496-2538
 *
 * Validated against: lustre-release master 47638add78 (2026-09-06)
 *
 * Validation notes: function names and the lr_lock drop / BL_AST
 * send / relock / restart structure match; ldlm_handle_enqueue0 is
 * now ldlm_handle_enqueue.  Two concurrent ldlm_reprocess_all calls
 * are still serialized only by lr_lock (no per-resource reprocess
 * mutex), as modeled.  FL_Destroy raising the active reprocessor's
 * erestart abstracts ldlm_handle_ast_error (ldlm_lockd.c:686-756)
 * returning -ERESTART when the BL_AST target was already cancelled.
 * The bl_ast_list inside ldlm_reprocess_queue is populated only for
 * the RECOVERY intention in this tree (plain/extent RESCAN collect
 * no BL_ASTs); IBITS RESCAN goes through
 * ldlm_reprocess_inodebits_queue, which has the same drop / send /
 * relock / restart shape (108-117).
 *)
EXTENDS Integers, FiniteSets, TLC

CONSTANTS
    NumWaiters,       \* 2 or 3
    CompatibleMode,   \* TRUE = PR waiters (compatible with each other)
    InjectBugSkipRescan,  \* TRUE = skip ERESTART rescan in RP_A
    InjectBugNoReprocessOnFail
                      \* TRUE = LU-14522: when export disconnects during
                      \* enqueue, the granted lock is destroyed but
                      \* ldlm_reprocess_all is not called.  Remaining
                      \* waiters that conflicted only with the destroyed
                      \* lock get stuck permanently.

ASSUME NumWaiters \in 2..3

Waiters == 1..NumWaiters

(* --algorithm ldlm_dual_reprocess

variables
    lr_lock = "free",
    holder_active = TRUE,

    \* Lock states: "waiting", "granted", "none"
    lock_state = [i \in Waiters |-> "waiting"],
    grant_count = [i \in Waiters |-> 0],

    \* RP_A state (triggered by cancel)
    rpa_phase = "idle",
    rpa_cursor = 1,
    rpa_needs_blast = FALSE,
    rpa_erestart = FALSE,

    \* RP_B state (triggered externally)
    rpb_phase = "idle",
    rpb_cursor = 1,
    rpb_needs_blast = FALSE,
    rpb_erestart = FALSE,

    \* FailedLock state
    fl_cursor = 1;

define
    IsGranted(i) == lock_state[i] = "granted"
    GrantedCount == Cardinality({i \in Waiters : IsGranted(i)})
    WaitingCount == Cardinality({i \in Waiters : lock_state[i] = "waiting"})

    \* Safety: no lock granted twice
    NoDoubleGrant == \A i \in Waiters : grant_count[i] <= 1

    \* Safety: at most one EX granted (unless PR mode)
    GrantedCompatible ==
        (~holder_active /\ ~CompatibleMode) => GrantedCount <= 1

    \* Safety: no grants while holder active
    NoGrantWhileHeld ==
        holder_active => GrantedCount = 0

    \* Terminal: no waiting lock should remain grantable when all done
    NoStuckWaiter ==
        (pc["cancel_thread"] = "Done"
         /\ pc["reprocess_a"] = "Done"
         /\ pc["reprocess_b"] = "Done"
         /\ pc["failed_lock"] = "Done") =>
            ~(\E i \in Waiters :
                lock_state[i] = "waiting"
                /\ ~holder_active
                /\ (CompatibleMode
                    \/ ~(\E j \in Waiters : j /= i /\ IsGranted(j))))

    \* Terminal: if holder cancelled and all processors done,
    \* at least one waiter must be granted (or all cancelled/gone)
    NoMissedGrant ==
        (pc["cancel_thread"] = "Done"
         /\ pc["reprocess_a"] = "Done"
         /\ pc["reprocess_b"] = "Done"
         /\ pc["failed_lock"] = "Done"
         /\ ~holder_active) =>
            IF CompatibleMode
            THEN WaitingCount = 0  \* All should be granted
            ELSE (WaitingCount = 0 \/ GrantedCount > 0)

    TypeOK ==
        /\ \A i \in Waiters : lock_state[i] \in {"waiting", "granted", "none"}
        /\ \A i \in Waiters : grant_count[i] \in 0..3
        /\ rpa_cursor \in 1..(NumWaiters+1)
        /\ rpb_cursor \in 1..(NumWaiters+1)
        /\ fl_cursor \in 1..(NumWaiters+1)
end define;

macro TryGrant(i) begin
    if ~holder_active
       /\ (CompatibleMode \/ ~(\E j \in Waiters : j /= i /\ IsGranted(j)))
       /\ lock_state[i] = "waiting" then
        lock_state[i] := "granted";
        grant_count[i] := grant_count[i] + 1;
    end if;
end macro;

\* ================================================================
\* CancelThread: Cancels holder H1, then triggers RP_A
\* Models: ldlm_cancel_lock_for_export (ldlm_lock.c:2566-2585) ->
\*         ldlm_lock_cancel (2496-2538) + ldlm_reprocess_all (2430)
\* ================================================================
fair process CancelThread = "cancel_thread"
begin
CT_Lock:
    await lr_lock = "free";
    lr_lock := "cancel_thread";

CT_Cancel:
    holder_active := FALSE;
    lr_lock := "free";
    \* Now call ldlm_reprocess_all -- signal RP_A to start
    rpa_phase := "ready";
end process;

\* ================================================================
\* ReprocessA: First reprocessor, triggered by cancel.
\* Models: ldlm_reprocess_queue (ldlm_lock.c:1958-2020) called from
\*         __ldlm_reprocess_all (2383-2428) after ldlm_lock_cancel
\* ================================================================
fair process ReprocessA = "reprocess_a"
begin
RPA_WaitReady:
    await rpa_phase = "ready";

RPA_Lock:
    await lr_lock = "free";
    lr_lock := "reprocess_a";
    rpa_phase := "scanning";
    rpa_cursor := 1;
    rpa_needs_blast := FALSE;
    rpa_erestart := FALSE;

RPA_Scan:
    if rpa_cursor <= NumWaiters then
        if lock_state[rpa_cursor] = "waiting" then
            TryGrant(rpa_cursor);
            if lock_state[rpa_cursor] = "waiting" then
                \* Conflict remains (e.g., another granted EX blocks)
                \* Need BL_ASTs
                rpa_needs_blast := TRUE;
                goto RPA_AfterScan;
            end if;
        end if;
RPA_Advance:
        rpa_cursor := rpa_cursor + 1;
        goto RPA_Scan;
    end if;

RPA_AfterScan:
    if rpa_needs_blast then
        \* Drop lr_lock, send BL_ASTs
        lr_lock := "free";
        rpa_phase := "bl_sending";
    else
        \* Nothing to send, done
        lr_lock := "free";
        rpa_phase := "done";
        goto RPA_Done;
    end if;

RPA_WaitASTs:
    \* BL_AST completion window - other threads can run
    skip;

RPA_Relock:
    await lr_lock = "free";
    lr_lock := "reprocess_a";

RPA_CheckRestart:
    if rpa_erestart /\ ~InjectBugSkipRescan then
        rpa_phase := "scanning";
        rpa_cursor := 1;
        rpa_needs_blast := FALSE;
        rpa_erestart := FALSE;
        goto RPA_Scan;
    end if;

RPA_Finish:
    rpa_phase := "done";
    lr_lock := "free";

RPA_Done:
    skip;
end process;

\* ================================================================
\* ReprocessB: Second concurrent reprocessor.
\* Models: ldlm_reprocess_all called from a different thread
\* (e.g., ldlm_handle_convert0 at ldlm_lockd.c:1695,
\* ldlm_request_cancel at 1774/1805, or second export disconnect)
\*
\* This reprocessor can run at any time after the cancel,
\* potentially overlapping with RP_A's BL_AST window.
\* ================================================================
fair process ReprocessB = "reprocess_b"
begin
RPB_WaitReady:
    \* RP_B starts after cancel completes (both reprocessors
    \* are triggered by events after the holder is gone)
    await ~holder_active;

RPB_Lock:
    await lr_lock = "free";
    lr_lock := "reprocess_b";
    rpb_phase := "scanning";
    rpb_cursor := 1;
    rpb_needs_blast := FALSE;
    rpb_erestart := FALSE;

RPB_Scan:
    if rpb_cursor <= NumWaiters then
        if lock_state[rpb_cursor] = "waiting" then
            TryGrant(rpb_cursor);
            if lock_state[rpb_cursor] = "waiting" then
                rpb_needs_blast := TRUE;
                goto RPB_AfterScan;
            end if;
        end if;
RPB_Advance:
        rpb_cursor := rpb_cursor + 1;
        goto RPB_Scan;
    end if;

RPB_AfterScan:
    if rpb_needs_blast then
        lr_lock := "free";
        rpb_phase := "bl_sending";
    else
        lr_lock := "free";
        rpb_phase := "done";
        goto RPB_Done;
    end if;

RPB_WaitASTs:
    skip;

RPB_Relock:
    await lr_lock = "free";
    lr_lock := "reprocess_b";

RPB_CheckRestart:
    if rpb_erestart then
        rpb_phase := "scanning";
        rpb_cursor := 1;
        rpb_needs_blast := FALSE;
        rpb_erestart := FALSE;
        goto RPB_Scan;
    end if;

RPB_Finish:
    rpb_phase := "done";
    lr_lock := "free";

RPB_Done:
    skip;
end process;

\* ================================================================
\* FailedLock: A granted lock's export disconnects, the lock is
\* destroyed.  The fix (LU-14522) calls ldlm_reprocess_all after
\* destroying the lock, allowing remaining waiters to be granted.
\*
\* Scenario: RP_A grants lock W1.  W2 still waits (EX vs EX
\* conflict with W1).  W1's export disconnects ->
\* ldlm_handle_enqueue destroys W1.  Without reprocess, W2
\* stays waiting forever.
\*
\* In the dual-reprocess context, this process can run during
\* either reprocessor's BL_AST window or after both finish.
\* When it runs during a BL_AST window, it sets the active
\* reprocessor's erestart flag (simulating the ERESTART that
\* would result from the lock destruction notification).
\*
\* Models: ldlm_handle_enqueue error path (ldlm_lockd.c:1569-1581;
\* ldlm_lock_cancel at 1572, ldlm_reprocess_all at 1579).
\* ================================================================
fair process FailedLock = "failed_lock"
begin
FL_Wait:
    \* Wait for a granted lock to exist
    await \E i \in Waiters : IsGranted(i);

FL_Lock:
    await lr_lock = "free";
    lr_lock := "failed_lock";

FL_Destroy:
    \* Export disconnects during enqueue: destroy a granted lock.
    \* ldlm_resource_unlink_lock + ldlm_lock_destroy_nolock
    with i \in {j \in Waiters : IsGranted(j)} do
        lock_state[i] := "none";
    end with;
    \* Signal active reprocessors to rescan (ERESTART)
    if rpa_phase = "bl_sending" then
        rpa_erestart := TRUE;
    end if;
    if rpb_phase = "bl_sending" then
        rpb_erestart := TRUE;
    end if;

FL_CheckReprocess:
    if InjectBugNoReprocessOnFail then
        \* BUG (LU-14522): skip ldlm_reprocess_all entirely.
        \* Waiting locks that conflicted only with the destroyed
        \* lock will never be granted.
        lr_lock := "free";
        goto FL_Done;
    end if;
FL_InitScan:
    fl_cursor := 1;

FL_Scan:
    if fl_cursor <= NumWaiters then
        if lock_state[fl_cursor] = "waiting" then
            TryGrant(fl_cursor);
        end if;
FL_ScanNext:
        fl_cursor := fl_cursor + 1;
        goto FL_Scan;
    end if;
FL_Unlock:
    lr_lock := "free";

FL_Done:
    skip;
end process;

end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "2910f6d3" /\ chksum(tla) = "f3ccf934")
VARIABLES lr_lock, holder_active, lock_state, grant_count, rpa_phase,
          rpa_cursor, rpa_needs_blast, rpa_erestart, rpb_phase, rpb_cursor,
          rpb_needs_blast, rpb_erestart, fl_cursor, pc

(* define statement *)
IsGranted(i) == lock_state[i] = "granted"
GrantedCount == Cardinality({i \in Waiters : IsGranted(i)})
WaitingCount == Cardinality({i \in Waiters : lock_state[i] = "waiting"})


NoDoubleGrant == \A i \in Waiters : grant_count[i] <= 1


GrantedCompatible ==
    (~holder_active /\ ~CompatibleMode) => GrantedCount <= 1


NoGrantWhileHeld ==
    holder_active => GrantedCount = 0


NoStuckWaiter ==
    (pc["cancel_thread"] = "Done"
     /\ pc["reprocess_a"] = "Done"
     /\ pc["reprocess_b"] = "Done"
     /\ pc["failed_lock"] = "Done") =>
        ~(\E i \in Waiters :
            lock_state[i] = "waiting"
            /\ ~holder_active
            /\ (CompatibleMode
                \/ ~(\E j \in Waiters : j /= i /\ IsGranted(j))))



NoMissedGrant ==
    (pc["cancel_thread"] = "Done"
     /\ pc["reprocess_a"] = "Done"
     /\ pc["reprocess_b"] = "Done"
     /\ pc["failed_lock"] = "Done"
     /\ ~holder_active) =>
        IF CompatibleMode
        THEN WaitingCount = 0
        ELSE (WaitingCount = 0 \/ GrantedCount > 0)

TypeOK ==
    /\ \A i \in Waiters : lock_state[i] \in {"waiting", "granted", "none"}
    /\ \A i \in Waiters : grant_count[i] \in 0..3
    /\ rpa_cursor \in 1..(NumWaiters+1)
    /\ rpb_cursor \in 1..(NumWaiters+1)
    /\ fl_cursor \in 1..(NumWaiters+1)


vars == << lr_lock, holder_active, lock_state, grant_count, rpa_phase,
           rpa_cursor, rpa_needs_blast, rpa_erestart, rpb_phase, rpb_cursor,
           rpb_needs_blast, rpb_erestart, fl_cursor, pc >>

ProcSet == {"cancel_thread"} \cup {"reprocess_a"} \cup {"reprocess_b"} \cup {"failed_lock"}

Init == (* Global variables *)
        /\ lr_lock = "free"
        /\ holder_active = TRUE
        /\ lock_state = [i \in Waiters |-> "waiting"]
        /\ grant_count = [i \in Waiters |-> 0]
        /\ rpa_phase = "idle"
        /\ rpa_cursor = 1
        /\ rpa_needs_blast = FALSE
        /\ rpa_erestart = FALSE
        /\ rpb_phase = "idle"
        /\ rpb_cursor = 1
        /\ rpb_needs_blast = FALSE
        /\ rpb_erestart = FALSE
        /\ fl_cursor = 1
        /\ pc = [self \in ProcSet |-> CASE self = "cancel_thread" -> "CT_Lock"
                                        [] self = "reprocess_a" -> "RPA_WaitReady"
                                        [] self = "reprocess_b" -> "RPB_WaitReady"
                                        [] self = "failed_lock" -> "FL_Wait"]

CT_Lock == /\ pc["cancel_thread"] = "CT_Lock"
           /\ lr_lock = "free"
           /\ lr_lock' = "cancel_thread"
           /\ pc' = [pc EXCEPT !["cancel_thread"] = "CT_Cancel"]
           /\ UNCHANGED << holder_active, lock_state, grant_count, rpa_phase,
                           rpa_cursor, rpa_needs_blast, rpa_erestart,
                           rpb_phase, rpb_cursor, rpb_needs_blast,
                           rpb_erestart, fl_cursor >>

CT_Cancel == /\ pc["cancel_thread"] = "CT_Cancel"
             /\ holder_active' = FALSE
             /\ lr_lock' = "free"
             /\ rpa_phase' = "ready"
             /\ pc' = [pc EXCEPT !["cancel_thread"] = "Done"]
             /\ UNCHANGED << lock_state, grant_count, rpa_cursor,
                             rpa_needs_blast, rpa_erestart, rpb_phase,
                             rpb_cursor, rpb_needs_blast, rpb_erestart,
                             fl_cursor >>

CancelThread == CT_Lock \/ CT_Cancel

RPA_WaitReady == /\ pc["reprocess_a"] = "RPA_WaitReady"
                 /\ rpa_phase = "ready"
                 /\ pc' = [pc EXCEPT !["reprocess_a"] = "RPA_Lock"]
                 /\ UNCHANGED << lr_lock, holder_active, lock_state,
                                 grant_count, rpa_phase, rpa_cursor,
                                 rpa_needs_blast, rpa_erestart, rpb_phase,
                                 rpb_cursor, rpb_needs_blast, rpb_erestart,
                                 fl_cursor >>

RPA_Lock == /\ pc["reprocess_a"] = "RPA_Lock"
            /\ lr_lock = "free"
            /\ lr_lock' = "reprocess_a"
            /\ rpa_phase' = "scanning"
            /\ rpa_cursor' = 1
            /\ rpa_needs_blast' = FALSE
            /\ rpa_erestart' = FALSE
            /\ pc' = [pc EXCEPT !["reprocess_a"] = "RPA_Scan"]
            /\ UNCHANGED << holder_active, lock_state, grant_count, rpb_phase,
                            rpb_cursor, rpb_needs_blast, rpb_erestart,
                            fl_cursor >>

RPA_Scan == /\ pc["reprocess_a"] = "RPA_Scan"
            /\ IF rpa_cursor <= NumWaiters
                  THEN /\ IF lock_state[rpa_cursor] = "waiting"
                             THEN /\ IF ~holder_active
                                        /\ (CompatibleMode \/ ~(\E j \in Waiters : j /= rpa_cursor /\ IsGranted(j)))
                                        /\ lock_state[rpa_cursor] = "waiting"
                                        THEN /\ lock_state' = [lock_state EXCEPT ![rpa_cursor] = "granted"]
                                             /\ grant_count' = [grant_count EXCEPT ![rpa_cursor] = grant_count[rpa_cursor] + 1]
                                        ELSE /\ TRUE
                                             /\ UNCHANGED << lock_state,
                                                             grant_count >>
                                  /\ IF lock_state'[rpa_cursor] = "waiting"
                                        THEN /\ rpa_needs_blast' = TRUE
                                             /\ pc' = [pc EXCEPT !["reprocess_a"] = "RPA_AfterScan"]
                                        ELSE /\ pc' = [pc EXCEPT !["reprocess_a"] = "RPA_Advance"]
                                             /\ UNCHANGED rpa_needs_blast
                             ELSE /\ pc' = [pc EXCEPT !["reprocess_a"] = "RPA_Advance"]
                                  /\ UNCHANGED << lock_state, grant_count,
                                                  rpa_needs_blast >>
                  ELSE /\ pc' = [pc EXCEPT !["reprocess_a"] = "RPA_AfterScan"]
                       /\ UNCHANGED << lock_state, grant_count,
                                       rpa_needs_blast >>
            /\ UNCHANGED << lr_lock, holder_active, rpa_phase, rpa_cursor,
                            rpa_erestart, rpb_phase, rpb_cursor,
                            rpb_needs_blast, rpb_erestart, fl_cursor >>

RPA_Advance == /\ pc["reprocess_a"] = "RPA_Advance"
               /\ rpa_cursor' = rpa_cursor + 1
               /\ pc' = [pc EXCEPT !["reprocess_a"] = "RPA_Scan"]
               /\ UNCHANGED << lr_lock, holder_active, lock_state, grant_count,
                               rpa_phase, rpa_needs_blast, rpa_erestart,
                               rpb_phase, rpb_cursor, rpb_needs_blast,
                               rpb_erestart, fl_cursor >>

RPA_AfterScan == /\ pc["reprocess_a"] = "RPA_AfterScan"
                 /\ IF rpa_needs_blast
                       THEN /\ lr_lock' = "free"
                            /\ rpa_phase' = "bl_sending"
                            /\ pc' = [pc EXCEPT !["reprocess_a"] = "RPA_WaitASTs"]
                       ELSE /\ lr_lock' = "free"
                            /\ rpa_phase' = "done"
                            /\ pc' = [pc EXCEPT !["reprocess_a"] = "RPA_Done"]
                 /\ UNCHANGED << holder_active, lock_state, grant_count,
                                 rpa_cursor, rpa_needs_blast, rpa_erestart,
                                 rpb_phase, rpb_cursor, rpb_needs_blast,
                                 rpb_erestart, fl_cursor >>

RPA_WaitASTs == /\ pc["reprocess_a"] = "RPA_WaitASTs"
                /\ TRUE
                /\ pc' = [pc EXCEPT !["reprocess_a"] = "RPA_Relock"]
                /\ UNCHANGED << lr_lock, holder_active, lock_state,
                                grant_count, rpa_phase, rpa_cursor,
                                rpa_needs_blast, rpa_erestart, rpb_phase,
                                rpb_cursor, rpb_needs_blast, rpb_erestart,
                                fl_cursor >>

RPA_Relock == /\ pc["reprocess_a"] = "RPA_Relock"
              /\ lr_lock = "free"
              /\ lr_lock' = "reprocess_a"
              /\ pc' = [pc EXCEPT !["reprocess_a"] = "RPA_CheckRestart"]
              /\ UNCHANGED << holder_active, lock_state, grant_count,
                              rpa_phase, rpa_cursor, rpa_needs_blast,
                              rpa_erestart, rpb_phase, rpb_cursor,
                              rpb_needs_blast, rpb_erestart, fl_cursor >>

RPA_CheckRestart == /\ pc["reprocess_a"] = "RPA_CheckRestart"
                    /\ IF rpa_erestart /\ ~InjectBugSkipRescan
                          THEN /\ rpa_phase' = "scanning"
                               /\ rpa_cursor' = 1
                               /\ rpa_needs_blast' = FALSE
                               /\ rpa_erestart' = FALSE
                               /\ pc' = [pc EXCEPT !["reprocess_a"] = "RPA_Scan"]
                          ELSE /\ pc' = [pc EXCEPT !["reprocess_a"] = "RPA_Finish"]
                               /\ UNCHANGED << rpa_phase, rpa_cursor,
                                               rpa_needs_blast, rpa_erestart >>
                    /\ UNCHANGED << lr_lock, holder_active, lock_state,
                                    grant_count, rpb_phase, rpb_cursor,
                                    rpb_needs_blast, rpb_erestart, fl_cursor >>

RPA_Finish == /\ pc["reprocess_a"] = "RPA_Finish"
              /\ rpa_phase' = "done"
              /\ lr_lock' = "free"
              /\ pc' = [pc EXCEPT !["reprocess_a"] = "RPA_Done"]
              /\ UNCHANGED << holder_active, lock_state, grant_count,
                              rpa_cursor, rpa_needs_blast, rpa_erestart,
                              rpb_phase, rpb_cursor, rpb_needs_blast,
                              rpb_erestart, fl_cursor >>

RPA_Done == /\ pc["reprocess_a"] = "RPA_Done"
            /\ TRUE
            /\ pc' = [pc EXCEPT !["reprocess_a"] = "Done"]
            /\ UNCHANGED << lr_lock, holder_active, lock_state, grant_count,
                            rpa_phase, rpa_cursor, rpa_needs_blast,
                            rpa_erestart, rpb_phase, rpb_cursor,
                            rpb_needs_blast, rpb_erestart, fl_cursor >>

ReprocessA == RPA_WaitReady \/ RPA_Lock \/ RPA_Scan \/ RPA_Advance
                 \/ RPA_AfterScan \/ RPA_WaitASTs \/ RPA_Relock
                 \/ RPA_CheckRestart \/ RPA_Finish \/ RPA_Done

RPB_WaitReady == /\ pc["reprocess_b"] = "RPB_WaitReady"
                 /\ ~holder_active
                 /\ pc' = [pc EXCEPT !["reprocess_b"] = "RPB_Lock"]
                 /\ UNCHANGED << lr_lock, holder_active, lock_state,
                                 grant_count, rpa_phase, rpa_cursor,
                                 rpa_needs_blast, rpa_erestart, rpb_phase,
                                 rpb_cursor, rpb_needs_blast, rpb_erestart,
                                 fl_cursor >>

RPB_Lock == /\ pc["reprocess_b"] = "RPB_Lock"
            /\ lr_lock = "free"
            /\ lr_lock' = "reprocess_b"
            /\ rpb_phase' = "scanning"
            /\ rpb_cursor' = 1
            /\ rpb_needs_blast' = FALSE
            /\ rpb_erestart' = FALSE
            /\ pc' = [pc EXCEPT !["reprocess_b"] = "RPB_Scan"]
            /\ UNCHANGED << holder_active, lock_state, grant_count, rpa_phase,
                            rpa_cursor, rpa_needs_blast, rpa_erestart,
                            fl_cursor >>

RPB_Scan == /\ pc["reprocess_b"] = "RPB_Scan"
            /\ IF rpb_cursor <= NumWaiters
                  THEN /\ IF lock_state[rpb_cursor] = "waiting"
                             THEN /\ IF ~holder_active
                                        /\ (CompatibleMode \/ ~(\E j \in Waiters : j /= rpb_cursor /\ IsGranted(j)))
                                        /\ lock_state[rpb_cursor] = "waiting"
                                        THEN /\ lock_state' = [lock_state EXCEPT ![rpb_cursor] = "granted"]
                                             /\ grant_count' = [grant_count EXCEPT ![rpb_cursor] = grant_count[rpb_cursor] + 1]
                                        ELSE /\ TRUE
                                             /\ UNCHANGED << lock_state,
                                                             grant_count >>
                                  /\ IF lock_state'[rpb_cursor] = "waiting"
                                        THEN /\ rpb_needs_blast' = TRUE
                                             /\ pc' = [pc EXCEPT !["reprocess_b"] = "RPB_AfterScan"]
                                        ELSE /\ pc' = [pc EXCEPT !["reprocess_b"] = "RPB_Advance"]
                                             /\ UNCHANGED rpb_needs_blast
                             ELSE /\ pc' = [pc EXCEPT !["reprocess_b"] = "RPB_Advance"]
                                  /\ UNCHANGED << lock_state, grant_count,
                                                  rpb_needs_blast >>
                  ELSE /\ pc' = [pc EXCEPT !["reprocess_b"] = "RPB_AfterScan"]
                       /\ UNCHANGED << lock_state, grant_count,
                                       rpb_needs_blast >>
            /\ UNCHANGED << lr_lock, holder_active, rpa_phase, rpa_cursor,
                            rpa_needs_blast, rpa_erestart, rpb_phase,
                            rpb_cursor, rpb_erestart, fl_cursor >>

RPB_Advance == /\ pc["reprocess_b"] = "RPB_Advance"
               /\ rpb_cursor' = rpb_cursor + 1
               /\ pc' = [pc EXCEPT !["reprocess_b"] = "RPB_Scan"]
               /\ UNCHANGED << lr_lock, holder_active, lock_state, grant_count,
                               rpa_phase, rpa_cursor, rpa_needs_blast,
                               rpa_erestart, rpb_phase, rpb_needs_blast,
                               rpb_erestart, fl_cursor >>

RPB_AfterScan == /\ pc["reprocess_b"] = "RPB_AfterScan"
                 /\ IF rpb_needs_blast
                       THEN /\ lr_lock' = "free"
                            /\ rpb_phase' = "bl_sending"
                            /\ pc' = [pc EXCEPT !["reprocess_b"] = "RPB_WaitASTs"]
                       ELSE /\ lr_lock' = "free"
                            /\ rpb_phase' = "done"
                            /\ pc' = [pc EXCEPT !["reprocess_b"] = "RPB_Done"]
                 /\ UNCHANGED << holder_active, lock_state, grant_count,
                                 rpa_phase, rpa_cursor, rpa_needs_blast,
                                 rpa_erestart, rpb_cursor, rpb_needs_blast,
                                 rpb_erestart, fl_cursor >>

RPB_WaitASTs == /\ pc["reprocess_b"] = "RPB_WaitASTs"
                /\ TRUE
                /\ pc' = [pc EXCEPT !["reprocess_b"] = "RPB_Relock"]
                /\ UNCHANGED << lr_lock, holder_active, lock_state,
                                grant_count, rpa_phase, rpa_cursor,
                                rpa_needs_blast, rpa_erestart, rpb_phase,
                                rpb_cursor, rpb_needs_blast, rpb_erestart,
                                fl_cursor >>

RPB_Relock == /\ pc["reprocess_b"] = "RPB_Relock"
              /\ lr_lock = "free"
              /\ lr_lock' = "reprocess_b"
              /\ pc' = [pc EXCEPT !["reprocess_b"] = "RPB_CheckRestart"]
              /\ UNCHANGED << holder_active, lock_state, grant_count,
                              rpa_phase, rpa_cursor, rpa_needs_blast,
                              rpa_erestart, rpb_phase, rpb_cursor,
                              rpb_needs_blast, rpb_erestart, fl_cursor >>

RPB_CheckRestart == /\ pc["reprocess_b"] = "RPB_CheckRestart"
                    /\ IF rpb_erestart
                          THEN /\ rpb_phase' = "scanning"
                               /\ rpb_cursor' = 1
                               /\ rpb_needs_blast' = FALSE
                               /\ rpb_erestart' = FALSE
                               /\ pc' = [pc EXCEPT !["reprocess_b"] = "RPB_Scan"]
                          ELSE /\ pc' = [pc EXCEPT !["reprocess_b"] = "RPB_Finish"]
                               /\ UNCHANGED << rpb_phase, rpb_cursor,
                                               rpb_needs_blast, rpb_erestart >>
                    /\ UNCHANGED << lr_lock, holder_active, lock_state,
                                    grant_count, rpa_phase, rpa_cursor,
                                    rpa_needs_blast, rpa_erestart, fl_cursor >>

RPB_Finish == /\ pc["reprocess_b"] = "RPB_Finish"
              /\ rpb_phase' = "done"
              /\ lr_lock' = "free"
              /\ pc' = [pc EXCEPT !["reprocess_b"] = "RPB_Done"]
              /\ UNCHANGED << holder_active, lock_state, grant_count,
                              rpa_phase, rpa_cursor, rpa_needs_blast,
                              rpa_erestart, rpb_cursor, rpb_needs_blast,
                              rpb_erestart, fl_cursor >>

RPB_Done == /\ pc["reprocess_b"] = "RPB_Done"
            /\ TRUE
            /\ pc' = [pc EXCEPT !["reprocess_b"] = "Done"]
            /\ UNCHANGED << lr_lock, holder_active, lock_state, grant_count,
                            rpa_phase, rpa_cursor, rpa_needs_blast,
                            rpa_erestart, rpb_phase, rpb_cursor,
                            rpb_needs_blast, rpb_erestart, fl_cursor >>

ReprocessB == RPB_WaitReady \/ RPB_Lock \/ RPB_Scan \/ RPB_Advance
                 \/ RPB_AfterScan \/ RPB_WaitASTs \/ RPB_Relock
                 \/ RPB_CheckRestart \/ RPB_Finish \/ RPB_Done

FL_Wait == /\ pc["failed_lock"] = "FL_Wait"
           /\ \E i \in Waiters : IsGranted(i)
           /\ pc' = [pc EXCEPT !["failed_lock"] = "FL_Lock"]
           /\ UNCHANGED << lr_lock, holder_active, lock_state, grant_count,
                           rpa_phase, rpa_cursor, rpa_needs_blast,
                           rpa_erestart, rpb_phase, rpb_cursor,
                           rpb_needs_blast, rpb_erestart, fl_cursor >>

FL_Lock == /\ pc["failed_lock"] = "FL_Lock"
           /\ lr_lock = "free"
           /\ lr_lock' = "failed_lock"
           /\ pc' = [pc EXCEPT !["failed_lock"] = "FL_Destroy"]
           /\ UNCHANGED << holder_active, lock_state, grant_count, rpa_phase,
                           rpa_cursor, rpa_needs_blast, rpa_erestart,
                           rpb_phase, rpb_cursor, rpb_needs_blast,
                           rpb_erestart, fl_cursor >>

FL_Destroy == /\ pc["failed_lock"] = "FL_Destroy"
              /\ \E i \in {j \in Waiters : IsGranted(j)}:
                   lock_state' = [lock_state EXCEPT ![i] = "none"]
              /\ IF rpa_phase = "bl_sending"
                    THEN /\ rpa_erestart' = TRUE
                    ELSE /\ TRUE
                         /\ UNCHANGED rpa_erestart
              /\ IF rpb_phase = "bl_sending"
                    THEN /\ rpb_erestart' = TRUE
                    ELSE /\ TRUE
                         /\ UNCHANGED rpb_erestart
              /\ pc' = [pc EXCEPT !["failed_lock"] = "FL_CheckReprocess"]
              /\ UNCHANGED << lr_lock, holder_active, grant_count, rpa_phase,
                              rpa_cursor, rpa_needs_blast, rpb_phase,
                              rpb_cursor, rpb_needs_blast, fl_cursor >>

FL_CheckReprocess == /\ pc["failed_lock"] = "FL_CheckReprocess"
                     /\ IF InjectBugNoReprocessOnFail
                           THEN /\ lr_lock' = "free"
                                /\ pc' = [pc EXCEPT !["failed_lock"] = "FL_Done"]
                           ELSE /\ pc' = [pc EXCEPT !["failed_lock"] = "FL_InitScan"]
                                /\ UNCHANGED lr_lock
                     /\ UNCHANGED << holder_active, lock_state, grant_count,
                                     rpa_phase, rpa_cursor, rpa_needs_blast,
                                     rpa_erestart, rpb_phase, rpb_cursor,
                                     rpb_needs_blast, rpb_erestart, fl_cursor >>

FL_InitScan == /\ pc["failed_lock"] = "FL_InitScan"
               /\ fl_cursor' = 1
               /\ pc' = [pc EXCEPT !["failed_lock"] = "FL_Scan"]
               /\ UNCHANGED << lr_lock, holder_active, lock_state, grant_count,
                               rpa_phase, rpa_cursor, rpa_needs_blast,
                               rpa_erestart, rpb_phase, rpb_cursor,
                               rpb_needs_blast, rpb_erestart >>

FL_Scan == /\ pc["failed_lock"] = "FL_Scan"
           /\ IF fl_cursor <= NumWaiters
                 THEN /\ IF lock_state[fl_cursor] = "waiting"
                            THEN /\ IF ~holder_active
                                       /\ (CompatibleMode \/ ~(\E j \in Waiters : j /= fl_cursor /\ IsGranted(j)))
                                       /\ lock_state[fl_cursor] = "waiting"
                                       THEN /\ lock_state' = [lock_state EXCEPT ![fl_cursor] = "granted"]
                                            /\ grant_count' = [grant_count EXCEPT ![fl_cursor] = grant_count[fl_cursor] + 1]
                                       ELSE /\ TRUE
                                            /\ UNCHANGED << lock_state,
                                                            grant_count >>
                            ELSE /\ TRUE
                                 /\ UNCHANGED << lock_state, grant_count >>
                      /\ pc' = [pc EXCEPT !["failed_lock"] = "FL_ScanNext"]
                 ELSE /\ pc' = [pc EXCEPT !["failed_lock"] = "FL_Unlock"]
                      /\ UNCHANGED << lock_state, grant_count >>
           /\ UNCHANGED << lr_lock, holder_active, rpa_phase, rpa_cursor,
                           rpa_needs_blast, rpa_erestart, rpb_phase,
                           rpb_cursor, rpb_needs_blast, rpb_erestart,
                           fl_cursor >>

FL_ScanNext == /\ pc["failed_lock"] = "FL_ScanNext"
               /\ fl_cursor' = fl_cursor + 1
               /\ pc' = [pc EXCEPT !["failed_lock"] = "FL_Scan"]
               /\ UNCHANGED << lr_lock, holder_active, lock_state, grant_count,
                               rpa_phase, rpa_cursor, rpa_needs_blast,
                               rpa_erestart, rpb_phase, rpb_cursor,
                               rpb_needs_blast, rpb_erestart >>

FL_Unlock == /\ pc["failed_lock"] = "FL_Unlock"
             /\ lr_lock' = "free"
             /\ pc' = [pc EXCEPT !["failed_lock"] = "FL_Done"]
             /\ UNCHANGED << holder_active, lock_state, grant_count, rpa_phase,
                             rpa_cursor, rpa_needs_blast, rpa_erestart,
                             rpb_phase, rpb_cursor, rpb_needs_blast,
                             rpb_erestart, fl_cursor >>

FL_Done == /\ pc["failed_lock"] = "FL_Done"
           /\ TRUE
           /\ pc' = [pc EXCEPT !["failed_lock"] = "Done"]
           /\ UNCHANGED << lr_lock, holder_active, lock_state, grant_count,
                           rpa_phase, rpa_cursor, rpa_needs_blast,
                           rpa_erestart, rpb_phase, rpb_cursor,
                           rpb_needs_blast, rpb_erestart, fl_cursor >>

FailedLock == FL_Wait \/ FL_Lock \/ FL_Destroy \/ FL_CheckReprocess
                 \/ FL_InitScan \/ FL_Scan \/ FL_ScanNext \/ FL_Unlock
                 \/ FL_Done

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == CancelThread \/ ReprocessA \/ ReprocessB \/ FailedLock
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(CancelThread)
        /\ WF_vars(ReprocessA)
        /\ WF_vars(ReprocessB)
        /\ WF_vars(FailedLock)

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

\* Liveness: both reprocessors eventually complete
EventualCompletion ==
    <>(rpa_phase = "done" /\ rpb_phase = "done")

=============================================================================
