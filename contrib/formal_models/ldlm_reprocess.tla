---------------------------- MODULE ldlm_reprocess ----------------------------
(*
 * PlusCal/TLA+ model of LDLM waiting queue reprocessing with
 * multiple waiting locks.
 *
 * Models the server-side reprocessing loop from
 * ldlm_reprocess_queue (ldlm_lock.c:1958-2020) with N waiting
 * locks contending on the same resource.  The key race: the
 * reprocess loop drops lr_lock to send BL_ASTs via
 * ldlm_run_ast_work, then restarts the queue scan on ERESTART.
 * With multiple waiters, interleaving between granting one lock
 * and sending BL_ASTs for another creates windows not present
 * in the single-lock model.
 *
 * Lifecycle modeled:
 *   1. Resource R has holder H (EX mode)
 *   2. Locks L1, L2 enqueue for EX, both conflict with H
 *   3. BL_AST sent to H
 *   4. ldlm_reprocess_queue runs: iterates waiting list,
 *      tries to grant each lock via policy callback
 *   5. If conflicts remain, sends BL_ASTs (drops lr_lock)
 *   6. On ERESTART, rescans from beginning
 *   7. During the BL_AST window, holder cancel and/or
 *      concurrent lock cancellation can race
 *
 * Key protocol details:
 *   - ldlm_process_plain_lock RESCAN: checks granted + waiting
 *     queues for conflicts.  If none, calls ldlm_grant_lock.
 *   - Waiting queue is ordered: L1 before L2 in FIFO
 *   - L2 (EX) conflicts with L1 if L1 is granted before L2
 *   - The reprocess loop holds lr_lock during the iteration
 *     but drops it for BL_AST sending
 *
 * Safety invariants:
 *   NoDoubleGrant:     Each lock granted at most once
 *   GrantedCompatible: All granted locks are mode-compatible
 *   NoGrantWhileHeld:  No grants while holder active
 *   PoolCorrect:       Pool count matches granted count
 *   WaitingIntegrity:  Waiting locks have zero grant calls
 *
 * Source (lustre-release master 47638add78):
 *   ldlm_reprocess_queue        ldlm_lock.c:1958-2020
 *     list_for_each_safe scan 1980-2003 (RESCAN breaks on
 *     LDLM_ITER_STOP at 2000-2002; BL_ASTs collected at 1994),
 *     unlock_res 2006, ldlm_run_ast_work 2008, lock_res 2011,
 *     GOTO restart on -ERESTART 2013
 *   __ldlm_reprocess_all        ldlm_lock.c:2383-2428 (CP_AST send
 *     with lr_lock dropped at 2412, goto restart 2419)
 *   ldlm_reprocess_inodebits_queue ldlm_inodebits.c:47-124 (IBITS
 *     RESCAN variant: BL_AST send 108-113, GOTO restart 114-117)
 *   ldlm_process_plain_lock     ldlm_plain.c:110-147 (RESCAN 124-136)
 *   ldlm_grant_lock             ldlm_lock.c:1121-1158 (pool_add 1156)
 *   ldlm_run_ast_work           ldlm_lock.c:2315-2373 (-ERESTART 2368)
 *   ldlm_cb_interpret           ldlm_lockd.c:758-814
 *   ldlm_handle_ast_error       ldlm_lockd.c:686-756
 *   ldlm_lock_cancel            ldlm_lock.c:2496-2538 (pool_del 2531)
 *   ldlm_handle_enqueue         ldlm_lockd.c:1248-1595 (failed-enqueue
 *     cancel/destroy + ldlm_reprocess_all at 1569-1581, LU-14522)
 *   ldlm_handle_conflict_lock   ldlm_lock.c:2036-2094 (ldlm_reprocess_all
 *     on -ERESTART at 2064-2065, LU-13692)
 *
 * Validated against: lustre-release master 47638add78 (2026-09-06)
 *
 * Validation notes: all modeled functions exist under these names
 * (ldlm_handle_enqueue0 is now ldlm_handle_enqueue) and the ERESTART
 * full rescan (rp_cursor := 1) matches GOTO restart at
 * ldlm_lock.c:2013 and ldlm_inodebits.c:116.  In this tree the
 * bl_ast_list inside ldlm_reprocess_queue is only populated for the
 * RECOVERY intention: plain and extent RESCAN pass NULL work lists
 * (ldlm_plain.c:126/129, ldlm_extent.c:883-886), so the
 * RESCAN-with-BL_AST-window shape modeled here is realized by
 * ldlm_reprocess_inodebits_queue for IBITS resources and by the
 * CP_AST window of __ldlm_reprocess_all for the other types.  The
 * LU-13692 injection (InjectBugLocalRestart) abstracts the pre-fix
 * GOTO(restart) in ldlm_lock_enqueue_helper, which re-ran the policy
 * for the enqueuing lock only; the fix is the ldlm_reprocess_all
 * call in ldlm_handle_conflict_lock (2064-2065).  FailedLock holds
 * lr_lock across destroy + rescan, whereas ldlm_handle_enqueue
 * drops it between ldlm_lock_cancel (1572) and ldlm_reprocess_all
 * (1579); the model was written with the stricter atomicity (not
 * drift).
 *)

EXTENDS Integers, FiniteSets, Sequences, TLC

CONSTANTS
    NumLocks,             \* Number of waiting locks (2 or 3)
    CompatibleMode,       \* TRUE = waiting locks use PR (compatible with
                          \* each other, conflict only with holder's EX)
    InjectBugNoRestart,   \* TRUE = skip ERESTART handling entirely
    InjectBugLocalRestart,\* TRUE = LU-13692: on ERESTART, only recheck
                          \* the lock that triggered the BL_AST, not the
                          \* whole queue.  Pre-fix: enqueue_helper did
                          \* GOTO(restart) which re-ran policy for current
                          \* lock only, missing other eligible waiters.
    InjectBugNoReprocessOnFail
                          \* TRUE = LU-14522: when export disconnects
                          \* during enqueue, ldlm_handle_enqueue drops
                          \* the lock but skips ldlm_reprocess_all.
                          \* Waiting locks conflicting only with the
                          \* destroyed lock get stuck permanently.

ASSUME NumLocks \in 2..4

Locks == 1..NumLocks

(* --algorithm ldlm_reprocess

variables
    \* ---- Resource spinlock (lr_lock) ----
    lr_lock = "free",

    \* ---- Holder H state ----
    holder_active = TRUE,

    \* ---- Lock states (per waiting lock) ----
    lock_list = [i \in Locks |-> "waiting"],

    \* ---- Grant tracking ----
    lock_granted = [i \in Locks |-> FALSE],
    grant_calls = [i \in Locks |-> 0],

    \* ---- Pool accounting ----
    pool_count = 0,

    \* ---- Reprocess state machine ----
    rp_phase = "idle",
    rp_cursor = 1,
    bl_ast_list = {},
    granted_this_pass = {},
    erestart = FALSE,

    \* Track whether ERESTART was handled during this reprocess
    did_restart = FALSE,

    \* Cursor for FailedLock reprocess scan
    fl_cursor = 1;

define
    IsGranted(i) == lock_list[i] = "granted"
    GrantedCount == Cardinality({i \in Locks : IsGranted(i)})

    \* ========== SAFETY INVARIANTS ==========

    NoDoubleGrant == \A i \in Locks : grant_calls[i] <= 1

    \* EX conflicts with EX: at most one lock granted (unless CompatibleMode)
    GrantedCompatible ==
        (~holder_active /\ ~CompatibleMode) => (GrantedCount <= 1)

    NoGrantWhileHeld ==
        holder_active => (GrantedCount = 0)

    PoolCorrect == pool_count = GrantedCount

    WaitingIntegrity ==
        \A i \in Locks :
            (lock_list[i] = "waiting") => (grant_calls[i] = 0)

    \* Terminal: when reprocessor finishes after an ERESTART-
    \* triggering cancel (holder cancelled during BL_AST window),
    \* at least one waiting lock must have been granted.
    \* If holder cancels AFTER the window, a separate reprocess
    \* handles it (not modeled here).
    \*
    \* Checked only when holder cancelled AND reprocessor saw it
    \* (erestart was set during the window).  We detect this by
    \* checking: reprocessor done, holder gone, and no lock was
    \* granted -- which means the rescan missed its chance.
    \* After ERESTART rescan, if holder cancelled:
    \* - EX mode: at least one waiting lock must be granted
    \* - PR/CompatibleMode: ALL waiting locks must be granted
    \* (since they're compatible with each other)
    NoMissedGrant ==
        (rp_phase = "done" /\ did_restart /\ ~holder_active
         /\ pc["failed_lock"] \in {"FL_Wait", "Done"}) =>
            IF CompatibleMode
            THEN \* All non-cancelled waiting locks must be granted
                 ~(\E i \in Locks : lock_list[i] = "waiting")
            ELSE \* At least one must be granted (or all cancelled)
                 (GrantedCount = 0) =>
                    ~(\E i \in Locks : lock_list[i] = "waiting")

    \* LU-14522: After a granted lock is destroyed (failed enqueue),
    \* if no holder and no remaining granted locks block waiters,
    \* no waiter should be stuck.  Violated when ldlm_reprocess_all
    \* is not called after lock destruction.
    NoStuckWaiter ==
        (pc["failed_lock"] = "Done" /\ ~holder_active
            /\ ~(\E i \in Locks : IsGranted(i))) =>
                ~(\E i \in Locks : lock_list[i] = "waiting")

    \* Terminal: when ALL processes are done, no waiting lock should
    \* remain that COULD have been granted.  This is stronger than
    \* NoMissedGrant and NoStuckWaiter, which check specific scenarios.
    \* A violation here means a lock was grantable but nobody granted it.
    NoRemainingGrantable ==
        (pc["holder_cancel"] = "Done"
         /\ pc["reprocessor"] = "Done"
         /\ pc["concurrent_cancel"] = "Done"
         /\ pc["failed_lock"] = "Done") =>
            ~(\E i \in Locks :
                lock_list[i] = "waiting"
                /\ ~holder_active
                /\ (CompatibleMode
                    \/ ~(\E j \in Locks : j /= i /\ IsGranted(j))))

    TypeOK ==
        /\ \A i \in Locks : lock_list[i] \in {"waiting", "granted", "none"}
        /\ \A i \in Locks : grant_calls[i] \in 0..3
        /\ pool_count \in -1..5
        /\ rp_cursor \in 1..(NumLocks+1)
        /\ fl_cursor \in 1..(NumLocks+1)
end define;

macro TryGrant(i) begin
    \* EX mode: conflicts with holder AND other granted locks
    \* PR mode (CompatibleMode): conflicts with holder only
    if ~holder_active
       /\ (CompatibleMode \/ ~(\E j \in Locks : j /= i /\ IsGranted(j))) then
        lock_list[i] := "granted";
        lock_granted[i] := TRUE;
        grant_calls[i] := grant_calls[i] + 1;
        pool_count := pool_count + 1;
        granted_this_pass := granted_this_pass \union {i};
    end if;
end macro;

\* ================================================================
\* HolderCancel: Holder H cancels during the BL_AST window.
\*
\* This always triggers ERESTART: ldlm_handle_ast_error
\* (ldlm_lockd.c:686-756) calls ldlm_lock_cancel and returns
\* -ERESTART at 698-699 (cancel already received) or 751-752
\* (client returned -EINVAL); the instant-cancel variant is
\* ldlm_server_blocking_ast:954-969 + ldlm_ast_fini:833-837.
\*
\* In the real code: BL_AST reply arrives -> ldlm_cb_interpret
\* (ldlm_lockd.c:758-814) -> ldlm_handle_ast_error ->
\* ldlm_lock_cancel(lock) -> atomic_inc(&arg->restart) at 811 ->
\* ldlm_run_ast_work (ldlm_lock.c:2315-2373) returns -ERESTART
\* at 2368.
\* ================================================================
fair process HolderCancel = "holder_cancel"
begin
HC_Wait:
    await rp_phase = "bl_sending";

HC_Lock:
    await lr_lock = "free";
    lr_lock := "holder_cancel";

HC_Cancel:
    holder_active := FALSE;
    \* Instant cancel always produces ERESTART
    erestart := TRUE;
    lr_lock := "free";
end process;

\* ================================================================
\* Reprocessor: Iterates the waiting queue under lr_lock.
\*
\* Models: ldlm_reprocess_queue (ldlm_lock.c:1958-2020)
\* ================================================================
fair process Reprocessor = "reprocessor"
begin
RP_Start:
    await lr_lock = "free";
    lr_lock := "reprocessor";
    rp_phase := "scanning";
    rp_cursor := 1;
    bl_ast_list := {};
    granted_this_pass := {};
    erestart := FALSE;

RP_Scan:
    if rp_cursor <= NumLocks then
        if lock_list[rp_cursor] = "waiting" then
            TryGrant(rp_cursor);
            if lock_list[rp_cursor] = "waiting" then
                \* Conflict: need BL_ASTs.  ITER_STOP for RESCAN.
                bl_ast_list := bl_ast_list \union {rp_cursor};
                goto RP_AfterScan;
            end if;
        end if;
RP_Advance:
        rp_cursor := rp_cursor + 1;
        goto RP_Scan;
    end if;

RP_AfterScan:
    if bl_ast_list /= {} then
        \* unlock_res(res) -- RACE WINDOW OPENS
        lr_lock := "free";
        rp_phase := "bl_sending";
    else
        \* Nothing to send, we're done
        lr_lock := "free";
        rp_phase := "done";
        goto RP_Done;
    end if;

RP_WaitASTs:
    \* ldlm_run_ast_work: wait for BL_AST completion.
    \* In reality this is synchronous -- it sends RPCs and waits.
    \* HolderCancel runs during this window.
    skip;

RP_Relock:
    await lr_lock = "free";
    lr_lock := "reprocessor";

RP_CheckRestart:
    if erestart /\ ~InjectBugNoRestart then
        rp_phase := "scanning";
        if InjectBugLocalRestart then
            \* LU-13692 BUG: enqueue_helper GOTO(restart)
            \* only re-runs policy for the LAST lock (the
            \* one being enqueued).  Earlier waiting locks
            \* that are now eligible get missed.
            rp_cursor := NumLocks;
        else
            \* FIX: full rescan from beginning of waiting queue
            rp_cursor := 1;
        end if;
        bl_ast_list := {};
        granted_this_pass := {};
        erestart := FALSE;
        did_restart := TRUE;
        goto RP_Scan;
    end if;
RP_BugMark:
    \* Bug path: if InjectBugNoRestart, we skip restart but
    \* still mark that erestart was requested (for invariant)
    if erestart /\ InjectBugNoRestart then
        did_restart := TRUE;
    end if;

RP_Finish:
    rp_phase := "done";
    lr_lock := "free";

RP_Done:
    skip;
end process;

\* ================================================================
\* ConcurrentCancel: A waiting lock gets cancelled during the
\* BL_AST window.
\*
\* Models: Client cancel RPC (ldlm_request_cancel, ldlm_lockd.c:
\* 1716-1810) on a different thread; ldlm_lock_cancel
\* (ldlm_lock.c:2496-2538) acquires lr_lock, unlinks the lock from
\* the waiting list (2527) and destroys it (2528).
\* ================================================================
fair process ConcurrentCancel = "concurrent_cancel"
begin
CC_Wait:
    await rp_phase = "bl_sending";

CC_Lock:
    await lr_lock = "free";
    lr_lock := "concurrent_cancel";

CC_Cancel:
    \* Cancel the last waiting lock
    if lock_list[NumLocks] = "waiting" then
        lock_list[NumLocks] := "none";
    end if;
    lr_lock := "free";
end process;

\* ================================================================
\* FailedLock: A granted lock's export disconnects, the lock is
\* destroyed.  The fix (LU-14522) calls ldlm_reprocess_all after
\* destroying the lock, allowing remaining waiters to be granted.
\*
\* Scenario: Reprocessor grants lock L1.  L2 still waits (EX vs
\* EX conflict with L1).  L1's export disconnects ->
\* ldlm_handle_enqueue destroys L1.  Without reprocess, L2
\* stays waiting forever.
\*
\* Models: ldlm_handle_enqueue error path (ldlm_lockd.c:1569-1581;
\* ldlm_lock_cancel at 1572, ldlm_reprocess_all at 1579).
\* ================================================================
fair process FailedLock = "failed_lock"
begin
FL_Wait:
    \* Wait for a granted lock to exist.  Export disconnect can
    \* happen at any time -- during BL_AST window (lr_lock free)
    \* or after reprocess completes.  This models the race between
    \* FailedLock and the reprocessor more faithfully than waiting
    \* for rp_phase = "done".
    await (\E i \in Locks : IsGranted(i))
       /\ (rp_phase = "done" \/ rp_phase = "bl_sending");

FL_Lock:
    await lr_lock = "free";
    lr_lock := "failed_lock";

FL_Destroy:
    \* Export disconnects during enqueue: destroy the granted lock.
    \* ldlm_resource_unlink_lock + ldlm_lock_destroy_nolock
    with i \in {j \in Locks : IsGranted(j)} do
        lock_list[i] := "none";
        pool_count := pool_count - 1;
    end with;

FL_CheckReprocess:
    if InjectBugNoReprocessOnFail then
        \* BUG (LU-14522): skip ldlm_reprocess_all entirely.
        \* Waiting locks that conflicted only with the destroyed
        \* lock will never be granted.
        lr_lock := "free";
        goto FL_Done;
    end if;
FL_InitScan:
    \* FIX: call ldlm_reprocess_all(lock->l_resource, lock)
    fl_cursor := 1;

FL_Scan:
    if fl_cursor <= NumLocks then
        if lock_list[fl_cursor] = "waiting" then
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

\* BEGIN TRANSLATION
VARIABLES lr_lock, holder_active, lock_list, lock_granted, grant_calls,
          pool_count, rp_phase, rp_cursor, bl_ast_list, granted_this_pass,
          erestart, did_restart, fl_cursor, pc

(* define statement *)
IsGranted(i) == lock_list[i] = "granted"
GrantedCount == Cardinality({i \in Locks : IsGranted(i)})



NoDoubleGrant == \A i \in Locks : grant_calls[i] <= 1


GrantedCompatible ==
    (~holder_active /\ ~CompatibleMode) => (GrantedCount <= 1)

NoGrantWhileHeld ==
    holder_active => (GrantedCount = 0)

PoolCorrect == pool_count = GrantedCount

WaitingIntegrity ==
    \A i \in Locks :
        (lock_list[i] = "waiting") => (grant_calls[i] = 0)















NoMissedGrant ==
    (rp_phase = "done" /\ did_restart /\ ~holder_active
     /\ pc["failed_lock"] \in {"FL_Wait", "Done"}) =>
        IF CompatibleMode
        THEN
             ~(\E i \in Locks : lock_list[i] = "waiting")
        ELSE
             (GrantedCount = 0) =>
                ~(\E i \in Locks : lock_list[i] = "waiting")





NoStuckWaiter ==
    (pc["failed_lock"] = "Done" /\ ~holder_active
        /\ ~(\E i \in Locks : IsGranted(i))) =>
            ~(\E i \in Locks : lock_list[i] = "waiting")


NoRemainingGrantable ==
    (pc["holder_cancel"] = "Done"
     /\ pc["reprocessor"] = "Done"
     /\ pc["concurrent_cancel"] = "Done"
     /\ pc["failed_lock"] = "Done") =>
        ~(\E i \in Locks :
            lock_list[i] = "waiting"
            /\ ~holder_active
            /\ (CompatibleMode
                \/ ~(\E j \in Locks : j /= i /\ IsGranted(j))))

TypeOK ==
    /\ \A i \in Locks : lock_list[i] \in {"waiting", "granted", "none"}
    /\ \A i \in Locks : grant_calls[i] \in 0..3
    /\ pool_count \in -1..5
    /\ rp_cursor \in 1..(NumLocks+1)
    /\ fl_cursor \in 1..(NumLocks+1)


vars == << lr_lock, holder_active, lock_list, lock_granted, grant_calls,
           pool_count, rp_phase, rp_cursor, bl_ast_list, granted_this_pass,
           erestart, did_restart, fl_cursor, pc >>

ProcSet == {"holder_cancel"} \cup {"reprocessor"} \cup {"concurrent_cancel"} \cup {"failed_lock"}

Init == (* Global variables *)
        /\ lr_lock = "free"
        /\ holder_active = TRUE
        /\ lock_list = [i \in Locks |-> "waiting"]
        /\ lock_granted = [i \in Locks |-> FALSE]
        /\ grant_calls = [i \in Locks |-> 0]
        /\ pool_count = 0
        /\ rp_phase = "idle"
        /\ rp_cursor = 1
        /\ bl_ast_list = {}
        /\ granted_this_pass = {}
        /\ erestart = FALSE
        /\ did_restart = FALSE
        /\ fl_cursor = 1
        /\ pc = [self \in ProcSet |-> CASE self = "holder_cancel" -> "HC_Wait"
                                        [] self = "reprocessor" -> "RP_Start"
                                        [] self = "concurrent_cancel" -> "CC_Wait"
                                        [] self = "failed_lock" -> "FL_Wait"]

HC_Wait == /\ pc["holder_cancel"] = "HC_Wait"
           /\ rp_phase = "bl_sending"
           /\ pc' = [pc EXCEPT !["holder_cancel"] = "HC_Lock"]
           /\ UNCHANGED << lr_lock, holder_active, lock_list, lock_granted,
                           grant_calls, pool_count, rp_phase, rp_cursor,
                           bl_ast_list, granted_this_pass, erestart,
                           did_restart, fl_cursor >>

HC_Lock == /\ pc["holder_cancel"] = "HC_Lock"
           /\ lr_lock = "free"
           /\ lr_lock' = "holder_cancel"
           /\ pc' = [pc EXCEPT !["holder_cancel"] = "HC_Cancel"]
           /\ UNCHANGED << holder_active, lock_list, lock_granted, grant_calls,
                           pool_count, rp_phase, rp_cursor, bl_ast_list,
                           granted_this_pass, erestart, did_restart, fl_cursor >>

HC_Cancel == /\ pc["holder_cancel"] = "HC_Cancel"
             /\ holder_active' = FALSE
             /\ erestart' = TRUE
             /\ lr_lock' = "free"
             /\ pc' = [pc EXCEPT !["holder_cancel"] = "Done"]
             /\ UNCHANGED << lock_list, lock_granted, grant_calls, pool_count,
                             rp_phase, rp_cursor, bl_ast_list,
                             granted_this_pass, did_restart, fl_cursor >>

HolderCancel == HC_Wait \/ HC_Lock \/ HC_Cancel

RP_Start == /\ pc["reprocessor"] = "RP_Start"
            /\ lr_lock = "free"
            /\ lr_lock' = "reprocessor"
            /\ rp_phase' = "scanning"
            /\ rp_cursor' = 1
            /\ bl_ast_list' = {}
            /\ granted_this_pass' = {}
            /\ erestart' = FALSE
            /\ pc' = [pc EXCEPT !["reprocessor"] = "RP_Scan"]
            /\ UNCHANGED << holder_active, lock_list, lock_granted,
                            grant_calls, pool_count, did_restart, fl_cursor >>

RP_Scan == /\ pc["reprocessor"] = "RP_Scan"
           /\ IF rp_cursor <= NumLocks
                 THEN /\ IF lock_list[rp_cursor] = "waiting"
                            THEN /\ IF ~holder_active
                                       /\ (CompatibleMode \/ ~(\E j \in Locks : j /= rp_cursor /\ IsGranted(j)))
                                       THEN /\ lock_list' = [lock_list EXCEPT ![rp_cursor] = "granted"]
                                            /\ lock_granted' = [lock_granted EXCEPT ![rp_cursor] = TRUE]
                                            /\ grant_calls' = [grant_calls EXCEPT ![rp_cursor] = grant_calls[rp_cursor] + 1]
                                            /\ pool_count' = pool_count + 1
                                            /\ granted_this_pass' = (granted_this_pass \union {rp_cursor})
                                       ELSE /\ TRUE
                                            /\ UNCHANGED << lock_list,
                                                            lock_granted,
                                                            grant_calls,
                                                            pool_count,
                                                            granted_this_pass >>
                                 /\ IF lock_list'[rp_cursor] = "waiting"
                                       THEN /\ bl_ast_list' = (bl_ast_list \union {rp_cursor})
                                            /\ pc' = [pc EXCEPT !["reprocessor"] = "RP_AfterScan"]
                                       ELSE /\ pc' = [pc EXCEPT !["reprocessor"] = "RP_Advance"]
                                            /\ UNCHANGED bl_ast_list
                            ELSE /\ pc' = [pc EXCEPT !["reprocessor"] = "RP_Advance"]
                                 /\ UNCHANGED << lock_list, lock_granted,
                                                 grant_calls, pool_count,
                                                 bl_ast_list,
                                                 granted_this_pass >>
                 ELSE /\ pc' = [pc EXCEPT !["reprocessor"] = "RP_AfterScan"]
                      /\ UNCHANGED << lock_list, lock_granted, grant_calls,
                                      pool_count, bl_ast_list,
                                      granted_this_pass >>
           /\ UNCHANGED << lr_lock, holder_active, rp_phase, rp_cursor,
                           erestart, did_restart, fl_cursor >>

RP_Advance == /\ pc["reprocessor"] = "RP_Advance"
              /\ rp_cursor' = rp_cursor + 1
              /\ pc' = [pc EXCEPT !["reprocessor"] = "RP_Scan"]
              /\ UNCHANGED << lr_lock, holder_active, lock_list, lock_granted,
                              grant_calls, pool_count, rp_phase, bl_ast_list,
                              granted_this_pass, erestart, did_restart,
                              fl_cursor >>

RP_AfterScan == /\ pc["reprocessor"] = "RP_AfterScan"
                /\ IF bl_ast_list /= {}
                      THEN /\ lr_lock' = "free"
                           /\ rp_phase' = "bl_sending"
                           /\ pc' = [pc EXCEPT !["reprocessor"] = "RP_WaitASTs"]
                      ELSE /\ lr_lock' = "free"
                           /\ rp_phase' = "done"
                           /\ pc' = [pc EXCEPT !["reprocessor"] = "RP_Done"]
                /\ UNCHANGED << holder_active, lock_list, lock_granted,
                                grant_calls, pool_count, rp_cursor,
                                bl_ast_list, granted_this_pass, erestart,
                                did_restart, fl_cursor >>

RP_WaitASTs == /\ pc["reprocessor"] = "RP_WaitASTs"
               /\ TRUE
               /\ pc' = [pc EXCEPT !["reprocessor"] = "RP_Relock"]
               /\ UNCHANGED << lr_lock, holder_active, lock_list, lock_granted,
                               grant_calls, pool_count, rp_phase, rp_cursor,
                               bl_ast_list, granted_this_pass, erestart,
                               did_restart, fl_cursor >>

RP_Relock == /\ pc["reprocessor"] = "RP_Relock"
             /\ lr_lock = "free"
             /\ lr_lock' = "reprocessor"
             /\ pc' = [pc EXCEPT !["reprocessor"] = "RP_CheckRestart"]
             /\ UNCHANGED << holder_active, lock_list, lock_granted,
                             grant_calls, pool_count, rp_phase, rp_cursor,
                             bl_ast_list, granted_this_pass, erestart,
                             did_restart, fl_cursor >>

RP_CheckRestart == /\ pc["reprocessor"] = "RP_CheckRestart"
                   /\ IF erestart /\ ~InjectBugNoRestart
                         THEN /\ rp_phase' = "scanning"
                              /\ IF InjectBugLocalRestart
                                    THEN /\ rp_cursor' = NumLocks
                                    ELSE /\ rp_cursor' = 1
                              /\ bl_ast_list' = {}
                              /\ granted_this_pass' = {}
                              /\ erestart' = FALSE
                              /\ did_restart' = TRUE
                              /\ pc' = [pc EXCEPT !["reprocessor"] = "RP_Scan"]
                         ELSE /\ pc' = [pc EXCEPT !["reprocessor"] = "RP_BugMark"]
                              /\ UNCHANGED << rp_phase, rp_cursor, bl_ast_list,
                                              granted_this_pass, erestart,
                                              did_restart >>
                   /\ UNCHANGED << lr_lock, holder_active, lock_list,
                                   lock_granted, grant_calls, pool_count,
                                   fl_cursor >>

RP_BugMark == /\ pc["reprocessor"] = "RP_BugMark"
              /\ IF erestart /\ InjectBugNoRestart
                    THEN /\ did_restart' = TRUE
                    ELSE /\ TRUE
                         /\ UNCHANGED did_restart
              /\ pc' = [pc EXCEPT !["reprocessor"] = "RP_Finish"]
              /\ UNCHANGED << lr_lock, holder_active, lock_list, lock_granted,
                              grant_calls, pool_count, rp_phase, rp_cursor,
                              bl_ast_list, granted_this_pass, erestart,
                              fl_cursor >>

RP_Finish == /\ pc["reprocessor"] = "RP_Finish"
             /\ rp_phase' = "done"
             /\ lr_lock' = "free"
             /\ pc' = [pc EXCEPT !["reprocessor"] = "RP_Done"]
             /\ UNCHANGED << holder_active, lock_list, lock_granted,
                             grant_calls, pool_count, rp_cursor, bl_ast_list,
                             granted_this_pass, erestart, did_restart,
                             fl_cursor >>

RP_Done == /\ pc["reprocessor"] = "RP_Done"
           /\ TRUE
           /\ pc' = [pc EXCEPT !["reprocessor"] = "Done"]
           /\ UNCHANGED << lr_lock, holder_active, lock_list, lock_granted,
                           grant_calls, pool_count, rp_phase, rp_cursor,
                           bl_ast_list, granted_this_pass, erestart,
                           did_restart, fl_cursor >>

Reprocessor == RP_Start \/ RP_Scan \/ RP_Advance \/ RP_AfterScan
                  \/ RP_WaitASTs \/ RP_Relock \/ RP_CheckRestart
                  \/ RP_BugMark \/ RP_Finish \/ RP_Done

CC_Wait == /\ pc["concurrent_cancel"] = "CC_Wait"
           /\ rp_phase = "bl_sending"
           /\ pc' = [pc EXCEPT !["concurrent_cancel"] = "CC_Lock"]
           /\ UNCHANGED << lr_lock, holder_active, lock_list, lock_granted,
                           grant_calls, pool_count, rp_phase, rp_cursor,
                           bl_ast_list, granted_this_pass, erestart,
                           did_restart, fl_cursor >>

CC_Lock == /\ pc["concurrent_cancel"] = "CC_Lock"
           /\ lr_lock = "free"
           /\ lr_lock' = "concurrent_cancel"
           /\ pc' = [pc EXCEPT !["concurrent_cancel"] = "CC_Cancel"]
           /\ UNCHANGED << holder_active, lock_list, lock_granted, grant_calls,
                           pool_count, rp_phase, rp_cursor, bl_ast_list,
                           granted_this_pass, erestart, did_restart, fl_cursor >>

CC_Cancel == /\ pc["concurrent_cancel"] = "CC_Cancel"
             /\ IF lock_list[NumLocks] = "waiting"
                   THEN /\ lock_list' = [lock_list EXCEPT ![NumLocks] = "none"]
                   ELSE /\ TRUE
                        /\ UNCHANGED lock_list
             /\ lr_lock' = "free"
             /\ pc' = [pc EXCEPT !["concurrent_cancel"] = "Done"]
             /\ UNCHANGED << holder_active, lock_granted, grant_calls,
                             pool_count, rp_phase, rp_cursor, bl_ast_list,
                             granted_this_pass, erestart, did_restart,
                             fl_cursor >>

ConcurrentCancel == CC_Wait \/ CC_Lock \/ CC_Cancel

FL_Wait == /\ pc["failed_lock"] = "FL_Wait"
           /\ (\E i \in Locks : IsGranted(i))
           /\ (rp_phase = "done" \/ rp_phase = "bl_sending")
           /\ pc' = [pc EXCEPT !["failed_lock"] = "FL_Lock"]
           /\ UNCHANGED << lr_lock, holder_active, lock_list, lock_granted,
                           grant_calls, pool_count, rp_phase, rp_cursor,
                           bl_ast_list, granted_this_pass, erestart,
                           did_restart, fl_cursor >>

FL_Lock == /\ pc["failed_lock"] = "FL_Lock"
           /\ lr_lock = "free"
           /\ lr_lock' = "failed_lock"
           /\ pc' = [pc EXCEPT !["failed_lock"] = "FL_Destroy"]
           /\ UNCHANGED << holder_active, lock_list, lock_granted, grant_calls,
                           pool_count, rp_phase, rp_cursor, bl_ast_list,
                           granted_this_pass, erestart, did_restart, fl_cursor >>

FL_Destroy == /\ pc["failed_lock"] = "FL_Destroy"
              /\ \E i \in {j \in Locks : IsGranted(j)}:
                   /\ lock_list' = [lock_list EXCEPT ![i] = "none"]
                   /\ pool_count' = pool_count - 1
              /\ pc' = [pc EXCEPT !["failed_lock"] = "FL_CheckReprocess"]
              /\ UNCHANGED << lr_lock, holder_active, lock_granted,
                              grant_calls, rp_phase, rp_cursor, bl_ast_list,
                              granted_this_pass, erestart, did_restart,
                              fl_cursor >>

FL_CheckReprocess == /\ pc["failed_lock"] = "FL_CheckReprocess"
                     /\ IF InjectBugNoReprocessOnFail
                           THEN /\ lr_lock' = "free"
                                /\ pc' = [pc EXCEPT !["failed_lock"] = "FL_Done"]
                           ELSE /\ pc' = [pc EXCEPT !["failed_lock"] = "FL_InitScan"]
                                /\ UNCHANGED lr_lock
                     /\ UNCHANGED << holder_active, lock_list, lock_granted,
                                     grant_calls, pool_count, rp_phase,
                                     rp_cursor, bl_ast_list, granted_this_pass,
                                     erestart, did_restart, fl_cursor >>

FL_InitScan == /\ pc["failed_lock"] = "FL_InitScan"
               /\ fl_cursor' = 1
               /\ pc' = [pc EXCEPT !["failed_lock"] = "FL_Scan"]
               /\ UNCHANGED << lr_lock, holder_active, lock_list, lock_granted,
                               grant_calls, pool_count, rp_phase, rp_cursor,
                               bl_ast_list, granted_this_pass, erestart,
                               did_restart >>

FL_Scan == /\ pc["failed_lock"] = "FL_Scan"
           /\ IF fl_cursor <= NumLocks
                 THEN /\ IF lock_list[fl_cursor] = "waiting"
                            THEN /\ IF ~holder_active
                                       /\ (CompatibleMode \/ ~(\E j \in Locks : j /= fl_cursor /\ IsGranted(j)))
                                       THEN /\ lock_list' = [lock_list EXCEPT ![fl_cursor] = "granted"]
                                            /\ lock_granted' = [lock_granted EXCEPT ![fl_cursor] = TRUE]
                                            /\ grant_calls' = [grant_calls EXCEPT ![fl_cursor] = grant_calls[fl_cursor] + 1]
                                            /\ pool_count' = pool_count + 1
                                            /\ granted_this_pass' = (granted_this_pass \union {fl_cursor})
                                       ELSE /\ TRUE
                                            /\ UNCHANGED << lock_list,
                                                            lock_granted,
                                                            grant_calls,
                                                            pool_count,
                                                            granted_this_pass >>
                            ELSE /\ TRUE
                                 /\ UNCHANGED << lock_list, lock_granted,
                                                 grant_calls, pool_count,
                                                 granted_this_pass >>
                      /\ pc' = [pc EXCEPT !["failed_lock"] = "FL_ScanNext"]
                 ELSE /\ pc' = [pc EXCEPT !["failed_lock"] = "FL_Unlock"]
                      /\ UNCHANGED << lock_list, lock_granted, grant_calls,
                                      pool_count, granted_this_pass >>
           /\ UNCHANGED << lr_lock, holder_active, rp_phase, rp_cursor,
                           bl_ast_list, erestart, did_restart, fl_cursor >>

FL_ScanNext == /\ pc["failed_lock"] = "FL_ScanNext"
               /\ fl_cursor' = fl_cursor + 1
               /\ pc' = [pc EXCEPT !["failed_lock"] = "FL_Scan"]
               /\ UNCHANGED << lr_lock, holder_active, lock_list, lock_granted,
                               grant_calls, pool_count, rp_phase, rp_cursor,
                               bl_ast_list, granted_this_pass, erestart,
                               did_restart >>

FL_Unlock == /\ pc["failed_lock"] = "FL_Unlock"
             /\ lr_lock' = "free"
             /\ pc' = [pc EXCEPT !["failed_lock"] = "FL_Done"]
             /\ UNCHANGED << holder_active, lock_list, lock_granted,
                             grant_calls, pool_count, rp_phase, rp_cursor,
                             bl_ast_list, granted_this_pass, erestart,
                             did_restart, fl_cursor >>

FL_Done == /\ pc["failed_lock"] = "FL_Done"
           /\ TRUE
           /\ pc' = [pc EXCEPT !["failed_lock"] = "Done"]
           /\ UNCHANGED << lr_lock, holder_active, lock_list, lock_granted,
                           grant_calls, pool_count, rp_phase, rp_cursor,
                           bl_ast_list, granted_this_pass, erestart,
                           did_restart, fl_cursor >>

FailedLock == FL_Wait \/ FL_Lock \/ FL_Destroy \/ FL_CheckReprocess
                 \/ FL_InitScan \/ FL_Scan \/ FL_ScanNext \/ FL_Unlock
                 \/ FL_Done

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == HolderCancel \/ Reprocessor \/ ConcurrentCancel \/ FailedLock
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(HolderCancel)
        /\ WF_vars(Reprocessor)
        /\ WF_vars(ConcurrentCancel)
        /\ WF_vars(FailedLock)

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

\* ================================================================
\* Liveness: reprocessing eventually completes
\* ================================================================
EventualCompletion ==
    <>(rp_phase = "done")

=============================================================================
