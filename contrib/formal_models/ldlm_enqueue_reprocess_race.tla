--------------------- MODULE ldlm_enqueue_reprocess_race ---------------------
(*
 * Model: LDLM concurrent enqueue vs reprocess race
 *
 * Tests the interleaving between ldlm_lock_enqueue (adding a new
 * waiter) and ldlm_reprocess_queue (granting existing waiters),
 * both operating on the same resource's waiting queue.
 *
 * Scenario:
 *   - Resource R has holder H (EX mode)
 *   - W1, W2 already in waiting queue (each wants EX or PR)
 *   - BL_AST sent to H
 *   - H cancels -> triggers ldlm_reprocess_all (Reprocessor)
 *   - Meanwhile, a new client enqueues W3 (NewEnqueue)
 *
 * The critical race: the Reprocessor holds lr_lock while scanning,
 * grants W1, then hits W2 (conflict if EX) and enters BL_AST
 * window (drops lr_lock).  During this window:
 *   (a) NewEnqueue can acquire lr_lock and process its enqueue
 *   (b) The new enqueue checks both granted and waiting queues
 *   (c) It might see W1 as granted and conflict, or see it as
 *       waiting (stale view) if the reprocessor hasn't yet
 *       moved it to granted
 *
 * But since lr_lock serializes, (c) can't happen -- NewEnqueue
 * always sees the state after Reprocessor releases lr_lock.
 * The question: does the Reprocessor's ERESTART rescan after
 * the BL_AST window correctly handle the newly-enqueued W3?
 *
 * Key subtlety from the real code:
 *   - ldlm_process_plain_lock RESCAN checks both granted AND
 *     waiting queues for conflicts
 *   - A new waiter added to the waiting queue AFTER a granted
 *     lock means the granted lock is BEFORE the new waiter
 *   - The new waiter stops at itself in the waiting queue scan,
 *     so it sees waiting-queue locks that precede it
 *   - The RESCAN policy does NOT send new BL_ASTs
 *   - Only the ENQUEUE path sends BL_ASTs to conflicting holders
 *
 * Source (lustre-release master 47638add78):
 *   ldlm_lock_enqueue          ldlm_lock.c:1783-1949
 *   ldlm_lock_enqueue_helper   ldlm_lock.c:1750-1770
 *   ldlm_handle_conflict_lock  ldlm_lock.c:2036-2094 (add to
 *     lr_waiting 2053-2054, unlock_res 2055, BL_AST send 2057,
 *     ldlm_reprocess_all on -ERESTART 2064-2065, lock_res 2067)
 *   ldlm_process_plain_lock    ldlm_plain.c:110-147
 *     (RESCAN 124-136 with NULL work lists, ENQUEUE 138-146)
 *   ldlm_plain_compat_queue    ldlm_plain.c:47-100 (stops at the
 *     request itself in the waiting queue, 64-65)
 *   ldlm_reprocess_queue       ldlm_lock.c:1958-2020
 *   __ldlm_reprocess_all       ldlm_lock.c:2383-2428
 *   ldlm_handle_enqueue        ldlm_lockd.c:1248-1595
 *     (ldlm_reprocess_all after a successful enqueue 1583-1586)
 *
 * Validated against: lustre-release master 47638add78 (2026-09-06)
 *
 * Validation notes: the "RESCAN policy does NOT send new BL_ASTs"
 * claim holds for plain and extent locks (NULL work lists at
 * ldlm_plain.c:126/129 and ldlm_extent.c:883-886), so for those
 * types ldlm_reprocess_queue never drops lr_lock in RESCAN; the
 * drop / relock / restart window modeled by RP_AfterScan ..
 * RP_CheckRestart corresponds to the CP_AST send in
 * __ldlm_reprocess_all (lr_lock dropped 2412, goto restart 2419).
 * IBITS RESCAN is handled by ldlm_reprocess_inodebits_queue
 * (ldlm_inodebits.c:47-124), which does collect BL_ASTs from the
 * granted queue (ldlm_process_inodebits_lock 350-351, 375-376) and
 * drops lr_lock to send them (108-117).
 *)
EXTENDS Integers, FiniteSets, TLC

CONSTANTS
    CompatibleMode,       \* TRUE = PR waiters; FALSE = EX waiters
    NewEnqueueMode,       \* "same" = same mode as waiters;
                          \* "compat" = compatible with waiters
    InjectBugNoRescan     \* TRUE = skip ERESTART rescan after BL_AST

(* --algorithm ldlm_enqueue_reprocess_race

variables
    lr_lock = "free",
    holder_active = TRUE,

    \* Locks: 1=W1, 2=W2, 3=W3(new)
    \* W1, W2 start waiting; W3 starts as "none" (not yet enqueued)
    lock_state = <<"waiting", "waiting", "none">>,
    grant_count = <<0, 0, 0>>,

    \* Reprocessor state
    rp_phase = "idle",
    rp_cursor = 1,
    rp_needs_blast = FALSE,
    rp_erestart = FALSE,

    \* W3 mode: compatible with W1/W2 or conflicting
    w3_compat_with_waiters = (NewEnqueueMode = "compat");

define
    IsGranted(i) == lock_state[i] = "granted"
    IsWaiting(i) == lock_state[i] = "waiting"
    GrantedCount == Cardinality({i \in 1..3 : IsGranted(i)})
    WaitingCount == Cardinality({i \in 1..3 : IsWaiting(i)})

    \* Mode conflict check:
    \* - EX vs EX: always conflicts
    \* - PR vs PR: never conflicts (CompatibleMode)
    \* - W3 vs W1/W2: depends on w3_compat_with_waiters
    \* For simplicity: if CompatibleMode, all waiters are PR
    \* and compatible with each other.
    \* W3 is always conflicting with holder (otherwise no point).
    ConflictsWithGranted(i) ==
        \* A waiting lock conflicts with a granted lock if:
        \* - Holder is active (holder is EX, conflicts with everything)
        \* - Another granted EX lock exists (unless CompatibleMode)
        \* - For W3 with "compat" mode: doesn't conflict with other
        \*   PR-granted locks, but conflicts with EX-granted locks
        IF holder_active THEN TRUE
        ELSE IF CompatibleMode THEN FALSE  \* PR vs PR = compat
        ELSE IF i = 3 /\ w3_compat_with_waiters THEN
            \* W3 is compatible with other waiters' mode but
            \* still conflicts with EX-granted locks
            \E j \in 1..2 : IsGranted(j)
        ELSE
            \* EX mode: conflicts with any other granted lock
            \E j \in 1..3 : j /= i /\ IsGranted(j)

    \* ========== SAFETY INVARIANTS ==========

    NoDoubleGrant == \A i \in 1..3 : grant_count[i] <= 1

    \* EX mode: at most one granted (unless compat)
    GrantedCompatible ==
        (~holder_active /\ ~CompatibleMode) =>
            IF w3_compat_with_waiters
            \* W3 is compat with W1/W2 but W1/W2 conflict with each other
            \* So at most one of {W1,W2} granted, plus W3 can be granted
            THEN Cardinality({i \in 1..2 : IsGranted(i)}) <= 1
            ELSE GrantedCount <= 1

    NoGrantWhileHeld ==
        holder_active => GrantedCount = 0

    \* Terminal: no grantable lock left waiting when all done
    NoStuckWaiter ==
        (pc["cancel_thread"] = "Done"
         /\ pc["reprocessor"] = "Done"
         /\ pc["new_enqueue"] = "Done") =>
            ~(\E i \in 1..3 :
                lock_state[i] = "waiting"
                /\ ~ConflictsWithGranted(i))

    TypeOK ==
        /\ \A i \in 1..3 : lock_state[i] \in
                {"waiting", "granted", "none"}
        /\ \A i \in 1..3 : grant_count[i] \in 0..3
        /\ rp_cursor \in 1..4
end define;

macro TryGrant(i) begin
    if ~ConflictsWithGranted(i) /\ lock_state[i] = "waiting" then
        lock_state[i] := "granted";
        grant_count[i] := grant_count[i] + 1;
    end if;
end macro;

\* ================================================================
\* CancelThread: Holder cancels, triggers reprocess
\* ================================================================
fair process CancelThread = "cancel_thread"
begin
CT_Lock:
    await lr_lock = "free";
    lr_lock := "cancel_thread";
CT_Cancel:
    holder_active := FALSE;
    lr_lock := "free";
    rp_phase := "ready";
end process;

\* ================================================================
\* Reprocessor: Scans waiting queue after holder cancel
\* Models: ldlm_reprocess_queue in RESCAN mode (ldlm_lock.c:1958-2020,
\* called from __ldlm_reprocess_all 2383-2428)
\* ================================================================
fair process Reprocessor = "reprocessor"
begin
RP_WaitReady:
    await rp_phase = "ready";
RP_Lock:
    await lr_lock = "free";
    lr_lock := "reprocessor";
    rp_phase := "scanning";
    rp_cursor := 1;
    rp_needs_blast := FALSE;
    rp_erestart := FALSE;

RP_Scan:
    if rp_cursor <= 3 then
        if lock_state[rp_cursor] = "waiting" then
            TryGrant(rp_cursor);
            if lock_state[rp_cursor] = "waiting" then
                \* Still waiting = conflict.  In RESCAN mode:
                \* ITER_STOP -- stop scanning, go to BL_AST path
                rp_needs_blast := TRUE;
                goto RP_AfterScan;
            end if;
        end if;
RP_Advance:
        rp_cursor := rp_cursor + 1;
        goto RP_Scan;
    end if;

RP_AfterScan:
    if rp_needs_blast then
        lr_lock := "free";
        rp_phase := "bl_sending";
    else
        lr_lock := "free";
        rp_phase := "done";
        goto RP_Done;
    end if;

RP_WaitASTs:
    \* BL_AST window -- other threads can acquire lr_lock
    skip;

RP_Relock:
    await lr_lock = "free";
    lr_lock := "reprocessor";

RP_CheckRestart:
    if rp_erestart /\ ~InjectBugNoRescan then
        rp_phase := "scanning";
        rp_cursor := 1;
        rp_needs_blast := FALSE;
        rp_erestart := FALSE;
        goto RP_Scan;
    end if;

RP_Finish:
    rp_phase := "done";
    lr_lock := "free";

RP_Done:
    skip;
end process;

\* ================================================================
\* NewEnqueue: A new client enqueues W3 concurrently.
\* Models: ldlm_lock_enqueue (ldlm_lock.c:1783-1949) ->
\* ldlm_lock_enqueue_helper (1750-1770) -> ldlm_process_plain_lock
\* (ldlm_plain.c:110-147) -> ldlm_handle_conflict_lock (2036-2094)
\*
\* W3 arrives after the holder cancel but potentially while
\* the reprocessor is in its BL_AST window.
\*
\* ENQUEUE mode: checks granted + waiting queues.  If conflicts
\* found, adds to waiting queue and sends BL_ASTs.
\* ================================================================
fair process NewEnqueue = "new_enqueue"
begin
NE_Wait:
    \* Wait for holder to be cancelled (new lock arrives after)
    await ~holder_active;

NE_Lock:
    await lr_lock = "free";
    lr_lock := "new_enqueue";

NE_Enqueue:
    \* Check granted queue + waiting queue for conflicts
    \* In the real code: ldlm_process_plain_lock ENQUEUE path,
    \* ldlm_plain.c:138-146 (compat against granted + waiting ahead)
    if ~ConflictsWithGranted(3) then
        \* No granted conflicts.  Check waiting queue for conflicts.
        \* W3 sees locks ahead of it in the waiting queue.
        \* If W1 or W2 is still waiting and conflicts with W3,
        \* W3 must wait behind them (FIFO ordering).
        if CompatibleMode \/ w3_compat_with_waiters then
            \* PR or compat: no conflict with other PR waiters
            lock_state[3] := "granted";
            grant_count[3] := grant_count[3] + 1;
        elsif ~(\E j \in 1..2 : lock_state[j] = "waiting") then
            \* No waiting locks ahead -> grant
            lock_state[3] := "granted";
            grant_count[3] := grant_count[3] + 1;
        else
            \* EX waiter ahead in queue -> must wait
            lock_state[3] := "waiting";
        end if;
    else
        \* Conflicts with granted locks -> wait
        lock_state[3] := "waiting";
    end if;

NE_Unlock:
    lr_lock := "free";
    \* If W3 was granted, ldlm_handle_enqueue (ldlm_lockd.c:1583-1586)
    \* calls ldlm_reprocess_all for any waiters behind W3.  But in our
    \* model W3 is the last lock, so this is a no-op.
    \* If W3 was NOT granted, BL_ASTs were sent to conflicting holders
    \* which may set erestart on the ongoing reprocessor.
    if lock_state[3] = "waiting" /\ rp_phase = "bl_sending" then
        \* BL_AST sent during reprocessor's window could trigger
        \* ERESTART if a cancel arrives
        skip;  \* BL_ASTs sent but no immediate effect in this model
    end if;
end process;

end algorithm; *)
\* BEGIN TRANSLATION
VARIABLES lr_lock, holder_active, lock_state, grant_count, rp_phase,
          rp_cursor, rp_needs_blast, rp_erestart, w3_compat_with_waiters, pc

(* define statement *)
IsGranted(i) == lock_state[i] = "granted"
IsWaiting(i) == lock_state[i] = "waiting"
GrantedCount == Cardinality({i \in 1..3 : IsGranted(i)})
WaitingCount == Cardinality({i \in 1..3 : IsWaiting(i)})








ConflictsWithGranted(i) ==





    IF holder_active THEN TRUE
    ELSE IF CompatibleMode THEN FALSE
    ELSE IF i = 3 /\ w3_compat_with_waiters THEN


        \E j \in 1..2 : IsGranted(j)
    ELSE

        \E j \in 1..3 : j /= i /\ IsGranted(j)



NoDoubleGrant == \A i \in 1..3 : grant_count[i] <= 1


GrantedCompatible ==
    (~holder_active /\ ~CompatibleMode) =>
        IF w3_compat_with_waiters


        THEN Cardinality({i \in 1..2 : IsGranted(i)}) <= 1
        ELSE GrantedCount <= 1

NoGrantWhileHeld ==
    holder_active => GrantedCount = 0


NoStuckWaiter ==
    (pc["cancel_thread"] = "Done"
     /\ pc["reprocessor"] = "Done"
     /\ pc["new_enqueue"] = "Done") =>
        ~(\E i \in 1..3 :
            lock_state[i] = "waiting"
            /\ ~ConflictsWithGranted(i))

TypeOK ==
    /\ \A i \in 1..3 : lock_state[i] \in
            {"waiting", "granted", "none"}
    /\ \A i \in 1..3 : grant_count[i] \in 0..3
    /\ rp_cursor \in 1..4


vars == << lr_lock, holder_active, lock_state, grant_count, rp_phase,
           rp_cursor, rp_needs_blast, rp_erestart, w3_compat_with_waiters, pc
        >>

ProcSet == {"cancel_thread"} \cup {"reprocessor"} \cup {"new_enqueue"}

Init == (* Global variables *)
        /\ lr_lock = "free"
        /\ holder_active = TRUE
        /\ lock_state = <<"waiting", "waiting", "none">>
        /\ grant_count = <<0, 0, 0>>
        /\ rp_phase = "idle"
        /\ rp_cursor = 1
        /\ rp_needs_blast = FALSE
        /\ rp_erestart = FALSE
        /\ w3_compat_with_waiters = (NewEnqueueMode = "compat")
        /\ pc = [self \in ProcSet |-> CASE self = "cancel_thread" -> "CT_Lock"
                                        [] self = "reprocessor" -> "RP_WaitReady"
                                        [] self = "new_enqueue" -> "NE_Wait"]

CT_Lock == /\ pc["cancel_thread"] = "CT_Lock"
           /\ lr_lock = "free"
           /\ lr_lock' = "cancel_thread"
           /\ pc' = [pc EXCEPT !["cancel_thread"] = "CT_Cancel"]
           /\ UNCHANGED << holder_active, lock_state, grant_count, rp_phase,
                           rp_cursor, rp_needs_blast, rp_erestart,
                           w3_compat_with_waiters >>

CT_Cancel == /\ pc["cancel_thread"] = "CT_Cancel"
             /\ holder_active' = FALSE
             /\ lr_lock' = "free"
             /\ rp_phase' = "ready"
             /\ pc' = [pc EXCEPT !["cancel_thread"] = "Done"]
             /\ UNCHANGED << lock_state, grant_count, rp_cursor,
                             rp_needs_blast, rp_erestart,
                             w3_compat_with_waiters >>

CancelThread == CT_Lock \/ CT_Cancel

RP_WaitReady == /\ pc["reprocessor"] = "RP_WaitReady"
                /\ rp_phase = "ready"
                /\ pc' = [pc EXCEPT !["reprocessor"] = "RP_Lock"]
                /\ UNCHANGED << lr_lock, holder_active, lock_state,
                                grant_count, rp_phase, rp_cursor,
                                rp_needs_blast, rp_erestart,
                                w3_compat_with_waiters >>

RP_Lock == /\ pc["reprocessor"] = "RP_Lock"
           /\ lr_lock = "free"
           /\ lr_lock' = "reprocessor"
           /\ rp_phase' = "scanning"
           /\ rp_cursor' = 1
           /\ rp_needs_blast' = FALSE
           /\ rp_erestart' = FALSE
           /\ pc' = [pc EXCEPT !["reprocessor"] = "RP_Scan"]
           /\ UNCHANGED << holder_active, lock_state, grant_count,
                           w3_compat_with_waiters >>

RP_Scan == /\ pc["reprocessor"] = "RP_Scan"
           /\ IF rp_cursor <= 3
                 THEN /\ IF lock_state[rp_cursor] = "waiting"
                            THEN /\ IF ~ConflictsWithGranted(rp_cursor) /\ lock_state[rp_cursor] = "waiting"
                                       THEN /\ lock_state' = [lock_state EXCEPT ![rp_cursor] = "granted"]
                                            /\ grant_count' = [grant_count EXCEPT ![rp_cursor] = grant_count[rp_cursor] + 1]
                                       ELSE /\ TRUE
                                            /\ UNCHANGED << lock_state,
                                                            grant_count >>
                                 /\ IF lock_state'[rp_cursor] = "waiting"
                                       THEN /\ rp_needs_blast' = TRUE
                                            /\ pc' = [pc EXCEPT !["reprocessor"] = "RP_AfterScan"]
                                       ELSE /\ pc' = [pc EXCEPT !["reprocessor"] = "RP_Advance"]
                                            /\ UNCHANGED rp_needs_blast
                            ELSE /\ pc' = [pc EXCEPT !["reprocessor"] = "RP_Advance"]
                                 /\ UNCHANGED << lock_state, grant_count,
                                                 rp_needs_blast >>
                 ELSE /\ pc' = [pc EXCEPT !["reprocessor"] = "RP_AfterScan"]
                      /\ UNCHANGED << lock_state, grant_count, rp_needs_blast >>
           /\ UNCHANGED << lr_lock, holder_active, rp_phase, rp_cursor,
                           rp_erestart, w3_compat_with_waiters >>

RP_Advance == /\ pc["reprocessor"] = "RP_Advance"
              /\ rp_cursor' = rp_cursor + 1
              /\ pc' = [pc EXCEPT !["reprocessor"] = "RP_Scan"]
              /\ UNCHANGED << lr_lock, holder_active, lock_state, grant_count,
                              rp_phase, rp_needs_blast, rp_erestart,
                              w3_compat_with_waiters >>

RP_AfterScan == /\ pc["reprocessor"] = "RP_AfterScan"
                /\ IF rp_needs_blast
                      THEN /\ lr_lock' = "free"
                           /\ rp_phase' = "bl_sending"
                           /\ pc' = [pc EXCEPT !["reprocessor"] = "RP_WaitASTs"]
                      ELSE /\ lr_lock' = "free"
                           /\ rp_phase' = "done"
                           /\ pc' = [pc EXCEPT !["reprocessor"] = "RP_Done"]
                /\ UNCHANGED << holder_active, lock_state, grant_count,
                                rp_cursor, rp_needs_blast, rp_erestart,
                                w3_compat_with_waiters >>

RP_WaitASTs == /\ pc["reprocessor"] = "RP_WaitASTs"
               /\ TRUE
               /\ pc' = [pc EXCEPT !["reprocessor"] = "RP_Relock"]
               /\ UNCHANGED << lr_lock, holder_active, lock_state, grant_count,
                               rp_phase, rp_cursor, rp_needs_blast,
                               rp_erestart, w3_compat_with_waiters >>

RP_Relock == /\ pc["reprocessor"] = "RP_Relock"
             /\ lr_lock = "free"
             /\ lr_lock' = "reprocessor"
             /\ pc' = [pc EXCEPT !["reprocessor"] = "RP_CheckRestart"]
             /\ UNCHANGED << holder_active, lock_state, grant_count, rp_phase,
                             rp_cursor, rp_needs_blast, rp_erestart,
                             w3_compat_with_waiters >>

RP_CheckRestart == /\ pc["reprocessor"] = "RP_CheckRestart"
                   /\ IF rp_erestart /\ ~InjectBugNoRescan
                         THEN /\ rp_phase' = "scanning"
                              /\ rp_cursor' = 1
                              /\ rp_needs_blast' = FALSE
                              /\ rp_erestart' = FALSE
                              /\ pc' = [pc EXCEPT !["reprocessor"] = "RP_Scan"]
                         ELSE /\ pc' = [pc EXCEPT !["reprocessor"] = "RP_Finish"]
                              /\ UNCHANGED << rp_phase, rp_cursor,
                                              rp_needs_blast, rp_erestart >>
                   /\ UNCHANGED << lr_lock, holder_active, lock_state,
                                   grant_count, w3_compat_with_waiters >>

RP_Finish == /\ pc["reprocessor"] = "RP_Finish"
             /\ rp_phase' = "done"
             /\ lr_lock' = "free"
             /\ pc' = [pc EXCEPT !["reprocessor"] = "RP_Done"]
             /\ UNCHANGED << holder_active, lock_state, grant_count, rp_cursor,
                             rp_needs_blast, rp_erestart,
                             w3_compat_with_waiters >>

RP_Done == /\ pc["reprocessor"] = "RP_Done"
           /\ TRUE
           /\ pc' = [pc EXCEPT !["reprocessor"] = "Done"]
           /\ UNCHANGED << lr_lock, holder_active, lock_state, grant_count,
                           rp_phase, rp_cursor, rp_needs_blast, rp_erestart,
                           w3_compat_with_waiters >>

Reprocessor == RP_WaitReady \/ RP_Lock \/ RP_Scan \/ RP_Advance
                  \/ RP_AfterScan \/ RP_WaitASTs \/ RP_Relock
                  \/ RP_CheckRestart \/ RP_Finish \/ RP_Done

NE_Wait == /\ pc["new_enqueue"] = "NE_Wait"
           /\ ~holder_active
           /\ pc' = [pc EXCEPT !["new_enqueue"] = "NE_Lock"]
           /\ UNCHANGED << lr_lock, holder_active, lock_state, grant_count,
                           rp_phase, rp_cursor, rp_needs_blast, rp_erestart,
                           w3_compat_with_waiters >>

NE_Lock == /\ pc["new_enqueue"] = "NE_Lock"
           /\ lr_lock = "free"
           /\ lr_lock' = "new_enqueue"
           /\ pc' = [pc EXCEPT !["new_enqueue"] = "NE_Enqueue"]
           /\ UNCHANGED << holder_active, lock_state, grant_count, rp_phase,
                           rp_cursor, rp_needs_blast, rp_erestart,
                           w3_compat_with_waiters >>

NE_Enqueue == /\ pc["new_enqueue"] = "NE_Enqueue"
              /\ IF ~ConflictsWithGranted(3)
                    THEN /\ IF CompatibleMode \/ w3_compat_with_waiters
                               THEN /\ lock_state' = [lock_state EXCEPT ![3] = "granted"]
                                    /\ grant_count' = [grant_count EXCEPT ![3] = grant_count[3] + 1]
                               ELSE /\ IF ~(\E j \in 1..2 : lock_state[j] = "waiting")
                                          THEN /\ lock_state' = [lock_state EXCEPT ![3] = "granted"]
                                               /\ grant_count' = [grant_count EXCEPT ![3] = grant_count[3] + 1]
                                          ELSE /\ lock_state' = [lock_state EXCEPT ![3] = "waiting"]
                                               /\ UNCHANGED grant_count
                    ELSE /\ lock_state' = [lock_state EXCEPT ![3] = "waiting"]
                         /\ UNCHANGED grant_count
              /\ pc' = [pc EXCEPT !["new_enqueue"] = "NE_Unlock"]
              /\ UNCHANGED << lr_lock, holder_active, rp_phase, rp_cursor,
                              rp_needs_blast, rp_erestart,
                              w3_compat_with_waiters >>

NE_Unlock == /\ pc["new_enqueue"] = "NE_Unlock"
             /\ lr_lock' = "free"
             /\ IF lock_state[3] = "waiting" /\ rp_phase = "bl_sending"
                   THEN /\ TRUE
                   ELSE /\ TRUE
             /\ pc' = [pc EXCEPT !["new_enqueue"] = "Done"]
             /\ UNCHANGED << holder_active, lock_state, grant_count, rp_phase,
                             rp_cursor, rp_needs_blast, rp_erestart,
                             w3_compat_with_waiters >>

NewEnqueue == NE_Wait \/ NE_Lock \/ NE_Enqueue \/ NE_Unlock

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == CancelThread \/ Reprocessor \/ NewEnqueue
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(CancelThread)
        /\ WF_vars(Reprocessor)
        /\ WF_vars(NewEnqueue)

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

\* Liveness
EventualCompletion ==
    <>(rp_phase = "done")

=============================================================================
