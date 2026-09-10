-------------------- MODULE ldlm_recovery_reprocess --------------------
(*
 * Model: LDLM recovery reprocess iterator invalidation (LU-10841)
 *
 * Bug: During LDLM_PROCESS_RECOVERY reprocessing, the policy processor
 * drops lr_lock to send BL_ASTs via ldlm_handle_conflict_lock().  The
 * waiting queue is iterated with list_for_each_safe(tmp, pos, queue),
 * which caches the next-entry pointer (pos) at the top of each
 * iteration.  While lr_lock is dropped, another thread can cancel the
 * lock at the cached pos position, unlinking it from the list.  When
 * the loop resumes, it dereferences the stale pos pointer - crash.
 *
 * Fix (d6e9ece60a): Move BL_AST sending out of per-lock policy
 * processors.  During recovery reprocess, policy processors only
 * collect conflicting locks into an rpc_list without dropping lr_lock.
 * After the full queue iteration completes, ldlm_reprocess_queue()
 * drops lr_lock to send BL_ASTs in bulk.  On ERESTART, the entire
 * iteration restarts from scratch with a fresh iterator.
 *
 * Processes:
 *   RecoveryReprocessor - iterates waiting queue, grants or collects
 *       BL_AST work.  Bug variant drops lr_lock per-lock inside the
 *       loop.  Fix variant accumulates and sends after loop.
 *   Interferer - another thread that cancels a waiting lock during
 *       the lr_lock drop window, invalidating the cached iterator.
 *   HolderCancel - holder cancels during BL_AST window (ERESTART).
 *
 * Key invariant: NoCursorDangling - the reprocessor never accesses
 * a queue slot whose lock has been destroyed (removed from queue).
 *
 * Source (lustre-release master 47638add78):
 *   ldlm_reprocess_queue        ldlm_lock.c:1958-2020
 *     list_for_each_safe(tmp, pos, queue) 1980; RECOVERY never
 *     breaks (2000-2002); bl_ast_list accumulated 1992-1994;
 *     unlock_res 2006, ldlm_run_ast_work 2008, lock_res 2011,
 *     GOTO restart (fresh iterator) 2013
 *   __ldlm_reprocess_all        ldlm_lock.c:2383-2428 (RECOVERY
 *     intention via ldlm_reprocess_res 2436-2444 from
 *     ldlm_reprocess_recovery_done 2447-2456)
 *   ldlm_reprocess_inodebits_queue ldlm_inodebits.c:47-124
 *     (delegates RECOVERY to ldlm_reprocess_queue at 68-70)
 *   callers: target_finish_recovery ldlm_lib.c:1884-1937 (1909),
 *     ldlm_export_cancel_locks ldlm_lock.c:2661-2689 (2684)
 *   policy processors (collect BL_ASTs into work_list, no lr_lock
 *     drop): ldlm_process_plain_lock ldlm_plain.c:110-147,
 *     ldlm_process_inodebits_lock ldlm_inodebits.c:333-442,
 *     ldlm_process_extent_lock ldlm_extent.c:860-925
 *   pre-fix bug path: policy -> ldlm_handle_conflict_lock
 *     ldlm_lock.c:2036-2094 (unlock_res 2055 / lock_res 2067),
 *     now reached only from ldlm_lock_enqueue_helper 1750-1770
 *   Interferer: ldlm_lock_cancel ldlm_lock.c:2496-2538
 *     (ldlm_resource_unlink_lock 2527)
 *
 * Validated against: lustre-release master 47638add78 (2026-09-06)
 *
 * Validation notes: the d6e9ece60a structure is intact: in
 * RECOVERY intention the loop scans the whole queue under lr_lock,
 * BL_ASTs are sent once after the loop, and -ERESTART restarts
 * with a fresh list_for_each_safe.  One policy processor can still
 * drop lr_lock inside the loop: ldlm_process_flock_lock releases
 * and re-takes the resource lock around ldlm_lock_create when a
 * granted flock must be split (ldlm_flock.c:578-582).  That flock
 * path is outside this model's scope (it predates LU-10841 and was
 * not changed by it).
 *)
EXTENDS Integers, FiniteSets, Sequences, TLC

CONSTANTS
    NumWaiters,             \* Number of waiting locks (2 or 3)
    InjectBugPerLockDrop    \* TRUE = BUG: drop lr_lock per-lock inside loop
                            \* FALSE = FIX: accumulate, send after loop

ASSUME NumWaiters \in 2..3

Waiters == 1..NumWaiters

(* --algorithm ldlm_recovery_reprocess

variables
    \* ---- Resource spinlock ----
    lr_lock = "free",

    \* ---- Holder state ----
    holder_active = TRUE,

    \* ---- Waiting queue: array models the linked list ----
    \* Each entry: "waiting", "granted", "destroyed"
    queue = [i \in Waiters |-> "waiting"],

    \* ---- Reprocessor state ----
    rp_cursor = 0,            \* current position in iteration
    rp_cached_next = 0,       \* cached next-entry pointer (list_for_each_safe pos)
    rp_phase = "idle",        \* idle, scanning, bl_dropping, bl_sending, done
    rp_bl_list = {},          \* accumulated BL_AST work (fix path)
    rp_needs_blast = FALSE,   \* current lock needs BL_AST (bug path)
    erestart = FALSE,

    \* ---- Tracking for invariants ----
    stale_access = FALSE,     \* TRUE if reprocessor accessed a destroyed slot
    grant_count = [i \in Waiters |-> 0];

define
    IsGranted(i) == queue[i] = "granted"
    IsWaiting(i) == queue[i] = "waiting"
    IsDestroyed(i) == queue[i] = "destroyed"
    GrantedCount == Cardinality({i \in Waiters : IsGranted(i)})
    WaitingCount == Cardinality({i \in Waiters : IsWaiting(i)})
    DestroyedCount == Cardinality({i \in Waiters : IsDestroyed(i)})

    \* ========== SAFETY INVARIANTS ==========

    \* Core bug detector: reprocessor never accessed a destroyed slot
    NoCursorDangling == ~stale_access

    \* No lock granted more than once
    NoDoubleGrant == \A i \in Waiters : grant_count[i] <= 1

    \* No grants while holder is active
    NoGrantWhileHeld == holder_active => GrantedCount = 0

    \* At most one EX granted (all waiters are EX in this model)
    GrantedExclusive == ~holder_active => GrantedCount <= 1

    \* Terminal: when all processes done and holder gone, no waiter
    \* should remain that could have been granted.
    \* Account for destroyed locks: the interferer can destroy a lock,
    \* so we check that remaining waiters are blocked by a grant.
    NoStuckWaiter ==
        (pc["reprocessor"] = "Done"
         /\ pc["interferer"] = "Done"
         /\ pc["holder_cancel"] = "Done"
         /\ ~holder_active) =>
            \* No waiting lock should remain grantable
            ~(\E i \in Waiters :
                queue[i] = "waiting"
                /\ ~(\E j \in Waiters : j /= i /\ IsGranted(j)))

    TypeOK ==
        /\ \A i \in Waiters : queue[i] \in {"waiting", "granted", "destroyed"}
        /\ \A i \in Waiters : grant_count[i] \in 0..3
        /\ rp_cursor \in 0..(NumWaiters+1)
        /\ rp_cached_next \in 0..(NumWaiters+1)
end define;

macro TryGrant(i) begin
    if ~holder_active
       /\ queue[i] = "waiting"
       /\ ~(\E j \in Waiters : j /= i /\ IsGranted(j)) then
        queue[i] := "granted";
        grant_count[i] := grant_count[i] + 1;
    end if;
end macro;

\* ================================================================
\* HolderCancel: Holder cancels during BL_AST window.
\* Triggers ERESTART.
\* ================================================================
fair process HolderCancel = "holder_cancel"
begin
HC_Wait:
    await rp_phase = "bl_sending" \/ rp_phase = "bl_dropping";

HC_Lock:
    await lr_lock = "free";
    lr_lock := "holder_cancel";

HC_Cancel:
    holder_active := FALSE;
    erestart := TRUE;
    lr_lock := "free";
end process;

\* ================================================================
\* Interferer: Another thread cancels a waiting lock during the
\* lr_lock drop window.  This is the thread that invalidates the
\* cached iterator.
\*
\* Models: BL_AST callback -> ldlm_lock_cancel (ldlm_lock.c:2496-2538,
\* ldlm_resource_unlink_lock at 2527) -> list_del on a
\* waiting lock that happens to be the cached pos pointer.
\* ================================================================
fair process Interferer = "interferer"
begin
IF_Wait:
    \* Wait for lr_lock to be dropped (BL_AST window)
    await rp_phase = "bl_sending" \/ rp_phase = "bl_dropping";

IF_Lock:
    await lr_lock = "free";
    lr_lock := "interferer";

IF_Cancel:
    \* Cancel the lock at position rp_cached_next (if valid and waiting).
    \* This is the exact scenario: the cached next pointer is invalidated.
    if rp_cached_next >= 1 /\ rp_cached_next <= NumWaiters then
        if queue[rp_cached_next] = "waiting" then
            queue[rp_cached_next] := "destroyed";
        end if;
    end if;
    lr_lock := "free";
end process;

\* ================================================================
\* RecoveryReprocessor: Iterates waiting queue under lr_lock.
\*
\* Bug path (InjectBugPerLockDrop = TRUE):
\*   For each waiting lock, if conflict -> drop lr_lock to send
\*   BL_AST, then resume iteration using cached_next.
\*   BUG: cached_next may point to a destroyed entry.
\*
\* Fix path (InjectBugPerLockDrop = FALSE):
\*   Iterate entire queue under lr_lock, collecting BL_AST work.
\*   After loop, drop lr_lock to send BL_ASTs in bulk.
\*   On ERESTART, restart entire iteration from scratch.
\* ================================================================
fair process RecoveryReprocessor = "reprocessor"
begin
RP_Start:
    await lr_lock = "free";
    lr_lock := "reprocessor";
    rp_phase := "scanning";
    rp_cursor := 1;
    rp_cached_next := 2;
    rp_bl_list := {};
    rp_needs_blast := FALSE;
    erestart := FALSE;

RP_Scan:
    if rp_cursor <= NumWaiters then
        \* Check for stale access: are we reading a destroyed slot?
        if queue[rp_cursor] = "destroyed" then
            \* This is the stale iterator dereference!
            stale_access := TRUE;
        end if;

        if queue[rp_cursor] = "waiting" then
            TryGrant(rp_cursor);
            if queue[rp_cursor] = "waiting" then
                \* Conflict remains - need BL_ASTs
                if InjectBugPerLockDrop then
                    \* BUG PATH: drop lr_lock now, per-lock
                    rp_needs_blast := TRUE;
                    \* Cache next before dropping lock
                    if rp_cursor < NumWaiters then
                        rp_cached_next := rp_cursor + 1;
                    else
                        rp_cached_next := NumWaiters + 1;
                    end if;
                    goto RP_BugDrop;
                else
                    \* FIX PATH: accumulate, continue iteration
                    rp_bl_list := rp_bl_list \union {rp_cursor};
                end if;
            end if;
        end if;
RP_Advance:
        \* Advance cursor
        rp_cursor := rp_cursor + 1;
        if rp_cursor <= NumWaiters then
            rp_cached_next := rp_cursor + 1;
        else
            rp_cached_next := NumWaiters + 1;
        end if;
        goto RP_Scan;
    end if;

RP_AfterScan:
    \* End of iteration - fix path sends accumulated BL_ASTs
    if ~InjectBugPerLockDrop /\ rp_bl_list /= {} then
        lr_lock := "free";
        rp_phase := "bl_sending";
        goto RP_FixWaitASTs;
    end if;

RP_Finish:
    rp_phase := "done";
    lr_lock := "free";
    goto RP_Done;

\* ---- Bug path: per-lock lr_lock drop ----
RP_BugDrop:
    \* Drop lr_lock to send BL_AST for current lock
    lr_lock := "free";
    rp_phase := "bl_dropping";

RP_BugWaitASTs:
    \* BL_AST completion window - interferer and holder_cancel run here
    skip;

RP_BugRelock:
    await lr_lock = "free";
    lr_lock := "reprocessor";
    rp_phase := "scanning";

RP_BugCheckRestart:
    if erestart then
        \* Even in bug path, ERESTART restarts from beginning
        rp_cursor := 1;
        rp_cached_next := 2;
        erestart := FALSE;
        goto RP_Scan;
    end if;

RP_BugResume:
    \* Resume iteration from cached_next - THIS IS THE BUG
    \* cached_next may point to a destroyed entry
    rp_cursor := rp_cached_next;
    if rp_cursor <= NumWaiters then
        rp_cached_next := rp_cursor + 1;
    end if;
    goto RP_Scan;

\* ---- Fix path: bulk BL_AST send after loop ----
RP_FixWaitASTs:
    \* BL_AST completion window
    skip;

RP_FixRelock:
    await lr_lock = "free";
    lr_lock := "reprocessor";

RP_FixCheckRestart:
    if erestart then
        \* FIX: restart entire iteration from scratch - fresh iterator
        rp_phase := "scanning";
        rp_cursor := 1;
        rp_cached_next := 2;
        rp_bl_list := {};
        erestart := FALSE;
        goto RP_Scan;
    else
        \* No restart needed, done
        goto RP_Finish;
    end if;

RP_Done:
    skip;
end process;

end algorithm; *)
\* BEGIN TRANSLATION
VARIABLES lr_lock, holder_active, queue, rp_cursor, rp_cached_next, rp_phase,
          rp_bl_list, rp_needs_blast, erestart, stale_access, grant_count, pc

(* define statement *)
IsGranted(i) == queue[i] = "granted"
IsWaiting(i) == queue[i] = "waiting"
IsDestroyed(i) == queue[i] = "destroyed"
GrantedCount == Cardinality({i \in Waiters : IsGranted(i)})
WaitingCount == Cardinality({i \in Waiters : IsWaiting(i)})
DestroyedCount == Cardinality({i \in Waiters : IsDestroyed(i)})




NoCursorDangling == ~stale_access


NoDoubleGrant == \A i \in Waiters : grant_count[i] <= 1


NoGrantWhileHeld == holder_active => GrantedCount = 0


GrantedExclusive == ~holder_active => GrantedCount <= 1





NoStuckWaiter ==
    (pc["reprocessor"] = "Done"
     /\ pc["interferer"] = "Done"
     /\ pc["holder_cancel"] = "Done"
     /\ ~holder_active) =>

        ~(\E i \in Waiters :
            queue[i] = "waiting"
            /\ ~(\E j \in Waiters : j /= i /\ IsGranted(j)))

TypeOK ==
    /\ \A i \in Waiters : queue[i] \in {"waiting", "granted", "destroyed"}
    /\ \A i \in Waiters : grant_count[i] \in 0..3
    /\ rp_cursor \in 0..(NumWaiters+1)
    /\ rp_cached_next \in 0..(NumWaiters+1)


vars == << lr_lock, holder_active, queue, rp_cursor, rp_cached_next, rp_phase,
           rp_bl_list, rp_needs_blast, erestart, stale_access, grant_count,
           pc >>

ProcSet == {"holder_cancel"} \cup {"interferer"} \cup {"reprocessor"}

Init == (* Global variables *)
        /\ lr_lock = "free"
        /\ holder_active = TRUE
        /\ queue = [i \in Waiters |-> "waiting"]
        /\ rp_cursor = 0
        /\ rp_cached_next = 0
        /\ rp_phase = "idle"
        /\ rp_bl_list = {}
        /\ rp_needs_blast = FALSE
        /\ erestart = FALSE
        /\ stale_access = FALSE
        /\ grant_count = [i \in Waiters |-> 0]
        /\ pc = [self \in ProcSet |-> CASE self = "holder_cancel" -> "HC_Wait"
                                        [] self = "interferer" -> "IF_Wait"
                                        [] self = "reprocessor" -> "RP_Start"]

HC_Wait == /\ pc["holder_cancel"] = "HC_Wait"
           /\ rp_phase = "bl_sending" \/ rp_phase = "bl_dropping"
           /\ pc' = [pc EXCEPT !["holder_cancel"] = "HC_Lock"]
           /\ UNCHANGED << lr_lock, holder_active, queue, rp_cursor,
                           rp_cached_next, rp_phase, rp_bl_list,
                           rp_needs_blast, erestart, stale_access, grant_count >>

HC_Lock == /\ pc["holder_cancel"] = "HC_Lock"
           /\ lr_lock = "free"
           /\ lr_lock' = "holder_cancel"
           /\ pc' = [pc EXCEPT !["holder_cancel"] = "HC_Cancel"]
           /\ UNCHANGED << holder_active, queue, rp_cursor, rp_cached_next,
                           rp_phase, rp_bl_list, rp_needs_blast, erestart,
                           stale_access, grant_count >>

HC_Cancel == /\ pc["holder_cancel"] = "HC_Cancel"
             /\ holder_active' = FALSE
             /\ erestart' = TRUE
             /\ lr_lock' = "free"
             /\ pc' = [pc EXCEPT !["holder_cancel"] = "Done"]
             /\ UNCHANGED << queue, rp_cursor, rp_cached_next, rp_phase,
                             rp_bl_list, rp_needs_blast, stale_access,
                             grant_count >>

HolderCancel == HC_Wait \/ HC_Lock \/ HC_Cancel

IF_Wait == /\ pc["interferer"] = "IF_Wait"
           /\ rp_phase = "bl_sending" \/ rp_phase = "bl_dropping"
           /\ pc' = [pc EXCEPT !["interferer"] = "IF_Lock"]
           /\ UNCHANGED << lr_lock, holder_active, queue, rp_cursor,
                           rp_cached_next, rp_phase, rp_bl_list,
                           rp_needs_blast, erestart, stale_access, grant_count >>

IF_Lock == /\ pc["interferer"] = "IF_Lock"
           /\ lr_lock = "free"
           /\ lr_lock' = "interferer"
           /\ pc' = [pc EXCEPT !["interferer"] = "IF_Cancel"]
           /\ UNCHANGED << holder_active, queue, rp_cursor, rp_cached_next,
                           rp_phase, rp_bl_list, rp_needs_blast, erestart,
                           stale_access, grant_count >>

IF_Cancel == /\ pc["interferer"] = "IF_Cancel"
             /\ IF rp_cached_next >= 1 /\ rp_cached_next <= NumWaiters
                   THEN /\ IF queue[rp_cached_next] = "waiting"
                              THEN /\ queue' = [queue EXCEPT ![rp_cached_next] = "destroyed"]
                              ELSE /\ TRUE
                                   /\ queue' = queue
                   ELSE /\ TRUE
                        /\ queue' = queue
             /\ lr_lock' = "free"
             /\ pc' = [pc EXCEPT !["interferer"] = "Done"]
             /\ UNCHANGED << holder_active, rp_cursor, rp_cached_next,
                             rp_phase, rp_bl_list, rp_needs_blast, erestart,
                             stale_access, grant_count >>

Interferer == IF_Wait \/ IF_Lock \/ IF_Cancel

RP_Start == /\ pc["reprocessor"] = "RP_Start"
            /\ lr_lock = "free"
            /\ lr_lock' = "reprocessor"
            /\ rp_phase' = "scanning"
            /\ rp_cursor' = 1
            /\ rp_cached_next' = 2
            /\ rp_bl_list' = {}
            /\ rp_needs_blast' = FALSE
            /\ erestart' = FALSE
            /\ pc' = [pc EXCEPT !["reprocessor"] = "RP_Scan"]
            /\ UNCHANGED << holder_active, queue, stale_access, grant_count >>

RP_Scan == /\ pc["reprocessor"] = "RP_Scan"
           /\ IF rp_cursor <= NumWaiters
                 THEN /\ IF queue[rp_cursor] = "destroyed"
                            THEN /\ stale_access' = TRUE
                            ELSE /\ TRUE
                                 /\ UNCHANGED stale_access
                      /\ IF queue[rp_cursor] = "waiting"
                            THEN /\ IF ~holder_active
                                       /\ queue[rp_cursor] = "waiting"
                                       /\ ~(\E j \in Waiters : j /= rp_cursor /\ IsGranted(j))
                                       THEN /\ queue' = [queue EXCEPT ![rp_cursor] = "granted"]
                                            /\ grant_count' = [grant_count EXCEPT ![rp_cursor] = grant_count[rp_cursor] + 1]
                                       ELSE /\ TRUE
                                            /\ UNCHANGED << queue, grant_count >>
                                 /\ IF queue'[rp_cursor] = "waiting"
                                       THEN /\ IF InjectBugPerLockDrop
                                                  THEN /\ rp_needs_blast' = TRUE
                                                       /\ IF rp_cursor < NumWaiters
                                                             THEN /\ rp_cached_next' = rp_cursor + 1
                                                             ELSE /\ rp_cached_next' = NumWaiters + 1
                                                       /\ pc' = [pc EXCEPT !["reprocessor"] = "RP_BugDrop"]
                                                       /\ UNCHANGED rp_bl_list
                                                  ELSE /\ rp_bl_list' = (rp_bl_list \union {rp_cursor})
                                                       /\ pc' = [pc EXCEPT !["reprocessor"] = "RP_Advance"]
                                                       /\ UNCHANGED << rp_cached_next,
                                                                       rp_needs_blast >>
                                       ELSE /\ pc' = [pc EXCEPT !["reprocessor"] = "RP_Advance"]
                                            /\ UNCHANGED << rp_cached_next,
                                                            rp_bl_list,
                                                            rp_needs_blast >>
                            ELSE /\ pc' = [pc EXCEPT !["reprocessor"] = "RP_Advance"]
                                 /\ UNCHANGED << queue, rp_cached_next,
                                                 rp_bl_list, rp_needs_blast,
                                                 grant_count >>
                 ELSE /\ pc' = [pc EXCEPT !["reprocessor"] = "RP_AfterScan"]
                      /\ UNCHANGED << queue, rp_cached_next, rp_bl_list,
                                      rp_needs_blast, stale_access,
                                      grant_count >>
           /\ UNCHANGED << lr_lock, holder_active, rp_cursor, rp_phase,
                           erestart >>

RP_Advance == /\ pc["reprocessor"] = "RP_Advance"
              /\ rp_cursor' = rp_cursor + 1
              /\ IF rp_cursor' <= NumWaiters
                    THEN /\ rp_cached_next' = rp_cursor' + 1
                    ELSE /\ rp_cached_next' = NumWaiters + 1
              /\ pc' = [pc EXCEPT !["reprocessor"] = "RP_Scan"]
              /\ UNCHANGED << lr_lock, holder_active, queue, rp_phase,
                              rp_bl_list, rp_needs_blast, erestart,
                              stale_access, grant_count >>

RP_AfterScan == /\ pc["reprocessor"] = "RP_AfterScan"
                /\ IF ~InjectBugPerLockDrop /\ rp_bl_list /= {}
                      THEN /\ lr_lock' = "free"
                           /\ rp_phase' = "bl_sending"
                           /\ pc' = [pc EXCEPT !["reprocessor"] = "RP_FixWaitASTs"]
                      ELSE /\ pc' = [pc EXCEPT !["reprocessor"] = "RP_Finish"]
                           /\ UNCHANGED << lr_lock, rp_phase >>
                /\ UNCHANGED << holder_active, queue, rp_cursor,
                                rp_cached_next, rp_bl_list, rp_needs_blast,
                                erestart, stale_access, grant_count >>

RP_Finish == /\ pc["reprocessor"] = "RP_Finish"
             /\ rp_phase' = "done"
             /\ lr_lock' = "free"
             /\ pc' = [pc EXCEPT !["reprocessor"] = "RP_Done"]
             /\ UNCHANGED << holder_active, queue, rp_cursor, rp_cached_next,
                             rp_bl_list, rp_needs_blast, erestart,
                             stale_access, grant_count >>

RP_BugDrop == /\ pc["reprocessor"] = "RP_BugDrop"
              /\ lr_lock' = "free"
              /\ rp_phase' = "bl_dropping"
              /\ pc' = [pc EXCEPT !["reprocessor"] = "RP_BugWaitASTs"]
              /\ UNCHANGED << holder_active, queue, rp_cursor, rp_cached_next,
                              rp_bl_list, rp_needs_blast, erestart,
                              stale_access, grant_count >>

RP_BugWaitASTs == /\ pc["reprocessor"] = "RP_BugWaitASTs"
                  /\ TRUE
                  /\ pc' = [pc EXCEPT !["reprocessor"] = "RP_BugRelock"]
                  /\ UNCHANGED << lr_lock, holder_active, queue, rp_cursor,
                                  rp_cached_next, rp_phase, rp_bl_list,
                                  rp_needs_blast, erestart, stale_access,
                                  grant_count >>

RP_BugRelock == /\ pc["reprocessor"] = "RP_BugRelock"
                /\ lr_lock = "free"
                /\ lr_lock' = "reprocessor"
                /\ rp_phase' = "scanning"
                /\ pc' = [pc EXCEPT !["reprocessor"] = "RP_BugCheckRestart"]
                /\ UNCHANGED << holder_active, queue, rp_cursor,
                                rp_cached_next, rp_bl_list, rp_needs_blast,
                                erestart, stale_access, grant_count >>

RP_BugCheckRestart == /\ pc["reprocessor"] = "RP_BugCheckRestart"
                      /\ IF erestart
                            THEN /\ rp_cursor' = 1
                                 /\ rp_cached_next' = 2
                                 /\ erestart' = FALSE
                                 /\ pc' = [pc EXCEPT !["reprocessor"] = "RP_Scan"]
                            ELSE /\ pc' = [pc EXCEPT !["reprocessor"] = "RP_BugResume"]
                                 /\ UNCHANGED << rp_cursor, rp_cached_next,
                                                 erestart >>
                      /\ UNCHANGED << lr_lock, holder_active, queue, rp_phase,
                                      rp_bl_list, rp_needs_blast, stale_access,
                                      grant_count >>

RP_BugResume == /\ pc["reprocessor"] = "RP_BugResume"
                /\ rp_cursor' = rp_cached_next
                /\ IF rp_cursor' <= NumWaiters
                      THEN /\ rp_cached_next' = rp_cursor' + 1
                      ELSE /\ TRUE
                           /\ UNCHANGED rp_cached_next
                /\ pc' = [pc EXCEPT !["reprocessor"] = "RP_Scan"]
                /\ UNCHANGED << lr_lock, holder_active, queue, rp_phase,
                                rp_bl_list, rp_needs_blast, erestart,
                                stale_access, grant_count >>

RP_FixWaitASTs == /\ pc["reprocessor"] = "RP_FixWaitASTs"
                  /\ TRUE
                  /\ pc' = [pc EXCEPT !["reprocessor"] = "RP_FixRelock"]
                  /\ UNCHANGED << lr_lock, holder_active, queue, rp_cursor,
                                  rp_cached_next, rp_phase, rp_bl_list,
                                  rp_needs_blast, erestart, stale_access,
                                  grant_count >>

RP_FixRelock == /\ pc["reprocessor"] = "RP_FixRelock"
                /\ lr_lock = "free"
                /\ lr_lock' = "reprocessor"
                /\ pc' = [pc EXCEPT !["reprocessor"] = "RP_FixCheckRestart"]
                /\ UNCHANGED << holder_active, queue, rp_cursor,
                                rp_cached_next, rp_phase, rp_bl_list,
                                rp_needs_blast, erestart, stale_access,
                                grant_count >>

RP_FixCheckRestart == /\ pc["reprocessor"] = "RP_FixCheckRestart"
                      /\ IF erestart
                            THEN /\ rp_phase' = "scanning"
                                 /\ rp_cursor' = 1
                                 /\ rp_cached_next' = 2
                                 /\ rp_bl_list' = {}
                                 /\ erestart' = FALSE
                                 /\ pc' = [pc EXCEPT !["reprocessor"] = "RP_Scan"]
                            ELSE /\ pc' = [pc EXCEPT !["reprocessor"] = "RP_Finish"]
                                 /\ UNCHANGED << rp_cursor, rp_cached_next,
                                                 rp_phase, rp_bl_list,
                                                 erestart >>
                      /\ UNCHANGED << lr_lock, holder_active, queue,
                                      rp_needs_blast, stale_access,
                                      grant_count >>

RP_Done == /\ pc["reprocessor"] = "RP_Done"
           /\ TRUE
           /\ pc' = [pc EXCEPT !["reprocessor"] = "Done"]
           /\ UNCHANGED << lr_lock, holder_active, queue, rp_cursor,
                           rp_cached_next, rp_phase, rp_bl_list,
                           rp_needs_blast, erestart, stale_access, grant_count >>

RecoveryReprocessor == RP_Start \/ RP_Scan \/ RP_Advance \/ RP_AfterScan
                          \/ RP_Finish \/ RP_BugDrop \/ RP_BugWaitASTs
                          \/ RP_BugRelock \/ RP_BugCheckRestart
                          \/ RP_BugResume \/ RP_FixWaitASTs \/ RP_FixRelock
                          \/ RP_FixCheckRestart \/ RP_Done

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == HolderCancel \/ Interferer \/ RecoveryReprocessor
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(HolderCancel)
        /\ WF_vars(Interferer)
        /\ WF_vars(RecoveryReprocessor)

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

\* Liveness: reprocessing eventually completes
EventualCompletion ==
    <>(rp_phase = "done")

=============================================================================
