---------------------------- MODULE ldlm_lock_order_audit ----------------------------
(*
 * Model: LDLM lock-ordering audit -- systematic check of all main code paths
 *
 * Encodes the documented LDLM lock ordering from lustre/include/lustre_dlm.h
 * (lines 185-202) and checks that all major code paths respect it.
 *
 * Documented ordering (lustre_dlm.h):
 *   lr_lock > waiting_locks_spinlock    (res before waiting)
 *   lr_lock > led_lock                  (res before led)
 *   lr_lock > ns_lock                   (res before namespace)
 *   lr_lvb_mutex > lr_lock              (lvb before res)
 *   res_lock > exp_bl_list_lock > waiting_locks_spinlock
 *
 * This model focuses on the four main spinlocks involved in deadlocks:
 *   ns_lock, res_lock (lr_lock), exp_bl_list_lock, waiting_locks_spinlock
 *
 * Five concurrent processes model the major LDLM code paths:
 *   ConvertThread:   ldlm_cli_inodebits_convert (ldlm_inodebits.c:501-603)
 *   CancelThread:    ldlm_prepare_lru_list + ldlm_cli_cancel_local (ldlm_request.c)
 *   BLASTCallback:   ldlm_handle_bl_callback (ldlm_lockd.c:1900-1936)
 *   ReprocessThread: ldlm_reprocess_queue (ldlm_lock.c:1958-2020)
 *   EnqueueThread:   ldlm_handle_conflict_lock (ldlm_lock.c:2036-2094)
 *
 * Lock acquisition sequences (from source reading):
 *
 *   ConvertThread:
 *     1. res_lock (caller holds via lock_res_and_lock, line 512)
 *     2. DROP res_lock for blocking_ast callback (line 556)
 *     3. Reacquire res_lock (line 560)
 *     4. ns_lock (line 590, for LRU add -- while holding res_lock)
 *     Order: res_lock -> ns_lock  (with drop/reacquire window)
 *
 *   CancelThread (LRU cancel):
 *     1. ns_lock (line 2157, ldlm_prepare_lru_list scans LRU)
 *     2. DROP ns_lock (line 2178)
 *     3. res_lock (line 2221, lock_res_and_lock for flag check)
 *     4. DROP res_lock (line 2274)
 *     Order: ns_lock -> res_lock  (sequential, not nested)
 *     NOTE: In current code ns_lock is dropped before res_lock acquired,
 *           so no true nesting. Bug injection models the case where they
 *           are held simultaneously.
 *
 *   BLASTCallback:
 *     1. res_lock (line 1909, lock_res_and_lock)
 *     2. DROP res_lock (line 1916)
 *     3. blocking_ast callback (no locks held)
 *     Order: res_lock only (no nesting)
 *
 *   ReprocessThread:
 *     1. res_lock (caller holds, line 1956 "Must be called with resource lock held")
 *     2. DROP res_lock (line 2006, for bl_ast work)
 *     3. Reacquire res_lock (line 2011)
 *     Order: res_lock only (with drop/reacquire window)
 *
 *   EnqueueThread:
 *     1. res_lock (caller holds, line 2044 check_res_locked)
 *     2. DROP res_lock (line 2055, unlock_res for bl_ast RPCs)
 *     3. Reacquire res_lock (line 2067, lock_res)
 *     Order: res_lock only (with drop/reacquire window)
 *
 *   WaitingLockThread (server-side):
 *     1. waiting_locks_spinlock (line 460)
 *     2. No other locks taken while holding it
 *     But ldlm_del_waiting_lock (line 550-558):
 *       waiting_locks_spinlock -> exp_bl_list_lock (sequential)
 *     And documented: res_lock > exp_bl_list_lock > waiting_locks_spinlock
 *
 * Bug injections:
 *   InjectBugConvertNsNested = TRUE:
 *     Convert acquires ns_lock while still holding res_lock (the actual
 *     code at line 590 does this). If another path holds ns_lock and
 *     wants res_lock, deadlock occurs.
 *
 *   InjectBugCancelNested = TRUE:
 *     Cancel holds ns_lock while acquiring res_lock (simulates a bug
 *     where the drop at line 2178 is missing). Combined with convert's
 *     res_lock->ns_lock this creates a classic AB/BA deadlock.
 *
 *   InjectBugWaitExpNested = TRUE:
 *     Waiting-lock thread acquires exp_bl_list_lock while holding
 *     waiting_locks_spinlock, then tries res_lock. Violates the
 *     documented res > exp_bl > waiting order.
 *
 * Safety invariants:
 *   NoLockOrderInversion: At no reachable state does any thread hold a
 *     lower-ranked lock while waiting for a higher-ranked lock.
 *   NoDeadlock: No cycle exists in the wait-for graph (pairwise check).
 *   TypeOK: Type correctness for all variables.
 *
 * The model reproduces the PR #14 ns_lock/res_lock inversion when
 * InjectBugConvertNsNested=TRUE and InjectBugCancelNested=TRUE.
 *
 * IMPORTANT: Lock acquisition is split into two atomic steps (Wait + Grab)
 * so that the "waiting" state is observable for deadlock detection.
 *
 * Validated against: lustre-release master 47638add78 (2026-09-06)
 *
 * Validation notes: line refs refreshed (ldlm_prepare_lru_list is
 * now ldlm_request.c:2103-2285; ldlm_reprocess_queue and
 * ldlm_handle_conflict_lock shifted by one line); the convert,
 * bl_callback and waiting-lock refs were already exact and the
 * lustre_dlm.h ordering block is unchanged at 185-202.  Two places
 * where the real code nests more than the model does, both in the
 * documented direction: the EnqueueThread path takes
 * waiting_locks_spinlock under lr_lock (ldlm_server_blocking_ast
 * ldlm_lockd.c:931/974 -> ldlm_add_waiting_lock 460) rather than
 * after dropping it, and the LRU cancel path takes ns_lock under
 * lr_lock in ldlm_lock_remove_from_lru_check (ldlm_lock.c:255-281,
 * called at ldlm_request.c:2224).  Neither changes any invariant.
 *)

EXTENDS Integers, FiniteSets, TLC

CONSTANTS
    InjectBugConvertNsNested,   \* TRUE = convert takes ns_lock while holding res_lock
    InjectBugCancelNested,      \* TRUE = cancel holds ns_lock while taking res_lock
    InjectBugWaitExpNested      \* TRUE = waiting-lock thread violates res>exp>waiting order

\* Lock identifiers
LOCKS == {"res_lock", "ns_lock", "exp_bl_list_lock", "waiting_spinlock"}

\* Intended ordering: maps each lock to its rank (higher = acquired first)
LockRank == [
    res_lock         |-> 4,
    ns_lock          |-> 2,
    exp_bl_list_lock |-> 2,
    waiting_spinlock |-> 1
]

\* Process identifiers
Procs == {"convert", "cancel", "blast", "reprocess", "enqueue"}

VARIABLES
    res_lock,           \* "free" or owner process name
    ns_lock,            \* "free" or owner process name
    exp_bl_lock,        \* "free" or owner process name
    waiting_spinlock,   \* "free" or owner process name
    held,               \* [Procs -> SUBSET LOCKS] -- currently held locks per process
    waiting_for,        \* [Procs -> {"none"} \cup LOCKS] -- what each process waits for
    pc                  \* [Procs -> String] -- program counter per process

vars == << res_lock, ns_lock, exp_bl_lock, waiting_spinlock,
           held, waiting_for, pc >>

\* =====================================================================
\* Helper: map lock name to lock variable value
\* =====================================================================
LockVar(lock) ==
    CASE lock = "res_lock" -> res_lock
      [] lock = "ns_lock" -> ns_lock
      [] lock = "exp_bl_list_lock" -> exp_bl_lock
      [] lock = "waiting_spinlock" -> waiting_spinlock

\* =====================================================================
\* Init
\* =====================================================================

Init ==
    /\ res_lock = "free"
    /\ ns_lock = "free"
    /\ exp_bl_lock = "free"
    /\ waiting_spinlock = "free"
    /\ held = [p \in Procs |-> {}]
    /\ waiting_for = [p \in Procs |-> "none"]
    /\ pc = [p \in Procs |->
                CASE p = "convert"   -> "CV_WaitRes"
                  [] p = "cancel"    -> "CN_WaitNs"
                  [] p = "blast"     -> "BL_WaitRes"
                  [] p = "reprocess" -> "RP_WaitRes"
                  [] p = "enqueue"   -> "EN_WaitRes"]

\* =====================================================================
\* ConvertThread -- ldlm_cli_inodebits_convert (ldlm_inodebits.c:501-603)
\*
\* Path: res_lock -> drop -> callback -> res_lock -> ns_lock -> done
\* The ns_lock at line 590 while holding res_lock is the key inversion.
\* =====================================================================

\* Step 1: Declare intent to acquire res_lock
CV_WaitRes ==
    /\ pc["convert"] = "CV_WaitRes"
    /\ waiting_for' = [waiting_for EXCEPT !["convert"] = "res_lock"]
    /\ pc' = [pc EXCEPT !["convert"] = "CV_GrabRes"]
    /\ UNCHANGED << res_lock, ns_lock, exp_bl_lock, waiting_spinlock, held >>

\* Step 2: Acquire res_lock when free
CV_GrabRes ==
    /\ pc["convert"] = "CV_GrabRes"
    /\ res_lock = "free"
    /\ res_lock' = "convert"
    /\ held' = [held EXCEPT !["convert"] = held["convert"] \union {"res_lock"}]
    /\ waiting_for' = [waiting_for EXCEPT !["convert"] = "none"]
    /\ pc' = [pc EXCEPT !["convert"] = "CV_DropRes"]
    /\ UNCHANGED << ns_lock, exp_bl_lock, waiting_spinlock >>

\* Step 3: Drop res_lock for blocking_ast callback (line 556)
CV_DropRes ==
    /\ pc["convert"] = "CV_DropRes"
    /\ res_lock' = "free"
    /\ held' = [held EXCEPT !["convert"] = held["convert"] \ {"res_lock"}]
    /\ pc' = [pc EXCEPT !["convert"] = "CV_Callback"]
    /\ UNCHANGED << ns_lock, exp_bl_lock, waiting_spinlock, waiting_for >>

\* Step 4: blocking_ast callback with no locks held
CV_Callback ==
    /\ pc["convert"] = "CV_Callback"
    /\ pc' = [pc EXCEPT !["convert"] = "CV_WaitRes2"]
    /\ UNCHANGED << res_lock, ns_lock, exp_bl_lock, waiting_spinlock, held, waiting_for >>

\* Step 5: Declare intent to reacquire res_lock (line 560)
CV_WaitRes2 ==
    /\ pc["convert"] = "CV_WaitRes2"
    /\ waiting_for' = [waiting_for EXCEPT !["convert"] = "res_lock"]
    /\ pc' = [pc EXCEPT !["convert"] = "CV_GrabRes2"]
    /\ UNCHANGED << res_lock, ns_lock, exp_bl_lock, waiting_spinlock, held >>

\* Step 6: Reacquire res_lock
CV_GrabRes2 ==
    /\ pc["convert"] = "CV_GrabRes2"
    /\ res_lock = "free"
    /\ res_lock' = "convert"
    /\ held' = [held EXCEPT !["convert"] = held["convert"] \union {"res_lock"}]
    /\ waiting_for' = [waiting_for EXCEPT !["convert"] = "none"]
    /\ pc' = [pc EXCEPT !["convert"] = "CV_PreNsLock"]
    /\ UNCHANGED << ns_lock, exp_bl_lock, waiting_spinlock >>

\* Step 7: Prepare for ns_lock acquisition (maybe release res_lock first)
CV_PreNsLock ==
    /\ pc["convert"] = "CV_PreNsLock"
    /\ IF InjectBugConvertNsNested
       THEN \* BUG: keep res_lock, proceed to wait for ns_lock
            /\ pc' = [pc EXCEPT !["convert"] = "CV_WaitNs"]
            /\ UNCHANGED << res_lock, ns_lock, exp_bl_lock, waiting_spinlock, held, waiting_for >>
       ELSE \* FIX: release res_lock before taking ns_lock
            /\ res_lock' = "free"
            /\ held' = [held EXCEPT !["convert"] = held["convert"] \ {"res_lock"}]
            /\ pc' = [pc EXCEPT !["convert"] = "CV_WaitNs"]
            /\ UNCHANGED << ns_lock, exp_bl_lock, waiting_spinlock, waiting_for >>

\* Step 8: Declare intent to acquire ns_lock
CV_WaitNs ==
    /\ pc["convert"] = "CV_WaitNs"
    /\ waiting_for' = [waiting_for EXCEPT !["convert"] = "ns_lock"]
    /\ pc' = [pc EXCEPT !["convert"] = "CV_GrabNs"]
    /\ UNCHANGED << res_lock, ns_lock, exp_bl_lock, waiting_spinlock, held >>

\* Step 9: Acquire ns_lock for LRU add (line 590)
CV_GrabNs ==
    /\ pc["convert"] = "CV_GrabNs"
    /\ ns_lock = "free"
    /\ ns_lock' = "convert"
    /\ held' = [held EXCEPT !["convert"] = held["convert"] \union {"ns_lock"}]
    /\ waiting_for' = [waiting_for EXCEPT !["convert"] = "none"]
    /\ pc' = [pc EXCEPT !["convert"] = "CV_ReleaseNs"]
    /\ UNCHANGED << res_lock, exp_bl_lock, waiting_spinlock >>

\* Step 10: Release ns_lock (line 593)
CV_ReleaseNs ==
    /\ pc["convert"] = "CV_ReleaseNs"
    /\ ns_lock' = "free"
    /\ held' = [held EXCEPT !["convert"] = held["convert"] \ {"ns_lock"}]
    /\ pc' = [pc EXCEPT !["convert"] = "CV_FinalRelease"]
    /\ UNCHANGED << res_lock, exp_bl_lock, waiting_spinlock, waiting_for >>

\* Step 11: Release res_lock if still held (bug path keeps it)
CV_FinalRelease ==
    /\ pc["convert"] = "CV_FinalRelease"
    /\ IF "res_lock" \in held["convert"]
       THEN /\ res_lock' = "free"
            /\ held' = [held EXCEPT !["convert"] = held["convert"] \ {"res_lock"}]
       ELSE UNCHANGED << res_lock, held >>
    /\ pc' = [pc EXCEPT !["convert"] = "Done"]
    /\ UNCHANGED << ns_lock, exp_bl_lock, waiting_spinlock, waiting_for >>

\* =====================================================================
\* CancelThread -- ldlm_prepare_lru_list + ldlm_cli_cancel_local
\* (ldlm_request.c:2103-2285, 1382-1423)
\*
\* Path: ns_lock -> [drop ns_lock] -> res_lock -> done
\* Bug: omitting the ns_lock drop creates ns->res nesting.
\* =====================================================================

CN_WaitNs ==
    /\ pc["cancel"] = "CN_WaitNs"
    /\ waiting_for' = [waiting_for EXCEPT !["cancel"] = "ns_lock"]
    /\ pc' = [pc EXCEPT !["cancel"] = "CN_GrabNs"]
    /\ UNCHANGED << res_lock, ns_lock, exp_bl_lock, waiting_spinlock, held >>

CN_GrabNs ==
    /\ pc["cancel"] = "CN_GrabNs"
    /\ ns_lock = "free"
    /\ ns_lock' = "cancel"
    /\ held' = [held EXCEPT !["cancel"] = held["cancel"] \union {"ns_lock"}]
    /\ waiting_for' = [waiting_for EXCEPT !["cancel"] = "none"]
    /\ pc' = [pc EXCEPT !["cancel"] = "CN_MaybeDropNs"]
    /\ UNCHANGED << res_lock, exp_bl_lock, waiting_spinlock >>

CN_MaybeDropNs ==
    /\ pc["cancel"] = "CN_MaybeDropNs"
    /\ IF InjectBugCancelNested
       THEN \* BUG: keep ns_lock while acquiring res_lock
            /\ pc' = [pc EXCEPT !["cancel"] = "CN_WaitRes"]
            /\ UNCHANGED << res_lock, ns_lock, exp_bl_lock, waiting_spinlock, held, waiting_for >>
       ELSE \* CORRECT: drop ns_lock first (line 2178)
            /\ ns_lock' = "free"
            /\ held' = [held EXCEPT !["cancel"] = held["cancel"] \ {"ns_lock"}]
            /\ pc' = [pc EXCEPT !["cancel"] = "CN_WaitRes"]
            /\ UNCHANGED << res_lock, exp_bl_lock, waiting_spinlock, waiting_for >>

CN_WaitRes ==
    /\ pc["cancel"] = "CN_WaitRes"
    /\ waiting_for' = [waiting_for EXCEPT !["cancel"] = "res_lock"]
    /\ pc' = [pc EXCEPT !["cancel"] = "CN_GrabRes"]
    /\ UNCHANGED << res_lock, ns_lock, exp_bl_lock, waiting_spinlock, held >>

CN_GrabRes ==
    /\ pc["cancel"] = "CN_GrabRes"
    /\ res_lock = "free"
    /\ res_lock' = "cancel"
    /\ held' = [held EXCEPT !["cancel"] = held["cancel"] \union {"res_lock"}]
    /\ waiting_for' = [waiting_for EXCEPT !["cancel"] = "none"]
    /\ pc' = [pc EXCEPT !["cancel"] = "CN_ReleaseRes"]
    /\ UNCHANGED << ns_lock, exp_bl_lock, waiting_spinlock >>

CN_ReleaseRes ==
    /\ pc["cancel"] = "CN_ReleaseRes"
    /\ res_lock' = "free"
    /\ held' = [held EXCEPT !["cancel"] = held["cancel"] \ {"res_lock"}]
    /\ pc' = [pc EXCEPT !["cancel"] = "CN_ReleaseNs"]
    /\ UNCHANGED << ns_lock, exp_bl_lock, waiting_spinlock, waiting_for >>

CN_ReleaseNs ==
    /\ pc["cancel"] = "CN_ReleaseNs"
    /\ IF "ns_lock" \in held["cancel"]
       THEN /\ ns_lock' = "free"
            /\ held' = [held EXCEPT !["cancel"] = held["cancel"] \ {"ns_lock"}]
       ELSE UNCHANGED << ns_lock, held >>
    /\ pc' = [pc EXCEPT !["cancel"] = "Done"]
    /\ UNCHANGED << res_lock, exp_bl_lock, waiting_spinlock, waiting_for >>

\* =====================================================================
\* BLASTCallback -- ldlm_handle_bl_callback (ldlm_lockd.c:1900-1936)
\*
\* Simple: res_lock -> release -> callback (no locks)
\* =====================================================================

BL_WaitRes ==
    /\ pc["blast"] = "BL_WaitRes"
    /\ waiting_for' = [waiting_for EXCEPT !["blast"] = "res_lock"]
    /\ pc' = [pc EXCEPT !["blast"] = "BL_GrabRes"]
    /\ UNCHANGED << res_lock, ns_lock, exp_bl_lock, waiting_spinlock, held >>

BL_GrabRes ==
    /\ pc["blast"] = "BL_GrabRes"
    /\ res_lock = "free"
    /\ res_lock' = "blast"
    /\ held' = [held EXCEPT !["blast"] = held["blast"] \union {"res_lock"}]
    /\ waiting_for' = [waiting_for EXCEPT !["blast"] = "none"]
    /\ pc' = [pc EXCEPT !["blast"] = "BL_ReleaseRes"]
    /\ UNCHANGED << ns_lock, exp_bl_lock, waiting_spinlock >>

BL_ReleaseRes ==
    /\ pc["blast"] = "BL_ReleaseRes"
    /\ res_lock' = "free"
    /\ held' = [held EXCEPT !["blast"] = held["blast"] \ {"res_lock"}]
    /\ pc' = [pc EXCEPT !["blast"] = "Done"]
    /\ UNCHANGED << ns_lock, exp_bl_lock, waiting_spinlock, waiting_for >>

\* =====================================================================
\* ReprocessThread -- ldlm_reprocess_queue (ldlm_lock.c:1958-2020)
\*
\* Path: res_lock -> process -> drop -> bl_ast -> res_lock -> release
\* =====================================================================

RP_WaitRes ==
    /\ pc["reprocess"] = "RP_WaitRes"
    /\ waiting_for' = [waiting_for EXCEPT !["reprocess"] = "res_lock"]
    /\ pc' = [pc EXCEPT !["reprocess"] = "RP_GrabRes"]
    /\ UNCHANGED << res_lock, ns_lock, exp_bl_lock, waiting_spinlock, held >>

RP_GrabRes ==
    /\ pc["reprocess"] = "RP_GrabRes"
    /\ res_lock = "free"
    /\ res_lock' = "reprocess"
    /\ held' = [held EXCEPT !["reprocess"] = held["reprocess"] \union {"res_lock"}]
    /\ waiting_for' = [waiting_for EXCEPT !["reprocess"] = "none"]
    /\ pc' = [pc EXCEPT !["reprocess"] = "RP_DropRes"]
    /\ UNCHANGED << ns_lock, exp_bl_lock, waiting_spinlock >>

RP_DropRes ==
    /\ pc["reprocess"] = "RP_DropRes"
    /\ res_lock' = "free"
    /\ held' = [held EXCEPT !["reprocess"] = held["reprocess"] \ {"res_lock"}]
    /\ pc' = [pc EXCEPT !["reprocess"] = "RP_BlAst"]
    /\ UNCHANGED << ns_lock, exp_bl_lock, waiting_spinlock, waiting_for >>

RP_BlAst ==
    /\ pc["reprocess"] = "RP_BlAst"
    /\ pc' = [pc EXCEPT !["reprocess"] = "RP_WaitRes2"]
    /\ UNCHANGED << res_lock, ns_lock, exp_bl_lock, waiting_spinlock, held, waiting_for >>

RP_WaitRes2 ==
    /\ pc["reprocess"] = "RP_WaitRes2"
    /\ waiting_for' = [waiting_for EXCEPT !["reprocess"] = "res_lock"]
    /\ pc' = [pc EXCEPT !["reprocess"] = "RP_GrabRes2"]
    /\ UNCHANGED << res_lock, ns_lock, exp_bl_lock, waiting_spinlock, held >>

RP_GrabRes2 ==
    /\ pc["reprocess"] = "RP_GrabRes2"
    /\ res_lock = "free"
    /\ res_lock' = "reprocess"
    /\ held' = [held EXCEPT !["reprocess"] = held["reprocess"] \union {"res_lock"}]
    /\ waiting_for' = [waiting_for EXCEPT !["reprocess"] = "none"]
    /\ pc' = [pc EXCEPT !["reprocess"] = "RP_ReleaseRes"]
    /\ UNCHANGED << ns_lock, exp_bl_lock, waiting_spinlock >>

RP_ReleaseRes ==
    /\ pc["reprocess"] = "RP_ReleaseRes"
    /\ res_lock' = "free"
    /\ held' = [held EXCEPT !["reprocess"] = held["reprocess"] \ {"res_lock"}]
    /\ pc' = [pc EXCEPT !["reprocess"] = "Done"]
    /\ UNCHANGED << ns_lock, exp_bl_lock, waiting_spinlock, waiting_for >>

\* =====================================================================
\* EnqueueThread -- ldlm_handle_conflict_lock (ldlm_lock.c:2036-2094)
\*
\* Path: res_lock -> drop -> waiting_spinlock [-> exp_bl_lock] -> release -> res_lock
\* =====================================================================

EN_WaitRes ==
    /\ pc["enqueue"] = "EN_WaitRes"
    /\ waiting_for' = [waiting_for EXCEPT !["enqueue"] = "res_lock"]
    /\ pc' = [pc EXCEPT !["enqueue"] = "EN_GrabRes"]
    /\ UNCHANGED << res_lock, ns_lock, exp_bl_lock, waiting_spinlock, held >>

EN_GrabRes ==
    /\ pc["enqueue"] = "EN_GrabRes"
    /\ res_lock = "free"
    /\ res_lock' = "enqueue"
    /\ held' = [held EXCEPT !["enqueue"] = held["enqueue"] \union {"res_lock"}]
    /\ waiting_for' = [waiting_for EXCEPT !["enqueue"] = "none"]
    /\ pc' = [pc EXCEPT !["enqueue"] = "EN_DropRes"]
    /\ UNCHANGED << ns_lock, exp_bl_lock, waiting_spinlock >>

EN_DropRes ==
    /\ pc["enqueue"] = "EN_DropRes"
    /\ res_lock' = "free"
    /\ held' = [held EXCEPT !["enqueue"] = held["enqueue"] \ {"res_lock"}]
    /\ pc' = [pc EXCEPT !["enqueue"] = "EN_WaitSpin"]
    /\ UNCHANGED << ns_lock, exp_bl_lock, waiting_spinlock, waiting_for >>

EN_WaitSpin ==
    /\ pc["enqueue"] = "EN_WaitSpin"
    /\ waiting_for' = [waiting_for EXCEPT !["enqueue"] = "waiting_spinlock"]
    /\ pc' = [pc EXCEPT !["enqueue"] = "EN_GrabSpin"]
    /\ UNCHANGED << res_lock, ns_lock, exp_bl_lock, waiting_spinlock, held >>

EN_GrabSpin ==
    /\ pc["enqueue"] = "EN_GrabSpin"
    /\ waiting_spinlock = "free"
    /\ waiting_spinlock' = "enqueue"
    /\ held' = [held EXCEPT !["enqueue"] = held["enqueue"] \union {"waiting_spinlock"}]
    /\ waiting_for' = [waiting_for EXCEPT !["enqueue"] = "none"]
    /\ IF InjectBugWaitExpNested
       THEN pc' = [pc EXCEPT !["enqueue"] = "EN_WaitExp"]
       ELSE pc' = [pc EXCEPT !["enqueue"] = "EN_ReleaseSpin"]
    /\ UNCHANGED << res_lock, ns_lock, exp_bl_lock >>

\* Bug path: wait for exp_bl_lock while holding waiting_spinlock
EN_WaitExp ==
    /\ pc["enqueue"] = "EN_WaitExp"
    /\ waiting_for' = [waiting_for EXCEPT !["enqueue"] = "exp_bl_list_lock"]
    /\ pc' = [pc EXCEPT !["enqueue"] = "EN_GrabExp"]
    /\ UNCHANGED << res_lock, ns_lock, exp_bl_lock, waiting_spinlock, held >>

EN_GrabExp ==
    /\ pc["enqueue"] = "EN_GrabExp"
    /\ exp_bl_lock = "free"
    /\ exp_bl_lock' = "enqueue"
    /\ held' = [held EXCEPT !["enqueue"] = held["enqueue"] \union {"exp_bl_list_lock"}]
    /\ waiting_for' = [waiting_for EXCEPT !["enqueue"] = "none"]
    /\ pc' = [pc EXCEPT !["enqueue"] = "EN_ReleaseExp"]
    /\ UNCHANGED << res_lock, ns_lock, waiting_spinlock >>

EN_ReleaseExp ==
    /\ pc["enqueue"] = "EN_ReleaseExp"
    /\ exp_bl_lock' = "free"
    /\ held' = [held EXCEPT !["enqueue"] = held["enqueue"] \ {"exp_bl_list_lock"}]
    /\ pc' = [pc EXCEPT !["enqueue"] = "EN_ReleaseSpin"]
    /\ UNCHANGED << res_lock, ns_lock, waiting_spinlock, waiting_for >>

EN_ReleaseSpin ==
    /\ pc["enqueue"] = "EN_ReleaseSpin"
    /\ waiting_spinlock' = "free"
    /\ held' = [held EXCEPT !["enqueue"] = held["enqueue"] \ {"waiting_spinlock"}]
    /\ pc' = [pc EXCEPT !["enqueue"] = "EN_WaitRes2"]
    /\ UNCHANGED << res_lock, ns_lock, exp_bl_lock, waiting_for >>

EN_WaitRes2 ==
    /\ pc["enqueue"] = "EN_WaitRes2"
    /\ waiting_for' = [waiting_for EXCEPT !["enqueue"] = "res_lock"]
    /\ pc' = [pc EXCEPT !["enqueue"] = "EN_GrabRes2"]
    /\ UNCHANGED << res_lock, ns_lock, exp_bl_lock, waiting_spinlock, held >>

EN_GrabRes2 ==
    /\ pc["enqueue"] = "EN_GrabRes2"
    /\ res_lock = "free"
    /\ res_lock' = "enqueue"
    /\ held' = [held EXCEPT !["enqueue"] = held["enqueue"] \union {"res_lock"}]
    /\ waiting_for' = [waiting_for EXCEPT !["enqueue"] = "none"]
    /\ pc' = [pc EXCEPT !["enqueue"] = "EN_ReleaseRes"]
    /\ UNCHANGED << ns_lock, exp_bl_lock, waiting_spinlock >>

EN_ReleaseRes ==
    /\ pc["enqueue"] = "EN_ReleaseRes"
    /\ res_lock' = "free"
    /\ held' = [held EXCEPT !["enqueue"] = held["enqueue"] \ {"res_lock"}]
    /\ pc' = [pc EXCEPT !["enqueue"] = "Done"]
    /\ UNCHANGED << ns_lock, exp_bl_lock, waiting_spinlock, waiting_for >>

\* =====================================================================
\* Stuttering step for termination (all processes at Done)
\* =====================================================================

Terminating ==
    /\ \A p \in Procs: pc[p] = "Done"
    /\ UNCHANGED vars

\* =====================================================================
\* Specification
\* =====================================================================

ConvertThread == CV_WaitRes \/ CV_GrabRes \/ CV_DropRes \/ CV_Callback
                 \/ CV_WaitRes2 \/ CV_GrabRes2 \/ CV_PreNsLock
                 \/ CV_WaitNs \/ CV_GrabNs \/ CV_ReleaseNs \/ CV_FinalRelease

CancelThread == CN_WaitNs \/ CN_GrabNs \/ CN_MaybeDropNs
                \/ CN_WaitRes \/ CN_GrabRes \/ CN_ReleaseRes \/ CN_ReleaseNs

BLASTCallback == BL_WaitRes \/ BL_GrabRes \/ BL_ReleaseRes

ReprocessThread == RP_WaitRes \/ RP_GrabRes \/ RP_DropRes \/ RP_BlAst
                   \/ RP_WaitRes2 \/ RP_GrabRes2 \/ RP_ReleaseRes

EnqueueThread == EN_WaitRes \/ EN_GrabRes \/ EN_DropRes
                 \/ EN_WaitSpin \/ EN_GrabSpin
                 \/ EN_WaitExp \/ EN_GrabExp \/ EN_ReleaseExp
                 \/ EN_ReleaseSpin \/ EN_WaitRes2 \/ EN_GrabRes2 \/ EN_ReleaseRes

Next == ConvertThread \/ CancelThread \/ BLASTCallback
        \/ ReprocessThread \/ EnqueueThread
        \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(ConvertThread)
        /\ WF_vars(CancelThread)
        /\ WF_vars(BLASTCallback)
        /\ WF_vars(ReprocessThread)
        /\ WF_vars(EnqueueThread)

\* =====================================================================
\* Invariants
\* =====================================================================

\* Type correctness
TypeOK ==
    /\ res_lock \in {"free"} \cup Procs
    /\ ns_lock \in {"free"} \cup Procs
    /\ exp_bl_lock \in {"free"} \cup Procs
    /\ waiting_spinlock \in {"free"} \cup Procs
    /\ \A p \in Procs: held[p] \subseteq LOCKS
    /\ \A p \in Procs: waiting_for[p] \in {"none"} \cup LOCKS

\* NoDeadlock: No circular wait between any pair of processes.
\* A deadlock exists when process A holds lock X and waits for lock Y,
\* while process B holds lock Y and waits for lock X.
NoDeadlock ==
    ~\E p1, p2 \in Procs:
        /\ p1 /= p2
        /\ waiting_for[p1] /= "none"
        /\ waiting_for[p2] /= "none"
        \* p1 waits for a lock held by p2
        /\ waiting_for[p1] \in held[p2]
        \* p2 waits for a lock held by p1
        /\ waiting_for[p2] \in held[p1]

\* NoLockOrderInversion: No thread holds a lower-ranked lock while waiting
\* for a higher-ranked lock. The intended order is higher-ranked first.
\* This catches ordering violations even without a concurrent deadlock.
NoLockOrderInversion ==
    ~\E p \in Procs:
        /\ waiting_for[p] /= "none"
        /\ \E heldLock \in held[p]:
            LockRank[waiting_for[p]] > LockRank[heldLock]

\* Termination: all processes eventually complete
Termination == <>(\A p \in Procs: pc[p] = "Done")

\* =====================================================================
\* Named deadlock witnesses for specific known inversions
\* =====================================================================

\* PR #14 deadlock: convert holds res_lock waiting for ns_lock,
\*                  cancel holds ns_lock waiting for res_lock.
NoPR14Deadlock ==
    ~(/\ "res_lock" \in held["convert"]
      /\ waiting_for["convert"] = "ns_lock"
      /\ "ns_lock" \in held["cancel"]
      /\ waiting_for["cancel"] = "res_lock")

=============================================================================
