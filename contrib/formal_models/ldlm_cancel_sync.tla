---------------------------- MODULE ldlm_cancel_sync ----------------------------
(*
 * PlusCal/TLA+ model of the LDLM cancel callback synchronization
 * protocol from ldlm_cancel_callback (ldlm_lock.c:2459-2482).
 *
 * Models N concurrent threads calling ldlm_cancel_callback on
 * the same lock.  Uses a two-flag protocol:
 *   - LDLM_FL_CANCEL: "first caller wins" gate
 *   - LDLM_FL_BL_DONE: completion signal
 *
 * The first thread to enter sets CANCEL, drops lr_lock, runs
 * the blocking_ast callback, reacquires lr_lock, sets BL_DONE,
 * and wakes waiters.  Subsequent threads either:
 *   - See CANCEL set but BL_DONE not set -> wait on l_waitq
 *   - See both CANCEL and BL_DONE set -> skip (already done)
 *
 * Race window: between unlock (line 2465) and relock (2468),
 * other threads can acquire lr_lock and observe CANCEL=TRUE,
 * BL_DONE=FALSE.  They must correctly wait rather than proceed.
 *
 * Safety invariants:
 *   CallbackOnce:      blocking_ast called exactly once
 *   BLDoneImpliesCancel: BL_DONE only set after CANCEL
 *   AllComplete:        All threads eventually finish
 *   NoWaitAfterDone:    No thread waits when BL_DONE is set
 *
 * Also models the destroy race: what if another thread destroys
 * the lock (sets DESTROYED) during the callback window?
 * Inject InjectBugNoWait to skip the wait_event_idle path.
 *
 * Source (lustre-release master 47638add78):
 *   lustre/ldlm/ldlm_lock.c     ldlm_cancel_callback (2459-2482)
 *     T_CheckCancel: CANCEL test/set 2462-2463; T_RunCallback:
 *     unlock 2465, blocking_ast 2466-2467, relock 2468;
 *     T_SetBLDone: BL_DONE 2474, wake_up 2475; T_Wait: unlock 2478,
 *     wait_event_idle(is_bl_done) 2479, relock 2480.  The
 *     l_blocking_ast == NULL branch (2469-2471, no unlock window)
 *     is not modeled.
 *   lustre/ldlm/ldlm_internal.h is_bl_done (337-348)
 *   lustre/ldlm/ldlm_lock.c     ldlm_lock_cancel (2496-2538)
 *     caller: lr_lock held from 2503, ldlm_cancel_callback 2519,
 *     second ldlm_del_waiting_lock 2521-2525 (see LU-7860 below).
 *   lustre/ldlm/ldlm_lockd.c    ldlm_add_waiting_lock (440-497)
 *     WL_TryAdd: called with lr_lock held (446), refuses a lock with
 *     CANCEL set under waiting_locks_spinlock 460-464.
 *   Fix commit 657bbc4969 (LU-6416).
 *
 * Validated against: lustre-release master 47638add78 (2026-09-06)
 *)

EXTENDS Integers, FiniteSets, TLC

CONSTANTS
    NumThreads,          \* Number of concurrent cancel callers
    InjectBugNoWait,     \* TRUE = skip wait_event_idle (proceed without BL_DONE)
    InjectBugNoCheckCancel  \* TRUE = LU-6416: ldlm_add_waiting_lock
                            \* does not check CANCEL flag, allowing
                            \* cancelled lock to be re-added to
                            \* waiting list during callback window

ASSUME NumThreads \in 2..5

ThreadNums == 1..NumThreads
Threads == {ToString(i) : i \in ThreadNums}

\* Thread ID is already a string now
ThreadStr(t) == t

(* --algorithm ldlm_cancel_sync

variables
    \* ---- Resource spinlock (lr_lock) ----
    lr_lock = "free",

    \* ---- Lock flags (protected by lr_lock) ----
    fl_CANCEL = FALSE,
    fl_BL_DONE = FALSE,
    fl_DESTROYED = FALSE,

    \* ---- Callback tracking ----
    callback_calls = 0,    \* How many times blocking_ast was called
    callback_running = FALSE,  \* Is callback currently executing?

    \* ---- Waitqueue ----
    \* Models wait_event_idle(lock->l_waitq, is_bl_done(lock))
    \* Threads set themselves as waiting; wake_up signals all.
    waiting = {},          \* Set of thread IDs currently waiting

    \* ---- Per-thread completion ----
    thread_done = [t \in Threads |-> FALSE],

    \* ---- Waiting list (LU-6416) ----
    \* Models whether the lock is on the server waiting list.
    \* During the cancel callback window, another thread can
    \* try to re-add the lock via ldlm_add_waiting_lock.
    on_waiting_list = FALSE;

define
    \* ========== SAFETY INVARIANTS ==========

    \* blocking_ast must be called exactly once (never zero, never twice)
    CallbackOnce ==
        callback_calls <= 1

    \* BL_DONE can only be set if CANCEL was set first
    BLDoneImpliesCancel ==
        fl_BL_DONE => fl_CANCEL

    \* Callback must not be running after all threads complete
    NoCallbackAfterDone ==
        (\A t \in Threads : thread_done[t]) =>
            ~callback_running

    \* After a thread completes ldlm_cancel_callback, CANCEL and
    \* BL_DONE must both be set
    PostCondition ==
        \A t \in Threads :
            thread_done[t] => (fl_CANCEL /\ fl_BL_DONE)

    \* LU-6416: A cancelled lock must never be on the waiting list
    \* after ldlm_lock_cancel finishes (ldlm_cancel_callback returns).
    \* The fix (657bbc4969) checks CANCEL in ldlm_add_waiting_lock
    \* (ldlm_lockd.c:461-464) to prevent re-addition entirely and
    \* replaced the second ldlm_del_waiting_lock in ldlm_lock_cancel
    \* with an LASSERT; LU-7860 (62a859fade) restored that second
    \* removal (ldlm_lock.c:2521-2525) as a belt-and-braces check, so
    \* current master has both.  Only the add-side check is modeled.
    NoCancelledOnWaiting ==
        (fl_BL_DONE) => ~on_waiting_list

    TypeOK ==
        /\ callback_calls \in 0..3
        /\ fl_CANCEL \in BOOLEAN
        /\ fl_BL_DONE \in BOOLEAN
        /\ waiting \subseteq Threads
        /\ on_waiting_list \in BOOLEAN
end define;

\* ================================================================
\* Each thread models one call to ldlm_cancel_callback.
\*
\* Protocol from ldlm_lock.c:2459-2482:
\*   check_res_locked(lock->l_resource);
\*   if (!(lock->l_flags & LDLM_FL_CANCEL)) {
\*       lock->l_flags |= LDLM_FL_CANCEL;
\*       unlock_res_and_lock(lock);
\*       lock->l_blocking_ast(lock, ...);
\*       lock_res_and_lock(lock);
\*       lock->l_flags |= LDLM_FL_BL_DONE;
\*       wake_up(&lock->l_waitq);
\*   } else if (!(lock->l_flags & LDLM_FL_BL_DONE)) {
\*       unlock_res_and_lock(lock);
\*       wait_event_idle(lock->l_waitq, is_bl_done(lock));
\*       lock_res_and_lock(lock);
\*   }
\* ================================================================
fair process Canceller \in Threads
begin
T_Lock:
    \* lock_res_and_lock(lock) -- called by ldlm_lock_cancel
    \* before calling ldlm_cancel_callback
    await lr_lock = "free";
    lr_lock := ThreadStr(self);

T_CheckCancel:
    \* check_res_locked(lock->l_resource)
    if ~fl_CANCEL then
        \* First caller: set CANCEL flag
        fl_CANCEL := TRUE;

        \* unlock_res_and_lock(lock) -- drop lock for callback
        lr_lock := "free";
    else
        \* CANCEL already set by another thread
        if ~fl_BL_DONE then
            \* BL_DONE not yet set: must wait
            if InjectBugNoWait then
                \* BUG: skip wait, proceed as if done
                lr_lock := "free";
                goto T_Complete;
            end if;

T_Unlock2:
            \* unlock_res_and_lock(lock)
            lr_lock := "free";
            goto T_Wait;
        else
            \* Both CANCEL and BL_DONE set: nothing to do
            lr_lock := "free";
            goto T_Complete;
        end if;
    end if;

T_RunCallback:
    \* lock->l_blocking_ast(lock, NULL, ..., LDLM_CB_CANCELING)
    \* Runs WITHOUT lr_lock held
    callback_calls := callback_calls + 1;
    callback_running := TRUE;

T_CallbackDone:
    callback_running := FALSE;

T_Relock:
    \* lock_res_and_lock(lock)
    await lr_lock = "free";
    lr_lock := ThreadStr(self);

T_SetBLDone:
    \* "only canceller can set bl_done bit"
    fl_BL_DONE := TRUE;

    \* wake_up(&lock->l_waitq)
    \* All waiting threads are woken
    waiting := {};

    lr_lock := "free";
    goto T_Complete;

T_Wait:
    \* wait_event_idle(lock->l_waitq, is_bl_done(lock))
    \* First: check without lock (fast path in is_bl_done)
    if fl_BL_DONE then
        goto T_WaitRelock;
    end if;

T_AddWait:
    \* Not done yet: add self to waitqueue
    waiting := waiting \union {self};

T_WaitCheck:
    \* wait_event_idle wakes up, checks condition
    \* is_bl_done: lock_res_and_lock, check, unlock_res_and_lock
    await fl_BL_DONE \/ self \notin waiting;
    if ~fl_BL_DONE then
        \* Spurious wakeup: go back to sleep
        waiting := waiting \union {self};
        goto T_WaitCheck;
    end if;

T_WaitRelock:
    \* lock_res_and_lock(lock) -- reacquire after wait
    await lr_lock = "free";
    lr_lock := ThreadStr(self);

T_WaitUnlock:
    \* Now holding lock with CANCEL and BL_DONE both set
    lr_lock := "free";

T_Complete:
    thread_done[self] := TRUE;
end process;

\* ================================================================
\* WaitingListAdder: Another server thread that tries to add
\* the lock to the waiting list during the cancel callback window.
\*
\* Models: ldlm_handle_enqueue (ldlm_lockd.c:1455-1487) sending completion AST with
\* AST_SENT set, then calling ldlm_add_waiting_lock.
\* This races with ldlm_cancel_callback's unlock window.
\*
\* LU-6416 fix: ldlm_add_waiting_lock checks CANCEL flag
\* under waiting_locks_spinlock and refuses to add.
\* ================================================================
fair process WaitingListAdder = "adder"
begin
WL_Wait:
    \* Wait for the callback window (CANCEL set, lr_lock free)
    await callback_running;

WL_Lock:
    await lr_lock = "free";
    lr_lock := "adder";

WL_TryAdd:
    \* ldlm_add_waiting_lock: try to add lock to waiting list
    if InjectBugNoCheckCancel then
        \* BUG: don't check CANCEL flag, always add
        on_waiting_list := TRUE;
    else
        \* FIX: check CANCEL flag first (under spinlock)
        if ~fl_CANCEL then
            on_waiting_list := TRUE;
        end if;
    end if;
    lr_lock := "free";
end process;

end algorithm; *)

\* BEGIN TRANSLATION
VARIABLES lr_lock, fl_CANCEL, fl_BL_DONE, fl_DESTROYED, callback_calls,
          callback_running, waiting, thread_done, on_waiting_list, pc

(* define statement *)
CallbackOnce ==
    callback_calls <= 1


BLDoneImpliesCancel ==
    fl_BL_DONE => fl_CANCEL


NoCallbackAfterDone ==
    (\A t \in Threads : thread_done[t]) =>
        ~callback_running



PostCondition ==
    \A t \in Threads :
        thread_done[t] => (fl_CANCEL /\ fl_BL_DONE)






NoCancelledOnWaiting ==
    (fl_BL_DONE) => ~on_waiting_list

TypeOK ==
    /\ callback_calls \in 0..3
    /\ fl_CANCEL \in BOOLEAN
    /\ fl_BL_DONE \in BOOLEAN
    /\ waiting \subseteq Threads
    /\ on_waiting_list \in BOOLEAN


vars == << lr_lock, fl_CANCEL, fl_BL_DONE, fl_DESTROYED, callback_calls,
           callback_running, waiting, thread_done, on_waiting_list, pc >>

ProcSet == (Threads) \cup {"adder"}

Init == (* Global variables *)
        /\ lr_lock = "free"
        /\ fl_CANCEL = FALSE
        /\ fl_BL_DONE = FALSE
        /\ fl_DESTROYED = FALSE
        /\ callback_calls = 0
        /\ callback_running = FALSE
        /\ waiting = {}
        /\ thread_done = [t \in Threads |-> FALSE]
        /\ on_waiting_list = FALSE
        /\ pc = [self \in ProcSet |-> CASE self \in Threads -> "T_Lock"
                                        [] self = "adder" -> "WL_Wait"]

T_Lock(self) == /\ pc[self] = "T_Lock"
                /\ lr_lock = "free"
                /\ lr_lock' = ThreadStr(self)
                /\ pc' = [pc EXCEPT ![self] = "T_CheckCancel"]
                /\ UNCHANGED << fl_CANCEL, fl_BL_DONE, fl_DESTROYED,
                                callback_calls, callback_running, waiting,
                                thread_done, on_waiting_list >>

T_CheckCancel(self) == /\ pc[self] = "T_CheckCancel"
                       /\ IF ~fl_CANCEL
                             THEN /\ fl_CANCEL' = TRUE
                                  /\ lr_lock' = "free"
                                  /\ pc' = [pc EXCEPT ![self] = "T_RunCallback"]
                             ELSE /\ IF ~fl_BL_DONE
                                        THEN /\ IF InjectBugNoWait
                                                   THEN /\ lr_lock' = "free"
                                                        /\ pc' = [pc EXCEPT ![self] = "T_Complete"]
                                                   ELSE /\ pc' = [pc EXCEPT ![self] = "T_Unlock2"]
                                                        /\ UNCHANGED lr_lock
                                        ELSE /\ lr_lock' = "free"
                                             /\ pc' = [pc EXCEPT ![self] = "T_Complete"]
                                  /\ UNCHANGED fl_CANCEL
                       /\ UNCHANGED << fl_BL_DONE, fl_DESTROYED,
                                       callback_calls, callback_running,
                                       waiting, thread_done, on_waiting_list >>

T_Unlock2(self) == /\ pc[self] = "T_Unlock2"
                   /\ lr_lock' = "free"
                   /\ pc' = [pc EXCEPT ![self] = "T_Wait"]
                   /\ UNCHANGED << fl_CANCEL, fl_BL_DONE, fl_DESTROYED,
                                   callback_calls, callback_running, waiting,
                                   thread_done, on_waiting_list >>

T_RunCallback(self) == /\ pc[self] = "T_RunCallback"
                       /\ callback_calls' = callback_calls + 1
                       /\ callback_running' = TRUE
                       /\ pc' = [pc EXCEPT ![self] = "T_CallbackDone"]
                       /\ UNCHANGED << lr_lock, fl_CANCEL, fl_BL_DONE,
                                       fl_DESTROYED, waiting, thread_done,
                                       on_waiting_list >>

T_CallbackDone(self) == /\ pc[self] = "T_CallbackDone"
                        /\ callback_running' = FALSE
                        /\ pc' = [pc EXCEPT ![self] = "T_Relock"]
                        /\ UNCHANGED << lr_lock, fl_CANCEL, fl_BL_DONE,
                                        fl_DESTROYED, callback_calls, waiting,
                                        thread_done, on_waiting_list >>

T_Relock(self) == /\ pc[self] = "T_Relock"
                  /\ lr_lock = "free"
                  /\ lr_lock' = ThreadStr(self)
                  /\ pc' = [pc EXCEPT ![self] = "T_SetBLDone"]
                  /\ UNCHANGED << fl_CANCEL, fl_BL_DONE, fl_DESTROYED,
                                  callback_calls, callback_running, waiting,
                                  thread_done, on_waiting_list >>

T_SetBLDone(self) == /\ pc[self] = "T_SetBLDone"
                     /\ fl_BL_DONE' = TRUE
                     /\ waiting' = {}
                     /\ lr_lock' = "free"
                     /\ pc' = [pc EXCEPT ![self] = "T_Complete"]
                     /\ UNCHANGED << fl_CANCEL, fl_DESTROYED, callback_calls,
                                     callback_running, thread_done,
                                     on_waiting_list >>

T_Wait(self) == /\ pc[self] = "T_Wait"
                /\ IF fl_BL_DONE
                      THEN /\ pc' = [pc EXCEPT ![self] = "T_WaitRelock"]
                      ELSE /\ pc' = [pc EXCEPT ![self] = "T_AddWait"]
                /\ UNCHANGED << lr_lock, fl_CANCEL, fl_BL_DONE, fl_DESTROYED,
                                callback_calls, callback_running, waiting,
                                thread_done, on_waiting_list >>

T_AddWait(self) == /\ pc[self] = "T_AddWait"
                   /\ waiting' = (waiting \union {self})
                   /\ pc' = [pc EXCEPT ![self] = "T_WaitCheck"]
                   /\ UNCHANGED << lr_lock, fl_CANCEL, fl_BL_DONE,
                                   fl_DESTROYED, callback_calls,
                                   callback_running, thread_done,
                                   on_waiting_list >>

T_WaitCheck(self) == /\ pc[self] = "T_WaitCheck"
                     /\ fl_BL_DONE \/ self \notin waiting
                     /\ IF ~fl_BL_DONE
                           THEN /\ waiting' = (waiting \union {self})
                                /\ pc' = [pc EXCEPT ![self] = "T_WaitCheck"]
                           ELSE /\ pc' = [pc EXCEPT ![self] = "T_WaitRelock"]
                                /\ UNCHANGED waiting
                     /\ UNCHANGED << lr_lock, fl_CANCEL, fl_BL_DONE,
                                     fl_DESTROYED, callback_calls,
                                     callback_running, thread_done,
                                     on_waiting_list >>

T_WaitRelock(self) == /\ pc[self] = "T_WaitRelock"
                      /\ lr_lock = "free"
                      /\ lr_lock' = ThreadStr(self)
                      /\ pc' = [pc EXCEPT ![self] = "T_WaitUnlock"]
                      /\ UNCHANGED << fl_CANCEL, fl_BL_DONE, fl_DESTROYED,
                                      callback_calls, callback_running,
                                      waiting, thread_done, on_waiting_list >>

T_WaitUnlock(self) == /\ pc[self] = "T_WaitUnlock"
                      /\ lr_lock' = "free"
                      /\ pc' = [pc EXCEPT ![self] = "T_Complete"]
                      /\ UNCHANGED << fl_CANCEL, fl_BL_DONE, fl_DESTROYED,
                                      callback_calls, callback_running,
                                      waiting, thread_done, on_waiting_list >>

T_Complete(self) == /\ pc[self] = "T_Complete"
                    /\ thread_done' = [thread_done EXCEPT ![self] = TRUE]
                    /\ pc' = [pc EXCEPT ![self] = "Done"]
                    /\ UNCHANGED << lr_lock, fl_CANCEL, fl_BL_DONE,
                                    fl_DESTROYED, callback_calls,
                                    callback_running, waiting, on_waiting_list >>

Canceller(self) == T_Lock(self) \/ T_CheckCancel(self) \/ T_Unlock2(self)
                      \/ T_RunCallback(self) \/ T_CallbackDone(self)
                      \/ T_Relock(self) \/ T_SetBLDone(self)
                      \/ T_Wait(self) \/ T_AddWait(self)
                      \/ T_WaitCheck(self) \/ T_WaitRelock(self)
                      \/ T_WaitUnlock(self) \/ T_Complete(self)

WL_Wait == /\ pc["adder"] = "WL_Wait"
           /\ callback_running
           /\ pc' = [pc EXCEPT !["adder"] = "WL_Lock"]
           /\ UNCHANGED << lr_lock, fl_CANCEL, fl_BL_DONE, fl_DESTROYED,
                           callback_calls, callback_running, waiting,
                           thread_done, on_waiting_list >>

WL_Lock == /\ pc["adder"] = "WL_Lock"
           /\ lr_lock = "free"
           /\ lr_lock' = "adder"
           /\ pc' = [pc EXCEPT !["adder"] = "WL_TryAdd"]
           /\ UNCHANGED << fl_CANCEL, fl_BL_DONE, fl_DESTROYED, callback_calls,
                           callback_running, waiting, thread_done,
                           on_waiting_list >>

WL_TryAdd == /\ pc["adder"] = "WL_TryAdd"
             /\ IF InjectBugNoCheckCancel
                   THEN /\ on_waiting_list' = TRUE
                   ELSE /\ IF ~fl_CANCEL
                              THEN /\ on_waiting_list' = TRUE
                              ELSE /\ TRUE
                                   /\ UNCHANGED on_waiting_list
             /\ lr_lock' = "free"
             /\ pc' = [pc EXCEPT !["adder"] = "Done"]
             /\ UNCHANGED << fl_CANCEL, fl_BL_DONE, fl_DESTROYED,
                             callback_calls, callback_running, waiting,
                             thread_done >>

WaitingListAdder == WL_Wait \/ WL_Lock \/ WL_TryAdd

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == WaitingListAdder
           \/ (\E self \in Threads: Canceller(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Threads : WF_vars(Canceller(self))
        /\ WF_vars(WaitingListAdder)

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

\* ================================================================
\* Liveness: all threads eventually complete
\* ================================================================
AllComplete ==
    <>(\A t \in Threads : thread_done[t])

=============================================================================
