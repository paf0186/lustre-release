----------------------- MODULE ldlm_unified_lifecycle -----------------------
(*
 * Unified LDLM lock lifecycle model.
 *
 * Merges flag-level detail from ldlm_grant_cancel, multi-thread
 * cancel sync from ldlm_cancel_sync, concurrent reprocess from
 * ldlm_dual_reprocess, and ERESTART/failed-lock handling from
 * ldlm_reprocess into a single specification covering the full
 * lock lifecycle on one resource.
 *
 * Scenario:
 *   - Resource R has holder H (EX mode, already granted)
 *   - Waiter W enqueues for EX, conflicts with H
 *   - Full lifecycle: enqueue -> conflict -> BL_AST -> cancel ->
 *     reprocess -> grant -> CP_AST -> resource change
 *
 * Concurrency modeled:
 *   - EnqueueHandler: server enqueue of W, BL_AST send, recheck
 *     (LU-8246: BLOCK_GRANTED on already-granted lock)
 *   - CancellerA/CancellerB: two threads calling ldlm_cancel_callback
 *     on H simultaneously (cancel sync protocol, LU-6416)
 *   - WaitingListAdder: re-adds cancelled lock during callback
 *     window (LU-6416)
 *   - ServerCancel: server cancel of H, triggers reprocess
 *     (FIXED 2026-03-13: waits for BL_DONE, not just CANCEL, because
 *      the cancel RPC is only sent after callback writeback completes.
 *      osc_cache_writeback_range(hp=1) blocks synchronously.)
 *   - Reprocessor: server reprocess after cancel, with ERESTART
 *   - CPCallback: client CP callback for W, resource change race
 *     (LU-8391: double grant after change_resource)
 *   - AltGranter: alternate grant path during resource change window
 *
 * Bug injection constants:
 *   InjectBug8391  - omit granted check after resource change (double grant)
 *   InjectBug8246  - omit granted check after BL_AST send (flag inconsistency)
 *   InjectBug6416  - don't check CANCEL in add_waiting_lock (re-add race)
 *   InjectBugNoWait - skip wait_event_idle in cancel sync
 *   InjectBugNoRestart - skip ERESTART rescan entirely
 *
 * Safety invariants:
 *   NoDoubleGrant         - W granted at most once (server + client each)
 *   FlagConsistency       - BLOCK_GRANTED cleared when granted at completion
 *   CancelCallbackOnce    - H's blocking_ast called exactly once
 *   BLDoneImpliesCancel   - BL_DONE only after CANCEL
 *   NoCancelledOnWaiting  - cancelled lock not on waiting list after BL_DONE
 *   NoGrantWhileHeld      - W not granted while H active
 *   PoolCorrect           - pool counts match grant calls
 *
 * Abstractions / simplifications:
 *   - Single resource R (no multi-resource contention)
 *   - One holder H + one waiter W (minimal for lifecycle coverage;
 *     dual-reprocess races tested separately in ldlm_dual_reprocess)
 *   - Cancel sync limited to 2 threads (sufficient per cancel_sync model)
 *   - Coordination via separate boolean flags (no shared phase variable)
 *   - Mode compatibility simplified: H=EX, W=EX (always conflict)
 *
 * Usage:
 *   ./run_model.sh ldlm_unified_lifecycle
 *
 * Source (lustre-release master 47638add78):
 *   EnqueueHandler   ldlm_lock_enqueue ldlm_lock.c:1783-1949 ->
 *                    ldlm_lock_enqueue_helper 1750-1770 ->
 *                    ldlm_handle_conflict_lock 2036-2094
 *                    (unlock_res 2055, lock_res 2067, DESTROYED ->
 *                    -EAGAIN 2075-2076, granted -> clear
 *                    LDLM_FL_BLOCKED_MASK 2079-2088, then
 *                    LDLM_FL_BLOCK_GRANTED set 2091)
 *   CancellerA/B     ldlm_cancel_callback ldlm_lock.c:2459-2482
 *                    (CANCEL 2462-2463, BL_DONE 2474, wait 2476-2480)
 *                    from ldlm_lock_cancel 2496-2538 and
 *                    ldlm_cli_cancel_local ldlm_request.c:1382-1423
 *   WaitingListAdder ldlm_add_waiting_lock ldlm_lockd.c:440-497
 *                    (CANCEL check 461-464); second
 *                    ldlm_del_waiting_lock in ldlm_lock_cancel
 *                    2521-2525 (LU-7860, 62a859fade)
 *   ServerCancel     ldlm_request_cancel ldlm_lockd.c:1716-1810 ->
 *                    ldlm_lock_cancel -> ldlm_reprocess_all 2430
 *   Reprocessor      __ldlm_reprocess_all ldlm_lock.c:2383-2428,
 *                    ldlm_reprocess_queue 1958-2020
 *   CPCallback       ldlm_handle_cp_callback ldlm_lockd.c:1957-2097
 *                    (resource change 2003-2015, double-grant check
 *                    2024-2029, ldlm_grant_lock 2070)
 *   client blocked   ldlm_lock_enqueue local path ldlm_lock.c:
 *                    1878-1884 (granted before enqueue returned:
 *                    clear LDLM_FL_BLOCKED_MASK), 1909-1914
 *
 * Validated against: lustre-release master 47638add78 (2026-09-06)
 *
 * Validation notes:
 *   - LU-8246 (DISCREPANCY-OPEN): the modeled fix, EH_Check, clears
 *     BLOCK_GRANTED and skips EH_SetBlocked when W was granted
 *     during the BL_AST window.  Since LU-13692 (24e3b5395b) removed
 *     the early RETURN(0) in ldlm_handle_conflict_lock, the server
 *     clears LDLM_FL_BLOCKED_MASK at 2087 but then unconditionally
 *     ORs LDLM_FL_BLOCK_GRANTED back in at 2091, so the reply flag
 *     is set even for a lock granted in the window.  The client
 *     compensates in ldlm_lock_enqueue (1878-1884: local && granted
 *     -> clear BLOCKED_MASK), so FlagConsistency still holds for the
 *     client-side view the invariant checks, but via a different
 *     mechanism than EH_Check encodes.  Left as is: the PlusCal body
 *     would need re-translation and the invariant conflates the
 *     server reply flag with the client's lock flag.
 *   - LU-6416: the CANCEL check in ldlm_add_waiting_lock (461-464)
 *     is intact; LU-7860 (62a859fade) restored the second
 *     ldlm_del_waiting_lock in ldlm_lock_cancel (2521-2525) as
 *     defence in depth.  The modeled fix matches the first mechanism.
 *   - LU-8391: ldlm_handle_cp_callback still re-checks
 *     destroyed/granted after ldlm_lock_change_resource (2024-2029),
 *     as CP_8391Check models.
 *   - Model note (not drift): reprocess_ready is set in the same
 *     step as h_active := FALSE, so the RP_Scan "holder still
 *     active" branch and hence InjectBugNoRestart are unreachable.
 *)

EXTENDS Integers, FiniteSets, TLC

CONSTANTS
    InjectBug8391,          \* TRUE = omit granted check after resource change
    InjectBug8246,          \* TRUE = omit granted check after BL_AST send
    InjectBug6416,          \* TRUE = don't check CANCEL in add_waiting_lock
    InjectBugNoWait,        \* TRUE = skip wait_event_idle in cancel sync
    InjectBugNoRestart      \* TRUE = skip ERESTART rescan

(* --algorithm ldlm_unified_lifecycle

variables
    \* ---- Resource spinlock (lr_lock) ----
    lr_lock = "free",

    \* ---- Holder H state ----
    h_active = TRUE,              \* holder lock is granted
    h_fl_CANCEL = FALSE,          \* LDLM_FL_CANCEL on H
    h_fl_BL_DONE = FALSE,         \* LDLM_FL_BL_DONE on H
    h_fl_AST_SENT = FALSE,        \* BL_AST queued for H
    h_callback_calls = 0,         \* times blocking_ast called for H
    h_callback_running = FALSE,   \* blocking_ast currently executing
    h_on_waiting_list = FALSE,    \* H on server waiting list (LU-6416)
    h_cancel_waiting = {},        \* threads waiting on H's l_waitq

    \* ---- Waiter W state (server-side) ----
    w_list = "none",              \* "none" | "waiting" | "granted"
    w_fl_AST_SENT = FALSE,        \* BL_AST was sent for W's conflict
    w_fl_CP_REQD = FALSE,         \* CP_AST queued for W
    w_fl_BLOCK_GRANTED = FALSE,   \* LDLM_FL_BLOCK_GRANTED on W
    w_fl_DESTROYED = FALSE,       \* W destroyed

    \* ---- Waiter W state (client-side) ----
    w_granted_mode = 0,           \* 0 = not granted, 4 = granted EX
    w_resource = "R1",            \* current resource
    w_cp_resource = "R2",         \* resource from CP_AST (server assigned)

    \* ---- Grant tracking ----
    w_server_grant_calls = 0,
    w_client_grant_calls = 0,
    w_server_pool = 0,
    w_client_pool = 0,

    \* ---- Reprocess state ----
    erestart = FALSE,

    \* ---- Coordination flags (separate, no race) ----
    reprocess_ready = FALSE,      \* ServerCancel signals reprocessor
    cp_ready = FALSE,             \* Reprocessor signals CPCallback
    resource_changing = FALSE,    \* CPCallback signals AltGranter
    lifecycle_done = FALSE,       \* CPCallback signals completion

    \* ---- Per-canceller completion ----
    cancel_a_done = FALSE,
    cancel_b_done = FALSE;

define
    IsWGranted == w_granted_mode = 4

    \* ========== SAFETY INVARIANTS ==========

    NoDoubleServerGrant == w_server_grant_calls <= 1
    NoDoubleClientGrant == w_client_grant_calls <= 1
    ServerPoolCorrect == w_server_pool <= 1
    ClientPoolCorrect == w_client_pool <= 1

    \* When lifecycle completes with W granted, BLOCK_GRANTED must be clear
    FlagConsistency ==
        (lifecycle_done /\ IsWGranted /\ w_list = "granted")
            => ~w_fl_BLOCK_GRANTED

    CancelCallbackOnce == h_callback_calls <= 1
    BLDoneImpliesCancel == h_fl_BL_DONE => h_fl_CANCEL
    NoCancelledOnWaiting == h_fl_BL_DONE => ~h_on_waiting_list

    NoGrantWhileHeld ==
        h_active => (w_list /= "granted" /\ w_server_grant_calls = 0)

    CancelPostCondition ==
        (cancel_a_done /\ cancel_b_done) =>
            (h_fl_CANCEL /\ h_fl_BL_DONE)

    TotalGrantCorrect ==
        (w_server_grant_calls + w_client_grant_calls) <= 2

    GrantBalanced ==
        /\ w_server_grant_calls <= 1
        /\ w_client_grant_calls <= 1

    TypeOK ==
        /\ w_granted_mode \in {0, 4}
        /\ w_list \in {"none", "waiting", "granted"}
        /\ w_server_pool \in -1..3
        /\ w_client_pool \in -1..3
        /\ w_server_grant_calls \in 0..3
        /\ w_client_grant_calls \in 0..3
        /\ h_callback_calls \in 0..3
        /\ h_cancel_waiting \subseteq {"a", "b"}
        /\ h_on_waiting_list \in BOOLEAN

    \* ========== CROSS-CUTTING SAFETY INVARIANTS ==========

    \* (a) W should not be server-granted while BL_AST is pending
    \*     (BL_AST sent but cancel not yet initiated by any canceller)
    \*     Cross-cuts: EnqueueHandler, CancellerA/B, Reprocessor
    NoGrantWhileBLASTPending ==
        (h_fl_AST_SENT /\ ~h_fl_CANCEL) => (w_server_grant_calls = 0)

    \* (b) W should not be server-granted while cancel callback is running.
    \*     The cancel RPC is sent only after callback writeback completes
    \*     (osc_cache_writeback_range hp=1 blocks synchronously), so the
    \*     server cannot see the cancel until BL_DONE is set.  ServerCancel
    \*     now correctly waits for h_fl_BL_DONE, not h_fl_CANCEL.
    \*     Cross-cuts: CancellerA/B, ServerCancel, Reprocessor
    NoGrantDuringCallback ==
        h_callback_running => (w_server_grant_calls = 0)

    \* (c) Cancelled lock should not be on waiting list (stronger than
    \*     NoCancelledOnWaiting which only checks after BL_DONE)
    \*     Cross-cuts: CancellerA/B, WaitingListAdder, CPCallback
    CancelImpliesNotWaiting ==
        h_fl_CANCEL => ~h_on_waiting_list

    \* (d) Client grant implies BL_AST callback is complete
    \*     (CP_AST completion should not be reordered with BL_AST delivery)
    \*     Cross-cuts: CancellerA/B, Reprocessor, CPCallback, AltGranter
    BLDoneBeforeClientGrant ==
        (w_client_grant_calls > 0) => h_fl_BL_DONE
end define;

\* ================================================================
\* EnqueueHandler: Server-side enqueue of waiter W
\*
\* Models: ldlm_lock_enqueue (ldlm_lock.c:1783-1949) ->
\* ldlm_lock_enqueue_helper (1750-1770) ->
\* ldlm_handle_conflict_lock (2036-2094)
\* Race window (LU-8246): lr_lock dropped at 2055 to send BL_ASTs,
\* re-taken at 2067; destroyed / granted re-checks at 2075-2088.
\* ================================================================
fair process EnqueueHandler = "enqueue"
begin
EH_Lock:
    await lr_lock = "free";
    lr_lock := "enqueue";

EH_Enqueue:
    \* W conflicts with H -> add W to waiting, queue BL_AST for H
    w_list := "waiting";
    w_fl_AST_SENT := TRUE;
    h_fl_AST_SENT := TRUE;
    \* Drop lr_lock to send BL_ASTs
    lr_lock := "free";

EH_SendBLAST:
    \* BL_AST sending -- window opens (cancellers can start)
    skip;

EH_Relock:
    await lr_lock = "free";
    lr_lock := "enqueue";

EH_Check:
    \* === FIX FOR LU-8246 ===
    if ~InjectBug8246 /\ (w_fl_DESTROYED \/ IsWGranted) then
        if IsWGranted then
            w_fl_BLOCK_GRANTED := FALSE;
        end if;
        lr_lock := "free";
        goto EH_Done;
    end if;

EH_SetBlocked:
    \* BUG 8246: set BLOCK_GRANTED even on already-granted lock
    w_fl_BLOCK_GRANTED := TRUE;
    lr_lock := "free";

EH_Done:
    skip;
end process;

\* ================================================================
\* CancellerA: First thread calling ldlm_cancel_callback on H
\* Models: ldlm_cancel_callback (ldlm_lock.c:2459-2482)
\* ================================================================
fair process CancellerA = "canceller_a"
begin
CA_Wait:
    await h_fl_AST_SENT;

CA_Lock:
    await lr_lock = "free";
    lr_lock := "canceller_a";

CA_CheckCancel:
    if ~h_fl_CANCEL then
        h_fl_CANCEL := TRUE;
        lr_lock := "free";
    else
        if ~h_fl_BL_DONE then
            if InjectBugNoWait then
                lr_lock := "free";
                goto CA_Complete;
            end if;
CA_Unlock2:
            lr_lock := "free";
            goto CA_Wait2;
        else
            lr_lock := "free";
            goto CA_Complete;
        end if;
    end if;

CA_RunCallback:
    h_callback_calls := h_callback_calls + 1;
    h_callback_running := TRUE;

CA_CallbackDone:
    h_callback_running := FALSE;

CA_Relock:
    await lr_lock = "free";
    lr_lock := "canceller_a";

CA_SetBLDone:
    h_fl_BL_DONE := TRUE;
    h_cancel_waiting := {};
    h_on_waiting_list := FALSE;
    lr_lock := "free";
    goto CA_Complete;

CA_Wait2:
    if h_fl_BL_DONE then
        goto CA_WaitRelock;
    end if;
CA_AddWait:
    h_cancel_waiting := h_cancel_waiting \union {"a"};
CA_WaitCheck:
    await h_fl_BL_DONE \/ "a" \notin h_cancel_waiting;
    if ~h_fl_BL_DONE then
        h_cancel_waiting := h_cancel_waiting \union {"a"};
        goto CA_WaitCheck;
    end if;

CA_WaitRelock:
    await lr_lock = "free";
    lr_lock := "canceller_a";
CA_WaitUnlock:
    lr_lock := "free";

CA_Complete:
    cancel_a_done := TRUE;
end process;

\* ================================================================
\* CancellerB: Second thread calling ldlm_cancel_callback on H
\* Models: ldlm_cancel_callback (ldlm_lock.c:2459-2482)
\* ================================================================
fair process CancellerB = "canceller_b"
begin
CB_Wait:
    await h_fl_AST_SENT;

CB_Lock:
    await lr_lock = "free";
    lr_lock := "canceller_b";

CB_CheckCancel:
    if ~h_fl_CANCEL then
        h_fl_CANCEL := TRUE;
        lr_lock := "free";
    else
        if ~h_fl_BL_DONE then
            if InjectBugNoWait then
                lr_lock := "free";
                goto CB_Complete;
            end if;
CB_Unlock2:
            lr_lock := "free";
            goto CB_Wait2;
        else
            lr_lock := "free";
            goto CB_Complete;
        end if;
    end if;

CB_RunCallback:
    h_callback_calls := h_callback_calls + 1;
    h_callback_running := TRUE;

CB_CallbackDone:
    h_callback_running := FALSE;

CB_Relock:
    await lr_lock = "free";
    lr_lock := "canceller_b";

CB_SetBLDone:
    h_fl_BL_DONE := TRUE;
    h_cancel_waiting := {};
    h_on_waiting_list := FALSE;
    lr_lock := "free";
    goto CB_Complete;

CB_Wait2:
    if h_fl_BL_DONE then
        goto CB_WaitRelock;
    end if;
CB_AddWait:
    h_cancel_waiting := h_cancel_waiting \union {"b"};
CB_WaitCheck:
    await h_fl_BL_DONE \/ "b" \notin h_cancel_waiting;
    if ~h_fl_BL_DONE then
        h_cancel_waiting := h_cancel_waiting \union {"b"};
        goto CB_WaitCheck;
    end if;

CB_WaitRelock:
    await lr_lock = "free";
    lr_lock := "canceller_b";
CB_WaitUnlock:
    lr_lock := "free";

CB_Complete:
    cancel_b_done := TRUE;
end process;

\* ================================================================
\* WaitingListAdder: Tries to re-add H to waiting list during
\* the cancel callback window (LU-6416)
\* Models: ldlm_add_waiting_lock (ldlm_lockd.c:440-497; the CANCEL
\* check is 461-464), reached from ldlm_server_completion_ast 1118
\* and ldlm_handle_enqueue 1487-1488.
\* ================================================================
fair process WaitingListAdder = "wl_adder"
begin
WL_Wait:
    await h_callback_running;

WL_Lock:
    await lr_lock = "free";
    lr_lock := "wl_adder";

WL_TryAdd:
    if InjectBug6416 then
        h_on_waiting_list := TRUE;
    else
        if ~h_fl_CANCEL then
            h_on_waiting_list := TRUE;
        end if;
    end if;
    lr_lock := "free";
end process;

\* ================================================================
\* ServerCancel: Server processes H's cancel and triggers reprocess.
\* Models: ldlm_request_cancel (ldlm_lockd.c:1716-1810) ->
\* ldlm_lock_cancel (ldlm_lock.c:2496-2538) -> ldlm_reprocess_all.
\*
\* The server receives the cancel RPC, which is sent by the client
\* only AFTER the cancel callback (including synchronous writeback
\* via osc_cache_writeback_range with hp=1) has completed and
\* BL_DONE is set.  Therefore the server cannot see the cancel
\* until h_fl_BL_DONE = TRUE.
\*
\* Previously this waited on h_fl_CANCEL, which incorrectly allowed
\* the server to race ahead while the client callback was still
\* running (the callback sets CANCEL first, then runs writeback,
\* then sets BL_DONE).  Fixed 2026-03-13: wait for BL_DONE.
\* ================================================================
fair process ServerCancel = "server_cancel"
begin
SC_WaitCancel:
    await h_fl_BL_DONE;

SC_Lock:
    await lr_lock = "free";
    lr_lock := "server_cancel";

SC_RemoveHolder:
    h_active := FALSE;
    lr_lock := "free";
    reprocess_ready := TRUE;
end process;

\* ================================================================
\* Reprocessor: Server-side reprocess of waiting queue.
\*
\* Models: __ldlm_reprocess_all (ldlm_lock.c:2383-2428) /
\* ldlm_reprocess_queue (1958-2020) with ERESTART handling.
\* ================================================================
fair process Reprocessor = "reprocessor"
begin
RP_WaitReady:
    await reprocess_ready;

RP_Lock:
    await lr_lock = "free";
    lr_lock := "reprocessor";
    erestart := FALSE;

RP_Scan:
    if w_list = "waiting" /\ ~w_fl_DESTROYED then
        if ~h_active then
            \* Grant W server-side
            w_server_pool := w_server_pool + 1;
            w_server_grant_calls := w_server_grant_calls + 1;
            w_fl_CP_REQD := TRUE;
            lr_lock := "free";
            cp_ready := TRUE;
            goto RP_Done;
        else
            \* Holder still active -- need BL_ASTs, drop lr_lock
            lr_lock := "free";
        end if;
    else
        lr_lock := "free";
        goto RP_Done;
    end if;

RP_BLASTWindow:
    \* BL_AST window -- holder cancel can set erestart here
    skip;

RP_Relock:
    await lr_lock = "free";
    lr_lock := "reprocessor";

RP_CheckRestart:
    if erestart /\ ~InjectBugNoRestart then
        erestart := FALSE;
        goto RP_Scan;
    end if;

RP_Finish:
    if w_list = "waiting" /\ ~w_fl_DESTROYED /\ ~h_active then
        w_server_pool := w_server_pool + 1;
        w_server_grant_calls := w_server_grant_calls + 1;
        w_fl_CP_REQD := TRUE;
        lr_lock := "free";
        cp_ready := TRUE;
    else
        lr_lock := "free";
    end if;

RP_Done:
    skip;
end process;

\* ================================================================
\* CPCallback: Client-side completion AST handler for W.
\*
\* Models: ldlm_handle_cp_callback (ldlm_lockd.c:1957-2097).
\* Race window (LU-8391): lr_lock dropped 2006-2014 around
\* ldlm_lock_change_resource; granted/destroyed re-check 2024-2029.
\* ================================================================
fair process CPCallback = "cp_callback"
begin
CP_Wait:
    await cp_ready;

CP_Lock:
    await lr_lock = "free";
    lr_lock := "cp_callback";

CP_ResourceCheck:
    if w_cp_resource /= w_resource then
        w_list := "none";
        lr_lock := "free";
    else
        goto CP_Grant;
    end if;

CP_ChangeResource:
    w_resource := w_cp_resource;
    resource_changing := TRUE;

CP_Relock:
    await lr_lock = "free";
    lr_lock := "cp_callback";

CP_8391Check:
    \* === FIX FOR LU-8391 ===
    if ~InjectBug8391 /\ (IsWGranted \/ w_fl_DESTROYED) then
        lr_lock := "free";
        goto CP_Done;
    end if;

CP_Grant:
    w_granted_mode := 4;
    w_list := "granted";
    w_client_pool := w_client_pool + 1;
    w_client_grant_calls := w_client_grant_calls + 1;
    w_fl_BLOCK_GRANTED := FALSE;
    lr_lock := "free";

CP_Done:
    lifecycle_done := TRUE;
end process;

\* ================================================================
\* AltGranter: Another client-side thread that can grant W during
\* CPCallback's resource change window (LU-8391 race).
\* Models: any other path calling ldlm_grant_lock on W (e.g. a resent
\* CP AST in ldlm_handle_cp_callback) while lr_lock is dropped
\* between ldlm_lockd.c:2006 and 2014.
\* ================================================================
fair process AltGranter = "alt_granter"
begin
AG_Wait:
    await resource_changing;

AG_Lock:
    await lr_lock = "free";
    lr_lock := "alt_granter";

AG_Grant:
    if ~IsWGranted /\ ~w_fl_DESTROYED /\ w_list /= "granted" then
        w_granted_mode := 4;
        w_list := "granted";
        w_client_pool := w_client_pool + 1;
        w_client_grant_calls := w_client_grant_calls + 1;
        w_fl_BLOCK_GRANTED := FALSE;
    end if;
    lr_lock := "free";
end process;

end algorithm; *)

\* BEGIN TRANSLATION - theass needs to be removed
VARIABLES lr_lock, h_active, h_fl_CANCEL, h_fl_BL_DONE, h_fl_AST_SENT,
          h_callback_calls, h_callback_running, h_on_waiting_list,
          h_cancel_waiting, w_list, w_fl_AST_SENT, w_fl_CP_REQD,
          w_fl_BLOCK_GRANTED, w_fl_DESTROYED, w_granted_mode, w_resource,
          w_cp_resource, w_server_grant_calls, w_client_grant_calls,
          w_server_pool, w_client_pool, erestart, reprocess_ready, cp_ready,
          resource_changing, lifecycle_done, cancel_a_done, cancel_b_done, pc

(* define statement *)
IsWGranted == w_granted_mode = 4



NoDoubleServerGrant == w_server_grant_calls <= 1
NoDoubleClientGrant == w_client_grant_calls <= 1
ServerPoolCorrect == w_server_pool <= 1
ClientPoolCorrect == w_client_pool <= 1


FlagConsistency ==
    (lifecycle_done /\ IsWGranted /\ w_list = "granted")
        => ~w_fl_BLOCK_GRANTED

CancelCallbackOnce == h_callback_calls <= 1
BLDoneImpliesCancel == h_fl_BL_DONE => h_fl_CANCEL
NoCancelledOnWaiting == h_fl_BL_DONE => ~h_on_waiting_list

NoGrantWhileHeld ==
    h_active => (w_list /= "granted" /\ w_server_grant_calls = 0)

CancelPostCondition ==
    (cancel_a_done /\ cancel_b_done) =>
        (h_fl_CANCEL /\ h_fl_BL_DONE)

TotalGrantCorrect ==
    (w_server_grant_calls + w_client_grant_calls) <= 2

GrantBalanced ==
    /\ w_server_grant_calls <= 1
    /\ w_client_grant_calls <= 1

TypeOK ==
    /\ w_granted_mode \in {0, 4}
    /\ w_list \in {"none", "waiting", "granted"}
    /\ w_server_pool \in -1..3
    /\ w_client_pool \in -1..3
    /\ w_server_grant_calls \in 0..3
    /\ w_client_grant_calls \in 0..3
    /\ h_callback_calls \in 0..3
    /\ h_cancel_waiting \subseteq {"a", "b"}
    /\ h_on_waiting_list \in BOOLEAN

NoGrantWhileBLASTPending ==
    (h_fl_AST_SENT /\ ~h_fl_CANCEL) => (w_server_grant_calls = 0)

NoGrantDuringCallback ==
    h_callback_running => (w_server_grant_calls = 0)

CancelImpliesNotWaiting ==
    h_fl_CANCEL => ~h_on_waiting_list

BLDoneBeforeClientGrant ==
    (w_client_grant_calls > 0) => h_fl_BL_DONE


vars == << lr_lock, h_active, h_fl_CANCEL, h_fl_BL_DONE, h_fl_AST_SENT,
           h_callback_calls, h_callback_running, h_on_waiting_list,
           h_cancel_waiting, w_list, w_fl_AST_SENT, w_fl_CP_REQD,
           w_fl_BLOCK_GRANTED, w_fl_DESTROYED, w_granted_mode, w_resource,
           w_cp_resource, w_server_grant_calls, w_client_grant_calls,
           w_server_pool, w_client_pool, erestart, reprocess_ready, cp_ready,
           resource_changing, lifecycle_done, cancel_a_done, cancel_b_done,
           pc >>

ProcSet == {"enqueue"} \cup {"canceller_a"} \cup {"canceller_b"} \cup {"wl_adder"} \cup {"server_cancel"} \cup {"reprocessor"} \cup {"cp_callback"} \cup {"alt_granter"}

Init == (* Global variables *)
        /\ lr_lock = "free"
        /\ h_active = TRUE
        /\ h_fl_CANCEL = FALSE
        /\ h_fl_BL_DONE = FALSE
        /\ h_fl_AST_SENT = FALSE
        /\ h_callback_calls = 0
        /\ h_callback_running = FALSE
        /\ h_on_waiting_list = FALSE
        /\ h_cancel_waiting = {}
        /\ w_list = "none"
        /\ w_fl_AST_SENT = FALSE
        /\ w_fl_CP_REQD = FALSE
        /\ w_fl_BLOCK_GRANTED = FALSE
        /\ w_fl_DESTROYED = FALSE
        /\ w_granted_mode = 0
        /\ w_resource = "R1"
        /\ w_cp_resource = "R2"
        /\ w_server_grant_calls = 0
        /\ w_client_grant_calls = 0
        /\ w_server_pool = 0
        /\ w_client_pool = 0
        /\ erestart = FALSE
        /\ reprocess_ready = FALSE
        /\ cp_ready = FALSE
        /\ resource_changing = FALSE
        /\ lifecycle_done = FALSE
        /\ cancel_a_done = FALSE
        /\ cancel_b_done = FALSE
        /\ pc = [self \in ProcSet |-> CASE self = "enqueue" -> "EH_Lock"
                                        [] self = "canceller_a" -> "CA_Wait"
                                        [] self = "canceller_b" -> "CB_Wait"
                                        [] self = "wl_adder" -> "WL_Wait"
                                        [] self = "server_cancel" -> "SC_WaitCancel"
                                        [] self = "reprocessor" -> "RP_WaitReady"
                                        [] self = "cp_callback" -> "CP_Wait"
                                        [] self = "alt_granter" -> "AG_Wait"]

EH_Lock == /\ pc["enqueue"] = "EH_Lock"
           /\ lr_lock = "free"
           /\ lr_lock' = "enqueue"
           /\ pc' = [pc EXCEPT !["enqueue"] = "EH_Enqueue"]
           /\ UNCHANGED << h_active, h_fl_CANCEL, h_fl_BL_DONE, h_fl_AST_SENT,
                           h_callback_calls, h_callback_running,
                           h_on_waiting_list, h_cancel_waiting, w_list,
                           w_fl_AST_SENT, w_fl_CP_REQD, w_fl_BLOCK_GRANTED,
                           w_fl_DESTROYED, w_granted_mode, w_resource,
                           w_cp_resource, w_server_grant_calls,
                           w_client_grant_calls, w_server_pool, w_client_pool,
                           erestart, reprocess_ready, cp_ready,
                           resource_changing, lifecycle_done, cancel_a_done,
                           cancel_b_done >>

EH_Enqueue == /\ pc["enqueue"] = "EH_Enqueue"
              /\ w_list' = "waiting"
              /\ w_fl_AST_SENT' = TRUE
              /\ h_fl_AST_SENT' = TRUE
              /\ lr_lock' = "free"
              /\ pc' = [pc EXCEPT !["enqueue"] = "EH_SendBLAST"]
              /\ UNCHANGED << h_active, h_fl_CANCEL, h_fl_BL_DONE,
                              h_callback_calls, h_callback_running,
                              h_on_waiting_list, h_cancel_waiting,
                              w_fl_CP_REQD, w_fl_BLOCK_GRANTED, w_fl_DESTROYED,
                              w_granted_mode, w_resource, w_cp_resource,
                              w_server_grant_calls, w_client_grant_calls,
                              w_server_pool, w_client_pool, erestart,
                              reprocess_ready, cp_ready, resource_changing,
                              lifecycle_done, cancel_a_done, cancel_b_done >>

EH_SendBLAST == /\ pc["enqueue"] = "EH_SendBLAST"
                /\ TRUE
                /\ pc' = [pc EXCEPT !["enqueue"] = "EH_Relock"]
                /\ UNCHANGED << lr_lock, h_active, h_fl_CANCEL, h_fl_BL_DONE,
                                h_fl_AST_SENT, h_callback_calls,
                                h_callback_running, h_on_waiting_list,
                                h_cancel_waiting, w_list, w_fl_AST_SENT,
                                w_fl_CP_REQD, w_fl_BLOCK_GRANTED,
                                w_fl_DESTROYED, w_granted_mode, w_resource,
                                w_cp_resource, w_server_grant_calls,
                                w_client_grant_calls, w_server_pool,
                                w_client_pool, erestart, reprocess_ready,
                                cp_ready, resource_changing, lifecycle_done,
                                cancel_a_done, cancel_b_done >>

EH_Relock == /\ pc["enqueue"] = "EH_Relock"
             /\ lr_lock = "free"
             /\ lr_lock' = "enqueue"
             /\ pc' = [pc EXCEPT !["enqueue"] = "EH_Check"]
             /\ UNCHANGED << h_active, h_fl_CANCEL, h_fl_BL_DONE,
                             h_fl_AST_SENT, h_callback_calls,
                             h_callback_running, h_on_waiting_list,
                             h_cancel_waiting, w_list, w_fl_AST_SENT,
                             w_fl_CP_REQD, w_fl_BLOCK_GRANTED, w_fl_DESTROYED,
                             w_granted_mode, w_resource, w_cp_resource,
                             w_server_grant_calls, w_client_grant_calls,
                             w_server_pool, w_client_pool, erestart,
                             reprocess_ready, cp_ready, resource_changing,
                             lifecycle_done, cancel_a_done, cancel_b_done >>

EH_Check == /\ pc["enqueue"] = "EH_Check"
            /\ IF ~InjectBug8246 /\ (w_fl_DESTROYED \/ IsWGranted)
                  THEN /\ IF IsWGranted
                             THEN /\ w_fl_BLOCK_GRANTED' = FALSE
                             ELSE /\ TRUE
                                  /\ UNCHANGED w_fl_BLOCK_GRANTED
                       /\ lr_lock' = "free"
                       /\ pc' = [pc EXCEPT !["enqueue"] = "EH_Done"]
                  ELSE /\ pc' = [pc EXCEPT !["enqueue"] = "EH_SetBlocked"]
                       /\ UNCHANGED << lr_lock, w_fl_BLOCK_GRANTED >>
            /\ UNCHANGED << h_active, h_fl_CANCEL, h_fl_BL_DONE, h_fl_AST_SENT,
                            h_callback_calls, h_callback_running,
                            h_on_waiting_list, h_cancel_waiting, w_list,
                            w_fl_AST_SENT, w_fl_CP_REQD, w_fl_DESTROYED,
                            w_granted_mode, w_resource, w_cp_resource,
                            w_server_grant_calls, w_client_grant_calls,
                            w_server_pool, w_client_pool, erestart,
                            reprocess_ready, cp_ready, resource_changing,
                            lifecycle_done, cancel_a_done, cancel_b_done >>

EH_SetBlocked == /\ pc["enqueue"] = "EH_SetBlocked"
                 /\ w_fl_BLOCK_GRANTED' = TRUE
                 /\ lr_lock' = "free"
                 /\ pc' = [pc EXCEPT !["enqueue"] = "EH_Done"]
                 /\ UNCHANGED << h_active, h_fl_CANCEL, h_fl_BL_DONE,
                                 h_fl_AST_SENT, h_callback_calls,
                                 h_callback_running, h_on_waiting_list,
                                 h_cancel_waiting, w_list, w_fl_AST_SENT,
                                 w_fl_CP_REQD, w_fl_DESTROYED, w_granted_mode,
                                 w_resource, w_cp_resource,
                                 w_server_grant_calls, w_client_grant_calls,
                                 w_server_pool, w_client_pool, erestart,
                                 reprocess_ready, cp_ready, resource_changing,
                                 lifecycle_done, cancel_a_done, cancel_b_done >>

EH_Done == /\ pc["enqueue"] = "EH_Done"
           /\ TRUE
           /\ pc' = [pc EXCEPT !["enqueue"] = "Done"]
           /\ UNCHANGED << lr_lock, h_active, h_fl_CANCEL, h_fl_BL_DONE,
                           h_fl_AST_SENT, h_callback_calls, h_callback_running,
                           h_on_waiting_list, h_cancel_waiting, w_list,
                           w_fl_AST_SENT, w_fl_CP_REQD, w_fl_BLOCK_GRANTED,
                           w_fl_DESTROYED, w_granted_mode, w_resource,
                           w_cp_resource, w_server_grant_calls,
                           w_client_grant_calls, w_server_pool, w_client_pool,
                           erestart, reprocess_ready, cp_ready,
                           resource_changing, lifecycle_done, cancel_a_done,
                           cancel_b_done >>

EnqueueHandler == EH_Lock \/ EH_Enqueue \/ EH_SendBLAST \/ EH_Relock
                     \/ EH_Check \/ EH_SetBlocked \/ EH_Done

CA_Wait == /\ pc["canceller_a"] = "CA_Wait"
           /\ h_fl_AST_SENT
           /\ pc' = [pc EXCEPT !["canceller_a"] = "CA_Lock"]
           /\ UNCHANGED << lr_lock, h_active, h_fl_CANCEL, h_fl_BL_DONE,
                           h_fl_AST_SENT, h_callback_calls, h_callback_running,
                           h_on_waiting_list, h_cancel_waiting, w_list,
                           w_fl_AST_SENT, w_fl_CP_REQD, w_fl_BLOCK_GRANTED,
                           w_fl_DESTROYED, w_granted_mode, w_resource,
                           w_cp_resource, w_server_grant_calls,
                           w_client_grant_calls, w_server_pool, w_client_pool,
                           erestart, reprocess_ready, cp_ready,
                           resource_changing, lifecycle_done, cancel_a_done,
                           cancel_b_done >>

CA_Lock == /\ pc["canceller_a"] = "CA_Lock"
           /\ lr_lock = "free"
           /\ lr_lock' = "canceller_a"
           /\ pc' = [pc EXCEPT !["canceller_a"] = "CA_CheckCancel"]
           /\ UNCHANGED << h_active, h_fl_CANCEL, h_fl_BL_DONE, h_fl_AST_SENT,
                           h_callback_calls, h_callback_running,
                           h_on_waiting_list, h_cancel_waiting, w_list,
                           w_fl_AST_SENT, w_fl_CP_REQD, w_fl_BLOCK_GRANTED,
                           w_fl_DESTROYED, w_granted_mode, w_resource,
                           w_cp_resource, w_server_grant_calls,
                           w_client_grant_calls, w_server_pool, w_client_pool,
                           erestart, reprocess_ready, cp_ready,
                           resource_changing, lifecycle_done, cancel_a_done,
                           cancel_b_done >>

CA_CheckCancel == /\ pc["canceller_a"] = "CA_CheckCancel"
                  /\ IF ~h_fl_CANCEL
                        THEN /\ h_fl_CANCEL' = TRUE
                             /\ lr_lock' = "free"
                             /\ pc' = [pc EXCEPT !["canceller_a"] = "CA_RunCallback"]
                        ELSE /\ IF ~h_fl_BL_DONE
                                   THEN /\ IF InjectBugNoWait
                                              THEN /\ lr_lock' = "free"
                                                   /\ pc' = [pc EXCEPT !["canceller_a"] = "CA_Complete"]
                                              ELSE /\ pc' = [pc EXCEPT !["canceller_a"] = "CA_Unlock2"]
                                                   /\ UNCHANGED lr_lock
                                   ELSE /\ lr_lock' = "free"
                                        /\ pc' = [pc EXCEPT !["canceller_a"] = "CA_Complete"]
                             /\ UNCHANGED h_fl_CANCEL
                  /\ UNCHANGED << h_active, h_fl_BL_DONE, h_fl_AST_SENT,
                                  h_callback_calls, h_callback_running,
                                  h_on_waiting_list, h_cancel_waiting, w_list,
                                  w_fl_AST_SENT, w_fl_CP_REQD,
                                  w_fl_BLOCK_GRANTED, w_fl_DESTROYED,
                                  w_granted_mode, w_resource, w_cp_resource,
                                  w_server_grant_calls, w_client_grant_calls,
                                  w_server_pool, w_client_pool, erestart,
                                  reprocess_ready, cp_ready, resource_changing,
                                  lifecycle_done, cancel_a_done, cancel_b_done >>

CA_Unlock2 == /\ pc["canceller_a"] = "CA_Unlock2"
              /\ lr_lock' = "free"
              /\ pc' = [pc EXCEPT !["canceller_a"] = "CA_Wait2"]
              /\ UNCHANGED << h_active, h_fl_CANCEL, h_fl_BL_DONE,
                              h_fl_AST_SENT, h_callback_calls,
                              h_callback_running, h_on_waiting_list,
                              h_cancel_waiting, w_list, w_fl_AST_SENT,
                              w_fl_CP_REQD, w_fl_BLOCK_GRANTED, w_fl_DESTROYED,
                              w_granted_mode, w_resource, w_cp_resource,
                              w_server_grant_calls, w_client_grant_calls,
                              w_server_pool, w_client_pool, erestart,
                              reprocess_ready, cp_ready, resource_changing,
                              lifecycle_done, cancel_a_done, cancel_b_done >>

CA_RunCallback == /\ pc["canceller_a"] = "CA_RunCallback"
                  /\ h_callback_calls' = h_callback_calls + 1
                  /\ h_callback_running' = TRUE
                  /\ pc' = [pc EXCEPT !["canceller_a"] = "CA_CallbackDone"]
                  /\ UNCHANGED << lr_lock, h_active, h_fl_CANCEL, h_fl_BL_DONE,
                                  h_fl_AST_SENT, h_on_waiting_list,
                                  h_cancel_waiting, w_list, w_fl_AST_SENT,
                                  w_fl_CP_REQD, w_fl_BLOCK_GRANTED,
                                  w_fl_DESTROYED, w_granted_mode, w_resource,
                                  w_cp_resource, w_server_grant_calls,
                                  w_client_grant_calls, w_server_pool,
                                  w_client_pool, erestart, reprocess_ready,
                                  cp_ready, resource_changing, lifecycle_done,
                                  cancel_a_done, cancel_b_done >>

CA_CallbackDone == /\ pc["canceller_a"] = "CA_CallbackDone"
                   /\ h_callback_running' = FALSE
                   /\ pc' = [pc EXCEPT !["canceller_a"] = "CA_Relock"]
                   /\ UNCHANGED << lr_lock, h_active, h_fl_CANCEL,
                                   h_fl_BL_DONE, h_fl_AST_SENT,
                                   h_callback_calls, h_on_waiting_list,
                                   h_cancel_waiting, w_list, w_fl_AST_SENT,
                                   w_fl_CP_REQD, w_fl_BLOCK_GRANTED,
                                   w_fl_DESTROYED, w_granted_mode, w_resource,
                                   w_cp_resource, w_server_grant_calls,
                                   w_client_grant_calls, w_server_pool,
                                   w_client_pool, erestart, reprocess_ready,
                                   cp_ready, resource_changing, lifecycle_done,
                                   cancel_a_done, cancel_b_done >>

CA_Relock == /\ pc["canceller_a"] = "CA_Relock"
             /\ lr_lock = "free"
             /\ lr_lock' = "canceller_a"
             /\ pc' = [pc EXCEPT !["canceller_a"] = "CA_SetBLDone"]
             /\ UNCHANGED << h_active, h_fl_CANCEL, h_fl_BL_DONE,
                             h_fl_AST_SENT, h_callback_calls,
                             h_callback_running, h_on_waiting_list,
                             h_cancel_waiting, w_list, w_fl_AST_SENT,
                             w_fl_CP_REQD, w_fl_BLOCK_GRANTED, w_fl_DESTROYED,
                             w_granted_mode, w_resource, w_cp_resource,
                             w_server_grant_calls, w_client_grant_calls,
                             w_server_pool, w_client_pool, erestart,
                             reprocess_ready, cp_ready, resource_changing,
                             lifecycle_done, cancel_a_done, cancel_b_done >>

CA_SetBLDone == /\ pc["canceller_a"] = "CA_SetBLDone"
                /\ h_fl_BL_DONE' = TRUE
                /\ h_cancel_waiting' = {}
                /\ h_on_waiting_list' = FALSE
                /\ lr_lock' = "free"
                /\ pc' = [pc EXCEPT !["canceller_a"] = "CA_Complete"]
                /\ UNCHANGED << h_active, h_fl_CANCEL, h_fl_AST_SENT,
                                h_callback_calls, h_callback_running, w_list,
                                w_fl_AST_SENT, w_fl_CP_REQD,
                                w_fl_BLOCK_GRANTED, w_fl_DESTROYED,
                                w_granted_mode, w_resource, w_cp_resource,
                                w_server_grant_calls, w_client_grant_calls,
                                w_server_pool, w_client_pool, erestart,
                                reprocess_ready, cp_ready, resource_changing,
                                lifecycle_done, cancel_a_done, cancel_b_done >>

CA_Wait2 == /\ pc["canceller_a"] = "CA_Wait2"
            /\ IF h_fl_BL_DONE
                  THEN /\ pc' = [pc EXCEPT !["canceller_a"] = "CA_WaitRelock"]
                  ELSE /\ pc' = [pc EXCEPT !["canceller_a"] = "CA_AddWait"]
            /\ UNCHANGED << lr_lock, h_active, h_fl_CANCEL, h_fl_BL_DONE,
                            h_fl_AST_SENT, h_callback_calls,
                            h_callback_running, h_on_waiting_list,
                            h_cancel_waiting, w_list, w_fl_AST_SENT,
                            w_fl_CP_REQD, w_fl_BLOCK_GRANTED, w_fl_DESTROYED,
                            w_granted_mode, w_resource, w_cp_resource,
                            w_server_grant_calls, w_client_grant_calls,
                            w_server_pool, w_client_pool, erestart,
                            reprocess_ready, cp_ready, resource_changing,
                            lifecycle_done, cancel_a_done, cancel_b_done >>

CA_AddWait == /\ pc["canceller_a"] = "CA_AddWait"
              /\ h_cancel_waiting' = (h_cancel_waiting \union {"a"})
              /\ pc' = [pc EXCEPT !["canceller_a"] = "CA_WaitCheck"]
              /\ UNCHANGED << lr_lock, h_active, h_fl_CANCEL, h_fl_BL_DONE,
                              h_fl_AST_SENT, h_callback_calls,
                              h_callback_running, h_on_waiting_list, w_list,
                              w_fl_AST_SENT, w_fl_CP_REQD, w_fl_BLOCK_GRANTED,
                              w_fl_DESTROYED, w_granted_mode, w_resource,
                              w_cp_resource, w_server_grant_calls,
                              w_client_grant_calls, w_server_pool,
                              w_client_pool, erestart, reprocess_ready,
                              cp_ready, resource_changing, lifecycle_done,
                              cancel_a_done, cancel_b_done >>

CA_WaitCheck == /\ pc["canceller_a"] = "CA_WaitCheck"
                /\ h_fl_BL_DONE \/ "a" \notin h_cancel_waiting
                /\ IF ~h_fl_BL_DONE
                      THEN /\ h_cancel_waiting' = (h_cancel_waiting \union {"a"})
                           /\ pc' = [pc EXCEPT !["canceller_a"] = "CA_WaitCheck"]
                      ELSE /\ pc' = [pc EXCEPT !["canceller_a"] = "CA_WaitRelock"]
                           /\ UNCHANGED h_cancel_waiting
                /\ UNCHANGED << lr_lock, h_active, h_fl_CANCEL, h_fl_BL_DONE,
                                h_fl_AST_SENT, h_callback_calls,
                                h_callback_running, h_on_waiting_list, w_list,
                                w_fl_AST_SENT, w_fl_CP_REQD,
                                w_fl_BLOCK_GRANTED, w_fl_DESTROYED,
                                w_granted_mode, w_resource, w_cp_resource,
                                w_server_grant_calls, w_client_grant_calls,
                                w_server_pool, w_client_pool, erestart,
                                reprocess_ready, cp_ready, resource_changing,
                                lifecycle_done, cancel_a_done, cancel_b_done >>

CA_WaitRelock == /\ pc["canceller_a"] = "CA_WaitRelock"
                 /\ lr_lock = "free"
                 /\ lr_lock' = "canceller_a"
                 /\ pc' = [pc EXCEPT !["canceller_a"] = "CA_WaitUnlock"]
                 /\ UNCHANGED << h_active, h_fl_CANCEL, h_fl_BL_DONE,
                                 h_fl_AST_SENT, h_callback_calls,
                                 h_callback_running, h_on_waiting_list,
                                 h_cancel_waiting, w_list, w_fl_AST_SENT,
                                 w_fl_CP_REQD, w_fl_BLOCK_GRANTED,
                                 w_fl_DESTROYED, w_granted_mode, w_resource,
                                 w_cp_resource, w_server_grant_calls,
                                 w_client_grant_calls, w_server_pool,
                                 w_client_pool, erestart, reprocess_ready,
                                 cp_ready, resource_changing, lifecycle_done,
                                 cancel_a_done, cancel_b_done >>

CA_WaitUnlock == /\ pc["canceller_a"] = "CA_WaitUnlock"
                 /\ lr_lock' = "free"
                 /\ pc' = [pc EXCEPT !["canceller_a"] = "CA_Complete"]
                 /\ UNCHANGED << h_active, h_fl_CANCEL, h_fl_BL_DONE,
                                 h_fl_AST_SENT, h_callback_calls,
                                 h_callback_running, h_on_waiting_list,
                                 h_cancel_waiting, w_list, w_fl_AST_SENT,
                                 w_fl_CP_REQD, w_fl_BLOCK_GRANTED,
                                 w_fl_DESTROYED, w_granted_mode, w_resource,
                                 w_cp_resource, w_server_grant_calls,
                                 w_client_grant_calls, w_server_pool,
                                 w_client_pool, erestart, reprocess_ready,
                                 cp_ready, resource_changing, lifecycle_done,
                                 cancel_a_done, cancel_b_done >>

CA_Complete == /\ pc["canceller_a"] = "CA_Complete"
               /\ cancel_a_done' = TRUE
               /\ pc' = [pc EXCEPT !["canceller_a"] = "Done"]
               /\ UNCHANGED << lr_lock, h_active, h_fl_CANCEL, h_fl_BL_DONE,
                               h_fl_AST_SENT, h_callback_calls,
                               h_callback_running, h_on_waiting_list,
                               h_cancel_waiting, w_list, w_fl_AST_SENT,
                               w_fl_CP_REQD, w_fl_BLOCK_GRANTED,
                               w_fl_DESTROYED, w_granted_mode, w_resource,
                               w_cp_resource, w_server_grant_calls,
                               w_client_grant_calls, w_server_pool,
                               w_client_pool, erestart, reprocess_ready,
                               cp_ready, resource_changing, lifecycle_done,
                               cancel_b_done >>

CancellerA == CA_Wait \/ CA_Lock \/ CA_CheckCancel \/ CA_Unlock2
                 \/ CA_RunCallback \/ CA_CallbackDone \/ CA_Relock
                 \/ CA_SetBLDone \/ CA_Wait2 \/ CA_AddWait \/ CA_WaitCheck
                 \/ CA_WaitRelock \/ CA_WaitUnlock \/ CA_Complete

CB_Wait == /\ pc["canceller_b"] = "CB_Wait"
           /\ h_fl_AST_SENT
           /\ pc' = [pc EXCEPT !["canceller_b"] = "CB_Lock"]
           /\ UNCHANGED << lr_lock, h_active, h_fl_CANCEL, h_fl_BL_DONE,
                           h_fl_AST_SENT, h_callback_calls, h_callback_running,
                           h_on_waiting_list, h_cancel_waiting, w_list,
                           w_fl_AST_SENT, w_fl_CP_REQD, w_fl_BLOCK_GRANTED,
                           w_fl_DESTROYED, w_granted_mode, w_resource,
                           w_cp_resource, w_server_grant_calls,
                           w_client_grant_calls, w_server_pool, w_client_pool,
                           erestart, reprocess_ready, cp_ready,
                           resource_changing, lifecycle_done, cancel_a_done,
                           cancel_b_done >>

CB_Lock == /\ pc["canceller_b"] = "CB_Lock"
           /\ lr_lock = "free"
           /\ lr_lock' = "canceller_b"
           /\ pc' = [pc EXCEPT !["canceller_b"] = "CB_CheckCancel"]
           /\ UNCHANGED << h_active, h_fl_CANCEL, h_fl_BL_DONE, h_fl_AST_SENT,
                           h_callback_calls, h_callback_running,
                           h_on_waiting_list, h_cancel_waiting, w_list,
                           w_fl_AST_SENT, w_fl_CP_REQD, w_fl_BLOCK_GRANTED,
                           w_fl_DESTROYED, w_granted_mode, w_resource,
                           w_cp_resource, w_server_grant_calls,
                           w_client_grant_calls, w_server_pool, w_client_pool,
                           erestart, reprocess_ready, cp_ready,
                           resource_changing, lifecycle_done, cancel_a_done,
                           cancel_b_done >>

CB_CheckCancel == /\ pc["canceller_b"] = "CB_CheckCancel"
                  /\ IF ~h_fl_CANCEL
                        THEN /\ h_fl_CANCEL' = TRUE
                             /\ lr_lock' = "free"
                             /\ pc' = [pc EXCEPT !["canceller_b"] = "CB_RunCallback"]
                        ELSE /\ IF ~h_fl_BL_DONE
                                   THEN /\ IF InjectBugNoWait
                                              THEN /\ lr_lock' = "free"
                                                   /\ pc' = [pc EXCEPT !["canceller_b"] = "CB_Complete"]
                                              ELSE /\ pc' = [pc EXCEPT !["canceller_b"] = "CB_Unlock2"]
                                                   /\ UNCHANGED lr_lock
                                   ELSE /\ lr_lock' = "free"
                                        /\ pc' = [pc EXCEPT !["canceller_b"] = "CB_Complete"]
                             /\ UNCHANGED h_fl_CANCEL
                  /\ UNCHANGED << h_active, h_fl_BL_DONE, h_fl_AST_SENT,
                                  h_callback_calls, h_callback_running,
                                  h_on_waiting_list, h_cancel_waiting, w_list,
                                  w_fl_AST_SENT, w_fl_CP_REQD,
                                  w_fl_BLOCK_GRANTED, w_fl_DESTROYED,
                                  w_granted_mode, w_resource, w_cp_resource,
                                  w_server_grant_calls, w_client_grant_calls,
                                  w_server_pool, w_client_pool, erestart,
                                  reprocess_ready, cp_ready, resource_changing,
                                  lifecycle_done, cancel_a_done, cancel_b_done >>

CB_Unlock2 == /\ pc["canceller_b"] = "CB_Unlock2"
              /\ lr_lock' = "free"
              /\ pc' = [pc EXCEPT !["canceller_b"] = "CB_Wait2"]
              /\ UNCHANGED << h_active, h_fl_CANCEL, h_fl_BL_DONE,
                              h_fl_AST_SENT, h_callback_calls,
                              h_callback_running, h_on_waiting_list,
                              h_cancel_waiting, w_list, w_fl_AST_SENT,
                              w_fl_CP_REQD, w_fl_BLOCK_GRANTED, w_fl_DESTROYED,
                              w_granted_mode, w_resource, w_cp_resource,
                              w_server_grant_calls, w_client_grant_calls,
                              w_server_pool, w_client_pool, erestart,
                              reprocess_ready, cp_ready, resource_changing,
                              lifecycle_done, cancel_a_done, cancel_b_done >>

CB_RunCallback == /\ pc["canceller_b"] = "CB_RunCallback"
                  /\ h_callback_calls' = h_callback_calls + 1
                  /\ h_callback_running' = TRUE
                  /\ pc' = [pc EXCEPT !["canceller_b"] = "CB_CallbackDone"]
                  /\ UNCHANGED << lr_lock, h_active, h_fl_CANCEL, h_fl_BL_DONE,
                                  h_fl_AST_SENT, h_on_waiting_list,
                                  h_cancel_waiting, w_list, w_fl_AST_SENT,
                                  w_fl_CP_REQD, w_fl_BLOCK_GRANTED,
                                  w_fl_DESTROYED, w_granted_mode, w_resource,
                                  w_cp_resource, w_server_grant_calls,
                                  w_client_grant_calls, w_server_pool,
                                  w_client_pool, erestart, reprocess_ready,
                                  cp_ready, resource_changing, lifecycle_done,
                                  cancel_a_done, cancel_b_done >>

CB_CallbackDone == /\ pc["canceller_b"] = "CB_CallbackDone"
                   /\ h_callback_running' = FALSE
                   /\ pc' = [pc EXCEPT !["canceller_b"] = "CB_Relock"]
                   /\ UNCHANGED << lr_lock, h_active, h_fl_CANCEL,
                                   h_fl_BL_DONE, h_fl_AST_SENT,
                                   h_callback_calls, h_on_waiting_list,
                                   h_cancel_waiting, w_list, w_fl_AST_SENT,
                                   w_fl_CP_REQD, w_fl_BLOCK_GRANTED,
                                   w_fl_DESTROYED, w_granted_mode, w_resource,
                                   w_cp_resource, w_server_grant_calls,
                                   w_client_grant_calls, w_server_pool,
                                   w_client_pool, erestart, reprocess_ready,
                                   cp_ready, resource_changing, lifecycle_done,
                                   cancel_a_done, cancel_b_done >>

CB_Relock == /\ pc["canceller_b"] = "CB_Relock"
             /\ lr_lock = "free"
             /\ lr_lock' = "canceller_b"
             /\ pc' = [pc EXCEPT !["canceller_b"] = "CB_SetBLDone"]
             /\ UNCHANGED << h_active, h_fl_CANCEL, h_fl_BL_DONE,
                             h_fl_AST_SENT, h_callback_calls,
                             h_callback_running, h_on_waiting_list,
                             h_cancel_waiting, w_list, w_fl_AST_SENT,
                             w_fl_CP_REQD, w_fl_BLOCK_GRANTED, w_fl_DESTROYED,
                             w_granted_mode, w_resource, w_cp_resource,
                             w_server_grant_calls, w_client_grant_calls,
                             w_server_pool, w_client_pool, erestart,
                             reprocess_ready, cp_ready, resource_changing,
                             lifecycle_done, cancel_a_done, cancel_b_done >>

CB_SetBLDone == /\ pc["canceller_b"] = "CB_SetBLDone"
                /\ h_fl_BL_DONE' = TRUE
                /\ h_cancel_waiting' = {}
                /\ h_on_waiting_list' = FALSE
                /\ lr_lock' = "free"
                /\ pc' = [pc EXCEPT !["canceller_b"] = "CB_Complete"]
                /\ UNCHANGED << h_active, h_fl_CANCEL, h_fl_AST_SENT,
                                h_callback_calls, h_callback_running, w_list,
                                w_fl_AST_SENT, w_fl_CP_REQD,
                                w_fl_BLOCK_GRANTED, w_fl_DESTROYED,
                                w_granted_mode, w_resource, w_cp_resource,
                                w_server_grant_calls, w_client_grant_calls,
                                w_server_pool, w_client_pool, erestart,
                                reprocess_ready, cp_ready, resource_changing,
                                lifecycle_done, cancel_a_done, cancel_b_done >>

CB_Wait2 == /\ pc["canceller_b"] = "CB_Wait2"
            /\ IF h_fl_BL_DONE
                  THEN /\ pc' = [pc EXCEPT !["canceller_b"] = "CB_WaitRelock"]
                  ELSE /\ pc' = [pc EXCEPT !["canceller_b"] = "CB_AddWait"]
            /\ UNCHANGED << lr_lock, h_active, h_fl_CANCEL, h_fl_BL_DONE,
                            h_fl_AST_SENT, h_callback_calls,
                            h_callback_running, h_on_waiting_list,
                            h_cancel_waiting, w_list, w_fl_AST_SENT,
                            w_fl_CP_REQD, w_fl_BLOCK_GRANTED, w_fl_DESTROYED,
                            w_granted_mode, w_resource, w_cp_resource,
                            w_server_grant_calls, w_client_grant_calls,
                            w_server_pool, w_client_pool, erestart,
                            reprocess_ready, cp_ready, resource_changing,
                            lifecycle_done, cancel_a_done, cancel_b_done >>

CB_AddWait == /\ pc["canceller_b"] = "CB_AddWait"
              /\ h_cancel_waiting' = (h_cancel_waiting \union {"b"})
              /\ pc' = [pc EXCEPT !["canceller_b"] = "CB_WaitCheck"]
              /\ UNCHANGED << lr_lock, h_active, h_fl_CANCEL, h_fl_BL_DONE,
                              h_fl_AST_SENT, h_callback_calls,
                              h_callback_running, h_on_waiting_list, w_list,
                              w_fl_AST_SENT, w_fl_CP_REQD, w_fl_BLOCK_GRANTED,
                              w_fl_DESTROYED, w_granted_mode, w_resource,
                              w_cp_resource, w_server_grant_calls,
                              w_client_grant_calls, w_server_pool,
                              w_client_pool, erestart, reprocess_ready,
                              cp_ready, resource_changing, lifecycle_done,
                              cancel_a_done, cancel_b_done >>

CB_WaitCheck == /\ pc["canceller_b"] = "CB_WaitCheck"
                /\ h_fl_BL_DONE \/ "b" \notin h_cancel_waiting
                /\ IF ~h_fl_BL_DONE
                      THEN /\ h_cancel_waiting' = (h_cancel_waiting \union {"b"})
                           /\ pc' = [pc EXCEPT !["canceller_b"] = "CB_WaitCheck"]
                      ELSE /\ pc' = [pc EXCEPT !["canceller_b"] = "CB_WaitRelock"]
                           /\ UNCHANGED h_cancel_waiting
                /\ UNCHANGED << lr_lock, h_active, h_fl_CANCEL, h_fl_BL_DONE,
                                h_fl_AST_SENT, h_callback_calls,
                                h_callback_running, h_on_waiting_list, w_list,
                                w_fl_AST_SENT, w_fl_CP_REQD,
                                w_fl_BLOCK_GRANTED, w_fl_DESTROYED,
                                w_granted_mode, w_resource, w_cp_resource,
                                w_server_grant_calls, w_client_grant_calls,
                                w_server_pool, w_client_pool, erestart,
                                reprocess_ready, cp_ready, resource_changing,
                                lifecycle_done, cancel_a_done, cancel_b_done >>

CB_WaitRelock == /\ pc["canceller_b"] = "CB_WaitRelock"
                 /\ lr_lock = "free"
                 /\ lr_lock' = "canceller_b"
                 /\ pc' = [pc EXCEPT !["canceller_b"] = "CB_WaitUnlock"]
                 /\ UNCHANGED << h_active, h_fl_CANCEL, h_fl_BL_DONE,
                                 h_fl_AST_SENT, h_callback_calls,
                                 h_callback_running, h_on_waiting_list,
                                 h_cancel_waiting, w_list, w_fl_AST_SENT,
                                 w_fl_CP_REQD, w_fl_BLOCK_GRANTED,
                                 w_fl_DESTROYED, w_granted_mode, w_resource,
                                 w_cp_resource, w_server_grant_calls,
                                 w_client_grant_calls, w_server_pool,
                                 w_client_pool, erestart, reprocess_ready,
                                 cp_ready, resource_changing, lifecycle_done,
                                 cancel_a_done, cancel_b_done >>

CB_WaitUnlock == /\ pc["canceller_b"] = "CB_WaitUnlock"
                 /\ lr_lock' = "free"
                 /\ pc' = [pc EXCEPT !["canceller_b"] = "CB_Complete"]
                 /\ UNCHANGED << h_active, h_fl_CANCEL, h_fl_BL_DONE,
                                 h_fl_AST_SENT, h_callback_calls,
                                 h_callback_running, h_on_waiting_list,
                                 h_cancel_waiting, w_list, w_fl_AST_SENT,
                                 w_fl_CP_REQD, w_fl_BLOCK_GRANTED,
                                 w_fl_DESTROYED, w_granted_mode, w_resource,
                                 w_cp_resource, w_server_grant_calls,
                                 w_client_grant_calls, w_server_pool,
                                 w_client_pool, erestart, reprocess_ready,
                                 cp_ready, resource_changing, lifecycle_done,
                                 cancel_a_done, cancel_b_done >>

CB_Complete == /\ pc["canceller_b"] = "CB_Complete"
               /\ cancel_b_done' = TRUE
               /\ pc' = [pc EXCEPT !["canceller_b"] = "Done"]
               /\ UNCHANGED << lr_lock, h_active, h_fl_CANCEL, h_fl_BL_DONE,
                               h_fl_AST_SENT, h_callback_calls,
                               h_callback_running, h_on_waiting_list,
                               h_cancel_waiting, w_list, w_fl_AST_SENT,
                               w_fl_CP_REQD, w_fl_BLOCK_GRANTED,
                               w_fl_DESTROYED, w_granted_mode, w_resource,
                               w_cp_resource, w_server_grant_calls,
                               w_client_grant_calls, w_server_pool,
                               w_client_pool, erestart, reprocess_ready,
                               cp_ready, resource_changing, lifecycle_done,
                               cancel_a_done >>

CancellerB == CB_Wait \/ CB_Lock \/ CB_CheckCancel \/ CB_Unlock2
                 \/ CB_RunCallback \/ CB_CallbackDone \/ CB_Relock
                 \/ CB_SetBLDone \/ CB_Wait2 \/ CB_AddWait \/ CB_WaitCheck
                 \/ CB_WaitRelock \/ CB_WaitUnlock \/ CB_Complete

WL_Wait == /\ pc["wl_adder"] = "WL_Wait"
           /\ h_callback_running
           /\ pc' = [pc EXCEPT !["wl_adder"] = "WL_Lock"]
           /\ UNCHANGED << lr_lock, h_active, h_fl_CANCEL, h_fl_BL_DONE,
                           h_fl_AST_SENT, h_callback_calls, h_callback_running,
                           h_on_waiting_list, h_cancel_waiting, w_list,
                           w_fl_AST_SENT, w_fl_CP_REQD, w_fl_BLOCK_GRANTED,
                           w_fl_DESTROYED, w_granted_mode, w_resource,
                           w_cp_resource, w_server_grant_calls,
                           w_client_grant_calls, w_server_pool, w_client_pool,
                           erestart, reprocess_ready, cp_ready,
                           resource_changing, lifecycle_done, cancel_a_done,
                           cancel_b_done >>

WL_Lock == /\ pc["wl_adder"] = "WL_Lock"
           /\ lr_lock = "free"
           /\ lr_lock' = "wl_adder"
           /\ pc' = [pc EXCEPT !["wl_adder"] = "WL_TryAdd"]
           /\ UNCHANGED << h_active, h_fl_CANCEL, h_fl_BL_DONE, h_fl_AST_SENT,
                           h_callback_calls, h_callback_running,
                           h_on_waiting_list, h_cancel_waiting, w_list,
                           w_fl_AST_SENT, w_fl_CP_REQD, w_fl_BLOCK_GRANTED,
                           w_fl_DESTROYED, w_granted_mode, w_resource,
                           w_cp_resource, w_server_grant_calls,
                           w_client_grant_calls, w_server_pool, w_client_pool,
                           erestart, reprocess_ready, cp_ready,
                           resource_changing, lifecycle_done, cancel_a_done,
                           cancel_b_done >>

WL_TryAdd == /\ pc["wl_adder"] = "WL_TryAdd"
             /\ IF InjectBug6416
                   THEN /\ h_on_waiting_list' = TRUE
                   ELSE /\ IF ~h_fl_CANCEL
                              THEN /\ h_on_waiting_list' = TRUE
                              ELSE /\ TRUE
                                   /\ UNCHANGED h_on_waiting_list
             /\ lr_lock' = "free"
             /\ pc' = [pc EXCEPT !["wl_adder"] = "Done"]
             /\ UNCHANGED << h_active, h_fl_CANCEL, h_fl_BL_DONE,
                             h_fl_AST_SENT, h_callback_calls,
                             h_callback_running, h_cancel_waiting, w_list,
                             w_fl_AST_SENT, w_fl_CP_REQD, w_fl_BLOCK_GRANTED,
                             w_fl_DESTROYED, w_granted_mode, w_resource,
                             w_cp_resource, w_server_grant_calls,
                             w_client_grant_calls, w_server_pool,
                             w_client_pool, erestart, reprocess_ready,
                             cp_ready, resource_changing, lifecycle_done,
                             cancel_a_done, cancel_b_done >>

WaitingListAdder == WL_Wait \/ WL_Lock \/ WL_TryAdd

SC_WaitCancel == /\ pc["server_cancel"] = "SC_WaitCancel"
                 /\ h_fl_BL_DONE
                 /\ pc' = [pc EXCEPT !["server_cancel"] = "SC_Lock"]
                 /\ UNCHANGED << lr_lock, h_active, h_fl_CANCEL, h_fl_BL_DONE,
                                 h_fl_AST_SENT, h_callback_calls,
                                 h_callback_running, h_on_waiting_list,
                                 h_cancel_waiting, w_list, w_fl_AST_SENT,
                                 w_fl_CP_REQD, w_fl_BLOCK_GRANTED,
                                 w_fl_DESTROYED, w_granted_mode, w_resource,
                                 w_cp_resource, w_server_grant_calls,
                                 w_client_grant_calls, w_server_pool,
                                 w_client_pool, erestart, reprocess_ready,
                                 cp_ready, resource_changing, lifecycle_done,
                                 cancel_a_done, cancel_b_done >>

SC_Lock == /\ pc["server_cancel"] = "SC_Lock"
           /\ lr_lock = "free"
           /\ lr_lock' = "server_cancel"
           /\ pc' = [pc EXCEPT !["server_cancel"] = "SC_RemoveHolder"]
           /\ UNCHANGED << h_active, h_fl_CANCEL, h_fl_BL_DONE, h_fl_AST_SENT,
                           h_callback_calls, h_callback_running,
                           h_on_waiting_list, h_cancel_waiting, w_list,
                           w_fl_AST_SENT, w_fl_CP_REQD, w_fl_BLOCK_GRANTED,
                           w_fl_DESTROYED, w_granted_mode, w_resource,
                           w_cp_resource, w_server_grant_calls,
                           w_client_grant_calls, w_server_pool, w_client_pool,
                           erestart, reprocess_ready, cp_ready,
                           resource_changing, lifecycle_done, cancel_a_done,
                           cancel_b_done >>

SC_RemoveHolder == /\ pc["server_cancel"] = "SC_RemoveHolder"
                   /\ h_active' = FALSE
                   /\ lr_lock' = "free"
                   /\ reprocess_ready' = TRUE
                   /\ pc' = [pc EXCEPT !["server_cancel"] = "Done"]
                   /\ UNCHANGED << h_fl_CANCEL, h_fl_BL_DONE, h_fl_AST_SENT,
                                   h_callback_calls, h_callback_running,
                                   h_on_waiting_list, h_cancel_waiting, w_list,
                                   w_fl_AST_SENT, w_fl_CP_REQD,
                                   w_fl_BLOCK_GRANTED, w_fl_DESTROYED,
                                   w_granted_mode, w_resource, w_cp_resource,
                                   w_server_grant_calls, w_client_grant_calls,
                                   w_server_pool, w_client_pool, erestart,
                                   cp_ready, resource_changing, lifecycle_done,
                                   cancel_a_done, cancel_b_done >>

ServerCancel == SC_WaitCancel \/ SC_Lock \/ SC_RemoveHolder

RP_WaitReady == /\ pc["reprocessor"] = "RP_WaitReady"
                /\ reprocess_ready
                /\ pc' = [pc EXCEPT !["reprocessor"] = "RP_Lock"]
                /\ UNCHANGED << lr_lock, h_active, h_fl_CANCEL, h_fl_BL_DONE,
                                h_fl_AST_SENT, h_callback_calls,
                                h_callback_running, h_on_waiting_list,
                                h_cancel_waiting, w_list, w_fl_AST_SENT,
                                w_fl_CP_REQD, w_fl_BLOCK_GRANTED,
                                w_fl_DESTROYED, w_granted_mode, w_resource,
                                w_cp_resource, w_server_grant_calls,
                                w_client_grant_calls, w_server_pool,
                                w_client_pool, erestart, reprocess_ready,
                                cp_ready, resource_changing, lifecycle_done,
                                cancel_a_done, cancel_b_done >>

RP_Lock == /\ pc["reprocessor"] = "RP_Lock"
           /\ lr_lock = "free"
           /\ lr_lock' = "reprocessor"
           /\ erestart' = FALSE
           /\ pc' = [pc EXCEPT !["reprocessor"] = "RP_Scan"]
           /\ UNCHANGED << h_active, h_fl_CANCEL, h_fl_BL_DONE, h_fl_AST_SENT,
                           h_callback_calls, h_callback_running,
                           h_on_waiting_list, h_cancel_waiting, w_list,
                           w_fl_AST_SENT, w_fl_CP_REQD, w_fl_BLOCK_GRANTED,
                           w_fl_DESTROYED, w_granted_mode, w_resource,
                           w_cp_resource, w_server_grant_calls,
                           w_client_grant_calls, w_server_pool, w_client_pool,
                           reprocess_ready, cp_ready, resource_changing,
                           lifecycle_done, cancel_a_done, cancel_b_done >>

RP_Scan == /\ pc["reprocessor"] = "RP_Scan"
           /\ IF w_list = "waiting" /\ ~w_fl_DESTROYED
                 THEN /\ IF ~h_active
                            THEN /\ w_server_pool' = w_server_pool + 1
                                 /\ w_server_grant_calls' = w_server_grant_calls + 1
                                 /\ w_fl_CP_REQD' = TRUE
                                 /\ lr_lock' = "free"
                                 /\ cp_ready' = TRUE
                                 /\ pc' = [pc EXCEPT !["reprocessor"] = "RP_Done"]
                            ELSE /\ lr_lock' = "free"
                                 /\ pc' = [pc EXCEPT !["reprocessor"] = "RP_BLASTWindow"]
                                 /\ UNCHANGED << w_fl_CP_REQD,
                                                 w_server_grant_calls,
                                                 w_server_pool, cp_ready >>
                 ELSE /\ lr_lock' = "free"
                      /\ pc' = [pc EXCEPT !["reprocessor"] = "RP_Done"]
                      /\ UNCHANGED << w_fl_CP_REQD, w_server_grant_calls,
                                      w_server_pool, cp_ready >>
           /\ UNCHANGED << h_active, h_fl_CANCEL, h_fl_BL_DONE, h_fl_AST_SENT,
                           h_callback_calls, h_callback_running,
                           h_on_waiting_list, h_cancel_waiting, w_list,
                           w_fl_AST_SENT, w_fl_BLOCK_GRANTED, w_fl_DESTROYED,
                           w_granted_mode, w_resource, w_cp_resource,
                           w_client_grant_calls, w_client_pool, erestart,
                           reprocess_ready, resource_changing, lifecycle_done,
                           cancel_a_done, cancel_b_done >>

RP_BLASTWindow == /\ pc["reprocessor"] = "RP_BLASTWindow"
                  /\ TRUE
                  /\ pc' = [pc EXCEPT !["reprocessor"] = "RP_Relock"]
                  /\ UNCHANGED << lr_lock, h_active, h_fl_CANCEL, h_fl_BL_DONE,
                                  h_fl_AST_SENT, h_callback_calls,
                                  h_callback_running, h_on_waiting_list,
                                  h_cancel_waiting, w_list, w_fl_AST_SENT,
                                  w_fl_CP_REQD, w_fl_BLOCK_GRANTED,
                                  w_fl_DESTROYED, w_granted_mode, w_resource,
                                  w_cp_resource, w_server_grant_calls,
                                  w_client_grant_calls, w_server_pool,
                                  w_client_pool, erestart, reprocess_ready,
                                  cp_ready, resource_changing, lifecycle_done,
                                  cancel_a_done, cancel_b_done >>

RP_Relock == /\ pc["reprocessor"] = "RP_Relock"
             /\ lr_lock = "free"
             /\ lr_lock' = "reprocessor"
             /\ pc' = [pc EXCEPT !["reprocessor"] = "RP_CheckRestart"]
             /\ UNCHANGED << h_active, h_fl_CANCEL, h_fl_BL_DONE,
                             h_fl_AST_SENT, h_callback_calls,
                             h_callback_running, h_on_waiting_list,
                             h_cancel_waiting, w_list, w_fl_AST_SENT,
                             w_fl_CP_REQD, w_fl_BLOCK_GRANTED, w_fl_DESTROYED,
                             w_granted_mode, w_resource, w_cp_resource,
                             w_server_grant_calls, w_client_grant_calls,
                             w_server_pool, w_client_pool, erestart,
                             reprocess_ready, cp_ready, resource_changing,
                             lifecycle_done, cancel_a_done, cancel_b_done >>

RP_CheckRestart == /\ pc["reprocessor"] = "RP_CheckRestart"
                   /\ IF erestart /\ ~InjectBugNoRestart
                         THEN /\ erestart' = FALSE
                              /\ pc' = [pc EXCEPT !["reprocessor"] = "RP_Scan"]
                         ELSE /\ pc' = [pc EXCEPT !["reprocessor"] = "RP_Finish"]
                              /\ UNCHANGED erestart
                   /\ UNCHANGED << lr_lock, h_active, h_fl_CANCEL,
                                   h_fl_BL_DONE, h_fl_AST_SENT,
                                   h_callback_calls, h_callback_running,
                                   h_on_waiting_list, h_cancel_waiting, w_list,
                                   w_fl_AST_SENT, w_fl_CP_REQD,
                                   w_fl_BLOCK_GRANTED, w_fl_DESTROYED,
                                   w_granted_mode, w_resource, w_cp_resource,
                                   w_server_grant_calls, w_client_grant_calls,
                                   w_server_pool, w_client_pool,
                                   reprocess_ready, cp_ready,
                                   resource_changing, lifecycle_done,
                                   cancel_a_done, cancel_b_done >>

RP_Finish == /\ pc["reprocessor"] = "RP_Finish"
             /\ IF w_list = "waiting" /\ ~w_fl_DESTROYED /\ ~h_active
                   THEN /\ w_server_pool' = w_server_pool + 1
                        /\ w_server_grant_calls' = w_server_grant_calls + 1
                        /\ w_fl_CP_REQD' = TRUE
                        /\ lr_lock' = "free"
                        /\ cp_ready' = TRUE
                   ELSE /\ lr_lock' = "free"
                        /\ UNCHANGED << w_fl_CP_REQD, w_server_grant_calls,
                                        w_server_pool, cp_ready >>
             /\ pc' = [pc EXCEPT !["reprocessor"] = "RP_Done"]
             /\ UNCHANGED << h_active, h_fl_CANCEL, h_fl_BL_DONE,
                             h_fl_AST_SENT, h_callback_calls,
                             h_callback_running, h_on_waiting_list,
                             h_cancel_waiting, w_list, w_fl_AST_SENT,
                             w_fl_BLOCK_GRANTED, w_fl_DESTROYED,
                             w_granted_mode, w_resource, w_cp_resource,
                             w_client_grant_calls, w_client_pool, erestart,
                             reprocess_ready, resource_changing,
                             lifecycle_done, cancel_a_done, cancel_b_done >>

RP_Done == /\ pc["reprocessor"] = "RP_Done"
           /\ TRUE
           /\ pc' = [pc EXCEPT !["reprocessor"] = "Done"]
           /\ UNCHANGED << lr_lock, h_active, h_fl_CANCEL, h_fl_BL_DONE,
                           h_fl_AST_SENT, h_callback_calls, h_callback_running,
                           h_on_waiting_list, h_cancel_waiting, w_list,
                           w_fl_AST_SENT, w_fl_CP_REQD, w_fl_BLOCK_GRANTED,
                           w_fl_DESTROYED, w_granted_mode, w_resource,
                           w_cp_resource, w_server_grant_calls,
                           w_client_grant_calls, w_server_pool, w_client_pool,
                           erestart, reprocess_ready, cp_ready,
                           resource_changing, lifecycle_done, cancel_a_done,
                           cancel_b_done >>

Reprocessor == RP_WaitReady \/ RP_Lock \/ RP_Scan \/ RP_BLASTWindow
                  \/ RP_Relock \/ RP_CheckRestart \/ RP_Finish \/ RP_Done

CP_Wait == /\ pc["cp_callback"] = "CP_Wait"
           /\ cp_ready
           /\ pc' = [pc EXCEPT !["cp_callback"] = "CP_Lock"]
           /\ UNCHANGED << lr_lock, h_active, h_fl_CANCEL, h_fl_BL_DONE,
                           h_fl_AST_SENT, h_callback_calls, h_callback_running,
                           h_on_waiting_list, h_cancel_waiting, w_list,
                           w_fl_AST_SENT, w_fl_CP_REQD, w_fl_BLOCK_GRANTED,
                           w_fl_DESTROYED, w_granted_mode, w_resource,
                           w_cp_resource, w_server_grant_calls,
                           w_client_grant_calls, w_server_pool, w_client_pool,
                           erestart, reprocess_ready, cp_ready,
                           resource_changing, lifecycle_done, cancel_a_done,
                           cancel_b_done >>

CP_Lock == /\ pc["cp_callback"] = "CP_Lock"
           /\ lr_lock = "free"
           /\ lr_lock' = "cp_callback"
           /\ pc' = [pc EXCEPT !["cp_callback"] = "CP_ResourceCheck"]
           /\ UNCHANGED << h_active, h_fl_CANCEL, h_fl_BL_DONE, h_fl_AST_SENT,
                           h_callback_calls, h_callback_running,
                           h_on_waiting_list, h_cancel_waiting, w_list,
                           w_fl_AST_SENT, w_fl_CP_REQD, w_fl_BLOCK_GRANTED,
                           w_fl_DESTROYED, w_granted_mode, w_resource,
                           w_cp_resource, w_server_grant_calls,
                           w_client_grant_calls, w_server_pool, w_client_pool,
                           erestart, reprocess_ready, cp_ready,
                           resource_changing, lifecycle_done, cancel_a_done,
                           cancel_b_done >>

CP_ResourceCheck == /\ pc["cp_callback"] = "CP_ResourceCheck"
                    /\ IF w_cp_resource /= w_resource
                          THEN /\ w_list' = "none"
                               /\ lr_lock' = "free"
                               /\ pc' = [pc EXCEPT !["cp_callback"] = "CP_ChangeResource"]
                          ELSE /\ pc' = [pc EXCEPT !["cp_callback"] = "CP_Grant"]
                               /\ UNCHANGED << lr_lock, w_list >>
                    /\ UNCHANGED << h_active, h_fl_CANCEL, h_fl_BL_DONE,
                                    h_fl_AST_SENT, h_callback_calls,
                                    h_callback_running, h_on_waiting_list,
                                    h_cancel_waiting, w_fl_AST_SENT,
                                    w_fl_CP_REQD, w_fl_BLOCK_GRANTED,
                                    w_fl_DESTROYED, w_granted_mode, w_resource,
                                    w_cp_resource, w_server_grant_calls,
                                    w_client_grant_calls, w_server_pool,
                                    w_client_pool, erestart, reprocess_ready,
                                    cp_ready, resource_changing,
                                    lifecycle_done, cancel_a_done,
                                    cancel_b_done >>

CP_ChangeResource == /\ pc["cp_callback"] = "CP_ChangeResource"
                     /\ w_resource' = w_cp_resource
                     /\ resource_changing' = TRUE
                     /\ pc' = [pc EXCEPT !["cp_callback"] = "CP_Relock"]
                     /\ UNCHANGED << lr_lock, h_active, h_fl_CANCEL,
                                     h_fl_BL_DONE, h_fl_AST_SENT,
                                     h_callback_calls, h_callback_running,
                                     h_on_waiting_list, h_cancel_waiting,
                                     w_list, w_fl_AST_SENT, w_fl_CP_REQD,
                                     w_fl_BLOCK_GRANTED, w_fl_DESTROYED,
                                     w_granted_mode, w_cp_resource,
                                     w_server_grant_calls,
                                     w_client_grant_calls, w_server_pool,
                                     w_client_pool, erestart, reprocess_ready,
                                     cp_ready, lifecycle_done, cancel_a_done,
                                     cancel_b_done >>

CP_Relock == /\ pc["cp_callback"] = "CP_Relock"
             /\ lr_lock = "free"
             /\ lr_lock' = "cp_callback"
             /\ pc' = [pc EXCEPT !["cp_callback"] = "CP_8391Check"]
             /\ UNCHANGED << h_active, h_fl_CANCEL, h_fl_BL_DONE,
                             h_fl_AST_SENT, h_callback_calls,
                             h_callback_running, h_on_waiting_list,
                             h_cancel_waiting, w_list, w_fl_AST_SENT,
                             w_fl_CP_REQD, w_fl_BLOCK_GRANTED, w_fl_DESTROYED,
                             w_granted_mode, w_resource, w_cp_resource,
                             w_server_grant_calls, w_client_grant_calls,
                             w_server_pool, w_client_pool, erestart,
                             reprocess_ready, cp_ready, resource_changing,
                             lifecycle_done, cancel_a_done, cancel_b_done >>

CP_8391Check == /\ pc["cp_callback"] = "CP_8391Check"
                /\ IF ~InjectBug8391 /\ (IsWGranted \/ w_fl_DESTROYED)
                      THEN /\ lr_lock' = "free"
                           /\ pc' = [pc EXCEPT !["cp_callback"] = "CP_Done"]
                      ELSE /\ pc' = [pc EXCEPT !["cp_callback"] = "CP_Grant"]
                           /\ UNCHANGED lr_lock
                /\ UNCHANGED << h_active, h_fl_CANCEL, h_fl_BL_DONE,
                                h_fl_AST_SENT, h_callback_calls,
                                h_callback_running, h_on_waiting_list,
                                h_cancel_waiting, w_list, w_fl_AST_SENT,
                                w_fl_CP_REQD, w_fl_BLOCK_GRANTED,
                                w_fl_DESTROYED, w_granted_mode, w_resource,
                                w_cp_resource, w_server_grant_calls,
                                w_client_grant_calls, w_server_pool,
                                w_client_pool, erestart, reprocess_ready,
                                cp_ready, resource_changing, lifecycle_done,
                                cancel_a_done, cancel_b_done >>

CP_Grant == /\ pc["cp_callback"] = "CP_Grant"
            /\ w_granted_mode' = 4
            /\ w_list' = "granted"
            /\ w_client_pool' = w_client_pool + 1
            /\ w_client_grant_calls' = w_client_grant_calls + 1
            /\ w_fl_BLOCK_GRANTED' = FALSE
            /\ lr_lock' = "free"
            /\ pc' = [pc EXCEPT !["cp_callback"] = "CP_Done"]
            /\ UNCHANGED << h_active, h_fl_CANCEL, h_fl_BL_DONE, h_fl_AST_SENT,
                            h_callback_calls, h_callback_running,
                            h_on_waiting_list, h_cancel_waiting, w_fl_AST_SENT,
                            w_fl_CP_REQD, w_fl_DESTROYED, w_resource,
                            w_cp_resource, w_server_grant_calls, w_server_pool,
                            erestart, reprocess_ready, cp_ready,
                            resource_changing, lifecycle_done, cancel_a_done,
                            cancel_b_done >>

CP_Done == /\ pc["cp_callback"] = "CP_Done"
           /\ lifecycle_done' = TRUE
           /\ pc' = [pc EXCEPT !["cp_callback"] = "Done"]
           /\ UNCHANGED << lr_lock, h_active, h_fl_CANCEL, h_fl_BL_DONE,
                           h_fl_AST_SENT, h_callback_calls, h_callback_running,
                           h_on_waiting_list, h_cancel_waiting, w_list,
                           w_fl_AST_SENT, w_fl_CP_REQD, w_fl_BLOCK_GRANTED,
                           w_fl_DESTROYED, w_granted_mode, w_resource,
                           w_cp_resource, w_server_grant_calls,
                           w_client_grant_calls, w_server_pool, w_client_pool,
                           erestart, reprocess_ready, cp_ready,
                           resource_changing, cancel_a_done, cancel_b_done >>

CPCallback == CP_Wait \/ CP_Lock \/ CP_ResourceCheck \/ CP_ChangeResource
                 \/ CP_Relock \/ CP_8391Check \/ CP_Grant \/ CP_Done

AG_Wait == /\ pc["alt_granter"] = "AG_Wait"
           /\ resource_changing
           /\ pc' = [pc EXCEPT !["alt_granter"] = "AG_Lock"]
           /\ UNCHANGED << lr_lock, h_active, h_fl_CANCEL, h_fl_BL_DONE,
                           h_fl_AST_SENT, h_callback_calls, h_callback_running,
                           h_on_waiting_list, h_cancel_waiting, w_list,
                           w_fl_AST_SENT, w_fl_CP_REQD, w_fl_BLOCK_GRANTED,
                           w_fl_DESTROYED, w_granted_mode, w_resource,
                           w_cp_resource, w_server_grant_calls,
                           w_client_grant_calls, w_server_pool, w_client_pool,
                           erestart, reprocess_ready, cp_ready,
                           resource_changing, lifecycle_done, cancel_a_done,
                           cancel_b_done >>

AG_Lock == /\ pc["alt_granter"] = "AG_Lock"
           /\ lr_lock = "free"
           /\ lr_lock' = "alt_granter"
           /\ pc' = [pc EXCEPT !["alt_granter"] = "AG_Grant"]
           /\ UNCHANGED << h_active, h_fl_CANCEL, h_fl_BL_DONE, h_fl_AST_SENT,
                           h_callback_calls, h_callback_running,
                           h_on_waiting_list, h_cancel_waiting, w_list,
                           w_fl_AST_SENT, w_fl_CP_REQD, w_fl_BLOCK_GRANTED,
                           w_fl_DESTROYED, w_granted_mode, w_resource,
                           w_cp_resource, w_server_grant_calls,
                           w_client_grant_calls, w_server_pool, w_client_pool,
                           erestart, reprocess_ready, cp_ready,
                           resource_changing, lifecycle_done, cancel_a_done,
                           cancel_b_done >>

AG_Grant == /\ pc["alt_granter"] = "AG_Grant"
            /\ IF ~IsWGranted /\ ~w_fl_DESTROYED /\ w_list /= "granted"
                  THEN /\ w_granted_mode' = 4
                       /\ w_list' = "granted"
                       /\ w_client_pool' = w_client_pool + 1
                       /\ w_client_grant_calls' = w_client_grant_calls + 1
                       /\ w_fl_BLOCK_GRANTED' = FALSE
                  ELSE /\ TRUE
                       /\ UNCHANGED << w_list, w_fl_BLOCK_GRANTED,
                                       w_granted_mode, w_client_grant_calls,
                                       w_client_pool >>
            /\ lr_lock' = "free"
            /\ pc' = [pc EXCEPT !["alt_granter"] = "Done"]
            /\ UNCHANGED << h_active, h_fl_CANCEL, h_fl_BL_DONE, h_fl_AST_SENT,
                            h_callback_calls, h_callback_running,
                            h_on_waiting_list, h_cancel_waiting, w_fl_AST_SENT,
                            w_fl_CP_REQD, w_fl_DESTROYED, w_resource,
                            w_cp_resource, w_server_grant_calls, w_server_pool,
                            erestart, reprocess_ready, cp_ready,
                            resource_changing, lifecycle_done, cancel_a_done,
                            cancel_b_done >>

AltGranter == AG_Wait \/ AG_Lock \/ AG_Grant

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == EnqueueHandler \/ CancellerA \/ CancellerB \/ WaitingListAdder
           \/ ServerCancel \/ Reprocessor \/ CPCallback \/ AltGranter
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(EnqueueHandler)
        /\ WF_vars(CancellerA)
        /\ WF_vars(CancellerB)
        /\ WF_vars(WaitingListAdder)
        /\ WF_vars(ServerCancel)
        /\ WF_vars(Reprocessor)
        /\ WF_vars(CPCallback)
        /\ WF_vars(AltGranter)

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

\* ================================================================
\* Liveness: lifecycle eventually completes
\* ================================================================
EventualCompletion ==
    <>(lifecycle_done)

\* Cancel sync: all cancellers eventually complete
AllCancellersComplete ==
    <>(cancel_a_done /\ cancel_b_done)

=============================================================================
