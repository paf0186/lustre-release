--------------------------- MODULE ldlm_bl_ast_race ---------------------------
(*
 * Model: LDLM BL_AST vs Failed Enqueue Race (LU-13989)
 *
 * Models the client-side race between:
 *   - BL_AST callback arriving from the server
 *   - failed_lock_cleanup() processing a failed enqueue
 *
 * The bug: failed_lock_cleanup() unconditionally sets
 *   LDLM_FL_LOCAL_ONLY, suppressing the cancel RPC.
 *   If a BL_AST was already received, the server expects
 *   the cancel RPC.  Without it, the server waits forever
 *   and evicts the client.
 *
 * The fix (c1be044913): Only set LOCAL_ONLY if BL_AST
 *   was NOT received (or server handle is unknown).
 *   Also adds server handle to BL_AST RPC body.
 *
 * Key insight: If FailedCleanup runs BEFORE the BL_AST
 *   handler, it sets FAILED.  When BL_AST arrives, the
 *   client returns -EINVAL.  The SERVER handles -EINVAL
 *   by calling ldlm_lock_cancel on the server side
 *   (ldlm_handle_ast_error, line 751).  So the server
 *   cleans up even without a cancel RPC.
 *
 * Two cancel pathways:
 *   Path A: BL_AST first -> flags seen -> no LOCAL_ONLY
 *           -> cancel RPC sent -> server cleans up
 *   Path B: FailedCleanup first -> LOCAL_ONLY set
 *           -> BL_AST handler sees FAILED -> returns -EINVAL
 *           -> server cancels lock on -EINVAL (ERESTART)
 *
 * When InjectBugLocalOnly=TRUE, Path A breaks because
 *   LOCAL_ONLY is always set, AND the -EINVAL fallback
 *   doesn't exist (pre-fix, the BL_AST handler doesn't
 *   check FAILED, so it tries to cancel via blocking_ast
 *   but LOCAL_ONLY suppresses it, and no -EINVAL reply).
 *
 * Correctness: The server's lock must be cancelled by
 *   the time all processes are done.
 *
 * Source (lustre-release master 47638add78):
 *   lustre/ldlm/ldlm_request.c  failed_lock_cleanup (566-616)
 *     FC_Lock/FC_SetFlags/FC_CheckBLAST/FC_Unlock: lock_res_and_lock
 *     572, FAILED|ATOMIC_CB|CBPENDING 580-581, LOCAL_ONLY only if
 *     !(BL_AST && l_remote_handle.cookie) 582-584, unlock 587;
 *     FC_Cancel: ldlm_lock_decref_internal 614 -> blocking_ast ->
 *     ldlm_cli_cancel.
 *   lustre/ldlm/ldlm_lockd.c    ldlm_callback_handler (2353-2534)
 *     BL_Lock/BL_CheckFailed/BL_Unlock: BL_CALLBACK under
 *     lock_res_and_lock 2460-2491; FAILED (or CANCELING+BL_DONE)
 *     -> reply -EINVAL 2470-2480; else ldlm_set_bl_ast 2487 and
 *     l_remote_handle taken from the AST 2489-2490.
 *   lustre/ldlm/ldlm_lockd.c    ldlm_handle_bl_callback (1900-1936)
 *     BL_TriggerCancel: sets CBPENDING 1913, blocking_ast 1923.
 *   lustre/ldlm/ldlm_request.c  ldlm_cli_cancel_local (1382-1423)
 *     BL_CancelCheck/FC_CancelCheck: LOCAL_ONLY|CANCEL_ON_BLOCK
 *     suppresses the CANCEL RPC 1398-1409.
 *   lustre/ldlm/ldlm_lockd.c    ldlm_handle_ast_error (686-756)
 *     server side: -EINVAL AST reply -> ldlm_lock_cancel 733-752.
 *   Fix commit c1be044913 (LU-13989).
 *
 * Validated against: lustre-release master 47638add78 (2026-09-06)
 *)
EXTENDS Integers, FiniteSets, TLC

\* Bug injection: TRUE = old code (LOCAL_ONLY unconditional,
\* no FAILED check in BL_AST handler, no -EINVAL reply).
CONSTANT InjectBugLocalOnly

(* --algorithm ldlm_bl_ast_race

variables
    \* ---- Lock flags (client side) ----
    fl_bl_ast       = FALSE,   \* LDLM_FL_BL_AST
    fl_local_only   = FALSE,   \* LDLM_FL_LOCAL_ONLY
    fl_cbpending    = FALSE,   \* LDLM_FL_CBPENDING
    fl_failed       = FALSE,   \* LDLM_FL_FAILED
    remote_handle   = 0,       \* l_remote_handle.cookie

    \* ---- Server state ----
    lock_on_server  = FALSE,   \* lock on server waiting list
    bl_ast_sent     = FALSE,   \* server sent BL_AST
    server_got_cancel = FALSE, \* server cancelled the lock

    \* ---- Communication ----
    enqueue_sent    = FALSE,
    enqueue_failed  = FALSE,
    bl_ast_arrived  = FALSE,
    cancel_rpc_sent = FALSE,

    \* ---- Lock ----
    res_lock        = "free";

define
    \* Terminal: when all client processes are done, the server
    \* lock must have been cancelled (either via cancel RPC
    \* or via -EINVAL reply triggering server-side cancel).
    ServerLockCancelled ==
        (pc["bl_ast_receiver"] = "Done"
         /\ pc["failed_cleanup"] = "Done") =>
            (bl_ast_sent => server_got_cancel)

    TypeOK ==
        /\ fl_bl_ast \in BOOLEAN
        /\ fl_local_only \in BOOLEAN
        /\ fl_cbpending \in BOOLEAN
        /\ fl_failed \in BOOLEAN
        /\ remote_handle \in 0..1
        /\ lock_on_server \in BOOLEAN
        /\ bl_ast_sent \in BOOLEAN
        /\ server_got_cancel \in BOOLEAN
        /\ res_lock \in {"free", "bl_ast", "cleanup", "bl_cancel"}
end define;

\* ==== Server: place lock, send BL_AST, fail enqueue ====
fair process ServerProcess = "server"
begin
SP_Wait:
    await enqueue_sent;
SP_PlaceLock:
    lock_on_server := TRUE;
SP_SendBLAST:
    bl_ast_sent := TRUE;
    bl_ast_arrived := TRUE;
SP_FailEnqueue:
    enqueue_failed := TRUE;
SP_Done:
    skip;
end process;

\* ==== Client sends enqueue ====
fair process ClientEnqueue = "client_enqueue"
begin
CE_Send:
    enqueue_sent := TRUE;
CE_Done:
    skip;
end process;

\* ==== BL_AST receiver on client ====
\* In the fix: checks FAILED flag.  If FAILED, returns -EINVAL
\* to server, which triggers server-side ldlm_lock_cancel.
\* If NOT FAILED, sets BL_AST flag and triggers cancel.
fair process BLASTReceiver = "bl_ast_receiver"
begin
BL_Wait:
    await bl_ast_arrived;
BL_Lock:
    await res_lock = "free";
    res_lock := "bl_ast";
BL_CheckFailed:
    \* ldlm_callback_handler: checks FAILED flag
    if InjectBugLocalOnly then
        \* BUG: old code doesn't check FAILED, always proceeds
        \* to set BL_AST flag and trigger blocking callback.
        fl_bl_ast := TRUE;
        fl_cbpending := TRUE;
        remote_handle := 1;
        res_lock := "free";
        goto BL_TriggerCancel;
    else
        \* FIX: if lock is FAILED, return -EINVAL to server
        if fl_failed then
            \* Return -EINVAL -> server calls ldlm_lock_cancel
            server_got_cancel := TRUE;
            res_lock := "free";
            goto BL_Done;
        else
            \* Normal path: set BL_AST flag
            fl_bl_ast := TRUE;
            fl_cbpending := TRUE;
            remote_handle := 1;
        end if;
    end if;
BL_Unlock:
    res_lock := "free";
BL_TriggerCancel:
    \* blocking_ast callback -> ldlm_cli_cancel
    await res_lock = "free";
    res_lock := "bl_cancel";
BL_CancelCheck:
    \* ldlm_cli_cancel_local: checks LOCAL_ONLY
    if ~fl_local_only then
        cancel_rpc_sent := TRUE;
        server_got_cancel := TRUE;
    end if;
BL_CancelDone:
    res_lock := "free";
BL_Done:
    skip;
end process;

\* ==== Failed lock cleanup on client ====
fair process FailedCleanup = "failed_cleanup"
begin
FC_Wait:
    await enqueue_failed;
FC_Lock:
    await res_lock = "free";
    res_lock := "cleanup";
FC_SetFlags:
    fl_failed := TRUE;
    fl_cbpending := TRUE;
FC_CheckBLAST:
    if InjectBugLocalOnly then
        \* BUG: always set LOCAL_ONLY
        fl_local_only := TRUE;
    else
        \* FIX: only if no BL_AST or no server handle
        if ~(fl_bl_ast /\ remote_handle /= 0) then
            fl_local_only := TRUE;
        end if;
    end if;
FC_Unlock:
    res_lock := "free";
FC_Cancel:
    \* ldlm_lock_decref_internal -> ldlm_cli_cancel
    await res_lock = "free";
    res_lock := "cleanup";
FC_CancelCheck:
    if ~fl_local_only then
        cancel_rpc_sent := TRUE;
        server_got_cancel := TRUE;
    end if;
FC_CancelDone:
    res_lock := "free";
FC_Done:
    skip;
end process;

end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "c88aa4c8" /\ chksum(tla) = "a2e90b2d")
VARIABLES fl_bl_ast, fl_local_only, fl_cbpending, fl_failed, remote_handle,
          lock_on_server, bl_ast_sent, server_got_cancel, enqueue_sent,
          enqueue_failed, bl_ast_arrived, cancel_rpc_sent, res_lock, pc

(* define statement *)
ServerLockCancelled ==
    (pc["bl_ast_receiver"] = "Done"
     /\ pc["failed_cleanup"] = "Done") =>
        (bl_ast_sent => server_got_cancel)

TypeOK ==
    /\ fl_bl_ast \in BOOLEAN
    /\ fl_local_only \in BOOLEAN
    /\ fl_cbpending \in BOOLEAN
    /\ fl_failed \in BOOLEAN
    /\ remote_handle \in 0..1
    /\ lock_on_server \in BOOLEAN
    /\ bl_ast_sent \in BOOLEAN
    /\ server_got_cancel \in BOOLEAN
    /\ res_lock \in {"free", "bl_ast", "cleanup", "bl_cancel"}


vars == << fl_bl_ast, fl_local_only, fl_cbpending, fl_failed, remote_handle,
           lock_on_server, bl_ast_sent, server_got_cancel, enqueue_sent,
           enqueue_failed, bl_ast_arrived, cancel_rpc_sent, res_lock, pc >>

ProcSet == {"server"} \cup {"client_enqueue"} \cup {"bl_ast_receiver"} \cup {"failed_cleanup"}

Init == (* Global variables *)
        /\ fl_bl_ast = FALSE
        /\ fl_local_only = FALSE
        /\ fl_cbpending = FALSE
        /\ fl_failed = FALSE
        /\ remote_handle = 0
        /\ lock_on_server = FALSE
        /\ bl_ast_sent = FALSE
        /\ server_got_cancel = FALSE
        /\ enqueue_sent = FALSE
        /\ enqueue_failed = FALSE
        /\ bl_ast_arrived = FALSE
        /\ cancel_rpc_sent = FALSE
        /\ res_lock = "free"
        /\ pc = [self \in ProcSet |-> CASE self = "server" -> "SP_Wait"
                                        [] self = "client_enqueue" -> "CE_Send"
                                        [] self = "bl_ast_receiver" -> "BL_Wait"
                                        [] self = "failed_cleanup" -> "FC_Wait"]

SP_Wait == /\ pc["server"] = "SP_Wait"
           /\ enqueue_sent
           /\ pc' = [pc EXCEPT !["server"] = "SP_PlaceLock"]
           /\ UNCHANGED << fl_bl_ast, fl_local_only, fl_cbpending, fl_failed,
                           remote_handle, lock_on_server, bl_ast_sent,
                           server_got_cancel, enqueue_sent, enqueue_failed,
                           bl_ast_arrived, cancel_rpc_sent, res_lock >>

SP_PlaceLock == /\ pc["server"] = "SP_PlaceLock"
                /\ lock_on_server' = TRUE
                /\ pc' = [pc EXCEPT !["server"] = "SP_SendBLAST"]
                /\ UNCHANGED << fl_bl_ast, fl_local_only, fl_cbpending,
                                fl_failed, remote_handle, bl_ast_sent,
                                server_got_cancel, enqueue_sent,
                                enqueue_failed, bl_ast_arrived,
                                cancel_rpc_sent, res_lock >>

SP_SendBLAST == /\ pc["server"] = "SP_SendBLAST"
                /\ bl_ast_sent' = TRUE
                /\ bl_ast_arrived' = TRUE
                /\ pc' = [pc EXCEPT !["server"] = "SP_FailEnqueue"]
                /\ UNCHANGED << fl_bl_ast, fl_local_only, fl_cbpending,
                                fl_failed, remote_handle, lock_on_server,
                                server_got_cancel, enqueue_sent,
                                enqueue_failed, cancel_rpc_sent, res_lock >>

SP_FailEnqueue == /\ pc["server"] = "SP_FailEnqueue"
                  /\ enqueue_failed' = TRUE
                  /\ pc' = [pc EXCEPT !["server"] = "SP_Done"]
                  /\ UNCHANGED << fl_bl_ast, fl_local_only, fl_cbpending,
                                  fl_failed, remote_handle, lock_on_server,
                                  bl_ast_sent, server_got_cancel, enqueue_sent,
                                  bl_ast_arrived, cancel_rpc_sent, res_lock >>

SP_Done == /\ pc["server"] = "SP_Done"
           /\ TRUE
           /\ pc' = [pc EXCEPT !["server"] = "Done"]
           /\ UNCHANGED << fl_bl_ast, fl_local_only, fl_cbpending, fl_failed,
                           remote_handle, lock_on_server, bl_ast_sent,
                           server_got_cancel, enqueue_sent, enqueue_failed,
                           bl_ast_arrived, cancel_rpc_sent, res_lock >>

ServerProcess == SP_Wait \/ SP_PlaceLock \/ SP_SendBLAST \/ SP_FailEnqueue
                    \/ SP_Done

CE_Send == /\ pc["client_enqueue"] = "CE_Send"
           /\ enqueue_sent' = TRUE
           /\ pc' = [pc EXCEPT !["client_enqueue"] = "CE_Done"]
           /\ UNCHANGED << fl_bl_ast, fl_local_only, fl_cbpending, fl_failed,
                           remote_handle, lock_on_server, bl_ast_sent,
                           server_got_cancel, enqueue_failed, bl_ast_arrived,
                           cancel_rpc_sent, res_lock >>

CE_Done == /\ pc["client_enqueue"] = "CE_Done"
           /\ TRUE
           /\ pc' = [pc EXCEPT !["client_enqueue"] = "Done"]
           /\ UNCHANGED << fl_bl_ast, fl_local_only, fl_cbpending, fl_failed,
                           remote_handle, lock_on_server, bl_ast_sent,
                           server_got_cancel, enqueue_sent, enqueue_failed,
                           bl_ast_arrived, cancel_rpc_sent, res_lock >>

ClientEnqueue == CE_Send \/ CE_Done

BL_Wait == /\ pc["bl_ast_receiver"] = "BL_Wait"
           /\ bl_ast_arrived
           /\ pc' = [pc EXCEPT !["bl_ast_receiver"] = "BL_Lock"]
           /\ UNCHANGED << fl_bl_ast, fl_local_only, fl_cbpending, fl_failed,
                           remote_handle, lock_on_server, bl_ast_sent,
                           server_got_cancel, enqueue_sent, enqueue_failed,
                           bl_ast_arrived, cancel_rpc_sent, res_lock >>

BL_Lock == /\ pc["bl_ast_receiver"] = "BL_Lock"
           /\ res_lock = "free"
           /\ res_lock' = "bl_ast"
           /\ pc' = [pc EXCEPT !["bl_ast_receiver"] = "BL_CheckFailed"]
           /\ UNCHANGED << fl_bl_ast, fl_local_only, fl_cbpending, fl_failed,
                           remote_handle, lock_on_server, bl_ast_sent,
                           server_got_cancel, enqueue_sent, enqueue_failed,
                           bl_ast_arrived, cancel_rpc_sent >>

BL_CheckFailed == /\ pc["bl_ast_receiver"] = "BL_CheckFailed"
                  /\ IF InjectBugLocalOnly
                        THEN /\ fl_bl_ast' = TRUE
                             /\ fl_cbpending' = TRUE
                             /\ remote_handle' = 1
                             /\ res_lock' = "free"
                             /\ pc' = [pc EXCEPT !["bl_ast_receiver"] = "BL_TriggerCancel"]
                             /\ UNCHANGED server_got_cancel
                        ELSE /\ IF fl_failed
                                   THEN /\ server_got_cancel' = TRUE
                                        /\ res_lock' = "free"
                                        /\ pc' = [pc EXCEPT !["bl_ast_receiver"] = "BL_Done"]
                                        /\ UNCHANGED << fl_bl_ast, fl_cbpending, remote_handle >>
                                   ELSE /\ fl_bl_ast' = TRUE
                                        /\ fl_cbpending' = TRUE
                                        /\ remote_handle' = 1
                                        /\ pc' = [pc EXCEPT !["bl_ast_receiver"] = "BL_Unlock"]
                                        /\ UNCHANGED << server_got_cancel, res_lock >>
                  /\ UNCHANGED << fl_local_only, fl_failed, lock_on_server,
                                  bl_ast_sent, enqueue_sent, enqueue_failed,
                                  bl_ast_arrived, cancel_rpc_sent >>

BL_Unlock == /\ pc["bl_ast_receiver"] = "BL_Unlock"
             /\ res_lock' = "free"
             /\ pc' = [pc EXCEPT !["bl_ast_receiver"] = "BL_TriggerCancel"]
             /\ UNCHANGED << fl_bl_ast, fl_local_only, fl_cbpending, fl_failed,
                             remote_handle, lock_on_server, bl_ast_sent,
                             server_got_cancel, enqueue_sent, enqueue_failed,
                             bl_ast_arrived, cancel_rpc_sent >>

BL_TriggerCancel == /\ pc["bl_ast_receiver"] = "BL_TriggerCancel"
                    /\ res_lock = "free"
                    /\ res_lock' = "bl_cancel"
                    /\ pc' = [pc EXCEPT !["bl_ast_receiver"] = "BL_CancelCheck"]
                    /\ UNCHANGED << fl_bl_ast, fl_local_only, fl_cbpending,
                                    fl_failed, remote_handle, lock_on_server,
                                    bl_ast_sent, server_got_cancel,
                                    enqueue_sent, enqueue_failed,
                                    bl_ast_arrived, cancel_rpc_sent >>

BL_CancelCheck == /\ pc["bl_ast_receiver"] = "BL_CancelCheck"
                  /\ IF ~fl_local_only
                        THEN /\ cancel_rpc_sent' = TRUE
                             /\ server_got_cancel' = TRUE
                        ELSE /\ TRUE
                             /\ UNCHANGED << cancel_rpc_sent, server_got_cancel >>
                  /\ pc' = [pc EXCEPT !["bl_ast_receiver"] = "BL_CancelDone"]
                  /\ UNCHANGED << fl_bl_ast, fl_local_only, fl_cbpending,
                                  fl_failed, remote_handle, lock_on_server,
                                  bl_ast_sent, enqueue_sent, enqueue_failed,
                                  bl_ast_arrived, res_lock >>

BL_CancelDone == /\ pc["bl_ast_receiver"] = "BL_CancelDone"
                 /\ res_lock' = "free"
                 /\ pc' = [pc EXCEPT !["bl_ast_receiver"] = "BL_Done"]
                 /\ UNCHANGED << fl_bl_ast, fl_local_only, fl_cbpending,
                                 fl_failed, remote_handle, lock_on_server,
                                 bl_ast_sent, server_got_cancel,
                                 enqueue_sent, enqueue_failed,
                                 bl_ast_arrived, cancel_rpc_sent >>

BL_Done == /\ pc["bl_ast_receiver"] = "BL_Done"
           /\ TRUE
           /\ pc' = [pc EXCEPT !["bl_ast_receiver"] = "Done"]
           /\ UNCHANGED << fl_bl_ast, fl_local_only, fl_cbpending, fl_failed,
                           remote_handle, lock_on_server, bl_ast_sent,
                           server_got_cancel, enqueue_sent, enqueue_failed,
                           bl_ast_arrived, cancel_rpc_sent, res_lock >>

BLASTReceiver == BL_Wait \/ BL_Lock \/ BL_CheckFailed \/ BL_Unlock
                    \/ BL_TriggerCancel \/ BL_CancelCheck
                    \/ BL_CancelDone \/ BL_Done

FC_Wait == /\ pc["failed_cleanup"] = "FC_Wait"
           /\ enqueue_failed
           /\ pc' = [pc EXCEPT !["failed_cleanup"] = "FC_Lock"]
           /\ UNCHANGED << fl_bl_ast, fl_local_only, fl_cbpending, fl_failed,
                           remote_handle, lock_on_server, bl_ast_sent,
                           server_got_cancel, enqueue_sent, enqueue_failed,
                           bl_ast_arrived, cancel_rpc_sent, res_lock >>

FC_Lock == /\ pc["failed_cleanup"] = "FC_Lock"
           /\ res_lock = "free"
           /\ res_lock' = "cleanup"
           /\ pc' = [pc EXCEPT !["failed_cleanup"] = "FC_SetFlags"]
           /\ UNCHANGED << fl_bl_ast, fl_local_only, fl_cbpending, fl_failed,
                           remote_handle, lock_on_server, bl_ast_sent,
                           server_got_cancel, enqueue_sent, enqueue_failed,
                           bl_ast_arrived, cancel_rpc_sent >>

FC_SetFlags == /\ pc["failed_cleanup"] = "FC_SetFlags"
               /\ fl_failed' = TRUE
               /\ fl_cbpending' = TRUE
               /\ pc' = [pc EXCEPT !["failed_cleanup"] = "FC_CheckBLAST"]
               /\ UNCHANGED << fl_bl_ast, fl_local_only, remote_handle,
                               lock_on_server, bl_ast_sent, server_got_cancel,
                               enqueue_sent, enqueue_failed, bl_ast_arrived,
                               cancel_rpc_sent, res_lock >>

FC_CheckBLAST == /\ pc["failed_cleanup"] = "FC_CheckBLAST"
                 /\ IF InjectBugLocalOnly
                       THEN /\ fl_local_only' = TRUE
                       ELSE /\ IF ~(fl_bl_ast /\ remote_handle /= 0)
                                  THEN /\ fl_local_only' = TRUE
                                  ELSE /\ TRUE
                                       /\ UNCHANGED fl_local_only
                 /\ pc' = [pc EXCEPT !["failed_cleanup"] = "FC_Unlock"]
                 /\ UNCHANGED << fl_bl_ast, fl_cbpending, fl_failed,
                                 remote_handle, lock_on_server, bl_ast_sent,
                                 server_got_cancel, enqueue_sent,
                                 enqueue_failed, bl_ast_arrived,
                                 cancel_rpc_sent, res_lock >>

FC_Unlock == /\ pc["failed_cleanup"] = "FC_Unlock"
             /\ res_lock' = "free"
             /\ pc' = [pc EXCEPT !["failed_cleanup"] = "FC_Cancel"]
             /\ UNCHANGED << fl_bl_ast, fl_local_only, fl_cbpending, fl_failed,
                             remote_handle, lock_on_server, bl_ast_sent,
                             server_got_cancel, enqueue_sent, enqueue_failed,
                             bl_ast_arrived, cancel_rpc_sent >>

FC_Cancel == /\ pc["failed_cleanup"] = "FC_Cancel"
             /\ res_lock = "free"
             /\ res_lock' = "cleanup"
             /\ pc' = [pc EXCEPT !["failed_cleanup"] = "FC_CancelCheck"]
             /\ UNCHANGED << fl_bl_ast, fl_local_only, fl_cbpending, fl_failed,
                             remote_handle, lock_on_server, bl_ast_sent,
                             server_got_cancel, enqueue_sent, enqueue_failed,
                             bl_ast_arrived, cancel_rpc_sent >>

FC_CancelCheck == /\ pc["failed_cleanup"] = "FC_CancelCheck"
                  /\ IF ~fl_local_only
                        THEN /\ cancel_rpc_sent' = TRUE
                             /\ server_got_cancel' = TRUE
                        ELSE /\ TRUE
                             /\ UNCHANGED << cancel_rpc_sent, server_got_cancel >>
                  /\ pc' = [pc EXCEPT !["failed_cleanup"] = "FC_CancelDone"]
                  /\ UNCHANGED << fl_bl_ast, fl_local_only, fl_cbpending,
                                  fl_failed, remote_handle, lock_on_server,
                                  bl_ast_sent, enqueue_sent, enqueue_failed,
                                  bl_ast_arrived, res_lock >>

FC_CancelDone == /\ pc["failed_cleanup"] = "FC_CancelDone"
                 /\ res_lock' = "free"
                 /\ pc' = [pc EXCEPT !["failed_cleanup"] = "FC_Done"]
                 /\ UNCHANGED << fl_bl_ast, fl_local_only, fl_cbpending,
                                 fl_failed, remote_handle, lock_on_server,
                                 bl_ast_sent, server_got_cancel,
                                 enqueue_sent, enqueue_failed,
                                 bl_ast_arrived, cancel_rpc_sent >>

FC_Done == /\ pc["failed_cleanup"] = "FC_Done"
           /\ TRUE
           /\ pc' = [pc EXCEPT !["failed_cleanup"] = "Done"]
           /\ UNCHANGED << fl_bl_ast, fl_local_only, fl_cbpending, fl_failed,
                           remote_handle, lock_on_server, bl_ast_sent,
                           server_got_cancel, enqueue_sent, enqueue_failed,
                           bl_ast_arrived, cancel_rpc_sent, res_lock >>

FailedCleanup == FC_Wait \/ FC_Lock \/ FC_SetFlags \/ FC_CheckBLAST
                    \/ FC_Unlock \/ FC_Cancel \/ FC_CancelCheck
                    \/ FC_CancelDone \/ FC_Done

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == ServerProcess \/ ClientEnqueue \/ BLASTReceiver \/ FailedCleanup
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(ServerProcess)
        /\ WF_vars(ClientEnqueue)
        /\ WF_vars(BLASTReceiver)
        /\ WF_vars(FailedCleanup)

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION
=============================================================================
