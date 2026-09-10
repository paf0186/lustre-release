---------------------- MODULE recovery_model_multiepoch ----------------------
(*
 * TLA+ specification of the Lustre VBR recovery protocol with
 * multiple server restarts while the client is disconnected.
 *
 * Extends recovery_model.tla to cover a key edge case: the server
 * restarts N times (N <= MaxRestarts) before the client reconnects,
 * leaving cli_epoch stale by up to N epochs.  The VBR filter must
 * still correctly decide which requests to replay based on the
 * server's persistent committed_set, regardless of epoch gap.
 *
 * Subsystem: lustre/ptlrpc/import.c, lustre/target/tgt_handler.c,
 *            lustre/ptlrpc/recover.c, lustre/ptlrpc/service.c
 *
 * Source (lustre-release master 47638add78).  This is a protocol-level
 * abstraction; each action stands for the following code paths:
 *   ClientSendRequest / ServerCommitRequest:
 *     lustre/ptlrpc/service.c:2470 ptlrpc_server_handle_request ->
 *       lustre/target/tgt_handler.c:751 tgt_request_handle
 *     lustre/target/tgt_lastrcvd.c:1478-1640 tgt_last_rcvd_update
 *       (transno assignment 1519-1523; per-export lcd_last_transno and
 *       lcd_pre_versions 1586-1596)
 *     lustre/target/tgt_lastrcvd.c:936-988 tgt_cb_last_committed
 *       (obd_last_committed / exp_last_committed = srv_committed_set)
 *   Disconnect:
 *     lustre/ptlrpc/import.c:162-218 ptlrpc_set_import_discon (FULL ->
 *       DISCON), :427-437 ptlrpc_fail_import
 *   ServerRestart (srv_recovering, srv_epoch):
 *     lustre/ldlm/ldlm_lib.c:3072-3099 target_recovery_init,
 *       :2853-3001 target_recovery_thread (OBDF_RECOVERING set 2892)
 *     lustre/target/tgt_lastrcvd.c:867-924 tgt_boot_epoch_update
 *       (lsd_start_epoch / LR_EPOCH_BITS = srv_epoch; NB the code bumps
 *       it at the end of replay, ldlm_lib.c:2942, or immediately when
 *       there is nothing to recover, ldlm_lib.c:3081)
 *   ClientReconnect / ServerAcceptReconnect / ServerRejectReconnect:
 *     lustre/ptlrpc/import.c:728-879 ptlrpc_connect_import_locked,
 *       :1088-1563 ptlrpc_connect_interpret (MSG_CONNECT_RECOVERING ->
 *       REPLAY 1367 / REPLAY_LOCKS 1279; EVICTED 1336, 1348, 1384)
 *     lustre/ldlm/ldlm_lib.c:1157-1751 target_handle_connect (unknown
 *       client denied during recovery 1483-1518; accept: exp_failed race
 *       check 1657-1664, exp_in_recovery / replay_needed 1665-1667,
 *       obd_connected_clients 1698-1700; MSG_CONNECT_RECOVERING 1731-1732)
 *   ServerEvictClient (eviction timer):
 *     lustre/ldlm/ldlm_lib.c:2035-2072 target_start_recovery_timer,
 *       :2081-2136 extend_recovery_timer, :3056-3070
 *       target_recovery_expired (obd_recovery_expired), :2357-2568
 *       target_recovery_overseer (hard timeout 2374-2437; stale export
 *       eviction 2416, 2454, 2463, 2503), :2188-2224 exp_connect_healthy /
 *       exp_req_replay_healthy / exp_lock_replay_healthy / exp_vbr_healthy
 *     lustre/obdclass/genops.c:1564-1612 class_disconnect_stale_exports
 *   ClientReplayRequest / ClientSkipStaleRequest (VBR):
 *     lustre/ptlrpc/recover.c:34-139 ptlrpc_replay_next (replay cursor,
 *       imp_committed_list then imp_replay_list, imp_last_replay_transno)
 *     lustre/target/tgt_handler.c:546-608 tgt_handle_recovery
 *       (req_can_reconstruct 565-583), :500-545 tgt_filter_recovery_request
 *     lustre/ldlm/ldlm_lib.c:3141-3402 target_queue_recovery_request,
 *       :2232-2308 check_for_next_transno (transno ordering),
 *       :2705-2851 replay_request_or_update
 *     lustre/target/tgt_lastrcvd.c:1602-1619 VBR failure: a replay whose
 *       transno is below the slot's lcd_last_transno sets exp_vbr_failed
 *       and returns -EOVERFLOW
 *   ClientReplayDone / ServerReplayComplete:
 *     lustre/ptlrpc/import.c:1598-1628 signal_completed_replay
 *       (MSG_REQ_REPLAY_DONE | MSG_LOCK_REPLAY_DONE)
 *     lustre/ldlm/ldlm_lib.c:3101-3139 target_process_req_flags
 *       (obd_req_replay_clients / obd_lock_replay_clients)
 *   RecoveryComplete:
 *     lustre/ldlm/ldlm_lib.c:1884-1937 target_finish_recovery,
 *       :2965 OBDF_RECOVERING cleared
 *     lustre/ptlrpc/import.c:1686-1800 ptlrpc_import_recovery_state_machine
 *       (RECOVER -> FULL 1771-1777)
 *
 * Validated against: lustre-release master 47638add78 (2026-09-06)
 * Validation notes:
 *   - Source refs added (there were none).  All referenced mechanisms are
 *     present; no modeled transition contradicts the code.
 *   - Known abstractions (not drift): the model filters replays on the
 *     client (ClientReplayRequest/ClientSkipStaleRequest); in the code
 *     the client replays every request on its replay lists
 *     (ptlrpc_replay_next) and the server rejects version-mismatched
 *     replays with -EOVERFLOW / exp_vbr_failed, later evicting such
 *     exports (exp_vbr_healthy, ldlm_lib.c:2503).  srv_epoch is an
 *     incarnation counter: the on-disk lsd_start_epoch is bumped by
 *     tgt_boot_epoch_update once per completed recovery (or immediately
 *     when there are no clients to recover, ldlm_lib.c:3081), so
 *     consecutive crashes before any client reconnects do not each bump
 *     it as ServerRestart does.  InjectPartialPersist and InjectNoEpochBump
 *     have no counterpart in the code (last_rcvd is written
 *     transactionally, tgt_server_data_update tgt_lastrcvd.c:715).
 *
 * Bug injections:
 *   InjectStrictEpochMatch = TRUE  =>  VBR filter requires exact
 *   epoch match (req_epoch = cli_epoch) and ignores committed_set
 *   when the epoch gap is > 1.  This causes committed requests to
 *   be incorrectly skipped after multiple server restarts.
 *
 *   InjectPartialPersist = TRUE  =>  On each server restart, the
 *   highest transno in srv_committed_set is dropped, simulating
 *   incomplete fsync / journal write.  This causes committed
 *   requests to lose their persistent record and be skipped.
 *
 *   InjectNoEpochBump = TRUE  =>  Server restart does not bump
 *   srv_epoch.  Epoch matching then succeeds for ALL queued
 *   requests (including uncommitted ones), causing data corruption.
 *
 * Abstractions:
 *   - Single client, single server (sufficient for VBR correctness).
 *   - Request pool is a small finite set (MaxRequests, default 2).
 *   - Transaction numbers bounded by MaxTransno.
 *   - Server epoch bounded by MaxEpoch (= 1 + MaxRestarts).
 *   - srv_committed_set survives restarts (persistent storage).
 *   - Network modeled implicitly: disconnect event breaks connection,
 *     reconnect RPC reaches server directly.
 *   - Single disconnect period with up to MaxRestarts server restarts
 *     before client reconnects.
 *)

EXTENDS Integers, FiniteSets, TLC

CONSTANTS
    MaxRequests,            \* Number of requests in the pool (e.g., 2)
    MaxTransno,             \* Upper bound on transaction numbers (e.g., 3)
    MaxEpoch,               \* Upper bound on server epochs (e.g., 3)
    MaxRestarts,            \* Max server restarts while client is disconnected (e.g., 2)
    InjectStrictEpochMatch, \* Bug injection: TRUE = strict epoch match only
    InjectPartialPersist,   \* Bug injection: TRUE = lose highest committed transno on restart
    InjectNoEpochBump       \* Bug injection: TRUE = server restart doesn't bump epoch

Requests == 1..MaxRequests

\* ================================================================
\* Variables
\* ================================================================

VARIABLES
    \* --- Client state ---
    cli_state,          \* "FULL" | "DISCON" | "CONNECTING" | "REPLAY" |
                        \*   "REPLAY_WAIT" | "RECOVER" | "EVICTED"
    cli_epoch,          \* Client's view of the server epoch
    cli_last_transno,   \* Highest transno seen by client
    cli_replay_queue,   \* Set of request IDs queued for replay
    cli_replaying,      \* Set of request IDs already replayed this recovery

    \* --- Per-request client state ---
    req_transno,        \* [Requests -> 0..MaxTransno] transno assigned by server
    req_epoch,          \* [Requests -> 0..MaxEpoch] epoch when request was sent
    req_committed,      \* [Requests -> BOOLEAN] server committed this request
    req_status,         \* [Requests -> "unsent"|"inflight"|"completed"|"replayed"]

    \* --- Server state ---
    srv_epoch,          \* Current server epoch (bumped on each restart)
    srv_last_transno,   \* Highest committed transno on server
    srv_recovering,     \* TRUE if server is in recovery mode
    srv_connected,      \* TRUE if client is connected
    srv_evict_pending,  \* TRUE if eviction timer is running
    srv_replay_complete,\* TRUE if replay phase is done
    srv_committed_set,  \* Set of transnos committed on server (persistent)
    srv_restart_count,  \* Number of restarts in current disconnect period

    \* --- Protocol flag ---
    done                \* TRUE when protocol has completed (for termination)

vars == << cli_state, cli_epoch, cli_last_transno, cli_replay_queue,
           cli_replaying, req_transno, req_epoch, req_committed,
           req_status, srv_epoch, srv_last_transno, srv_recovering,
           srv_connected, srv_evict_pending, srv_replay_complete,
           srv_committed_set, srv_restart_count, done >>

\* ================================================================
\* Initial state
\* ================================================================

Init ==
    \* Client starts connected and operational
    /\ cli_state = "FULL"
    /\ cli_epoch = 1
    /\ cli_last_transno = 0
    /\ cli_replay_queue = {}
    /\ cli_replaying = {}
    \* No requests sent yet
    /\ req_transno = [r \in Requests |-> 0]
    /\ req_epoch = [r \in Requests |-> 0]
    /\ req_committed = [r \in Requests |-> FALSE]
    /\ req_status = [r \in Requests |-> "unsent"]
    \* Server starts normally
    /\ srv_epoch = 1
    /\ srv_last_transno = 0
    /\ srv_recovering = FALSE
    /\ srv_connected = TRUE
    /\ srv_evict_pending = FALSE
    /\ srv_replay_complete = FALSE
    /\ srv_committed_set = {}
    /\ srv_restart_count = 0
    /\ done = FALSE

\* ================================================================
\* Normal operation: client sends requests, server processes them
\* ================================================================

\* Client sends a new request to server (normal path)
ClientSendRequest(r) ==
    /\ ~done
    /\ cli_state = "FULL"
    /\ req_status[r] = "unsent"
    /\ cli_last_transno < MaxTransno
    /\ srv_connected
    /\ ~srv_recovering
    \* Assign next transno, record epoch
    /\ LET t == cli_last_transno + 1
       IN /\ req_transno' = [req_transno EXCEPT ![r] = t]
          /\ req_epoch' = [req_epoch EXCEPT ![r] = srv_epoch]
          /\ cli_last_transno' = t
          /\ req_status' = [req_status EXCEPT ![r] = "inflight"]
    /\ UNCHANGED << cli_state, cli_epoch, cli_replay_queue, cli_replaying,
                    req_committed, srv_epoch, srv_last_transno,
                    srv_recovering, srv_connected, srv_evict_pending,
                    srv_replay_complete, srv_committed_set,
                    srv_restart_count, done >>

\* Server processes (commits) an inflight request
ServerCommitRequest(r) ==
    /\ ~done
    /\ req_status[r] = "inflight"
    /\ srv_connected
    /\ ~srv_recovering
    /\ req_epoch[r] = srv_epoch   \* epoch must match
    \* Server commits: advances its last_transno, adds to committed set
    /\ srv_last_transno' = IF req_transno[r] > srv_last_transno
                           THEN req_transno[r]
                           ELSE srv_last_transno
    /\ srv_committed_set' = srv_committed_set \union {req_transno[r]}
    /\ req_committed' = [req_committed EXCEPT ![r] = TRUE]
    /\ req_status' = [req_status EXCEPT ![r] = "completed"]
    \* Client gets reply: request is completed and in replay queue
    /\ cli_replay_queue' = cli_replay_queue \union {r}
    /\ UNCHANGED << cli_state, cli_epoch, cli_last_transno, cli_replaying,
                    req_transno, req_epoch, srv_epoch,
                    srv_recovering, srv_connected, srv_evict_pending,
                    srv_replay_complete, srv_restart_count, done >>

\* ================================================================
\* Disconnect and server restart(s)
\* ================================================================

\* Connection is lost (client detects disconnect)
Disconnect ==
    /\ ~done
    /\ cli_state = "FULL"
    /\ srv_connected
    /\ cli_state' = "DISCON"
    /\ srv_connected' = FALSE
    /\ srv_evict_pending' = TRUE   \* Server starts eviction timer
    /\ srv_restart_count' = 0      \* Reset restart counter
    \* Any inflight requests are "lost" -- mark as needing replay
    /\ req_status' = [r \in Requests |->
                        IF req_status[r] = "inflight"
                        THEN "completed"
                        ELSE req_status[r]]
    \* Client remembers inflight requests for replay
    /\ cli_replay_queue' = cli_replay_queue \union
                           {r \in Requests : req_status[r] = "inflight"}
    /\ UNCHANGED << cli_epoch, cli_last_transno, cli_replaying,
                    req_transno, req_epoch, req_committed,
                    srv_epoch, srv_last_transno, srv_recovering,
                    srv_replay_complete, srv_committed_set, done >>

\* Server restarts (enters recovery mode, bumps epoch).
\* Can happen multiple times while client is disconnected.
\*
\* Bug injection (InjectNoEpochBump): server forgets to bump epoch
\* on restart.  This causes epoch matching to succeed for ALL requests
\* during replay, including uncommitted ones -- a data corruption risk.
\*
\* Bug injection (InjectPartialPersist): the highest transno in
\* committed_set is lost on restart, simulating incomplete fsync/
\* journal write.  This causes committed requests to be incorrectly
\* skipped during VBR replay.
ServerRestart ==
    /\ ~done
    /\ ~srv_connected              \* client is disconnected
    /\ cli_state = "DISCON"        \* client hasn't started reconnecting
    /\ srv_epoch < MaxEpoch
    /\ srv_restart_count < MaxRestarts
    \* If server was already recovering from a prior restart,
    \* it crashes again -- recovery restarts from scratch
    /\ srv_epoch' = IF InjectNoEpochBump THEN srv_epoch
                     ELSE srv_epoch + 1
    /\ srv_recovering' = TRUE
    /\ srv_replay_complete' = FALSE
    /\ srv_evict_pending' = TRUE
    /\ srv_restart_count' = srv_restart_count + 1
    \* Bug injection: InjectPartialPersist -- lose highest committed transno
    /\ IF InjectPartialPersist /\ srv_committed_set /= {}
       THEN LET maxT == CHOOSE t \in srv_committed_set :
                            \A t2 \in srv_committed_set : t >= t2
            IN srv_committed_set' = srv_committed_set \ {maxT}
       ELSE UNCHANGED srv_committed_set
    /\ UNCHANGED << cli_state, cli_epoch, cli_last_transno,
                    cli_replay_queue, cli_replaying,
                    req_transno, req_epoch, req_committed, req_status,
                    srv_last_transno, srv_connected, done >>

\* ================================================================
\* Client reconnect and server response
\* ================================================================

\* Client initiates reconnect attempt
ClientReconnect ==
    /\ ~done
    /\ cli_state = "DISCON"
    /\ cli_state' = "CONNECTING"
    /\ UNCHANGED << cli_epoch, cli_last_transno, cli_replay_queue,
                    cli_replaying, req_transno, req_epoch,
                    req_committed, req_status,
                    srv_epoch, srv_last_transno, srv_recovering,
                    srv_connected, srv_evict_pending, srv_replay_complete,
                    srv_committed_set, srv_restart_count, done >>

\* Server accepts reconnect -- client enters REPLAY
\* Server must be recovering and not yet evicted the client.
ServerAcceptReconnect ==
    /\ ~done
    /\ cli_state = "CONNECTING"
    /\ srv_recovering
    /\ srv_evict_pending       \* client hasn't been evicted yet
    \* Server cancels eviction, accepts client
    /\ srv_evict_pending' = FALSE
    /\ srv_connected' = TRUE
    \* Client gets server's new epoch, enters REPLAY
    /\ cli_state' = "REPLAY"
    /\ cli_epoch' = srv_epoch
    /\ cli_replaying' = {}     \* Clear replayed set for this recovery
    /\ UNCHANGED << cli_last_transno, cli_replay_queue,
                    req_transno, req_epoch, req_committed, req_status,
                    srv_epoch, srv_last_transno, srv_recovering,
                    srv_replay_complete, srv_committed_set,
                    srv_restart_count, done >>

\* Server evicts the client (eviction timer fires before reconnect)
ServerEvictClient ==
    /\ ~done
    /\ srv_evict_pending
    /\ srv_recovering
    /\ ~srv_connected   \* client hasn't reconnected yet
    \* Eviction: cancel timer, mark client as evicted
    /\ srv_evict_pending' = FALSE
    /\ cli_state' = "EVICTED"
    \* Server proceeds without this client
    /\ srv_recovering' = FALSE
    /\ srv_replay_complete' = TRUE
    /\ UNCHANGED << cli_epoch, cli_last_transno, cli_replay_queue,
                    cli_replaying, req_transno, req_epoch,
                    req_committed, req_status,
                    srv_epoch, srv_last_transno, srv_connected,
                    srv_committed_set, srv_restart_count, done >>

\* Server rejects reconnect: not recovering or client already evicted.
\* Client is evicted (terminal -- no retry in this model).
ServerRejectReconnect ==
    /\ ~done
    /\ cli_state = "CONNECTING"
    /\ \/ ~srv_recovering           \* server not in recovery
       \/ ~srv_evict_pending        \* client was evicted
    /\ cli_state' = "EVICTED"
    /\ UNCHANGED << cli_epoch, cli_last_transno, cli_replay_queue,
                    cli_replaying, req_transno, req_epoch,
                    req_committed, req_status,
                    srv_epoch, srv_last_transno, srv_recovering,
                    srv_connected, srv_evict_pending, srv_replay_complete,
                    srv_committed_set, srv_restart_count, done >>

\* ================================================================
\* VBR replay: client replays committed requests with epoch matching
\* ================================================================

\* Client replays a request from the replay queue.
\* VBR filtering: replay if server committed the transno (the
\* version-based criterion), regardless of epoch gap.
\*
\* Bug injection (InjectStrictEpochMatch): when epoch gap > 1,
\* require exact epoch match and ignore committed_set.  This
\* causes committed requests to be incorrectly skipped when the
\* server has restarted multiple times.
ClientReplayRequest(r) ==
    /\ ~done
    /\ cli_state = "REPLAY"
    /\ srv_connected
    /\ srv_recovering
    /\ r \in cli_replay_queue
    /\ r \notin cli_replaying     \* not already replayed this recovery
    \* VBR epoch check with optional bug injection
    /\ IF InjectStrictEpochMatch
       THEN \* BUG: strict epoch match -- only allow replay if epoch
            \* gap <= 1.  For gap > 1, require exact epoch match
            \* (which is impossible since epoch has advanced past
            \* the request's epoch by more than 1).
            \/ req_epoch[r] = cli_epoch                \* same epoch (gap=0)
            \/ (req_epoch[r] = cli_epoch - 1           \* gap=1: allow VBR
                /\ req_transno[r] \in srv_committed_set)
       ELSE \* CORRECT: transno in committed_set is sufficient
            \* for replay regardless of epoch gap
            \/ req_epoch[r] = cli_epoch                \* same epoch
            \/ req_transno[r] \in srv_committed_set    \* VBR: committed
    \* Mark as replayed
    /\ cli_replaying' = cli_replaying \union {r}
    /\ req_status' = [req_status EXCEPT ![r] = "replayed"]
    \* Server re-commits (or recognizes as duplicate)
    /\ srv_last_transno' = IF req_transno[r] > srv_last_transno
                           THEN req_transno[r]
                           ELSE srv_last_transno
    /\ srv_committed_set' = srv_committed_set \union {req_transno[r]}
    /\ UNCHANGED << cli_state, cli_epoch, cli_last_transno,
                    cli_replay_queue, req_transno, req_epoch,
                    req_committed, srv_epoch,
                    srv_recovering, srv_connected, srv_evict_pending,
                    srv_replay_complete, srv_restart_count, done >>

\* Client skips a request whose epoch doesn't match and transno
\* is not in the committed set (VBR filtering: stale request).
\*
\* Bug injection (InjectStrictEpochMatch): when epoch gap > 1,
\* skip the request even if transno IS in committed_set.
ClientSkipStaleRequest(r) ==
    /\ ~done
    /\ cli_state = "REPLAY"
    /\ r \in cli_replay_queue
    /\ r \notin cli_replaying
    \* VBR skip condition with optional bug injection
    /\ IF InjectStrictEpochMatch
       THEN \* BUG: skip if epoch gap > 1 regardless of committed_set
            /\ req_epoch[r] /= cli_epoch
            /\ \/ req_transno[r] \notin srv_committed_set
               \/ req_epoch[r] < cli_epoch - 1  \* gap > 1: skip even if committed
       ELSE \* CORRECT: only skip if epoch mismatch AND not committed
            /\ req_epoch[r] /= cli_epoch
            /\ req_transno[r] \notin srv_committed_set
    \* Remove from queue, don't replay
    /\ cli_replay_queue' = cli_replay_queue \ {r}
    /\ UNCHANGED << cli_state, cli_epoch, cli_last_transno, cli_replaying,
                    req_transno, req_epoch, req_committed, req_status,
                    srv_epoch, srv_last_transno, srv_recovering,
                    srv_connected, srv_evict_pending, srv_replay_complete,
                    srv_committed_set, srv_restart_count, done >>

\* ================================================================
\* Recovery completion
\* ================================================================

\* Client finishes replay: all queued requests have been replayed
\* or skipped.  Client moves to REPLAY_WAIT.
ClientReplayDone ==
    /\ ~done
    /\ cli_state = "REPLAY"
    \* All requests in the replay queue are either replayed or removed
    /\ cli_replay_queue \ cli_replaying = {}
    /\ cli_state' = "REPLAY_WAIT"
    /\ UNCHANGED << cli_epoch, cli_last_transno, cli_replay_queue,
                    cli_replaying, req_transno, req_epoch,
                    req_committed, req_status,
                    srv_epoch, srv_last_transno, srv_recovering,
                    srv_connected, srv_evict_pending, srv_replay_complete,
                    srv_committed_set, srv_restart_count, done >>

\* Server acknowledges replay complete, moves client to RECOVER
ServerReplayComplete ==
    /\ ~done
    /\ cli_state = "REPLAY_WAIT"
    /\ srv_recovering
    /\ srv_connected
    /\ srv_replay_complete' = TRUE
    /\ cli_state' = "RECOVER"
    /\ UNCHANGED << cli_epoch, cli_last_transno, cli_replay_queue,
                    cli_replaying, req_transno, req_epoch,
                    req_committed, req_status,
                    srv_epoch, srv_last_transno, srv_recovering,
                    srv_connected, srv_evict_pending,
                    srv_committed_set, srv_restart_count, done >>

\* Recovery finishes: server exits recovery, client goes FULL
RecoveryComplete ==
    /\ ~done
    /\ cli_state = "RECOVER"
    /\ srv_recovering
    /\ srv_connected
    /\ srv_replay_complete
    \* Both sides return to normal operation
    /\ cli_state' = "FULL"
    /\ srv_recovering' = FALSE
    /\ done' = TRUE
    /\ UNCHANGED << cli_epoch, cli_last_transno,
                    cli_replay_queue, cli_replaying,
                    req_transno, req_epoch, req_committed, req_status,
                    srv_epoch, srv_last_transno,
                    srv_connected, srv_evict_pending, srv_replay_complete,
                    srv_committed_set, srv_restart_count >>

\* Terminal: client was evicted, protocol ends
EvictedTerminal ==
    /\ cli_state = "EVICTED"
    /\ ~done
    /\ done' = TRUE
    /\ UNCHANGED << cli_state, cli_epoch, cli_last_transno,
                    cli_replay_queue, cli_replaying,
                    req_transno, req_epoch, req_committed, req_status,
                    srv_epoch, srv_last_transno, srv_recovering,
                    srv_connected, srv_evict_pending, srv_replay_complete,
                    srv_committed_set, srv_restart_count >>

\* ================================================================
\* Spec
\* ================================================================

\* Allow infinite stuttering once done (prevents deadlock on termination)
Terminating == done /\ UNCHANGED vars

Next ==
    \/ \E r \in Requests : ClientSendRequest(r)
    \/ \E r \in Requests : ServerCommitRequest(r)
    \/ Disconnect
    \/ ServerRestart
    \/ ClientReconnect
    \/ ServerAcceptReconnect
    \/ ServerEvictClient
    \/ ServerRejectReconnect
    \/ \E r \in Requests : ClientReplayRequest(r)
    \/ \E r \in Requests : ClientSkipStaleRequest(r)
    \/ ClientReplayDone
    \/ ServerReplayComplete
    \/ RecoveryComplete
    \/ EvictedTerminal
    \/ Terminating

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

\* ================================================================
\* Invariants
\* ================================================================

\* Type invariant
TypeOK ==
    /\ cli_state \in {"FULL", "DISCON", "CONNECTING", "REPLAY",
                       "REPLAY_WAIT", "RECOVER", "EVICTED"}
    /\ cli_epoch \in 0..MaxEpoch
    /\ cli_last_transno \in 0..MaxTransno
    /\ cli_replay_queue \subseteq Requests
    /\ cli_replaying \subseteq Requests
    /\ \A r \in Requests :
        /\ req_transno[r] \in 0..MaxTransno
        /\ req_epoch[r] \in 0..MaxEpoch
        /\ req_committed[r] \in BOOLEAN
        /\ req_status[r] \in {"unsent", "inflight", "completed", "replayed"}
    /\ srv_epoch \in 0..MaxEpoch
    /\ srv_last_transno \in 0..MaxTransno
    /\ srv_recovering \in BOOLEAN
    /\ srv_connected \in BOOLEAN
    /\ srv_evict_pending \in BOOLEAN
    /\ srv_replay_complete \in BOOLEAN
    /\ srv_committed_set \subseteq 1..MaxTransno
    /\ srv_restart_count \in 0..MaxRestarts
    /\ done \in BOOLEAN

\* SAFETY: Replayed requests must have their transno in the server's
\* committed set.  The epoch gap does NOT matter -- VBR uses the
\* committed_set as the reliable criterion, not epoch proximity.
\* This is the relaxed version: req_transno in committed_set is
\* sufficient even if the epoch gap is > 1.
ReplayedEpochMatch ==
    \A r \in Requests :
        req_status[r] = "replayed" =>
            \/ req_epoch[r] = cli_epoch
            \/ req_transno[r] \in srv_committed_set

\* SAFETY: No request is replayed twice in a single recovery.
NoDoubleReplay ==
    \A r \in Requests :
        req_status[r] = "replayed" => r \in cli_replaying

\* SAFETY: Client epoch never exceeds server epoch.
ClientEpochBound ==
    cli_epoch <= srv_epoch

\* SAFETY: If client is in REPLAY state, server must be recovering.
ReplayImpliesRecovering ==
    cli_state = "REPLAY" => srv_recovering

\* SAFETY: If recovery completes (done=TRUE via RecoveryComplete),
\* then all replayed requests have their transnos in the server's
\* committed set.
RecoveryPreservesCommits ==
    (done /\ cli_state = "FULL") =>
        \A r \in cli_replaying :
            req_transno[r] \in srv_committed_set

\* SAFETY: No replayed request has transno 0 (unsent requests
\* should never be replayed).
NoReplayOfUnsent ==
    \A r \in Requests :
        req_status[r] = "replayed" => req_transno[r] > 0

\* NEW: SAFETY: Epoch gap handling.
\* When recovery completes successfully, every committed request
\* must have been replayed -- regardless of epoch gap.  The VBR
\* committed_set lookup is the reliable criterion; a request with
\* epoch gap > 1 (e.g., req_epoch=1, srv_epoch=3) should still be
\* replayed if its transno is in the committed_set.
\*
\* The bug injection (InjectStrictEpochMatch) violates this: it
\* requires exact epoch match for gap > 1, causing committed
\* requests to be incorrectly skipped.
EpochGapHandled ==
    (done /\ cli_state = "FULL") =>
        \A r \in Requests :
            (req_committed[r] /\ req_transno[r] > 0)
                => r \in cli_replaying

\* ================================================================
\* New invariants: multi-epoch edge-case coverage
\* ================================================================

\* (a) Operations from a skipped epoch are never replayed.
\* A "skipped epoch" is one the server passed through but the client
\* never operated in.  SentEpochs = {epoch of each request that was
\* actually sent}.  Any replayed request must be from a sent epoch.
SkippedEpochOpsNeverReplayed ==
    LET SentEpochs == {req_epoch[r] : r \in {s \in Requests : req_transno[s] > 0}}
    IN \A r \in Requests :
        r \in cli_replaying => req_epoch[r] \in SentEpochs

\* (b) Epoch monotonicity: replayed requests' epochs are bounded by
\* the current client epoch (no "future epoch" replays).  Combined
\* with SkippedEpochOpsNeverReplayed, this bounds the epoch range.
\* In a multi-cycle extension with an ordering variable this would
\* check non-decreasing epoch order; here we check the upper bound.
EpochMonotonicReplay ==
    \A r \in Requests :
        r \in cli_replaying => req_epoch[r] <= cli_epoch

\* (c) No operation replayed against wrong epoch's server state.
\* During the REPLAY phase the client and server must agree on the
\* current epoch -- a desynchronization means replaying against stale
\* or future server state.
NoReplayAgainstWrongEpoch ==
    cli_state = "REPLAY" => cli_epoch = srv_epoch

\* (d) Committed-set integrity (persistence check): if the server
\* committed a request, its transno must remain in srv_committed_set.
\* Catches partial-persistence / journal-ordering bugs on restart.
CommittedSetIntegrity ==
    \A r \in Requests :
        req_committed[r] => req_transno[r] \in srv_committed_set

\* (e) Uncommitted requests should never be replayed.  The VBR filter
\* must ensure only server-committed operations are re-applied.
\* Catches the missing-epoch-bump bug (InjectNoEpochBump) where
\* epoch matching succeeds for all requests including uncommitted ones.
UncommittedNeverReplayed ==
    \A r \in Requests :
        req_status[r] = "replayed" => req_committed[r]

\* (f) Server transno consistency: srv_last_transno must be at least
\* as large as every transno in the committed set.  A violation means
\* the transno counter drifted below committed data.
ServerTransnoConsistent ==
    \A t \in srv_committed_set : t <= srv_last_transno

\* ================================================================
\* Temporal properties
\* ================================================================

\* Recovery eventually completes (either FULL or EVICTED)
EventuallyDone == <>(done)

=============================================================================
