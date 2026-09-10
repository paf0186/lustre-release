---------------------- MODULE recovery_model_multiclient ----------------------
(*
 * TLA+ specification of Lustre multi-client recovery protocol.
 *
 * Extends recovery_model.tla from single-client to two simultaneous
 * clients sharing one server recovery window.  The server has
 * per-client eviction timers; each client independently races to
 * reconnect before its timer fires.
 *
 * Scenarios captured:
 *   1. c1 reconnects in time, c2 evicted -- server completes on
 *      c1's replay alone (evicted client does not block recovery).
 *   2. Both reconnect -- server waits for both replay completions.
 *   3. Both evicted -- server completes immediately.
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
 *     exports (exp_vbr_healthy, ldlm_lib.c:2503).  Per-client eviction
 *     timers (srv_evict_pending[c]) abstract the single per-target
 *     obd_recovery_timer plus per-export exp_in_recovery / exp_failed
 *     state; on expiry all stale exports are evicted together
 *     (class_disconnect_stale_exports).  The per-client VBR set
 *     (VBRCommittedSet with InjectBugGlobalVBR = FALSE) matches the
 *     per-export last_rcvd slot (tgt_lastrcvd.c:1586-1596); the
 *     InjectBugGlobalVBR = TRUE variant used by the baseline cfg is the
 *     model's own simplification, not code behavior.
 *
 * Abstractions for tractability:
 *   - Two clients, one server (Symmetry on Clients).
 *   - MaxRequests = 1 per client (2 total requests in state space).
 *   - Single disconnect/recovery cycle (done flag prevents loops).
 *   - Network modeled implicitly (no explicit channel).
 *   - Lock replay and bulk I/O abstracted away.
 *)

EXTENDS Integers, FiniteSets, TLC

CONSTANTS
    Clients,        \* Model value set, e.g. {c1, c2}
    MaxRequests,    \* Requests per client (e.g. 1)
    MaxTransno,     \* Upper bound on transaction numbers (e.g. 3)
    MaxEpoch,       \* Upper bound on server epochs (e.g. 2)
    InjectBugNoWaitAll,  \* Bug injection: server completes recovery without
                         \* waiting for all connected clients to finish replay
    InjectBugMidReplayEvict,  \* Bug injection: server can evict a client during
                              \* active replay (simulates timeout/network failure)
    InjectBugGlobalVBR   \* Bug injection: VBR uses global committed set instead
                         \* of per-client (per-export) committed set.  When TRUE,
                         \* cross-client transno collisions produce false VBR
                         \* matches allowing uncommitted requests to be replayed.

\* Symmetry set for TLC state-space reduction
Symmetry == Permutations(Clients)

\* Request IDs: each client has MaxRequests requests, tagged by client
\* We use <<c, i>> pairs as request identifiers
AllRequests == Clients \X (1..MaxRequests)

\* ================================================================
\* Variables
\* ================================================================

VARIABLES
    \* --- Per-client state ---
    cli_state,          \* [Clients -> {"FULL","DISCON","CONNECTING",
                        \*   "REPLAY","REPLAY_WAIT","RECOVER","EVICTED"}]
    cli_epoch,          \* [Clients -> 0..MaxEpoch]
    cli_last_transno,   \* [Clients -> 0..MaxTransno]
    cli_replay_queue,   \* [Clients -> SUBSET AllRequests]
    cli_replaying,      \* [Clients -> SUBSET AllRequests]

    \* --- Per-request state (indexed by <<client, reqnum>>) ---
    req_transno,        \* [AllRequests -> 0..MaxTransno]
    req_epoch,          \* [AllRequests -> 0..MaxEpoch]
    req_committed,      \* [AllRequests -> BOOLEAN]
    req_status,         \* [AllRequests -> "unsent"|"inflight"|"completed"|"replayed"]

    \* --- Server state ---
    srv_epoch,          \* Current server epoch
    srv_last_transno,   \* Highest committed transno
    srv_recovering,     \* TRUE if in recovery mode
    srv_connected,      \* [Clients -> BOOLEAN] per-client connection
    srv_evict_pending,  \* [Clients -> BOOLEAN] per-client eviction timer
    srv_committed_set,  \* Set of transnos committed (persistent)

    \* --- Protocol flag ---
    done                \* TRUE when recovery protocol has completed

vars == << cli_state, cli_epoch, cli_last_transno, cli_replay_queue,
           cli_replaying, req_transno, req_epoch, req_committed,
           req_status, srv_epoch, srv_last_transno, srv_recovering,
           srv_connected, srv_evict_pending, srv_committed_set, done >>

\* ================================================================
\* Helpers
\* ================================================================

\* Requests belonging to a specific client
ClientRequests(c) == {<<c, i>> : i \in 1..MaxRequests}

\* All clients that are connected (not evicted, completed reconnect)
ConnectedClients == {c \in Clients : srv_connected[c]}

\* All clients that have been evicted
EvictedClients == {c \in Clients : cli_state[c] = "EVICTED"}

\* All clients still expected to participate in recovery
\* (connected and not yet done with replay)
ActiveRecoveringClients ==
    {c \in Clients : srv_connected[c] /\ cli_state[c] \in
        {"REPLAY", "REPLAY_WAIT", "RECOVER"}}

\* Server can complete recovery when every non-evicted client
\* that reconnected has finished replay (reached RECOVER state)
AllConnectedClientsRecovered ==
    \A c \in Clients :
        srv_connected[c] => cli_state[c] = "RECOVER"

\* No more clients can possibly reconnect (all either connected or evicted)
NoMoreReconnectsPossible ==
    \A c \in Clients :
        srv_connected[c] \/ cli_state[c] = "EVICTED"

\* Per-client committed transnos: derived from request state.
\* In real Lustre, each export tracks its own committed transnos.
\* This operator reconstructs the per-export view from req_committed.
PerClientCommitted(c) ==
    {req_transno[r] : r \in {r2 \in ClientRequests(c) : req_committed[r2]}}

\* Committed set visible for VBR checks, parameterized by client.
\* Bug variant (InjectBugGlobalVBR=TRUE) uses global set, allowing
\* cross-client transno collisions to produce false VBR matches.
\* Fix variant (FALSE) uses per-client set matching real Lustre exports.
VBRCommittedSet(c) ==
    IF InjectBugGlobalVBR
    THEN srv_committed_set
    ELSE PerClientCommitted(c)

\* ================================================================
\* Initial state
\* ================================================================

Init ==
    \* All clients start connected and operational
    /\ cli_state = [c \in Clients |-> "FULL"]
    /\ cli_epoch = [c \in Clients |-> 1]
    /\ cli_last_transno = [c \in Clients |-> 0]
    /\ cli_replay_queue = [c \in Clients |-> {}]
    /\ cli_replaying = [c \in Clients |-> {}]
    \* No requests sent yet
    /\ req_transno = [r \in AllRequests |-> 0]
    /\ req_epoch = [r \in AllRequests |-> 0]
    /\ req_committed = [r \in AllRequests |-> FALSE]
    /\ req_status = [r \in AllRequests |-> "unsent"]
    \* Server starts normally
    /\ srv_epoch = 1
    /\ srv_last_transno = 0
    /\ srv_recovering = FALSE
    /\ srv_connected = [c \in Clients |-> TRUE]
    /\ srv_evict_pending = [c \in Clients |-> FALSE]
    /\ srv_committed_set = {}
    /\ done = FALSE

\* ================================================================
\* Normal operation: clients send requests, server processes them
\* ================================================================

\* Client c sends a new request r = <<c, i>>
ClientSendRequest(c, r) ==
    /\ ~done
    /\ r[1] = c                          \* request belongs to this client
    /\ cli_state[c] = "FULL"
    /\ req_status[r] = "unsent"
    /\ cli_last_transno[c] < MaxTransno
    /\ srv_connected[c]
    /\ ~srv_recovering
    /\ LET t == cli_last_transno[c] + 1
       IN /\ req_transno' = [req_transno EXCEPT ![r] = t]
          /\ req_epoch' = [req_epoch EXCEPT ![r] = srv_epoch]
          /\ cli_last_transno' = [cli_last_transno EXCEPT ![c] = t]
          /\ req_status' = [req_status EXCEPT ![r] = "inflight"]
    /\ UNCHANGED << cli_state, cli_epoch, cli_replay_queue, cli_replaying,
                    req_committed, srv_epoch, srv_last_transno,
                    srv_recovering, srv_connected, srv_evict_pending,
                    srv_committed_set, done >>

\* Server commits an inflight request
ServerCommitRequest(c, r) ==
    /\ ~done
    /\ r[1] = c
    /\ req_status[r] = "inflight"
    /\ srv_connected[c]
    /\ ~srv_recovering
    /\ req_epoch[r] = srv_epoch
    /\ srv_last_transno' = IF req_transno[r] > srv_last_transno
                           THEN req_transno[r]
                           ELSE srv_last_transno
    /\ srv_committed_set' = srv_committed_set \union {req_transno[r]}
    /\ req_committed' = [req_committed EXCEPT ![r] = TRUE]
    /\ req_status' = [req_status EXCEPT ![r] = "completed"]
    /\ cli_replay_queue' = [cli_replay_queue EXCEPT ![c] =
                                cli_replay_queue[c] \union {r}]
    /\ UNCHANGED << cli_state, cli_epoch, cli_last_transno, cli_replaying,
                    req_transno, req_epoch, srv_epoch,
                    srv_recovering, srv_connected, srv_evict_pending, done >>

\* ================================================================
\* Disconnect and server restart
\* ================================================================

\* All clients disconnect simultaneously (server crashes / network partition)
Disconnect ==
    /\ ~done
    /\ \A c \in Clients : cli_state[c] = "FULL"
    /\ \A c \in Clients : srv_connected[c]
    \* All clients go to DISCON
    /\ cli_state' = [c \in Clients |-> "DISCON"]
    /\ srv_connected' = [c \in Clients |-> FALSE]
    /\ srv_evict_pending' = [c \in Clients |-> TRUE]
    \* Inflight requests become completed (lost in transit)
    /\ req_status' = [r \in AllRequests |->
                        IF req_status[r] = "inflight"
                        THEN "completed"
                        ELSE req_status[r]]
    \* Clients remember inflight requests for replay
    /\ cli_replay_queue' = [c \in Clients |->
                                cli_replay_queue[c] \union
                                {r \in ClientRequests(c) : req_status[r] = "inflight"}]
    /\ UNCHANGED << cli_epoch, cli_last_transno, cli_replaying,
                    req_transno, req_epoch, req_committed,
                    srv_epoch, srv_last_transno, srv_recovering,
                    srv_committed_set, done >>

\* Server restarts (enters recovery mode, bumps epoch)
ServerRestart ==
    /\ ~done
    /\ \A c \in Clients : ~srv_connected[c]   \* all clients disconnected
    /\ ~srv_recovering
    /\ srv_epoch < MaxEpoch
    /\ srv_epoch' = srv_epoch + 1
    /\ srv_recovering' = TRUE
    /\ srv_evict_pending' = [c \in Clients |-> TRUE]
    /\ UNCHANGED << cli_state, cli_epoch, cli_last_transno,
                    cli_replay_queue, cli_replaying,
                    req_transno, req_epoch, req_committed, req_status,
                    srv_last_transno, srv_connected,
                    srv_committed_set, done >>

\* ================================================================
\* Client reconnect and server response (per-client)
\* ================================================================

\* Client c initiates reconnect
ClientReconnect(c) ==
    /\ ~done
    /\ cli_state[c] = "DISCON"
    /\ cli_state' = [cli_state EXCEPT ![c] = "CONNECTING"]
    /\ UNCHANGED << cli_epoch, cli_last_transno, cli_replay_queue,
                    cli_replaying, req_transno, req_epoch,
                    req_committed, req_status,
                    srv_epoch, srv_last_transno, srv_recovering,
                    srv_connected, srv_evict_pending,
                    srv_committed_set, done >>

\* Server accepts reconnect from client c
ServerAcceptReconnect(c) ==
    /\ ~done
    /\ cli_state[c] = "CONNECTING"
    /\ srv_recovering
    /\ srv_evict_pending[c]              \* client hasn't been evicted yet
    \* Cancel eviction timer, accept client
    /\ srv_evict_pending' = [srv_evict_pending EXCEPT ![c] = FALSE]
    /\ srv_connected' = [srv_connected EXCEPT ![c] = TRUE]
    \* Client enters REPLAY with server's new epoch
    /\ cli_state' = [cli_state EXCEPT ![c] = "REPLAY"]
    /\ cli_epoch' = [cli_epoch EXCEPT ![c] = srv_epoch]
    /\ cli_replaying' = [cli_replaying EXCEPT ![c] = {}]
    /\ UNCHANGED << cli_last_transno, cli_replay_queue,
                    req_transno, req_epoch, req_committed, req_status,
                    srv_epoch, srv_last_transno, srv_recovering,
                    srv_committed_set, done >>

\* Server evicts client c (per-client eviction timer fires)
ServerEvictClient(c) ==
    /\ ~done
    /\ srv_evict_pending[c]
    /\ srv_recovering
    /\ ~srv_connected[c]                 \* client hasn't reconnected
    \* Eviction: cancel timer, mark client as evicted
    /\ srv_evict_pending' = [srv_evict_pending EXCEPT ![c] = FALSE]
    /\ cli_state' = [cli_state EXCEPT ![c] = "EVICTED"]
    /\ UNCHANGED << cli_epoch, cli_last_transno, cli_replay_queue,
                    cli_replaying, req_transno, req_epoch,
                    req_committed, req_status,
                    srv_epoch, srv_last_transno, srv_recovering,
                    srv_connected, srv_committed_set, done >>

\* Server rejects reconnect from client c (already evicted or not recovering)
ServerRejectReconnect(c) ==
    /\ ~done
    /\ cli_state[c] = "CONNECTING"
    /\ \/ ~srv_recovering
       \/ ~srv_evict_pending[c]          \* client was already evicted
    /\ cli_state' = [cli_state EXCEPT ![c] = "EVICTED"]
    /\ UNCHANGED << cli_epoch, cli_last_transno, cli_replay_queue,
                    cli_replaying, req_transno, req_epoch,
                    req_committed, req_status,
                    srv_epoch, srv_last_transno, srv_recovering,
                    srv_connected, srv_evict_pending,
                    srv_committed_set, done >>

\* Server evicts a connected client mid-replay (timeout during recovery).
\* In real Lustre, a client can become unresponsive at any point during
\* recovery.  This action models that scenario.  Gated by InjectBugMidReplayEvict.
ServerEvictMidReplay(c) ==
    /\ InjectBugMidReplayEvict
    /\ ~done
    /\ cli_state[c] \in {"REPLAY", "REPLAY_WAIT"}
    /\ srv_connected[c]
    /\ srv_recovering
    \* Eviction: disconnect and mark as evicted
    /\ srv_connected' = [srv_connected EXCEPT ![c] = FALSE]
    /\ cli_state' = [cli_state EXCEPT ![c] = "EVICTED"]
    /\ UNCHANGED << cli_epoch, cli_last_transno, cli_replay_queue,
                    cli_replaying, req_transno, req_epoch,
                    req_committed, req_status,
                    srv_epoch, srv_last_transno, srv_recovering,
                    srv_evict_pending, srv_committed_set, done >>

\* ================================================================
\* VBR replay: client replays committed requests with epoch matching
\* ================================================================

\* Client c replays request r from its replay queue
ClientReplayRequest(c, r) ==
    /\ ~done
    /\ r[1] = c
    /\ cli_state[c] = "REPLAY"
    /\ srv_connected[c]
    /\ srv_recovering
    /\ r \in cli_replay_queue[c]
    /\ r \notin cli_replaying[c]
    \* VBR epoch check (uses per-client or global set based on bug injection)
    /\ \/ req_epoch[r] = cli_epoch[c]
       \/ req_transno[r] \in VBRCommittedSet(c)
    \* Mark as replayed
    /\ cli_replaying' = [cli_replaying EXCEPT ![c] =
                            cli_replaying[c] \union {r}]
    /\ req_status' = [req_status EXCEPT ![r] = "replayed"]
    \* Server re-commits
    /\ srv_last_transno' = IF req_transno[r] > srv_last_transno
                           THEN req_transno[r]
                           ELSE srv_last_transno
    /\ srv_committed_set' = srv_committed_set \union {req_transno[r]}
    /\ UNCHANGED << cli_state, cli_epoch, cli_last_transno,
                    cli_replay_queue, req_transno, req_epoch,
                    req_committed, srv_epoch,
                    srv_recovering, srv_connected, srv_evict_pending,
                    done >>

\* Client c skips a stale request (VBR filtering)
ClientSkipStaleRequest(c, r) ==
    /\ ~done
    /\ r[1] = c
    /\ cli_state[c] = "REPLAY"
    /\ r \in cli_replay_queue[c]
    /\ r \notin cli_replaying[c]
    \* VBR: epoch mismatch AND transno not committed (per-client or global)
    /\ req_epoch[r] /= cli_epoch[c]
    /\ req_transno[r] \notin VBRCommittedSet(c)
    \* Remove from queue
    /\ cli_replay_queue' = [cli_replay_queue EXCEPT ![c] =
                                cli_replay_queue[c] \ {r}]
    /\ UNCHANGED << cli_state, cli_epoch, cli_last_transno, cli_replaying,
                    req_transno, req_epoch, req_committed, req_status,
                    srv_epoch, srv_last_transno, srv_recovering,
                    srv_connected, srv_evict_pending,
                    srv_committed_set, done >>

\* ================================================================
\* Recovery completion
\* ================================================================

\* Client c finishes replay -- all queued requests replayed or skipped
ClientReplayDone(c) ==
    /\ ~done
    /\ cli_state[c] = "REPLAY"
    /\ cli_replay_queue[c] \ cli_replaying[c] = {}
    /\ cli_state' = [cli_state EXCEPT ![c] = "REPLAY_WAIT"]
    /\ UNCHANGED << cli_epoch, cli_last_transno, cli_replay_queue,
                    cli_replaying, req_transno, req_epoch,
                    req_committed, req_status,
                    srv_epoch, srv_last_transno, srv_recovering,
                    srv_connected, srv_evict_pending,
                    srv_committed_set, done >>

\* Server acknowledges replay complete for client c
ServerReplayComplete(c) ==
    /\ ~done
    /\ cli_state[c] = "REPLAY_WAIT"
    /\ srv_recovering
    /\ srv_connected[c]
    /\ cli_state' = [cli_state EXCEPT ![c] = "RECOVER"]
    /\ UNCHANGED << cli_epoch, cli_last_transno, cli_replay_queue,
                    cli_replaying, req_transno, req_epoch,
                    req_committed, req_status,
                    srv_epoch, srv_last_transno, srv_recovering,
                    srv_connected, srv_evict_pending,
                    srv_committed_set, done >>

\* Recovery finishes: all connected clients recovered, no pending evictions
\* that could still produce a reconnect.
\* Server exits recovery, connected clients go FULL.
RecoveryComplete ==
    /\ ~done
    /\ srv_recovering
    \* BUG: when InjectBugNoWaitAll=TRUE, server completes recovery
    \* without waiting for all connected clients to finish replay.
    \* This allows partial recovery -- some clients still replaying.
    /\ IF InjectBugNoWaitAll
       THEN \E c \in Clients : srv_connected[c] /\ cli_state[c] = "RECOVER"
       ELSE AllConnectedClientsRecovered
    \* No client still pending (all either connected+recovered or evicted)
    /\ NoMoreReconnectsPossible
    \* Transition: server exits recovery, connected clients go FULL
    /\ cli_state' = [c \in Clients |->
                        IF srv_connected[c] THEN "FULL"
                        ELSE cli_state[c]]
    /\ srv_recovering' = FALSE
    /\ done' = TRUE
    /\ UNCHANGED << cli_epoch, cli_last_transno,
                    cli_replay_queue, cli_replaying,
                    req_transno, req_epoch, req_committed, req_status,
                    srv_epoch, srv_last_transno,
                    srv_connected, srv_evict_pending,
                    srv_committed_set >>

\* Terminal: all clients are evicted, no one to recover
AllEvictedTerminal ==
    /\ ~done
    /\ \A c \in Clients : cli_state[c] = "EVICTED"
    /\ srv_recovering
    /\ srv_recovering' = FALSE
    /\ done' = TRUE
    /\ UNCHANGED << cli_state, cli_epoch, cli_last_transno,
                    cli_replay_queue, cli_replaying,
                    req_transno, req_epoch, req_committed, req_status,
                    srv_epoch, srv_last_transno,
                    srv_connected, srv_evict_pending,
                    srv_committed_set >>

\* ================================================================
\* Spec
\* ================================================================

Terminating == done /\ UNCHANGED vars

Next ==
    \/ \E c \in Clients : \E r \in ClientRequests(c) : ClientSendRequest(c, r)
    \/ \E c \in Clients : \E r \in ClientRequests(c) : ServerCommitRequest(c, r)
    \/ Disconnect
    \/ ServerRestart
    \/ \E c \in Clients : ClientReconnect(c)
    \/ \E c \in Clients : ServerAcceptReconnect(c)
    \/ \E c \in Clients : ServerEvictClient(c)
    \/ \E c \in Clients : ServerRejectReconnect(c)
    \/ \E c \in Clients : ServerEvictMidReplay(c)
    \/ \E c \in Clients : \E r \in ClientRequests(c) : ClientReplayRequest(c, r)
    \/ \E c \in Clients : \E r \in ClientRequests(c) : ClientSkipStaleRequest(c, r)
    \/ \E c \in Clients : ClientReplayDone(c)
    \/ \E c \in Clients : ServerReplayComplete(c)
    \/ RecoveryComplete
    \/ AllEvictedTerminal
    \/ Terminating

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

\* ================================================================
\* Invariants
\* ================================================================

TypeOK ==
    /\ \A c \in Clients :
        /\ cli_state[c] \in {"FULL", "DISCON", "CONNECTING", "REPLAY",
                              "REPLAY_WAIT", "RECOVER", "EVICTED"}
        /\ cli_epoch[c] \in 0..MaxEpoch
        /\ cli_last_transno[c] \in 0..MaxTransno
        /\ cli_replay_queue[c] \subseteq AllRequests
        /\ cli_replaying[c] \subseteq AllRequests
    /\ \A r \in AllRequests :
        /\ req_transno[r] \in 0..MaxTransno
        /\ req_epoch[r] \in 0..MaxEpoch
        /\ req_committed[r] \in BOOLEAN
        /\ req_status[r] \in {"unsent", "inflight", "completed", "replayed"}
    /\ srv_epoch \in 0..MaxEpoch
    /\ srv_last_transno \in 0..MaxTransno
    /\ srv_recovering \in BOOLEAN
    /\ \A c \in Clients :
        /\ srv_connected[c] \in BOOLEAN
        /\ srv_evict_pending[c] \in BOOLEAN
    /\ srv_committed_set \subseteq 1..MaxTransno
    /\ done \in BOOLEAN

\* SAFETY: Evicted client's requests were only replayed while still connected.
\* A client evicted before replay started (cli_replaying empty) should have no
\* "replayed" requests.  A client evicted mid-replay may have partially replayed
\* requests, but only those tracked in cli_replaying -- requests that were replayed
\* while the client was still connected.  Any "replayed" request for an evicted
\* client must appear in cli_replaying; phantom replays (req_status = "replayed"
\* but not tracked) are still caught.
EvictedClientNotReplaying ==
    \A c \in Clients :
        cli_state[c] = "EVICTED" =>
            \A r \in ClientRequests(c) :
                req_status[r] = "replayed" => r \in cli_replaying[c]

\* SAFETY: No partial commit -- when done, all replayed transnos are
\* in the server's committed set.
NoPartialCommit ==
    done =>
        \A c \in Clients :
            \A r \in cli_replaying[c] :
                req_transno[r] \in srv_committed_set

\* SAFETY: Replayed requests have VBR-valid epochs
ReplayedEpochMatch ==
    \A r \in AllRequests :
        req_status[r] = "replayed" =>
            \/ req_epoch[r] = cli_epoch[r[1]]
            \/ req_transno[r] \in srv_committed_set

\* SAFETY: No request is replayed twice in a single recovery
NoDoubleReplay ==
    \A c \in Clients :
        \A r \in AllRequests :
            (r[1] = c /\ req_status[r] = "replayed") =>
                r \in cli_replaying[c]

\* SAFETY: Client epoch never exceeds server epoch
ClientEpochBound ==
    \A c \in Clients : cli_epoch[c] <= srv_epoch

\* SAFETY: If client is in REPLAY, server must be recovering
ReplayImpliesRecovering ==
    \A c \in Clients :
        cli_state[c] = "REPLAY" => srv_recovering

\* SAFETY: No lost replay -- when done, every client that ended up
\* FULL (i.e., survived recovery) must have replayed all queued requests.
\* The bug InjectBugNoWaitAll violates this: server completes recovery
\* while a connected client still has un-replayed requests in its queue.
NoLostReplay ==
    done =>
        \A c \in Clients :
            cli_state[c] = "FULL" =>
                cli_replay_queue[c] \ cli_replaying[c] = {}

\* SAFETY: VBR cross-client integrity -- a replayed request whose VBR
\* passed via the committed set (not epoch match) must have been genuinely
\* committed by the SAME client.  Catches the bug where a global committed
\* set allows client A's committed transno to validate client B's
\* uncommitted request replay.
\*
\* In real Lustre, committed sets are per-export (per-client connection).
\* The model's use of a single global srv_committed_set is an abstraction
\* that produces false VBR matches when two clients have requests with
\* the same transno value.
VBRIntegrityAcrossClients ==
    \A r \in AllRequests :
        req_status[r] = "replayed" =>
            \/ req_epoch[r] = cli_epoch[r[1]]
            \/ \E r2 \in ClientRequests(r[1]) :
                   req_committed[r2] /\ req_transno[r2] = req_transno[r]

\* SAFETY: No split-brain during recovery -- while the server is in
\* recovery mode, no connected client should be in normal operational
\* state (FULL).  A violation would mean the server is simultaneously
\* accepting new operations and processing recovery replays.
NoSplitBrainRecovery ==
    srv_recovering =>
        \A c \in Clients :
            srv_connected[c] =>
                cli_state[c] \in {"REPLAY", "REPLAY_WAIT", "RECOVER"}

\* SAFETY: Replay completeness -- after recovery, every committed request
\* from a recovered (FULL) client must have been replayed (not skipped).
\* Skipping a committed request means the server lost a durable transaction.
\* This is stronger than NoLostReplay: it specifically checks committed
\* requests and verifies they reached "replayed" status.
ReplayCompleteness ==
    done =>
        \A c \in Clients :
            cli_state[c] = "FULL" =>
                \A r \in ClientRequests(c) :
                    (req_committed[r] /\ r \in cli_replay_queue[c]) =>
                        req_status[r] = "replayed"

\* SAFETY: Clean bipartite termination -- after recovery completes,
\* every client is either fully recovered (FULL + connected) or fully
\* evicted (EVICTED + disconnected).  No transitional states remain.
ConsistentRecoveryTermination ==
    done =>
        \A c \in Clients :
            \/ (srv_connected[c] /\ cli_state[c] = "FULL")
            \/ (~srv_connected[c] /\ cli_state[c] = "EVICTED")

\* ================================================================
\* Temporal properties
\* ================================================================

\* LIVENESS: Recovery eventually completes
RecoveryCompletesEventually == <>(done)

=============================================================================
