-------------------------- MODULE recovery_model --------------------------
(*
 * TLA+ specification of the Lustre client-server recovery protocol
 * with Version-Based Recovery (VBR).
 *
 * Models the two-party recovery handshake in ptlrpc:
 *   - Client reconnect after disconnect
 *   - Server eviction timer vs client reconnect race
 *   - VBR epoch (transno) matching during replay
 *   - Request replay filtering: only committed requests are replayed,
 *     each replayed exactly once, with matching epoch
 *   - Recovery completion handshake
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
 *   - JIRA status of the cross-referenced tickets: LU-2257 closed "Cannot
 *     Reproduce", LU-6928 resolved "Duplicate", LU-10251 Open, LU-19601
 *     fixed by 892d89d37a (recovery timer extra).  None has a fix commit
 *     that this model's InjectBug* constants reproduce; the injected bugs
 *     are hypothetical variants of the modeled protocol.  The code
 *     counterpart of the Bug D fix is the exp_failed check under exp_lock
 *     in target_handle_connect (ldlm_lib.c:1657-1664) together with
 *     class_disconnect_stale_exports skipping exports whose test_export
 *     (exp_connect_healthy = exp_in_recovery) passes.
 *   - Known abstractions (not drift): the model filters replays on the
 *     client (ClientReplayRequest/ClientSkipStaleRequest); in the code
 *     the client replays every request on its replay lists
 *     (ptlrpc_replay_next) and the server rejects version-mismatched
 *     replays with -EOVERFLOW / exp_vbr_failed, later evicting such
 *     exports (exp_vbr_healthy, ldlm_lib.c:2503).  srv_committed_set
 *     stands for the per-export last_rcvd slot plus obd_last_committed,
 *     not a set of transnos.  A reconnect while the server is not in
 *     recovery is accepted by the code (obd_reconnect path,
 *     ldlm_lib.c:1533-1540) and goes to RECOVER (import.c:1358, 1376);
 *     ServerRejectReconnect only covers the case where the export is
 *     already gone.
 *
 * Design rationale -- new model vs extending import_model.tla:
 *   import_model.tla models the client-side import state machine
 *   (single-party: imp_state lifecycle with 5 concurrent threads).
 *   VBR recovery is a two-party protocol with distinct client and
 *   server state (epochs, transaction numbers, replay queues,
 *   eviction timers). A separate model avoids bloating import_model's
 *   state space and keeps each model focused on one concern.
 *
 * Abstractions for tractability:
 *   - Single client, single server (sufficient for VBR correctness).
 *   - Request pool is a small finite set (MaxRequests, default 2).
 *   - Transaction numbers are bounded naturals (0..MaxTransno).
 *   - Server epoch is a bounded natural (0..MaxEpoch).
 *   - Network modeled implicitly: disconnect event breaks connection,
 *     reconnect RPC reaches server directly (no explicit channel).
 *   - Lock replay is abstracted away (handled by import_model).
 *   - Bulk I/O is not modeled (orthogonal to recovery protocol).
 *   - Single disconnect/recovery cycle (done flag prevents loops).
 *
 * ================================================================
 * Bug injection constants and real LU-issue cross-references
 * ================================================================
 *
 * This model supports four injectable bugs controlled by boolean constants.
 * Set exactly one to TRUE per _bug.cfg run; set all FALSE for baseline and
 * _fix.cfg runs.  Each bug exercises a different invariant.
 *
 * Bug A -- InjectDoubleReplay (NoDoubleReplay invariant)
 *   Models: client fails to track requests in cli_replaying, so the same
 *   request can be replayed in a single recovery cycle without the
 *   deduplication set being updated.
 *   Real LU: No direct match found via JIRA search (2026-03-12).
 *   Conceptually related to the "version mismatch during replay" class
 *   (e.g. LU-6928, LU-2257) where incorrect request bookkeeping leads
 *   to duplicate or out-of-order replays causing server-side confusion.
 *
 * Bug B -- InjectEpochBypass (ReplayedEpochMatch invariant)
 *   Models: client skips the VBR epoch/transno check and replays every
 *   queued request unconditionally, including stale requests from a
 *   prior epoch that the server would reject.
 *   Real LU: LU-6928 -- "Version mismatch during DNE replay": client
 *   sends a replay RPC with an epoch/transno pair that no longer matches
 *   the server's committed history, causing -EOVERFLOW and eviction.
 *   Also related: LU-2257 (eviction from MDT during recovery, VBR
 *   version mismatch in client log).
 *
 * Bug C -- InjectEarlyExit (ReplayImpliesRecovering invariant)
 *   Models: server prematurely clears the recovering flag before replay
 *   is complete, leaving clients in REPLAY state with no recovery context.
 *   Real LU: LU-10251 -- "MDS hangs in recovery, recovery timer is bogus":
 *   server enters a state where it cannot exit recovery cleanly; the dual
 *   failure mode (exiting too early) is the injected variant.
 *   Also related: LU-19601 -- "replay-dual/0a doesn't abort recovery".
 *
 * Bug D -- InjectEvictionRace (NoEvictionDuringReplay invariant)
 *   Models: two sub-bugs working together: (1) ServerAcceptReconnect
 *   fails to atomically cancel the eviction timer when accepting a client,
 *   and (2) ServerEvictClient fires even when the client is connected.
 *   The result is a client that progresses to REPLAY state while the
 *   eviction timer is still armed.
 *   Real LU: LU-2257 -- "eviction from MDT during recovery": client is
 *   evicted while it is actively recovering/replaying; server log shows
 *   "1 was evicted" despite client having established a connection.
 *
 * ================================================================
 * What this model structurally cannot catch
 * ================================================================
 *
 * (a) Multi-client races: With N clients each in {DISCON, CONNECTING,
 *     REPLAY, REPLAY_WAIT, RECOVER, EVICTED}, the state space grows as
 *     O(6^N * MaxEpoch^N * MaxTransno^(N*MaxRequests)).  For N=2 this
 *     is already ~50x the single-client baseline, pushing TLC into
 *     minutes; N=3 is likely impractical without symmetry reduction.
 *     Bugs requiring two clients to race in REPLAY (e.g. the two-client
 *     VBR interleaving in LU-2257) cannot be expressed here.
 *
 * (b) Multiple recovery cycles: The `done` flag is a one-shot terminator.
 *     Bugs that appear only after a second disconnect within a single
 *     session (e.g., reconnect -> partial replay -> re-disconnect) require
 *     extending the model with a cycle counter and resettable state.
 *     State space impact: O(MaxCycles * current_states).
 *
 * (c) Network reordering / duplicate delivery: The model uses implicit
 *     atomic messaging.  Out-of-order RPC arrival or duplicate delivery
 *     (as can happen with Lustre's LNET retransmission) requires an
 *     explicit network buffer with per-message ordering, roughly doubling
 *     the state variables and multiplying the state space by O(MaxRequests!).
 *
 * (d) Lock replay: Abstracted away; lock replay races are covered by
 *     import_model.tla and ldlm_recovery_reprocess.tla.
 *)

EXTENDS Integers, FiniteSets, TLC

CONSTANTS
    MaxRequests,    \* Number of requests in the pool (e.g., 2)
    MaxTransno,     \* Upper bound on transaction numbers (e.g., 3)
    MaxEpoch,       \* Upper bound on server epochs (e.g., 2)
    InjectDoubleReplay,   \* Bug A: disable cli_replaying deduplication tracking
    InjectEpochBypass,    \* Bug B: skip VBR epoch/transno check in replay
    InjectEarlyExit,      \* Bug C: allow srv_recovering=FALSE before replay done
    InjectEvictionRace    \* Bug D: eviction timer not cancelled on reconnect

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

    \* --- Protocol flag ---
    done                \* TRUE when protocol has completed (for termination)

vars == << cli_state, cli_epoch, cli_last_transno, cli_replay_queue,
           cli_replaying, req_transno, req_epoch, req_committed,
           req_status, srv_epoch, srv_last_transno, srv_recovering,
           srv_connected, srv_evict_pending, srv_replay_complete,
           srv_committed_set, done >>

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
                    srv_replay_complete, srv_committed_set, done >>

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
                    srv_replay_complete, done >>

\* ================================================================
\* Disconnect and server restart
\* ================================================================

\* Connection is lost (client detects disconnect)
Disconnect ==
    /\ ~done
    /\ cli_state = "FULL"
    /\ srv_connected
    /\ cli_state' = "DISCON"
    /\ srv_connected' = FALSE
    /\ srv_evict_pending' = TRUE   \* Server starts eviction timer
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

\* Server restarts (enters recovery mode, bumps epoch)
ServerRestart ==
    /\ ~done
    /\ ~srv_connected           \* client is disconnected
    /\ ~srv_recovering          \* not already recovering
    /\ srv_epoch < MaxEpoch
    /\ srv_epoch' = srv_epoch + 1
    /\ srv_recovering' = TRUE
    /\ srv_replay_complete' = FALSE
    /\ srv_evict_pending' = TRUE
    \* Server retains its committed set (persistent storage)
    /\ UNCHANGED << cli_state, cli_epoch, cli_last_transno,
                    cli_replay_queue, cli_replaying,
                    req_transno, req_epoch, req_committed, req_status,
                    srv_last_transno, srv_connected,
                    srv_committed_set, done >>

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
                    srv_committed_set, done >>

\* Server accepts reconnect -- client enters REPLAY
\* Server must be recovering and not yet evicted the client.
\*
\* Bug D (InjectEvictionRace): in the correct implementation, ServerAcceptReconnect
\* atomically cancels the eviction timer (srv_evict_pending=FALSE) when accepting
\* the client.  The bug models a race where the cancel is not performed atomically,
\* leaving the timer armed even as the client enters REPLAY state.
ServerAcceptReconnect ==
    /\ ~done
    /\ cli_state = "CONNECTING"
    /\ srv_recovering
    /\ srv_evict_pending       \* client hasn't been evicted yet
    \* Server cancels eviction and accepts client.
    \* Bug D: when InjectEvictionRace=TRUE, the eviction timer is NOT cancelled,
    \* leaving srv_evict_pending=TRUE while the client enters REPLAY.
    /\ srv_evict_pending' = IF InjectEvictionRace THEN TRUE ELSE FALSE
    /\ srv_connected' = TRUE
    \* Client gets server's new epoch, enters REPLAY
    /\ cli_state' = "REPLAY"
    /\ cli_epoch' = srv_epoch
    /\ cli_replaying' = {}     \* Clear replayed set for this recovery
    /\ UNCHANGED << cli_last_transno, cli_replay_queue,
                    req_transno, req_epoch, req_committed, req_status,
                    srv_epoch, srv_last_transno, srv_recovering,
                    srv_replay_complete, srv_committed_set, done >>

\* Server evicts the client (eviction timer fires before reconnect)
\*
\* Bug D (InjectEvictionRace): in the correct implementation, ServerEvictClient
\* requires ~srv_connected (client has not yet reconnected).  The bug removes this
\* guard, allowing eviction to fire even after the client has reconnected and is in
\* REPLAY state.  Combined with InjectEvictionRace in ServerAcceptReconnect (timer
\* not cancelled), this creates the race: client in REPLAY, timer still armed,
\* server fires eviction.
ServerEvictClient ==
    /\ ~done
    /\ srv_evict_pending
    /\ srv_recovering
    /\ (~InjectEvictionRace => ~srv_connected)  \* Bug D: remove ~srv_connected guard
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
                    srv_committed_set, done >>

\* Server rejects reconnect: not recovering or client already evicted.
\* Client is evicted (terminal -- no retry in this single-cycle model).
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
                    srv_committed_set, done >>

\* ================================================================
\* VBR replay: client replays committed requests with epoch matching
\* ================================================================

\* Client replays a request from the replay queue.
\* VBR filtering: only replay if request epoch matches current
\* server epoch OR server committed the transno (version match).
\*
\* Bug A (InjectDoubleReplay): models a client that fails to update
\* cli_replaying after sending a replay RPC.  The tracking set is never
\* updated, so the deduplication guard (r \notin cli_replaying) passes on
\* every call, and req_status is set to "replayed" without cli_replaying
\* being updated.  NoDoubleReplay fires because req_status="replayed" but
\* r \notin cli_replaying.
\*
\* Bug B (InjectEpochBypass): models a client that sends every queued
\* request unconditionally, skipping the VBR epoch/transno validation.
\* ReplayedEpochMatch fires when a stale-epoch request (not in
\* srv_committed_set) is replayed.
ClientReplayRequest(r) ==
    /\ ~done
    /\ cli_state = "REPLAY"
    /\ srv_connected
    /\ srv_recovering
    /\ r \in cli_replay_queue
    /\ r \notin cli_replaying     \* deduplication guard (always present)
    \* VBR epoch check: request must have been from a prior epoch
    \* that the server recognizes, or the transno must be in the
    \* server's committed set (version-based validation).
    \* Bug B: bypass this check entirely (replay all queued requests).
    /\ (InjectEpochBypass \/
        \/ req_epoch[r] = cli_epoch            \* same epoch
        \/ req_transno[r] \in srv_committed_set) \* VBR: transno was committed
    \* Mark as replayed.
    \* Bug A: don't update cli_replaying (client fails to track the replay),
    \* leaving req_status="replayed" while r \notin cli_replaying.
    /\ cli_replaying' = IF InjectDoubleReplay
                        THEN cli_replaying          \* Bug A: omit tracking update
                        ELSE cli_replaying \union {r}
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
                    srv_replay_complete, done >>

\* Client skips a request whose epoch doesn't match and transno
\* is not in the committed set (VBR filtering: stale request).
ClientSkipStaleRequest(r) ==
    /\ ~done
    /\ cli_state = "REPLAY"
    /\ r \in cli_replay_queue
    /\ r \notin cli_replaying
    \* VBR: epoch mismatch AND transno not committed -- skip
    /\ req_epoch[r] /= cli_epoch
    /\ req_transno[r] \notin srv_committed_set
    \* Remove from queue, don't replay
    /\ cli_replay_queue' = cli_replay_queue \ {r}
    /\ UNCHANGED << cli_state, cli_epoch, cli_last_transno, cli_replaying,
                    req_transno, req_epoch, req_committed, req_status,
                    srv_epoch, srv_last_transno, srv_recovering,
                    srv_connected, srv_evict_pending, srv_replay_complete,
                    srv_committed_set, done >>

\* ================================================================
\* Recovery completion
\* ================================================================

\* Client finishes replay: all queued requests have been replayed
\* or skipped. Client moves to REPLAY_WAIT.
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
                    srv_committed_set, done >>

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
                    srv_committed_set, done >>

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
                    srv_committed_set >>

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
                    srv_committed_set >>

\* ================================================================
\* Bug C: server exits recovery prematurely (before replay complete)
\* ================================================================

\* Bug C (InjectEarlyExit): models a server that clears the recovering flag
\* before srv_replay_complete is set.  In the correct implementation, only
\* RecoveryComplete or ServerEvictClient can set srv_recovering=FALSE, and
\* both require srv_replay_complete=TRUE first.  This action injects a path
\* where srv_recovering goes FALSE while clients may still be in REPLAY.
\* ReplayImpliesRecovering (cli_state="REPLAY" => srv_recovering) fires
\* in the next state where cli_state="REPLAY" and srv_recovering=FALSE.
\* Real LU: LU-10251 -- MDS hangs in recovery (timer bogus); early-exit
\* is the symmetric failure mode.
ServerExitRecoveryEarly ==
    /\ InjectEarlyExit
    /\ ~done
    /\ srv_recovering
    /\ ~srv_replay_complete        \* Bug: exit before replay is done
    /\ srv_recovering' = FALSE
    /\ UNCHANGED << cli_state, cli_epoch, cli_last_transno,
                    cli_replay_queue, cli_replaying,
                    req_transno, req_epoch, req_committed, req_status,
                    srv_epoch, srv_last_transno, srv_connected,
                    srv_evict_pending, srv_replay_complete,
                    srv_committed_set, done >>

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
    \/ ServerExitRecoveryEarly
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
    /\ done \in BOOLEAN

\* SAFETY: Replayed requests must have matching epoch or VBR match.
\* A request that has been replayed must either share the current
\* epoch OR have been committed by the server before the disconnect
\* (req_committed[r]=TRUE).  We use req_committed rather than
\* srv_committed_set because ClientReplayRequest adds to srv_committed_set
\* as part of the replay action itself; checking srv_committed_set in the
\* post-state would always pass, defeating the invariant.
\* req_committed[r] is set by ServerCommitRequest during normal operation
\* and never changed, so it correctly reflects the pre-disconnect state.
ReplayedEpochMatch ==
    \A r \in Requests :
        req_status[r] = "replayed" =>
            \/ req_epoch[r] = cli_epoch
            \/ req_committed[r]     \* was committed before disconnect (VBR match)

\* SAFETY: No request is replayed without being tracked in cli_replaying.
\* The cli_replaying set is the authoritative deduplication record; once a
\* request is replayed, it must appear in cli_replaying.  If the tracking
\* update is skipped (Bug A), req_status="replayed" without cli_replaying
\* being updated, violating this invariant.
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

\* SAFETY: When the client is in REPLAY state, the eviction timer must
\* not be active.  The timer is armed on disconnect and should be
\* atomically cancelled when the server accepts the reconnect.
\* Bug D (InjectEvictionRace) injects a path where ServerAcceptReconnect
\* does not cancel the timer, leaving srv_evict_pending=TRUE while
\* cli_state="REPLAY".  Related: LU-2257 -- client evicted during recovery.
NoEvictionDuringReplay ==
    cli_state = "REPLAY" => ~srv_evict_pending

\* ================================================================
\* Temporal properties
\* ================================================================

\* Recovery eventually completes (either FULL or EVICTED)
EventuallyDone == <>(done)

=============================================================================
