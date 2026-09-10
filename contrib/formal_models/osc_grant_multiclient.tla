--------------------- MODULE osc_grant_multiclient ---------------------
(*
 * Multi-client grant competition model for the OSC grant subsystem.
 *
 * Extends the single-client grant models (osc_grant_model.tla,
 * osc_grant_eviction_race.tla) to two clients competing for a bounded
 * server-side grant pool.  Models the grant shrink protocol race where
 * the server can over-allocate grants during the shrink-acknowledgment
 * window.
 *
 * Architecture:
 *   Server: holds server_total_grant (bounded)
 *   Client1, Client2: each holds cl_import_grant (bounded)
 *
 * Protocol:
 *   1. Server grants to clients on connect (splits server_total_grant)
 *   2. Server sends SHRINK to one or both clients when total exceeds limit
 *   3. Clients acknowledge shrink by reducing cl_import_grant
 *   4. On eviction: server reclaims the evicted client's grant
 *   5. After eviction: client can reconnect and receive new grants
 *
 * Bug injections:
 *
 *   InjectBugShrinkRace:
 *     Server sends shrink to Client1, but before Client1 acks, Client2
 *     connects and receives a new grant that assumes the shrink already
 *     took effect.  This causes sum(cl_import_grant) > server_total_grant.
 *
 *   InjectBugEvictShrinkDoubleCount:
 *     On eviction, server subtracts BOTH the client's grant AND the pending
 *     shrink amount from srv_granted, double-counting the return.  With
 *     reconnect enabled, the resulting negative srv_granted inflates the
 *     "remaining" pool, allowing over-allocation that violates
 *     GrantSafetyInvariant.
 *
 *   InjectBugEvictNoReclaim:
 *     On eviction, server marks client disconnected but forgets to reduce
 *     srv_granted.  The server's tracking diverges from reality, causing
 *     grant pool starvation (server thinks pool is full when it isn't).
 *     Violates ServerTrackingConsistent.
 *
 * Key invariant:
 *   sum of cl_import_grant across all clients <= server_total_grant
 *   AT ALL TIMES (not just at quiescent points -- checked during the
 *   shrink acknowledgment window too).
 *
 * Uses Symmetry = Permutations(Clients) in cfg to reduce state space.
 *
 * === Real-code verification (2026-03-12, lustre-design-docs-ljx) ===
 *
 * Verified against lustre-release master (target/tgt_grant.c,
 * osc/osc_request.c).
 *
 * The InjectBugShrinkRace = TRUE path does NOT exist in real Lustre code
 * due to a fundamental architecture difference between the model and the
 * implementation.
 *
 * MODEL vs. REAL CODE:
 *
 * The model assumes a SERVER-INITIATED shrink protocol:
 *   1. Server sends "please shrink by X" to Client1  (ServerShrink action)
 *   2. srv_pending_shrink[c] tracks how much the server is waiting for
 *   3. Client1 acks and reduces its grant  (ClientShrinkAck action)
 *   4. BUG: when Client2 connects in the window between steps 1 and 3,
 *      server optimistically calculates:
 *        remaining = SERVER_TOTAL - srv_granted + TotalPendingShrink
 *      treating the pending-but-unacknowledged shrink as already returned.
 *
 * Real Lustre uses CLIENT-INITIATED shrink exclusively:
 *   1. Client voluntarily decides to shrink (osc_should_shrink_grant()).
 *   2. Client atomically reduces cl_avail_grant locally
 *      (osc_shrink_grant_local(), under cl_loi_list_lock, osc_request.c:797).
 *   3. Client sends RPC to server with OBD_FL_SHRINK_GRANT flag,
 *      carrying oa->o_grant = amount returned.
 *   4. Server calls tgt_grant_shrink() (tgt_grant.c:581) which IMMEDIATELY
 *      reduces tgd_tot_granted and ted_grant by the shrink amount.
 *
 * Consequence: there is NO "pending shrink window" on the server side:
 *   - The server never sends a shrink request to a client.
 *   - The server has no srv_pending_shrink counter.
 *   - tgt_grant_space_left() (tgt_grant.c:416) computes:
 *       left = filesystem_free - (tgd_tot_granted + reserved)
 *     using tgd_tot_granted directly, with no pending-shrink discount.
 *   - tgd_tot_granted is only reduced when the server ACTUALLY processes
 *     a shrink RPC, never preemptively.
 *
 * When Client2 connects while Client1's shrink is in-flight (i.e., Client1
 * has already reduced cl_avail_grant locally but the server hasn't yet
 * received the RPC):
 *   - The server still sees the pre-shrink tgd_tot_granted (conservative).
 *   - Client2 receives LESS grant (not more) because the server hasn't yet
 *     credited the shrink.
 *   - sum(client grants) can transiently be slightly BELOW server total, but
 *     never above it.  This is safe.
 *
 * Lock coverage: tgt_grant_connect() and tgt_grant_space_left() both hold
 * tgd_grant_lock (spinlock) across the entire space calculation and allocation.
 * No drop-and-reacquire pattern exists.  The lock prevents any interleaved
 * update to tgd_tot_granted from other clients' RPCs during the connect path.
 *
 * No JIRA filed for InjectBugShrinkRace.  Race is architecturally impossible
 * in real code because the server-initiated shrink protocol modeled here
 * does not exist.
 *
 * The eviction accounting bugs (InjectBugEvictShrinkDoubleCount,
 * InjectBugEvictNoReclaim) model plausible coding errors in
 * tgt_grant_discard() / obd_export_evict():
 *   - Double-count: reducing ted_grant by both the export's grant and the
 *     pending shrink (which is already included in the grant).
 *   - No-reclaim: failing to call tgt_grant_discard() during eviction,
 *     leaving stale tgd_tot_granted.
 *
 * Model retained as an exploration of what WOULD break if Lustre ever
 * introduced a server-initiated "please shrink by X" mechanism without
 * a corresponding conservative pending-shrink accounting scheme.
 *
 * Source (lustre-release master 47638add78):
 *   lustre/osc/osc_request.c
 *     osc_should_shrink_grant()    881-911    client decides to shrink
 *     osc_shrink_grant_local()     797-809    cl_avail_grant -= o_grant
 *                                             under cl_loi_list_lock,
 *                                             799-802; OBD_FL_SHRINK_GRANT
 *     osc_shrink_grant_to_target() 829-879    same, via OST_SET_INFO
 *                                             KEY_GRANT_SHRINK (872)
 *     osc_shrink_grant_interpret() 774-795    declined shrink credited
 *                                             back via osc_update_grant
 *     osc_import_event()           3896-3970  IMP_EVENT_DISCON 3907-3913
 *                                             (client side of ServerEvict)
 *   lustre/target/tgt_grant.c
 *     tgt_grant_space_left()       416-467    left = free - (tot_granted
 *                                             + reserved), 456
 *     tgt_grant_shrink()           581-615    ted_grant/tgd_tot_granted -=
 *                                             o_grant at 606-607, o_grant
 *                                             = 0 at 614 (ClientShrinkAck
 *                                             server half)
 *     tgt_grant_alloc()            884-977    tgd_tot_granted/ted_grant +=
 *                                             grant at 954-955
 *                                             (ServerConnect amount)
 *     tgt_grant_connect()          1024-1091  tgd_grant_lock 1054-1084,
 *                                             tgt_grant_alloc at 1068
 *     tgt_grant_discard()          1104-1153  tgd_tot_granted -= ted_grant
 *                                             1139 (clamp/recalc 1116-1137,
 *                                             LU-14543); ted_grant = 0 at
 *                                             1142 (ServerEvict)
 *   lustre/ofd/ofd_obd.c
 *     ofd_obd_disconnect()         422        -> tgt_grant_discard
 *     ofd_destroy_export()         510        -> tgt_grant_discard
 *   lustre/ofd/ofd_dev.c
 *     ofd_set_info_hdl()           809-881    KEY_GRANT_SHRINK handler
 *
 * Validated against: lustre-release master 47638add78 (2026-09-06)
 * Validation notes: line refs above refreshed (tgt_grant_shrink 578->581,
 *   tgt_grant_space_left 415->416; osc_shrink_grant_local still 797).
 *   The "no drop-and-reacquire" statement is accurate for the space
 *   calculation: tgt_grant_connect() does drop tgd_grant_lock at
 *   1062-1066 when cached statfs is stale, but only to re-run statfs;
 *   it then re-takes the lock and recomputes left before allocating.
 *   No model change.
 *)

EXTENDS Integers, FiniteSets, TLC

CONSTANTS
    Clients,                         \* Symmetry set: {Client1, Client2, ...}
    SERVER_TOTAL,                    \* Total grant pool on server (e.g. 6)
    MAX_CLIENT_GRANT,                \* Max per-client grant (e.g. 4)
    InjectBugShrinkRace,             \* TRUE = bug: server grants assuming pending shrink took effect
    InjectBugEvictShrinkDoubleCount, \* TRUE = bug: eviction double-counts pending shrink
    InjectBugEvictNoReclaim          \* TRUE = bug: eviction forgets to reclaim grant

ASSUME SERVER_TOTAL > 0
ASSUME MAX_CLIENT_GRANT > 0
ASSUME SERVER_TOTAL >= MAX_CLIENT_GRANT

VARIABLES
    cl_grant,            \* [Clients -> Nat] cl_import_grant per client
    cl_connected,        \* [Clients -> BOOLEAN] connection state
    cl_evicted,          \* [Clients -> BOOLEAN] eviction state
    srv_granted,         \* server's view of total grants outstanding
    srv_pending_shrink,  \* [Clients -> Nat] shrink server expects from each client
    shrink_msg,          \* [Clients -> Nat] in-flight shrink message to client
    srv_lock             \* "free" or holder id (mutex)

vars == << cl_grant, cl_connected, cl_evicted, srv_granted,
           srv_pending_shrink, shrink_msg, srv_lock >>

\* === Helper: sum of client grants ===
\* Recursive sum over a set (TLC-friendly via SUBSET)
SetSum(f, S) == LET PartialSum[T \in SUBSET S] ==
                    IF T = {} THEN 0
                    ELSE LET x == CHOOSE x \in T : TRUE
                         IN f[x] + PartialSum[T \ {x}]
                IN PartialSum[S]

TotalClientGrant == SetSum(cl_grant, Clients)
TotalPendingShrink == SetSum(shrink_msg, Clients)

\* === Symmetry for model checking ===
Symmetry == Permutations(Clients)

\* === Invariants ===

\* PRIMARY: sum of client grants never exceeds server total
GrantSafetyInvariant == TotalClientGrant <= SERVER_TOTAL

\* Per-client grants are non-negative
GrantsNonNegative == \A c \in Clients : cl_grant[c] >= 0

\* Per-client grants are bounded
GrantsBounded == \A c \in Clients : cl_grant[c] <= MAX_CLIENT_GRANT

\* Shrink messages are non-negative
ShrinkNonNegative == \A c \in Clients : shrink_msg[c] >= 0

\* Pending shrinks are non-negative
PendingShrinkNonNegative == \A c \in Clients : srv_pending_shrink[c] >= 0

\* Server granted tracking is bounded
ServerGrantedBounded == srv_granted <= SERVER_TOTAL

\* Server granted is non-negative
ServerGrantedNonNeg == srv_granted >= 0

\* ---------------------------------------------------------------
\* NEW INVARIANTS (lustre-design-docs-at9.11)
\* ---------------------------------------------------------------

\* Server tracking matches actual client grants (accounting consistency).
\* If this diverges, the server either over-allocates (safety) or
\* under-allocates (liveness / pool starvation).
ServerTrackingConsistent == srv_granted = TotalClientGrant

\* Evicted clients have clean state: no grant, no pending shrink,
\* no in-flight shrink message.
EvictedClientClean == \A c \in Clients :
    cl_evicted[c] => /\ cl_grant[c] = 0
                     /\ shrink_msg[c] = 0
                     /\ srv_pending_shrink[c] = 0

\* Connected and evicted are mutually exclusive.
ConnectedNotEvicted == \A c \in Clients :
    ~(cl_connected[c] /\ cl_evicted[c])

\* Only connected clients hold grants.
DisconnectedNoGrant == \A c \in Clients :
    ~cl_connected[c] => cl_grant[c] = 0

\* Server grant pool never goes negative (remaining capacity >= 0).
\* Equivalent to ServerGrantedBounded + ServerGrantedNonNeg but
\* expressed as the pool perspective.
GrantPoolNonNegative == SERVER_TOTAL - srv_granted >= 0

\* Shrink notification to one client doesn't corrupt another's accounting:
\* for any two distinct clients, the sum of their grants still respects the
\* server pool, even when one has a pending shrink.
CrossClientShrinkSafety == \A c1, c2 \in Clients :
    c1 /= c2 =>
        cl_grant[c1] + cl_grant[c2] <= SERVER_TOTAL

\* === Initial state ===
Init == /\ cl_grant = [c \in Clients |-> 0]
        /\ cl_connected = [c \in Clients |-> FALSE]
        /\ cl_evicted = [c \in Clients |-> FALSE]
        /\ srv_granted = 0
        /\ srv_pending_shrink = [c \in Clients |-> 0]
        /\ shrink_msg = [c \in Clients |-> 0]
        /\ srv_lock = "free"

\* === Actions ===

\* ---------------------------------------------------------------
\* ServerConnect(c): Connect client c and grant it resources.
\*
\* When a client connects, the server allocates a portion of the
\* remaining grant pool.  Amount = min(remaining, MAX_CLIENT_GRANT).
\*
\* BUG MODE (InjectBugShrinkRace):
\*   Server calculates "remaining" by subtracting pending shrinks
\*   from srv_granted, assuming they will be acked.  This creates
\*   over-allocation if a shrink hasn't been acked yet.
\*
\* FIXED MODE:
\*   Server uses srv_granted as-is (conservative: only counts
\*   grants already acknowledged as returned).
\* ---------------------------------------------------------------
ServerConnect(c) ==
    /\ srv_lock = "free"
    /\ ~cl_connected[c]
    /\ ~cl_evicted[c]
    /\ LET remaining == IF InjectBugShrinkRace
                        THEN SERVER_TOTAL - srv_granted + TotalPendingShrink
                        ELSE SERVER_TOTAL - srv_granted
           amount == IF remaining > MAX_CLIENT_GRANT THEN MAX_CLIENT_GRANT
                     ELSE IF remaining > 0 THEN remaining
                     ELSE 0
       IN /\ amount > 0
          /\ cl_grant' = [cl_grant EXCEPT ![c] = amount]
          /\ cl_connected' = [cl_connected EXCEPT ![c] = TRUE]
          /\ srv_granted' = srv_granted + amount
          /\ UNCHANGED << cl_evicted, srv_pending_shrink, shrink_msg, srv_lock >>

\* ---------------------------------------------------------------
\* ServerShrink(c): Send shrink request to connected client c.
\*
\* Server picks a connected client that has grant > 1 and asks
\* it to return 1 unit.  Shrink is sent as an in-flight message.
\* ---------------------------------------------------------------
ServerShrink(c) ==
    /\ srv_lock = "free"
    /\ cl_connected[c]
    /\ cl_grant[c] > 1
    /\ shrink_msg[c] = 0
    /\ shrink_msg' = [shrink_msg EXCEPT ![c] = 1]
    /\ srv_pending_shrink' = [srv_pending_shrink EXCEPT ![c] = 1]
    /\ UNCHANGED << cl_grant, cl_connected, cl_evicted, srv_granted, srv_lock >>

\* ---------------------------------------------------------------
\* ClientShrinkAck(c): Client c acknowledges a pending shrink.
\*
\* Client reduces its grant by the shrink amount and notifies
\* the server.
\* ---------------------------------------------------------------
ClientShrinkAck(c) ==
    /\ srv_lock = "free"
    /\ shrink_msg[c] > 0
    /\ LET shrink_amt == shrink_msg[c]
           actual_shrink == IF cl_grant[c] >= shrink_amt THEN shrink_amt
                           ELSE cl_grant[c]
       IN /\ cl_grant' = [cl_grant EXCEPT ![c] = cl_grant[c] - actual_shrink]
          /\ srv_granted' = srv_granted - actual_shrink
          /\ srv_pending_shrink' = [srv_pending_shrink EXCEPT ![c] = 0]
          /\ shrink_msg' = [shrink_msg EXCEPT ![c] = 0]
    /\ UNCHANGED << cl_connected, cl_evicted, srv_lock >>

\* ---------------------------------------------------------------
\* ServerEvict(c): Evict connected client c, reclaim its grants.
\*
\* Models osc_import_event IMP_EVENT_DISCON.  Server reclaims the
\* client's grant and cancels any pending shrink.
\*
\* BUG MODE (InjectBugEvictShrinkDoubleCount):
\*   Server subtracts both cl_grant[c] AND srv_pending_shrink[c]
\*   from srv_granted.  The pending shrink is already accounted for
\*   within the grant (the client hasn't reduced yet), so this
\*   double-counts the return, driving srv_granted negative.
\*   On reconnect, the inflated "remaining" pool causes over-allocation.
\*
\* BUG MODE (InjectBugEvictNoReclaim):
\*   Server marks client disconnected but forgets to reduce
\*   srv_granted.  Tracking diverges from reality.
\*
\* FIXED MODE:
\*   Server subtracts exactly cl_grant[c] from srv_granted.
\* ---------------------------------------------------------------
ServerEvict(c) ==
    /\ srv_lock = "free"
    /\ cl_connected[c]
    /\ LET grant_reclaim == IF InjectBugEvictNoReclaim THEN 0 ELSE cl_grant[c]
           shrink_extra == IF InjectBugEvictShrinkDoubleCount
                          THEN srv_pending_shrink[c]
                          ELSE 0
       IN srv_granted' = srv_granted - grant_reclaim - shrink_extra
    /\ cl_grant' = [cl_grant EXCEPT ![c] = 0]
    /\ cl_connected' = [cl_connected EXCEPT ![c] = FALSE]
    /\ cl_evicted' = [cl_evicted EXCEPT ![c] = TRUE]
    /\ srv_pending_shrink' = [srv_pending_shrink EXCEPT ![c] = 0]
    /\ shrink_msg' = [shrink_msg EXCEPT ![c] = 0]
    /\ UNCHANGED srv_lock

\* ---------------------------------------------------------------
\* ClientReconnect(c): Evicted client clears eviction flag.
\*
\* After eviction, a client can reconnect by clearing its eviction
\* state.  This allows ServerConnect to run again for this client.
\* Models the real Lustre reconnection path where a previously
\* evicted export re-establishes connection.
\* ---------------------------------------------------------------
ClientReconnect(c) ==
    /\ cl_evicted[c]
    /\ ~cl_connected[c]
    /\ cl_evicted' = [cl_evicted EXCEPT ![c] = FALSE]
    /\ UNCHANGED << cl_grant, cl_connected, srv_granted,
                    srv_pending_shrink, shrink_msg, srv_lock >>

\* === Next-state relation ===
Next == \/ \E c \in Clients : ServerConnect(c)
        \/ \E c \in Clients : ServerShrink(c)
        \/ \E c \in Clients : ClientShrinkAck(c)
        \/ \E c \in Clients : ServerEvict(c)
        \/ \E c \in Clients : ClientReconnect(c)

\* === Specification ===
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

====
