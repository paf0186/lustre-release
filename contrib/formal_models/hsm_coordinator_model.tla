----------------------- MODULE hsm_coordinator_model -------------------------
(*
 * TLA+ specification of the Lustre HSM coordinator request state machine.
 *
 * Models the HSM request lifecycle in:
 *   lustre/mdt/mdt_hsm_cdt_actions.c    (agent llog records)
 *   lustre/mdt/mdt_hsm_cdt_agent.c      (agent dispatch / registration)
 *   lustre/mdt/mdt_coordinator.c        (coordinator main loop, state
 *                                        transitions, recovery, cancel)
 *
 * Request lifecycle (enum agent_req_status, lustre_idl.h:3112-3118;
 * the model's DONE is ARS_SUCCEED):
 *   WAITING -> STARTED -> DONE
 *                      -> FAILED
 *          -> CANCELED
 *
 * Validated against: lustre-release master 47638add78 (2026-09-06)
 *
 * Source (file:line ranges in that tree):
 *   - mdt_hsm_add_actions()       mdt_hsm_cdt_client.c:397-430 ->
 *     mdt_hsm_register_hal() 245-383 -> mdt_agent_record_add()
 *     mdt_hsm_cdt_actions.c:165-227 (new record is ARS_WAITING, 183)
 *   - mdt_coordinator()           mdt_coordinator.c:653-858 (main loop)
 *       -> cdt_llog_process() with mdt_coordinator_cb() 429-470
 *       -> mdt_cdt_waiting_cb() 165-322 (collect WAITING)
 *       -> mdt_cdt_started_cb() 324-413 (STARTED past
 *          cdt_active_req_timeout -> ARS_CANCELED, 396-398)
 *   - mdt_hsm_agent_send()        mdt_hsm_cdt_agent.c:427-633
 *       (WAITING -> STARTED on successful send, 614-615)
 *   - mdt_hsm_update_request_state() mdt_coordinator.c:1815-1940
 *       -> hsm_cdt_request_completed() 1586-1804
 *          (STARTED -> SUCCEED / FAILED / WAITING for retry)
 *   - Cancel: mdt_hsm_add_hsr() 1420-1504 (HSMA_CANCEL marks the target
 *     record ARS_CANCELED), hsm_cancel_all_actions() 1998-2103 with
 *     mdt_cancel_all_cb() 1954-1996 (WAITING or STARTED -> CANCELED)
 *   - Coordinator (re)start: mdt_hsm_cdt_start() 1284-1342 ->
 *     mdt_coordinator() -> cdt_start_pending_restore() 618-643 ->
 *     mdt_hsm_pending_restore() 1048-1068 -> hsm_restore_cb() 986-1035
 *     (STARTED -> WAITING for HSMA_RESTORE only, 1019-1024)
 *   - mdt_hsm_cdt_cleanup()       mdt_coordinator.c:513-543 (in-memory
 *     request list dropped when the coordinator stops)
 *
 * Validation notes (2026-09-10):
 *   LU-19579 is still Open (no fix in this tree).  hsm_restore_cb()
 *   re-queues STARTED records only for HSMA_RESTORE; STARTED archive and
 *   remove records are neither re-queued nor re-registered in the in-memory
 *   request list, so agent progress for them fails and they stay STARTED
 *   until cdt_active_req_timeout cancels them (mdt_cdt_started_cb).  Hence
 *   InjectLU19579=TRUE describes the tree for archive/remove and
 *   InjectLU19579=FALSE describes what the tree already does for restore.
 *   LU-19829 was resolved by 78c41cd38b ("hsm: set dirty flag on archive
 *   failure", mdt_coordinator.c:1659-1666), which mitigates the data loss
 *   but does NOT restore the dispatch-time dedup: hsm_find_compatible()
 *   (mdt_hsm_cdt_client.c:90-121) still scans the llog only for HSMA_CANCEL
 *   without a cookie (LU-13651).  The tree therefore corresponds to
 *   InjectLU19829=TRUE for the dedup guard; InjectLU19829=FALSE models the
 *   pre-LU-13651 behaviour, and AtMostOneStartedPerFID is not an invariant
 *   of the current code.  The code also cancels STARTED requests (via the
 *   agent, hsm_cancel_all_actions) and times them out; both are outside
 *   this model's scope as stated below.
 *
 * Actors:
 *   Coordinator thread: scans WAITING queue, dispatches to agent (WAITING->STARTED)
 *   Agent process:      receives STARTED, reports DONE or FAILED
 *   Cancel thread:      transitions WAITING -> CANCELED
 *   Recovery thread:    runs after MDT failover; re-queues or abandons STARTED
 *
 * ================================================================
 * Bug injection constants and LU cross-references
 * ================================================================
 *
 * InjectLU19579 -- NoStartedAfterRecovery invariant
 *   Real bug: LU-19579 -- "HSM recovery does not work for STARTED actions".
 *   After MDT failover the coordinator start-up scan (hsm_restore_cb in
 *   mdt_coordinator.c) re-queues only STARTED restore actions; STARTED
 *   archive/remove actions are left as they are.  Because agents lose their
 *   MDT connection on failover they cannot deliver completions.  The
 *   coordinator never re-queues the STARTED actions; they hang indefinitely
 *   (or until a per-action timeout fires and the operator notices).
 *   Model: FailoverOccur clears req_agent for all STARTED requests (modeling
 *   agent connection loss); RecoverActions then skips those STARTED requests
 *   (InjectLU19579=TRUE), leaving req_state=STARTED/req_agent="none" with no
 *   action able to advance them.
 *   Invariant violated: NoStartedAfterRecovery
 *
 * InjectLU19829 -- AtMostOneStartedPerFID invariant
 *   Real bug: LU-19829 -- "Files lost due to the removal of request
 *   deduplication in HSM" (dedup dropped by LU-13651).
 *   Lustre 2.14 deduplicated concurrent archive requests for the same FID
 *   (coalescing them into one STARTED action).  The dedup code was dropped
 *   in the 2.15 merge window, allowing the coordinator to dispatch two
 *   separate STARTED archive actions for the same file.  If two agents
 *   independently write archive data, the second write overwrites the first,
 *   causing silent data loss.
 *   Model: CdtDispatch omits the "no STARTED for same FID" guard when
 *   InjectLU19829=TRUE, allowing two requests with the same FID to both
 *   reach STARTED simultaneously.
 *   Invariant violated: AtMostOneStartedPerFID
 *
 * ================================================================
 * Abstractions for tractability
 * ================================================================
 *
 *  - Single agent ("agent1"): sufficient to exercise all dispatch/cancel/
 *    recovery races; adding agents multiplies state space by O(NumAgents!).
 *  - NumRequests=2, NumFids=1 (LU-19829 cfgs) or NumFids=2 (LU-19579/
 *    baseline cfgs): minimal configuration to catch both bugs.
 *  - MDT fails at most once (failover_occurred ensures one-shot).
 *  - On failover, agent connections are modeled as broken by clearing
 *    req_agent for all STARTED requests; agents cannot deliver completions
 *    to a dead MDT.  After RecoverActions the MDT is active again.
 *  - Cancel modeled only for WAITING (STARTED cancel involves coordinator
 *    waiting for agent to acknowledge; that layer is out of scope here).
 *  - Terminating action allows infinite stuttering once all requests reach
 *    terminal states, preventing TLC deadlock reports.
 *
 * ================================================================
 * What this model structurally cannot catch
 * ================================================================
 *
 *  (a) Multi-agent races: with N concurrent agents the state space grows as
 *      O(N * NumRequests!).  LU-19829 is caught with a single agent and
 *      two requests for the same FID, so agent count is not the bottleneck.
 *
 *  (b) Multiple failover cycles: after recovery the MDT is considered stable.
 *      A second failover would require a cycle counter and resettable state.
 *
 *  (c) HSM policy engine ordering: priority selection among WAITING requests
 *      is abstracted (any WAITING can be dispatched in any order).
 *
 *  (d) Agent re-registration lifecycle: agent crash + reconnect is not
 *      modeled; "agent1" is assumed to reconnect after recovery.
 *)

EXTENDS Integers, FiniteSets, TLC

CONSTANTS
    NumRequests,   \* Number of HSM requests in play (e.g., 2)
    NumFids,       \* Number of distinct file IDs (1 forces shared FID for LU-19829)
    InjectLU19579, \* Bug: recovery skips STARTED actions on MDT failover
    InjectLU19829  \* Bug: no FID dedup check before dispatch

Requests == 1..NumRequests
Fids     == 1..NumFids

\* ================================================================
\* Variables
\* ================================================================

VARIABLES
    req_state,         \* [Requests -> {"WAITING","STARTED","DONE","FAILED","CANCELED"}]
    req_fid,           \* [Requests -> Fids]  file ID for each request
    req_agent,         \* [Requests -> {"none","agent1"}]  assigned agent
    mdt_active,        \* BOOLEAN  TRUE = MDT is running and accepting agent RPCs
    failover_occurred, \* BOOLEAN  TRUE = MDT has failed over (one-shot flag)
    recovery_done      \* BOOLEAN  TRUE = coordinator recovery loop has completed

vars == << req_state, req_fid, req_agent, mdt_active, failover_occurred, recovery_done >>

TerminalStates == {"DONE", "FAILED", "CANCELED"}

\* ================================================================
\* Type invariant
\* ================================================================

TypeOK ==
    /\ req_state        \in [Requests -> {"WAITING","STARTED","DONE","FAILED","CANCELED"}]
    /\ req_fid          \in [Requests -> Fids]
    /\ req_agent        \in [Requests -> {"none", "agent1"}]
    /\ mdt_active        \in BOOLEAN
    /\ failover_occurred \in BOOLEAN
    /\ recovery_done     \in BOOLEAN

\* ================================================================
\* Helpers
\* ================================================================

\* Set of requests in STARTED state for a given FID
StartedForFid(f) ==
    { r \in Requests : req_state[r] = "STARTED" /\ req_fid[r] = f }

\* All requests have reached a terminal state
AllTerminal ==
    \A r \in Requests : req_state[r] \in TerminalStates

\* ================================================================
\* Initial state
\* ================================================================

Init ==
    /\ req_state = [r \in Requests |-> "WAITING"]
    /\ req_fid   \in [Requests -> Fids]  \* TLC explores all FID assignments
    /\ req_agent = [r \in Requests |-> "none"]
    /\ mdt_active        = TRUE
    /\ failover_occurred = FALSE
    /\ recovery_done     = FALSE

\* ================================================================
\* Actions
\* ================================================================

\* ------------------------------------------------------------------
\* Coordinator dispatches a WAITING request to the agent.
\*
\* Fix (correct behavior): before dispatching, check that no STARTED
\* request already exists for the same FID (deduplication guard).
\*
\* Bug LU-19829: InjectLU19829=TRUE skips this guard, allowing two
\* STARTED archive requests for the same FID simultaneously.
\* ------------------------------------------------------------------
CdtDispatch(r) ==
    /\ mdt_active
    /\ req_state[r] = "WAITING"
    /\ req_agent[r] = "none"
    /\ IF ~InjectLU19829
       THEN StartedForFid(req_fid[r]) = {}  \* dedup guard (correct)
       ELSE TRUE                             \* BUG: guard absent
    /\ req_state' = [req_state EXCEPT ![r] = "STARTED"]
    /\ req_agent' = [req_agent EXCEPT ![r] = "agent1"]
    /\ UNCHANGED << req_fid, mdt_active, failover_occurred, recovery_done >>

\* ------------------------------------------------------------------
\* Agent completes successfully: STARTED -> DONE.
\* Requires mdt_active (agent cannot deliver result to a dead MDT).
\* ------------------------------------------------------------------
AgentDone(r) ==
    /\ mdt_active
    /\ req_state[r] = "STARTED"
    /\ req_agent[r] = "agent1"
    /\ req_state' = [req_state EXCEPT ![r] = "DONE"]
    /\ req_agent' = [req_agent EXCEPT ![r] = "none"]
    /\ UNCHANGED << req_fid, mdt_active, failover_occurred, recovery_done >>

\* ------------------------------------------------------------------
\* Agent reports failure: STARTED -> FAILED.
\* ------------------------------------------------------------------
AgentFailed(r) ==
    /\ mdt_active
    /\ req_state[r] = "STARTED"
    /\ req_agent[r] = "agent1"
    /\ req_state' = [req_state EXCEPT ![r] = "FAILED"]
    /\ req_agent' = [req_agent EXCEPT ![r] = "none"]
    /\ UNCHANGED << req_fid, mdt_active, failover_occurred, recovery_done >>

\* ------------------------------------------------------------------
\* Cancel a WAITING request: WAITING -> CANCELED.
\* (Cancellation of STARTED requests involves an async callback;
\* that protocol layer is out of scope for this model.)
\* ------------------------------------------------------------------
CancelWaiting(r) ==
    /\ mdt_active
    /\ req_state[r] = "WAITING"
    /\ req_state' = [req_state EXCEPT ![r] = "CANCELED"]
    /\ UNCHANGED << req_fid, req_agent, mdt_active, failover_occurred, recovery_done >>

\* ------------------------------------------------------------------
\* MDT failover: MDT goes down (one-shot, guarded by ~failover_occurred).
\* On failover, all in-flight agent connections are broken: clear req_agent
\* for any STARTED requests so they cannot deliver completions to the dead MDT.
\* ------------------------------------------------------------------
FailoverOccur ==
    /\ mdt_active
    /\ ~failover_occurred
    /\ mdt_active'        = FALSE
    /\ failover_occurred' = TRUE
    \* Break agent connections for in-flight requests
    /\ req_agent' = [r \in Requests |->
           IF req_state[r] = "STARTED" THEN "none" ELSE req_agent[r]]
    /\ UNCHANGED << req_state, req_fid, recovery_done >>

\* ------------------------------------------------------------------
\* Recovery thread: runs after failover, re-queues in-flight actions.
\* After recovery completes, the new MDT instance becomes active (mdt_active=TRUE).
\*
\* Correct behavior: STARTED -> WAITING (re-queued for dispatch by new MDT).
\*
\* Bug LU-19579 (InjectLU19579=TRUE): recovery loop skips STARTED actions,
\* leaving req_state=STARTED with req_agent="none".  These requests are stuck:
\*   - AgentDone/AgentFailed cannot fire (req_agent="none").
\*   - CdtDispatch cannot fire (req_state != "WAITING").
\*   - They hang until an external timeout.
\* ------------------------------------------------------------------
RecoverActions ==
    /\ ~mdt_active
    /\ ~recovery_done
    /\ failover_occurred
    /\ LET reset(r) ==
           IF req_state[r] = "STARTED"
           THEN IF InjectLU19579
                THEN "STARTED"   \* BUG: silently skipped
                ELSE "WAITING"   \* FIX: re-queued for re-dispatch
           ELSE req_state[r]
       IN req_state' = [r \in Requests |-> reset(r)]
    /\ mdt_active'    = TRUE   \* new MDT instance is now active
    /\ recovery_done' = TRUE
    /\ UNCHANGED << req_fid, req_agent, failover_occurred >>

\* ------------------------------------------------------------------
\* Termination: allow infinite stuttering once all requests are terminal.
\* Prevents TLC from reporting deadlock in valid end states.
\* ------------------------------------------------------------------
Terminating ==
    /\ AllTerminal
    /\ UNCHANGED vars

\* ================================================================
\* Next-state relation and specification
\* ================================================================

Next ==
    \/ \E r \in Requests : CdtDispatch(r)
    \/ \E r \in Requests : AgentDone(r)
    \/ \E r \in Requests : AgentFailed(r)
    \/ \E r \in Requests : CancelWaiting(r)
    \/ FailoverOccur
    \/ RecoverActions
    \/ Terminating

Spec == Init /\ [][Next]_vars

\* ================================================================
\* Safety invariants
\* ================================================================

\* DONE/FAILED are terminal: no re-dispatch. Violated if coordinator
\* re-dispatches a completed request.
NoDoneRedispatch ==
    \A r \in Requests :
        req_state[r] \in {"DONE", "FAILED"} => req_agent[r] = "none"

\* CANCELED requests must not have an agent assigned.
CanceledNoAgent ==
    \A r \in Requests :
        req_state[r] = "CANCELED" => req_agent[r] = "none"

\* STARTED requests must have an agent assigned (or have lost it on failover,
\* but that is a transient fault state; StartedHasAgent is intentionally NOT
\* checked in the LU-19579 bug cfgs where failover clears req_agent first).
StartedHasAgent ==
    \A r \in Requests :
        req_state[r] = "STARTED" /\ mdt_active => req_agent[r] /= "none"

\* At most one STARTED request per FID at any time.
\* Violated by LU-19829 (archive dedup guard removed).
AtMostOneStartedPerFID ==
    \A f \in Fids :
        Cardinality(StartedForFid(f)) <= 1

\* After recovery completes, no requests remain in STARTED state with no agent.
\* With LU-19579, recovery skips STARTED; FailoverOccur already cleared req_agent.
\* The result: req_state="STARTED" /\ req_agent="none" /\ mdt_active=TRUE -- stuck.
\* This is subsumed by StartedHasAgent above, but provided as an explicit alias
\* to preserve the LU-19579 cross-reference for --verify-fix output.
\*
\* NOTE: "no STARTED after recovery" would be too strong -- legitimate re-dispatches
\* after recovery also produce STARTED states (with req_agent /= "none").
\* The invariant that actually catches LU-19579 is StartedHasAgent.
NoStartedAfterRecovery ==
    \A r \in Requests :
        ~(req_state[r] = "STARTED" /\ req_agent[r] = "none" /\ mdt_active)

\* ================================================================
\* Liveness
\* ================================================================

\* All requests eventually reach a terminal state.
EventuallyAllTerminal == <>(AllTerminal)

=============================================================================
