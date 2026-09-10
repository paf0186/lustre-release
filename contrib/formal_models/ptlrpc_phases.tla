------------------------ MODULE ptlrpc_phases ------------------------
(*
 * TLA+ specification of the PTLRPC client request phase machine.
 *
 * Models RQ_PHASE_* transitions for a single client-side RPC in
 * ptlrpc_check_set() (lustre/ptlrpc/client.c), including:
 *   - Phase transitions: NEW -> RPC -> BULK -> INTERPRET -> COMPLETE
 *   - Unregistering sub-phases: UNREG_RPC, UNREG_BULK
 *   - Network callbacks: reply arrives, bulk completes, MDs unlink
 *   - Timeout expiry: ptlrpc_expire_one_request
 *   - Flag-driven implicit transitions (rq_err, rq_net_err,
 *     rq_timedout, rq_replied, rq_resend, rq_intr)
 *
 * Known bugs modeled:
 *
 *   LU-7434: Before the fix, a single "UNREGISTERING" phase was
 *   used for both RPC and bulk MD unlinks. If bulk is lost,
 *   ptlrpc_expire_one_request tries to move to UNREG_BULK but
 *   ptlrpc_rqphase_move() is a no-op (already in UNREGISTERING).
 *   Bulk MDs are never unlinked -> hang.
 *   Fix: split into UNREG_RPC and UNREG_BULK.
 *   Set InjectBug7434 = TRUE to use old single UNREGISTERING phase.
 *
 *   LU-11647: On resend, the code must unregister old bulk MDs
 *   before calling ptl_send_rpc (which calls ptlrpc_register_bulk).
 *   Before the fix, ptlrpc_unregister_bulk was only called in the
 *   timeout sub-path, not all resend paths. Result: ASSERTION
 *   (bd_md_count == 0) failed in ptlrpc_register_bulk.
 *   Fix: move ptlrpc_unregister_bulk unconditionally before
 *   ptl_send_rpc on all resend paths.
 *   Set InjectBug11647 = TRUE to skip bulk unregister before resend.
 *
 *   LU-12816/LU-13509: ptl_send_rpc calls ptlrpc_register_bulk
 *   (sets bd_registered=1), then fails (e.g., reply ME attach
 *   ENOMEM). Cleanup calls ptlrpc_unregister_bulk but doesn't
 *   clear bd_registered. On resend, ptlrpc_register_bulk asserts
 *   !bd_registered -> LBUG.
 *   Fix: clear bd_registered in ptlrpc_unregister_bulk itself.
 *   Set InjectBug12816 = TRUE to leave bd_registered stale.
 *
 *   LU-5696: request_out_callback fires after reply_in_callback
 *   (out-of-order callbacks). The callback sets req_unlinked=TRUE
 *   but doesn't call ptlrpc_client_wake_req(). check_set sleeps
 *   and never re-examines the request -> hang.
 *   Fix: add ptlrpc_client_wake_req() in request_out_callback.
 *   Set InjectBug5696 = TRUE to suppress wakeup from ReqOutCallback.
 *
 * Source (lustre-release master 47638add78):
 *   lustre/include/lustre_net.h:739-748   enum rq_phase
 *   lustre/include/lustre_net.h:2393-2421 ptlrpc_rqphase_move (PhaseMove;
 *                                    nested-unreg guard 2399-2404)
 *   lustre/include/lustre_net.h:2452-2471 ptlrpc_client_recv_or_unlink
 *                                    (RecvOrUnlink)
 *   lustre/include/lustre_net.h:2018-2037 ptlrpc_client_bulk_active
 *   lustre/ptlrpc/client.c:1808-1943 ptlrpc_send_new_req (SendNew)
 *   lustre/ptlrpc/client.c:1985-2467 ptlrpc_check_set (CheckSetActions;
 *                                    per-action refs inline below)
 *   lustre/ptlrpc/client.c:2478-2557 ptlrpc_expire_one_request
 *                                    (NetErrExpire, ExpireReply/ExpireBulk:
 *                                    rq_timedout 2488, unregister reply
 *                                    and bulk 2509-2510)
 *   lustre/ptlrpc/client.c:2563-2600 ptlrpc_expired_set (TimeoutFires)
 *   lustre/ptlrpc/client.c:2977-3045 ptlrpc_unregister_reply
 *   lustre/ptlrpc/niobuf.c:335-468   ptlrpc_register_bulk (bd_failure
 *                                    cleared 367, bd_registered LASSERTF
 *                                    381-384 and set 387)
 *   lustre/ptlrpc/niobuf.c:469-533   ptlrpc_unregister_bulk (bd_registered
 *                                    cleared 477-478 = LU-13509 fix,
 *                                    mdunlink 496, UNREG_BULK move 502)
 *   lustre/ptlrpc/niobuf.c:852-1166  ptl_send_rpc (ptlrpc_register_bulk
 *                                    1000-1002, flag reset 1051-1064,
 *                                    cleanup_bulk 1149)
 *   lustre/ptlrpc/events.c:29-70     request_out_callback (ReqOutCallback;
 *                                    LU-5696 wakeup 53-54, 63-64)
 *   lustre/ptlrpc/events.c:75-166    reply_in_callback (ReplyInCallback,
 *                                    ReplyUnlinked)
 *   lustre/ptlrpc/events.c:171-221   client_bulk_callback (BulkCompleteOk/Fail)
 *
 * Validated against: lustre-release master 47638add78 (2026-09-06)
 * Validation notes:
 *   - Line refs updated; no semantic drift.  All four modeled fixes are
 *     present: UNREG_RPC/UNREG_BULK split (LU-7434), ptlrpc_unregister_bulk
 *     before ptl_send_rpc on every resend (LU-11647, client.c:2282-2284),
 *     bd_registered cleared in ptlrpc_unregister_bulk (LU-13509,
 *     niobuf.c:477-478), wakeup in request_out_callback (LU-5696,
 *     events.c:53-54).
 *   - Known abstractions (not drift): reply_in_callback also clears
 *     rq_resend on a real reply (events.c:143); ReplyInCallback leaves
 *     resend unchanged, so a reply racing a pending resend is resent in
 *     the model but processed in the code.  The LU-5696 wakeup fires only
 *     when rq_reply_unlinked is already set; ReqOutCallbackStep wakes
 *     unconditionally.  TimeoutFires sets no_resend to bound the resend
 *     loop; the code has no such coupling.
 *)

EXTENDS Integers, FiniteSets, TLC

CONSTANTS
    InjectBug7434,    \* TRUE = old single UNREGISTERING phase
    InjectBug11647,   \* TRUE = resend without unregistering bulk first
    InjectBug12816,   \* TRUE = bd_registered not cleared on partial send fail
    InjectBug5696,    \* TRUE = ReqOutCallback doesn't wake check_set
    HasBulk,          \* TRUE = request has rq_bulk (e.g., OST_READ/WRITE)
    BulkLost,         \* TRUE = bulk never completes (LU-7434 scenario)
    NoResend          \* TRUE = request won't be resent (breaks resend loop)

VARIABLES
    \* Request phase (the core state)
    phase,
    next_phase,        \* saved phase when entering UNREG_*

    \* Network MD state
    req_unlinked,      \* request MD unlinked (request_out_callback)
    reply_unlinked,    \* reply MD unlinked (reply_in_callback UNLINK)
    receiving_reply,   \* reply MD posted, awaiting reply
    bulk_active,       \* bulk MDs still active

    \* Reply/completion
    replied,           \* reply has been received
    reply_err,         \* reply indicates error (status < 0)

    \* Error and timeout flags (set asynchronously)
    err,               \* rq_err: general error
    net_err,           \* rq_net_err: network error
    timedout,          \* rq_timedout
    resend,            \* rq_resend
    intr,              \* rq_intr: signal interrupt
    no_resend,         \* rq_no_resend

    \* Bulk outcome
    bulk_failed,

    \* Bug detection: set TRUE if ptl_send_rpc called with bulk
    \* already registered (LU-11647: bd_md_count != 0 assertion)
    bulk_double_registered,

    \* Scheduling: TRUE when check_set should iterate on this request.
    \* Callbacks set this TRUE (wake the set); check_set consumes it.
    \* Kept separate from vars so individual actions don't need to
    \* handle it -- the Next relation composes it at the top level.
    set_woken

\* Core state variables (used by individual actions)
vars == << phase, next_phase, req_unlinked, reply_unlinked,
           receiving_reply, bulk_active, replied, reply_err,
           err, net_err, timedout, resend, intr, no_resend,
           bulk_failed, bulk_double_registered >>

\* All variables including scheduling (used by Spec)
all_vars == << phase, next_phase, req_unlinked, reply_unlinked,
               receiving_reply, bulk_active, replied, reply_err,
               err, net_err, timedout, resend, intr, no_resend,
               bulk_failed, bulk_double_registered, set_woken >>

\* ================================================================
\* Helpers
\* ================================================================

\* recv_or_unlink: TRUE if reply MD is still active
\* (matches ptlrpc_client_recv_or_unlink)
RecvOrUnlink == receiving_reply \/ ~reply_unlinked \/ ~req_unlinked

\* Phase move semantics (ptlrpc_rqphase_move)
\* Returns [new_phase, new_next_phase] as a record
PhaseMove(cur_phase, cur_next, target) ==
    IF target \in {"UNREG_RPC", "UNREG_BULK"} THEN
        IF cur_phase \in {"UNREG_RPC", "UNREG_BULK", "UNREGISTERING"} THEN
            \* No-op: already unregistering
            [p |-> cur_phase, np |-> cur_next]
        ELSE IF InjectBug7434 THEN
            [p |-> "UNREGISTERING", np |-> cur_phase]
        ELSE
            [p |-> target, np |-> cur_phase]
    ELSE
        [p |-> target, np |-> cur_next]

\* Unchanged helper for all non-phase variables
NonPhaseVars == << req_unlinked, reply_unlinked, receiving_reply,
                   bulk_active, replied, reply_err, err, net_err,
                   timedout, resend, intr, no_resend, bulk_failed,
                   bulk_double_registered >>

\* ================================================================
\* Valid phases
\* ================================================================

ValidPhases == IF InjectBug7434
               THEN {"NEW", "RPC", "BULK", "INTERPRET", "COMPLETE",
                     "UNREGISTERING", "UNDEFINED"}
               ELSE {"NEW", "RPC", "BULK", "INTERPRET", "COMPLETE",
                     "UNREG_RPC", "UNREG_BULK", "UNDEFINED"}

\* ================================================================
\* Initial state
\* ================================================================

Init ==
    /\ phase = "NEW"
    /\ next_phase = "UNDEFINED"
    /\ req_unlinked = TRUE
    /\ reply_unlinked = TRUE
    /\ receiving_reply = FALSE
    /\ bulk_active = FALSE
    /\ replied = FALSE
    /\ reply_err = FALSE
    /\ err = FALSE
    /\ net_err = FALSE
    /\ timedout = FALSE
    /\ resend = FALSE
    /\ intr = FALSE
    /\ no_resend = NoResend
    /\ bulk_failed = FALSE
    /\ bulk_double_registered = FALSE
    /\ set_woken = TRUE   \* Initially woken to send the NEW request

\* ================================================================
\* CheckSet actions: model ptlrpc_check_set() iteration
\*
\* Each action represents one path through the check_set loop body.
\* The checker loops until COMPLETE; each iteration picks the first
\* matching condition and applies it.
\* ================================================================

\* --- NEW: send the request (ptlrpc_send_new_req -> ptl_send_rpc) ---
\* ptl_send_rpc clears all flags from previous attempts (niobuf.c:1051-1064)
SendNew ==
    /\ phase = "NEW"
    /\ phase' = "RPC"
    /\ next_phase' = next_phase
    /\ req_unlinked' = FALSE
    /\ reply_unlinked' = FALSE
    /\ receiving_reply' = TRUE
    /\ bulk_active' = IF HasBulk THEN TRUE ELSE FALSE
    \* ptl_send_rpc clears these flags
    /\ replied' = FALSE
    /\ err' = FALSE
    /\ net_err' = FALSE
    /\ timedout' = FALSE
    /\ resend' = FALSE
    \* ptlrpc_register_bulk clears bd_failure (niobuf.c)
    /\ bulk_failed' = FALSE
    /\ UNCHANGED << reply_err, intr, no_resend,
                    bulk_double_registered >>

\* LU-12816: ptl_send_rpc registers bulk (bd_registered=1), then
\* fails on reply ME attach. Cleanup unregisters bulk MDs but with
\* the bug doesn't clear bd_registered. Request goes back to NEW.
\* Next send hits ASSERTION(!bd_registered) in ptlrpc_register_bulk.
SendNewPartialFail ==
    /\ phase = "NEW"
    /\ HasBulk
    /\ InjectBug12816
    \* Bulk was registered then unregistered, but bd_registered stuck
    /\ bulk_double_registered' = TRUE
    /\ UNCHANGED << phase, next_phase, req_unlinked, reply_unlinked,
                    receiving_reply, bulk_active, replied, reply_err,
                    err, net_err, timedout, resend, intr, no_resend,
                    bulk_failed >>

\* --- UNREG_RPC: wait for recv_or_unlink to clear ---
\* (Wait actions removed -- in the wakeup model, "nothing to do" is
\* naturally represented by CheckSetStep being disabled when no
\* progress action is enabled. This avoids WF starvation where a
\* no-op Wait action satisfies fairness while starving real progress.)

UnregRpcDone ==
    /\ phase = "UNREG_RPC"
    /\ ~RecvOrUnlink
    /\ phase' = next_phase
    /\ UNCHANGED << next_phase, NonPhaseVars >>

\* --- UNREG_BULK: wait for bulk_active to clear ---
UnregBulkDone ==
    /\ phase = "UNREG_BULK"
    /\ ~bulk_active
    /\ phase' = next_phase
    /\ UNCHANGED << next_phase, NonPhaseVars >>

\* --- UNREGISTERING (bug mode): single phase, only checks recv_or_unlink ---
UnregDone ==
    /\ InjectBug7434
    /\ phase = "UNREGISTERING"
    /\ ~RecvOrUnlink
    \* BUG: proceeds even if bulk_active is still TRUE
    /\ phase' = next_phase
    /\ UNCHANGED << next_phase, NonPhaseVars >>

\* --- net_err without timeout: expire the request ---
\* ptlrpc_expire_one_request sets timedout, starts async unlinks
NetErrExpire ==
    /\ phase \in {"RPC", "BULK"}
    /\ net_err
    /\ ~timedout
    /\ timedout' = TRUE
    \* Start reply unlink
    /\ LET pm == PhaseMove(phase, next_phase, "UNREG_RPC")
       IN IF RecvOrUnlink THEN
              /\ phase' = pm.p
              /\ next_phase' = pm.np
          ELSE
              /\ UNCHANGED << phase, next_phase >>
    /\ UNCHANGED << req_unlinked, reply_unlinked, receiving_reply,
                    bulk_active, replied, reply_err, err, net_err,
                    resend, intr, no_resend, bulk_failed,
                    bulk_double_registered >>

\* After net_err expire, if unlinks done and no_resend -> INTERPRET
NetErrFail ==
    /\ phase \in {"RPC", "BULK"}
    /\ net_err /\ timedout
    /\ ~RecvOrUnlink /\ ~bulk_active
    /\ no_resend
    /\ phase' = "INTERPRET"
    /\ UNCHANGED << next_phase, NonPhaseVars >>

\* --- rq_err: unregister and fail ---
\* err check runs AFTER net_err check (client.c:2131 vs 2111)
ErrUnreg ==
    /\ phase \in {"RPC", "BULK", "INTERPRET"}
    /\ err
    /\ ~(net_err /\ ~timedout)  \* net_err check has priority
    /\ RecvOrUnlink
    /\ LET pm == PhaseMove(phase, next_phase, "UNREG_RPC")
       IN /\ phase' = pm.p
          /\ next_phase' = pm.np
    /\ UNCHANGED << req_unlinked, reply_unlinked, receiving_reply,
                    bulk_active, replied, reply_err, err, net_err,
                    timedout, resend, intr, no_resend, bulk_failed,
                    bulk_double_registered >>

ErrFail ==
    /\ phase \in {"RPC", "BULK"}
    /\ err
    /\ ~(net_err /\ ~timedout)  \* net_err check has priority
    /\ ~RecvOrUnlink
    /\ phase' = "INTERPRET"
    /\ replied' = FALSE
    /\ UNCHANGED << next_phase, req_unlinked, reply_unlinked,
                    receiving_reply, bulk_active, reply_err, err,
                    net_err, timedout, resend, intr, no_resend,
                    bulk_failed, bulk_double_registered >>

\* --- intr + timedout: interrupt ---
\* In check_set, this check runs BEFORE the RPC/BULK-specific blocks
\* (client.c:2156-2161). So it takes priority over resend/reply checks.
IntrTimeout ==
    /\ phase \in {"RPC", "BULK"}
    /\ intr /\ timedout
    /\ ~err
    /\ ~(net_err /\ ~timedout)  \* net_err check runs first
    /\ phase' = "INTERPRET"
    /\ UNCHANGED << next_phase, NonPhaseVars >>

\* Guard: these checks are in the RPC/BULK-specific blocks, which only
\* run AFTER the err, net_err, and intr+timedout checks pass.
\* "UpstreamChecksPass" means none of those higher-priority checks fire.
\* client.c:2111 (net_err), 2131 (err), 2156 (intr+timedout), 2163 (RPC)
UpstreamChecksPass ==
    /\ ~err
    /\ ~(net_err /\ ~timedout)
    /\ ~(intr /\ timedout)

\* --- RPC phase: reply received, process it ---
RpcReplyReceived ==
    /\ phase = "RPC"
    /\ replied
    /\ UpstreamChecksPass
    /\ ~resend /\ ~timedout
    \* Must unregister reply first
    /\ ~RecvOrUnlink
    \* after_reply succeeds, decide next phase
    /\ IF ~HasBulk \/ reply_err THEN
           phase' = "INTERPRET"
       ELSE
           phase' = "BULK"
    /\ UNCHANGED << next_phase, NonPhaseVars >>

\* Reply received but reply MD still active -> start unlink
RpcReplyUnregNeeded ==
    /\ phase = "RPC"
    /\ replied
    /\ UpstreamChecksPass
    /\ ~resend /\ ~timedout
    /\ RecvOrUnlink
    /\ LET pm == PhaseMove(phase, next_phase, "UNREG_RPC")
       IN /\ phase' = pm.p
          /\ next_phase' = pm.np
    /\ UNCHANGED << req_unlinked, reply_unlinked, receiving_reply,
                    bulk_active, replied, reply_err, err, net_err,
                    timedout, resend, intr, no_resend, bulk_failed,
                    bulk_double_registered >>

\* Timeout/resend in RPC phase: unregister and resend
RpcResendUnreg ==
    /\ phase = "RPC"
    /\ (timedout \/ resend)
    /\ UpstreamChecksPass
    /\ RecvOrUnlink
    /\ LET pm == PhaseMove(phase, next_phase, "UNREG_RPC")
       IN /\ phase' = pm.p
          /\ next_phase' = pm.np
    /\ UNCHANGED << req_unlinked, reply_unlinked, receiving_reply,
                    bulk_active, replied, reply_err, err, net_err,
                    timedout, resend, intr, no_resend, bulk_failed,
                    bulk_double_registered >>

\* Timeout/resend: unlink done, now resend (calls ptl_send_rpc)
\* LU-11647 fix: bulk must be inactive before calling ptl_send_rpc.
\* With InjectBug11647, the bulk check is skipped -> double register.
RpcResendDoSend ==
    /\ phase = "RPC"
    /\ (timedout \/ resend)
    /\ UpstreamChecksPass
    /\ ~no_resend   \* ptlrpc_no_resend check (client.c:2194)
    /\ ~RecvOrUnlink
    /\ InjectBug11647 \/ ~bulk_active  \* LU-11647: bug skips check
    \* Detect double-register: ptlrpc_register_bulk ASSERTION failure
    /\ bulk_double_registered' = (bulk_active /\ HasBulk)
    \* ptl_send_rpc: re-post MDs and clear flags (niobuf.c:1051-1064)
    /\ req_unlinked' = FALSE
    /\ reply_unlinked' = FALSE
    /\ receiving_reply' = TRUE
    /\ bulk_active' = IF HasBulk THEN TRUE ELSE FALSE
    /\ replied' = FALSE
    /\ err' = FALSE
    /\ net_err' = FALSE
    /\ timedout' = FALSE
    /\ resend' = FALSE
    /\ bulk_failed' = FALSE
    /\ UNCHANGED << phase, next_phase, reply_err,
                    intr, no_resend >>

\* Resend fails with ENOMEM: back to NEW
RpcResendFail ==
    /\ phase = "RPC"
    /\ (timedout \/ resend)
    /\ UpstreamChecksPass
    /\ ~no_resend
    /\ ~RecvOrUnlink
    /\ phase' = "NEW"
    /\ resend' = FALSE
    /\ timedout' = FALSE
    /\ UNCHANGED << next_phase, req_unlinked, reply_unlinked,
                    receiving_reply, bulk_active, replied, reply_err,
                    err, net_err, intr, no_resend, bulk_failed,
                    bulk_double_registered >>

\* no_resend set: fail with -ENOTCONN (client.c:2194-2203)
RpcNoResendFail ==
    /\ phase = "RPC"
    /\ (timedout \/ resend)
    /\ UpstreamChecksPass
    /\ no_resend
    /\ ~RecvOrUnlink
    /\ phase' = "INTERPRET"
    /\ UNCHANGED << next_phase, NonPhaseVars >>

\* --- BULK phase: wait for bulk to complete ---
BulkDone ==
    /\ phase = "BULK"
    /\ ~bulk_active
    /\ UpstreamChecksPass
    /\ phase' = "INTERPRET"
    /\ UNCHANGED << next_phase, NonPhaseVars >>

\* --- INTERPRET: unregister both MDs, then complete ---
InterpretUnregReply ==
    /\ phase = "INTERPRET"
    /\ RecvOrUnlink
    /\ LET pm == PhaseMove(phase, next_phase, "UNREG_RPC")
       IN /\ phase' = pm.p
          /\ next_phase' = pm.np
    /\ UNCHANGED << req_unlinked, reply_unlinked, receiving_reply,
                    bulk_active, replied, reply_err, err, net_err,
                    timedout, resend, intr, no_resend, bulk_failed,
                    bulk_double_registered >>

InterpretUnregBulk ==
    /\ phase = "INTERPRET"
    /\ ~RecvOrUnlink
    /\ HasBulk /\ bulk_active
    /\ LET pm == PhaseMove(phase, next_phase, "UNREG_BULK")
       IN /\ phase' = pm.p
          /\ next_phase' = pm.np
    /\ UNCHANGED << req_unlinked, reply_unlinked, receiving_reply,
                    bulk_active, replied, reply_err, err, net_err,
                    timedout, resend, intr, no_resend, bulk_failed,
                    bulk_double_registered >>

InterpretComplete ==
    /\ phase = "INTERPRET"
    /\ ~RecvOrUnlink
    /\ (~HasBulk \/ ~bulk_active)
    /\ phase' = "COMPLETE"
    /\ UNCHANGED << next_phase, NonPhaseVars >>

\* ================================================================
\* Network actions: asynchronous LNet callbacks
\* ================================================================

\* request_out_callback: request MD sent and unlinked
ReqOutCallback ==
    /\ ~req_unlinked
    /\ req_unlinked' = TRUE
    /\ UNCHANGED << phase, next_phase, reply_unlinked, receiving_reply,
                    bulk_active, replied, reply_err, err, net_err,
                    timedout, resend, intr, no_resend, bulk_failed,
                    bulk_double_registered >>

\* reply_in_callback: reply arrives
ReplyInCallback ==
    /\ receiving_reply /\ ~replied
    /\ receiving_reply' = FALSE
    /\ replied' = TRUE
    /\ \/ reply_err' = FALSE
       \/ reply_err' = TRUE
    /\ UNCHANGED << phase, next_phase, req_unlinked, reply_unlinked,
                    bulk_active, err, net_err, timedout, resend,
                    intr, no_resend, bulk_failed,
                    bulk_double_registered >>

\* reply MD unlink completes (LNET_EVENT_UNLINK on reply ME)
\* Only fires after reply was received (~receiving_reply from
\* ReplyInCallback) or after explicit LNetMDUnlink (ExpireReply
\* clears receiving_reply directly). In LNet, REPLY event always
\* precedes UNLINK event for the same MD.
ReplyUnlinked ==
    /\ ~reply_unlinked
    /\ ~receiving_reply  \* reply must have been received or MD unlinked
    /\ reply_unlinked' = TRUE
    /\ receiving_reply' = FALSE
    /\ UNCHANGED << phase, next_phase, req_unlinked, bulk_active,
                    replied, reply_err, err, net_err, timedout,
                    resend, intr, no_resend, bulk_failed,
                    bulk_double_registered >>

\* client_bulk_callback: bulk transfer completes (success)
\* When BulkLost=TRUE, this never fires (simulating lost bulk)
BulkCompleteOk ==
    /\ ~BulkLost
    /\ bulk_active
    /\ bulk_active' = FALSE
    /\ bulk_failed' = FALSE
    /\ UNCHANGED << phase, next_phase, req_unlinked, reply_unlinked,
                    receiving_reply, replied, reply_err, err, net_err,
                    timedout, resend, intr, no_resend,
                    bulk_double_registered >>

\* client_bulk_callback: bulk transfer fails
BulkCompleteFail ==
    /\ ~BulkLost
    /\ bulk_active
    /\ bulk_active' = FALSE
    /\ bulk_failed' = TRUE
    /\ UNCHANGED << phase, next_phase, req_unlinked, reply_unlinked,
                    receiving_reply, replied, reply_err, err, net_err,
                    timedout, resend, intr, no_resend,
                    bulk_double_registered >>

\* Network error occurs
NetworkError ==
    /\ phase = "RPC"
    /\ net_err' = TRUE
    /\ UNCHANGED << phase, next_phase, req_unlinked, reply_unlinked,
                    receiving_reply, bulk_active, replied, reply_err,
                    err, timedout, resend, intr, no_resend,
                    bulk_failed, bulk_double_registered >>

\* Timeout fires (set-level timer, fires in any active phase)
TimeoutFires ==
    /\ phase \in {"RPC", "BULK", "UNREG_RPC", "UNREG_BULK", "UNREGISTERING"}
    /\ timedout' = TRUE
    /\ no_resend' = TRUE
    /\ UNCHANGED << phase, next_phase, req_unlinked, reply_unlinked,
                    receiving_reply, bulk_active, replied, reply_err,
                    err, net_err, resend, intr, bulk_failed,
                    bulk_double_registered >>

\* Signal interrupt
SignalIntr ==
    /\ intr' = TRUE
    /\ UNCHANGED << phase, next_phase, req_unlinked, reply_unlinked,
                    receiving_reply, bulk_active, replied, reply_err,
                    err, net_err, timedout, resend, no_resend,
                    bulk_failed, bulk_double_registered >>

\* ================================================================
\* Expiry: ptlrpc_expire_one_request
\*
\* On timeout, initiates async unlinks of both reply and bulk MDs.
\* With the bug: tries to move to UNREG_BULK but if already in
\* UNREGISTERING, the move is a no-op -> bulk never unlinked.
\* With the fix: moves to UNREG_RPC and UNREG_BULK independently.
\*
\* After calling LNetMDUnlink, the unlink callback fires
\* asynchronously (modeled by ReplyUnlinked/BulkComplete* above).
\* The expiry action models the LNetMDUnlink call for bulk, which
\* in the fixed code eventually triggers BulkCompleteFail.
\* ================================================================

\* Expire: initiate reply unlink
ExpireReply ==
    /\ timedout
    /\ phase /= "COMPLETE" /\ phase /= "NEW"
    /\ RecvOrUnlink
    /\ LET pm == PhaseMove(phase, next_phase, "UNREG_RPC")
       IN /\ phase' = pm.p
          /\ next_phase' = pm.np
    \* Force the reply unlink (LNetMDUnlink effect)
    /\ reply_unlinked' = TRUE
    /\ receiving_reply' = FALSE
    /\ UNCHANGED << req_unlinked, bulk_active, replied, reply_err,
                    err, net_err, timedout, resend, intr, no_resend,
                    bulk_failed, bulk_double_registered >>

\* Expire: initiate bulk unlink
\* This is where LU-7434 manifests. In the buggy code, if we're
\* already in UNREGISTERING, PhaseMove is a no-op and we never
\* call LNetMDUnlink on the bulk MDs.
ExpireBulk ==
    /\ timedout
    /\ phase /= "COMPLETE" /\ phase /= "NEW"
    /\ HasBulk /\ bulk_active
    /\ LET pm == PhaseMove(phase, next_phase, "UNREG_BULK")
       IN /\ phase' = pm.p
          /\ next_phase' = pm.np
          \* Only force bulk unlink if phase actually changed
          \* (i.e., we're not stuck in UNREGISTERING with the bug)
          /\ IF pm.p = "UNREG_BULK" \/ pm.p /= phase THEN
                 /\ bulk_active' = FALSE
                 /\ bulk_failed' = TRUE
             ELSE
                 \* BUG PATH: phase didn't change, no unlink initiated
                 /\ UNCHANGED << bulk_active, bulk_failed >>
    /\ UNCHANGED << req_unlinked, reply_unlinked, receiving_reply,
                    replied, reply_err, err, net_err, timedout,
                    resend, intr, no_resend,
                    bulk_double_registered >>

\* ================================================================
\* Spec
\* ================================================================

CheckSetActions ==
    \/ SendNew \/ SendNewPartialFail
    \/ UnregRpcDone
    \/ UnregBulkDone
    \/ UnregDone
    \/ NetErrExpire \/ NetErrFail
    \/ ErrUnreg \/ ErrFail
    \/ IntrTimeout
    \/ RpcReplyReceived \/ RpcReplyUnregNeeded
    \/ RpcResendUnreg \/ RpcResendDoSend \/ RpcResendFail \/ RpcNoResendFail
    \/ BulkDone
    \/ InterpretUnregReply \/ InterpretUnregBulk \/ InterpretComplete

\* ================================================================
\* Wakeup mechanism: ptlrpc_check_set scheduling
\*
\* check_set only runs when the set is woken. After processing, if
\* progress was made (core state changed), ptlrpcd reschedules itself
\* immediately. If nothing changed (waiting), the thread sleeps until
\* a callback wakes it.
\*
\* set_woken is handled here in the Next relation, NOT in individual
\* actions. Each action only touches vars (core state). The Next
\* relation composes set_woken on top.
\*
\* LU-5696: request_out_callback didn't call ptlrpc_client_wake_req.
\* With InjectBug5696, ReqOutCallback doesn't wake the set. If it
\* fires AFTER all other callbacks that would wake, check_set never
\* re-examines the request -> hang.
\* ================================================================

\* check_set evaluates conditions and takes the first useful action.
\* In the model, CheckSetProgress fires when any CheckSetAction is
\* enabled. If no action is useful, CheckSetSleep fires -- check_set
\* found nothing to do and the thread goes back to sleep.
\*
\* CheckSetSleep uses ENABLED to guard: it only fires when no
\* CheckSetAction is possible. This models the code's sequential
\* condition evaluation -- if something matches, it runs; otherwise
\* the loop returns 0 and ptlrpcd sleeps.
CheckSetProgress ==
    /\ set_woken
    /\ CheckSetActions
    /\ set_woken' = TRUE   \* progress made, self-reschedule

CheckSetSleep ==
    /\ set_woken
    /\ ~ENABLED CheckSetActions   \* nothing useful to do
    /\ UNCHANGED vars
    /\ set_woken' = FALSE          \* thread goes to sleep

\* Network callbacks wake the set. Each callback calls wake_up()
\* on the set waitq via ptlrpc_client_wake_req().
\* LU-5696 bug: ReqOutCallback omits the wake call.
NetworkStep ==
    \/ (ReqOutCallback /\ set_woken' = IF InjectBug5696
                                        THEN set_woken
                                        ELSE TRUE)
    \/ (ReplyInCallback /\ set_woken' = TRUE)
    \/ (ReplyUnlinked /\ set_woken' = TRUE)
    \/ (BulkCompleteOk /\ set_woken' = TRUE)
    \/ (BulkCompleteFail /\ set_woken' = TRUE)
    \/ (NetworkError /\ set_woken' = TRUE)
    \/ (TimeoutFires /\ set_woken' = TRUE)
    \/ (SignalIntr /\ set_woken' = TRUE)

\* Expiry runs from the timer context and wakes the set
ExpiryStep ==
    /\ (\/ ExpireReply \/ ExpireBulk)
    /\ set_woken' = TRUE

Next ==
    \/ CheckSetProgress
    \/ CheckSetSleep
    \/ NetworkStep
    \/ ExpiryStep

\* ================================================================
\* Fairness
\* ================================================================
\*
\* Per-callback WF because each LNet MD completion is independent --
\* one completing doesn't discharge another's obligation.
\*
\* Two Spec variants:
\*
\* Spec: LNet fairness only. Every posted MD eventually completes.
\*   No environmental events (timeout, net_err, signal) are forced.
\*   Use this for normal-path and wakeup-bug configs (LU-5696).
\*
\* SpecTimeout: LNet fairness + timeout MUST fire. For scenarios
\*   where bulk is lost (BulkLost=TRUE) and only timeout/expiry
\*   can unlink it (LU-7434 BulkLost scenarios).

ReqOutCallbackStep == ReqOutCallback /\ set_woken' = IF InjectBug5696
                                                      THEN set_woken
                                                      ELSE TRUE
ReplyInCallbackStep == ReplyInCallback /\ set_woken' = TRUE
ReplyUnlinkedStep == ReplyUnlinked /\ set_woken' = TRUE
BulkCompleteOkStep == BulkCompleteOk /\ set_woken' = TRUE
BulkCompleteFailStep == BulkCompleteFail /\ set_woken' = TRUE
NetworkErrorStep == NetworkError /\ set_woken' = TRUE
TimeoutFiresStep == TimeoutFires /\ set_woken' = TRUE
SignalIntrStep == SignalIntr /\ set_woken' = TRUE
ExpireReplyStep == ExpireReply /\ set_woken' = TRUE
ExpireBulkStep == ExpireBulk /\ set_woken' = TRUE

\* Base fairness: LNet MD completions + check_set + expiry
LNetFairness ==
        WF_all_vars(CheckSetProgress)
        /\ WF_all_vars(ReqOutCallbackStep)
        /\ WF_all_vars(ReplyInCallbackStep)
        /\ WF_all_vars(ReplyUnlinkedStep)
        /\ WF_all_vars(BulkCompleteOkStep)
        /\ WF_all_vars(BulkCompleteFailStep)
        /\ WF_all_vars(ExpireReplyStep)
        /\ WF_all_vars(ExpireBulkStep)

\* Normal spec: only LNet fairness. Timeout/error/signal may or may
\* not happen -- the system must reach COMPLETE regardless.
Spec == Init /\ [][Next]_all_vars /\ LNetFairness

\* Timeout spec: adds WF on timeout. Use when bulk is lost and only
\* the timeout/expiry path can unlink it.
SpecTimeout == Init /\ [][Next]_all_vars /\ LNetFairness
               /\ WF_all_vars(TimeoutFiresStep)

\* ================================================================
\* Invariants
\* ================================================================

PhaseIsValid == phase \in ValidPhases

\* When COMPLETE, all MDs must be unlinked
CompleteImpliesUnlinked ==
    phase = "COMPLETE" =>
        /\ req_unlinked
        /\ reply_unlinked
        /\ ~bulk_active

\* next_phase is meaningful only in UNREG states
UnregNextPhaseValid ==
    (phase = "UNREG_RPC" \/ phase = "UNREG_BULK"
     \/ phase = "UNREGISTERING") =>
        /\ next_phase /= phase
        /\ next_phase /= "UNDEFINED"

\* LU-11647 / LU-12816: ptl_send_rpc must never be called with bulk
\* already registered. The bulk_double_registered flag is set when:
\*   - LU-11647: RpcResendDoSend fires with bulk_active=TRUE
\*     (InjectBug11647 skips the ~bulk_active guard)
\*   - LU-12816: SendNewPartialFail leaves bd_registered=1 after
\*     partial send failure (InjectBug12816 skips cleanup)
NoBulkDoubleRegister == ~bulk_double_registered

\* ================================================================
\* Novel invariants: derived from C code assertions and
\* implicit expectations in ptlrpc_check_set().
\* ================================================================

\* client.c:2401 LASSERT(!req->rq_receiving_reply) before interpret.
\* When we reach COMPLETE, receiving_reply must be FALSE. The MD must
\* have been consumed by reply_in_callback or unlinked by expiry.
CompleteImpliesNotReceiving ==
    phase = "COMPLETE" => ~receiving_reply

\* You only enter BULK phase after RpcReplyReceived, which requires
\* replied=TRUE. So if phase=BULK, replied must be TRUE.
BulkImpliesReplied ==
    phase = "BULK" => replied

\* When check_set reaches INTERPRET (the completion path), all
\* reply/request MDs should be unlinked (recv_or_unlink must be
\* FALSE). This is enforced by InterpretUnregReply moving to
\* UNREG_RPC first if RecvOrUnlink. So INTERPRET + RecvOrUnlink
\* should only be a transient state, never seen with ~RecvOrUnlink
\* already FALSE. Actually, the code allows entering INTERPRET
\* from err/net_err paths with RecvOrUnlink still TRUE (the
\* interpret label handles unregistration inline). So this is
\* valid -- but when COMPLETE is reached, everything must be done.
\* (CompleteImpliesUnlinked already checks this.)

\* Note: phase=NEW /\ bulk_failed is a valid transient state (after
\* RpcResendFail with prior bulk failure). bulk_failed is cleared
\* by ptlrpc_register_bulk on the next successful ptl_send_rpc.

\* ================================================================
\* Temporal properties
\* ================================================================

\* Request eventually reaches COMPLETE
EventuallyComplete == <>(phase = "COMPLETE")

\* No permanent hang: if not complete, eventually will be
NoHang == [](phase /= "COMPLETE" => <>(phase = "COMPLETE"))

=============================================================================
