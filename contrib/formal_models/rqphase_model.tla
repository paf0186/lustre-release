---------------------------- MODULE rqphase_model ----------------------------
(*
 * PlusCal/TLA+ specification of the PTLRPC request phase machine.
 *
 * Models RQ_PHASE_* transitions in lustre/ptlrpc/client.c:
 *   - 8 phases: NEW, RPC, BULK, INTERPRET, COMPLETE,
 *     UNREG_RPC, UNREG_BULK, UNDEFINED
 *   - ptlrpc_check_set() loop driving phase transitions
 *   - Network callbacks (reply, bulk) setting flags
 *   - Timeout handler initiating async unlink
 *   - Recovery replaying requests (reset to NEW)
 *   - ptlrpc_rqphase_move() nested-unreg prevention
 *
 * Known bug modeled:
 *   LU-7434: Single UNREGISTERING phase could not distinguish
 *            RPC unlink from bulk unlink. Lost bulk with only
 *            RPC unlink pending caused a hang because
 *            expired_set skipped UNREGISTERING and check_set
 *            waited on recv_or_unlink (already done) but never
 *            checked bulk_active.
 *            Set InjectBug7434 = TRUE to reproduce.
 *
 * Source (lustre-release master 47638add78):
 *   lustre/include/lustre_net.h:739-748   enum rq_phase (8 phases)
 *   lustre/include/lustre_net.h:2393-2421 ptlrpc_rqphase_move (nested
 *                                    unreg prevention 2399-2404,
 *                                    imp_unregistering inc/dec)
 *   lustre/include/lustre_net.h:2018-2037 ptlrpc_client_bulk_active
 *   lustre/include/lustre_net.h:2452-2471 ptlrpc_client_recv_or_unlink
 *   lustre/ptlrpc/client.c:1808-1943 ptlrpc_send_new_req (CS_New: NEW ->
 *                                    RPC 1829; import error -> INTERPRET
 *                                    1855-1860; ENOMEM back to NEW
 *                                    1923-1932; other send error sets
 *                                    rq_net_err 1933-1940)
 *   lustre/ptlrpc/client.c:1985-2467 ptlrpc_check_set
 *       2056-2108  UNREG_RPC / UNREG_BULK wait and resume  (CS_Unreg)
 *       2111-2129  rq_net_err && !rq_timedout               (CS_NetErr)
 *       2131-2141  rq_err                                   (CS_Err)
 *       2163-2308  RQ_PHASE_RPC timedout/resend: unregister
 *                  reply 2168, ptl_send_rpc 2286, ENOMEM ->
 *                  NEW 2287-2296, error -> rq_net_err 2303  (CS_RPC,
 *                                                            CS_Resend)
 *       2311-2358  reply wait, ptlrpc_unregister_reply 2337,
 *                  after_reply 2341, -> INTERPRET or BULK   (CS_WaitReply,
 *                  2353-2358                                 CS_GotReply,
 *                                                            CS_AfterReply)
 *       2361-2379  RQ_PHASE_BULK                            (CS_Bulk)
 *       2381-2404  interpret: unregister reply 2388 then    (CS_Interpret)
 *                  bulk 2394, LASSERT(!rq_receiving_reply)
 *                  2401, -> COMPLETE 2404
 *   lustre/ptlrpc/client.c:2478-2557 ptlrpc_expire_one_request
 *                                    (rq_timedout 2488, async unregister
 *                                    of reply and bulk 2509-2510)
 *   lustre/ptlrpc/client.c:2563-2600 ptlrpc_expired_set (TimeoutHandler:
 *                                    only RPC (not waiting/resend) and
 *                                    BULK phases expire, 2580-2583)
 *   lustre/ptlrpc/client.c:2977-3045 ptlrpc_unregister_reply
 *   lustre/ptlrpc/niobuf.c:469-533   ptlrpc_unregister_bulk
 *                                    (mdunlink_iterate_helper 496 runs
 *                                    before the UNREG_BULK move 502)
 *   lustre/ptlrpc/events.c:75-166    reply_in_callback (ReplyCallback)
 *   lustre/ptlrpc/events.c:171-221   client_bulk_callback (BulkCallback)
 *
 * Validated against: lustre-release master 47638add78 (2026-09-06)
 * Validation notes:
 *   - No semantic drift: the UNREG_RPC/UNREG_BULK split, the nested-unreg
 *     guard, the expired_set phase filter and the check_set ordering
 *     above all match the model.  Source refs added (there were none).
 *   - Known abstractions (not drift): CS_NetErr goes straight to
 *     INTERPRET with rq_err; the code only does so when rq_no_resend is
 *     set and otherwise resends (client.c:2111-2129).  CS_Resend
 *     re-registers bulk without the ptlrpc_unregister_bulk call the code
 *     makes first (client.c:2282-2284, LU-11647; covered by
 *     ptlrpc_phases.tla).  reply_in_callback also clears rq_resend on a
 *     real reply (events.c:143), which ReplyCallback does not.
 *   - rqphase_model__LU7434_bug.cfg listed AllThreadsTerminate (never
 *     defined in this module) under PROPERTIES; TLC rejected the config
 *     and the runner misread the non-zero exit as the expected failure.
 *     Removed from the cfg; EventuallyComplete is now genuinely violated
 *     with InjectBug7434 = TRUE.
 *)

EXTENDS Integers, FiniteSets, TLC

CONSTANTS
    InjectBug7434

(* --algorithm PlusCal
variables
    \* Request phase (the core state variable)
    rq_phase = "NEW";
    \* Saved phase to return to after UNREG completes
    rq_next_phase = "UNDEFINED";
    \* Whether request has associated bulk transfer
    rq_has_bulk = FALSE;

    \* Flags set by network callbacks
    rq_replied = FALSE;          \* reply_in_callback sets this
    rq_receiving_reply = FALSE;  \* TRUE while reply buffer posted
    rq_reply_unlinked = TRUE;    \* reply MD unlinked
    rq_bulk_active = FALSE;      \* bulk MD(s) have outstanding refs
    rq_bulk_failed = FALSE;      \* bulk transfer had error
    \* Whether bulk data transfer is "lost" (LU-7434 scenario).
    \* Lost means the natural transfer won't complete.
    \* But LNetMDUnlink (forced unlink) will still clear it.
    bulk_lost = FALSE;
    \* Whether LNetMDUnlink has been called for bulk.
    \* Set by ptlrpc_unregister_bulk (models mdunlink_iterate_helper).
    \* When TRUE + bulk_lost, bulk callback will complete the unlink.
    bulk_unlink_requested = FALSE;

    \* Error/timeout flags
    rq_timedout = FALSE;
    rq_net_err = FALSE;
    rq_err = FALSE;
    rq_resend = FALSE;

    \* imp_unregistering counter
    imp_unregistering = 0;

    \* Track process completion (no recovery process)

define
    ValidPhases == {"NEW", "RPC", "BULK", "INTERPRET", "COMPLETE",
                    "UNREG_RPC", "UNREG_BULK", "UNDEFINED"}

    PhaseIsValid == rq_phase \in ValidPhases

    \* Phase must never be UNDEFINED during normal operation
    PhaseNeverUndefined == rq_phase /= "UNDEFINED"

    \* Cannot nest UNREG phases
    NoNestedUnreg ==
        (rq_phase \in {"UNREG_RPC", "UNREG_BULK"}) =>
            rq_next_phase \notin {"UNREG_RPC", "UNREG_BULK",
                                   "UNDEFINED"}

    \* imp_unregistering must be >= 0
    UnregCounterValid == imp_unregistering >= 0

    \* If phase is UNREG_*, imp_unregistering must be > 0
    UnregCounterConsistent ==
        (rq_phase \in {"UNREG_RPC", "UNREG_BULK"}) =>
            imp_unregistering > 0

    \* When request is COMPLETE, all network activity must be done
    CompleteIsClean ==
        rq_phase = "COMPLETE" =>
            /\ ~rq_receiving_reply
            /\ rq_reply_unlinked
            /\ ~rq_bulk_active

    \* A request must eventually reach COMPLETE (liveness)
    EventuallyComplete == <>(rq_phase = "COMPLETE")

    \* UNREG phases must eventually resolve
    UnregEventuallyResolves ==
        [](rq_phase \in {"UNREG_RPC", "UNREG_BULK"} =>
            <>(rq_phase \notin {"UNREG_RPC", "UNREG_BULK"}))
end define;

\* ================================================================
\* CheckSetProcess: models ptlrpc_check_set() for one request.
\* Loops until COMPLETE.
\* ================================================================
fair process CheckSetProcess = "check_set"
begin
CS_Start:
    if rq_phase = "COMPLETE" then
        goto Done;
    end if;

\* ---- Handle NEW phase: ptlrpc_send_new_req ----
CS_New:
    if rq_phase = "NEW" then
        either
            \* Normal send: NEW -> RPC
            \* has_bulk is decided on first send and stays fixed
            if ~rq_replied /\ ~rq_has_bulk then
                \* First send: nondeterministically pick bulk
                either
                    rq_has_bulk := TRUE ||
                    rq_bulk_active := TRUE;
                or
                    skip; \* no bulk
                end either;
            elsif rq_has_bulk then
                \* Re-send: re-register bulk
                rq_bulk_active := TRUE ||
                rq_bulk_failed := FALSE ||
                bulk_lost := FALSE ||
                bulk_unlink_requested := FALSE;
            end if;
CS_NewSend:
            rq_phase := "RPC" ||
            rq_receiving_reply := TRUE ||
            rq_reply_unlinked := FALSE ||
            rq_replied := FALSE;
        or
            \* Import error: NEW -> INTERPRET
            rq_phase := "INTERPRET";
        or
            \* ENOMEM: stay in NEW
            skip;
        end either;
    end if;

\* ---- Handle UNREG phases ----
CS_Unreg:
    if rq_phase = "UNREG_RPC" then
        \* UNREG_RPC checks reply unlink (recv_or_unlink)
        if rq_reply_unlinked /\ ~rq_receiving_reply then
            imp_unregistering := imp_unregistering - 1 ||
            rq_phase := rq_next_phase;
        else
            goto CS_Start;
        end if;
    elsif rq_phase = "UNREG_BULK" then
        \* UNREG_BULK checks bulk active
        if ~rq_bulk_active then
            imp_unregistering := imp_unregistering - 1 ||
            rq_phase := rq_next_phase;
        else
            goto CS_Start;
        end if;
    end if;

CS_CheckInterpret1:
    if rq_phase = "INTERPRET" then
        goto CS_Interpret;
    end if;

\* ---- Handle net_err + timeout ----
CS_NetErr:
    if rq_phase = "RPC" /\ rq_net_err /\ ~rq_timedout then
        rq_timedout := TRUE ||
        rq_phase := "INTERPRET" ||
        rq_err := TRUE;
        goto CS_Interpret;
    end if;

\* ---- Handle err flag ----
CS_Err:
    if rq_phase = "RPC" /\ rq_err then
        if ~rq_reply_unlinked \/ rq_receiving_reply then
            rq_next_phase := rq_phase ||
            imp_unregistering := imp_unregistering + 1 ||
            rq_phase := "UNREG_RPC";
            goto CS_Start;
        end if;
CS_ErrInterpret:
        rq_phase := "INTERPRET";
        goto CS_Interpret;
    end if;

\* ---- Handle RPC phase: normal reply processing ----
CS_RPC:
    if rq_phase = "RPC" then
        if rq_timedout \/ rq_resend then
            if ~rq_reply_unlinked \/ rq_receiving_reply then
                if rq_phase /= "UNREG_RPC" /\ rq_phase /= "UNREG_BULK" then
                    rq_next_phase := rq_phase ||
                    imp_unregistering := imp_unregistering + 1 ||
                    rq_phase := "UNREG_RPC";
                end if;
                goto CS_Start;
            end if;
CS_Resend:
            either
                \* Resend succeeds
                rq_timedout := FALSE ||
                rq_resend := FALSE ||
                rq_net_err := FALSE ||
                rq_receiving_reply := TRUE ||
                rq_reply_unlinked := FALSE;
                if rq_has_bulk then
                    rq_bulk_active := TRUE ||
                    rq_bulk_failed := FALSE ||
                    bulk_lost := FALSE ||
                    bulk_unlink_requested := FALSE;
                end if;
            or
                \* ENOMEM: back to NEW, bulk deactivated
                rq_phase := "NEW" ||
                rq_bulk_active := FALSE;
            or
                \* Other send error
                rq_net_err := TRUE;
            end either;
            goto CS_Start;
        end if;

CS_WaitReply:
        \* Waiting for reply
        if rq_receiving_reply \/ ~rq_replied then
            goto CS_Start;
        end if;

CS_GotReply:
        \* Reply received. Unregister reply buffer.
        if ~rq_reply_unlinked then
            if rq_phase /= "UNREG_RPC" /\ rq_phase /= "UNREG_BULK" then
                rq_next_phase := rq_phase ||
                imp_unregistering := imp_unregistering + 1 ||
                rq_phase := "UNREG_RPC";
            end if;
            goto CS_Start;
        end if;

CS_AfterReply:
        \* after_reply processing
        either
            if ~rq_has_bulk then
                rq_phase := "INTERPRET";
                goto CS_Interpret;
            end if;
CS_ToBulk:
            rq_phase := "BULK";
        or
            \* after_reply triggers resend
            rq_resend := TRUE;
            goto CS_Start;
        end either;
    end if;

\* ---- Handle BULK phase ----
CS_Bulk:
    if rq_phase = "BULK" /\ rq_bulk_active then
        goto CS_Start;
    end if;
CS_BulkDone:
    if rq_phase = "BULK" then
        rq_err := rq_err \/ rq_bulk_failed;
        rq_phase := "INTERPRET";
    end if;

\* ---- Handle INTERPRET phase ----
CS_Interpret:
    if rq_phase = "INTERPRET" then
        \* Must unregister reply
        if ~rq_reply_unlinked \/ rq_receiving_reply then
            if rq_phase /= "UNREG_RPC" /\ rq_phase /= "UNREG_BULK" then
                rq_next_phase := "INTERPRET" ||
                imp_unregistering := imp_unregistering + 1 ||
                rq_phase := "UNREG_RPC";
            end if;
            goto CS_Start;
        end if;
CS_InterpretBulk:
        \* Must unregister bulk
        if rq_has_bulk /\ rq_bulk_active then
            if InjectBug7434 then
                \* BUG: uses UNREG_RPC (old single UNREGISTERING)
                \* for bulk unlink too. check_set will check
                \* recv_or_unlink (already done!) and immediately
                \* return to INTERPRET, leaving bulk active.
                \* Note: LNetMDUnlink IS called (unregister_bulk
                \* calls mdunlink before the phase move)
                bulk_unlink_requested := TRUE ||
                rq_next_phase := "INTERPRET" ||
                imp_unregistering := imp_unregistering + 1 ||
                rq_phase := "UNREG_RPC";
            else
                \* FIXED: uses UNREG_BULK for bulk unlink
                bulk_unlink_requested := TRUE ||
                rq_next_phase := "INTERPRET" ||
                imp_unregistering := imp_unregistering + 1 ||
                rq_phase := "UNREG_BULK";
            end if;
            goto CS_Start;
        end if;
CS_Complete:
        \* All clean: interpret and complete
        rq_phase := "COMPLETE";
        goto Done;
    end if;

CS_Loop:
    goto CS_Start;
end process;

\* ================================================================
\* ReplyCallback: reply_in_callback (events.c)
\* Loops: fires whenever reply buffer is posted. LNet guarantees
\* eventual delivery of unlink event for any posted MD.
\* ================================================================
fair process ReplyCallback = "reply_cb"
begin
RC_Wait:
    if rq_phase = "COMPLETE" then
        goto Done;
    end if;
RC_Fire:
    if rq_receiving_reply then
        either
            \* Normal reply received + immediate unlink
            rq_replied := TRUE ||
            rq_receiving_reply := FALSE ||
            rq_reply_unlinked := TRUE;
        or
            \* Reply received, unlink deferred
            rq_replied := TRUE ||
            rq_receiving_reply := FALSE;
        or
            \* Unlink event only (timeout-initiated unlink)
            rq_reply_unlinked := TRUE ||
            rq_receiving_reply := FALSE;
        end either;
    elsif ~rq_reply_unlinked then
        \* Deferred unlink event: LNet completes MD unlink
        \* after reply was already received
        rq_reply_unlinked := TRUE;
    end if;
    goto RC_Wait;
end process;

\* ================================================================
\* BulkCallback: client_bulk_callback (events.c)
\* Loops: fires whenever bulk is active, UNLESS bulk is "lost".
\* Lost bulk = callback never fires (the LU-7434 scenario).
\* ================================================================
fair process BulkCallback = "bulk_cb"
begin
BC_Wait:
    if rq_phase = "COMPLETE" then
        goto Done;
    end if;
BC_Fire:
    if rq_bulk_active then
        if bulk_lost then
            \* Bulk data transfer lost but LNetMDUnlink was called:
            \* forced unlink completes, clearing bulk_active
            if bulk_unlink_requested then
                rq_bulk_active := FALSE ||
                rq_net_err := TRUE;
            end if;
            \* If unlink not requested, stay stuck (the bug!)
        else
            either
                \* Bulk completes successfully
                rq_bulk_active := FALSE;
            or
                \* Bulk fails
                rq_bulk_active := FALSE ||
                rq_bulk_failed := TRUE ||
                rq_net_err := TRUE;
            or
                \* Bulk gets lost (only happens once)
                bulk_lost := TRUE;
            end either;
        end if;
    end if;
    goto BC_Wait;
end process;

\* ================================================================
\* TimeoutHandler: ptlrpc_expired_set + ptlrpc_expire_one_request
\* Loops: fires when request is in RPC/BULK phase.
\* ================================================================
fair process TimeoutHandler = "timeout"
begin
TH_Wait:
    if rq_phase = "COMPLETE" then
        goto Done;
    end if;
TH_Check:
    if rq_phase = "RPC" \/ rq_phase = "BULK" then
        rq_timedout := TRUE;
TH_UnregReply:
        \* ptlrpc_unregister_reply (async)
        if ~rq_reply_unlinked \/ rq_receiving_reply then
            if rq_phase /= "UNREG_RPC" /\ rq_phase /= "UNREG_BULK" then
                rq_next_phase := rq_phase ||
                imp_unregistering := imp_unregistering + 1 ||
                rq_phase := "UNREG_RPC";
            end if;
        end if;
TH_UnregBulk:
        \* ptlrpc_unregister_bulk (async)
        \* mdunlink_iterate_helper is called BEFORE phase move
        if rq_has_bulk /\ rq_bulk_active then
            bulk_unlink_requested := TRUE;
            if InjectBug7434 then
                \* BUG: tries UNREG_RPC (old UNREGISTERING) but
                \* we're already in UNREG_RPC from reply above.
                \* No-op due to nested unreg prevention!
                if rq_phase /= "UNREG_RPC" /\ rq_phase /= "UNREG_BULK" then
                    rq_next_phase := rq_phase ||
                    imp_unregistering := imp_unregistering + 1 ||
                    rq_phase := "UNREG_RPC";
                end if;
            else
                \* FIXED: Use UNREG_BULK if not already in UNREG.
                if rq_phase /= "UNREG_RPC" /\ rq_phase /= "UNREG_BULK" then
                    rq_next_phase := rq_phase ||
                    imp_unregistering := imp_unregistering + 1 ||
                    rq_phase := "UNREG_BULK";
                end if;
            end if;
        end if;
    end if;
TH_Loop:
    goto TH_Wait;
end process;

\* Recovery is not modeled here -- it requires import-level
\* locking that would obscure the LU-7434 phase machine bug.
\* Recovery resets the phase to NEW, which is well-understood.
\* The interesting bugs are in the UNREG phase handling.

end algorithm; *)

\* BEGIN TRANSLATION
VARIABLES rq_phase, rq_next_phase, rq_has_bulk, rq_replied,
          rq_receiving_reply, rq_reply_unlinked, rq_bulk_active,
          rq_bulk_failed, bulk_lost, bulk_unlink_requested, rq_timedout,
          rq_net_err, rq_err, rq_resend, imp_unregistering, pc

(* define statement *)
ValidPhases == {"NEW", "RPC", "BULK", "INTERPRET", "COMPLETE",
                "UNREG_RPC", "UNREG_BULK", "UNDEFINED"}

PhaseIsValid == rq_phase \in ValidPhases


PhaseNeverUndefined == rq_phase /= "UNDEFINED"


NoNestedUnreg ==
    (rq_phase \in {"UNREG_RPC", "UNREG_BULK"}) =>
        rq_next_phase \notin {"UNREG_RPC", "UNREG_BULK",
                               "UNDEFINED"}


UnregCounterValid == imp_unregistering >= 0


UnregCounterConsistent ==
    (rq_phase \in {"UNREG_RPC", "UNREG_BULK"}) =>
        imp_unregistering > 0


CompleteIsClean ==
    rq_phase = "COMPLETE" =>
        /\ ~rq_receiving_reply
        /\ rq_reply_unlinked
        /\ ~rq_bulk_active


EventuallyComplete == <>(rq_phase = "COMPLETE")


UnregEventuallyResolves ==
    [](rq_phase \in {"UNREG_RPC", "UNREG_BULK"} =>
        <>(rq_phase \notin {"UNREG_RPC", "UNREG_BULK"}))


vars == << rq_phase, rq_next_phase, rq_has_bulk, rq_replied,
           rq_receiving_reply, rq_reply_unlinked, rq_bulk_active,
           rq_bulk_failed, bulk_lost, bulk_unlink_requested, rq_timedout,
           rq_net_err, rq_err, rq_resend, imp_unregistering, pc >>

ProcSet == {"check_set"} \cup {"reply_cb"} \cup {"bulk_cb"} \cup {"timeout"}

Init == (* Global variables *)
        /\ rq_phase = "NEW"
        /\ rq_next_phase = "UNDEFINED"
        /\ rq_has_bulk = FALSE
        /\ rq_replied = FALSE
        /\ rq_receiving_reply = FALSE
        /\ rq_reply_unlinked = TRUE
        /\ rq_bulk_active = FALSE
        /\ rq_bulk_failed = FALSE
        /\ bulk_lost = FALSE
        /\ bulk_unlink_requested = FALSE
        /\ rq_timedout = FALSE
        /\ rq_net_err = FALSE
        /\ rq_err = FALSE
        /\ rq_resend = FALSE
        /\ imp_unregistering = 0
        /\ pc = [self \in ProcSet |-> CASE self = "check_set" -> "CS_Start"
                                        [] self = "reply_cb" -> "RC_Wait"
                                        [] self = "bulk_cb" -> "BC_Wait"
                                        [] self = "timeout" -> "TH_Wait"]

CS_Start == /\ pc["check_set"] = "CS_Start"
            /\ IF rq_phase = "COMPLETE"
                  THEN /\ pc' = [pc EXCEPT !["check_set"] = "Done"]
                  ELSE /\ pc' = [pc EXCEPT !["check_set"] = "CS_New"]
            /\ UNCHANGED << rq_phase, rq_next_phase, rq_has_bulk, rq_replied,
                            rq_receiving_reply, rq_reply_unlinked,
                            rq_bulk_active, rq_bulk_failed, bulk_lost,
                            bulk_unlink_requested, rq_timedout, rq_net_err,
                            rq_err, rq_resend, imp_unregistering >>

CS_New == /\ pc["check_set"] = "CS_New"
          /\ IF rq_phase = "NEW"
                THEN /\ \/ /\ IF ~rq_replied /\ ~rq_has_bulk
                                 THEN /\ \/ /\ /\ rq_bulk_active' = TRUE
                                               /\ rq_has_bulk' = TRUE
                                         \/ /\ TRUE
                                            /\ UNCHANGED <<rq_has_bulk, rq_bulk_active>>
                                      /\ UNCHANGED << rq_bulk_failed,
                                                      bulk_lost,
                                                      bulk_unlink_requested >>
                                 ELSE /\ IF rq_has_bulk
                                            THEN /\ /\ bulk_lost' = FALSE
                                                    /\ bulk_unlink_requested' = FALSE
                                                    /\ rq_bulk_active' = TRUE
                                                    /\ rq_bulk_failed' = FALSE
                                            ELSE /\ TRUE
                                                 /\ UNCHANGED << rq_bulk_active,
                                                                 rq_bulk_failed,
                                                                 bulk_lost,
                                                                 bulk_unlink_requested >>
                                      /\ UNCHANGED rq_has_bulk
                           /\ pc' = [pc EXCEPT !["check_set"] = "CS_NewSend"]
                           /\ UNCHANGED rq_phase
                        \/ /\ rq_phase' = "INTERPRET"
                           /\ pc' = [pc EXCEPT !["check_set"] = "CS_Unreg"]
                           /\ UNCHANGED <<rq_has_bulk, rq_bulk_active, rq_bulk_failed, bulk_lost, bulk_unlink_requested>>
                        \/ /\ TRUE
                           /\ pc' = [pc EXCEPT !["check_set"] = "CS_Unreg"]
                           /\ UNCHANGED <<rq_phase, rq_has_bulk, rq_bulk_active, rq_bulk_failed, bulk_lost, bulk_unlink_requested>>
                ELSE /\ pc' = [pc EXCEPT !["check_set"] = "CS_Unreg"]
                     /\ UNCHANGED << rq_phase, rq_has_bulk, rq_bulk_active,
                                     rq_bulk_failed, bulk_lost,
                                     bulk_unlink_requested >>
          /\ UNCHANGED << rq_next_phase, rq_replied, rq_receiving_reply,
                          rq_reply_unlinked, rq_timedout, rq_net_err, rq_err,
                          rq_resend, imp_unregistering >>

CS_NewSend == /\ pc["check_set"] = "CS_NewSend"
              /\ /\ rq_phase' = "RPC"
                 /\ rq_receiving_reply' = TRUE
                 /\ rq_replied' = FALSE
                 /\ rq_reply_unlinked' = FALSE
              /\ pc' = [pc EXCEPT !["check_set"] = "CS_Unreg"]
              /\ UNCHANGED << rq_next_phase, rq_has_bulk, rq_bulk_active,
                              rq_bulk_failed, bulk_lost, bulk_unlink_requested,
                              rq_timedout, rq_net_err, rq_err, rq_resend,
                              imp_unregistering >>

CS_Unreg == /\ pc["check_set"] = "CS_Unreg"
            /\ IF rq_phase = "UNREG_RPC"
                  THEN /\ IF rq_reply_unlinked /\ ~rq_receiving_reply
                             THEN /\ /\ imp_unregistering' = imp_unregistering - 1
                                     /\ rq_phase' = rq_next_phase
                                  /\ pc' = [pc EXCEPT !["check_set"] = "CS_CheckInterpret1"]
                             ELSE /\ pc' = [pc EXCEPT !["check_set"] = "CS_Start"]
                                  /\ UNCHANGED << rq_phase, imp_unregistering >>
                  ELSE /\ IF rq_phase = "UNREG_BULK"
                             THEN /\ IF ~rq_bulk_active
                                        THEN /\ /\ imp_unregistering' = imp_unregistering - 1
                                                /\ rq_phase' = rq_next_phase
                                             /\ pc' = [pc EXCEPT !["check_set"] = "CS_CheckInterpret1"]
                                        ELSE /\ pc' = [pc EXCEPT !["check_set"] = "CS_Start"]
                                             /\ UNCHANGED << rq_phase,
                                                             imp_unregistering >>
                             ELSE /\ pc' = [pc EXCEPT !["check_set"] = "CS_CheckInterpret1"]
                                  /\ UNCHANGED << rq_phase, imp_unregistering >>
            /\ UNCHANGED << rq_next_phase, rq_has_bulk, rq_replied,
                            rq_receiving_reply, rq_reply_unlinked,
                            rq_bulk_active, rq_bulk_failed, bulk_lost,
                            bulk_unlink_requested, rq_timedout, rq_net_err,
                            rq_err, rq_resend >>

CS_CheckInterpret1 == /\ pc["check_set"] = "CS_CheckInterpret1"
                      /\ IF rq_phase = "INTERPRET"
                            THEN /\ pc' = [pc EXCEPT !["check_set"] = "CS_Interpret"]
                            ELSE /\ pc' = [pc EXCEPT !["check_set"] = "CS_NetErr"]
                      /\ UNCHANGED << rq_phase, rq_next_phase, rq_has_bulk,
                                      rq_replied, rq_receiving_reply,
                                      rq_reply_unlinked, rq_bulk_active,
                                      rq_bulk_failed, bulk_lost,
                                      bulk_unlink_requested, rq_timedout,
                                      rq_net_err, rq_err, rq_resend,
                                      imp_unregistering >>

CS_NetErr == /\ pc["check_set"] = "CS_NetErr"
             /\ IF rq_phase = "RPC" /\ rq_net_err /\ ~rq_timedout
                   THEN /\ /\ rq_err' = TRUE
                           /\ rq_phase' = "INTERPRET"
                           /\ rq_timedout' = TRUE
                        /\ pc' = [pc EXCEPT !["check_set"] = "CS_Interpret"]
                   ELSE /\ pc' = [pc EXCEPT !["check_set"] = "CS_Err"]
                        /\ UNCHANGED << rq_phase, rq_timedout, rq_err >>
             /\ UNCHANGED << rq_next_phase, rq_has_bulk, rq_replied,
                             rq_receiving_reply, rq_reply_unlinked,
                             rq_bulk_active, rq_bulk_failed, bulk_lost,
                             bulk_unlink_requested, rq_net_err, rq_resend,
                             imp_unregistering >>

CS_Err == /\ pc["check_set"] = "CS_Err"
          /\ IF rq_phase = "RPC" /\ rq_err
                THEN /\ IF ~rq_reply_unlinked \/ rq_receiving_reply
                           THEN /\ /\ imp_unregistering' = imp_unregistering + 1
                                   /\ rq_next_phase' = rq_phase
                                   /\ rq_phase' = "UNREG_RPC"
                                /\ pc' = [pc EXCEPT !["check_set"] = "CS_Start"]
                           ELSE /\ pc' = [pc EXCEPT !["check_set"] = "CS_ErrInterpret"]
                                /\ UNCHANGED << rq_phase, rq_next_phase,
                                                imp_unregistering >>
                ELSE /\ pc' = [pc EXCEPT !["check_set"] = "CS_RPC"]
                     /\ UNCHANGED << rq_phase, rq_next_phase,
                                     imp_unregistering >>
          /\ UNCHANGED << rq_has_bulk, rq_replied, rq_receiving_reply,
                          rq_reply_unlinked, rq_bulk_active, rq_bulk_failed,
                          bulk_lost, bulk_unlink_requested, rq_timedout,
                          rq_net_err, rq_err, rq_resend >>

CS_ErrInterpret == /\ pc["check_set"] = "CS_ErrInterpret"
                   /\ rq_phase' = "INTERPRET"
                   /\ pc' = [pc EXCEPT !["check_set"] = "CS_Interpret"]
                   /\ UNCHANGED << rq_next_phase, rq_has_bulk, rq_replied,
                                   rq_receiving_reply, rq_reply_unlinked,
                                   rq_bulk_active, rq_bulk_failed, bulk_lost,
                                   bulk_unlink_requested, rq_timedout,
                                   rq_net_err, rq_err, rq_resend,
                                   imp_unregistering >>

CS_RPC == /\ pc["check_set"] = "CS_RPC"
          /\ IF rq_phase = "RPC"
                THEN /\ IF rq_timedout \/ rq_resend
                           THEN /\ IF ~rq_reply_unlinked \/ rq_receiving_reply
                                      THEN /\ IF rq_phase /= "UNREG_RPC" /\ rq_phase /= "UNREG_BULK"
                                                 THEN /\ /\ imp_unregistering' = imp_unregistering + 1
                                                         /\ rq_next_phase' = rq_phase
                                                         /\ rq_phase' = "UNREG_RPC"
                                                 ELSE /\ TRUE
                                                      /\ UNCHANGED << rq_phase,
                                                                      rq_next_phase,
                                                                      imp_unregistering >>
                                           /\ pc' = [pc EXCEPT !["check_set"] = "CS_Start"]
                                      ELSE /\ pc' = [pc EXCEPT !["check_set"] = "CS_Resend"]
                                           /\ UNCHANGED << rq_phase,
                                                           rq_next_phase,
                                                           imp_unregistering >>
                           ELSE /\ pc' = [pc EXCEPT !["check_set"] = "CS_WaitReply"]
                                /\ UNCHANGED << rq_phase, rq_next_phase,
                                                imp_unregistering >>
                ELSE /\ pc' = [pc EXCEPT !["check_set"] = "CS_Bulk"]
                     /\ UNCHANGED << rq_phase, rq_next_phase,
                                     imp_unregistering >>
          /\ UNCHANGED << rq_has_bulk, rq_replied, rq_receiving_reply,
                          rq_reply_unlinked, rq_bulk_active, rq_bulk_failed,
                          bulk_lost, bulk_unlink_requested, rq_timedout,
                          rq_net_err, rq_err, rq_resend >>

CS_WaitReply == /\ pc["check_set"] = "CS_WaitReply"
                /\ IF rq_receiving_reply \/ ~rq_replied
                      THEN /\ pc' = [pc EXCEPT !["check_set"] = "CS_Start"]
                      ELSE /\ pc' = [pc EXCEPT !["check_set"] = "CS_GotReply"]
                /\ UNCHANGED << rq_phase, rq_next_phase, rq_has_bulk,
                                rq_replied, rq_receiving_reply,
                                rq_reply_unlinked, rq_bulk_active,
                                rq_bulk_failed, bulk_lost,
                                bulk_unlink_requested, rq_timedout, rq_net_err,
                                rq_err, rq_resend, imp_unregistering >>

CS_GotReply == /\ pc["check_set"] = "CS_GotReply"
               /\ IF ~rq_reply_unlinked
                     THEN /\ IF rq_phase /= "UNREG_RPC" /\ rq_phase /= "UNREG_BULK"
                                THEN /\ /\ imp_unregistering' = imp_unregistering + 1
                                        /\ rq_next_phase' = rq_phase
                                        /\ rq_phase' = "UNREG_RPC"
                                ELSE /\ TRUE
                                     /\ UNCHANGED << rq_phase, rq_next_phase,
                                                     imp_unregistering >>
                          /\ pc' = [pc EXCEPT !["check_set"] = "CS_Start"]
                     ELSE /\ pc' = [pc EXCEPT !["check_set"] = "CS_AfterReply"]
                          /\ UNCHANGED << rq_phase, rq_next_phase,
                                          imp_unregistering >>
               /\ UNCHANGED << rq_has_bulk, rq_replied, rq_receiving_reply,
                               rq_reply_unlinked, rq_bulk_active,
                               rq_bulk_failed, bulk_lost,
                               bulk_unlink_requested, rq_timedout, rq_net_err,
                               rq_err, rq_resend >>

CS_AfterReply == /\ pc["check_set"] = "CS_AfterReply"
                 /\ \/ /\ IF ~rq_has_bulk
                             THEN /\ rq_phase' = "INTERPRET"
                                  /\ pc' = [pc EXCEPT !["check_set"] = "CS_Interpret"]
                             ELSE /\ pc' = [pc EXCEPT !["check_set"] = "CS_ToBulk"]
                                  /\ UNCHANGED rq_phase
                       /\ UNCHANGED rq_resend
                    \/ /\ rq_resend' = TRUE
                       /\ pc' = [pc EXCEPT !["check_set"] = "CS_Start"]
                       /\ UNCHANGED rq_phase
                 /\ UNCHANGED << rq_next_phase, rq_has_bulk, rq_replied,
                                 rq_receiving_reply, rq_reply_unlinked,
                                 rq_bulk_active, rq_bulk_failed, bulk_lost,
                                 bulk_unlink_requested, rq_timedout,
                                 rq_net_err, rq_err, imp_unregistering >>

CS_ToBulk == /\ pc["check_set"] = "CS_ToBulk"
             /\ rq_phase' = "BULK"
             /\ pc' = [pc EXCEPT !["check_set"] = "CS_Bulk"]
             /\ UNCHANGED << rq_next_phase, rq_has_bulk, rq_replied,
                             rq_receiving_reply, rq_reply_unlinked,
                             rq_bulk_active, rq_bulk_failed, bulk_lost,
                             bulk_unlink_requested, rq_timedout, rq_net_err,
                             rq_err, rq_resend, imp_unregistering >>

CS_Resend == /\ pc["check_set"] = "CS_Resend"
             /\ \/ /\ /\ rq_net_err' = FALSE
                      /\ rq_receiving_reply' = TRUE
                      /\ rq_reply_unlinked' = FALSE
                      /\ rq_resend' = FALSE
                      /\ rq_timedout' = FALSE
                   /\ IF rq_has_bulk
                         THEN /\ /\ bulk_lost' = FALSE
                                 /\ bulk_unlink_requested' = FALSE
                                 /\ rq_bulk_active' = TRUE
                                 /\ rq_bulk_failed' = FALSE
                         ELSE /\ TRUE
                              /\ UNCHANGED << rq_bulk_active, rq_bulk_failed,
                                              bulk_lost, bulk_unlink_requested >>
                   /\ UNCHANGED rq_phase
                \/ /\ /\ rq_bulk_active' = FALSE
                      /\ rq_phase' = "NEW"
                   /\ UNCHANGED <<rq_receiving_reply, rq_reply_unlinked, rq_bulk_failed, bulk_lost, bulk_unlink_requested, rq_timedout, rq_net_err, rq_resend>>
                \/ /\ rq_net_err' = TRUE
                   /\ UNCHANGED <<rq_phase, rq_receiving_reply, rq_reply_unlinked, rq_bulk_active, rq_bulk_failed, bulk_lost, bulk_unlink_requested, rq_timedout, rq_resend>>
             /\ pc' = [pc EXCEPT !["check_set"] = "CS_Start"]
             /\ UNCHANGED << rq_next_phase, rq_has_bulk, rq_replied, rq_err,
                             imp_unregistering >>

CS_Bulk == /\ pc["check_set"] = "CS_Bulk"
           /\ IF rq_phase = "BULK" /\ rq_bulk_active
                 THEN /\ pc' = [pc EXCEPT !["check_set"] = "CS_Start"]
                 ELSE /\ pc' = [pc EXCEPT !["check_set"] = "CS_BulkDone"]
           /\ UNCHANGED << rq_phase, rq_next_phase, rq_has_bulk, rq_replied,
                           rq_receiving_reply, rq_reply_unlinked,
                           rq_bulk_active, rq_bulk_failed, bulk_lost,
                           bulk_unlink_requested, rq_timedout, rq_net_err,
                           rq_err, rq_resend, imp_unregistering >>

CS_BulkDone == /\ pc["check_set"] = "CS_BulkDone"
               /\ IF rq_phase = "BULK"
                     THEN /\ rq_err' = (rq_err \/ rq_bulk_failed)
                          /\ rq_phase' = "INTERPRET"
                     ELSE /\ TRUE
                          /\ UNCHANGED << rq_phase, rq_err >>
               /\ pc' = [pc EXCEPT !["check_set"] = "CS_Interpret"]
               /\ UNCHANGED << rq_next_phase, rq_has_bulk, rq_replied,
                               rq_receiving_reply, rq_reply_unlinked,
                               rq_bulk_active, rq_bulk_failed, bulk_lost,
                               bulk_unlink_requested, rq_timedout, rq_net_err,
                               rq_resend, imp_unregistering >>

CS_Interpret == /\ pc["check_set"] = "CS_Interpret"
                /\ IF rq_phase = "INTERPRET"
                      THEN /\ IF ~rq_reply_unlinked \/ rq_receiving_reply
                                 THEN /\ IF rq_phase /= "UNREG_RPC" /\ rq_phase /= "UNREG_BULK"
                                            THEN /\ /\ imp_unregistering' = imp_unregistering + 1
                                                    /\ rq_next_phase' = "INTERPRET"
                                                    /\ rq_phase' = "UNREG_RPC"
                                            ELSE /\ TRUE
                                                 /\ UNCHANGED << rq_phase,
                                                                 rq_next_phase,
                                                                 imp_unregistering >>
                                      /\ pc' = [pc EXCEPT !["check_set"] = "CS_Start"]
                                 ELSE /\ pc' = [pc EXCEPT !["check_set"] = "CS_InterpretBulk"]
                                      /\ UNCHANGED << rq_phase, rq_next_phase,
                                                      imp_unregistering >>
                      ELSE /\ pc' = [pc EXCEPT !["check_set"] = "CS_Loop"]
                           /\ UNCHANGED << rq_phase, rq_next_phase,
                                           imp_unregistering >>
                /\ UNCHANGED << rq_has_bulk, rq_replied, rq_receiving_reply,
                                rq_reply_unlinked, rq_bulk_active,
                                rq_bulk_failed, bulk_lost,
                                bulk_unlink_requested, rq_timedout, rq_net_err,
                                rq_err, rq_resend >>

CS_InterpretBulk == /\ pc["check_set"] = "CS_InterpretBulk"
                    /\ IF rq_has_bulk /\ rq_bulk_active
                          THEN /\ IF InjectBug7434
                                     THEN /\ /\ bulk_unlink_requested' = TRUE
                                             /\ imp_unregistering' = imp_unregistering + 1
                                             /\ rq_next_phase' = "INTERPRET"
                                             /\ rq_phase' = "UNREG_RPC"
                                     ELSE /\ /\ bulk_unlink_requested' = TRUE
                                             /\ imp_unregistering' = imp_unregistering + 1
                                             /\ rq_next_phase' = "INTERPRET"
                                             /\ rq_phase' = "UNREG_BULK"
                               /\ pc' = [pc EXCEPT !["check_set"] = "CS_Start"]
                          ELSE /\ pc' = [pc EXCEPT !["check_set"] = "CS_Complete"]
                               /\ UNCHANGED << rq_phase, rq_next_phase,
                                               bulk_unlink_requested,
                                               imp_unregistering >>
                    /\ UNCHANGED << rq_has_bulk, rq_replied,
                                    rq_receiving_reply, rq_reply_unlinked,
                                    rq_bulk_active, rq_bulk_failed, bulk_lost,
                                    rq_timedout, rq_net_err, rq_err, rq_resend >>

CS_Complete == /\ pc["check_set"] = "CS_Complete"
               /\ rq_phase' = "COMPLETE"
               /\ pc' = [pc EXCEPT !["check_set"] = "Done"]
               /\ UNCHANGED << rq_next_phase, rq_has_bulk, rq_replied,
                               rq_receiving_reply, rq_reply_unlinked,
                               rq_bulk_active, rq_bulk_failed, bulk_lost,
                               bulk_unlink_requested, rq_timedout, rq_net_err,
                               rq_err, rq_resend, imp_unregistering >>

CS_Loop == /\ pc["check_set"] = "CS_Loop"
           /\ pc' = [pc EXCEPT !["check_set"] = "CS_Start"]
           /\ UNCHANGED << rq_phase, rq_next_phase, rq_has_bulk, rq_replied,
                           rq_receiving_reply, rq_reply_unlinked,
                           rq_bulk_active, rq_bulk_failed, bulk_lost,
                           bulk_unlink_requested, rq_timedout, rq_net_err,
                           rq_err, rq_resend, imp_unregistering >>

CheckSetProcess == CS_Start \/ CS_New \/ CS_NewSend \/ CS_Unreg
                      \/ CS_CheckInterpret1 \/ CS_NetErr \/ CS_Err
                      \/ CS_ErrInterpret \/ CS_RPC \/ CS_WaitReply
                      \/ CS_GotReply \/ CS_AfterReply \/ CS_ToBulk
                      \/ CS_Resend \/ CS_Bulk \/ CS_BulkDone
                      \/ CS_Interpret \/ CS_InterpretBulk \/ CS_Complete
                      \/ CS_Loop

RC_Wait == /\ pc["reply_cb"] = "RC_Wait"
           /\ IF rq_phase = "COMPLETE"
                 THEN /\ pc' = [pc EXCEPT !["reply_cb"] = "Done"]
                 ELSE /\ pc' = [pc EXCEPT !["reply_cb"] = "RC_Fire"]
           /\ UNCHANGED << rq_phase, rq_next_phase, rq_has_bulk, rq_replied,
                           rq_receiving_reply, rq_reply_unlinked,
                           rq_bulk_active, rq_bulk_failed, bulk_lost,
                           bulk_unlink_requested, rq_timedout, rq_net_err,
                           rq_err, rq_resend, imp_unregistering >>

RC_Fire == /\ pc["reply_cb"] = "RC_Fire"
           /\ IF rq_receiving_reply
                 THEN /\ \/ /\ /\ rq_receiving_reply' = FALSE
                               /\ rq_replied' = TRUE
                               /\ rq_reply_unlinked' = TRUE
                         \/ /\ /\ rq_receiving_reply' = FALSE
                               /\ rq_replied' = TRUE
                            /\ UNCHANGED rq_reply_unlinked
                         \/ /\ /\ rq_receiving_reply' = FALSE
                               /\ rq_reply_unlinked' = TRUE
                            /\ UNCHANGED rq_replied
                 ELSE /\ IF ~rq_reply_unlinked
                            THEN /\ rq_reply_unlinked' = TRUE
                            ELSE /\ TRUE
                                 /\ UNCHANGED rq_reply_unlinked
                      /\ UNCHANGED << rq_replied, rq_receiving_reply >>
           /\ pc' = [pc EXCEPT !["reply_cb"] = "RC_Wait"]
           /\ UNCHANGED << rq_phase, rq_next_phase, rq_has_bulk,
                           rq_bulk_active, rq_bulk_failed, bulk_lost,
                           bulk_unlink_requested, rq_timedout, rq_net_err,
                           rq_err, rq_resend, imp_unregistering >>

ReplyCallback == RC_Wait \/ RC_Fire

BC_Wait == /\ pc["bulk_cb"] = "BC_Wait"
           /\ IF rq_phase = "COMPLETE"
                 THEN /\ pc' = [pc EXCEPT !["bulk_cb"] = "Done"]
                 ELSE /\ pc' = [pc EXCEPT !["bulk_cb"] = "BC_Fire"]
           /\ UNCHANGED << rq_phase, rq_next_phase, rq_has_bulk, rq_replied,
                           rq_receiving_reply, rq_reply_unlinked,
                           rq_bulk_active, rq_bulk_failed, bulk_lost,
                           bulk_unlink_requested, rq_timedout, rq_net_err,
                           rq_err, rq_resend, imp_unregistering >>

BC_Fire == /\ pc["bulk_cb"] = "BC_Fire"
           /\ IF rq_bulk_active
                 THEN /\ IF bulk_lost
                            THEN /\ IF bulk_unlink_requested
                                       THEN /\ /\ rq_bulk_active' = FALSE
                                               /\ rq_net_err' = TRUE
                                       ELSE /\ TRUE
                                            /\ UNCHANGED << rq_bulk_active,
                                                            rq_net_err >>
                                 /\ UNCHANGED << rq_bulk_failed, bulk_lost >>
                            ELSE /\ \/ /\ rq_bulk_active' = FALSE
                                       /\ UNCHANGED <<rq_bulk_failed, bulk_lost, rq_net_err>>
                                    \/ /\ /\ rq_bulk_active' = FALSE
                                          /\ rq_bulk_failed' = TRUE
                                          /\ rq_net_err' = TRUE
                                       /\ UNCHANGED bulk_lost
                                    \/ /\ bulk_lost' = TRUE
                                       /\ UNCHANGED <<rq_bulk_active, rq_bulk_failed, rq_net_err>>
                 ELSE /\ TRUE
                      /\ UNCHANGED << rq_bulk_active, rq_bulk_failed,
                                      bulk_lost, rq_net_err >>
           /\ pc' = [pc EXCEPT !["bulk_cb"] = "BC_Wait"]
           /\ UNCHANGED << rq_phase, rq_next_phase, rq_has_bulk, rq_replied,
                           rq_receiving_reply, rq_reply_unlinked,
                           bulk_unlink_requested, rq_timedout, rq_err,
                           rq_resend, imp_unregistering >>

BulkCallback == BC_Wait \/ BC_Fire

TH_Wait == /\ pc["timeout"] = "TH_Wait"
           /\ IF rq_phase = "COMPLETE"
                 THEN /\ pc' = [pc EXCEPT !["timeout"] = "Done"]
                 ELSE /\ pc' = [pc EXCEPT !["timeout"] = "TH_Check"]
           /\ UNCHANGED << rq_phase, rq_next_phase, rq_has_bulk, rq_replied,
                           rq_receiving_reply, rq_reply_unlinked,
                           rq_bulk_active, rq_bulk_failed, bulk_lost,
                           bulk_unlink_requested, rq_timedout, rq_net_err,
                           rq_err, rq_resend, imp_unregistering >>

TH_Check == /\ pc["timeout"] = "TH_Check"
            /\ IF rq_phase = "RPC" \/ rq_phase = "BULK"
                  THEN /\ rq_timedout' = TRUE
                       /\ pc' = [pc EXCEPT !["timeout"] = "TH_UnregReply"]
                  ELSE /\ pc' = [pc EXCEPT !["timeout"] = "TH_Loop"]
                       /\ UNCHANGED rq_timedout
            /\ UNCHANGED << rq_phase, rq_next_phase, rq_has_bulk, rq_replied,
                            rq_receiving_reply, rq_reply_unlinked,
                            rq_bulk_active, rq_bulk_failed, bulk_lost,
                            bulk_unlink_requested, rq_net_err, rq_err,
                            rq_resend, imp_unregistering >>

TH_UnregReply == /\ pc["timeout"] = "TH_UnregReply"
                 /\ IF ~rq_reply_unlinked \/ rq_receiving_reply
                       THEN /\ IF rq_phase /= "UNREG_RPC" /\ rq_phase /= "UNREG_BULK"
                                  THEN /\ /\ imp_unregistering' = imp_unregistering + 1
                                          /\ rq_next_phase' = rq_phase
                                          /\ rq_phase' = "UNREG_RPC"
                                  ELSE /\ TRUE
                                       /\ UNCHANGED << rq_phase, rq_next_phase,
                                                       imp_unregistering >>
                       ELSE /\ TRUE
                            /\ UNCHANGED << rq_phase, rq_next_phase,
                                            imp_unregistering >>
                 /\ pc' = [pc EXCEPT !["timeout"] = "TH_UnregBulk"]
                 /\ UNCHANGED << rq_has_bulk, rq_replied, rq_receiving_reply,
                                 rq_reply_unlinked, rq_bulk_active,
                                 rq_bulk_failed, bulk_lost,
                                 bulk_unlink_requested, rq_timedout,
                                 rq_net_err, rq_err, rq_resend >>

TH_UnregBulk == /\ pc["timeout"] = "TH_UnregBulk"
                /\ IF rq_has_bulk /\ rq_bulk_active
                      THEN /\ bulk_unlink_requested' = TRUE
                           /\ IF InjectBug7434
                                 THEN /\ IF rq_phase /= "UNREG_RPC" /\ rq_phase /= "UNREG_BULK"
                                            THEN /\ /\ imp_unregistering' = imp_unregistering + 1
                                                    /\ rq_next_phase' = rq_phase
                                                    /\ rq_phase' = "UNREG_RPC"
                                            ELSE /\ TRUE
                                                 /\ UNCHANGED << rq_phase,
                                                                 rq_next_phase,
                                                                 imp_unregistering >>
                                 ELSE /\ IF rq_phase /= "UNREG_RPC" /\ rq_phase /= "UNREG_BULK"
                                            THEN /\ /\ imp_unregistering' = imp_unregistering + 1
                                                    /\ rq_next_phase' = rq_phase
                                                    /\ rq_phase' = "UNREG_BULK"
                                            ELSE /\ TRUE
                                                 /\ UNCHANGED << rq_phase,
                                                                 rq_next_phase,
                                                                 imp_unregistering >>
                      ELSE /\ TRUE
                           /\ UNCHANGED << rq_phase, rq_next_phase,
                                           bulk_unlink_requested,
                                           imp_unregistering >>
                /\ pc' = [pc EXCEPT !["timeout"] = "TH_Loop"]
                /\ UNCHANGED << rq_has_bulk, rq_replied, rq_receiving_reply,
                                rq_reply_unlinked, rq_bulk_active,
                                rq_bulk_failed, bulk_lost, rq_timedout,
                                rq_net_err, rq_err, rq_resend >>

TH_Loop == /\ pc["timeout"] = "TH_Loop"
           /\ pc' = [pc EXCEPT !["timeout"] = "TH_Wait"]
           /\ UNCHANGED << rq_phase, rq_next_phase, rq_has_bulk, rq_replied,
                           rq_receiving_reply, rq_reply_unlinked,
                           rq_bulk_active, rq_bulk_failed, bulk_lost,
                           bulk_unlink_requested, rq_timedout, rq_net_err,
                           rq_err, rq_resend, imp_unregistering >>

TimeoutHandler == TH_Wait \/ TH_Check \/ TH_UnregReply \/ TH_UnregBulk
                     \/ TH_Loop

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == CheckSetProcess \/ ReplyCallback \/ BulkCallback \/ TimeoutHandler
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(CheckSetProcess)
        /\ WF_vars(ReplyCallback)
        /\ WF_vars(BulkCallback)
        /\ WF_vars(TimeoutHandler)

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

=============================================================================
