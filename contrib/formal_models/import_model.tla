---------------------------- MODULE import_model ----------------------------
(*
 * PlusCal/TLA+ specification of the Lustre import state machine.
 *
 * Models state transitions in lustre/ptlrpc/import.c:
 *   - Valid state transitions
 *   - imp_lock acquisition/release correctness
 *   - Idle disconnect/reconnect races
 *   - Recovery state machine progression
 *   - CLOSED as terminal state
 *
 * Known bug modeled:
 *   LU-19055: Missing unlock in ptlrpc_reconnect_if_idle when
 *             ptlrpc_connect_import_locked fails.
 *             Set InjectBug19055 = TRUE to reproduce.
 *             NB: LU-19055 was a Coverity report (CID 466795) and was
 *             resolved "Not a Bug" in JIRA: ptlrpc_connect_import_locked
 *             releases imp_lock on every return path, so the
 *             InjectBug19055 = FALSE cfg is the real code and the TRUE
 *             cfg is the hypothetical leak Coverity assumed.
 *
 * Source (lustre-release master 47638add78):
 *   lustre/include/lustre_import.h:69-80  enum lustre_imp_state
 *   lustre/ptlrpc/import.c:40-74     import_set_state_nolock (CLOSED is
 *                                    terminal, 58-59)
 *   lustre/ptlrpc/import.c:710-714   ptlrpc_connect_import
 *   lustre/ptlrpc/import.c:728-879   ptlrpc_connect_import_locked
 *                                    (ConnectThread CT_Check early returns
 *                                    750-762; CT_SetConnecting 764; DISCON
 *                                    on error 874-876; releases imp_lock
 *                                    on every path)
 *   lustre/ptlrpc/import.c:1088-1563 ptlrpc_connect_interpret
 *                                    (CT_Interpret*: CLOSED bail 1104-1109,
 *                                    IMPF_CONNECTED 1144; initial connect
 *                                    -> REPLAY_LOCKS 1279 / FULL 1283;
 *                                    reconnect -> EVICTED 1336/1348/1384,
 *                                    REPLAY 1367, RECOVER 1358/1376, FULL
 *                                    1386; DISCON on error 1439)
 *   lustre/ptlrpc/import.c:1635-1657 ptlrpc_invalidate_import_thread
 *                                    (EVICTED -> invalidate -> RECOVER 1652)
 *   lustre/ptlrpc/import.c:1686-1800 ptlrpc_import_recovery_state_machine
 *                                    (RecoveryThread: REPLAY -> REPLAY_LOCKS
 *                                    1743-1749, -> REPLAY_WAIT 1757-1759,
 *                                    -> RECOVER 1766-1768, RECOVER -> FULL
 *                                    1771-1777)
 *   lustre/ptlrpc/import.c:1857-1871 ptlrpc_disconnect_import_end
 *                                    (DISCON/CLOSED under imp_lock)
 *   lustre/ptlrpc/import.c:1909-1963 ptlrpc_disconnect_import_async
 *   lustre/ptlrpc/import.c:1978-2028 ptlrpc_disconnect_import
 *                                    (DisconnectThread)
 *   lustre/ptlrpc/import.c:2049-2092 ptlrpc_disconnect_idle_interpret
 *                                    (IdleThread ID_Interpret*/ID_Decision)
 *   lustre/ptlrpc/import.c:2109-2153 ptlrpc_disconnect_and_idle_import
 *                                    (IdleThread ID_Check/ID_GoConnecting)
 *   lustre/ptlrpc/client.c:1006-1029 ptlrpc_reconnect_if_idle
 *                                    (ReconnectIfIdleThread)
 *
 * Validated against: lustre-release master 47638add78 (2026-09-06)
 * Validation notes:
 *   - ptlrpc_reconnect_if_idle moved from client.c:992 to client.c:1006;
 *     body unchanged.
 *   - CT_Check now also bails on EVICTED, matching the -EALREADY early
 *     return in ptlrpc_connect_import_locked (import.c:758-762).  EVICTED
 *     is only ever set by ConnectThread itself after CT_Check, so the
 *     reachable state space is unchanged.
 *   - Known abstractions (not drift; they predate this validation):
 *     DisconnectThread models ptlrpc_disconnect_import as one atomic
 *     FULL -> {DISCON, CLOSED} step and bails on any other state.  The
 *     code goes FULL -> CONNECTING -> {DISCON, CLOSED} around the
 *     DISCONNECT RPC (ptlrpc_disconnect_import_async) and moves a
 *     non-FULL import straight to DISCON/CLOSED (import.c:1987-1991,
 *     1920-1927).  ptlrpc_connect_interpret bails only on CLOSED
 *     (import.c:1104), not on every non-CONNECTING state.  The code
 *     bumps imp_conn_cnt, not imp_generation, in
 *     ptlrpc_connect_import_locked (imp_generation is bumped by the
 *     idle paths and ptlrpc_deactivate_import_nolock, import.c:141).
 *)

EXTENDS Integers, FiniteSets, TLC

CONSTANTS
    InjectBug19055

(* --algorithm PlusCal
variables
    imp_state = "NEW";
    imp_generation = 0;
    imp_initiated_at = 0;
    imp_invalid = FALSE;
    imp_deactive = FALSE;
    imp_was_idle = FALSE;
    imp_connected = FALSE;
    imp_reqs = 0;
    imp_lock_holder = "none";
    thread_done = [t \in {"connect", "recovery", "idle_disc",
                          "reconn_idle", "disconnect"} |-> FALSE];

define
    ValidStates == {"CLOSED", "NEW", "DISCON", "CONNECTING",
                    "REPLAY", "REPLAY_LOCKS", "REPLAY_WAIT",
                    "RECOVER", "FULL", "EVICTED", "IDLE"}

    StateIsValid == imp_state \in ValidStates

    LockNotHeldByDone ==
        \A t \in DOMAIN thread_done:
            thread_done[t] => imp_lock_holder /= t

    ValidTransition(from, to) ==
        \/ from = "NEW"          /\ to \in {"CONNECTING", "CLOSED"}
        \/ from = "DISCON"       /\ to \in {"CONNECTING", "CLOSED"}
        \/ from = "CONNECTING"   /\ to \in {"FULL", "DISCON", "CLOSED",
                                             "EVICTED", "REPLAY",
                                             "REPLAY_LOCKS", "RECOVER",
                                             "IDLE", "NEW"}
        \/ from = "REPLAY"       /\ to \in {"REPLAY_LOCKS", "CONNECTING",
                                             "DISCON", "CLOSED"}
        \/ from = "REPLAY_LOCKS" /\ to \in {"REPLAY_WAIT", "CONNECTING",
                                             "DISCON", "CLOSED"}
        \/ from = "REPLAY_WAIT"  /\ to \in {"RECOVER", "CONNECTING",
                                             "DISCON", "CLOSED"}
        \/ from = "RECOVER"      /\ to \in {"FULL", "CONNECTING",
                                             "DISCON", "CLOSED"}
        \/ from = "FULL"         /\ to \in {"DISCON", "CONNECTING",
                                             "CLOSED"}
        \/ from = "EVICTED"      /\ to \in {"RECOVER", "CONNECTING",
                                             "DISCON", "CLOSED"}
        \/ from = "IDLE"         /\ to \in {"NEW", "CONNECTING", "CLOSED"}
end define;

\* ================================================================
\* ConnectThread: ptlrpc_connect_import + connect_interpret
\* ================================================================
fair process ConnectThread = "connect"
variables ct_initial = FALSE;
begin
CT_Lock:
    await imp_lock_holder = "none";
    imp_lock_holder := "connect";
CT_Check:
    \* ptlrpc_connect_import_locked early returns (import.c:750-762)
    if imp_state \in {"CLOSED", "FULL", "CONNECTING", "EVICTED"} \/ imp_connected then
        imp_lock_holder := "none";
        goto CT_Done;
    end if;
CT_SetConnecting:
    ct_initial := (imp_state = "NEW");
    imp_state := "CONNECTING";
    imp_generation := imp_generation + 1;
    imp_lock_holder := "none";
CT_RPC:
    skip;
CT_InterpretLock:
    await imp_lock_holder = "none";
    imp_lock_holder := "connect";
CT_InterpretCheck:
    if imp_state /= "CONNECTING" then
        imp_connected := FALSE ||
        imp_lock_holder := "none";
        goto CT_Done;
    else
        imp_connected := TRUE;
    end if;
CT_ResultFull:
    \* Nondeterministic: pick one outcome
    either
        imp_state := "FULL";
        imp_invalid := FALSE;
        imp_was_idle := FALSE;
    or
        goto CT_ResultRecovery;
    or
        goto CT_ResultEvicted;
    or
        goto CT_ResultError;
    end either;
CT_InterpretDone:
    imp_connected := FALSE;
    imp_lock_holder := "none";
    goto CT_Done;
CT_ResultRecovery:
    if ct_initial then
        imp_state := "REPLAY_LOCKS";
    else
        imp_state := "REPLAY";
    end if;
CT_RecovDone:
    imp_connected := FALSE;
    imp_lock_holder := "none";
    goto CT_Done;
CT_ResultEvicted:
    imp_state := "EVICTED";
CT_EvictDone:
    imp_connected := FALSE;
    imp_lock_holder := "none";
    goto CT_Done;
CT_ResultError:
    imp_state := "DISCON";
CT_ErrDone:
    imp_connected := FALSE;
    imp_lock_holder := "none";
CT_Done:
    thread_done["connect"] := TRUE;
end process;

\* ================================================================
\* RecoveryThread: ptlrpc_import_recovery_state_machine
\* ================================================================
fair process RecoveryThread = "recovery"
begin
RC_Lock:
    await imp_lock_holder = "none";
    imp_lock_holder := "recovery";
RC_Check:
    if imp_state = "EVICTED" then
        imp_invalid := TRUE;
        imp_state := "RECOVER";
        imp_lock_holder := "none";
        goto RC_RecoverLock;
    elsif imp_state = "REPLAY" then
        imp_state := "REPLAY_LOCKS";
        imp_lock_holder := "none";
    elsif imp_state \in {"REPLAY_LOCKS", "REPLAY_WAIT", "RECOVER"} then
        imp_lock_holder := "none";
    else
        imp_lock_holder := "none";
        goto RC_Done;
    end if;
RC_RLLock:
    await imp_lock_holder = "none";
    imp_lock_holder := "recovery";
RC_ReplayLocks:
    if imp_state = "REPLAY_LOCKS" then
        imp_state := "REPLAY_WAIT";
    end if;
    imp_lock_holder := "none";
RC_RWLock:
    await imp_lock_holder = "none";
    imp_lock_holder := "recovery";
RC_ReplayWait:
    if imp_state = "REPLAY_WAIT" then
        imp_state := "RECOVER";
    end if;
    imp_lock_holder := "none";
RC_RecoverLock:
    await imp_lock_holder = "none";
    imp_lock_holder := "recovery";
RC_Recover:
    if imp_state = "RECOVER" then
        imp_state := "FULL";
        imp_invalid := FALSE;
        imp_was_idle := FALSE;
    end if;
    imp_lock_holder := "none";
RC_Done:
    thread_done["recovery"] := TRUE;
end process;

\* ================================================================
\* IdleThread: ptlrpc_disconnect_and_idle_import +
\*             ptlrpc_disconnect_idle_interpret
\* FULL -> CONNECTING -> {IDLE, NEW}
\* ================================================================
fair process IdleThread = "idle_disc"
begin
ID_Lock:
    await imp_lock_holder = "none";
    imp_lock_holder := "idle_disc";
ID_Check:
    if imp_state /= "FULL" \/ imp_reqs > 1 then
        imp_lock_holder := "none";
        goto ID_Done;
    end if;
ID_GoConnecting:
    imp_state := "CONNECTING";
    imp_was_idle := TRUE;
    imp_lock_holder := "none";
ID_RPC:
    skip;
ID_InterpretLock:
    await imp_lock_holder = "none";
    imp_lock_holder := "idle_disc";
ID_InterpretCheck:
    if imp_state /= "CONNECTING" then
        imp_lock_holder := "none";
        goto ID_Done;
    end if;
ID_Decision:
    either
        \* New requests arrived -> reconnect
        imp_generation := imp_generation + 1;
        imp_initiated_at := imp_generation;
        imp_state := "NEW";
        imp_lock_holder := "none";
    or
        \* No requests -> IDLE
        imp_state := "IDLE";
        imp_lock_holder := "none";
    end either;
ID_Done:
    thread_done["idle_disc"] := TRUE;
end process;

\* ================================================================
\* ReconnectIfIdleThread: ptlrpc_reconnect_if_idle (client.c:1006)
\* IDLE -> NEW -> CONNECTING
\* LU-19055: missing unlock on error path
\* ================================================================
fair process ReconnectIfIdleThread = "reconn_idle"
begin
RI_Lock:
    await imp_lock_holder = "none";
    imp_lock_holder := "reconn_idle";
RI_Check:
    if imp_state /= "IDLE" then
        imp_lock_holder := "none";
        goto RI_Done;
    end if;
RI_SetNew:
    imp_generation := imp_generation + 1;
    imp_initiated_at := imp_generation;
    imp_state := "NEW";
RI_ConnectLocked:
    \* ptlrpc_connect_import_locked called with lock held
    either
        \* Success: transitions to CONNECTING, releases lock
        imp_state := "CONNECTING";
        imp_lock_holder := "none";
    or
        \* Error: connect_import_locked returns error
        goto RI_ErrorPath;
    end either;
RI_PostConnect:
    goto RI_Done;
RI_ErrorPath:
    if InjectBug19055 then
        \* BUG: lock NOT released! Caller does:
        \*   rc = ptlrpc_connect_import_locked(imp);
        \*   if (rc) return rc;  <-- no unlock!
        skip;
    else
        \* FIXED: lock released on error path too
        imp_lock_holder := "none";
    end if;
RI_Done:
    thread_done["reconn_idle"] := TRUE;
end process;

\* ================================================================
\* DisconnectThread: ptlrpc_disconnect_import
\* FULL -> {DISCON, CLOSED}
\* ================================================================
fair process DisconnectThread = "disconnect"
begin
DT_Lock:
    await imp_lock_holder = "none";
    imp_lock_holder := "disconnect";
DT_Check:
    if imp_state /= "FULL" then
        imp_lock_holder := "none";
        goto DT_Done;
    end if;
DT_Transition:
    either
        imp_state := "CLOSED";
    or
        imp_state := "DISCON";
    end either;
DT_Unlock:
    imp_lock_holder := "none";
DT_Done:
    thread_done["disconnect"] := TRUE;
end process;

end algorithm; *)

\* BEGIN TRANSLATION
VARIABLES imp_state, imp_generation, imp_initiated_at, imp_invalid,
          imp_deactive, imp_was_idle, imp_connected, imp_reqs,
          imp_lock_holder, thread_done, pc

(* define statement *)
ValidStates == {"CLOSED", "NEW", "DISCON", "CONNECTING",
                "REPLAY", "REPLAY_LOCKS", "REPLAY_WAIT",
                "RECOVER", "FULL", "EVICTED", "IDLE"}

StateIsValid == imp_state \in ValidStates

LockNotHeldByDone ==
    \A t \in DOMAIN thread_done:
        thread_done[t] => imp_lock_holder /= t

ValidTransition(from, to) ==
    \/ from = "NEW"          /\ to \in {"CONNECTING", "CLOSED"}
    \/ from = "DISCON"       /\ to \in {"CONNECTING", "CLOSED"}
    \/ from = "CONNECTING"   /\ to \in {"FULL", "DISCON", "CLOSED",
                                         "EVICTED", "REPLAY",
                                         "REPLAY_LOCKS", "RECOVER",
                                         "IDLE", "NEW"}
    \/ from = "REPLAY"       /\ to \in {"REPLAY_LOCKS", "CONNECTING",
                                         "DISCON", "CLOSED"}
    \/ from = "REPLAY_LOCKS" /\ to \in {"REPLAY_WAIT", "CONNECTING",
                                         "DISCON", "CLOSED"}
    \/ from = "REPLAY_WAIT"  /\ to \in {"RECOVER", "CONNECTING",
                                         "DISCON", "CLOSED"}
    \/ from = "RECOVER"      /\ to \in {"FULL", "CONNECTING",
                                         "DISCON", "CLOSED"}
    \/ from = "FULL"         /\ to \in {"DISCON", "CONNECTING",
                                         "CLOSED"}
    \/ from = "EVICTED"      /\ to \in {"RECOVER", "CONNECTING",
                                         "DISCON", "CLOSED"}
    \/ from = "IDLE"         /\ to \in {"NEW", "CONNECTING", "CLOSED"}

VARIABLE ct_initial

vars == << imp_state, imp_generation, imp_initiated_at, imp_invalid,
           imp_deactive, imp_was_idle, imp_connected, imp_reqs,
           imp_lock_holder, thread_done, pc, ct_initial >>

ProcSet == {"connect"} \cup {"recovery"} \cup {"idle_disc"} \cup {"reconn_idle"} \cup {"disconnect"}

Init == (* Global variables *)
        /\ imp_state = "NEW"
        /\ imp_generation = 0
        /\ imp_initiated_at = 0
        /\ imp_invalid = FALSE
        /\ imp_deactive = FALSE
        /\ imp_was_idle = FALSE
        /\ imp_connected = FALSE
        /\ imp_reqs = 0
        /\ imp_lock_holder = "none"
        /\ thread_done = [t \in {"connect", "recovery", "idle_disc",
                                 "reconn_idle", "disconnect"} |-> FALSE]
        (* Process ConnectThread *)
        /\ ct_initial = FALSE
        /\ pc = [self \in ProcSet |-> CASE self = "connect" -> "CT_Lock"
                                        [] self = "recovery" -> "RC_Lock"
                                        [] self = "idle_disc" -> "ID_Lock"
                                        [] self = "reconn_idle" -> "RI_Lock"
                                        [] self = "disconnect" -> "DT_Lock"]

CT_Lock == /\ pc["connect"] = "CT_Lock"
           /\ imp_lock_holder = "none"
           /\ imp_lock_holder' = "connect"
           /\ pc' = [pc EXCEPT !["connect"] = "CT_Check"]
           /\ UNCHANGED << imp_state, imp_generation, imp_initiated_at,
                           imp_invalid, imp_deactive, imp_was_idle,
                           imp_connected, imp_reqs, thread_done, ct_initial >>

CT_Check == /\ pc["connect"] = "CT_Check"
            /\ IF imp_state \in {"CLOSED", "FULL", "CONNECTING", "EVICTED"} \/ imp_connected
                  THEN /\ imp_lock_holder' = "none"
                       /\ pc' = [pc EXCEPT !["connect"] = "CT_Done"]
                  ELSE /\ pc' = [pc EXCEPT !["connect"] = "CT_SetConnecting"]
                       /\ UNCHANGED imp_lock_holder
            /\ UNCHANGED << imp_state, imp_generation, imp_initiated_at,
                            imp_invalid, imp_deactive, imp_was_idle,
                            imp_connected, imp_reqs, thread_done, ct_initial >>

CT_SetConnecting == /\ pc["connect"] = "CT_SetConnecting"
                    /\ ct_initial' = (imp_state = "NEW")
                    /\ imp_state' = "CONNECTING"
                    /\ imp_generation' = imp_generation + 1
                    /\ imp_lock_holder' = "none"
                    /\ pc' = [pc EXCEPT !["connect"] = "CT_RPC"]
                    /\ UNCHANGED << imp_initiated_at, imp_invalid,
                                    imp_deactive, imp_was_idle, imp_connected,
                                    imp_reqs, thread_done >>

CT_RPC == /\ pc["connect"] = "CT_RPC"
          /\ TRUE
          /\ pc' = [pc EXCEPT !["connect"] = "CT_InterpretLock"]
          /\ UNCHANGED << imp_state, imp_generation, imp_initiated_at,
                          imp_invalid, imp_deactive, imp_was_idle,
                          imp_connected, imp_reqs, imp_lock_holder,
                          thread_done, ct_initial >>

CT_InterpretLock == /\ pc["connect"] = "CT_InterpretLock"
                    /\ imp_lock_holder = "none"
                    /\ imp_lock_holder' = "connect"
                    /\ pc' = [pc EXCEPT !["connect"] = "CT_InterpretCheck"]
                    /\ UNCHANGED << imp_state, imp_generation,
                                    imp_initiated_at, imp_invalid,
                                    imp_deactive, imp_was_idle, imp_connected,
                                    imp_reqs, thread_done, ct_initial >>

CT_InterpretCheck == /\ pc["connect"] = "CT_InterpretCheck"
                     /\ IF imp_state /= "CONNECTING"
                           THEN /\ /\ imp_connected' = FALSE
                                   /\ imp_lock_holder' = "none"
                                /\ pc' = [pc EXCEPT !["connect"] = "CT_Done"]
                           ELSE /\ imp_connected' = TRUE
                                /\ pc' = [pc EXCEPT !["connect"] = "CT_ResultFull"]
                                /\ UNCHANGED imp_lock_holder
                     /\ UNCHANGED << imp_state, imp_generation,
                                     imp_initiated_at, imp_invalid,
                                     imp_deactive, imp_was_idle, imp_reqs,
                                     thread_done, ct_initial >>

CT_ResultFull == /\ pc["connect"] = "CT_ResultFull"
                 /\ \/ /\ imp_state' = "FULL"
                       /\ imp_invalid' = FALSE
                       /\ imp_was_idle' = FALSE
                       /\ pc' = [pc EXCEPT !["connect"] = "CT_InterpretDone"]
                    \/ /\ pc' = [pc EXCEPT !["connect"] = "CT_ResultRecovery"]
                       /\ UNCHANGED <<imp_state, imp_invalid, imp_was_idle>>
                    \/ /\ pc' = [pc EXCEPT !["connect"] = "CT_ResultEvicted"]
                       /\ UNCHANGED <<imp_state, imp_invalid, imp_was_idle>>
                    \/ /\ pc' = [pc EXCEPT !["connect"] = "CT_ResultError"]
                       /\ UNCHANGED <<imp_state, imp_invalid, imp_was_idle>>
                 /\ UNCHANGED << imp_generation, imp_initiated_at,
                                 imp_deactive, imp_connected, imp_reqs,
                                 imp_lock_holder, thread_done, ct_initial >>

CT_InterpretDone == /\ pc["connect"] = "CT_InterpretDone"
                    /\ imp_connected' = FALSE
                    /\ imp_lock_holder' = "none"
                    /\ pc' = [pc EXCEPT !["connect"] = "CT_Done"]
                    /\ UNCHANGED << imp_state, imp_generation,
                                    imp_initiated_at, imp_invalid,
                                    imp_deactive, imp_was_idle, imp_reqs,
                                    thread_done, ct_initial >>

CT_ResultRecovery == /\ pc["connect"] = "CT_ResultRecovery"
                     /\ IF ct_initial
                           THEN /\ imp_state' = "REPLAY_LOCKS"
                           ELSE /\ imp_state' = "REPLAY"
                     /\ pc' = [pc EXCEPT !["connect"] = "CT_RecovDone"]
                     /\ UNCHANGED << imp_generation, imp_initiated_at,
                                     imp_invalid, imp_deactive, imp_was_idle,
                                     imp_connected, imp_reqs, imp_lock_holder,
                                     thread_done, ct_initial >>

CT_RecovDone == /\ pc["connect"] = "CT_RecovDone"
                /\ imp_connected' = FALSE
                /\ imp_lock_holder' = "none"
                /\ pc' = [pc EXCEPT !["connect"] = "CT_Done"]
                /\ UNCHANGED << imp_state, imp_generation, imp_initiated_at,
                                imp_invalid, imp_deactive, imp_was_idle,
                                imp_reqs, thread_done, ct_initial >>

CT_ResultEvicted == /\ pc["connect"] = "CT_ResultEvicted"
                    /\ imp_state' = "EVICTED"
                    /\ pc' = [pc EXCEPT !["connect"] = "CT_EvictDone"]
                    /\ UNCHANGED << imp_generation, imp_initiated_at,
                                    imp_invalid, imp_deactive, imp_was_idle,
                                    imp_connected, imp_reqs, imp_lock_holder,
                                    thread_done, ct_initial >>

CT_EvictDone == /\ pc["connect"] = "CT_EvictDone"
                /\ imp_connected' = FALSE
                /\ imp_lock_holder' = "none"
                /\ pc' = [pc EXCEPT !["connect"] = "CT_Done"]
                /\ UNCHANGED << imp_state, imp_generation, imp_initiated_at,
                                imp_invalid, imp_deactive, imp_was_idle,
                                imp_reqs, thread_done, ct_initial >>

CT_ResultError == /\ pc["connect"] = "CT_ResultError"
                  /\ imp_state' = "DISCON"
                  /\ pc' = [pc EXCEPT !["connect"] = "CT_ErrDone"]
                  /\ UNCHANGED << imp_generation, imp_initiated_at,
                                  imp_invalid, imp_deactive, imp_was_idle,
                                  imp_connected, imp_reqs, imp_lock_holder,
                                  thread_done, ct_initial >>

CT_ErrDone == /\ pc["connect"] = "CT_ErrDone"
              /\ imp_connected' = FALSE
              /\ imp_lock_holder' = "none"
              /\ pc' = [pc EXCEPT !["connect"] = "CT_Done"]
              /\ UNCHANGED << imp_state, imp_generation, imp_initiated_at,
                              imp_invalid, imp_deactive, imp_was_idle,
                              imp_reqs, thread_done, ct_initial >>

CT_Done == /\ pc["connect"] = "CT_Done"
           /\ thread_done' = [thread_done EXCEPT !["connect"] = TRUE]
           /\ pc' = [pc EXCEPT !["connect"] = "Done"]
           /\ UNCHANGED << imp_state, imp_generation, imp_initiated_at,
                           imp_invalid, imp_deactive, imp_was_idle,
                           imp_connected, imp_reqs, imp_lock_holder,
                           ct_initial >>

ConnectThread == CT_Lock \/ CT_Check \/ CT_SetConnecting \/ CT_RPC
                    \/ CT_InterpretLock \/ CT_InterpretCheck
                    \/ CT_ResultFull \/ CT_InterpretDone
                    \/ CT_ResultRecovery \/ CT_RecovDone
                    \/ CT_ResultEvicted \/ CT_EvictDone \/ CT_ResultError
                    \/ CT_ErrDone \/ CT_Done

RC_Lock == /\ pc["recovery"] = "RC_Lock"
           /\ imp_lock_holder = "none"
           /\ imp_lock_holder' = "recovery"
           /\ pc' = [pc EXCEPT !["recovery"] = "RC_Check"]
           /\ UNCHANGED << imp_state, imp_generation, imp_initiated_at,
                           imp_invalid, imp_deactive, imp_was_idle,
                           imp_connected, imp_reqs, thread_done, ct_initial >>

RC_Check == /\ pc["recovery"] = "RC_Check"
            /\ IF imp_state = "EVICTED"
                  THEN /\ imp_invalid' = TRUE
                       /\ imp_state' = "RECOVER"
                       /\ imp_lock_holder' = "none"
                       /\ pc' = [pc EXCEPT !["recovery"] = "RC_RecoverLock"]
                  ELSE /\ IF imp_state = "REPLAY"
                             THEN /\ imp_state' = "REPLAY_LOCKS"
                                  /\ imp_lock_holder' = "none"
                                  /\ pc' = [pc EXCEPT !["recovery"] = "RC_RLLock"]
                             ELSE /\ IF imp_state \in {"REPLAY_LOCKS", "REPLAY_WAIT", "RECOVER"}
                                        THEN /\ imp_lock_holder' = "none"
                                             /\ pc' = [pc EXCEPT !["recovery"] = "RC_RLLock"]
                                        ELSE /\ imp_lock_holder' = "none"
                                             /\ pc' = [pc EXCEPT !["recovery"] = "RC_Done"]
                                  /\ UNCHANGED imp_state
                       /\ UNCHANGED imp_invalid
            /\ UNCHANGED << imp_generation, imp_initiated_at, imp_deactive,
                            imp_was_idle, imp_connected, imp_reqs, thread_done,
                            ct_initial >>

RC_RLLock == /\ pc["recovery"] = "RC_RLLock"
             /\ imp_lock_holder = "none"
             /\ imp_lock_holder' = "recovery"
             /\ pc' = [pc EXCEPT !["recovery"] = "RC_ReplayLocks"]
             /\ UNCHANGED << imp_state, imp_generation, imp_initiated_at,
                             imp_invalid, imp_deactive, imp_was_idle,
                             imp_connected, imp_reqs, thread_done, ct_initial >>

RC_ReplayLocks == /\ pc["recovery"] = "RC_ReplayLocks"
                  /\ IF imp_state = "REPLAY_LOCKS"
                        THEN /\ imp_state' = "REPLAY_WAIT"
                        ELSE /\ TRUE
                             /\ UNCHANGED imp_state
                  /\ imp_lock_holder' = "none"
                  /\ pc' = [pc EXCEPT !["recovery"] = "RC_RWLock"]
                  /\ UNCHANGED << imp_generation, imp_initiated_at,
                                  imp_invalid, imp_deactive, imp_was_idle,
                                  imp_connected, imp_reqs, thread_done,
                                  ct_initial >>

RC_RWLock == /\ pc["recovery"] = "RC_RWLock"
             /\ imp_lock_holder = "none"
             /\ imp_lock_holder' = "recovery"
             /\ pc' = [pc EXCEPT !["recovery"] = "RC_ReplayWait"]
             /\ UNCHANGED << imp_state, imp_generation, imp_initiated_at,
                             imp_invalid, imp_deactive, imp_was_idle,
                             imp_connected, imp_reqs, thread_done, ct_initial >>

RC_ReplayWait == /\ pc["recovery"] = "RC_ReplayWait"
                 /\ IF imp_state = "REPLAY_WAIT"
                       THEN /\ imp_state' = "RECOVER"
                       ELSE /\ TRUE
                            /\ UNCHANGED imp_state
                 /\ imp_lock_holder' = "none"
                 /\ pc' = [pc EXCEPT !["recovery"] = "RC_RecoverLock"]
                 /\ UNCHANGED << imp_generation, imp_initiated_at, imp_invalid,
                                 imp_deactive, imp_was_idle, imp_connected,
                                 imp_reqs, thread_done, ct_initial >>

RC_RecoverLock == /\ pc["recovery"] = "RC_RecoverLock"
                  /\ imp_lock_holder = "none"
                  /\ imp_lock_holder' = "recovery"
                  /\ pc' = [pc EXCEPT !["recovery"] = "RC_Recover"]
                  /\ UNCHANGED << imp_state, imp_generation, imp_initiated_at,
                                  imp_invalid, imp_deactive, imp_was_idle,
                                  imp_connected, imp_reqs, thread_done,
                                  ct_initial >>

RC_Recover == /\ pc["recovery"] = "RC_Recover"
              /\ IF imp_state = "RECOVER"
                    THEN /\ imp_state' = "FULL"
                         /\ imp_invalid' = FALSE
                         /\ imp_was_idle' = FALSE
                    ELSE /\ TRUE
                         /\ UNCHANGED << imp_state, imp_invalid, imp_was_idle >>
              /\ imp_lock_holder' = "none"
              /\ pc' = [pc EXCEPT !["recovery"] = "RC_Done"]
              /\ UNCHANGED << imp_generation, imp_initiated_at, imp_deactive,
                              imp_connected, imp_reqs, thread_done, ct_initial >>

RC_Done == /\ pc["recovery"] = "RC_Done"
           /\ thread_done' = [thread_done EXCEPT !["recovery"] = TRUE]
           /\ pc' = [pc EXCEPT !["recovery"] = "Done"]
           /\ UNCHANGED << imp_state, imp_generation, imp_initiated_at,
                           imp_invalid, imp_deactive, imp_was_idle,
                           imp_connected, imp_reqs, imp_lock_holder,
                           ct_initial >>

RecoveryThread == RC_Lock \/ RC_Check \/ RC_RLLock \/ RC_ReplayLocks
                     \/ RC_RWLock \/ RC_ReplayWait \/ RC_RecoverLock
                     \/ RC_Recover \/ RC_Done

ID_Lock == /\ pc["idle_disc"] = "ID_Lock"
           /\ imp_lock_holder = "none"
           /\ imp_lock_holder' = "idle_disc"
           /\ pc' = [pc EXCEPT !["idle_disc"] = "ID_Check"]
           /\ UNCHANGED << imp_state, imp_generation, imp_initiated_at,
                           imp_invalid, imp_deactive, imp_was_idle,
                           imp_connected, imp_reqs, thread_done, ct_initial >>

ID_Check == /\ pc["idle_disc"] = "ID_Check"
            /\ IF imp_state /= "FULL" \/ imp_reqs > 1
                  THEN /\ imp_lock_holder' = "none"
                       /\ pc' = [pc EXCEPT !["idle_disc"] = "ID_Done"]
                  ELSE /\ pc' = [pc EXCEPT !["idle_disc"] = "ID_GoConnecting"]
                       /\ UNCHANGED imp_lock_holder
            /\ UNCHANGED << imp_state, imp_generation, imp_initiated_at,
                            imp_invalid, imp_deactive, imp_was_idle,
                            imp_connected, imp_reqs, thread_done, ct_initial >>

ID_GoConnecting == /\ pc["idle_disc"] = "ID_GoConnecting"
                   /\ imp_state' = "CONNECTING"
                   /\ imp_was_idle' = TRUE
                   /\ imp_lock_holder' = "none"
                   /\ pc' = [pc EXCEPT !["idle_disc"] = "ID_RPC"]
                   /\ UNCHANGED << imp_generation, imp_initiated_at,
                                   imp_invalid, imp_deactive, imp_connected,
                                   imp_reqs, thread_done, ct_initial >>

ID_RPC == /\ pc["idle_disc"] = "ID_RPC"
          /\ TRUE
          /\ pc' = [pc EXCEPT !["idle_disc"] = "ID_InterpretLock"]
          /\ UNCHANGED << imp_state, imp_generation, imp_initiated_at,
                          imp_invalid, imp_deactive, imp_was_idle,
                          imp_connected, imp_reqs, imp_lock_holder,
                          thread_done, ct_initial >>

ID_InterpretLock == /\ pc["idle_disc"] = "ID_InterpretLock"
                    /\ imp_lock_holder = "none"
                    /\ imp_lock_holder' = "idle_disc"
                    /\ pc' = [pc EXCEPT !["idle_disc"] = "ID_InterpretCheck"]
                    /\ UNCHANGED << imp_state, imp_generation,
                                    imp_initiated_at, imp_invalid,
                                    imp_deactive, imp_was_idle, imp_connected,
                                    imp_reqs, thread_done, ct_initial >>

ID_InterpretCheck == /\ pc["idle_disc"] = "ID_InterpretCheck"
                     /\ IF imp_state /= "CONNECTING"
                           THEN /\ imp_lock_holder' = "none"
                                /\ pc' = [pc EXCEPT !["idle_disc"] = "ID_Done"]
                           ELSE /\ pc' = [pc EXCEPT !["idle_disc"] = "ID_Decision"]
                                /\ UNCHANGED imp_lock_holder
                     /\ UNCHANGED << imp_state, imp_generation,
                                     imp_initiated_at, imp_invalid,
                                     imp_deactive, imp_was_idle, imp_connected,
                                     imp_reqs, thread_done, ct_initial >>

ID_Decision == /\ pc["idle_disc"] = "ID_Decision"
               /\ \/ /\ imp_generation' = imp_generation + 1
                     /\ imp_initiated_at' = imp_generation'
                     /\ imp_state' = "NEW"
                     /\ imp_lock_holder' = "none"
                  \/ /\ imp_state' = "IDLE"
                     /\ imp_lock_holder' = "none"
                     /\ UNCHANGED <<imp_generation, imp_initiated_at>>
               /\ pc' = [pc EXCEPT !["idle_disc"] = "ID_Done"]
               /\ UNCHANGED << imp_invalid, imp_deactive, imp_was_idle,
                               imp_connected, imp_reqs, thread_done,
                               ct_initial >>

ID_Done == /\ pc["idle_disc"] = "ID_Done"
           /\ thread_done' = [thread_done EXCEPT !["idle_disc"] = TRUE]
           /\ pc' = [pc EXCEPT !["idle_disc"] = "Done"]
           /\ UNCHANGED << imp_state, imp_generation, imp_initiated_at,
                           imp_invalid, imp_deactive, imp_was_idle,
                           imp_connected, imp_reqs, imp_lock_holder,
                           ct_initial >>

IdleThread == ID_Lock \/ ID_Check \/ ID_GoConnecting \/ ID_RPC
                 \/ ID_InterpretLock \/ ID_InterpretCheck \/ ID_Decision
                 \/ ID_Done

RI_Lock == /\ pc["reconn_idle"] = "RI_Lock"
           /\ imp_lock_holder = "none"
           /\ imp_lock_holder' = "reconn_idle"
           /\ pc' = [pc EXCEPT !["reconn_idle"] = "RI_Check"]
           /\ UNCHANGED << imp_state, imp_generation, imp_initiated_at,
                           imp_invalid, imp_deactive, imp_was_idle,
                           imp_connected, imp_reqs, thread_done, ct_initial >>

RI_Check == /\ pc["reconn_idle"] = "RI_Check"
            /\ IF imp_state /= "IDLE"
                  THEN /\ imp_lock_holder' = "none"
                       /\ pc' = [pc EXCEPT !["reconn_idle"] = "RI_Done"]
                  ELSE /\ pc' = [pc EXCEPT !["reconn_idle"] = "RI_SetNew"]
                       /\ UNCHANGED imp_lock_holder
            /\ UNCHANGED << imp_state, imp_generation, imp_initiated_at,
                            imp_invalid, imp_deactive, imp_was_idle,
                            imp_connected, imp_reqs, thread_done, ct_initial >>

RI_SetNew == /\ pc["reconn_idle"] = "RI_SetNew"
             /\ imp_generation' = imp_generation + 1
             /\ imp_initiated_at' = imp_generation'
             /\ imp_state' = "NEW"
             /\ pc' = [pc EXCEPT !["reconn_idle"] = "RI_ConnectLocked"]
             /\ UNCHANGED << imp_invalid, imp_deactive, imp_was_idle,
                             imp_connected, imp_reqs, imp_lock_holder,
                             thread_done, ct_initial >>

RI_ConnectLocked == /\ pc["reconn_idle"] = "RI_ConnectLocked"
                    /\ \/ /\ imp_state' = "CONNECTING"
                          /\ imp_lock_holder' = "none"
                          /\ pc' = [pc EXCEPT !["reconn_idle"] = "RI_PostConnect"]
                       \/ /\ pc' = [pc EXCEPT !["reconn_idle"] = "RI_ErrorPath"]
                          /\ UNCHANGED <<imp_state, imp_lock_holder>>
                    /\ UNCHANGED << imp_generation, imp_initiated_at,
                                    imp_invalid, imp_deactive, imp_was_idle,
                                    imp_connected, imp_reqs, thread_done,
                                    ct_initial >>

RI_PostConnect == /\ pc["reconn_idle"] = "RI_PostConnect"
                  /\ pc' = [pc EXCEPT !["reconn_idle"] = "RI_Done"]
                  /\ UNCHANGED << imp_state, imp_generation, imp_initiated_at,
                                  imp_invalid, imp_deactive, imp_was_idle,
                                  imp_connected, imp_reqs, imp_lock_holder,
                                  thread_done, ct_initial >>

RI_ErrorPath == /\ pc["reconn_idle"] = "RI_ErrorPath"
                /\ IF InjectBug19055
                      THEN /\ TRUE
                           /\ UNCHANGED imp_lock_holder
                      ELSE /\ imp_lock_holder' = "none"
                /\ pc' = [pc EXCEPT !["reconn_idle"] = "RI_Done"]
                /\ UNCHANGED << imp_state, imp_generation, imp_initiated_at,
                                imp_invalid, imp_deactive, imp_was_idle,
                                imp_connected, imp_reqs, thread_done,
                                ct_initial >>

RI_Done == /\ pc["reconn_idle"] = "RI_Done"
           /\ thread_done' = [thread_done EXCEPT !["reconn_idle"] = TRUE]
           /\ pc' = [pc EXCEPT !["reconn_idle"] = "Done"]
           /\ UNCHANGED << imp_state, imp_generation, imp_initiated_at,
                           imp_invalid, imp_deactive, imp_was_idle,
                           imp_connected, imp_reqs, imp_lock_holder,
                           ct_initial >>

ReconnectIfIdleThread == RI_Lock \/ RI_Check \/ RI_SetNew
                            \/ RI_ConnectLocked \/ RI_PostConnect
                            \/ RI_ErrorPath \/ RI_Done

DT_Lock == /\ pc["disconnect"] = "DT_Lock"
           /\ imp_lock_holder = "none"
           /\ imp_lock_holder' = "disconnect"
           /\ pc' = [pc EXCEPT !["disconnect"] = "DT_Check"]
           /\ UNCHANGED << imp_state, imp_generation, imp_initiated_at,
                           imp_invalid, imp_deactive, imp_was_idle,
                           imp_connected, imp_reqs, thread_done, ct_initial >>

DT_Check == /\ pc["disconnect"] = "DT_Check"
            /\ IF imp_state /= "FULL"
                  THEN /\ imp_lock_holder' = "none"
                       /\ pc' = [pc EXCEPT !["disconnect"] = "DT_Done"]
                  ELSE /\ pc' = [pc EXCEPT !["disconnect"] = "DT_Transition"]
                       /\ UNCHANGED imp_lock_holder
            /\ UNCHANGED << imp_state, imp_generation, imp_initiated_at,
                            imp_invalid, imp_deactive, imp_was_idle,
                            imp_connected, imp_reqs, thread_done, ct_initial >>

DT_Transition == /\ pc["disconnect"] = "DT_Transition"
                 /\ \/ /\ imp_state' = "CLOSED"
                    \/ /\ imp_state' = "DISCON"
                 /\ pc' = [pc EXCEPT !["disconnect"] = "DT_Unlock"]
                 /\ UNCHANGED << imp_generation, imp_initiated_at, imp_invalid,
                                 imp_deactive, imp_was_idle, imp_connected,
                                 imp_reqs, imp_lock_holder, thread_done,
                                 ct_initial >>

DT_Unlock == /\ pc["disconnect"] = "DT_Unlock"
             /\ imp_lock_holder' = "none"
             /\ pc' = [pc EXCEPT !["disconnect"] = "DT_Done"]
             /\ UNCHANGED << imp_state, imp_generation, imp_initiated_at,
                             imp_invalid, imp_deactive, imp_was_idle,
                             imp_connected, imp_reqs, thread_done, ct_initial >>

DT_Done == /\ pc["disconnect"] = "DT_Done"
           /\ thread_done' = [thread_done EXCEPT !["disconnect"] = TRUE]
           /\ pc' = [pc EXCEPT !["disconnect"] = "Done"]
           /\ UNCHANGED << imp_state, imp_generation, imp_initiated_at,
                           imp_invalid, imp_deactive, imp_was_idle,
                           imp_connected, imp_reqs, imp_lock_holder,
                           ct_initial >>

DisconnectThread == DT_Lock \/ DT_Check \/ DT_Transition \/ DT_Unlock
                       \/ DT_Done

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == ConnectThread \/ RecoveryThread \/ IdleThread
           \/ ReconnectIfIdleThread \/ DisconnectThread
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(ConnectThread)
        /\ WF_vars(RecoveryThread)
        /\ WF_vars(IdleThread)
        /\ WF_vars(ReconnectIfIdleThread)
        /\ WF_vars(DisconnectThread)

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

\* Temporal properties
AllThreadsTerminate == <>(\A t \in DOMAIN thread_done : thread_done[t])
LockEventuallyFree == []<>(imp_lock_holder = "none")

=============================================================================
