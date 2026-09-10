---------------------------- MODULE ldlm_lock_model ----------------------------
(*
 * PlusCal/TLA+ specification of LDLM lock grant/cancel protocol.
 *
 * Models the distributed lock manager protocol between clients
 * and server for a single resource:
 *   - Lock enqueue (client -> server)
 *   - Grant vs block decision (server)
 *   - Blocking AST (server -> conflicting holder)
 *   - Lock cancellation (holder -> server)
 *   - Queue reprocessing and completion AST
 *
 * Modes: NL(0), CR(1), PR(2), PW(3), EX(4)
 *
 * Safety: No two incompatible locks simultaneously granted.
 * Liveness: Every enqueue eventually granted (no starvation).
 *
 * Source (lustre-release master 47638add78):
 *   mode compatibility     lustre_dlm.h:149-171 (LCK_COMPAT_*,
 *     lockmode_compat); lck_compat_array ldlm_lib.c:3502
 *   server enqueue         ldlm_handle_enqueue ldlm_lockd.c:1248-1595
 *     -> ldlm_lock_enqueue ldlm_lock.c:1783-1949
 *     -> ldlm_lock_enqueue_helper 1750-1770
 *     -> ldlm_process_plain_lock ldlm_plain.c:110-147
 *        (ldlm_plain_compat_queue 47-100 checks granted + waiting)
 *     -> ldlm_handle_conflict_lock ldlm_lock.c:2036-2094
 *        (waiting-list add 2053-2054 + BL_AST send 2057)
 *   grant                  ldlm_grant_lock ldlm_lock.c:1121-1158
 *   BL_AST send            ldlm_run_ast_work ldlm_lock.c:2315-2373,
 *     ldlm_server_blocking_ast ldlm_lockd.c:887-995
 *   CP_AST send            ldlm_server_completion_ast
 *     ldlm_lockd.c:1004-1134
 *   client BL_AST handler  ldlm_handle_bl_callback ldlm_lockd.c:1900-1936
 *   client CP_AST handler  ldlm_handle_cp_callback ldlm_lockd.c:1957-2097
 *   client cancel          ldlm_cli_cancel ldlm_request.c:1758-1835
 *   server cancel          ldlm_request_cancel ldlm_lockd.c:1716-1810
 *     -> ldlm_lock_cancel ldlm_lock.c:2496-2538
 *     -> ldlm_reprocess_all 2430 / __ldlm_reprocess_all 2383-2428
 *     -> ldlm_reprocess_queue 1958-2020
 *
 * Validated against: lustre-release master 47638add78 (2026-09-06)
 *
 * Validation notes: the Compat table matches LCK_COMPAT_EX/PW/PR/CR
 * (lustre_dlm.h:149-153) restricted to the five classic modes (the
 * CW/GROUP/COS/TXN modes are not modeled).  Two deliberate
 * abstractions differ from the C code: (1) SRV_Grant grants a new
 * request only when waitQ is empty, which is stricter than
 * ldlm_plain_compat_queue, which only requires compatibility with
 * the waiting locks queued ahead of the request (ldlm_plain.c:64-65);
 * (2) SRV_ReprocessLoop keeps scanning past a blocked waiter,
 * which is more permissive than RESCAN in ldlm_reprocess_queue,
 * which stops at the first LDLM_ITER_STOP (ldlm_lock.c:2000-2002).
 * Neither affects GrantedSafe (pairwise compatibility of the
 * granted set); both were present when the model was written.
 *)

EXTENDS Integers, FiniteSets, Sequences, TLC

CONSTANTS
    Clients,        \* e.g. {"c1", "c2", "c3"}
    RequestModes    \* Function: Clients -> {0..4}

(* --algorithm PlusCal

variables
    \* ---- Compatibility matrix ----
    \* Encoded as set of compatible pairs
    \* NL(0) compat with all
    \* CR(1) compat with NL,CR,PR,PW  (not EX)
    \* PR(2) compat with NL,CR,PR     (not PW,EX)
    \* PW(3) compat with NL,CR        (not PR,PW,EX)
    \* EX(4) compat with NL only

    \* ---- Server-side resource state ----
    granted = {},                          \* Set of granted client IDs
    waitQ = <<>>,                          \* FIFO waiting queue
    gMode = [c \in Clients |-> 0],        \* Granted mode per client

    \* ---- Message channels (as sets) ----
    enqMsg = {},         \* <<client, mode>> enqueue requests
    grantMsg = {},       \* <<client, mode>> grant notifications
    blastMsg = {},       \* <<client>> blocking ASTs to holders
    cancelMsg = {},      \* <<client>> cancel from client

    \* ---- Per-client state ----
    cState = [c \in Clients |-> "idle"],   \* idle/requested/holding/canceling
    cMode = [c \in Clients |-> 0];

define
    \* Mode compatibility check
    Compat(m1, m2) ==
        CASE m1 = 0 -> TRUE         \* NL compat with all
          [] m2 = 0 -> TRUE
          [] m1 = 1 -> m2 <= 3      \* CR: NL,CR,PR,PW
          [] m1 = 2 -> m2 <= 2      \* PR: NL,CR,PR
          [] m1 = 3 -> m2 <= 1      \* PW: NL,CR
          [] m1 = 4 -> m2 = 0       \* EX: NL only
          [] OTHER -> FALSE

    \* Is mode compatible with all currently granted locks?
    CompatAllGranted(mode) ==
        \A g \in granted : Compat(mode, gMode[g])

    \* ---- SAFETY INVARIANTS ----

    \* All pairs of granted locks are mode-compatible
    GrantedSafe ==
        \A c1, c2 \in granted :
            c1 /= c2 => Compat(gMode[c1], gMode[c2])

    \* Granted clients are in holding or canceling state
    StateConsistent ==
        \A c \in granted :
            cState[c] \in {"holding", "canceling"}

    WaitSet == {waitQ[i] : i \in 1..Len(waitQ)}

    \* No client both granted and waiting
    GrantWaitDisjoint ==
        granted \intersect WaitSet = {}

    TypeOK ==
        /\ granted \subseteq Clients
        /\ \A c \in Clients : cState[c] \in
            {"idle", "requested", "holding", "canceling"}
        /\ \A c \in Clients : gMode[c] \in 0..4
end define;

\* ================================================================
\* Client processes
\* ================================================================
fair process Client \in Clients
begin
CL_Req:
    \* Send lock enqueue to server
    await cState[self] = "idle";
    enqMsg := enqMsg \union {<<self, RequestModes[self]>>};
    cState[self] := "requested";

CL_Wait:
    \* Wait for grant
    await <<self, RequestModes[self]>> \in grantMsg;
    grantMsg := grantMsg \ {<<self, RequestModes[self]>>};
    cState[self] := "holding";
    cMode[self] := RequestModes[self];

CL_Hold:
    \* Hold the lock until voluntary release or blocking AST
    either
        \* Voluntary release after some work
        skip;
    or
        \* Receive blocking AST
        await <<self>> \in blastMsg;
        blastMsg := blastMsg \ {<<self>>};
        cState[self] := "canceling";
    end either;

CL_Cancel:
    \* Send cancel to server (whether voluntary or forced)
    cancelMsg := cancelMsg \union {<<self>>};
    cState[self] := "idle";
    cMode[self] := 0;
end process;

\* ================================================================
\* Server process
\* ================================================================
fair process Server = "server"
variables
    sc = "none",    \* current client being processed
    sm = 0,         \* current mode
    si = 0,         \* reprocess index
    newWaitQ = <<>>;
begin
SRV:
    while TRUE do
        either
            \* ---- ENQUEUE ----
            await enqMsg /= {};
            with req \in enqMsg do
                sc := req[1];
                sm := req[2];
                enqMsg := enqMsg \ {req};
            end with;

        SRV_Grant:
            if CompatAllGranted(sm) /\ waitQ = <<>> then
                \* No conflicts, empty wait queue -> grant
                granted := granted \union {sc};
                gMode[sc] := sm;
                grantMsg := grantMsg \union {<<sc, sm>>};
            else
                \* Conflict or waiters exist -> enqueue
                waitQ := Append(waitQ, sc);
                \* Send BL_ASTs to incompatible holders
                blastMsg := blastMsg \union
                    {<<g>> : g \in
                        {g2 \in granted :
                            ~Compat(gMode[g2], sm)}};
            end if;

        or
            \* ---- CANCEL ----
            await cancelMsg /= {};
            with cancel \in cancelMsg do
                sc := cancel[1];
                cancelMsg := cancelMsg \ {cancel};
            end with;

        SRV_Cancel:
            \* Remove from granted
            if sc \in granted then
                granted := granted \ {sc};
                gMode[sc] := 0;
            end if;
            \* Remove from waitQ if present
            newWaitQ := <<>>;
            si := 1;
        SRV_RemoveWait:
            while si <= Len(waitQ) do
                if waitQ[si] /= sc then
                    newWaitQ := Append(newWaitQ, waitQ[si]);
                end if;
                si := si + 1;
            end while;
            waitQ := newWaitQ;

            \* ---- REPROCESS: try to grant waiters ----
        SRV_Reprocess:
            si := 1;
            newWaitQ := <<>>;
        SRV_ReprocessLoop:
            while si <= Len(waitQ) do
                if CompatAllGranted(
                        RequestModes[waitQ[si]]) then
                    \* Grant this waiter
                    granted := granted \union
                        {waitQ[si]};
                    gMode[waitQ[si]] :=
                        RequestModes[waitQ[si]];
                    grantMsg := grantMsg \union
                        {<<waitQ[si],
                          RequestModes[waitQ[si]]>>};
                else
                    \* Can't grant yet, keep waiting
                    newWaitQ := Append(newWaitQ,
                        waitQ[si]);
                end if;
                si := si + 1;
            end while;
            waitQ := newWaitQ;
        end either;
    end while;
end process;

end algorithm; *)

\* BEGIN TRANSLATION
VARIABLES granted, waitQ, gMode, enqMsg, grantMsg, blastMsg, cancelMsg,
          cState, cMode, pc

(* define statement *)
Compat(m1, m2) ==
    CASE m1 = 0 -> TRUE
      [] m2 = 0 -> TRUE
      [] m1 = 1 -> m2 <= 3
      [] m1 = 2 -> m2 <= 2
      [] m1 = 3 -> m2 <= 1
      [] m1 = 4 -> m2 = 0
      [] OTHER -> FALSE


CompatAllGranted(mode) ==
    \A g \in granted : Compat(mode, gMode[g])




GrantedSafe ==
    \A c1, c2 \in granted :
        c1 /= c2 => Compat(gMode[c1], gMode[c2])


StateConsistent ==
    \A c \in granted :
        cState[c] \in {"holding", "canceling"}

WaitSet == {waitQ[i] : i \in 1..Len(waitQ)}


GrantWaitDisjoint ==
    granted \intersect WaitSet = {}

TypeOK ==
    /\ granted \subseteq Clients
    /\ \A c \in Clients : cState[c] \in
        {"idle", "requested", "holding", "canceling"}
    /\ \A c \in Clients : gMode[c] \in 0..4

VARIABLES sc, sm, si, newWaitQ

vars == << granted, waitQ, gMode, enqMsg, grantMsg, blastMsg, cancelMsg,
           cState, cMode, pc, sc, sm, si, newWaitQ >>

ProcSet == (Clients) \cup {"server"}

Init == (* Global variables *)
        /\ granted = {}
        /\ waitQ = <<>>
        /\ gMode = [c \in Clients |-> 0]
        /\ enqMsg = {}
        /\ grantMsg = {}
        /\ blastMsg = {}
        /\ cancelMsg = {}
        /\ cState = [c \in Clients |-> "idle"]
        /\ cMode = [c \in Clients |-> 0]
        (* Process Server *)
        /\ sc = "none"
        /\ sm = 0
        /\ si = 0
        /\ newWaitQ = <<>>
        /\ pc = [self \in ProcSet |-> CASE self \in Clients -> "CL_Req"
                                        [] self = "server" -> "SRV"]

CL_Req(self) == /\ pc[self] = "CL_Req"
                /\ cState[self] = "idle"
                /\ enqMsg' = (enqMsg \union {<<self, RequestModes[self]>>})
                /\ cState' = [cState EXCEPT ![self] = "requested"]
                /\ pc' = [pc EXCEPT ![self] = "CL_Wait"]
                /\ UNCHANGED << granted, waitQ, gMode, grantMsg, blastMsg,
                                cancelMsg, cMode, sc, sm, si, newWaitQ >>

CL_Wait(self) == /\ pc[self] = "CL_Wait"
                 /\ <<self, RequestModes[self]>> \in grantMsg
                 /\ grantMsg' = grantMsg \ {<<self, RequestModes[self]>>}
                 /\ cState' = [cState EXCEPT ![self] = "holding"]
                 /\ cMode' = [cMode EXCEPT ![self] = RequestModes[self]]
                 /\ pc' = [pc EXCEPT ![self] = "CL_Hold"]
                 /\ UNCHANGED << granted, waitQ, gMode, enqMsg, blastMsg,
                                 cancelMsg, sc, sm, si, newWaitQ >>

CL_Hold(self) == /\ pc[self] = "CL_Hold"
                 /\ \/ /\ TRUE
                       /\ UNCHANGED <<blastMsg, cState>>
                    \/ /\ <<self>> \in blastMsg
                       /\ blastMsg' = blastMsg \ {<<self>>}
                       /\ cState' = [cState EXCEPT ![self] = "canceling"]
                 /\ pc' = [pc EXCEPT ![self] = "CL_Cancel"]
                 /\ UNCHANGED << granted, waitQ, gMode, enqMsg, grantMsg,
                                 cancelMsg, cMode, sc, sm, si, newWaitQ >>

CL_Cancel(self) == /\ pc[self] = "CL_Cancel"
                   /\ cancelMsg' = (cancelMsg \union {<<self>>})
                   /\ cState' = [cState EXCEPT ![self] = "idle"]
                   /\ cMode' = [cMode EXCEPT ![self] = 0]
                   /\ pc' = [pc EXCEPT ![self] = "Done"]
                   /\ UNCHANGED << granted, waitQ, gMode, enqMsg, grantMsg,
                                   blastMsg, sc, sm, si, newWaitQ >>

Client(self) == CL_Req(self) \/ CL_Wait(self) \/ CL_Hold(self)
                   \/ CL_Cancel(self)

SRV == /\ pc["server"] = "SRV"
       /\ \/ /\ enqMsg /= {}
             /\ \E req \in enqMsg:
                  /\ sc' = req[1]
                  /\ sm' = req[2]
                  /\ enqMsg' = enqMsg \ {req}
             /\ pc' = [pc EXCEPT !["server"] = "SRV_Grant"]
             /\ UNCHANGED cancelMsg
          \/ /\ cancelMsg /= {}
             /\ \E cancel \in cancelMsg:
                  /\ sc' = cancel[1]
                  /\ cancelMsg' = cancelMsg \ {cancel}
             /\ pc' = [pc EXCEPT !["server"] = "SRV_Cancel"]
             /\ UNCHANGED <<enqMsg, sm>>
       /\ UNCHANGED << granted, waitQ, gMode, grantMsg, blastMsg, cState,
                       cMode, si, newWaitQ >>

SRV_Grant == /\ pc["server"] = "SRV_Grant"
             /\ IF CompatAllGranted(sm) /\ waitQ = <<>>
                   THEN /\ granted' = (granted \union {sc})
                        /\ gMode' = [gMode EXCEPT ![sc] = sm]
                        /\ grantMsg' = (grantMsg \union {<<sc, sm>>})
                        /\ UNCHANGED << waitQ, blastMsg >>
                   ELSE /\ waitQ' = Append(waitQ, sc)
                        /\ blastMsg' = (        blastMsg \union
                                        {<<g>> : g \in
                                            {g2 \in granted :
                                                ~Compat(gMode[g2], sm)}})
                        /\ UNCHANGED << granted, gMode, grantMsg >>
             /\ pc' = [pc EXCEPT !["server"] = "SRV"]
             /\ UNCHANGED << enqMsg, cancelMsg, cState, cMode, sc, sm, si,
                             newWaitQ >>

SRV_Cancel == /\ pc["server"] = "SRV_Cancel"
              /\ IF sc \in granted
                    THEN /\ granted' = granted \ {sc}
                         /\ gMode' = [gMode EXCEPT ![sc] = 0]
                    ELSE /\ TRUE
                         /\ UNCHANGED << granted, gMode >>
              /\ newWaitQ' = <<>>
              /\ si' = 1
              /\ pc' = [pc EXCEPT !["server"] = "SRV_RemoveWait"]
              /\ UNCHANGED << waitQ, enqMsg, grantMsg, blastMsg, cancelMsg,
                              cState, cMode, sc, sm >>

SRV_RemoveWait == /\ pc["server"] = "SRV_RemoveWait"
                  /\ IF si <= Len(waitQ)
                        THEN /\ IF waitQ[si] /= sc
                                   THEN /\ newWaitQ' = Append(newWaitQ, waitQ[si])
                                   ELSE /\ TRUE
                                        /\ UNCHANGED newWaitQ
                             /\ si' = si + 1
                             /\ pc' = [pc EXCEPT !["server"] = "SRV_RemoveWait"]
                             /\ waitQ' = waitQ
                        ELSE /\ waitQ' = newWaitQ
                             /\ pc' = [pc EXCEPT !["server"] = "SRV_Reprocess"]
                             /\ UNCHANGED << si, newWaitQ >>
                  /\ UNCHANGED << granted, gMode, enqMsg, grantMsg, blastMsg,
                                  cancelMsg, cState, cMode, sc, sm >>

SRV_Reprocess == /\ pc["server"] = "SRV_Reprocess"
                 /\ si' = 1
                 /\ newWaitQ' = <<>>
                 /\ pc' = [pc EXCEPT !["server"] = "SRV_ReprocessLoop"]
                 /\ UNCHANGED << granted, waitQ, gMode, enqMsg, grantMsg,
                                 blastMsg, cancelMsg, cState, cMode, sc, sm >>

SRV_ReprocessLoop == /\ pc["server"] = "SRV_ReprocessLoop"
                     /\ IF si <= Len(waitQ)
                           THEN /\ IF CompatAllGranted(
                                           RequestModes[waitQ[si]])
                                      THEN /\ granted' = (       granted \union
                                                          {waitQ[si]})
                                           /\ gMode' = [gMode EXCEPT ![waitQ[si]] = RequestModes[waitQ[si]]]
                                           /\ grantMsg' = (        grantMsg \union
                                                           {<<waitQ[si],
                                                             RequestModes[waitQ[si]]>>})
                                           /\ UNCHANGED newWaitQ
                                      ELSE /\ newWaitQ' =         Append(newWaitQ,
                                                          waitQ[si])
                                           /\ UNCHANGED << granted, gMode,
                                                           grantMsg >>
                                /\ si' = si + 1
                                /\ pc' = [pc EXCEPT !["server"] = "SRV_ReprocessLoop"]
                                /\ waitQ' = waitQ
                           ELSE /\ waitQ' = newWaitQ
                                /\ pc' = [pc EXCEPT !["server"] = "SRV"]
                                /\ UNCHANGED << granted, gMode, grantMsg, si,
                                                newWaitQ >>
                     /\ UNCHANGED << enqMsg, blastMsg, cancelMsg, cState,
                                     cMode, sc, sm >>

Server == SRV \/ SRV_Grant \/ SRV_Cancel \/ SRV_RemoveWait \/ SRV_Reprocess
             \/ SRV_ReprocessLoop

Next == Server
           \/ (\E self \in Clients: Client(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Clients : WF_vars(Client(self))
        /\ WF_vars(Server)

\* END TRANSLATION

\* ================================================================
\* Constant override for TLC
\* ================================================================
\* c1=EX(4), c2=PW(3), c3=PR(2) - all different conflicting modes
const_RequestModes == ("c1" :> 4 @@ "c2" :> 3 @@ "c3" :> 2)

\* ================================================================
\* Liveness properties (check with fairness)
\* ================================================================

\* Every request eventually gets granted
EventualGrant ==
    \A c \in Clients :
        (cState[c] = "requested") ~> (cState[c] = "holding")

=============================================================================
