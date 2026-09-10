--------------------- MODULE osc_grant_shrink_reconnect ---------------------
(*
 * Model: SHRINK grant notification racing osc_init_grant on reconnect.
 *
 * Extension to osc_grant_eviction_race.tla (PR #7).  After eviction and
 * reconnect, the server may send an OBD_BRW_DECREASE_GRANT (shrink)
 * while the client is mid-osc_init_grant().  This creates a TOCTOU window:
 *
 *   1. Client reads server_grant from CONNECT reply to compute avail
 *   2. Server sends SHRINK -- client processes it, reducing cl_import_grant
 *   3. Client writes the stale avail back, inflating cl_import_grant past
 *      the new server-authorized limit
 *
 * Processes:
 *   ReconnectGrant ("RG") -- reads server_grant, computes avail, writes back
 *   ShrinkHandler  ("SH") -- processes OBD_BRW_DECREASE_GRANT
 *   Writer         ("W")  -- reserve + consume grants (background activity)
 *
 * Invariants:
 *   GrantConservation -- cl_import_grant <= server_authorized_grant after
 *                       reconnect completes
 *   NoNegativeGrant  -- shrink arriving pre-init must not cause negative grant
 *
 * Configurations:
 *   baseline          -- no bug injection, reconnect completes cleanly (pass)
 *   shrink_toctou_bug -- (HISTORICAL: assumption violation; bug path does not
 *                        exist in real code -- see verification note below)
 *   shrink_toctou_fix -- atomic read+write with post-init shrink recheck (pass)
 *
 * Derived from osc_grant_eviction_race.tla.  Focused sub-model: 3 processes,
 * ~1000x smaller state space than the full grant model.
 *
 * === Real-code verification (2026-03-12, lustre-design-docs-04b) ===
 *
 * Verified against lustre-release master (osc_request.c:1002-1066 at
 * 47638add78; originally 988-1050).
 *
 * osc_init_grant() acquires spin_lock(&cli->cl_loi_list_lock) at line 1013
 * and holds it CONTINUOUSLY through the full read-compute-write sequence
 * (cl_avail_grant = ocd_grant - reserved - dirty, 1014-1027), releasing at
 * line 1056.  There is no lock drop-and-reacquire.
 *
 * Consequence: InjectBugShrinkTOCTOU = TRUE is structurally impossible in the
 * real code.  The ASSUME below enforces this: TLC will reject any config that
 * sets InjectBugShrinkTOCTOU = TRUE, making the bug configuration unreachable
 * rather than merely documented.
 *
 * Additionally, ocd->ocd_grant (the "server_grant" in this model) is a
 * parameter extracted from the CONNECT reply before osc_init_grant() is called;
 * concurrent shrink RPCs do not modify it.  Both properties close the window.
 *
 * No JIRA filed.  Model retained as a latent-risk exploration: it shows what
 * WOULD break if the lock discipline were ever relaxed.
 *
 * Source (lustre-release master 47638add78):
 *   lustre/osc/osc_request.c
 *     osc_import_event()      3896-3970  IMP_EVENT_DISCON zeroes
 *                                        cl_avail_grant 3907-3913
 *                                        (RG_DoEvict); IMP_EVENT_OCD ->
 *                                        osc_init_grant 3947-3951
 *     osc_init_grant()        1002-1066  single lock hold 1013-1056
 *                                        (RG_ReadServerGrant/RG_WriteBack)
 *     osc_update_grant()      756-762    the ONLY server->client grant
 *     __osc_update_grant()    749-754    update: additive, from a BRW
 *                                        reply (osc_brw_fini_request 2200)
 *                                        or a shrink reply (789)
 *   lustre/osc/osc_cache.c
 *     osc_reserve_grant()     1515-1525  avail -> reserved (Writer)
 *     osc_unreserve_grant_no_wake() 1527-1545 reserved -> dirty (Writer)
 *
 * Validated against: lustre-release master 47638add78 (2026-09-06)
 * Validation notes: there is no OBD_BRW_DECREASE_GRANT in the tree and
 *   no server-initiated shrink at all; the server only ever ADDS grant
 *   to the client (osc_update_grant above).  ShrinkHandler is therefore
 *   a hypothetical actor, as the note above already says for the TOCTOU
 *   path.  The shrink_toctou_bug cfg is rejected by the ASSUME (TLC:
 *   "Assumption ... is false"), not by an invariant; its @violated tag
 *   now says so.  No model change.
 *)

EXTENDS Integers, TLC

CONSTANTS
    TOTAL_GRANT,           \* Initial server-authorized grant
    SHRINK_AMOUNT,         \* How much the server shrinks by
    MAX_ITER,              \* Writer loop iterations
    InjectBugShrinkTOCTOU  \* MUST be FALSE: real osc_init_grant holds lock continuously

\* Real-code constraint: osc_init_grant() holds cl_loi_list_lock with no gap.
\* Setting InjectBugShrinkTOCTOU = TRUE is structurally impossible in the real
\* implementation; this ASSUME causes TLC to reject such configurations.
ASSUME InjectBugShrinkTOCTOU = FALSE

(* --algorithm PlusCal
variables
    \* Client-side grant accounting
    cl_import_grant = TOTAL_GRANT,    \* ocd->ocd_grant (client's view of total)
    cl_avail_grant = TOTAL_GRANT,     \* cli->cl_avail_grant
    cl_dirty_grant = 0,               \* cli->cl_dirty_grant
    cl_reserved_grant = 0,            \* cli->cl_reserved_grant

    \* Server-side authorized grant (what the server considers valid)
    server_authorized_grant = TOTAL_GRANT,

    \* Lock state (cl_loi_list_lock)
    loi_lock = "free",

    \* Reconnect sequencing
    \* Phase: "pre_eviction" -> "evicted" -> "reconnecting" -> "connected"
    phase = "pre_eviction",

    \* Flag: shrink notification has arrived (for recheck in fix path)
    shrink_pending = FALSE;

define
    \* === Core invariants ===

    \* After reconnect completes, client's import grant must not exceed
    \* what the server authorized.  This is the key safety property.
    GrantConservation ==
        phase = "connected" =>
            cl_import_grant <= server_authorized_grant

    \* No grant variable should ever go negative.
    NoNegativeGrant ==
        cl_import_grant >= 0 /\ cl_avail_grant >= 0 /\
        cl_dirty_grant >= 0 /\ cl_reserved_grant >= 0 /\
        server_authorized_grant >= 0

    \* Client available+dirty+reserved should not exceed import grant
    ClientPoolBounded ==
        cl_avail_grant + cl_dirty_grant + cl_reserved_grant <= cl_import_grant

    \* Server authorized grant should never go negative from shrink
    ServerGrantNonNegative ==
        server_authorized_grant >= 0

end define;

\* ---------------------------------------------------------------
\* Writer: models background grant consumption (osc_queue_async_io)
\*   Loops MAX_ITER times: reserve from avail, consume to dirty.
\*   Runs across all phases to create interference.
\* ---------------------------------------------------------------
fair process Writer = "W"
variables
    w_iter = 0;
begin
W_Start:
    if w_iter >= MAX_ITER then
        goto W_Done;
    else
        w_iter := w_iter + 1;
    end if;

W_AcquireLock1:
    await loi_lock = "free";
    loi_lock := "W";

W_Reserve:
    if cl_avail_grant >= 1 then
        cl_avail_grant := cl_avail_grant - 1;
        cl_reserved_grant := cl_reserved_grant + 1;
        loi_lock := "free";
    else
        loi_lock := "free";
        goto W_Start;
    end if;

W_AcquireLock2:
    await loi_lock = "free";
    loi_lock := "W";

W_ConsumeDirty:
    cl_reserved_grant := cl_reserved_grant - 1;
    cl_dirty_grant := cl_dirty_grant + 1;
    loi_lock := "free";
    goto W_Start;

W_Done:
    skip;
end process;

\* ---------------------------------------------------------------
\* ShrinkHandler: models osc_grant_shrink path
\*   Server sends OBD_BRW_DECREASE_GRANT, client reduces its grants.
\*
\*   In real code: osc_shrink_grant() under cl_loi_list_lock:
\*     cl_import_grant -= shrink_amount
\*     cl_avail_grant -= shrink_amount (clamped to 0)
\*
\*   Validation note (47638add78): no such server-initiated message
\*   exists; grant shrink is client-initiated (osc_shrink_grant_local /
\*   osc_shrink_grant_to_target, osc_request.c:797-879) and the server
\*   only ever adds grant back (osc_update_grant, 756-762).  Kept as a
\*   hypothetical interference source.
\*
\*   The shrink can arrive at any time after reconnect begins.
\*   The race is when it arrives mid-osc_init_grant.
\*
\*   One-shot: fires once when phase is "reconnecting" (the
\*   dangerous window) or "connected" (post-reconnect).
\* ---------------------------------------------------------------
fair process ShrinkHandler = "SH"
begin
SH_WaitReconnecting:
    \* Shrink arrives during or after reconnect
    await phase = "reconnecting" \/ phase = "connected";

SH_AcquireLock:
    await loi_lock = "free";
    loi_lock := "SH";

SH_ProcessShrink:
    \* Server reduces authorized grant
    server_authorized_grant := server_authorized_grant - SHRINK_AMOUNT;
    \* Client processes the shrink notification
    cl_import_grant := cl_import_grant - SHRINK_AMOUNT;
    \* Reduce avail (clamp to 0)
    if cl_avail_grant >= SHRINK_AMOUNT then
        cl_avail_grant := cl_avail_grant - SHRINK_AMOUNT;
    else
        cl_avail_grant := 0;
    end if;
    \* Signal that shrink was processed (for fix recheck)
    shrink_pending := TRUE;
    loi_lock := "free";

SH_Done:
    skip;
end process;

\* ---------------------------------------------------------------
\* ReconnectGrant: models osc_init_grant after eviction+reconnect
\*
\* Real code path:
\*   1. Eviction zeros cl_avail_grant
\*   2. Server CONNECT reply carries ocd_grant (= server_authorized_grant)
\*   3. osc_init_grant computes:
\*        cl_avail_grant = ocd_grant - cl_dirty_grant - cl_reserved_grant
\*        cl_import_grant = ocd_grant
\*
\* BUG variant (InjectBugShrinkTOCTOU = TRUE):
\*   Read server_grant into local variable (step 1), release lock,
\*   re-acquire lock, write back (step 2).  Between steps, ShrinkHandler
\*   can modify cl_import_grant, and our stale write overwrites it.
\*
\* FIX variant (InjectBugShrinkTOCTOU = FALSE):
\*   Atomic read+write under single lock hold.  After write, check
\*   if a shrink arrived during reconnect and reapply.
\* ---------------------------------------------------------------
fair process ReconnectGrant = "RG"
variables
    rg_server_grant = 0;  \* local copy of grant from CONNECT reply
begin
RG_Evict:
    \* First, simulate eviction: zero avail, mark evicted
    await loi_lock = "free";
    loi_lock := "RG";

RG_DoEvict:
    cl_avail_grant := 0;
    phase := "evicted";
    loi_lock := "free";

RG_BeginReconnect:
    \* Server CONNECT reply carries server_authorized_grant
    \* Mark phase so ShrinkHandler can fire during this window
    phase := "reconnecting";

RG_AcquireLock1:
    await loi_lock = "free";
    loi_lock := "RG";

RG_ReadServerGrant:
    \* Read the server grant from CONNECT reply
    rg_server_grant := server_authorized_grant;

    if InjectBugShrinkTOCTOU then
        \* BUG: release lock after read, creating TOCTOU window
        loi_lock := "free";
    else
        \* FIX: keep lock held, proceed to write atomically
        skip;
    end if;

RG_MaybeReacquire:
    if InjectBugShrinkTOCTOU then
        \* BUG path: re-acquire lock (ShrinkHandler can interleave here)
        await loi_lock = "free";
        loi_lock := "RG";
    end if;

RG_WriteBack:
    \* Write back: set import grant and compute avail
    if ~InjectBugShrinkTOCTOU /\ shrink_pending then
        \* FIX path: shrink arrived while we held lock during reconnect.
        \* The shrink already updated server_authorized_grant, so use
        \* the current server value, not the stale rg_server_grant.
        cl_import_grant := server_authorized_grant;
        cl_avail_grant := server_authorized_grant - cl_dirty_grant - cl_reserved_grant;
    else
        \* Normal path (bug or no-shrink): use the read value
        cl_import_grant := rg_server_grant;
        cl_avail_grant := rg_server_grant - cl_dirty_grant - cl_reserved_grant;
    end if;
    phase := "connected";
    loi_lock := "free";

RG_Done:
    skip;
end process;

end algorithm; *)
\* BEGIN TRANSLATION - theass://real sym-b://sym translator of PlusCal \* (chksum(pcal) = "b000feed" /\ chksum(tla) = "b000feed")
VARIABLES cl_import_grant, cl_avail_grant, cl_dirty_grant, cl_reserved_grant,
          server_authorized_grant, loi_lock, phase, shrink_pending, pc

(* define statement *)
GrantConservation ==
    phase = "connected" =>
        cl_import_grant <= server_authorized_grant


NoNegativeGrant ==
    cl_import_grant >= 0 /\ cl_avail_grant >= 0 /\
    cl_dirty_grant >= 0 /\ cl_reserved_grant >= 0 /\
    server_authorized_grant >= 0


ClientPoolBounded ==
    cl_avail_grant + cl_dirty_grant + cl_reserved_grant <= cl_import_grant


ServerGrantNonNegative ==
    server_authorized_grant >= 0

VARIABLES w_iter, rg_server_grant

vars == << cl_import_grant, cl_avail_grant, cl_dirty_grant, cl_reserved_grant,
           server_authorized_grant, loi_lock, phase, shrink_pending, pc,
           w_iter, rg_server_grant >>

ProcSet == {"W"} \cup {"SH"} \cup {"RG"}

Init == (* Global variables *)
        /\ cl_import_grant = TOTAL_GRANT
        /\ cl_avail_grant = TOTAL_GRANT
        /\ cl_dirty_grant = 0
        /\ cl_reserved_grant = 0
        /\ server_authorized_grant = TOTAL_GRANT
        /\ loi_lock = "free"
        /\ phase = "pre_eviction"
        /\ shrink_pending = FALSE
        (* Process Writer *)
        /\ w_iter = 0
        (* Process ReconnectGrant *)
        /\ rg_server_grant = 0
        /\ pc = [self \in ProcSet |-> CASE self = "W" -> "W_Start"
                                        [] self = "SH" -> "SH_WaitReconnecting"
                                        [] self = "RG" -> "RG_Evict"]

W_Start == /\ pc["W"] = "W_Start"
           /\ IF w_iter >= MAX_ITER
                 THEN /\ pc' = [pc EXCEPT !["W"] = "W_Done"]
                      /\ UNCHANGED w_iter
                 ELSE /\ w_iter' = w_iter + 1
                      /\ pc' = [pc EXCEPT !["W"] = "W_AcquireLock1"]
           /\ UNCHANGED << cl_import_grant, cl_avail_grant, cl_dirty_grant,
                           cl_reserved_grant, server_authorized_grant,
                           loi_lock, phase, shrink_pending, rg_server_grant >>

W_AcquireLock1 == /\ pc["W"] = "W_AcquireLock1"
                  /\ loi_lock = "free"
                  /\ loi_lock' = "W"
                  /\ pc' = [pc EXCEPT !["W"] = "W_Reserve"]
                  /\ UNCHANGED << cl_import_grant, cl_avail_grant,
                                  cl_dirty_grant, cl_reserved_grant,
                                  server_authorized_grant, phase,
                                  shrink_pending, w_iter, rg_server_grant >>

W_Reserve == /\ pc["W"] = "W_Reserve"
             /\ IF cl_avail_grant >= 1
                   THEN /\ cl_avail_grant' = cl_avail_grant - 1
                        /\ cl_reserved_grant' = cl_reserved_grant + 1
                        /\ loi_lock' = "free"
                        /\ pc' = [pc EXCEPT !["W"] = "W_AcquireLock2"]
                   ELSE /\ loi_lock' = "free"
                        /\ pc' = [pc EXCEPT !["W"] = "W_Start"]
                        /\ UNCHANGED << cl_avail_grant, cl_reserved_grant >>
             /\ UNCHANGED << cl_import_grant, cl_dirty_grant,
                             server_authorized_grant, phase, shrink_pending,
                             w_iter, rg_server_grant >>

W_AcquireLock2 == /\ pc["W"] = "W_AcquireLock2"
                  /\ loi_lock = "free"
                  /\ loi_lock' = "W"
                  /\ pc' = [pc EXCEPT !["W"] = "W_ConsumeDirty"]
                  /\ UNCHANGED << cl_import_grant, cl_avail_grant,
                                  cl_dirty_grant, cl_reserved_grant,
                                  server_authorized_grant, phase,
                                  shrink_pending, w_iter, rg_server_grant >>

W_ConsumeDirty == /\ pc["W"] = "W_ConsumeDirty"
                  /\ cl_reserved_grant' = cl_reserved_grant - 1
                  /\ cl_dirty_grant' = cl_dirty_grant + 1
                  /\ loi_lock' = "free"
                  /\ pc' = [pc EXCEPT !["W"] = "W_Start"]
                  /\ UNCHANGED << cl_import_grant, cl_avail_grant,
                                  server_authorized_grant, phase,
                                  shrink_pending, w_iter, rg_server_grant >>

W_Done == /\ pc["W"] = "W_Done"
          /\ TRUE
          /\ pc' = [pc EXCEPT !["W"] = "Done"]
          /\ UNCHANGED << cl_import_grant, cl_avail_grant, cl_dirty_grant,
                          cl_reserved_grant, server_authorized_grant, loi_lock,
                          phase, shrink_pending, w_iter, rg_server_grant >>

Writer == W_Start \/ W_AcquireLock1 \/ W_Reserve \/ W_AcquireLock2
             \/ W_ConsumeDirty \/ W_Done

SH_WaitReconnecting == /\ pc["SH"] = "SH_WaitReconnecting"
                       /\ phase = "reconnecting" \/ phase = "connected"
                       /\ pc' = [pc EXCEPT !["SH"] = "SH_AcquireLock"]
                       /\ UNCHANGED << cl_import_grant, cl_avail_grant,
                                       cl_dirty_grant, cl_reserved_grant,
                                       server_authorized_grant, loi_lock,
                                       phase, shrink_pending, w_iter,
                                       rg_server_grant >>

SH_AcquireLock == /\ pc["SH"] = "SH_AcquireLock"
                  /\ loi_lock = "free"
                  /\ loi_lock' = "SH"
                  /\ pc' = [pc EXCEPT !["SH"] = "SH_ProcessShrink"]
                  /\ UNCHANGED << cl_import_grant, cl_avail_grant,
                                  cl_dirty_grant, cl_reserved_grant,
                                  server_authorized_grant, phase,
                                  shrink_pending, w_iter, rg_server_grant >>

SH_ProcessShrink == /\ pc["SH"] = "SH_ProcessShrink"
                    /\ server_authorized_grant' = server_authorized_grant - SHRINK_AMOUNT
                    /\ cl_import_grant' = cl_import_grant - SHRINK_AMOUNT
                    /\ IF cl_avail_grant >= SHRINK_AMOUNT
                          THEN /\ cl_avail_grant' = cl_avail_grant - SHRINK_AMOUNT
                          ELSE /\ cl_avail_grant' = 0
                    /\ shrink_pending' = TRUE
                    /\ loi_lock' = "free"
                    /\ pc' = [pc EXCEPT !["SH"] = "SH_Done"]
                    /\ UNCHANGED << cl_dirty_grant, cl_reserved_grant, phase,
                                    w_iter, rg_server_grant >>

SH_Done == /\ pc["SH"] = "SH_Done"
           /\ TRUE
           /\ pc' = [pc EXCEPT !["SH"] = "Done"]
           /\ UNCHANGED << cl_import_grant, cl_avail_grant, cl_dirty_grant,
                           cl_reserved_grant, server_authorized_grant,
                           loi_lock, phase, shrink_pending, w_iter,
                           rg_server_grant >>

ShrinkHandler == SH_WaitReconnecting \/ SH_AcquireLock \/ SH_ProcessShrink
                    \/ SH_Done

RG_Evict == /\ pc["RG"] = "RG_Evict"
            /\ loi_lock = "free"
            /\ loi_lock' = "RG"
            /\ pc' = [pc EXCEPT !["RG"] = "RG_DoEvict"]
            /\ UNCHANGED << cl_import_grant, cl_avail_grant, cl_dirty_grant,
                            cl_reserved_grant, server_authorized_grant, phase,
                            shrink_pending, w_iter, rg_server_grant >>

RG_DoEvict == /\ pc["RG"] = "RG_DoEvict"
              /\ cl_avail_grant' = 0
              /\ phase' = "evicted"
              /\ loi_lock' = "free"
              /\ pc' = [pc EXCEPT !["RG"] = "RG_BeginReconnect"]
              /\ UNCHANGED << cl_import_grant, cl_dirty_grant,
                              cl_reserved_grant, server_authorized_grant,
                              shrink_pending, w_iter, rg_server_grant >>

RG_BeginReconnect == /\ pc["RG"] = "RG_BeginReconnect"
                     /\ phase' = "reconnecting"
                     /\ pc' = [pc EXCEPT !["RG"] = "RG_AcquireLock1"]
                     /\ UNCHANGED << cl_import_grant, cl_avail_grant,
                                     cl_dirty_grant, cl_reserved_grant,
                                     server_authorized_grant, loi_lock,
                                     shrink_pending, w_iter, rg_server_grant >>

RG_AcquireLock1 == /\ pc["RG"] = "RG_AcquireLock1"
                   /\ loi_lock = "free"
                   /\ loi_lock' = "RG"
                   /\ pc' = [pc EXCEPT !["RG"] = "RG_ReadServerGrant"]
                   /\ UNCHANGED << cl_import_grant, cl_avail_grant,
                                   cl_dirty_grant, cl_reserved_grant,
                                   server_authorized_grant, phase,
                                   shrink_pending, w_iter, rg_server_grant >>

RG_ReadServerGrant == /\ pc["RG"] = "RG_ReadServerGrant"
                      /\ rg_server_grant' = server_authorized_grant
                      /\ IF InjectBugShrinkTOCTOU
                            THEN /\ loi_lock' = "free"
                            ELSE /\ TRUE
                                 /\ UNCHANGED loi_lock
                      /\ pc' = [pc EXCEPT !["RG"] = "RG_MaybeReacquire"]
                      /\ UNCHANGED << cl_import_grant, cl_avail_grant,
                                      cl_dirty_grant, cl_reserved_grant,
                                      server_authorized_grant, phase,
                                      shrink_pending, w_iter >>

RG_MaybeReacquire == /\ pc["RG"] = "RG_MaybeReacquire"
                     /\ IF InjectBugShrinkTOCTOU
                           THEN /\ loi_lock = "free"
                                /\ loi_lock' = "RG"
                           ELSE /\ TRUE
                                /\ UNCHANGED loi_lock
                     /\ pc' = [pc EXCEPT !["RG"] = "RG_WriteBack"]
                     /\ UNCHANGED << cl_import_grant, cl_avail_grant,
                                     cl_dirty_grant, cl_reserved_grant,
                                     server_authorized_grant, phase,
                                     shrink_pending, w_iter, rg_server_grant >>

RG_WriteBack == /\ pc["RG"] = "RG_WriteBack"
                /\ IF ~InjectBugShrinkTOCTOU /\ shrink_pending
                      THEN /\ cl_import_grant' = server_authorized_grant
                           /\ cl_avail_grant' = server_authorized_grant - cl_dirty_grant - cl_reserved_grant
                      ELSE /\ cl_import_grant' = rg_server_grant
                           /\ cl_avail_grant' = rg_server_grant - cl_dirty_grant - cl_reserved_grant
                /\ phase' = "connected"
                /\ loi_lock' = "free"
                /\ pc' = [pc EXCEPT !["RG"] = "RG_Done"]
                /\ UNCHANGED << cl_dirty_grant, cl_reserved_grant,
                                server_authorized_grant, shrink_pending,
                                w_iter, rg_server_grant >>

RG_Done == /\ pc["RG"] = "RG_Done"
           /\ TRUE
           /\ pc' = [pc EXCEPT !["RG"] = "Done"]
           /\ UNCHANGED << cl_import_grant, cl_avail_grant, cl_dirty_grant,
                           cl_reserved_grant, server_authorized_grant,
                           loi_lock, phase, shrink_pending, w_iter,
                           rg_server_grant >>

ReconnectGrant == RG_Evict \/ RG_DoEvict \/ RG_BeginReconnect
                     \/ RG_AcquireLock1 \/ RG_ReadServerGrant
                     \/ RG_MaybeReacquire \/ RG_WriteBack \/ RG_Done

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == Writer \/ ShrinkHandler \/ ReconnectGrant
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Writer)
        /\ WF_vars(ShrinkHandler)
        /\ WF_vars(ReconnectGrant)

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

====
