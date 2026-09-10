----------------------- MODULE osc_grant_eviction_race -----------------------
(*
 * Focused sub-model for novel bug discovery in OSC grant accounting
 * during eviction, truncate, wire announce, and grant shrink races.
 *
 * Derived from osc_grant_model.tla.  Explores two specific race patterns:
 *
 *   Direction (1): Eviction + Truncate + WireAnnounce race on lost_grant
 *     - Truncate loops, moving dirty->lost (with borrow-to-avail path)
 *     - WireAnnounce loops, moving lost->wire_dropped
 *     - Eviction zeros avail+lost; interleaving with the above could
 *       cause lost_grant incoherence or accounting drift.
 *
 *   Direction (2): GrantShrink + Eviction TOCTOU
 *     - GrantShrink reads avail under lock, releases lock, re-acquires
 *       to perform shrink.  The TOCTOU window overlaps with eviction
 *       zeroing avail_grant.  The existing fix re-checks under lock;
 *       we verify this holds under all interleavings with looping actors.
 *
 * Key differences from the full model (osc_grant_model.tla):
 *   - 5 processes instead of 11 (~100x smaller state space)
 *   - Looping processes (Writer, GrantShrink, Truncate, WireAnnounce)
 *     expose repeated interaction patterns not tested in the one-shot original
 *   - Auxiliary state (ev_client_snapshot) enables stronger post-eviction
 *     invariants
 *   - No PFL, no DIO, no SyncFallback, no RPC tracking (orthogonal)
 *
 * Processes:
 *   Writer ("W")    - reserve + consume grants, loops MAX_ITER times
 *   GrantShrink ("GS") - TOCTOU shrink, loops MAX_ITER times
 *   Truncate ("TR") - dirty->lost with borrow, loops MAX_ITER times
 *   WireAnnounce ("WA") - lost->wire_dropped, loops MAX_ITER times
 *   Eviction ("EV") - one-shot: zeros avail+lost when dirty > 0
 *   Reconnect ("RN") - models osc_init_grant after eviction
 *
 * Novel bug hypothesis (Reconnect lost_grant leak):
 *   Between eviction (zeroing cl_lost_grant) and reconnect
 *   (osc_init_grant), truncate can drain dirty->lost, accumulating
 *   lost_grant > 0.  If osc_init_grant does NOT zero cl_lost_grant,
 *   the new avail_grant = server_grant - dirty - reserved ignores
 *   lost_grant, creating client-side grant inflation (total > server
 *   authorized).  InjectBugReconnectLostLeak models this omission.
 *
 * SOURCE VERIFICATION RESULT (2026-03-12, bead lustre-design-docs-cx7):
 *   BUG CONFIRMED in Lustre master (lustre/osc/osc_request.c).
 *
 *   osc_init_grant() does NOT zero cl_lost_grant.  The race window:
 *     1. IMP_EVENT_DISCON -> osc_import_event() zeros cl_avail_grant
 *        and cl_lost_grant.
 *     2. Failing RPCs drain dirty via osc_free_grant():
 *        cl_lost_grant += X, cl_dirty_grant -= X.
 *     3. osc_reconnect() zeros cl_lost_grant, reports
 *        ocd_grant = reserved + dirty_current to server.
 *     4. More RPCs fail between osc_reconnect and IMP_EVENT_OCD:
 *        cl_lost_grant += Y, cl_dirty_grant -= Y.
 *     5. IMP_EVENT_OCD -> osc_init_grant():
 *        cl_avail_grant = ocd_grant - cl_dirty_grant - cl_reserved_grant.
 *        cl_lost_grant is NOT zeroed -> remains at Y.
 *
 *   After osc_init_grant: client total = avail + dirty + reserved + lost
 *   = ocd_grant + Y > ocd_grant (Y grants double-counted).
 *
 *   JIRA: LU-19976 (also LU-19977, duplicate filed independently)
 *   Fix: zero cl_lost_grant in osc_init_grant() after setting cl_avail_grant.
 *
 * Source (lustre-release master 47638add78):
 *   lustre/osc/osc_request.c
 *     osc_import_event()           3896-3970  IMP_EVENT_DISCON zeroes
 *                                             cl_avail_grant and
 *                                             cl_lost_grant, 3907-3913
 *                                             (Eviction/EV_Disconnect)
 *     osc_reconnect()              3803-3834  ocd_grant = avail+reserved
 *                                             +dirty, cl_lost_grant = 0,
 *                                             3822-3824
 *     osc_import_event()           3947-3951  IMP_EVENT_OCD ->
 *                                             osc_init_grant()
 *     osc_init_grant()             1002-1066  cl_avail_grant = ocd_grant
 *                                             - reserved - dirty under
 *                                             cl_loi_list_lock 1013-1027;
 *                                             cl_lost_grant NOT touched
 *                                             (Reconnect/RN_InitGrant,
 *                                             the InjectBugReconnectLostLeak
 *                                             = TRUE behaviour)
 *     osc_announce_cached()        664-737    o_dropped clamp and
 *                                             cl_lost_grant -= o_dropped,
 *                                             724-732 (WireAnnounce)
 *     osc_shrink_grant_to_target() 829-879    target re-checked under lock
 *                                             855-863 (GrantShrink)
 *   lustre/osc/osc_cache.c
 *     osc_reserve_grant()          1515-1525  avail -> reserved (Writer)
 *     osc_unreserve_grant_no_wake() 1527-1545 reserved -> dirty (Writer)
 *     osc_free_grant()             1625-1649  dirty -> lost, borrow
 *                                             lost -> avail 1637-1641
 *                                             (Truncate)
 *     osc_extent_truncate()        1024-1144  -> osc_free_grant at 1138
 *     osc_extent_finish()          891-956    unsent extent: lost_grant =
 *                                             oe_grants (932) -> 950
 *
 * Validated against: lustre-release master 47638add78 (2026-09-06)
 * Validation notes: LU-19976 is still Open (LU-19977 closed as its
 *   duplicate) and osc_init_grant() at 47638add78 still does not touch
 *   cl_lost_grant, so InjectBugReconnectLostLeak = TRUE is the code as
 *   it is and = FALSE is the proposed fix.  No model change.
 *)

EXTENDS Integers, TLC

CONSTANTS
    TOTAL_GRANT,
    MAX_ITER,
    EnableReconnect,
    InjectBugReconnectLostLeak

(* --algorithm PlusCal
variables
    \* Grant pool (all protected by cl_loi_list_lock)
    avail_grant = TOTAL_GRANT,
    reserved_grant = 0,
    dirty_grant = 0,
    returned_grant = 0,

    \* Wire protocol tracking
    lost_grant = 0,
    wire_dropped = 0,

    \* Eviction tracking
    evicted = FALSE,

    \* Lock state
    loi_lock = "free",

    \* Auxiliary: snapshot of client-held total at eviction time
    \* Used by EvictedClientTotalBounded invariant
    ev_client_snapshot = 0,

    \* Reconnect tracking
    reconnected = FALSE;

define
    \* Model 32-bit wire width as small number for tractability
    WIRE_MAX == 1

    \* === Core invariants (same as full model) ===

    \* Grant conservation: total grants in the system never change
    GrantConservation ==
        avail_grant + reserved_grant + dirty_grant + returned_grant
        + lost_grant + wire_dropped = TOTAL_GRANT

    \* No negative grants
    GrantsNonNegative ==
        avail_grant >= 0 /\ reserved_grant >= 0 /\
        dirty_grant >= 0 /\ returned_grant >= 0 /\
        lost_grant >= 0

    \* Client-side grant pool can never exceed total
    ClientGrantBounded ==
        avail_grant + reserved_grant + dirty_grant <= TOTAL_GRANT

    \* Dirty grants imply the pool is not fully available
    DirtyImpliesNotAllAvail ==
        dirty_grant > 0 => avail_grant < TOTAL_GRANT

    \* After eviction, client-side total doesn't grow
    EvictedNoNewGrants ==
        evicted => avail_grant + reserved_grant +
                   dirty_grant + lost_grant <=
                   TOTAL_GRANT - wire_dropped

    \* === Novel invariants for eviction race discovery ===

    \* Wire dropped should never go negative
    WireDroppedNonNegative ==
        wire_dropped >= 0

    \* Returned grants should never go negative
    ReturnedNonNegative ==
        returned_grant >= 0

    \* After eviction, the client-held total (avail+reserved+dirty+lost)
    \* should not exceed the snapshot taken at eviction time.
    \* This catches post-eviction grant inflation: if any race creates
    \* grants from thin air (e.g., borrow + shrink interaction), the
    \* client total would exceed the snapshot.
    \*
    \* Note: The snapshot captures reserved+dirty at eviction time
    \* (avail and lost are zeroed by eviction, so they start at 0).
    \* Post-eviction, truncate-borrow can move dirty->avail and
    \* writers can move avail->reserved->dirty, but these are all
    \* internal movements that shouldn't change the total.
    \* GrantShrink moves avail->returned (decreases client total).
    \* WireAnnounce moves lost->wire_dropped (decreases client total).
    EvictedClientTotalBounded ==
        evicted => avail_grant + reserved_grant +
                   dirty_grant + lost_grant <=
                   ev_client_snapshot

    \* Stronger form of EvictedNoNewGrants: after eviction, no process
    \* should create new reserved grants (all pre-eviction reservations
    \* should drain, not grow).  Combined with Writer not checking
    \* eviction status (matching real code), this tests whether the
    \* borrow-from-lost->avail->reserve->dirty cycle is bounded.
    \*
    \* NOTE: This may FAIL if writers legitimately consume borrowed
    \* grants post-eviction. If it fails, the counterexample will
    \* show us the exact interleaving - which is valuable even if
    \* the behavior is "correct by design."
    \*
    \* Disabled by default (not in cfg INVARIANTS), used for exploration.
    EvictedReservedBounded ==
        evicted => reserved_grant = 0

    \* After reconnect, grant conservation must still hold.
    \* This is the key invariant for catching the lost_grant leak:
    \* if osc_init_grant doesn't zero cl_lost_grant, the total
    \* will exceed TOTAL_GRANT after reconnect.
    \*
    \* Note: GrantConservation already checks this, but after reconnect
    \* we reset returned/wire_dropped to 0, so conservation can break
    \* if lost_grant leaked through.
    ReconnectConservation ==
        reconnected =>
            avail_grant + reserved_grant + dirty_grant + returned_grant
            + lost_grant + wire_dropped = TOTAL_GRANT

end define;

\* ---------------------------------------------------------------
\* Writer: models osc_queue_async_io flow (simplified)
\*   Loops MAX_ITER times, each iteration:
\*     1. osc_enter_cache (reserve grant under lock)
\*     2. osc_extent_find (consume grant under lock)
\*   NOTE: Does NOT check eviction status - matching real code where
\*   osc_enter_cache blocks on grant availability regardless of
\*   import state.
\* ---------------------------------------------------------------
fair process Writer = "W"
variables
    w_grants = 0,
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
    if avail_grant >= 1 then
        avail_grant := avail_grant - 1;
        reserved_grant := reserved_grant + 1;
        w_grants := 1;
        loi_lock := "free";
    else
        loi_lock := "free";
        goto W_Done;
    end if;

W_AcquireLock2:
    await loi_lock = "free";
    loi_lock := "W";

W_ConsumeDirty:
    reserved_grant := reserved_grant - 1;
    dirty_grant := dirty_grant + 1;
    w_grants := 0;
    loi_lock := "free";
    goto W_Start;

W_Done:
    skip;
end process;

\* ---------------------------------------------------------------
\* GrantShrink: models osc_shrink_grant_to_target (LU-11288 fix)
\*
\* TOCTOU pattern: read avail under lock, release lock (gap where
\* eviction/writers can change avail), re-acquire lock, re-check
\* before shrinking.
\*
\* Loops MAX_ITER times to test repeated shrink + eviction races.
\* ---------------------------------------------------------------
fair process GrantShrink = "GS"
variables
    gs_target = 0,
    gs_iter = 0;
begin
GS_Start:
    if gs_iter >= MAX_ITER then
        goto GS_Done;
    else
        gs_iter := gs_iter + 1;
    end if;

GS_AcquireLock1:
    await loi_lock = "free";
    loi_lock := "GS";

GS_ReadAvail:
    if avail_grant >= 2 then
        gs_target := 1;
        loi_lock := "free";
    else
        loi_lock := "free";
        goto GS_Start;
    end if;
    \* TOCTOU gap: eviction/writers/truncate can change avail here

GS_AcquireLock2:
    await loi_lock = "free";
    loi_lock := "GS";

GS_Shrink:
    \* FIXED: re-check under lock before shrinking
    if gs_target >= avail_grant then
        \* avail changed (consumed by writers or zeroed by eviction)
        loi_lock := "free";
    else
        \* Safe to shrink: move excess avail to returned
        returned_grant := returned_grant + (avail_grant - gs_target);
        avail_grant := gs_target;
        loi_lock := "free";
    end if;
    goto GS_Start;

GS_Done:
    skip;
end process;

\* ---------------------------------------------------------------
\* Truncate: models osc_free_grant path (dirty->lost with borrow)
\*
\* When pages are truncated, dirty_grant is freed:
\*   cl_dirty_grant -= grants
\*   cl_lost_grant += grants
\*   if cl_avail_grant < grants && cl_lost_grant >= grants:
\*     cl_avail_grant += grants   (borrow from lost)
\*     cl_lost_grant -= grants
\*
\* The borrow-from-lost path restores avail_grant from dirty drain.
\* After eviction, this is the primary path that creates "phantom"
\* available grants.  We loop to test repeated truncate + eviction
\* + wire announce interactions.
\* ---------------------------------------------------------------
fair process Truncate = "TR"
variables
    tr_iter = 0;
begin
TR_Start:
    if tr_iter >= MAX_ITER then
        goto TR_Done;
    else
        tr_iter := tr_iter + 1;
    end if;

TR_AcquireLock:
    await loi_lock = "free" /\ dirty_grant > 0;
    loi_lock := "TR";

TR_FreeGrant:
    if dirty_grant > 0 /\ avail_grant = 0 then
        \* Borrow from lost to avail: dirty->lost->avail
        \* Net effect: dirty-=1, avail+=1, lost unchanged
        dirty_grant := dirty_grant - 1;
        avail_grant := 1;
    elsif dirty_grant > 0 then
        \* Normal: dirty->lost
        dirty_grant := dirty_grant - 1;
        lost_grant := lost_grant + 1;
    end if;
    loi_lock := "free";
    goto TR_Start;

TR_Done:
    skip;
end process;

\* ---------------------------------------------------------------
\* WireAnnounce: models osc_announce_cached (lost->wire_dropped)
\*
\* Sends cl_lost_grant to server via o_dropped wire field.
\* Clamped by WIRE_MAX (32-bit width modeled as 1).
\*
\* Loops to test repeated announcement + eviction races.
\* All under one lock hold (matching real code).
\* ---------------------------------------------------------------
fair process WireAnnounce = "WA"
variables
    wa_to_send = 0,
    wa_iter = 0;
begin
WA_Start:
    if wa_iter >= MAX_ITER then
        goto WA_Done;
    else
        wa_iter := wa_iter + 1;
    end if;

WA_AcquireLock:
    await loi_lock = "free" /\ lost_grant > 0;
    loi_lock := "WA";

WA_PackWire:
    if lost_grant > WIRE_MAX then
        wa_to_send := WIRE_MAX;
    else
        wa_to_send := lost_grant;
    end if;

WA_SendOnWire:
    wire_dropped := wire_dropped + wa_to_send;
    lost_grant := lost_grant - wa_to_send;
    loi_lock := "free";
    goto WA_Start;

WA_Done:
    skip;
end process;

\* ---------------------------------------------------------------
\* Eviction: models osc_import_event IMP_EVENT_DISCON
\*
\* On disconnect:
\*   1. Zero cl_avail_grant and cl_lost_grant
\*   2. Server reclaims those amounts (-> returned_grant in our model)
\*   3. Set evicted flag
\*
\* One-shot: fires when dirty > 0, takes a snapshot of the
\* client-held total for the EvictedClientTotalBounded invariant.
\* ---------------------------------------------------------------
fair process Eviction = "EV"
begin
EV_AcquireLock:
    await loi_lock = "free" /\ dirty_grant > 0 /\ ~evicted;
    loi_lock := "EV";

EV_Disconnect:
    \* Snapshot client-held total BEFORE zeroing avail+lost
    \* After eviction: client total = reserved + dirty (avail,lost zeroed)
    ev_client_snapshot := reserved_grant + dirty_grant;
    \* Server reclaims avail + lost
    returned_grant := returned_grant + avail_grant + lost_grant;
    avail_grant := 0;
    lost_grant := 0;
    evicted := TRUE;
    loi_lock := "free";

EV_Done:
    skip;
end process;

\* ---------------------------------------------------------------
\* Reconnect: models osc_init_grant after eviction
\*
\* After eviction + drain, the server sends fresh grants via
\* osc_init_grant.  The formula:
\*   cl_avail_grant = ocd_grant - cl_dirty_grant - cl_reserved_grant
\*
\* We model the server giving back TOTAL_GRANT (full pool).
\*
\* KEY RACE: Between eviction (which zeroed cl_lost_grant) and
\* reconnect, truncate can accumulate dirty->lost.  If reconnect
\* does NOT zero cl_lost_grant, the stale lost_grant makes the
\* client-side total exceed TOTAL_GRANT.
\*
\* InjectBugReconnectLostLeak = TRUE models the omission:
\*   osc_init_grant ignores cl_lost_grant (leaves it non-zero)
\*
\* InjectBugReconnectLostLeak = FALSE models correct behavior:
\*   osc_init_grant zeros cl_lost_grant (and cl_dirty_grant drains
\*   to lost are handled by subtracting dirty from server grant)
\* ---------------------------------------------------------------
fair process Reconnect = "RN"
begin
RN_WaitEnabled:
    if ~EnableReconnect then
        goto RN_Done;
    end if;

RN_WaitEviction:
    \* Wait until eviction has happened
    await evicted /\ ~reconnected;

RN_AcquireLock:
    await loi_lock = "free";
    loi_lock := "RN";

RN_InitGrant:
    \* osc_init_grant: server gives fresh TOTAL_GRANT
    \* avail = server_grant - dirty - reserved
    avail_grant := TOTAL_GRANT - dirty_grant - reserved_grant;

    if InjectBugReconnectLostLeak then
        \* BUG: do NOT zero cl_lost_grant
        \* Any lost_grant accumulated during dirty drain persists.
        \* This makes total > TOTAL_GRANT, breaking conservation.
        skip;
    else
        \* FIXED: zero cl_lost_grant at reconnect
        \* The lost grants were from the old connection; the server
        \* already reclaimed them at eviction.
        lost_grant := 0;
    end if;

    \* Reset server-side accounting (fresh connection)
    returned_grant := 0;
    wire_dropped := 0;
    evicted := FALSE;
    reconnected := TRUE;
    loi_lock := "free";

RN_Done:
    skip;
end process;

end algorithm; *)
\* BEGIN TRANSLATION
VARIABLES avail_grant, reserved_grant, dirty_grant, returned_grant,
          lost_grant, wire_dropped, evicted, loi_lock, ev_client_snapshot,
          reconnected, pc

(* define statement *)
WIRE_MAX == 1




GrantConservation ==
    avail_grant + reserved_grant + dirty_grant + returned_grant
    + lost_grant + wire_dropped = TOTAL_GRANT


GrantsNonNegative ==
    avail_grant >= 0 /\ reserved_grant >= 0 /\
    dirty_grant >= 0 /\ returned_grant >= 0 /\
    lost_grant >= 0


ClientGrantBounded ==
    avail_grant + reserved_grant + dirty_grant <= TOTAL_GRANT


DirtyImpliesNotAllAvail ==
    dirty_grant > 0 => avail_grant < TOTAL_GRANT


EvictedNoNewGrants ==
    evicted => avail_grant + reserved_grant +
               dirty_grant + lost_grant <=
               TOTAL_GRANT - wire_dropped




WireDroppedNonNegative ==
    wire_dropped >= 0


ReturnedNonNegative ==
    returned_grant >= 0














EvictedClientTotalBounded ==
    evicted => avail_grant + reserved_grant +
               dirty_grant + lost_grant <=
               ev_client_snapshot













EvictedReservedBounded ==
    evicted => reserved_grant = 0









ReconnectConservation ==
    reconnected =>
        avail_grant + reserved_grant + dirty_grant + returned_grant
        + lost_grant + wire_dropped = TOTAL_GRANT

VARIABLES w_grants, w_iter, gs_target, gs_iter, tr_iter, wa_to_send, wa_iter

vars == << avail_grant, reserved_grant, dirty_grant, returned_grant,
           lost_grant, wire_dropped, evicted, loi_lock, ev_client_snapshot,
           reconnected, pc, w_grants, w_iter, gs_target, gs_iter, tr_iter,
           wa_to_send, wa_iter >>

ProcSet == {"W"} \cup {"GS"} \cup {"TR"} \cup {"WA"} \cup {"EV"} \cup {"RN"}

Init == (* Global variables *)
        /\ avail_grant = TOTAL_GRANT
        /\ reserved_grant = 0
        /\ dirty_grant = 0
        /\ returned_grant = 0
        /\ lost_grant = 0
        /\ wire_dropped = 0
        /\ evicted = FALSE
        /\ loi_lock = "free"
        /\ ev_client_snapshot = 0
        /\ reconnected = FALSE
        (* Process Writer *)
        /\ w_grants = 0
        /\ w_iter = 0
        (* Process GrantShrink *)
        /\ gs_target = 0
        /\ gs_iter = 0
        (* Process Truncate *)
        /\ tr_iter = 0
        (* Process WireAnnounce *)
        /\ wa_to_send = 0
        /\ wa_iter = 0
        /\ pc = [self \in ProcSet |-> CASE self = "W" -> "W_Start"
                                        [] self = "GS" -> "GS_Start"
                                        [] self = "TR" -> "TR_Start"
                                        [] self = "WA" -> "WA_Start"
                                        [] self = "EV" -> "EV_AcquireLock"
                                        [] self = "RN" -> "RN_WaitEnabled"]

W_Start == /\ pc["W"] = "W_Start"
           /\ IF w_iter >= MAX_ITER
                 THEN /\ pc' = [pc EXCEPT !["W"] = "W_Done"]
                      /\ UNCHANGED w_iter
                 ELSE /\ w_iter' = w_iter + 1
                      /\ pc' = [pc EXCEPT !["W"] = "W_AcquireLock1"]
           /\ UNCHANGED << avail_grant, reserved_grant, dirty_grant,
                           returned_grant, lost_grant, wire_dropped, evicted,
                           loi_lock, ev_client_snapshot, reconnected, w_grants,
                           gs_target, gs_iter, tr_iter, wa_to_send, wa_iter >>

W_AcquireLock1 == /\ pc["W"] = "W_AcquireLock1"
                  /\ loi_lock = "free"
                  /\ loi_lock' = "W"
                  /\ pc' = [pc EXCEPT !["W"] = "W_Reserve"]
                  /\ UNCHANGED << avail_grant, reserved_grant, dirty_grant,
                                  returned_grant, lost_grant, wire_dropped,
                                  evicted, ev_client_snapshot, reconnected,
                                  w_grants, w_iter, gs_target, gs_iter,
                                  tr_iter, wa_to_send, wa_iter >>

W_Reserve == /\ pc["W"] = "W_Reserve"
             /\ IF avail_grant >= 1
                   THEN /\ avail_grant' = avail_grant - 1
                        /\ reserved_grant' = reserved_grant + 1
                        /\ w_grants' = 1
                        /\ loi_lock' = "free"
                        /\ pc' = [pc EXCEPT !["W"] = "W_AcquireLock2"]
                   ELSE /\ loi_lock' = "free"
                        /\ pc' = [pc EXCEPT !["W"] = "W_Done"]
                        /\ UNCHANGED << avail_grant, reserved_grant, w_grants >>
             /\ UNCHANGED << dirty_grant, returned_grant, lost_grant,
                             wire_dropped, evicted, ev_client_snapshot,
                             reconnected, w_iter, gs_target, gs_iter, tr_iter,
                             wa_to_send, wa_iter >>

W_AcquireLock2 == /\ pc["W"] = "W_AcquireLock2"
                  /\ loi_lock = "free"
                  /\ loi_lock' = "W"
                  /\ pc' = [pc EXCEPT !["W"] = "W_ConsumeDirty"]
                  /\ UNCHANGED << avail_grant, reserved_grant, dirty_grant,
                                  returned_grant, lost_grant, wire_dropped,
                                  evicted, ev_client_snapshot, reconnected,
                                  w_grants, w_iter, gs_target, gs_iter,
                                  tr_iter, wa_to_send, wa_iter >>

W_ConsumeDirty == /\ pc["W"] = "W_ConsumeDirty"
                  /\ reserved_grant' = reserved_grant - 1
                  /\ dirty_grant' = dirty_grant + 1
                  /\ w_grants' = 0
                  /\ loi_lock' = "free"
                  /\ pc' = [pc EXCEPT !["W"] = "W_Start"]
                  /\ UNCHANGED << avail_grant, returned_grant, lost_grant,
                                  wire_dropped, evicted, ev_client_snapshot,
                                  reconnected, w_iter, gs_target, gs_iter,
                                  tr_iter, wa_to_send, wa_iter >>

W_Done == /\ pc["W"] = "W_Done"
          /\ TRUE
          /\ pc' = [pc EXCEPT !["W"] = "Done"]
          /\ UNCHANGED << avail_grant, reserved_grant, dirty_grant,
                          returned_grant, lost_grant, wire_dropped, evicted,
                          loi_lock, ev_client_snapshot, reconnected, w_grants,
                          w_iter, gs_target, gs_iter, tr_iter, wa_to_send,
                          wa_iter >>

Writer == W_Start \/ W_AcquireLock1 \/ W_Reserve \/ W_AcquireLock2
             \/ W_ConsumeDirty \/ W_Done

GS_Start == /\ pc["GS"] = "GS_Start"
            /\ IF gs_iter >= MAX_ITER
                  THEN /\ pc' = [pc EXCEPT !["GS"] = "GS_Done"]
                       /\ UNCHANGED gs_iter
                  ELSE /\ gs_iter' = gs_iter + 1
                       /\ pc' = [pc EXCEPT !["GS"] = "GS_AcquireLock1"]
            /\ UNCHANGED << avail_grant, reserved_grant, dirty_grant,
                            returned_grant, lost_grant, wire_dropped, evicted,
                            loi_lock, ev_client_snapshot, reconnected,
                            w_grants, w_iter, gs_target, tr_iter, wa_to_send,
                            wa_iter >>

GS_AcquireLock1 == /\ pc["GS"] = "GS_AcquireLock1"
                   /\ loi_lock = "free"
                   /\ loi_lock' = "GS"
                   /\ pc' = [pc EXCEPT !["GS"] = "GS_ReadAvail"]
                   /\ UNCHANGED << avail_grant, reserved_grant, dirty_grant,
                                   returned_grant, lost_grant, wire_dropped,
                                   evicted, ev_client_snapshot, reconnected,
                                   w_grants, w_iter, gs_target, gs_iter,
                                   tr_iter, wa_to_send, wa_iter >>

GS_ReadAvail == /\ pc["GS"] = "GS_ReadAvail"
                /\ IF avail_grant >= 2
                      THEN /\ gs_target' = 1
                           /\ loi_lock' = "free"
                           /\ pc' = [pc EXCEPT !["GS"] = "GS_AcquireLock2"]
                      ELSE /\ loi_lock' = "free"
                           /\ pc' = [pc EXCEPT !["GS"] = "GS_Start"]
                           /\ UNCHANGED gs_target
                /\ UNCHANGED << avail_grant, reserved_grant, dirty_grant,
                                returned_grant, lost_grant, wire_dropped,
                                evicted, ev_client_snapshot, reconnected,
                                w_grants, w_iter, gs_iter, tr_iter, wa_to_send,
                                wa_iter >>

GS_AcquireLock2 == /\ pc["GS"] = "GS_AcquireLock2"
                   /\ loi_lock = "free"
                   /\ loi_lock' = "GS"
                   /\ pc' = [pc EXCEPT !["GS"] = "GS_Shrink"]
                   /\ UNCHANGED << avail_grant, reserved_grant, dirty_grant,
                                   returned_grant, lost_grant, wire_dropped,
                                   evicted, ev_client_snapshot, reconnected,
                                   w_grants, w_iter, gs_target, gs_iter,
                                   tr_iter, wa_to_send, wa_iter >>

GS_Shrink == /\ pc["GS"] = "GS_Shrink"
             /\ IF gs_target >= avail_grant
                   THEN /\ loi_lock' = "free"
                        /\ UNCHANGED << avail_grant, returned_grant >>
                   ELSE /\ returned_grant' = returned_grant + (avail_grant - gs_target)
                        /\ avail_grant' = gs_target
                        /\ loi_lock' = "free"
             /\ pc' = [pc EXCEPT !["GS"] = "GS_Start"]
             /\ UNCHANGED << reserved_grant, dirty_grant, lost_grant,
                             wire_dropped, evicted, ev_client_snapshot,
                             reconnected, w_grants, w_iter, gs_target, gs_iter,
                             tr_iter, wa_to_send, wa_iter >>

GS_Done == /\ pc["GS"] = "GS_Done"
           /\ TRUE
           /\ pc' = [pc EXCEPT !["GS"] = "Done"]
           /\ UNCHANGED << avail_grant, reserved_grant, dirty_grant,
                           returned_grant, lost_grant, wire_dropped, evicted,
                           loi_lock, ev_client_snapshot, reconnected, w_grants,
                           w_iter, gs_target, gs_iter, tr_iter, wa_to_send,
                           wa_iter >>

GrantShrink == GS_Start \/ GS_AcquireLock1 \/ GS_ReadAvail
                  \/ GS_AcquireLock2 \/ GS_Shrink \/ GS_Done

TR_Start == /\ pc["TR"] = "TR_Start"
            /\ IF tr_iter >= MAX_ITER
                  THEN /\ pc' = [pc EXCEPT !["TR"] = "TR_Done"]
                       /\ UNCHANGED tr_iter
                  ELSE /\ tr_iter' = tr_iter + 1
                       /\ pc' = [pc EXCEPT !["TR"] = "TR_AcquireLock"]
            /\ UNCHANGED << avail_grant, reserved_grant, dirty_grant,
                            returned_grant, lost_grant, wire_dropped, evicted,
                            loi_lock, ev_client_snapshot, reconnected,
                            w_grants, w_iter, gs_target, gs_iter, wa_to_send,
                            wa_iter >>

TR_AcquireLock == /\ pc["TR"] = "TR_AcquireLock"
                  /\ loi_lock = "free" /\ dirty_grant > 0
                  /\ loi_lock' = "TR"
                  /\ pc' = [pc EXCEPT !["TR"] = "TR_FreeGrant"]
                  /\ UNCHANGED << avail_grant, reserved_grant, dirty_grant,
                                  returned_grant, lost_grant, wire_dropped,
                                  evicted, ev_client_snapshot, reconnected,
                                  w_grants, w_iter, gs_target, gs_iter,
                                  tr_iter, wa_to_send, wa_iter >>

TR_FreeGrant == /\ pc["TR"] = "TR_FreeGrant"
                /\ IF dirty_grant > 0 /\ avail_grant = 0
                      THEN /\ dirty_grant' = dirty_grant - 1
                           /\ avail_grant' = 1
                           /\ UNCHANGED lost_grant
                      ELSE /\ IF dirty_grant > 0
                                 THEN /\ dirty_grant' = dirty_grant - 1
                                      /\ lost_grant' = lost_grant + 1
                                 ELSE /\ TRUE
                                      /\ UNCHANGED << dirty_grant, lost_grant >>
                           /\ UNCHANGED avail_grant
                /\ loi_lock' = "free"
                /\ pc' = [pc EXCEPT !["TR"] = "TR_Start"]
                /\ UNCHANGED << reserved_grant, returned_grant, wire_dropped,
                                evicted, ev_client_snapshot, reconnected,
                                w_grants, w_iter, gs_target, gs_iter, tr_iter,
                                wa_to_send, wa_iter >>

TR_Done == /\ pc["TR"] = "TR_Done"
           /\ TRUE
           /\ pc' = [pc EXCEPT !["TR"] = "Done"]
           /\ UNCHANGED << avail_grant, reserved_grant, dirty_grant,
                           returned_grant, lost_grant, wire_dropped, evicted,
                           loi_lock, ev_client_snapshot, reconnected, w_grants,
                           w_iter, gs_target, gs_iter, tr_iter, wa_to_send,
                           wa_iter >>

Truncate == TR_Start \/ TR_AcquireLock \/ TR_FreeGrant \/ TR_Done

WA_Start == /\ pc["WA"] = "WA_Start"
            /\ IF wa_iter >= MAX_ITER
                  THEN /\ pc' = [pc EXCEPT !["WA"] = "WA_Done"]
                       /\ UNCHANGED wa_iter
                  ELSE /\ wa_iter' = wa_iter + 1
                       /\ pc' = [pc EXCEPT !["WA"] = "WA_AcquireLock"]
            /\ UNCHANGED << avail_grant, reserved_grant, dirty_grant,
                            returned_grant, lost_grant, wire_dropped, evicted,
                            loi_lock, ev_client_snapshot, reconnected,
                            w_grants, w_iter, gs_target, gs_iter, tr_iter,
                            wa_to_send >>

WA_AcquireLock == /\ pc["WA"] = "WA_AcquireLock"
                  /\ loi_lock = "free" /\ lost_grant > 0
                  /\ loi_lock' = "WA"
                  /\ pc' = [pc EXCEPT !["WA"] = "WA_PackWire"]
                  /\ UNCHANGED << avail_grant, reserved_grant, dirty_grant,
                                  returned_grant, lost_grant, wire_dropped,
                                  evicted, ev_client_snapshot, reconnected,
                                  w_grants, w_iter, gs_target, gs_iter,
                                  tr_iter, wa_to_send, wa_iter >>

WA_PackWire == /\ pc["WA"] = "WA_PackWire"
               /\ IF lost_grant > WIRE_MAX
                     THEN /\ wa_to_send' = WIRE_MAX
                     ELSE /\ wa_to_send' = lost_grant
               /\ pc' = [pc EXCEPT !["WA"] = "WA_SendOnWire"]
               /\ UNCHANGED << avail_grant, reserved_grant, dirty_grant,
                               returned_grant, lost_grant, wire_dropped,
                               evicted, loi_lock, ev_client_snapshot,
                               reconnected, w_grants, w_iter, gs_target,
                               gs_iter, tr_iter, wa_iter >>

WA_SendOnWire == /\ pc["WA"] = "WA_SendOnWire"
                 /\ wire_dropped' = wire_dropped + wa_to_send
                 /\ lost_grant' = lost_grant - wa_to_send
                 /\ loi_lock' = "free"
                 /\ pc' = [pc EXCEPT !["WA"] = "WA_Start"]
                 /\ UNCHANGED << avail_grant, reserved_grant, dirty_grant,
                                 returned_grant, evicted, ev_client_snapshot,
                                 reconnected, w_grants, w_iter, gs_target,
                                 gs_iter, tr_iter, wa_to_send, wa_iter >>

WA_Done == /\ pc["WA"] = "WA_Done"
           /\ TRUE
           /\ pc' = [pc EXCEPT !["WA"] = "Done"]
           /\ UNCHANGED << avail_grant, reserved_grant, dirty_grant,
                           returned_grant, lost_grant, wire_dropped, evicted,
                           loi_lock, ev_client_snapshot, reconnected, w_grants,
                           w_iter, gs_target, gs_iter, tr_iter, wa_to_send,
                           wa_iter >>

WireAnnounce == WA_Start \/ WA_AcquireLock \/ WA_PackWire \/ WA_SendOnWire
                   \/ WA_Done

EV_AcquireLock == /\ pc["EV"] = "EV_AcquireLock"
                  /\ loi_lock = "free" /\ dirty_grant > 0 /\ ~evicted
                  /\ loi_lock' = "EV"
                  /\ pc' = [pc EXCEPT !["EV"] = "EV_Disconnect"]
                  /\ UNCHANGED << avail_grant, reserved_grant, dirty_grant,
                                  returned_grant, lost_grant, wire_dropped,
                                  evicted, ev_client_snapshot, reconnected,
                                  w_grants, w_iter, gs_target, gs_iter,
                                  tr_iter, wa_to_send, wa_iter >>

EV_Disconnect == /\ pc["EV"] = "EV_Disconnect"
                 /\ ev_client_snapshot' = reserved_grant + dirty_grant
                 /\ returned_grant' = returned_grant + avail_grant + lost_grant
                 /\ avail_grant' = 0
                 /\ lost_grant' = 0
                 /\ evicted' = TRUE
                 /\ loi_lock' = "free"
                 /\ pc' = [pc EXCEPT !["EV"] = "EV_Done"]
                 /\ UNCHANGED << reserved_grant, dirty_grant, wire_dropped,
                                 reconnected, w_grants, w_iter, gs_target,
                                 gs_iter, tr_iter, wa_to_send, wa_iter >>

EV_Done == /\ pc["EV"] = "EV_Done"
           /\ TRUE
           /\ pc' = [pc EXCEPT !["EV"] = "Done"]
           /\ UNCHANGED << avail_grant, reserved_grant, dirty_grant,
                           returned_grant, lost_grant, wire_dropped, evicted,
                           loi_lock, ev_client_snapshot, reconnected, w_grants,
                           w_iter, gs_target, gs_iter, tr_iter, wa_to_send,
                           wa_iter >>

Eviction == EV_AcquireLock \/ EV_Disconnect \/ EV_Done

RN_WaitEnabled == /\ pc["RN"] = "RN_WaitEnabled"
                  /\ IF ~EnableReconnect
                        THEN /\ pc' = [pc EXCEPT !["RN"] = "RN_Done"]
                        ELSE /\ pc' = [pc EXCEPT !["RN"] = "RN_WaitEviction"]
                  /\ UNCHANGED << avail_grant, reserved_grant, dirty_grant,
                                  returned_grant, lost_grant, wire_dropped,
                                  evicted, loi_lock, ev_client_snapshot,
                                  reconnected, w_grants, w_iter, gs_target,
                                  gs_iter, tr_iter, wa_to_send, wa_iter >>

RN_WaitEviction == /\ pc["RN"] = "RN_WaitEviction"
                   /\ evicted /\ ~reconnected
                   /\ pc' = [pc EXCEPT !["RN"] = "RN_AcquireLock"]
                   /\ UNCHANGED << avail_grant, reserved_grant, dirty_grant,
                                   returned_grant, lost_grant, wire_dropped,
                                   evicted, loi_lock, ev_client_snapshot,
                                   reconnected, w_grants, w_iter, gs_target,
                                   gs_iter, tr_iter, wa_to_send, wa_iter >>

RN_AcquireLock == /\ pc["RN"] = "RN_AcquireLock"
                  /\ loi_lock = "free"
                  /\ loi_lock' = "RN"
                  /\ pc' = [pc EXCEPT !["RN"] = "RN_InitGrant"]
                  /\ UNCHANGED << avail_grant, reserved_grant, dirty_grant,
                                  returned_grant, lost_grant, wire_dropped,
                                  evicted, ev_client_snapshot, reconnected,
                                  w_grants, w_iter, gs_target, gs_iter,
                                  tr_iter, wa_to_send, wa_iter >>

RN_InitGrant == /\ pc["RN"] = "RN_InitGrant"
                /\ avail_grant' = TOTAL_GRANT - dirty_grant - reserved_grant
                /\ IF InjectBugReconnectLostLeak
                      THEN /\ TRUE
                           /\ UNCHANGED lost_grant
                      ELSE /\ lost_grant' = 0
                /\ returned_grant' = 0
                /\ wire_dropped' = 0
                /\ evicted' = FALSE
                /\ reconnected' = TRUE
                /\ loi_lock' = "free"
                /\ pc' = [pc EXCEPT !["RN"] = "RN_Done"]
                /\ UNCHANGED << reserved_grant, dirty_grant,
                                ev_client_snapshot, w_grants, w_iter,
                                gs_target, gs_iter, tr_iter, wa_to_send,
                                wa_iter >>

RN_Done == /\ pc["RN"] = "RN_Done"
           /\ TRUE
           /\ pc' = [pc EXCEPT !["RN"] = "Done"]
           /\ UNCHANGED << avail_grant, reserved_grant, dirty_grant,
                           returned_grant, lost_grant, wire_dropped, evicted,
                           loi_lock, ev_client_snapshot, reconnected, w_grants,
                           w_iter, gs_target, gs_iter, tr_iter, wa_to_send,
                           wa_iter >>

Reconnect == RN_WaitEnabled \/ RN_WaitEviction \/ RN_AcquireLock
                \/ RN_InitGrant \/ RN_Done

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == Writer \/ GrantShrink \/ Truncate \/ WireAnnounce \/ Eviction
           \/ Reconnect
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Writer)
        /\ WF_vars(GrantShrink)
        /\ WF_vars(Truncate)
        /\ WF_vars(WireAnnounce)
        /\ WF_vars(Eviction)
        /\ WF_vars(Reconnect)

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

====
