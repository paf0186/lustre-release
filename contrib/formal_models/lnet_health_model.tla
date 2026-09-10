--------------------------- MODULE lnet_health_model ---------------------------
(*
 * TLA+ specification of LNet peer health tracking and route selection.
 *
 * Models health score maintenance and route selection races in
 * lnet/lnet/peer.c, lnet/lnet/router.c, lnet/lnet/lib-move.c:
 *   - Per-peer-NI health scores (lpni_healthv): atomic, bounded [0, MAX]
 *   - Per-NI health scores (ni_healthv): atomic, bounded [0, MAX]
 *   - Route selection via lnet_select_pathway / lnet_find_preferred_best_ni
 *   - Health decrement on send/receive failure (under net_lock)
 *   - Health increment on successful send/receive
 *   - Peer discovery (lnet_notify): up/down, health reset
 *   - Router sensitivity threshold for alive/dead determination
 *
 * Topology: 2 peers (each with 1 peer_ni), 1 local NI, 1 router
 * Health values scaled: MAX=2, sensitivity=1 for tractable state space.
 *
 * Known bugs modeled:
 *   LU-18444: Router sensitivity cascading failure - threshold-based alive
 *             check kills route even when health > 0.
 *   LU-13472: Stale route aliveness when discovery toggled off.
 *   LU-14783: Route reactivation delay - peer recovers but route stays
 *             down until monitor thread runs.
 *
 * Source (lustre-release master 47638add78):
 *   include/linux/lnet/lib-types.h:75       LNET_MAX_HEALTH_VALUE (HEALTH_MAX)
 *   lnet/lnet/api-ni.c:73-82                lnet_health_sensitivity (SENSITIVITY)
 *   lnet/lnet/router.c:92-139               router_sensitivity_percentage
 *                                           (ROUTER_SENSITIVITY; deprecated
 *                                           since LU-18444, no longer used
 *                                           for aliveness)
 *   include/linux/lnet/lib-lnet.h:1184-1197 lnet_dec_healthv_locked (DecHealth)
 *   include/linux/lnet/lib-lnet.h:1219-1223 lnet_inc_healthv (IncHealth)
 *   include/linux/lnet/lib-lnet.h:1200-1216 lnet_dec_ni_healthv_locked /
 *                                           lnet_dec_lpni_healthv_locked
 *   include/linux/lnet/lib-lnet.h:1226-1242 lnet_inc_ni_healthv (lock-free
 *                                           local NI increment, Hr_Do) /
 *                                           lnet_inc_lpni_healthv_locked
 *   include/linux/lnet/lib-lnet.h:1144-1150 lnet_set_lpni_healthv_locked
 *   include/linux/lnet/lib-lnet.h:1121-1124 lnet_is_peer_ni_alive
 *                                           (lpni_ns_status; peerN_alive,
 *                                           router_gw_alive)
 *   include/linux/lnet/lib-lnet.h:1272-1282 lnet_set_route_aliveness
 *                                           (lr_alive; route_alive)
 *   lnet/lnet/lib-msg.c:836-1028            lnet_health_check (SendFail
 *                                           dispatch 994-1027; success path
 *                                           947-992: lnet_inc_ni_healthv 954
 *                                           lock-free, peer NI increment or
 *                                           set-to-MAX for routers 965-989
 *                                           under lnet_net_lock(0))
 *   lnet/lnet/lib-msg.c:540-558             lnet_handle_local_failure
 *                                           (lnet_net_lock(0), Fl_Do)
 *   lnet/lnet/lib-msg.c:562-593             lnet_handle_remote_failure[_locked]
 *                                           (lnet_net_lock(0), Fl_Do)
 *   lnet/lnet/lib-move.c:3636-3777          lnet_recover_peer_nis
 *                                           (HealthRecover: monitor thread
 *                                           pings peer NIs on the recovery
 *                                           queue)
 *   lnet/lnet/peer.c:4727-4775              lnet_peer_ni_add_to_recoveryq_locked
 *   lnet/lnet/lib-move.c:2868-3041          lnet_select_pathway (RouteSelect,
 *                                           under lnet_net_lock(cpt))
 *   lnet/lnet/lib-move.c:1144-1250          lnet_select_peer_ni (health
 *                                           preference among peer NIs)
 *   lnet/lnet/lib-move.c:1298-1332          lnet_compare_gw_lpnis (health
 *                                           preference among gateways)
 *   lnet/lnet/lib-move.c:1382-1476          lnet_find_route_locked
 *   lnet/lnet/router.c:282-334              lnet_is_route_alive (lp_alive;
 *                                           cached lr_alive only when
 *                                           discovery is disabled 299-300,
 *                                           else lnet_is_gateway_net_alive)
 *   lnet/lnet/router.c:244-280              lnet_is_gateway_net_alive /
 *                                           lnet_is_gateway_alive
 *   lnet/lnet/router.c:380-448              lnet_router_discovery_ping_reply
 *                                           (Pd_Do monitor: lr_alive from
 *                                           the ping reply)
 *   lnet/lnet/router.c:451-481              lnet_router_discovery_complete
 *   lnet/lnet/router.c:1119-1328            lnet_check_routers (monitor
 *                                           thread gateway pings)
 *   lnet/lnet/router.c:1776-1929            lnet_notify (Pd_Do notify_up /
 *                                           notify_down: lp_alive 1857-1859,
 *                                           lr_alive when discovery disabled
 *                                           1863-1877, lpni_ns_status
 *                                           1892-1893, health set to MAX on
 *                                           up+reset 1906-1907)
 *   lnet/lnet/api-ni.c:138-149              lnet_peer_discovery_disabled
 *                                           (discovery_enabled)
 *
 * Validated against: lustre-release master 47638add78 (2026-09-06)
 * Validation notes:
 *   - Health arithmetic and locking match: decrement/increment by
 *     lnet_health_sensitivity clamped to [0, LNET_MAX_HEALTH_VALUE],
 *     peer NI health changed under lnet_net_lock(0), local NI increment
 *     lock-free (atomic).  Source refs added (there were none).
 *   - LU-18444 was fixed in two steps after the modeled threshold bug:
 *     70c5f58403 (2024-09) "Use only NI status for route aliveness" and
 *     98c6b29359 (2024-12) "Remove per-peer health sensitivity".  In this
 *     tree lnet_is_route_alive() uses only lp_alive and lpni_ns_status;
 *     health is a preference in lnet_compare_gw_lpnis(), never an
 *     alive/dead gate, and router_sensitivity_percentage is deprecated.
 *     The model's router_gw_alive abstracts lpni_ns_status/lp_alive and
 *     is coupled to health (0 <=> down) as a modeling device, so the
 *     InjectBug18444 = FALSE branches (route_alive tracks router_gw_alive)
 *     match the code's rule; the threshold branch is the pre-70c5f58403
 *     behavior.
 *   - LU-13472 (eee4358d9d, 2020): the cached lr_alive is now consulted
 *     only when discovery is disabled (router.c:299-300) and is kept
 *     current by lnet_notify (router.c:1863-1877) and the discovery ping
 *     reply (router.c:380-448); with discovery enabled aliveness is
 *     computed on the fly.
 *   - LU-14783 is still Open in JIRA (no fix commit in the tree).  In this
 *     tree lnet_notify(alive=true, reset=true) sets lp_alive and
 *     lpni_ns_status immediately (router.c:1857-1859, 1892-1893) and
 *     lnet_is_route_alive() is evaluated dynamically when discovery is
 *     enabled, so the InjectBug14783 = FALSE behavior corresponds to the
 *     current code; the TRUE variant has no counterpart here.
 *   - Known abstractions (not drift): Fl_Do decrements local NI health on
 *     every failure, while the code only does so for local failures and
 *     NETWORK_TIMEOUT (lib-msg.c:994-1027); a successful receive from a
 *     router sets its peer NI health to MAX in one step (lib-msg.c:
 *     974-976) rather than incrementing by SENSITIVITY.
 *
 * Concurrency model:
 *   net_lock protects all health modifications and route selection.
 *   Each process: (1) pick action unlocked, (2) acquire lock + work + release.
 *   Lock serialization means races only occur across lock-release boundaries.
 *   Local NI health increment is lock-free (atomic) - modeled separately.
 *)

EXTENDS Integers, TLC

CONSTANTS
    InjectBug18444,     \* Router sensitivity cascading failure
    InjectBug13472,     \* Stale route aliveness on discovery toggle
    InjectBug14783,     \* Route reactivation delay after recovery
    HEALTH_MAX,         \* LNET_MAX_HEALTH_VALUE (scaled down)
    SENSITIVITY,        \* lnet_health_sensitivity (scaled)
    ROUTER_SENSITIVITY  \* router_sensitivity_percentage

VARIABLES
    \* Per-peer-NI health (atomic_t lpni_healthv)
    peer1_health, peer2_health, router_gw_health,
    \* Local NI health
    local_ni_health,
    \* Peer alive status (lpni_ns_status)
    peer1_alive, peer2_alive, router_gw_alive,
    \* Route state (lr_alive)
    route_alive,
    \* Discovery state
    discovery_enabled,
    \* Lock state
    net_lock,
    \* Route selection result (written under lock, read after release)
    selected_peer, selected_health,
    \* Per-process program counter
    pc,
    \* Process-local: what target/action was chosen
    fl_target,    \* SendFail target
    hr_target,    \* HealthRecover target
    pd_action     \* PeerDiscovery action

vars == << peer1_health, peer2_health, router_gw_health, local_ni_health,
           peer1_alive, peer2_alive, router_gw_alive, route_alive,
           discovery_enabled, net_lock, selected_peer, selected_health,
           pc, fl_target, hr_target, pd_action >>

\* Router threshold: health must be >= this to be "alive" under LU-18444
router_threshold == (HEALTH_MAX * ROUTER_SENSITIVITY) \div 100

\* Helpers
DecHealth(h) == IF h >= SENSITIVITY THEN h - SENSITIVITY ELSE 0
IncHealth(h) == IF h + SENSITIVITY <= HEALTH_MAX
                THEN h + SENSITIVITY ELSE HEALTH_MAX

\* === INVARIANTS ===

\* (a) Never select a peer with health=0 (snapshot health must be > 0)
NeverRouteToDeadPeer ==
    selected_peer /= "none" => selected_health > 0

\* (b) Health scores bounded [0, HEALTH_MAX]
HealthBounded ==
    /\ peer1_health >= 0      /\ peer1_health <= HEALTH_MAX
    /\ peer2_health >= 0      /\ peer2_health <= HEALTH_MAX
    /\ router_gw_health >= 0  /\ router_gw_health <= HEALTH_MAX
    /\ local_ni_health >= 0   /\ local_ni_health <= HEALTH_MAX

\* (c) Route not overly aggressive: gateway alive+healthy => route alive
\* Violated by LU-18444 where threshold kills route at health > 0
RouteNotOverlyAggressive ==
    (router_gw_alive /\ router_gw_health > 0) => route_alive

\* (d) Alive consistent with health: health=0 => not alive
AliveConsistentWithHealth ==
    /\ (peer1_health = 0 => ~peer1_alive)
    /\ (peer2_health = 0 => ~peer2_alive)
    /\ (router_gw_health = 0 => ~router_gw_alive)

\* (e) Route alive implies gateway alive (LU-14783)
RouteImpliesGatewayAlive ==
    router_gw_alive => route_alive

\* (f) Discovery toggle: down gateway + no discovery => route down (LU-13472)
DiscoveryToggleSafe ==
    (~discovery_enabled /\ ~router_gw_alive) => ~route_alive

\* (g) Route selection consistency: snapshot matches actual at decision time.
\*     This is inherently violated by the TOCTOU between lock release and
\*     send -- a KNOWN DESIGN TRADE-OFF in LNet.  Health can change between
\*     selection (under net_lock) and use (after lock release).  LNet accepts
\*     this: the cost of holding net_lock through the entire send path would
\*     be prohibitive.  The worst case is sending to a peer whose health
\*     just dropped -- the send will fail and health will be decremented,
\*     triggering retry on a different path.  No data loss.
RouteSelectionConsistent ==
    selected_peer /= "none" =>
        CASE selected_peer = "peer1"  -> selected_health = peer1_health
          [] selected_peer = "peer2"  -> selected_health = peer2_health
          [] selected_peer = "router" -> selected_health = router_gw_health
          [] OTHER -> TRUE

\* ================================================================
\* Initial state
\* ================================================================
Init ==
    /\ peer1_health = HEALTH_MAX
    /\ peer2_health = HEALTH_MAX
    /\ router_gw_health = HEALTH_MAX
    /\ local_ni_health = HEALTH_MAX
    /\ peer1_alive = TRUE
    /\ peer2_alive = TRUE
    /\ router_gw_alive = TRUE
    /\ route_alive = TRUE
    /\ discovery_enabled = TRUE
    /\ net_lock = "free"
    /\ selected_peer = "none"
    /\ selected_health = 0
    /\ pc = [p \in {"Fl", "Hr", "Rs", "Pd"} |->
                CASE p = "Fl" -> "Fl_Pick"
                  [] p = "Hr" -> "Hr_Pick"
                  [] p = "Rs" -> "Rs_Lock"
                  [] p = "Pd" -> "Pd_Pick"
                  [] OTHER -> "done"]
    /\ fl_target = "none"
    /\ hr_target = "none"
    /\ pd_action = "none"

\* ================================================================
\* SendFail: message send failure (lib-msg.c)
\* Pick target (unlocked), then acquire lock + dec health + release
\* ================================================================

Fl_Pick ==
    /\ pc["Fl"] = "Fl_Pick"
    /\ \E tgt \in {"peer1", "peer2", "router"} :
        /\ fl_target' = tgt
        /\ pc' = [pc EXCEPT !["Fl"] = "Fl_Do"]
    /\ UNCHANGED << peer1_health, peer2_health, router_gw_health,
                    local_ni_health, peer1_alive, peer2_alive,
                    router_gw_alive, route_alive, discovery_enabled,
                    net_lock, selected_peer, selected_health,
                    hr_target, pd_action >>

\* Acquire lock, decrement health, update alive/route, release lock
Fl_Do ==
    /\ pc["Fl"] = "Fl_Do"
    /\ net_lock = "free"
    /\ LET newP1 == IF fl_target = "peer1" THEN DecHealth(peer1_health)
                     ELSE peer1_health
           newP2 == IF fl_target = "peer2" THEN DecHealth(peer2_health)
                     ELSE peer2_health
           newRt == IF fl_target = "router" THEN DecHealth(router_gw_health)
                     ELSE router_gw_health
           newP1a == IF newP1 = 0 THEN FALSE ELSE peer1_alive
           newP2a == IF newP2 = 0 THEN FALSE ELSE peer2_alive
           newRta == IF newRt = 0 THEN FALSE ELSE router_gw_alive
           newRoute == IF fl_target = "router"
                       THEN IF InjectBug13472 /\ ~discovery_enabled
                            THEN route_alive  \* BUG 13472: stale route, discovery off
                            ELSE IF InjectBug18444
                                 THEN IF newRt < router_threshold
                                      THEN FALSE ELSE route_alive
                                 ELSE IF newRt = 0 THEN FALSE
                                      ELSE route_alive
                       ELSE route_alive
           newNI == DecHealth(local_ni_health)
       IN /\ peer1_health' = newP1
          /\ peer2_health' = newP2
          /\ router_gw_health' = newRt
          /\ local_ni_health' = newNI
          /\ peer1_alive' = newP1a
          /\ peer2_alive' = newP2a
          /\ router_gw_alive' = newRta
          /\ route_alive' = newRoute
    /\ pc' = [pc EXCEPT !["Fl"] = "Fl_Pick"]
    /\ UNCHANGED << discovery_enabled, net_lock, selected_peer,
                    selected_health, fl_target, hr_target, pd_action >>

SendFail == Fl_Pick \/ Fl_Do

\* ================================================================
\* HealthRecover: periodic health recovery (peer.c)
\* Pick target (unlocked), then acquire lock + inc health + release
\* Local NI increment is lock-free (atomic) - no lock needed
\* ================================================================

Hr_Pick ==
    /\ pc["Hr"] = "Hr_Pick"
    /\ \E tgt \in {"peer1", "peer2", "router", "local_ni"} :
        /\ hr_target' = tgt
        /\ pc' = [pc EXCEPT !["Hr"] = "Hr_Do"]
    /\ UNCHANGED << peer1_health, peer2_health, router_gw_health,
                    local_ni_health, peer1_alive, peer2_alive,
                    router_gw_alive, route_alive, discovery_enabled,
                    net_lock, selected_peer, selected_health,
                    fl_target, pd_action >>

Hr_Do ==
    /\ pc["Hr"] = "Hr_Do"
    /\ IF hr_target = "local_ni"
       THEN \* Lock-free atomic increment for local NI
            /\ local_ni_health' = IncHealth(local_ni_health)
            /\ UNCHANGED << peer1_health, peer2_health, router_gw_health,
                            peer1_alive, peer2_alive, router_gw_alive,
                            route_alive, discovery_enabled, net_lock >>
       ELSE \* Peer health: requires net_lock
            /\ net_lock = "free"
            /\ LET newP1 == IF hr_target = "peer1"
                            THEN IncHealth(peer1_health) ELSE peer1_health
                   newP2 == IF hr_target = "peer2"
                            THEN IncHealth(peer2_health) ELSE peer2_health
                   newRt == IF hr_target = "router"
                            THEN IncHealth(router_gw_health)
                            ELSE router_gw_health
                   newP1a == IF newP1 > 0 THEN TRUE ELSE peer1_alive
                   newP2a == IF newP2 > 0 THEN TRUE ELSE peer2_alive
                   newRta == IF newRt > 0 THEN TRUE ELSE router_gw_alive
                   newRoute == IF hr_target = "router"
                               THEN IF InjectBug14783
                                    THEN route_alive
                                    ELSE IF newRt > 0 THEN TRUE
                                         ELSE route_alive
                               ELSE route_alive
               IN /\ peer1_health' = newP1
                  /\ peer2_health' = newP2
                  /\ router_gw_health' = newRt
                  /\ peer1_alive' = newP1a
                  /\ peer2_alive' = newP2a
                  /\ router_gw_alive' = newRta
                  /\ route_alive' = newRoute
                  /\ UNCHANGED << local_ni_health, discovery_enabled,
                                  net_lock >>
    /\ pc' = [pc EXCEPT !["Hr"] = "Hr_Pick"]
    /\ UNCHANGED << selected_peer, selected_health, fl_target,
                    hr_target, pd_action >>

HealthRecover == Hr_Pick \/ Hr_Do

\* ================================================================
\* RouteSelect: lnet_select_pathway (lib-move.c)
\* Acquire lock, read health, select best, record, release lock,
\* then use selection (after lock release, health may have changed)
\* ================================================================

\* Acquire lock + read + select + record + release (all under lock)
Rs_Lock ==
    /\ pc["Rs"] = "Rs_Lock"
    /\ net_lock = "free"
    /\ LET best == IF route_alive /\ router_gw_health > 0
                      /\ router_gw_health > peer1_health
                      /\ router_gw_health > peer2_health
                   THEN "router"
                   ELSE IF peer1_health >= peer2_health /\ peer1_health > 0
                        THEN "peer1"
                        ELSE IF peer2_health > 0
                             THEN "peer2"
                             ELSE "none"
           health == CASE best = "peer1"  -> peer1_health
                       [] best = "peer2"  -> peer2_health
                       [] best = "router" -> router_gw_health
                       [] OTHER -> 0
       IN /\ selected_peer' = best
          /\ selected_health' = health
    /\ pc' = [pc EXCEPT !["Rs"] = "Rs_Use"]
    /\ UNCHANGED << peer1_health, peer2_health, router_gw_health,
                    local_ni_health, peer1_alive, peer2_alive,
                    router_gw_alive, route_alive, discovery_enabled,
                    net_lock, fl_target, hr_target, pd_action >>

\* Use selection (after lock release - health may have changed!)
Rs_Use ==
    /\ pc["Rs"] = "Rs_Use"
    /\ selected_peer' = "none"
    /\ selected_health' = 0
    /\ pc' = [pc EXCEPT !["Rs"] = "Rs_Lock"]
    /\ UNCHANGED << peer1_health, peer2_health, router_gw_health,
                    local_ni_health, peer1_alive, peer2_alive,
                    router_gw_alive, route_alive, discovery_enabled,
                    net_lock, fl_target, hr_target, pd_action >>

RouteSelect == Rs_Lock \/ Rs_Use

\* ================================================================
\* PeerDiscovery: lnet_notify + discovery toggle + monitor (router.c)
\* Pick action (unlocked), then acquire lock + execute + release
\* ================================================================

Pd_Pick ==
    /\ pc["Pd"] = "Pd_Pick"
    /\ \E act \in {"notify_up", "notify_down", "toggle_disc", "monitor"} :
        /\ pd_action' = act
        /\ pc' = [pc EXCEPT !["Pd"] = "Pd_Do"]
    /\ UNCHANGED << peer1_health, peer2_health, router_gw_health,
                    local_ni_health, peer1_alive, peer2_alive,
                    router_gw_alive, route_alive, discovery_enabled,
                    net_lock, selected_peer, selected_health,
                    fl_target, hr_target >>

Pd_Do ==
    /\ pc["Pd"] = "Pd_Do"
    /\ net_lock = "free"
    /\ IF pd_action = "notify_up"
       THEN /\ router_gw_alive' = TRUE
            /\ router_gw_health' = HEALTH_MAX
            /\ IF InjectBug14783
               THEN route_alive' = route_alive
               ELSE route_alive' = TRUE
            /\ UNCHANGED << peer1_health, peer2_health, local_ni_health,
                            peer1_alive, peer2_alive, discovery_enabled >>
       ELSE IF pd_action = "notify_down"
            THEN /\ router_gw_alive' = FALSE
                 /\ router_gw_health' = 0
                 /\ route_alive' = FALSE
                 /\ UNCHANGED << peer1_health, peer2_health, local_ni_health,
                                 peer1_alive, peer2_alive, discovery_enabled >>
            ELSE IF pd_action = "toggle_disc"
                 THEN /\ IF discovery_enabled
                         THEN /\ discovery_enabled' = FALSE
                              /\ IF InjectBug13472
                                 THEN route_alive' = route_alive
                                 ELSE IF ~router_gw_alive
                                      THEN route_alive' = FALSE
                                      ELSE route_alive' = route_alive
                         ELSE /\ discovery_enabled' = TRUE
                              /\ UNCHANGED route_alive
                      /\ UNCHANGED << peer1_health, peer2_health,
                                      router_gw_health, local_ni_health,
                                      peer1_alive, peer2_alive,
                                      router_gw_alive >>
                 ELSE \* monitor: re-evaluate route aliveness
                      /\ route_alive' = IF router_gw_alive
                                        THEN IF InjectBug18444
                                             THEN router_gw_health >= router_threshold
                                             ELSE TRUE
                                        ELSE FALSE
                      /\ UNCHANGED << peer1_health, peer2_health,
                                      router_gw_health, local_ni_health,
                                      peer1_alive, peer2_alive,
                                      router_gw_alive, discovery_enabled >>
    /\ pc' = [pc EXCEPT !["Pd"] = "Pd_Pick"]
    /\ UNCHANGED << net_lock, selected_peer, selected_health,
                    fl_target, hr_target, pd_action >>

PeerDiscovery == Pd_Pick \/ Pd_Do

\* ================================================================
\* Specification
\* ================================================================

Next == SendFail \/ HealthRecover \/ RouteSelect \/ PeerDiscovery

Spec == Init /\ [][Next]_vars
        /\ WF_vars(SendFail)
        /\ WF_vars(HealthRecover)
        /\ WF_vars(RouteSelect)
        /\ WF_vars(PeerDiscovery)

=============================================================================
