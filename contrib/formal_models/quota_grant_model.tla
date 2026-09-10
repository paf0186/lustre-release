--------------------- MODULE quota_grant_model ---------------------
(*
 * TLA+ model of the Lustre QSD/QMT quota grant exchange protocol.
 *
 * Models a two-client scenario where each client's Quota Slave Daemon
 * (QSD) acquires quota slabs from the server's Quota Master Target (QMT).
 * The QMT enforces a hard per-ID limit: the sum of all QSD grants must
 * not exceed QMT_LIMIT.
 *
 * Architecture:
 *   QMT: tracks qmt_granted (total granted to all clients, <= QMT_LIMIT).
 *   Per-client: qsd_avail (locally available), qsd_inuse (held by writers),
 *               reclaim_rpc (units in-transit back to QMT).
 *
 * Protocol:
 *   1. Writers acquire 1 unit at a time from qsd_avail.
 *   2. When qsd_avail is depleted, QSD sends a replenish request to QMT.
 *   3. QMT computes headroom (QMT_LIMIT - qmt_granted) and grants a slab.
 *   4. QSD receives the grant slab, adds it to qsd_avail.
 *   5. Writers release quota back to qsd_avail when done.
 *   6. When qsd_avail has surplus, QSD reclaims some units to QMT.
 *      The reclaim amount is non-deterministic (1..qsd_avail-1).
 *
 * Rebalance protocol (EnableRebalance=TRUE):
 *   7. QMT asks a client to shrink (return some grant units).
 *   8. Client processes the shrink, returning what it can (may be less
 *      than requested if quota is in use).
 *
 * Soft limit / grace period (SOFT_LIMIT > 0):
 *   Grace period models the window where a user has exceeded the soft
 *   limit and the grace timer has expired.  After grace expiry, the
 *   effective limit drops to SOFT_LIMIT.  The model non-deterministically
 *   fires GraceExpire when qmt_granted <= SOFT_LIMIT (user was briefly
 *   below soft limit, then grace context latched).
 *
 * Conservation law (holds at every reachable state):
 *   sum_c(qsd_avail[c] + qsd_inuse[c] + reclaim_rpc[c]) = qmt_granted
 *
 * Primary safety invariant:
 *   qmt_granted <= QMT_LIMIT   (hard quota limit never exceeded)
 *
 * Bug injections:
 *
 *   InjectBugReplenishRace:
 *     QMT computes grant headroom as:
 *       QMT_LIMIT - qmt_granted + TotalPendingReclaim
 *     anticipating that in-flight reclaims from clients will soon reduce
 *     qmt_granted.  If reclaims are delayed, a new grant pushes qmt_granted
 *     above QMT_LIMIT.
 *
 *   InjectBugRebalanceDouble:
 *     QMT includes pending rebalance shrink amounts in headroom:
 *       limit - qmt_granted + TotalRebalancePending
 *     If the shrink response returns less than requested (client used
 *     some quota), qmt_granted exceeds QMT_LIMIT.
 *
 *   InjectBugRebalanceLoss:
 *     When processing a partial rebalance return, QMT deducts the full
 *     requested amount instead of the actual returned amount.  This
 *     causes qmt_granted to drop below the real total, violating
 *     conservation (quota units "disappear").
 *
 *   InjectBugGraceEnforce:
 *     After grace period expires, QMT continues using QMT_LIMIT instead
 *     of SOFT_LIMIT.  Clients get grants above the soft limit even
 *     though the grace period has elapsed.
 *
 *   InjectBugUncheckedAcquire (LU-19018):
 *     fallocate() bypasses quota enforcement entirely: it allocates space
 *     without consuming any QSD grant, creating phantom usage not backed
 *     by a QMT grant.  Violates the conservation invariant.
 *
 *   InjectBugStaleGrant (LU-16097):
 *     Admin reduces the effective quota limit (ADMIN_LIMIT < QMT_LIMIT),
 *     but QMT still grants up to QMT_LIMIT instead of ADMIN_LIMIT.
 *     Pre-acquired grants at clients are not reclaimed, so total grants
 *     exceed the admin-set limit.
 *
 *   InjectBugSoftLimit (LU-19503):
 *     After the grace period expires (modeled by QMT_SOFT_LIMIT > 0 in
 *     the cfg), QMT should enforce the soft limit as the effective ceiling.
 *     The bug ignores the expired grace and keeps granting up to the hard
 *     limit, allowing usage to exceed the soft limit.
 *
 *   InjectBugBrwSync (LU-19791):
 *     Pages already accepted into the client cache (OBD_BRW_ASYNC) were
 *     subjected to the OST-side quota check when root_prj_enable was
 *     set and root was over its project quota on another client; the
 *     OST returned -EDQUOT and the cached data was silently dropped,
 *     the application never being notified.  (The constant name comes
 *     from an earlier reading of the bug that blamed osc_page_submit()
 *     setting OBD_BRW_SYNC; that flag is set only on the immediate/sync
 *     transfer path and the fix was server-side, see Source below.)
 *
 * Related Lustre bugs:
 *   LU-19629: default quotas ignored for IDs with deleted explicit limits
 *   LU-19791: writes silently dropped on quota-exceeded path (OBD_BRW_SYNC)
 *   LU-19018: fallocate bypasses quota limits
 *   LU-16097: pre-allocated quota not reclaimed after limit reduction
 *   LU-19503: soft limit not enforced after grace period
 *   LU-14764: single OST quotas out of sync (rebalance headroom race)
 *   LU-11929: "Release too much!" (rebalance partial return over-deduction)
 *   LU-18612: stale over-softlimit flag after file removal
 *
 * Uses Symmetry = {Client1, Client2} in cfg to reduce state space.
 *
 * Source (lustre-release master 47638add78):
 *   Slave side (QSD), lustre/quota/qsd_handler.c, lqe_write_lock:
 *     qsd_op_begin()/qsd_op_begin0()  838-914 / 684-807
 *                                     lqe_waiting_write += space 728,
 *                                     qsd_acquire loop 737 (WriterAcquire)
 *     qsd_acquire()                   610-663   local first (633), then
 *                                     remote (655)
 *     qsd_acquire_local()             418-453   space + usage <=
 *                                     lqe_granted - lqe_pending_rel, 435
 *     qsd_calc_acquire()              467-493   qb_count = usage - granted
 *     qsd_acquire_remote()            508-594   DQACQ to QMT (QMTGrant)
 *     qsd_req_completion()            262-406   lqe_granted -= qb_count on
 *                                     release 327, += on acquire 337
 *                                     (QMTGrant / QSDReclaim completion)
 *     qsd_op_end0()                   1042-1086 lqe_pending_write -= 1066,
 *                                     qsd_adjust (WriterRelease)
 *     qsd_calc_adjust()               105-247   revoke all extra grant
 *                                     183-195 (LU-16097 57ac32a223),
 *                                     pre-release surplus 197-213
 *                                     (QSDReclaim), pre-acquire 227-241
 *   lustre/quota/qsd_lock.c
 *     qsd_id_glimpse_ast()            401-485   QMT-driven release:
 *                                     lvb_id_may_rel 450 or lqe_granted
 *                                     -= space 456 (QSDProcessRebalance);
 *                                     edquot 473, revoke adjust 477
 *   lustre/quota/qsd_writeback.c 350  LQUOTA_FLAG_REVOKE -> lqe_revoke
 *   Master side (QMT), lustre/quota/qmt_handler.c, qti_lqes_write_lock:
 *     qmt_dqacq0()                    965-1205  release: rejects rel >
 *                                     granted ("Release too much!",
 *                                     1053-1061), else qmt_rel_lqes 1065
 *                                     (QMTReceiveReclaim); edquot 1081;
 *                                     qmt_space_exhausted_lqes 1085
 *                                     (hard, or soft + grace expired);
 *                                     preacq 1091-1107; acquire
 *                                     1110-1128 (QMTGrant); grace timer
 *                                     qmt_lqes_tune_grace 1138
 *     qmt_grant_lqes()/qmt_rel_lqes() 817-825 / 843-859
 *     qmt_lqes_cannot_grant()         861-874
 *     qmt_lqes_grant_some_quota()     876-896
 *     qmt_lqes_alloc_expand()         898-922
 *   lustre/quota/qmt_entry.c
 *     qmt_adjust_edquot()             523-599   sets/clears lqe_edquot
 *     qmt_calc_softlimit()            603-623
 *     qmt_alloc_expand()              636-687   headroom = (soft|hard)
 *                                     limit - lqe_granted
 *     qmt_adjust_qunit()              724-848
 *   lustre/quota/qmt_internal.h
 *     qmt_hard_exhausted()            331-336   granted >= hardlimit
 *     qmt_soft_exhausted()            339-345   granted > softlimit and
 *                                     grace expired (GraceExpire /
 *                                     SOFT_LIMIT ceiling)
 *   lustre/quota/qmt_lock.c
 *     qmt_lvbo_update()               367-490   slave reports lvb_id_rel /
 *                                     lvb_id_may_rel 440-466
 *     qmt_glb_lock_notify()           853-911   LQUOTA_FLAG_REVOKE when
 *                                     granted > hardlimit 883-887
 *                                     (LU-16097)
 *     qmt_id_lock_glimpse()           956-1025  rebalance glimpse
 *                                     (QMTInitRebalance)
 *     qmt_reba_thread()               1076-1115
 *   OST write quota check (OSTQuotaReject):
 *     lustre/osd-ldiskfs/osd_io.c osd_declare_write_commit() 1288-:
 *       !OBD_BRW_SYNC -> OSD_QID_FORCE 1333-1334; OBD_BRW_ASYNC ->
 *       OSD_QID_IGNORE_ROOT_PRJ 1338-1339 (LU-19791 fix e1af85a420)
 *     lustre/osd-ldiskfs/osd_quota.c osd_declare_inode_qid() 630-
 *       (690-691), osd_declare_qid() 522- -> qsd_op_begin at 608
 *   fallocate (UncheckedAcquire): lustre/ofd/ofd_objects.c
 *     ofd_object_fallocate() 790-904, ofd_attr_handle_id 842 and
 *     dt_declare_fallocate(..., la, ...) 864 (LU-19018 e99c8bd1f2)
 *
 * Validated against: lustre-release master 47638add78 (2026-09-06)
 * Validation notes:
 *   - LU-19791: the fix is server-side (osd_declare_write_commit, see
 *     above); osc_page_submit() (osc_page.c:302) still sets
 *     OBD_BRW_SYNC for immediate transfers.  InjectBugBrwSync = FALSE
 *     corresponds to "cached pages are never rejected by the OST quota
 *     check", which is what the fix guarantees.  Comments and cfg
 *     descriptions corrected; state machine unchanged.
 *   - LU-16097: the fix reclaims pre-acquired grant on the slave via a
 *     REVOKE glimpse; the model expresses the same outcome as the
 *     master using ADMIN_LIMIT as its ceiling.
 *   - LU-19503: resolved by a documentation change only (c8d28267f9);
 *     the soft-limit ceiling after grace expiry is qmt_soft_exhausted()
 *     and was never absent from the code.  InjectBugSoftLimit is a
 *     hypothetical injection.
 *   - LU-11929 / LU-6382 (InjectBugRebalanceLoss) were closed Cannot
 *     Reproduce; qmt_dqacq0 rejects any release larger than what the
 *     slave holds instead of over-deducting, so the injection is
 *     hypothetical and the fix variant matches the code.
 *   - The LU19503_bug and LU19503_fix cfgs carried a stray non-comment
 *     line ("    InjectBugBrwSync = FALSE" right after the @constant tag,
 *     ahead of SPECIFICATION) that made TLC reject the cfg outright, so
 *     LU19503_fix had never actually passed and LU19503_bug "failed" for
 *     the wrong reason.  Line turned into a comment; after that the pair
 *     behaves as tagged (bug: SoftLimitInvariant, fix: pass).
 *   - No model change.
 *)

EXTENDS Integers, FiniteSets, TLC

CONSTANTS
    Clients,                       \* Symmetry set: {Client1, Client2}
    QMT_LIMIT,                     \* Total quota limit on QMT (e.g. 10)
    MAX_CLIENT_GRANT,              \* Max per-client grant per replenish slab (e.g. 5)
    MAX_INUSE,                     \* Max writers per client (e.g. 3)
    SOFT_LIMIT,                    \* Soft quota limit (0 = disabled, otherwise < QMT_LIMIT)
    ADMIN_LIMIT,                   \* Admin-set limit (<= QMT_LIMIT; models limit reduction)
    QMT_SOFT_LIMIT,                \* Soft limit for SoftLimitInvariant (0 = disabled)
    EnableRebalance,               \* TRUE = enable rebalance actions
    InjectBugReplenishRace,        \* TRUE = QMT inflates headroom with pending reclaims
    InjectBugRebalanceDouble,      \* TRUE = QMT inflates headroom with pending rebalance
    InjectBugRebalanceLoss,        \* TRUE = QMT over-deducts on partial rebalance return
    InjectBugGraceEnforce,         \* TRUE = QMT ignores soft limit after grace expires
    InjectBugUncheckedAcquire,     \* TRUE = LU-19018 fallocate bypasses quota check
    InjectBugStaleGrant,           \* TRUE = LU-16097 QMT ignores admin limit reduction
    InjectBugSoftLimit,            \* TRUE = LU-19503 soft limit not enforced after grace
    InjectBugBrwSync               \* TRUE = LU-19791 OBD_BRW_SYNC set on cached writes

ASSUME QMT_LIMIT > 0
ASSUME MAX_CLIENT_GRANT > 0
ASSUME MAX_CLIENT_GRANT <= QMT_LIMIT
ASSUME MAX_INUSE > 0
ASSUME SOFT_LIMIT >= 0
ASSUME SOFT_LIMIT = 0 \/ SOFT_LIMIT < QMT_LIMIT
ASSUME ADMIN_LIMIT > 0
ASSUME ADMIN_LIMIT <= QMT_LIMIT
ASSUME QMT_SOFT_LIMIT >= 0
ASSUME QMT_SOFT_LIMIT <= QMT_LIMIT

VARIABLES
    qsd_avail,           \* [Clients -> Nat] available quota at each QSD
    qsd_inuse,           \* [Clients -> Nat] in-use quota per client (0..MAX_INUSE)
    qmt_granted,         \* Nat: QMT's total outstanding grants across all clients
    reclaim_rpc,         \* [Clients -> Nat] in-flight reclaim from each client to QMT
    rebalance_pending,   \* [Clients -> Nat] pending shrink amount from QMT rebalance
    grace_expired,       \* BOOLEAN: TRUE after grace period has expired
    data_lost            \* BOOLEAN: TRUE if a write was silently dropped (LU-19791)

vars == << qsd_avail, qsd_inuse, qmt_granted, reclaim_rpc,
           rebalance_pending, grace_expired, data_lost >>

\* === Helper: sum over a function on a finite set ===
SetSum(f, S) ==
    LET PartialSum[T \in SUBSET S] ==
            IF T = {} THEN 0
            ELSE LET x == CHOOSE x \in T : TRUE
                 IN f[x] + PartialSum[T \ {x}]
    IN PartialSum[S]

TotalAtClients        == SetSum(qsd_avail, Clients) + SetSum(qsd_inuse, Clients)
TotalPendingReclaim   == SetSum(reclaim_rpc, Clients)
TotalRebalancePending == SetSum(rebalance_pending, Clients)

\* === Symmetry reduction ===
Symmetry == Permutations(Clients)

\* ================================================================
\* Invariants
\* ================================================================

\* PRIMARY SAFETY: QMT must never grant more than the hard limit.
\* Violated by InjectBugReplenishRace and InjectBugRebalanceDouble.
HardLimitInvariant == qmt_granted <= QMT_LIMIT

\* CONSERVATION: all quota units in the system are accounted for.
\* Violated by InjectBugRebalanceLoss and InjectBugUncheckedAcquire.
ConservationInvariant ==
    TotalAtClients + TotalPendingReclaim = qmt_granted

\* Non-negative counters.
NonNegative ==
    /\ qmt_granted >= 0
    /\ \A c \in Clients : qsd_avail[c] >= 0
    /\ \A c \in Clients : qsd_inuse[c] >= 0
    /\ \A c \in Clients : reclaim_rpc[c] >= 0
    /\ \A c \in Clients : rebalance_pending[c] >= 0

\* Per-client in-use quota is bounded by the writer limit.
InUseBounded == \A c \in Clients : qsd_inuse[c] <= MAX_INUSE

\* POOL TOTAL: total distributed quota across all targets (client-side view)
\* never exceeds the pool hard limit.  Derivable from Conservation +
\* HardLimit, but provides an independent client-side cross-check.
PoolTotalInvariant ==
    TotalAtClients + TotalPendingReclaim <= QMT_LIMIT

\* EFFECTIVE LIMIT: after grace period expires, the effective limit is
\* SOFT_LIMIT.  QMT must not have granted above this.
\* Violated by InjectBugGraceEnforce.
EffectiveLimitInvariant ==
    (SOFT_LIMIT = 0 \/ ~grace_expired) \/ qmt_granted <= SOFT_LIMIT

\* ADMIN LIMIT: QMT must not grant more than the admin-set limit.
\* In baseline cfgs ADMIN_LIMIT = QMT_LIMIT so this is equivalent to
\* HardLimitInvariant.  When ADMIN_LIMIT < QMT_LIMIT (modeling a limit
\* reduction), the bug mode (InjectBugStaleGrant=TRUE) violates this.
AdminLimitInvariant == qmt_granted <= ADMIN_LIMIT

\* SOFT LIMIT: once the grace period has expired (modeled by setting
\* QMT_SOFT_LIMIT > 0 in the cfg), QMT must not grant more than the
\* soft limit.  Violated by InjectBugSoftLimit=TRUE.
SoftLimitInvariant == QMT_SOFT_LIMIT > 0 => qmt_granted <= QMT_SOFT_LIMIT

\* DATA INTEGRITY: writes that have a valid QSD grant must not be
\* silently dropped.  Violated by InjectBugBrwSync=TRUE (LU-19791).
NoSilentDataLoss == ~data_lost

\* ================================================================
\* Initial state
\* ================================================================

Init ==
    /\ qsd_avail          = [c \in Clients |-> 0]
    /\ qsd_inuse          = [c \in Clients |-> 0]
    /\ qmt_granted        = 0
    /\ reclaim_rpc        = [c \in Clients |-> 0]
    /\ rebalance_pending  = [c \in Clients |-> 0]
    /\ grace_expired      = FALSE
    /\ data_lost          = FALSE

\* ================================================================
\* Actions
\* ================================================================

\* ----------------------------------------------------------------
\* WriterAcquire(c): a write thread on client c takes 1 unit.
\* ----------------------------------------------------------------
WriterAcquire(c) ==
    /\ qsd_avail[c] > 0
    /\ qsd_inuse[c] < MAX_INUSE
    /\ qsd_avail' = [qsd_avail EXCEPT ![c] = qsd_avail[c] - 1]
    /\ qsd_inuse' = [qsd_inuse EXCEPT ![c] = qsd_inuse[c] + 1]
    /\ UNCHANGED << qmt_granted, reclaim_rpc, rebalance_pending, grace_expired, data_lost >>

\* ----------------------------------------------------------------
\* WriterRelease(c): a write thread on client c returns 1 unit.
\* ----------------------------------------------------------------
WriterRelease(c) ==
    /\ qsd_inuse[c] > 0
    /\ qsd_avail' = [qsd_avail EXCEPT ![c] = qsd_avail[c] + 1]
    /\ qsd_inuse' = [qsd_inuse EXCEPT ![c] = qsd_inuse[c] - 1]
    /\ UNCHANGED << qmt_granted, reclaim_rpc, rebalance_pending, grace_expired, data_lost >>

\* ----------------------------------------------------------------
\* UncheckedAcquire(c): a code path (e.g. fallocate) acquires space
\* without checking quota.  Models LU-19018 where fallocate bypasses
\* quota enforcement entirely.
\*
\* Creates "phantom" usage not backed by any QMT grant: qsd_inuse
\* increases but qsd_avail and qmt_granted are unchanged, violating
\* the conservation law.
\*
\* Only enabled when InjectBugUncheckedAcquire = TRUE.
\* ----------------------------------------------------------------
UncheckedAcquire(c) ==
    /\ InjectBugUncheckedAcquire
    /\ qsd_inuse[c] < MAX_INUSE
    /\ qsd_inuse' = [qsd_inuse EXCEPT ![c] = qsd_inuse[c] + 1]
    /\ UNCHANGED << qsd_avail, qmt_granted, reclaim_rpc, rebalance_pending, grace_expired, data_lost >>

\* ----------------------------------------------------------------
\* QMTGrant(c): client c requests quota; QMT grants a slab.
\*
\* The grant amount is non-deterministic (1..min(headroom, MAX_CLIENT_GRANT)),
\* modeling different slab sizes chosen by the QMT.
\*
\* The effective limit depends on which bug mode is active:
\*   - InjectBugStaleGrant:  QMT uses QMT_LIMIT (ignores admin reduction)
\*   - InjectBugSoftLimit:   QMT uses ADMIN_LIMIT (ignores expired soft limit)
\*   - InjectBugGraceEnforce: QMT uses QMT_LIMIT (ignores grace expiry)
\*   - Normal (fix):         QMT uses the most restrictive applicable limit
\*
\* Headroom bugs:
\*   - InjectBugReplenishRace: adds TotalPendingReclaim to headroom.
\*   - InjectBugRebalanceDouble: adds TotalRebalancePending to headroom.
\* ----------------------------------------------------------------
QMTGrant(c) ==
    /\ qsd_avail[c] = 0          \* client is out of local quota
    /\ LET effective_limit ==
               IF InjectBugStaleGrant
               THEN QMT_LIMIT           \* Bug LU-16097: ignore admin reduction
               ELSE IF InjectBugGraceEnforce
                    THEN ADMIN_LIMIT     \* Bug: ignore grace expiry
                    ELSE IF QMT_SOFT_LIMIT > 0 /\ ~InjectBugSoftLimit
                         THEN QMT_SOFT_LIMIT
                         ELSE IF SOFT_LIMIT > 0 /\ grace_expired
                              THEN SOFT_LIMIT
                              ELSE ADMIN_LIMIT
           headroom == effective_limit - qmt_granted
                       + (IF InjectBugReplenishRace THEN TotalPendingReclaim ELSE 0)
                       + (IF InjectBugRebalanceDouble THEN TotalRebalancePending ELSE 0)
           max_grant == IF headroom > MAX_CLIENT_GRANT THEN MAX_CLIENT_GRANT
                        ELSE headroom
       IN /\ max_grant > 0
          /\ \E amount \in 1..max_grant :
             /\ qsd_avail'  = [qsd_avail  EXCEPT ![c] = amount]
             /\ qmt_granted' = qmt_granted + amount
             /\ UNCHANGED << qsd_inuse, reclaim_rpc, rebalance_pending, grace_expired, data_lost >>

\* ----------------------------------------------------------------
\* QSDReclaim(c): client c returns surplus quota to QMT.
\*
\* The reclaim amount is non-deterministic (1..qsd_avail[c]-1),
\* modeling partial reclaim of the local surplus.
\* ----------------------------------------------------------------
QSDReclaim(c) ==
    /\ reclaim_rpc[c] = 0        \* no reclaim currently in-flight for this client
    /\ qsd_avail[c] > 1          \* keep at least 1 unit locally
    /\ \E r \in 1..(qsd_avail[c] - 1) :
       /\ qsd_avail'  = [qsd_avail  EXCEPT ![c] = qsd_avail[c] - r]
       /\ reclaim_rpc' = [reclaim_rpc EXCEPT ![c] = r]
       /\ UNCHANGED << qsd_inuse, qmt_granted, rebalance_pending, grace_expired, data_lost >>

\* ----------------------------------------------------------------
\* QMTReceiveReclaim(c): QMT processes client c's in-flight reclaim.
\* ----------------------------------------------------------------
QMTReceiveReclaim(c) ==
    /\ reclaim_rpc[c] > 0
    /\ qmt_granted'  = qmt_granted - reclaim_rpc[c]
    /\ reclaim_rpc'  = [reclaim_rpc EXCEPT ![c] = 0]
    /\ UNCHANGED << qsd_avail, qsd_inuse, rebalance_pending, grace_expired, data_lost >>

\* ----------------------------------------------------------------
\* QMTInitRebalance(c): QMT asks client c to shrink its grant.
\*
\* Models the QMT deciding that client c has too much grant and should
\* return some.  The requested amount is non-deterministic
\* (1..qsd_avail[c]-1).  The client hasn't processed it yet, so its
\* local state is unchanged.
\*
\* The pending shrink is tracked in rebalance_pending[c].
\* ----------------------------------------------------------------
QMTInitRebalance(c) ==
    /\ EnableRebalance
    /\ rebalance_pending[c] = 0   \* no rebalance already in-flight for c
    /\ qsd_avail[c] > 1           \* client has surplus to shrink
    /\ \E amount \in 1..(qsd_avail[c] - 1) :
       /\ rebalance_pending' = [rebalance_pending EXCEPT ![c] = amount]
       /\ UNCHANGED << qsd_avail, qsd_inuse, qmt_granted, reclaim_rpc, grace_expired, data_lost >>

\* ----------------------------------------------------------------
\* QSDProcessRebalance(c): client c processes QMT's shrink request.
\*
\* Returns min(rebalance_pending[c], qsd_avail[c]) to QMT.  May be
\* less than requested if writers consumed some quota between the
\* rebalance initiation and processing.
\*
\* BUG (InjectBugRebalanceLoss):
\*   QMT deducts the full requested amount from qmt_granted even when
\*   the client could only return a partial amount.  This causes
\*   qmt_granted to drop below the real total, violating conservation
\*   (quota units "disappear" from the system).
\*
\* FIX:
\*   QMT deducts only the actually returned amount.
\* ----------------------------------------------------------------
QSDProcessRebalance(c) ==
    /\ rebalance_pending[c] > 0
    /\ LET requested   == rebalance_pending[c]
           can_return   == IF qsd_avail[c] >= requested THEN requested
                          ELSE qsd_avail[c]
           deduct       == IF InjectBugRebalanceLoss
                           THEN requested      \* BUG: deduct full even if partial
                           ELSE can_return     \* FIX: deduct only actual return
       IN /\ qsd_avail'         = [qsd_avail EXCEPT ![c] = qsd_avail[c] - can_return]
          /\ qmt_granted'       = qmt_granted - deduct
          /\ rebalance_pending' = [rebalance_pending EXCEPT ![c] = 0]
          /\ UNCHANGED << qsd_inuse, reclaim_rpc, grace_expired, data_lost >>

\* ----------------------------------------------------------------
\* GraceExpire: grace period expires while user is at/below soft limit.
\*
\* Models the scenario: user exceeded soft limit, grace timer ran,
\* user reduced usage back to soft limit, then grace latches.  After
\* this, the effective limit drops to SOFT_LIMIT.
\*
\* Precondition: qmt_granted <= SOFT_LIMIT ensures the invariant
\* EffectiveLimitInvariant holds at the transition point.
\* ----------------------------------------------------------------
GraceExpire ==
    /\ SOFT_LIMIT > 0
    /\ ~grace_expired
    /\ qmt_granted <= SOFT_LIMIT   \* currently at or below soft limit
    /\ grace_expired' = TRUE
    /\ UNCHANGED << qsd_avail, qsd_inuse, qmt_granted, reclaim_rpc, rebalance_pending, data_lost >>

\* ----------------------------------------------------------------
\* OSTQuotaReject(c): OST rejects a cached write in its server-side
\* quota check and drops the data.  Models LU-19791.
\*
\* In correct operation, cached (OBD_BRW_ASYNC) pages are forced
\* through the OST-side quota declaration (osd_declare_write_commit ->
\* osd_declare_inode_qid -> qsd_op_begin, osd-ldiskfs/osd_io.c
\* 1333-1339) because the client QSD grant already authorised them.
\*
\* BUG (InjectBugBrwSync): with root_prj_enable set, the root-project
\* quota check was still applied to those cached pages; if root was
\* over its project quota (on another client) the OST returned -EDQUOT.
\* Since this was a cached write, the error is not propagated to the
\* application -- data is silently lost.  Fix e1af85a420 adds
\* OSD_QID_IGNORE_ROOT_PRJ for OBD_BRW_ASYNC pages.  (The constant name
\* reflects an earlier, incorrect reading that blamed osc_page_submit()
\* setting OBD_BRW_SYNC; see header.)
\*
\* The rejection condition models the OST's QSD being unable to acquire
\* a grant from QMT because most quota has been distributed to clients.
\* The write data is lost; the client QSD grant is returned (the
\* writer "completes" without persistence).
\* ----------------------------------------------------------------
OSTQuotaReject(c) ==
    /\ InjectBugBrwSync
    /\ qsd_inuse[c] > 0                              \* writer has in-flight data
    /\ qmt_granted > QMT_LIMIT - MAX_CLIENT_GRANT    \* OST QSD can't get grant
    /\ data_lost' = TRUE
    /\ qsd_inuse' = [qsd_inuse EXCEPT ![c] = qsd_inuse[c] - 1]
    /\ qsd_avail' = [qsd_avail EXCEPT ![c] = qsd_avail[c] + 1]
    /\ UNCHANGED << qmt_granted, reclaim_rpc, rebalance_pending, grace_expired >>

\* ================================================================
\* Next-state relation
\* ================================================================

Next ==
    \/ \E c \in Clients : WriterAcquire(c)
    \/ \E c \in Clients : WriterRelease(c)
    \/ \E c \in Clients : UncheckedAcquire(c)
    \/ \E c \in Clients : QMTGrant(c)
    \/ \E c \in Clients : QSDReclaim(c)
    \/ \E c \in Clients : QMTReceiveReclaim(c)
    \/ \E c \in Clients : QMTInitRebalance(c)
    \/ \E c \in Clients : QSDProcessRebalance(c)
    \/ \E c \in Clients : OSTQuotaReject(c)
    \/ GraceExpire

\* ================================================================
\* Specification
\* ================================================================

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

====
