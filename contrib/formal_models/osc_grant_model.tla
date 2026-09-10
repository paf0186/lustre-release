--------------------------- MODULE osc_grant_model ---------------------------
(*
 * PlusCal/TLA+ specification of the OSC grant accounting subsystem.
 *
 * Models grant flow and RPC in-flight accounting in lustre/osc/osc_cache.c:
 *   - Grant pool: cl_avail_grant -> cl_reserved_grant -> cl_dirty_grant
 *   - cl_loi_list_lock serialization of grant counters
 *   - max_rpcs_in_flight enforcement
 *   - Grant reservation via osc_enter_cache / osc_reserve_grant
 *   - Grant consumption in osc_extent_find
 *   - Grant return on RPC completion
 *   - Grant shrink via osc_shrink_grant_to_target
 *   - PFL multi-component active extent lifecycle
 *   - Wire protocol width constraints (32-bit o_dropped/o_undirty)
 *   - Sync fallback and DIO grant consumption paths
 *
 * Lock order: cl_loi_list_lock protects all grant counters and
 *   rpcs_in_flight counters.
 *
 * Known bugs modeled:
 *   LU-19755: max_rpcs_in_flight TOCTOU - check under lock, release lock,
 *             submit RPC; multiple threads exceed the limit.
 *   LU-19709: osc_queue_async_io restart_find label placed after
 *             osc_enter_cache, so goto restart_find with grants=0
 *             hits LASSERT in osc_extent_find.
 *   LU-11288: osc_shrink_grant_to_target TOCTOU - target computed
 *             outside lock, avail_grant changes, subtraction underflows.
 *   LU-13100: PFL grant deadlock - same OSC in two components, writer
 *             holds active extent consuming grants, can't get more
 *             grants for second component without releasing first.
 *   LU-14125: o_dropped (32-bit) overflow when cl_lost_grant (64-bit)
 *             exceeds wire field width. Server sees truncated value,
 *             grant accounting diverges.
 *   LU-14901: Sync fallback path in vvp_io_write_commit skips grant
 *             consumption - reserved grant leaks when buffered write
 *             falls back to sync due to out-of-quota.
 *   LU-12687: DIO writes via osc_queue_sync_pages skip grant
 *             consumption - pages submitted without dirty_grant
 *             accounting, leading to premature ENOSPC.
 *             (The DIO grant path has since moved to
 *             osc_queue_dio_pages(), see Source below.)
 *
 * Source (lustre-release master 47638add78):
 *   lustre/osc/osc_cache.c
 *     osc_reserve_grant()           1515-1525  avail -> reserved (1520-1521)
 *     osc_unreserve_grant_no_wake() 1527-1545  reserved -> dirty (1536,1543)
 *     osc_consume_write_grant()     1473-1481  cl_dirty_pages++
 *     osc_free_grant()              1625-1649  dirty -> lost; borrow
 *                                              lost -> avail at 1637-1641
 *     osc_enter_cache_try()         1675-1706
 *     osc_enter_cache()             1758-1834  Writer*/SyncFallback reserve;
 *                                              returns -EDQUOT w/o reserving
 *     osc_extent_find()             689-880    LASSERTF(grants >= chunksize
 *                                              + tax) at 753 (LU-19709)
 *     osc_queue_async_io()          2509-2723  osc_enter_cache only when
 *                                              grants == 0 (2658-2659);
 *                                              restart_find: at 2664;
 *                                              GOTO(restart_find) at 2706
 *                                              (LU-19709 path); reserved ->
 *                                              dirty via osc_unreserve_grant
 *                                              at 2678
 *     osc_queue_dio_pages()         2757-2927  DIO grant reserve+consume
 *                                              under cl_loi_list_lock
 *                                              2847-2886 (LU-12687)
 *     osc_queue_sync_pages()        2929-3064  no grant consumption for
 *                                              non-DIO writes (LU-14901)
 *     osc_max_rpc_in_flight()       1838-1840
 *     osc_check_rpcs()              2383-2453  max_rpcs check under lock at
 *                                              2399-2404, unlock at 2407
 *                                              before the RPC is built
 *                                              (LU-19755 TOCTOU)
 *     osc_extent_truncate()         1024-1144  -> osc_free_grant at 1138
 *     osc_extent_finish()           891-956    -> osc_free_grant at 950;
 *                                              unsent extent: lost_grant =
 *                                              oe_grants at 932
 *     osc_extent_release()          593-675    active extent -> OES_CACHE
 *   lustre/osc/osc_io.c
 *     osc_io_extent_release()       497-508    LU-13100: release oi_active
 *   lustre/lov/lov_io.c
 *     lov_io_commit_async()         1776,1781  cl_io_extent_release() when
 *                                              the component changes
 *   lustre/osc/osc_request.c
 *     osc_announce_cached()         664-737    o_dropped clamped to INT_MAX
 *                                              and subtracted, 724-732
 *                                              (LU-14125)
 *     osc_shrink_grant_to_target()  829-879    target re-checked under lock
 *                                              at 855-863 (LU-11288)
 *     osc_build_rpc()               2793-3020  cl_w_in_flight++ under lock
 *                                              at 2954-2972
 *     brw_interpret()               2566-2757  cl_w_in_flight-- at 2715
 *     osc_import_event()            3896-3970  IMP_EVENT_DISCON zeroes
 *                                              cl_avail_grant/cl_lost_grant
 *                                              3907-3913
 *
 * Validated against: lustre-release master 47638add78 (2026-09-06)
 * Validation notes:
 *   - LU-19709 and LU-19755 are still Open in JIRA and have no fix in
 *     this tree: the InjectBug19709/InjectBug19755 = TRUE variants
 *     describe the code as it is (see osc_queue_async_io 2658-2706 and
 *     osc_check_rpcs 2399-2407 above); the = FALSE variants are the
 *     proposed fixes, not code in the tree.
 *   - LU-14901 is Open with no fix in the tree.  DISCREPANCY-OPEN: the
 *     SyncFallback process reserves grant first and then "leaks" it;
 *     in the tree the fallback happens precisely because
 *     osc_enter_cache() returned -EDQUOT WITHOUT reserving (1758-1834),
 *     or because osc_quota_chkdq() failed before any reservation
 *     (osc_queue_async_io 2547-2570), and vvp_io_write_commit()
 *     (llite/vvp_io.c 1207-1218) then sends the pages through
 *     vvp_io_commit_sync -> osc_queue_sync_pages with oe_grants = 0.
 *     So nothing is reserved and nothing leaks; only the "sync pages
 *     are submitted with no grant consumed" part of the process
 *     matches the code.  Left as is because the eventual fix shape is
 *     unknown.
 *   - LU-12687: the fix moved from osc_queue_sync_pages to
 *     osc_queue_dio_pages (LU-13814 8efbad8ff4, LU-19536 744289d8fe).
 *     When reservation fails the real code submits the DIO without
 *     grant (synchronously for non-AIO) instead of stopping; the
 *     DIOWriter "goto DW_Done" is a simplification of that path.
 *)

EXTENDS Integers, TLC

CONSTANTS
    InjectBug19755,
    InjectBug19709,
    InjectBug11288,
    InjectBug13100,
    InjectBug14125,
    InjectBug14901,
    InjectBug12687,
    EnableEviction,
    TOTAL_GRANT

(* --algorithm PlusCal
variables
    \* Grant pool (all protected by cl_loi_list_lock)
    avail_grant = TOTAL_GRANT, \* available grant (in units of chunksize+tax)
    reserved_grant = 0,     \* reserved by osc_enter_cache but not yet dirty
    dirty_grant = 0,        \* consumed by dirty pages
    returned_grant = 0,     \* grants returned to server via shrink

    \* RPC accounting
    rpcs_in_flight = 0,     \* cl_r_in_flight + cl_w_in_flight
    max_rpcs = 1,           \* cl_max_rpcs_in_flight

    \* Active extent tracking for PFL (LU-13100)
    \* An active extent holds dirty_grant that can't be reclaimed by
    \* RPC completion until the extent is released from ACTIVE state
    pfl_active_extent = FALSE,  \* PFL writer holds an active extent
    pfl_held_grant = 0,         \* dirty grant locked by PFL active extent

    \* Wire protocol tracking (LU-14125)
    \* cl_lost_grant is 64-bit, o_dropped wire field is 32-bit.
    \* We model WIRE_MAX=1 as the 32-bit boundary for tractability.
    \* lost_grant accumulates; wire_dropped tracks sent-to-server grants.
    lost_grant = 0,             \* cl_lost_grant (64-bit internal)
    wire_dropped = 0,           \* cumulative grants sent to server via o_dropped

    \* Eviction tracking
    \* When evicted, server reclaims avail+lost grants.
    \* Client-side dirty/reserved drain as in-flight RPCs fail.
    evicted = FALSE,            \* import disconnected

    \* Lock state
    loi_lock = "free";      \* cl_loi_list_lock: "free" or holder pid

define
    \* === CONSTANTS ===
    \* Model 32-bit wire width as small number for tractability
    \* Real value is INT_MAX (2^31-1); we use 1 so lost_grant > WIRE_MAX
    \* is reachable with our small grant pool
    WIRE_MAX == 1

    \* TOTAL_GRANT is now a CONSTANT (set per-cfg for state space control)

    \* === INVARIANTS ===

    \* Grant conservation: total grants in the system never change
    \* lost_grant is a staging area that hasn't left the client yet,
    \* wire_dropped is what the server acknowledged
    GrantConservation ==
        avail_grant + reserved_grant + dirty_grant + returned_grant
        + lost_grant + wire_dropped = TOTAL_GRANT

    \* No negative grants (violated by LU-11288 shrink underflow)
    GrantsNonNegative ==
        avail_grant >= 0 /\ reserved_grant >= 0 /\
        dirty_grant >= 0 /\ returned_grant >= 0 /\
        lost_grant >= 0

    \* RPCs in flight should not exceed max (violated by LU-19755)
    RPCsInFlightBounded ==
        rpcs_in_flight <= max_rpcs

    \* RPCs in flight is non-negative
    RPCsNonNegative ==
        rpcs_in_flight >= 0

    \* === Novel invariants for unknown bug discovery ===

    \* PFL held grant consistency: if grants are locked by PFL
    \* active extent, the extent must be active and dirty_grant
    \* must cover them.
    PFLHeldConsistency ==
        pfl_held_grant > 0 =>
            (pfl_active_extent /\ dirty_grant >= pfl_held_grant)

    \* Client-side grant pool can never exceed total.
    \* avail+reserved+dirty is what the client "owns" for IO.
    ClientGrantBounded ==
        avail_grant + reserved_grant + dirty_grant <= TOTAL_GRANT

    \* Dirty grants imply the pool is not fully available.
    \* This catches double-accounting where grants appear in
    \* both dirty and avail simultaneously.
    DirtyImpliesNotAllAvail ==
        dirty_grant > 0 => avail_grant < TOTAL_GRANT

    \* After eviction, avail can grow through the borrow-from-
    \* lost path (dirty->lost->avail), so avail <= dirty is too
    \* strict.  The real safety property: after eviction, the
    \* client-side total (avail+reserved+dirty+lost) must not
    \* grow.  This is a consequence of GrantConservation (since
    \* returned+wire_dropped only increase), but we state it
    \* explicitly to catch eviction-specific accounting bugs.
    EvictedNoNewGrants ==
        evicted => avail_grant + reserved_grant +
                   dirty_grant + lost_grant <=
                   TOTAL_GRANT - wire_dropped

    \* === Dirty page accounting invariants ===

    \* (a) Dirty pages can never exceed the client's active grant.
    \* Active grant = TOTAL minus server-reclaimed (returned + wire).
    \* Implied by GrantConservation + GrantsNonNegative but checked
    \* independently so violations produce targeted diagnostics.
    DirtyPagesWithinGrant ==
        dirty_grant <= TOTAL_GRANT - returned_grant - wire_dropped

    \* (b) Reserved grant eventually reaches zero: every reservation
    \* is consumed (reserved->dirty) or released. Catches grant leaks
    \* where reserved grants are stranded by a code path.
    \* Checked as PROPERTY (temporal), not INVARIANT.
    ReservedEventuallyConsumed ==
        reserved_grant > 0 ~> reserved_grant = 0

end define;

\* ---------------------------------------------------------------
\* Writer1: models osc_queue_async_io flow
\*   1. osc_enter_cache (reserve grant under lock)
\*   2. osc_extent_find (consume grant - LASSERT grants >= 1)
\*   3. Maybe extent gets stolen -> restart_find
\*   4. osc_check_rpcs -> check max_rpcs, submit RPC
\* ---------------------------------------------------------------
fair process Writer1 = "W1"
variables
    w1_grants = 0,
    w1_rpc_approved = FALSE;
begin
W1_AcquireLock1:
    \* osc_enter_cache: acquire lock, reserve grant
    await loi_lock = "free";
    loi_lock := "W1";

W1_Reserve:
    if avail_grant >= 1 then
        avail_grant := avail_grant - 1;
        reserved_grant := reserved_grant + 1;
        w1_grants := 1;
        loi_lock := "free";
    else
        \* No grant available, done
        loi_lock := "free";
        goto W1_Done;
    end if;

W1_ExtentFind:
    \* osc_extent_find: LASSERT grants >= chunksize + extent_tax
    if w1_grants < 1 then
        \* LU-19709 LASSERT failure: grants=0 reaching extent_find
        assert FALSE;
    end if;

W1_AcquireLock2:
    \* Consume grant: reserved -> dirty (under lock)
    await loi_lock = "free";
    loi_lock := "W1";

W1_ConsumeDirty:
    reserved_grant := reserved_grant - 1;
    dirty_grant := dirty_grant + 1;
    w1_grants := 0;
    loi_lock := "free";

W1_MaybeSteal:
    \* Non-deterministically, the active extent may be stolen
    \* (another thread writes it back, changing state from ACTIVE)
    either
        skip;
    or
        if InjectBug19709 then
            \* BUG: goto restart_find WITHOUT calling osc_enter_cache
            goto W1_ExtentFind;
        else
            \* FIXED: call osc_enter_cache to get new grants first
            goto W1_AcquireLock1;
        end if;
    end either;

W1_AcquireLock3:
    \* osc_check_rpcs: check max_rpcs_in_flight under lock
    await loi_lock = "free";
    loi_lock := "W1";

W1_CheckRPCs:
    if rpcs_in_flight >= max_rpcs then
        loi_lock := "free";
        goto W1_Done;
    elsif InjectBug19755 then
        \* BUG: Release lock BEFORE incrementing rpcs_in_flight
        w1_rpc_approved := TRUE;
        loi_lock := "free";
    else
        \* FIXED: increment while holding lock
        rpcs_in_flight := rpcs_in_flight + 1;
        loi_lock := "free";
        goto W1_Done;
    end if;

W1_AcquireLock4:
    \* TOCTOU window: re-acquire lock to increment counter
    await loi_lock = "free";
    loi_lock := "W1";

W1_SubmitRPC:
    w1_rpc_approved := FALSE;
    rpcs_in_flight := rpcs_in_flight + 1;
    loi_lock := "free";

W1_Done:
    skip;
end process;

\* ---------------------------------------------------------------
\* Writer2: identical logic (second concurrent writer)
\* ---------------------------------------------------------------
fair process Writer2 = "W2"
variables
    w2_grants = 0,
    w2_rpc_approved = FALSE;
begin
W2_AcquireLock1:
    await loi_lock = "free";
    loi_lock := "W2";

W2_Reserve:
    if avail_grant >= 1 then
        avail_grant := avail_grant - 1;
        reserved_grant := reserved_grant + 1;
        w2_grants := 1;
        loi_lock := "free";
    else
        loi_lock := "free";
        goto W2_Done;
    end if;

W2_ExtentFind:
    if w2_grants < 1 then
        assert FALSE;
    end if;

W2_AcquireLock2:
    await loi_lock = "free";
    loi_lock := "W2";

W2_ConsumeDirty:
    reserved_grant := reserved_grant - 1;
    dirty_grant := dirty_grant + 1;
    w2_grants := 0;
    loi_lock := "free";

W2_MaybeSteal:
    either
        skip;
    or
        if InjectBug19709 then
            goto W2_ExtentFind;
        else
            goto W2_AcquireLock1;
        end if;
    end either;

W2_AcquireLock3:
    await loi_lock = "free";
    loi_lock := "W2";

W2_CheckRPCs:
    if rpcs_in_flight >= max_rpcs then
        loi_lock := "free";
        goto W2_Done;
    elsif InjectBug19755 then
        w2_rpc_approved := TRUE;
        loi_lock := "free";
    else
        rpcs_in_flight := rpcs_in_flight + 1;
        loi_lock := "free";
        goto W2_Done;
    end if;

W2_AcquireLock4:
    await loi_lock = "free";
    loi_lock := "W2";

W2_SubmitRPC:
    w2_rpc_approved := FALSE;
    rpcs_in_flight := rpcs_in_flight + 1;
    loi_lock := "free";

W2_Done:
    skip;
end process;

\* ---------------------------------------------------------------
\* GrantShrink: models osc_shrink_grant_to_target (LU-11288)
\*
\* The bug: target is computed outside the lock, then under the
\* lock we do avail_grant - target. But avail_grant may have
\* decreased between computation and subtraction, so the result
\* goes negative (unsigned underflow in real code).
\* ---------------------------------------------------------------
fair process GrantShrink = "GS"
variables
    gs_target = 0;
begin
GS_ComputeTarget:
    \* Read avail_grant outside lock to compute target
    \* Target = keep half the current avail_grant
    \* (simplified from real osc_should_shrink_grant logic)
    await loi_lock = "free";
    loi_lock := "GS";

GS_ReadAvail:
    if avail_grant >= 2 then
        \* Target = keep 1 unit (shrink the rest)
        gs_target := 1;
        loi_lock := "free";
    else
        \* Nothing to shrink
        loi_lock := "free";
        goto GS_Done;
    end if;
    \* TOCTOU gap: avail_grant can change here (writers consuming it)

GS_AcquireLock:
    await loi_lock = "free";
    loi_lock := "GS";

GS_Shrink:
    if InjectBug11288 then
        \* BUG: no re-check of target vs avail_grant
        \* If writers consumed grants, avail_grant < gs_target,
        \* subtraction goes negative
        returned_grant := returned_grant + (avail_grant - gs_target);
        avail_grant := gs_target;
        loi_lock := "free";
    elsif gs_target >= avail_grant then
        \* FIXED: re-check under lock - available grant changed, skip
        loi_lock := "free";
        goto GS_Done;
    else
        \* FIXED: target still valid, do the shrink
        returned_grant := returned_grant + (avail_grant - gs_target);
        avail_grant := gs_target;
        loi_lock := "free";
    end if;

GS_Done:
    skip;
end process;

\* ---------------------------------------------------------------
\* PFLWriter: models a PFL writer hitting the same OSC twice
\*            (LU-13100 grant deadlock)
\*
\* The bug: writer creates an active extent on component 1 (consuming
\* grant), then tries to get grant for component 2 on the same OST.
\* Grant pool is exhausted because component 1's extent holds dirty
\* grant. Without releasing the active extent (allowing RPC submission
\* and grant return), the writer deadlocks waiting for grants.
\* ---------------------------------------------------------------
fair process PFLWriter = "PW"
begin
PW_AcquireLock1:
    \* Component 1: reserve grant
    await loi_lock = "free";
    loi_lock := "PW";

PW_ReserveComp1:
    if avail_grant >= 1 then
        avail_grant := avail_grant - 1;
        reserved_grant := reserved_grant + 1;
        loi_lock := "free";
    else
        loi_lock := "free";
        goto PW_Done;
    end if;

PW_AcquireLock2:
    \* Consume reserved -> dirty for component 1 extent
    await loi_lock = "free";
    loi_lock := "PW";

PW_ConsumeComp1:
    reserved_grant := reserved_grant - 1;
    dirty_grant := dirty_grant + 1;
    pfl_active_extent := TRUE;  \* holding active extent
    pfl_held_grant := 1;        \* this grant is locked by active extent
    loi_lock := "free";

PW_SwitchComponent:
    \* Now switch to component 2 on same OST
    if InjectBug13100 then
        \* BUG: don't release active extent before switching
        \* pfl_held_grant stays 1, blocking grant reclamation
        skip;
    else
        \* FIXED: release active extent, which allows it to be
        \* submitted as RPC and grants reclaimed. We model the
        \* full pipeline (release -> RPC -> completion) as atomic
        \* since it's the eventual effect of releasing.
        pfl_active_extent := FALSE;
        pfl_held_grant := 0;
        dirty_grant := dirty_grant - 1;
        avail_grant := avail_grant + 1;
    end if;

PW_AcquireLock3:
    \* Component 2: osc_enter_cache WAITS for grant (blocking)
    \* With bug: if all grants consumed by comp 1 active extent and
    \* other writers, this blocks forever -> deadlock
    await loi_lock = "free" /\ avail_grant >= 1;
    loi_lock := "PW";

PW_ReserveComp2:
    avail_grant := avail_grant - 1;
    reserved_grant := reserved_grant + 1;
    loi_lock := "free";

PW_AcquireLock4:
    await loi_lock = "free";
    loi_lock := "PW";

PW_ConsumeComp2:
    reserved_grant := reserved_grant - 1;
    dirty_grant := dirty_grant + 1;
    pfl_active_extent := FALSE;
    pfl_held_grant := 0;
    loi_lock := "free";

PW_Done:
    skip;
end process;

\* ---------------------------------------------------------------
\* RPCComplete: models brw_interpret returning grants
\* ---------------------------------------------------------------
fair process RPCComplete = "RC"
begin
RC_Wait:
    \* Wait for an RPC to complete
    await rpcs_in_flight > 0;

RC_AcquireLock:
    await loi_lock = "free";
    loi_lock := "RC";

RC_Complete:
    rpcs_in_flight := rpcs_in_flight - 1;
    \* Return dirty grant to available (simplified osc_free_grant)
    \* Can't reclaim grants held by PFL active extent
    if dirty_grant > pfl_held_grant then
        dirty_grant := dirty_grant - 1;
        avail_grant := avail_grant + 1;
    end if;
    loi_lock := "free";
    \* Loop back to handle more completions
    goto RC_Wait;

RC_Done:
    skip;
end process;

\* ---------------------------------------------------------------
\* WireAnnounce: models osc_announce_cached packing cl_lost_grant
\*               into o_dropped (32-bit wire field). (LU-14125)
\*
\* The bug: o_dropped = cl_lost_grant directly, which truncates
\* to 32 bits when cl_lost_grant > INT_MAX. Then cl_lost_grant = 0,
\* but server only got the low 32 bits.
\*
\* The fix: o_dropped = min(cl_lost_grant, WIRE_MAX), then
\* cl_lost_grant -= o_dropped (not zeroed).
\*
\* We model this with WIRE_MAX = 1 as the width boundary.
\* To trigger: need lost_grant to exceed WIRE_MAX, which happens
\* when multiple dirty pages are freed via osc_free_grant with
\* cl_lost_grant accumulating (e.g. grant shrink + RPC freeing).
\* ---------------------------------------------------------------
fair process WireAnnounce = "WA"
variables
    wa_to_send = 0;
begin
WA_AcquireLock:
    \* Wait until there are lost grants to announce
    await loi_lock = "free" /\ lost_grant > 0;
    loi_lock := "WA";

WA_PackWire:
    \* Compute how much fits on wire (both bug and fix clamp the same)
    if lost_grant > WIRE_MAX then
        wa_to_send := WIRE_MAX;
    else
        wa_to_send := lost_grant;
    end if;

WA_SendOnWire:
    wire_dropped := wire_dropped + wa_to_send;
    if InjectBug14125 then
        \* BUG: zero out ALL of cl_lost_grant even though wire
        \* could only carry a truncated amount. When lost_grant was
        \* > WIRE_MAX, the excess is silently dropped.
        lost_grant := 0;
    else
        \* FIXED: only subtract what was actually sent on wire
        lost_grant := lost_grant - wa_to_send;
    end if;
    loi_lock := "free";

WA_Done:
    skip;
end process;

\* ---------------------------------------------------------------
\* LostGrantAccumulator: models paths that add to cl_lost_grant
\*
\* In real code, cl_lost_grant grows when:
\*   - osc_free_grant() is passed a non-zero lost_grant: truncate
\*     (osc_extent_truncate, osc_cache.c:1138), an extent that was
\*     never sent (osc_extent_finish, 932/950), or a short write
\*     without GRANT_PARAM support
\*   - osc_unreserve_grant_no_wake() finds unused > reserved after
\*     an extent merge saved the extent tax (osc_cache.c:1527-1545)
\* Both move grant out of dirty/reserved, not out of avail; the
\* avail -> lost move below is a closed-system shortcut that keeps
\* GrantConservation intact while driving lost_grant up.
\*
\* We model two rounds of grant loss to push lost_grant above
\* WIRE_MAX, triggering the overflow bug.
\* ---------------------------------------------------------------
fair process LostAccum = "LA"
begin
LA_AcquireLock1:
    \* First loss: grant shrink moves avail to lost
    await loi_lock = "free" /\ avail_grant >= 1;
    loi_lock := "LA";

LA_AddLost1:
    lost_grant := lost_grant + 1;
    avail_grant := avail_grant - 1;
    loi_lock := "free";

LA_AcquireLock2:
    \* Second loss: more avail -> lost (pushes over WIRE_MAX=1)
    await loi_lock = "free" /\ avail_grant >= 1;
    loi_lock := "LA";

LA_AddLost2:
    lost_grant := lost_grant + 1;
    avail_grant := avail_grant - 1;
    loi_lock := "free";

LA_Done:
    skip;
end process;

\* ---------------------------------------------------------------
\* SyncFallbackWriter: models vvp_io_write_commit sync fallback
\*                     path (LU-14901)
\*
\* The bug: buffered write reserves grant via osc_enter_cache.
\* Then out-of-quota triggers fallback to osc_queue_sync_pages.
\* But sync path doesn't consume the reserved grant (no
\* reserved->dirty transition), so reserved_grant leaks.
\* The pages are submitted without dirty_grant, breaking
\* grant conservation.
\*
\* The fix: consume reserved grant on the sync fallback path.
\*
\* Validation note (47638add78): LU-14901 is still Open.  In the
\* tree the fallback is taken because osc_enter_cache() failed
\* WITHOUT reserving (osc_cache.c:1758-1834) or the quota check
\* failed first (osc_queue_async_io 2547-2570); vvp_io_write_commit
\* (vvp_io.c:1207-1218) then goes through vvp_io_commit_sync ->
\* osc_queue_sync_pages (osc_cache.c:2929-3064) with oe_grants = 0.
\* The "reserve then leak" shape of this process therefore does not
\* match the code; only the final assertion (sync pages submitted
\* with no grant consumed) does.  See DISCREPANCY-OPEN in header.
\* ---------------------------------------------------------------
fair process SyncFallback = "Sy"
variables
    sf_grants = 0,
    sf_consumed = FALSE;  \* tracks whether reserved->dirty happened
begin
Sy_AcquireLock1:
    \* osc_enter_cache: reserve grant (buffered write path)
    await loi_lock = "free";
    loi_lock := "Sy";

Sy_Reserve:
    if avail_grant >= 1 then
        avail_grant := avail_grant - 1;
        reserved_grant := reserved_grant + 1;
        sf_grants := 1;
        loi_lock := "free";
    else
        loi_lock := "free";
        goto Sy_Done;
    end if;

Sy_FallbackToSync:
    \* Out of quota detected, fall back to sync write
    if InjectBug14901 then
        \* BUG: skip grant consumption on sync fallback
        \* reserved_grant stays allocated, sync write proceeds
        \* without dirty_grant. ext->oe_grants == 0.
        sf_consumed := FALSE;
        goto Sy_SyncSubmit;
    end if;

Sy_AcquireLock2:
    \* FIXED: consume grant on sync path too
    \* reserved -> dirty transition happens in sync path
    await loi_lock = "free";
    loi_lock := "Sy";

Sy_ConsumeSync:
    reserved_grant := reserved_grant - 1;
    dirty_grant := dirty_grant + 1;
    sf_grants := 0;
    sf_consumed := TRUE;
    loi_lock := "free";

Sy_SyncSubmit:
    \* Submit the sync write RPC
    \* LASSERT: ext->oe_grants must be > 0 for the write
    \* With bug: reserved was never converted to dirty, so
    \* the extent has no grants. This triggers ENOSPC or
    \* grant leak.
    if sf_consumed = FALSE then
        assert FALSE;
    end if;

Sy_Done:
    skip;
end process;

\* ---------------------------------------------------------------
\* DIOWriter: models direct IO write via osc_queue_sync_pages
\*            (LU-12687)
\*
\* The bug: new IO engine lost consuming grants for DIO writes.
\* osc_queue_sync_pages didn't call osc_consume_write_grant for
\* OBD_BRW_NOCACHE pages. Pages submitted without dirty_grant,
\* server sees no dirty accounting, runs out of grant early.
\*
\* The fix: in osc_queue_sync_pages, when OBD_BRW_NOCACHE && write,
\* reserve and consume grants just like buffered writes.
\*
\* Validation note (47638add78): the DIO write path is now
\* osc_queue_dio_pages() (osc_cache.c:2757-2927).  Under one
\* cl_loi_list_lock hold it does osc_reserve_grant()/
\* osc_reserve_dio_grant() (2847-2850), osc_consume_write_grant()
\* per page, then osc_unreserve_grant_nolock(cli, grants, 0) which
\* converts reserved -> dirty (2873-2874); the atomic avail -> dirty
\* step below matches that.  If reservation fails the real code
\* still submits the DIO with oe_grants = 0 (sync for non-AIO,
\* 2858); the model's "goto DW_Done" stands in for that path.
\* ---------------------------------------------------------------
fair process DIOWriter = "DW"
variables
    dw_grants = 0;
begin
DW_AcquireLock1:
    \* DIO write: needs to reserve grant before submitting
    await loi_lock = "free";
    loi_lock := "DW";

DW_TryReserve:
    if InjectBug12687 then
        \* BUG: skip grant reservation entirely for DIO
        \* Pages will be submitted without any grant accounting
        loi_lock := "free";
    else
        \* FIXED: reserve and consume grant for DIO in
        \* osc_queue_dio_pages (osc_cache.c:2847-2886)
        if avail_grant >= 1 then
            avail_grant := avail_grant - 1;
            dirty_grant := dirty_grant + 1;
            dw_grants := 1;
            loi_lock := "free";
        else
            loi_lock := "free";
            goto DW_Done;
        end if;
    end if;

DW_SubmitDIO:
    \* Submit the DIO RPC - LASSERT that grants were consumed
    \* In real code, ext->oe_grants == 0 means server gets ENOSPC
    \* because no grant was reserved for this write
    if dw_grants < 1 then
        \* BUG path: DIO submitted without grant - LASSERT/ENOSPC
        assert FALSE;
    end if;

DW_Done:
    skip;
end process;

\* ---------------------------------------------------------------
\* Eviction: models osc_import_event IMP_EVENT_DISCON
\*
\* On disconnect, the client zeros cl_avail_grant and cl_lost_grant.
\* The server reclaims those grants. cl_dirty_grant and
\* cl_reserved_grant are NOT touched - they drain as in-flight
\* RPCs fail (modeled by RPCComplete/Truncate processes).
\*
\* After eviction, reconnect gives fresh grants via osc_init_grant.
\* The question: does grant accounting stay consistent through
\* the eviction + drain + reconnect sequence?
\*
\* We model this as:
\*   1. Eviction: avail+lost -> returned (server reclaimed)
\*   2. Drain: dirty->lost via osc_free_grant (truncate/RPC fail)
\*   3. Reconnect: server gives fresh ocd_grant, client computes
\*      avail = ocd_grant - reserved - dirty
\*
\* Key race potential: if dirty drains to lost between eviction
\* (which zeroed lost) and reconnect, those lost grants are not
\* accounted for in osc_init_grant's computation.
\* ---------------------------------------------------------------
fair process Eviction = "EV"
begin
EV_WaitEnabled:
    if ~EnableEviction then
        goto EV_Done;
    end if;

EV_AcquireLock:
    \* Wait for dirty pages to exist (eviction during IO)
    await loi_lock = "free" /\ dirty_grant > 0 /\ ~evicted;
    loi_lock := "EV";

EV_Disconnect:
    \* osc_import_event IMP_EVENT_DISCON:
    \* Server reclaims avail_grant and lost_grant.
    \* In closed system model, these go to returned_grant.
    returned_grant := returned_grant + avail_grant + lost_grant;
    avail_grant := 0;
    lost_grant := 0;
    evicted := TRUE;
    loi_lock := "free";

EV_Done:
    skip;
end process;

\* ---------------------------------------------------------------
\* Truncate: models osc_extent_truncate -> osc_free_grant path
\*
\* When pages are truncated, dirty_grant is freed:
\*   cl_dirty_grant -= grants
\*   cl_lost_grant += grants
\* The grants move from dirty to lost (where they'll be reported
\* to the server via o_dropped on the next RPC).
\*
\* Also models the borrow-from-lost-to-avail logic in osc_free_grant:
\* if cl_avail_grant < grant && cl_lost_grant >= grant, borrow
\* from lost to keep some avail_grant available.
\*
\* After eviction, this path is exercised as in-flight RPCs fail,
\* returning their dirty grants. The question is whether
\* lost_grant accumulated during this drain is properly handled
\* by the reconnect path.
\* ---------------------------------------------------------------
fair process Truncate = "TR"
begin
TR_AcquireLock:
    \* Wait for dirty pages to truncate
    await loi_lock = "free" /\ dirty_grant > pfl_held_grant;
    loi_lock := "TR";

TR_FreeGrant:
    \* osc_free_grant(cli, nr_pages, lost_grant=1, dirty_grant=1)
    \* All under cl_loi_list_lock: move dirty->lost, optionally
    \* borrow from lost->avail to keep writers unblocked.
    if dirty_grant > pfl_held_grant /\ avail_grant = 0 then
        \* Free dirty and borrow from lost (avail was depleted)
        dirty_grant := dirty_grant - 1;
        \* lost_grant += 1 then -= 1 nets to 0, avail gets 1
        avail_grant := 1;
    elsif dirty_grant > pfl_held_grant then
        \* Free dirty to lost, avail still has room
        dirty_grant := dirty_grant - 1;
        lost_grant := lost_grant + 1;
    end if;
    loi_lock := "free";

TR_Done:
    skip;
end process;

end algorithm; *)
\* BEGIN TRANSLATION
VARIABLES avail_grant, reserved_grant, dirty_grant, returned_grant,
          rpcs_in_flight, max_rpcs, pfl_active_extent, pfl_held_grant,
          lost_grant, wire_dropped, evicted, loi_lock, pc

(* define statement *)
WIRE_MAX == 1








GrantConservation ==
    avail_grant + reserved_grant + dirty_grant + returned_grant
    + lost_grant + wire_dropped = TOTAL_GRANT


GrantsNonNegative ==
    avail_grant >= 0 /\ reserved_grant >= 0 /\
    dirty_grant >= 0 /\ returned_grant >= 0 /\
    lost_grant >= 0


RPCsInFlightBounded ==
    rpcs_in_flight <= max_rpcs


RPCsNonNegative ==
    rpcs_in_flight >= 0


PFLHeldConsistency ==
    pfl_held_grant > 0 =>
        (pfl_active_extent /\ dirty_grant >= pfl_held_grant)

ClientGrantBounded ==
    avail_grant + reserved_grant + dirty_grant <= TOTAL_GRANT

DirtyImpliesNotAllAvail ==
    dirty_grant > 0 => avail_grant < TOTAL_GRANT

EvictedNoNewGrants ==
    evicted => avail_grant + reserved_grant +
               dirty_grant + lost_grant <=
               TOTAL_GRANT - wire_dropped

DirtyPagesWithinGrant ==
    dirty_grant <= TOTAL_GRANT - returned_grant - wire_dropped

ReservedEventuallyConsumed ==
    reserved_grant > 0 ~> reserved_grant = 0

VARIABLES w1_grants, w1_rpc_approved, w2_grants, w2_rpc_approved, gs_target,
          wa_to_send, sf_grants, sf_consumed, dw_grants

vars == << avail_grant, reserved_grant, dirty_grant, returned_grant,
           rpcs_in_flight, max_rpcs, pfl_active_extent, pfl_held_grant,
           lost_grant, wire_dropped, evicted, loi_lock, pc, w1_grants,
           w1_rpc_approved, w2_grants, w2_rpc_approved, gs_target, wa_to_send,
           sf_grants, sf_consumed, dw_grants >>

ProcSet == {"W1"} \cup {"W2"} \cup {"GS"} \cup {"PW"} \cup {"RC"} \cup {"WA"} \cup {"LA"} \cup {"Sy"} \cup {"DW"} \cup {"EV"} \cup {"TR"}

Init == (* Global variables *)
        /\ avail_grant = TOTAL_GRANT
        /\ reserved_grant = 0
        /\ dirty_grant = 0
        /\ returned_grant = 0
        /\ rpcs_in_flight = 0
        /\ max_rpcs = 1
        /\ pfl_active_extent = FALSE
        /\ pfl_held_grant = 0
        /\ lost_grant = 0
        /\ wire_dropped = 0
        /\ evicted = FALSE
        /\ loi_lock = "free"
        (* Process Writer1 *)
        /\ w1_grants = 0
        /\ w1_rpc_approved = FALSE
        (* Process Writer2 *)
        /\ w2_grants = 0
        /\ w2_rpc_approved = FALSE
        (* Process GrantShrink *)
        /\ gs_target = 0
        (* Process WireAnnounce *)
        /\ wa_to_send = 0
        (* Process SyncFallback *)
        /\ sf_grants = 0
        /\ sf_consumed = FALSE
        (* Process DIOWriter *)
        /\ dw_grants = 0
        /\ pc = [self \in ProcSet |-> CASE self = "W1" -> "W1_AcquireLock1"
                                        [] self = "W2" -> "W2_AcquireLock1"
                                        [] self = "GS" -> "GS_ComputeTarget"
                                        [] self = "PW" -> "PW_AcquireLock1"
                                        [] self = "RC" -> "RC_Wait"
                                        [] self = "WA" -> "WA_AcquireLock"
                                        [] self = "LA" -> "LA_AcquireLock1"
                                        [] self = "Sy" -> "Sy_AcquireLock1"
                                        [] self = "DW" -> "DW_AcquireLock1"
                                        [] self = "EV" -> "EV_WaitEnabled"
                                        [] self = "TR" -> "TR_AcquireLock"]

W1_AcquireLock1 == /\ pc["W1"] = "W1_AcquireLock1"
                   /\ loi_lock = "free"
                   /\ loi_lock' = "W1"
                   /\ pc' = [pc EXCEPT !["W1"] = "W1_Reserve"]
                   /\ UNCHANGED << avail_grant, reserved_grant, dirty_grant,
                                   returned_grant, rpcs_in_flight, max_rpcs,
                                   pfl_active_extent, pfl_held_grant,
                                   lost_grant, wire_dropped, evicted,
                                   w1_grants, w1_rpc_approved, w2_grants,
                                   w2_rpc_approved, gs_target, wa_to_send,
                                   sf_grants, sf_consumed, dw_grants >>

W1_Reserve == /\ pc["W1"] = "W1_Reserve"
              /\ IF avail_grant >= 1
                    THEN /\ avail_grant' = avail_grant - 1
                         /\ reserved_grant' = reserved_grant + 1
                         /\ w1_grants' = 1
                         /\ loi_lock' = "free"
                         /\ pc' = [pc EXCEPT !["W1"] = "W1_ExtentFind"]
                    ELSE /\ loi_lock' = "free"
                         /\ pc' = [pc EXCEPT !["W1"] = "W1_Done"]
                         /\ UNCHANGED << avail_grant, reserved_grant,
                                         w1_grants >>
              /\ UNCHANGED << dirty_grant, returned_grant, rpcs_in_flight,
                              max_rpcs, pfl_active_extent, pfl_held_grant,
                              lost_grant, wire_dropped, evicted,
                              w1_rpc_approved, w2_grants, w2_rpc_approved,
                              gs_target, wa_to_send, sf_grants, sf_consumed,
                              dw_grants >>

W1_ExtentFind == /\ pc["W1"] = "W1_ExtentFind"
                 /\ IF w1_grants < 1
                       THEN /\ Assert(FALSE,
                                      "Failure of assertion at line 155, column 9.")
                       ELSE /\ TRUE
                 /\ pc' = [pc EXCEPT !["W1"] = "W1_AcquireLock2"]
                 /\ UNCHANGED << avail_grant, reserved_grant, dirty_grant,
                                 returned_grant, rpcs_in_flight, max_rpcs,
                                 pfl_active_extent, pfl_held_grant, lost_grant,
                                 wire_dropped, evicted, loi_lock, w1_grants,
                                 w1_rpc_approved, w2_grants, w2_rpc_approved,
                                 gs_target, wa_to_send, sf_grants, sf_consumed,
                                 dw_grants >>

W1_AcquireLock2 == /\ pc["W1"] = "W1_AcquireLock2"
                   /\ loi_lock = "free"
                   /\ loi_lock' = "W1"
                   /\ pc' = [pc EXCEPT !["W1"] = "W1_ConsumeDirty"]
                   /\ UNCHANGED << avail_grant, reserved_grant, dirty_grant,
                                   returned_grant, rpcs_in_flight, max_rpcs,
                                   pfl_active_extent, pfl_held_grant,
                                   lost_grant, wire_dropped, evicted,
                                   w1_grants, w1_rpc_approved, w2_grants,
                                   w2_rpc_approved, gs_target, wa_to_send,
                                   sf_grants, sf_consumed, dw_grants >>

W1_ConsumeDirty == /\ pc["W1"] = "W1_ConsumeDirty"
                   /\ reserved_grant' = reserved_grant - 1
                   /\ dirty_grant' = dirty_grant + 1
                   /\ w1_grants' = 0
                   /\ loi_lock' = "free"
                   /\ pc' = [pc EXCEPT !["W1"] = "W1_MaybeSteal"]
                   /\ UNCHANGED << avail_grant, returned_grant, rpcs_in_flight,
                                   max_rpcs, pfl_active_extent, pfl_held_grant,
                                   lost_grant, wire_dropped, evicted,
                                   w1_rpc_approved, w2_grants, w2_rpc_approved,
                                   gs_target, wa_to_send, sf_grants,
                                   sf_consumed, dw_grants >>

W1_MaybeSteal == /\ pc["W1"] = "W1_MaybeSteal"
                 /\ \/ /\ TRUE
                       /\ pc' = [pc EXCEPT !["W1"] = "W1_AcquireLock3"]
                    \/ /\ IF InjectBug19709
                             THEN /\ pc' = [pc EXCEPT !["W1"] = "W1_ExtentFind"]
                             ELSE /\ pc' = [pc EXCEPT !["W1"] = "W1_AcquireLock1"]
                 /\ UNCHANGED << avail_grant, reserved_grant, dirty_grant,
                                 returned_grant, rpcs_in_flight, max_rpcs,
                                 pfl_active_extent, pfl_held_grant, lost_grant,
                                 wire_dropped, evicted, loi_lock, w1_grants,
                                 w1_rpc_approved, w2_grants, w2_rpc_approved,
                                 gs_target, wa_to_send, sf_grants, sf_consumed,
                                 dw_grants >>

W1_AcquireLock3 == /\ pc["W1"] = "W1_AcquireLock3"
                   /\ loi_lock = "free"
                   /\ loi_lock' = "W1"
                   /\ pc' = [pc EXCEPT !["W1"] = "W1_CheckRPCs"]
                   /\ UNCHANGED << avail_grant, reserved_grant, dirty_grant,
                                   returned_grant, rpcs_in_flight, max_rpcs,
                                   pfl_active_extent, pfl_held_grant,
                                   lost_grant, wire_dropped, evicted,
                                   w1_grants, w1_rpc_approved, w2_grants,
                                   w2_rpc_approved, gs_target, wa_to_send,
                                   sf_grants, sf_consumed, dw_grants >>

W1_CheckRPCs == /\ pc["W1"] = "W1_CheckRPCs"
                /\ IF rpcs_in_flight >= max_rpcs
                      THEN /\ loi_lock' = "free"
                           /\ pc' = [pc EXCEPT !["W1"] = "W1_Done"]
                           /\ UNCHANGED << rpcs_in_flight, w1_rpc_approved >>
                      ELSE /\ IF InjectBug19755
                                 THEN /\ w1_rpc_approved' = TRUE
                                      /\ loi_lock' = "free"
                                      /\ pc' = [pc EXCEPT !["W1"] = "W1_AcquireLock4"]
                                      /\ UNCHANGED rpcs_in_flight
                                 ELSE /\ rpcs_in_flight' = rpcs_in_flight + 1
                                      /\ loi_lock' = "free"
                                      /\ pc' = [pc EXCEPT !["W1"] = "W1_Done"]
                                      /\ UNCHANGED w1_rpc_approved
                /\ UNCHANGED << avail_grant, reserved_grant, dirty_grant,
                                returned_grant, max_rpcs, pfl_active_extent,
                                pfl_held_grant, lost_grant, wire_dropped,
                                evicted, w1_grants, w2_grants, w2_rpc_approved,
                                gs_target, wa_to_send, sf_grants, sf_consumed,
                                dw_grants >>

W1_AcquireLock4 == /\ pc["W1"] = "W1_AcquireLock4"
                   /\ loi_lock = "free"
                   /\ loi_lock' = "W1"
                   /\ pc' = [pc EXCEPT !["W1"] = "W1_SubmitRPC"]
                   /\ UNCHANGED << avail_grant, reserved_grant, dirty_grant,
                                   returned_grant, rpcs_in_flight, max_rpcs,
                                   pfl_active_extent, pfl_held_grant,
                                   lost_grant, wire_dropped, evicted,
                                   w1_grants, w1_rpc_approved, w2_grants,
                                   w2_rpc_approved, gs_target, wa_to_send,
                                   sf_grants, sf_consumed, dw_grants >>

W1_SubmitRPC == /\ pc["W1"] = "W1_SubmitRPC"
                /\ w1_rpc_approved' = FALSE
                /\ rpcs_in_flight' = rpcs_in_flight + 1
                /\ loi_lock' = "free"
                /\ pc' = [pc EXCEPT !["W1"] = "W1_Done"]
                /\ UNCHANGED << avail_grant, reserved_grant, dirty_grant,
                                returned_grant, max_rpcs, pfl_active_extent,
                                pfl_held_grant, lost_grant, wire_dropped,
                                evicted, w1_grants, w2_grants, w2_rpc_approved,
                                gs_target, wa_to_send, sf_grants, sf_consumed,
                                dw_grants >>

W1_Done == /\ pc["W1"] = "W1_Done"
           /\ TRUE
           /\ pc' = [pc EXCEPT !["W1"] = "Done"]
           /\ UNCHANGED << avail_grant, reserved_grant, dirty_grant,
                           returned_grant, rpcs_in_flight, max_rpcs,
                           pfl_active_extent, pfl_held_grant, lost_grant,
                           wire_dropped, evicted, loi_lock, w1_grants,
                           w1_rpc_approved, w2_grants, w2_rpc_approved,
                           gs_target, wa_to_send, sf_grants, sf_consumed,
                           dw_grants >>

Writer1 == W1_AcquireLock1 \/ W1_Reserve \/ W1_ExtentFind
              \/ W1_AcquireLock2 \/ W1_ConsumeDirty \/ W1_MaybeSteal
              \/ W1_AcquireLock3 \/ W1_CheckRPCs \/ W1_AcquireLock4
              \/ W1_SubmitRPC \/ W1_Done

W2_AcquireLock1 == /\ pc["W2"] = "W2_AcquireLock1"
                   /\ loi_lock = "free"
                   /\ loi_lock' = "W2"
                   /\ pc' = [pc EXCEPT !["W2"] = "W2_Reserve"]
                   /\ UNCHANGED << avail_grant, reserved_grant, dirty_grant,
                                   returned_grant, rpcs_in_flight, max_rpcs,
                                   pfl_active_extent, pfl_held_grant,
                                   lost_grant, wire_dropped, evicted,
                                   w1_grants, w1_rpc_approved, w2_grants,
                                   w2_rpc_approved, gs_target, wa_to_send,
                                   sf_grants, sf_consumed, dw_grants >>

W2_Reserve == /\ pc["W2"] = "W2_Reserve"
              /\ IF avail_grant >= 1
                    THEN /\ avail_grant' = avail_grant - 1
                         /\ reserved_grant' = reserved_grant + 1
                         /\ w2_grants' = 1
                         /\ loi_lock' = "free"
                         /\ pc' = [pc EXCEPT !["W2"] = "W2_ExtentFind"]
                    ELSE /\ loi_lock' = "free"
                         /\ pc' = [pc EXCEPT !["W2"] = "W2_Done"]
                         /\ UNCHANGED << avail_grant, reserved_grant,
                                         w2_grants >>
              /\ UNCHANGED << dirty_grant, returned_grant, rpcs_in_flight,
                              max_rpcs, pfl_active_extent, pfl_held_grant,
                              lost_grant, wire_dropped, evicted, w1_grants,
                              w1_rpc_approved, w2_rpc_approved, gs_target,
                              wa_to_send, sf_grants, sf_consumed, dw_grants >>

W2_ExtentFind == /\ pc["W2"] = "W2_ExtentFind"
                 /\ IF w2_grants < 1
                       THEN /\ Assert(FALSE,
                                      "Failure of assertion at line 243, column 9.")
                       ELSE /\ TRUE
                 /\ pc' = [pc EXCEPT !["W2"] = "W2_AcquireLock2"]
                 /\ UNCHANGED << avail_grant, reserved_grant, dirty_grant,
                                 returned_grant, rpcs_in_flight, max_rpcs,
                                 pfl_active_extent, pfl_held_grant, lost_grant,
                                 wire_dropped, evicted, loi_lock, w1_grants,
                                 w1_rpc_approved, w2_grants, w2_rpc_approved,
                                 gs_target, wa_to_send, sf_grants, sf_consumed,
                                 dw_grants >>

W2_AcquireLock2 == /\ pc["W2"] = "W2_AcquireLock2"
                   /\ loi_lock = "free"
                   /\ loi_lock' = "W2"
                   /\ pc' = [pc EXCEPT !["W2"] = "W2_ConsumeDirty"]
                   /\ UNCHANGED << avail_grant, reserved_grant, dirty_grant,
                                   returned_grant, rpcs_in_flight, max_rpcs,
                                   pfl_active_extent, pfl_held_grant,
                                   lost_grant, wire_dropped, evicted,
                                   w1_grants, w1_rpc_approved, w2_grants,
                                   w2_rpc_approved, gs_target, wa_to_send,
                                   sf_grants, sf_consumed, dw_grants >>

W2_ConsumeDirty == /\ pc["W2"] = "W2_ConsumeDirty"
                   /\ reserved_grant' = reserved_grant - 1
                   /\ dirty_grant' = dirty_grant + 1
                   /\ w2_grants' = 0
                   /\ loi_lock' = "free"
                   /\ pc' = [pc EXCEPT !["W2"] = "W2_MaybeSteal"]
                   /\ UNCHANGED << avail_grant, returned_grant, rpcs_in_flight,
                                   max_rpcs, pfl_active_extent, pfl_held_grant,
                                   lost_grant, wire_dropped, evicted,
                                   w1_grants, w1_rpc_approved, w2_rpc_approved,
                                   gs_target, wa_to_send, sf_grants,
                                   sf_consumed, dw_grants >>

W2_MaybeSteal == /\ pc["W2"] = "W2_MaybeSteal"
                 /\ \/ /\ TRUE
                       /\ pc' = [pc EXCEPT !["W2"] = "W2_AcquireLock3"]
                    \/ /\ IF InjectBug19709
                             THEN /\ pc' = [pc EXCEPT !["W2"] = "W2_ExtentFind"]
                             ELSE /\ pc' = [pc EXCEPT !["W2"] = "W2_AcquireLock1"]
                 /\ UNCHANGED << avail_grant, reserved_grant, dirty_grant,
                                 returned_grant, rpcs_in_flight, max_rpcs,
                                 pfl_active_extent, pfl_held_grant, lost_grant,
                                 wire_dropped, evicted, loi_lock, w1_grants,
                                 w1_rpc_approved, w2_grants, w2_rpc_approved,
                                 gs_target, wa_to_send, sf_grants, sf_consumed,
                                 dw_grants >>

W2_AcquireLock3 == /\ pc["W2"] = "W2_AcquireLock3"
                   /\ loi_lock = "free"
                   /\ loi_lock' = "W2"
                   /\ pc' = [pc EXCEPT !["W2"] = "W2_CheckRPCs"]
                   /\ UNCHANGED << avail_grant, reserved_grant, dirty_grant,
                                   returned_grant, rpcs_in_flight, max_rpcs,
                                   pfl_active_extent, pfl_held_grant,
                                   lost_grant, wire_dropped, evicted,
                                   w1_grants, w1_rpc_approved, w2_grants,
                                   w2_rpc_approved, gs_target, wa_to_send,
                                   sf_grants, sf_consumed, dw_grants >>

W2_CheckRPCs == /\ pc["W2"] = "W2_CheckRPCs"
                /\ IF rpcs_in_flight >= max_rpcs
                      THEN /\ loi_lock' = "free"
                           /\ pc' = [pc EXCEPT !["W2"] = "W2_Done"]
                           /\ UNCHANGED << rpcs_in_flight, w2_rpc_approved >>
                      ELSE /\ IF InjectBug19755
                                 THEN /\ w2_rpc_approved' = TRUE
                                      /\ loi_lock' = "free"
                                      /\ pc' = [pc EXCEPT !["W2"] = "W2_AcquireLock4"]
                                      /\ UNCHANGED rpcs_in_flight
                                 ELSE /\ rpcs_in_flight' = rpcs_in_flight + 1
                                      /\ loi_lock' = "free"
                                      /\ pc' = [pc EXCEPT !["W2"] = "W2_Done"]
                                      /\ UNCHANGED w2_rpc_approved
                /\ UNCHANGED << avail_grant, reserved_grant, dirty_grant,
                                returned_grant, max_rpcs, pfl_active_extent,
                                pfl_held_grant, lost_grant, wire_dropped,
                                evicted, w1_grants, w1_rpc_approved, w2_grants,
                                gs_target, wa_to_send, sf_grants, sf_consumed,
                                dw_grants >>

W2_AcquireLock4 == /\ pc["W2"] = "W2_AcquireLock4"
                   /\ loi_lock = "free"
                   /\ loi_lock' = "W2"
                   /\ pc' = [pc EXCEPT !["W2"] = "W2_SubmitRPC"]
                   /\ UNCHANGED << avail_grant, reserved_grant, dirty_grant,
                                   returned_grant, rpcs_in_flight, max_rpcs,
                                   pfl_active_extent, pfl_held_grant,
                                   lost_grant, wire_dropped, evicted,
                                   w1_grants, w1_rpc_approved, w2_grants,
                                   w2_rpc_approved, gs_target, wa_to_send,
                                   sf_grants, sf_consumed, dw_grants >>

W2_SubmitRPC == /\ pc["W2"] = "W2_SubmitRPC"
                /\ w2_rpc_approved' = FALSE
                /\ rpcs_in_flight' = rpcs_in_flight + 1
                /\ loi_lock' = "free"
                /\ pc' = [pc EXCEPT !["W2"] = "W2_Done"]
                /\ UNCHANGED << avail_grant, reserved_grant, dirty_grant,
                                returned_grant, max_rpcs, pfl_active_extent,
                                pfl_held_grant, lost_grant, wire_dropped,
                                evicted, w1_grants, w1_rpc_approved, w2_grants,
                                gs_target, wa_to_send, sf_grants, sf_consumed,
                                dw_grants >>

W2_Done == /\ pc["W2"] = "W2_Done"
           /\ TRUE
           /\ pc' = [pc EXCEPT !["W2"] = "Done"]
           /\ UNCHANGED << avail_grant, reserved_grant, dirty_grant,
                           returned_grant, rpcs_in_flight, max_rpcs,
                           pfl_active_extent, pfl_held_grant, lost_grant,
                           wire_dropped, evicted, loi_lock, w1_grants,
                           w1_rpc_approved, w2_grants, w2_rpc_approved,
                           gs_target, wa_to_send, sf_grants, sf_consumed,
                           dw_grants >>

Writer2 == W2_AcquireLock1 \/ W2_Reserve \/ W2_ExtentFind
              \/ W2_AcquireLock2 \/ W2_ConsumeDirty \/ W2_MaybeSteal
              \/ W2_AcquireLock3 \/ W2_CheckRPCs \/ W2_AcquireLock4
              \/ W2_SubmitRPC \/ W2_Done

GS_ComputeTarget == /\ pc["GS"] = "GS_ComputeTarget"
                    /\ loi_lock = "free"
                    /\ loi_lock' = "GS"
                    /\ pc' = [pc EXCEPT !["GS"] = "GS_ReadAvail"]
                    /\ UNCHANGED << avail_grant, reserved_grant, dirty_grant,
                                    returned_grant, rpcs_in_flight, max_rpcs,
                                    pfl_active_extent, pfl_held_grant,
                                    lost_grant, wire_dropped, evicted,
                                    w1_grants, w1_rpc_approved, w2_grants,
                                    w2_rpc_approved, gs_target, wa_to_send,
                                    sf_grants, sf_consumed, dw_grants >>

GS_ReadAvail == /\ pc["GS"] = "GS_ReadAvail"
                /\ IF avail_grant >= 2
                      THEN /\ gs_target' = 1
                           /\ loi_lock' = "free"
                           /\ pc' = [pc EXCEPT !["GS"] = "GS_AcquireLock"]
                      ELSE /\ loi_lock' = "free"
                           /\ pc' = [pc EXCEPT !["GS"] = "GS_Done"]
                           /\ UNCHANGED gs_target
                /\ UNCHANGED << avail_grant, reserved_grant, dirty_grant,
                                returned_grant, rpcs_in_flight, max_rpcs,
                                pfl_active_extent, pfl_held_grant, lost_grant,
                                wire_dropped, evicted, w1_grants,
                                w1_rpc_approved, w2_grants, w2_rpc_approved,
                                wa_to_send, sf_grants, sf_consumed, dw_grants >>

GS_AcquireLock == /\ pc["GS"] = "GS_AcquireLock"
                  /\ loi_lock = "free"
                  /\ loi_lock' = "GS"
                  /\ pc' = [pc EXCEPT !["GS"] = "GS_Shrink"]
                  /\ UNCHANGED << avail_grant, reserved_grant, dirty_grant,
                                  returned_grant, rpcs_in_flight, max_rpcs,
                                  pfl_active_extent, pfl_held_grant,
                                  lost_grant, wire_dropped, evicted, w1_grants,
                                  w1_rpc_approved, w2_grants, w2_rpc_approved,
                                  gs_target, wa_to_send, sf_grants,
                                  sf_consumed, dw_grants >>

GS_Shrink == /\ pc["GS"] = "GS_Shrink"
             /\ IF InjectBug11288
                   THEN /\ returned_grant' = returned_grant + (avail_grant - gs_target)
                        /\ avail_grant' = gs_target
                        /\ loi_lock' = "free"
                        /\ pc' = [pc EXCEPT !["GS"] = "GS_Done"]
                   ELSE /\ IF gs_target >= avail_grant
                              THEN /\ loi_lock' = "free"
                                   /\ pc' = [pc EXCEPT !["GS"] = "GS_Done"]
                                   /\ UNCHANGED << avail_grant, returned_grant >>
                              ELSE /\ returned_grant' = returned_grant + (avail_grant - gs_target)
                                   /\ avail_grant' = gs_target
                                   /\ loi_lock' = "free"
                                   /\ pc' = [pc EXCEPT !["GS"] = "GS_Done"]
             /\ UNCHANGED << reserved_grant, dirty_grant, rpcs_in_flight,
                             max_rpcs, pfl_active_extent, pfl_held_grant,
                             lost_grant, wire_dropped, evicted, w1_grants,
                             w1_rpc_approved, w2_grants, w2_rpc_approved,
                             gs_target, wa_to_send, sf_grants, sf_consumed,
                             dw_grants >>

GS_Done == /\ pc["GS"] = "GS_Done"
           /\ TRUE
           /\ pc' = [pc EXCEPT !["GS"] = "Done"]
           /\ UNCHANGED << avail_grant, reserved_grant, dirty_grant,
                           returned_grant, rpcs_in_flight, max_rpcs,
                           pfl_active_extent, pfl_held_grant, lost_grant,
                           wire_dropped, evicted, loi_lock, w1_grants,
                           w1_rpc_approved, w2_grants, w2_rpc_approved,
                           gs_target, wa_to_send, sf_grants, sf_consumed,
                           dw_grants >>

GrantShrink == GS_ComputeTarget \/ GS_ReadAvail \/ GS_AcquireLock
                  \/ GS_Shrink \/ GS_Done

PW_AcquireLock1 == /\ pc["PW"] = "PW_AcquireLock1"
                   /\ loi_lock = "free"
                   /\ loi_lock' = "PW"
                   /\ pc' = [pc EXCEPT !["PW"] = "PW_ReserveComp1"]
                   /\ UNCHANGED << avail_grant, reserved_grant, dirty_grant,
                                   returned_grant, rpcs_in_flight, max_rpcs,
                                   pfl_active_extent, pfl_held_grant,
                                   lost_grant, wire_dropped, evicted,
                                   w1_grants, w1_rpc_approved, w2_grants,
                                   w2_rpc_approved, gs_target, wa_to_send,
                                   sf_grants, sf_consumed, dw_grants >>

PW_ReserveComp1 == /\ pc["PW"] = "PW_ReserveComp1"
                   /\ IF avail_grant >= 1
                         THEN /\ avail_grant' = avail_grant - 1
                              /\ reserved_grant' = reserved_grant + 1
                              /\ loi_lock' = "free"
                              /\ pc' = [pc EXCEPT !["PW"] = "PW_AcquireLock2"]
                         ELSE /\ loi_lock' = "free"
                              /\ pc' = [pc EXCEPT !["PW"] = "PW_Done"]
                              /\ UNCHANGED << avail_grant, reserved_grant >>
                   /\ UNCHANGED << dirty_grant, returned_grant, rpcs_in_flight,
                                   max_rpcs, pfl_active_extent, pfl_held_grant,
                                   lost_grant, wire_dropped, evicted,
                                   w1_grants, w1_rpc_approved, w2_grants,
                                   w2_rpc_approved, gs_target, wa_to_send,
                                   sf_grants, sf_consumed, dw_grants >>

PW_AcquireLock2 == /\ pc["PW"] = "PW_AcquireLock2"
                   /\ loi_lock = "free"
                   /\ loi_lock' = "PW"
                   /\ pc' = [pc EXCEPT !["PW"] = "PW_ConsumeComp1"]
                   /\ UNCHANGED << avail_grant, reserved_grant, dirty_grant,
                                   returned_grant, rpcs_in_flight, max_rpcs,
                                   pfl_active_extent, pfl_held_grant,
                                   lost_grant, wire_dropped, evicted,
                                   w1_grants, w1_rpc_approved, w2_grants,
                                   w2_rpc_approved, gs_target, wa_to_send,
                                   sf_grants, sf_consumed, dw_grants >>

PW_ConsumeComp1 == /\ pc["PW"] = "PW_ConsumeComp1"
                   /\ reserved_grant' = reserved_grant - 1
                   /\ dirty_grant' = dirty_grant + 1
                   /\ pfl_active_extent' = TRUE
                   /\ pfl_held_grant' = 1
                   /\ loi_lock' = "free"
                   /\ pc' = [pc EXCEPT !["PW"] = "PW_SwitchComponent"]
                   /\ UNCHANGED << avail_grant, returned_grant, rpcs_in_flight,
                                   max_rpcs, lost_grant, wire_dropped, evicted,
                                   w1_grants, w1_rpc_approved, w2_grants,
                                   w2_rpc_approved, gs_target, wa_to_send,
                                   sf_grants, sf_consumed, dw_grants >>

PW_SwitchComponent == /\ pc["PW"] = "PW_SwitchComponent"
                      /\ IF InjectBug13100
                            THEN /\ TRUE
                                 /\ UNCHANGED << avail_grant, dirty_grant,
                                                 pfl_active_extent,
                                                 pfl_held_grant >>
                            ELSE /\ pfl_active_extent' = FALSE
                                 /\ pfl_held_grant' = 0
                                 /\ dirty_grant' = dirty_grant - 1
                                 /\ avail_grant' = avail_grant + 1
                      /\ pc' = [pc EXCEPT !["PW"] = "PW_AcquireLock3"]
                      /\ UNCHANGED << reserved_grant, returned_grant,
                                      rpcs_in_flight, max_rpcs, lost_grant,
                                      wire_dropped, evicted, loi_lock,
                                      w1_grants, w1_rpc_approved, w2_grants,
                                      w2_rpc_approved, gs_target, wa_to_send,
                                      sf_grants, sf_consumed, dw_grants >>

PW_AcquireLock3 == /\ pc["PW"] = "PW_AcquireLock3"
                   /\ loi_lock = "free" /\ avail_grant >= 1
                   /\ loi_lock' = "PW"
                   /\ pc' = [pc EXCEPT !["PW"] = "PW_ReserveComp2"]
                   /\ UNCHANGED << avail_grant, reserved_grant, dirty_grant,
                                   returned_grant, rpcs_in_flight, max_rpcs,
                                   pfl_active_extent, pfl_held_grant,
                                   lost_grant, wire_dropped, evicted,
                                   w1_grants, w1_rpc_approved, w2_grants,
                                   w2_rpc_approved, gs_target, wa_to_send,
                                   sf_grants, sf_consumed, dw_grants >>

PW_ReserveComp2 == /\ pc["PW"] = "PW_ReserveComp2"
                   /\ avail_grant' = avail_grant - 1
                   /\ reserved_grant' = reserved_grant + 1
                   /\ loi_lock' = "free"
                   /\ pc' = [pc EXCEPT !["PW"] = "PW_AcquireLock4"]
                   /\ UNCHANGED << dirty_grant, returned_grant, rpcs_in_flight,
                                   max_rpcs, pfl_active_extent, pfl_held_grant,
                                   lost_grant, wire_dropped, evicted,
                                   w1_grants, w1_rpc_approved, w2_grants,
                                   w2_rpc_approved, gs_target, wa_to_send,
                                   sf_grants, sf_consumed, dw_grants >>

PW_AcquireLock4 == /\ pc["PW"] = "PW_AcquireLock4"
                   /\ loi_lock = "free"
                   /\ loi_lock' = "PW"
                   /\ pc' = [pc EXCEPT !["PW"] = "PW_ConsumeComp2"]
                   /\ UNCHANGED << avail_grant, reserved_grant, dirty_grant,
                                   returned_grant, rpcs_in_flight, max_rpcs,
                                   pfl_active_extent, pfl_held_grant,
                                   lost_grant, wire_dropped, evicted,
                                   w1_grants, w1_rpc_approved, w2_grants,
                                   w2_rpc_approved, gs_target, wa_to_send,
                                   sf_grants, sf_consumed, dw_grants >>

PW_ConsumeComp2 == /\ pc["PW"] = "PW_ConsumeComp2"
                   /\ reserved_grant' = reserved_grant - 1
                   /\ dirty_grant' = dirty_grant + 1
                   /\ pfl_active_extent' = FALSE
                   /\ pfl_held_grant' = 0
                   /\ loi_lock' = "free"
                   /\ pc' = [pc EXCEPT !["PW"] = "PW_Done"]
                   /\ UNCHANGED << avail_grant, returned_grant, rpcs_in_flight,
                                   max_rpcs, lost_grant, wire_dropped, evicted,
                                   w1_grants, w1_rpc_approved, w2_grants,
                                   w2_rpc_approved, gs_target, wa_to_send,
                                   sf_grants, sf_consumed, dw_grants >>

PW_Done == /\ pc["PW"] = "PW_Done"
           /\ TRUE
           /\ pc' = [pc EXCEPT !["PW"] = "Done"]
           /\ UNCHANGED << avail_grant, reserved_grant, dirty_grant,
                           returned_grant, rpcs_in_flight, max_rpcs,
                           pfl_active_extent, pfl_held_grant, lost_grant,
                           wire_dropped, evicted, loi_lock, w1_grants,
                           w1_rpc_approved, w2_grants, w2_rpc_approved,
                           gs_target, wa_to_send, sf_grants, sf_consumed,
                           dw_grants >>

PFLWriter == PW_AcquireLock1 \/ PW_ReserveComp1 \/ PW_AcquireLock2
                \/ PW_ConsumeComp1 \/ PW_SwitchComponent \/ PW_AcquireLock3
                \/ PW_ReserveComp2 \/ PW_AcquireLock4 \/ PW_ConsumeComp2
                \/ PW_Done

RC_Wait == /\ pc["RC"] = "RC_Wait"
           /\ rpcs_in_flight > 0
           /\ pc' = [pc EXCEPT !["RC"] = "RC_AcquireLock"]
           /\ UNCHANGED << avail_grant, reserved_grant, dirty_grant,
                           returned_grant, rpcs_in_flight, max_rpcs,
                           pfl_active_extent, pfl_held_grant, lost_grant,
                           wire_dropped, evicted, loi_lock, w1_grants,
                           w1_rpc_approved, w2_grants, w2_rpc_approved,
                           gs_target, wa_to_send, sf_grants, sf_consumed,
                           dw_grants >>

RC_AcquireLock == /\ pc["RC"] = "RC_AcquireLock"
                  /\ loi_lock = "free"
                  /\ loi_lock' = "RC"
                  /\ pc' = [pc EXCEPT !["RC"] = "RC_Complete"]
                  /\ UNCHANGED << avail_grant, reserved_grant, dirty_grant,
                                  returned_grant, rpcs_in_flight, max_rpcs,
                                  pfl_active_extent, pfl_held_grant,
                                  lost_grant, wire_dropped, evicted, w1_grants,
                                  w1_rpc_approved, w2_grants, w2_rpc_approved,
                                  gs_target, wa_to_send, sf_grants,
                                  sf_consumed, dw_grants >>

RC_Complete == /\ pc["RC"] = "RC_Complete"
               /\ rpcs_in_flight' = rpcs_in_flight - 1
               /\ IF dirty_grant > pfl_held_grant
                     THEN /\ dirty_grant' = dirty_grant - 1
                          /\ avail_grant' = avail_grant + 1
                     ELSE /\ TRUE
                          /\ UNCHANGED << avail_grant, dirty_grant >>
               /\ loi_lock' = "free"
               /\ pc' = [pc EXCEPT !["RC"] = "RC_Wait"]
               /\ UNCHANGED << reserved_grant, returned_grant, max_rpcs,
                               pfl_active_extent, pfl_held_grant, lost_grant,
                               wire_dropped, evicted, w1_grants,
                               w1_rpc_approved, w2_grants, w2_rpc_approved,
                               gs_target, wa_to_send, sf_grants, sf_consumed,
                               dw_grants >>

RC_Done == /\ pc["RC"] = "RC_Done"
           /\ TRUE
           /\ pc' = [pc EXCEPT !["RC"] = "Done"]
           /\ UNCHANGED << avail_grant, reserved_grant, dirty_grant,
                           returned_grant, rpcs_in_flight, max_rpcs,
                           pfl_active_extent, pfl_held_grant, lost_grant,
                           wire_dropped, evicted, loi_lock, w1_grants,
                           w1_rpc_approved, w2_grants, w2_rpc_approved,
                           gs_target, wa_to_send, sf_grants, sf_consumed,
                           dw_grants >>

RPCComplete == RC_Wait \/ RC_AcquireLock \/ RC_Complete \/ RC_Done

WA_AcquireLock == /\ pc["WA"] = "WA_AcquireLock"
                  /\ loi_lock = "free" /\ lost_grant > 0
                  /\ loi_lock' = "WA"
                  /\ pc' = [pc EXCEPT !["WA"] = "WA_PackWire"]
                  /\ UNCHANGED << avail_grant, reserved_grant, dirty_grant,
                                  returned_grant, rpcs_in_flight, max_rpcs,
                                  pfl_active_extent, pfl_held_grant,
                                  lost_grant, wire_dropped, evicted, w1_grants,
                                  w1_rpc_approved, w2_grants, w2_rpc_approved,
                                  gs_target, wa_to_send, sf_grants,
                                  sf_consumed, dw_grants >>

WA_PackWire == /\ pc["WA"] = "WA_PackWire"
               /\ IF lost_grant > WIRE_MAX
                     THEN /\ wa_to_send' = WIRE_MAX
                     ELSE /\ wa_to_send' = lost_grant
               /\ pc' = [pc EXCEPT !["WA"] = "WA_SendOnWire"]
               /\ UNCHANGED << avail_grant, reserved_grant, dirty_grant,
                               returned_grant, rpcs_in_flight, max_rpcs,
                               pfl_active_extent, pfl_held_grant, lost_grant,
                               wire_dropped, evicted, loi_lock, w1_grants,
                               w1_rpc_approved, w2_grants, w2_rpc_approved,
                               gs_target, sf_grants, sf_consumed, dw_grants >>

WA_SendOnWire == /\ pc["WA"] = "WA_SendOnWire"
                 /\ wire_dropped' = wire_dropped + wa_to_send
                 /\ IF InjectBug14125
                       THEN /\ lost_grant' = 0
                       ELSE /\ lost_grant' = lost_grant - wa_to_send
                 /\ loi_lock' = "free"
                 /\ pc' = [pc EXCEPT !["WA"] = "WA_Done"]
                 /\ UNCHANGED << avail_grant, reserved_grant, dirty_grant,
                                 returned_grant, rpcs_in_flight, max_rpcs,
                                 pfl_active_extent, pfl_held_grant, evicted,
                                 w1_grants, w1_rpc_approved, w2_grants,
                                 w2_rpc_approved, gs_target, wa_to_send,
                                 sf_grants, sf_consumed, dw_grants >>

WA_Done == /\ pc["WA"] = "WA_Done"
           /\ TRUE
           /\ pc' = [pc EXCEPT !["WA"] = "Done"]
           /\ UNCHANGED << avail_grant, reserved_grant, dirty_grant,
                           returned_grant, rpcs_in_flight, max_rpcs,
                           pfl_active_extent, pfl_held_grant, lost_grant,
                           wire_dropped, evicted, loi_lock, w1_grants,
                           w1_rpc_approved, w2_grants, w2_rpc_approved,
                           gs_target, wa_to_send, sf_grants, sf_consumed,
                           dw_grants >>

WireAnnounce == WA_AcquireLock \/ WA_PackWire \/ WA_SendOnWire \/ WA_Done

LA_AcquireLock1 == /\ pc["LA"] = "LA_AcquireLock1"
                   /\ loi_lock = "free" /\ avail_grant >= 1
                   /\ loi_lock' = "LA"
                   /\ pc' = [pc EXCEPT !["LA"] = "LA_AddLost1"]
                   /\ UNCHANGED << avail_grant, reserved_grant, dirty_grant,
                                   returned_grant, rpcs_in_flight, max_rpcs,
                                   pfl_active_extent, pfl_held_grant,
                                   lost_grant, wire_dropped, evicted,
                                   w1_grants, w1_rpc_approved, w2_grants,
                                   w2_rpc_approved, gs_target, wa_to_send,
                                   sf_grants, sf_consumed, dw_grants >>

LA_AddLost1 == /\ pc["LA"] = "LA_AddLost1"
               /\ lost_grant' = lost_grant + 1
               /\ avail_grant' = avail_grant - 1
               /\ loi_lock' = "free"
               /\ pc' = [pc EXCEPT !["LA"] = "LA_AcquireLock2"]
               /\ UNCHANGED << reserved_grant, dirty_grant, returned_grant,
                               rpcs_in_flight, max_rpcs, pfl_active_extent,
                               pfl_held_grant, wire_dropped, evicted,
                               w1_grants, w1_rpc_approved, w2_grants,
                               w2_rpc_approved, gs_target, wa_to_send,
                               sf_grants, sf_consumed, dw_grants >>

LA_AcquireLock2 == /\ pc["LA"] = "LA_AcquireLock2"
                   /\ loi_lock = "free" /\ avail_grant >= 1
                   /\ loi_lock' = "LA"
                   /\ pc' = [pc EXCEPT !["LA"] = "LA_AddLost2"]
                   /\ UNCHANGED << avail_grant, reserved_grant, dirty_grant,
                                   returned_grant, rpcs_in_flight, max_rpcs,
                                   pfl_active_extent, pfl_held_grant,
                                   lost_grant, wire_dropped, evicted,
                                   w1_grants, w1_rpc_approved, w2_grants,
                                   w2_rpc_approved, gs_target, wa_to_send,
                                   sf_grants, sf_consumed, dw_grants >>

LA_AddLost2 == /\ pc["LA"] = "LA_AddLost2"
               /\ lost_grant' = lost_grant + 1
               /\ avail_grant' = avail_grant - 1
               /\ loi_lock' = "free"
               /\ pc' = [pc EXCEPT !["LA"] = "LA_Done"]
               /\ UNCHANGED << reserved_grant, dirty_grant, returned_grant,
                               rpcs_in_flight, max_rpcs, pfl_active_extent,
                               pfl_held_grant, wire_dropped, evicted,
                               w1_grants, w1_rpc_approved, w2_grants,
                               w2_rpc_approved, gs_target, wa_to_send,
                               sf_grants, sf_consumed, dw_grants >>

LA_Done == /\ pc["LA"] = "LA_Done"
           /\ TRUE
           /\ pc' = [pc EXCEPT !["LA"] = "Done"]
           /\ UNCHANGED << avail_grant, reserved_grant, dirty_grant,
                           returned_grant, rpcs_in_flight, max_rpcs,
                           pfl_active_extent, pfl_held_grant, lost_grant,
                           wire_dropped, evicted, loi_lock, w1_grants,
                           w1_rpc_approved, w2_grants, w2_rpc_approved,
                           gs_target, wa_to_send, sf_grants, sf_consumed,
                           dw_grants >>

LostAccum == LA_AcquireLock1 \/ LA_AddLost1 \/ LA_AcquireLock2
                \/ LA_AddLost2 \/ LA_Done

Sy_AcquireLock1 == /\ pc["Sy"] = "Sy_AcquireLock1"
                   /\ loi_lock = "free"
                   /\ loi_lock' = "Sy"
                   /\ pc' = [pc EXCEPT !["Sy"] = "Sy_Reserve"]
                   /\ UNCHANGED << avail_grant, reserved_grant, dirty_grant,
                                   returned_grant, rpcs_in_flight, max_rpcs,
                                   pfl_active_extent, pfl_held_grant,
                                   lost_grant, wire_dropped, evicted,
                                   w1_grants, w1_rpc_approved, w2_grants,
                                   w2_rpc_approved, gs_target, wa_to_send,
                                   sf_grants, sf_consumed, dw_grants >>

Sy_Reserve == /\ pc["Sy"] = "Sy_Reserve"
              /\ IF avail_grant >= 1
                    THEN /\ avail_grant' = avail_grant - 1
                         /\ reserved_grant' = reserved_grant + 1
                         /\ sf_grants' = 1
                         /\ loi_lock' = "free"
                         /\ pc' = [pc EXCEPT !["Sy"] = "Sy_FallbackToSync"]
                    ELSE /\ loi_lock' = "free"
                         /\ pc' = [pc EXCEPT !["Sy"] = "Sy_Done"]
                         /\ UNCHANGED << avail_grant, reserved_grant,
                                         sf_grants >>
              /\ UNCHANGED << dirty_grant, returned_grant, rpcs_in_flight,
                              max_rpcs, pfl_active_extent, pfl_held_grant,
                              lost_grant, wire_dropped, evicted, w1_grants,
                              w1_rpc_approved, w2_grants, w2_rpc_approved,
                              gs_target, wa_to_send, sf_consumed, dw_grants >>

Sy_FallbackToSync == /\ pc["Sy"] = "Sy_FallbackToSync"
                     /\ IF InjectBug14901
                           THEN /\ sf_consumed' = FALSE
                                /\ pc' = [pc EXCEPT !["Sy"] = "Sy_SyncSubmit"]
                           ELSE /\ pc' = [pc EXCEPT !["Sy"] = "Sy_AcquireLock2"]
                                /\ UNCHANGED sf_consumed
                     /\ UNCHANGED << avail_grant, reserved_grant, dirty_grant,
                                     returned_grant, rpcs_in_flight, max_rpcs,
                                     pfl_active_extent, pfl_held_grant,
                                     lost_grant, wire_dropped, evicted,
                                     loi_lock, w1_grants, w1_rpc_approved,
                                     w2_grants, w2_rpc_approved, gs_target,
                                     wa_to_send, sf_grants, dw_grants >>

Sy_AcquireLock2 == /\ pc["Sy"] = "Sy_AcquireLock2"
                   /\ loi_lock = "free"
                   /\ loi_lock' = "Sy"
                   /\ pc' = [pc EXCEPT !["Sy"] = "Sy_ConsumeSync"]
                   /\ UNCHANGED << avail_grant, reserved_grant, dirty_grant,
                                   returned_grant, rpcs_in_flight, max_rpcs,
                                   pfl_active_extent, pfl_held_grant,
                                   lost_grant, wire_dropped, evicted,
                                   w1_grants, w1_rpc_approved, w2_grants,
                                   w2_rpc_approved, gs_target, wa_to_send,
                                   sf_grants, sf_consumed, dw_grants >>

Sy_ConsumeSync == /\ pc["Sy"] = "Sy_ConsumeSync"
                  /\ reserved_grant' = reserved_grant - 1
                  /\ dirty_grant' = dirty_grant + 1
                  /\ sf_grants' = 0
                  /\ sf_consumed' = TRUE
                  /\ loi_lock' = "free"
                  /\ pc' = [pc EXCEPT !["Sy"] = "Sy_SyncSubmit"]
                  /\ UNCHANGED << avail_grant, returned_grant, rpcs_in_flight,
                                  max_rpcs, pfl_active_extent, pfl_held_grant,
                                  lost_grant, wire_dropped, evicted, w1_grants,
                                  w1_rpc_approved, w2_grants, w2_rpc_approved,
                                  gs_target, wa_to_send, dw_grants >>

Sy_SyncSubmit == /\ pc["Sy"] = "Sy_SyncSubmit"
                 /\ IF sf_consumed = FALSE
                       THEN /\ Assert(FALSE,
                                      "Failure of assertion at line 617, column 9.")
                       ELSE /\ TRUE
                 /\ pc' = [pc EXCEPT !["Sy"] = "Sy_Done"]
                 /\ UNCHANGED << avail_grant, reserved_grant, dirty_grant,
                                 returned_grant, rpcs_in_flight, max_rpcs,
                                 pfl_active_extent, pfl_held_grant, lost_grant,
                                 wire_dropped, evicted, loi_lock, w1_grants,
                                 w1_rpc_approved, w2_grants, w2_rpc_approved,
                                 gs_target, wa_to_send, sf_grants, sf_consumed,
                                 dw_grants >>

Sy_Done == /\ pc["Sy"] = "Sy_Done"
           /\ TRUE
           /\ pc' = [pc EXCEPT !["Sy"] = "Done"]
           /\ UNCHANGED << avail_grant, reserved_grant, dirty_grant,
                           returned_grant, rpcs_in_flight, max_rpcs,
                           pfl_active_extent, pfl_held_grant, lost_grant,
                           wire_dropped, evicted, loi_lock, w1_grants,
                           w1_rpc_approved, w2_grants, w2_rpc_approved,
                           gs_target, wa_to_send, sf_grants, sf_consumed,
                           dw_grants >>

SyncFallback == Sy_AcquireLock1 \/ Sy_Reserve \/ Sy_FallbackToSync
                   \/ Sy_AcquireLock2 \/ Sy_ConsumeSync \/ Sy_SyncSubmit
                   \/ Sy_Done

DW_AcquireLock1 == /\ pc["DW"] = "DW_AcquireLock1"
                   /\ loi_lock = "free"
                   /\ loi_lock' = "DW"
                   /\ pc' = [pc EXCEPT !["DW"] = "DW_TryReserve"]
                   /\ UNCHANGED << avail_grant, reserved_grant, dirty_grant,
                                   returned_grant, rpcs_in_flight, max_rpcs,
                                   pfl_active_extent, pfl_held_grant,
                                   lost_grant, wire_dropped, evicted,
                                   w1_grants, w1_rpc_approved, w2_grants,
                                   w2_rpc_approved, gs_target, wa_to_send,
                                   sf_grants, sf_consumed, dw_grants >>

DW_TryReserve == /\ pc["DW"] = "DW_TryReserve"
                 /\ IF InjectBug12687
                       THEN /\ loi_lock' = "free"
                            /\ pc' = [pc EXCEPT !["DW"] = "DW_SubmitDIO"]
                            /\ UNCHANGED << avail_grant, dirty_grant,
                                            dw_grants >>
                       ELSE /\ IF avail_grant >= 1
                                  THEN /\ avail_grant' = avail_grant - 1
                                       /\ dirty_grant' = dirty_grant + 1
                                       /\ dw_grants' = 1
                                       /\ loi_lock' = "free"
                                       /\ pc' = [pc EXCEPT !["DW"] = "DW_SubmitDIO"]
                                  ELSE /\ loi_lock' = "free"
                                       /\ pc' = [pc EXCEPT !["DW"] = "DW_Done"]
                                       /\ UNCHANGED << avail_grant,
                                                       dirty_grant, dw_grants >>
                 /\ UNCHANGED << reserved_grant, returned_grant,
                                 rpcs_in_flight, max_rpcs, pfl_active_extent,
                                 pfl_held_grant, lost_grant, wire_dropped,
                                 evicted, w1_grants, w1_rpc_approved,
                                 w2_grants, w2_rpc_approved, gs_target,
                                 wa_to_send, sf_grants, sf_consumed >>

DW_SubmitDIO == /\ pc["DW"] = "DW_SubmitDIO"
                /\ IF dw_grants < 1
                      THEN /\ Assert(FALSE,
                                     "Failure of assertion at line 670, column 9.")
                      ELSE /\ TRUE
                /\ pc' = [pc EXCEPT !["DW"] = "DW_Done"]
                /\ UNCHANGED << avail_grant, reserved_grant, dirty_grant,
                                returned_grant, rpcs_in_flight, max_rpcs,
                                pfl_active_extent, pfl_held_grant, lost_grant,
                                wire_dropped, evicted, loi_lock, w1_grants,
                                w1_rpc_approved, w2_grants, w2_rpc_approved,
                                gs_target, wa_to_send, sf_grants, sf_consumed,
                                dw_grants >>

DW_Done == /\ pc["DW"] = "DW_Done"
           /\ TRUE
           /\ pc' = [pc EXCEPT !["DW"] = "Done"]
           /\ UNCHANGED << avail_grant, reserved_grant, dirty_grant,
                           returned_grant, rpcs_in_flight, max_rpcs,
                           pfl_active_extent, pfl_held_grant, lost_grant,
                           wire_dropped, evicted, loi_lock, w1_grants,
                           w1_rpc_approved, w2_grants, w2_rpc_approved,
                           gs_target, wa_to_send, sf_grants, sf_consumed,
                           dw_grants >>

DIOWriter == DW_AcquireLock1 \/ DW_TryReserve \/ DW_SubmitDIO \/ DW_Done

EV_WaitEnabled == /\ pc["EV"] = "EV_WaitEnabled"
                  /\ IF ~EnableEviction
                        THEN /\ pc' = [pc EXCEPT !["EV"] = "EV_Done"]
                        ELSE /\ pc' = [pc EXCEPT !["EV"] = "EV_AcquireLock"]
                  /\ UNCHANGED << avail_grant, reserved_grant, dirty_grant,
                                  returned_grant, rpcs_in_flight, max_rpcs,
                                  pfl_active_extent, pfl_held_grant,
                                  lost_grant, wire_dropped, evicted, loi_lock,
                                  w1_grants, w1_rpc_approved, w2_grants,
                                  w2_rpc_approved, gs_target, wa_to_send,
                                  sf_grants, sf_consumed, dw_grants >>

EV_AcquireLock == /\ pc["EV"] = "EV_AcquireLock"
                  /\ loi_lock = "free" /\ dirty_grant > 0 /\ ~evicted
                  /\ loi_lock' = "EV"
                  /\ pc' = [pc EXCEPT !["EV"] = "EV_Disconnect"]
                  /\ UNCHANGED << avail_grant, reserved_grant, dirty_grant,
                                  returned_grant, rpcs_in_flight, max_rpcs,
                                  pfl_active_extent, pfl_held_grant,
                                  lost_grant, wire_dropped, evicted, w1_grants,
                                  w1_rpc_approved, w2_grants, w2_rpc_approved,
                                  gs_target, wa_to_send, sf_grants,
                                  sf_consumed, dw_grants >>

EV_Disconnect == /\ pc["EV"] = "EV_Disconnect"
                 /\ returned_grant' = returned_grant + avail_grant + lost_grant
                 /\ avail_grant' = 0
                 /\ lost_grant' = 0
                 /\ evicted' = TRUE
                 /\ loi_lock' = "free"
                 /\ pc' = [pc EXCEPT !["EV"] = "EV_Done"]
                 /\ UNCHANGED << reserved_grant, dirty_grant, rpcs_in_flight,
                                 max_rpcs, pfl_active_extent, pfl_held_grant,
                                 wire_dropped, w1_grants, w1_rpc_approved,
                                 w2_grants, w2_rpc_approved, gs_target,
                                 wa_to_send, sf_grants, sf_consumed, dw_grants >>

EV_Done == /\ pc["EV"] = "EV_Done"
           /\ TRUE
           /\ pc' = [pc EXCEPT !["EV"] = "Done"]
           /\ UNCHANGED << avail_grant, reserved_grant, dirty_grant,
                           returned_grant, rpcs_in_flight, max_rpcs,
                           pfl_active_extent, pfl_held_grant, lost_grant,
                           wire_dropped, evicted, loi_lock, w1_grants,
                           w1_rpc_approved, w2_grants, w2_rpc_approved,
                           gs_target, wa_to_send, sf_grants, sf_consumed,
                           dw_grants >>

Eviction == EV_WaitEnabled \/ EV_AcquireLock \/ EV_Disconnect \/ EV_Done

TR_AcquireLock == /\ pc["TR"] = "TR_AcquireLock"
                  /\ loi_lock = "free" /\ dirty_grant > pfl_held_grant
                  /\ loi_lock' = "TR"
                  /\ pc' = [pc EXCEPT !["TR"] = "TR_FreeGrant"]
                  /\ UNCHANGED << avail_grant, reserved_grant, dirty_grant,
                                  returned_grant, rpcs_in_flight, max_rpcs,
                                  pfl_active_extent, pfl_held_grant,
                                  lost_grant, wire_dropped, evicted, w1_grants,
                                  w1_rpc_approved, w2_grants, w2_rpc_approved,
                                  gs_target, wa_to_send, sf_grants,
                                  sf_consumed, dw_grants >>

TR_FreeGrant == /\ pc["TR"] = "TR_FreeGrant"
                /\ IF dirty_grant > pfl_held_grant /\ avail_grant = 0
                      THEN /\ dirty_grant' = dirty_grant - 1
                           /\ avail_grant' = 1
                           /\ UNCHANGED lost_grant
                      ELSE /\ IF dirty_grant > pfl_held_grant
                                 THEN /\ dirty_grant' = dirty_grant - 1
                                      /\ lost_grant' = lost_grant + 1
                                 ELSE /\ TRUE
                                      /\ UNCHANGED << dirty_grant, lost_grant >>
                           /\ UNCHANGED avail_grant
                /\ loi_lock' = "free"
                /\ pc' = [pc EXCEPT !["TR"] = "TR_Done"]
                /\ UNCHANGED << reserved_grant, returned_grant, rpcs_in_flight,
                                max_rpcs, pfl_active_extent, pfl_held_grant,
                                wire_dropped, evicted, w1_grants,
                                w1_rpc_approved, w2_grants, w2_rpc_approved,
                                gs_target, wa_to_send, sf_grants, sf_consumed,
                                dw_grants >>

TR_Done == /\ pc["TR"] = "TR_Done"
           /\ TRUE
           /\ pc' = [pc EXCEPT !["TR"] = "Done"]
           /\ UNCHANGED << avail_grant, reserved_grant, dirty_grant,
                           returned_grant, rpcs_in_flight, max_rpcs,
                           pfl_active_extent, pfl_held_grant, lost_grant,
                           wire_dropped, evicted, loi_lock, w1_grants,
                           w1_rpc_approved, w2_grants, w2_rpc_approved,
                           gs_target, wa_to_send, sf_grants, sf_consumed,
                           dw_grants >>

Truncate == TR_AcquireLock \/ TR_FreeGrant \/ TR_Done

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == Writer1 \/ Writer2 \/ GrantShrink \/ PFLWriter \/ RPCComplete
           \/ WireAnnounce \/ LostAccum \/ SyncFallback \/ DIOWriter \/ Eviction
           \/ Truncate
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Writer1)
        /\ WF_vars(Writer2)
        /\ WF_vars(GrantShrink)
        /\ WF_vars(PFLWriter)
        /\ WF_vars(RPCComplete)
        /\ WF_vars(WireAnnounce)
        /\ WF_vars(LostAccum)
        /\ WF_vars(SyncFallback)
        /\ WF_vars(DIOWriter)
        /\ WF_vars(Eviction)
        /\ WF_vars(Truncate)

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

\* === Dirty page accounting invariants (require process-local vars) ===

\* (c) Writers' locally-held reserved grants must be backed by the
\* global reserved_grant pool.  Grant shrink only touches avail_grant;
\* this ensures no path (including concurrent shrink) steals from
\* reserved grants, desynchronizing writer-local accounting from
\* global state.  Defined outside PlusCal because it references
\* process-local variables (w1_grants, w2_grants, sf_grants).
ShrinkWriteAtomicity ==
    reserved_grant >= w1_grants + w2_grants + sf_grants

====
