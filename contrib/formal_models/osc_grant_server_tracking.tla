-------------------- MODULE osc_grant_server_tracking --------------------
(*
 * Server-side OSC grant tracking model.
 *
 * Models the server's per-client grant record (srv_client_grant) and
 * the client's import grant (cl_import_grant) across connect, shrink,
 * eviction, and write RPC operations.  Verifies that when the system
 * is quiescent (no grant operations in flight), the server and client
 * agree on the grant amount.
 *
 * This complements the existing client-side models (osc_grant_model.tla,
 * osc_grant_eviction_race.tla) by adding the server-side perspective.
 * Those models verify internal client accounting; this model verifies
 * client-server agreement.
 *
 * Processes:
 *   GrantConnect ("GC") - server allocates grant, sends to client
 *   ShrinkOp ("SK")     - server sends shrink, client acks, server records
 *   Eviction ("EV")     - server reclaims grant, client zeros
 *   Writer ("W")        - background IO: reserve -> consume loop
 *   WriteRPC ("WR")     - client sends dirty to server via write BRW RPC
 *
 * Bug A (InjectBugA): Server sends grant on connect but doesn't record
 *   it in srv_client_grant.  At quiescence, server understates the
 *   client's grant.
 *
 *   Real-world analogue: ofd_grant_connect() sends ocd_grant in the
 *   CONNECT reply but fails to update ofd->ofd_tot_granted.  The
 *   server later sends a shrink based on stale ofd_tot_granted,
 *   or eviction reclaims less than the client actually held.
 *
 * Bug B (InjectBugB): Client processes shrink and acks, but server
 *   doesn't update srv_client_grant on receiving the ack.  At
 *   quiescence, server overstates the client's grant.
 *
 *   Real-world analogue: ofd_grant_shrink() sends the decrease
 *   notification but the callback that processes the ack
 *   (ofd_after_request -> ofd_grant_prepare) doesn't subtract
 *   the returned grant from ofd_tot_granted.
 *
 * Bug C (InjectBugC / LU-17933): A write RPC makes the server allocate
 *   additional grant to the export (tgt_grant_prepare_write ->
 *   tgt_grant_alloc records it in ted_grant/tgd_tot_granted and puts
 *   it in the reply's oa->o_grant).  If the write then fails, the
 *   reply carries no grant (tgt_grant_prepare_read zeroes o_grant), so
 *   the client never receives it, but the server keeps it recorded.
 *   At quiescence the server overstates the client's grant by the
 *   amount allocated for the failed RPC.
 *
 *   Fix df2b5d99ad "do not break grants on RPC failure" adds
 *   tgt_grant_dealloc(), called on the ofd_preprw_write /
 *   ofd_commitrw_write error paths, which subtracts the undelivered
 *   o_grant from ted_grant/tgd_tot_granted unless the export is
 *   already disconnected (LU-19016 a91c46a7da then also zeroes
 *   o_grant).  Until validation against 47638add78 this model had the
 *   mechanism inverted (server zeroing ted_grant on failure); see
 *   Validation notes.
 *
 * Bug D (InjectBugD / LU-14543): During disconnect, server does blind
 *   subtraction tgd_tot_granted -= ted_grant without bounds check.
 *   If a prior bug (like Bug C) has corrupted ted_grant or
 *   tgd_tot_granted, the subtraction underflows.
 *
 *   Real-world analogue: tgt_grant_discard() subtracts ted_grant from
 *   tgd_tot_granted.  If tgd_tot_granted < ted_grant (due to prior
 *   accounting errors), the unsigned subtraction wraps around, making
 *   tgd_tot_granted enormous.  Fix: clamp to 0.
 *
 * Bug E (InjectBugE / LU-13766): After server reboot, per-export grant
 *   is 0 but client retains dirty pages from the pre-reboot session.
 *   Write RPCs arrive before reconnect establishes grant, causing
 *   "claims X GRANT, real grant 0" errors.
 *
 *   Real-world analogue: server reboots, loses tgd_tot_granted and
 *   all ted_grant records.  Client reconnects with pre-existing dirty
 *   and sends write RPCs.  Server sees client claiming grant it hasn't
 *   allocated.  Fix: block writes until reconnect completes and
 *   re-establishes per-export grant.
 *
 * Configurations:
 *   baseline                       - all bugs off, all invariants (pass)
 *   connect_norecord_bug           - Bug A active (fail: QuiescentConsistency)
 *   connect_norecord_fix           - Bug A off (pass)
 *   shrink_norecord_bug            - Bug B active (fail: QuiescentConsistency)
 *   shrink_norecord_fix            - Bug B off (pass)
 *   LU17933_bug                    - Bug C active (fail: QuiescentConsistency)
 *   LU17933_fix                    - Bug C off (pass)
 *   LU14543_bug                    - Bug D active (fail: NoNegativeGrant)
 *   LU14543_fix                    - Bug D off (pass: defensive clamp)
 *   LU13766_bug                    - Bug E active, INITIAL_DIRTY=1 (fail: WriteRequiresConnection)
 *   LU13766_fix                    - Bug E off, INITIAL_DIRTY=1 (pass)
 *
 * Source (lustre-release master 47638add78):
 *   The server side is lustre/target/tgt_grant.c (tgd_grant_lock):
 *     tgt_grant_connect()      1024-1091  alloc at 1068, ocd_grant =
 *                                         ted_grant 1072 (GC_ServerAllocate)
 *     tgt_grant_alloc()        884-977    tgd_tot_granted/ted_grant +=
 *                                         grant 954-955 (WR_ServerProcess)
 *     tgt_grant_dealloc()      988-1006   undo undelivered alloc unless
 *                                         disconnected 1000-1003
 *                                         (WR_Failure, Bug C fix)
 *     tgt_grant_shrink()       581-615    ted_grant/tgd_tot_granted -=
 *                                         o_grant 606-607 (SK_ServerAck)
 *     tgt_grant_discard()      1104-1153  tgd_tot_granted -= ted_grant
 *                                         1139; recalc when tot < ted
 *                                         1116-1137 (Bug D fix, LU-14543
 *                                         bb5d81ea95); ted_grant = 0 1142
 *                                         (EV_ServerReclaim)
 *     tgt_grant_check()        698-861    "claims %lu GRANT, real grant"
 *                                         at 744 (Bug E symptom); replay
 *                                         and OBD_FL_RECOV_RESEND skip
 *                                         715-728
 *     tgt_grant_prepare_read() 1169-1228  o_grant = 0 at 1222 (failed
 *                                         write reply, Bug C)
 *   lustre/ofd/ofd_io.c ofd_preprw_write 869-872 and ofd_commitrw_write
 *     1420-1424: tgt_grant_commit + tgt_grant_dealloc on error
 *   lustre/ofd/ofd_dev.c ofd_set_info_hdl 809-881: KEY_GRANT_SHRINK RPC
 *   The client side is lustre/osc/osc_request.c (cl_loi_list_lock):
 *     osc_init_grant()         1002-1066  cl_avail_grant = ocd_grant -
 *                                         reserved - dirty, 1013-1027
 *                                         (GC_ClientApply)
 *     osc_shrink_grant_to_target() 829-879 client reduces cl_avail_grant
 *                                         855-863 then sends the shrink
 *                                         RPC (SK_ClientProcess)
 *     osc_update_grant()       756-762    reply o_grant added to
 *                                         cl_avail_grant, from
 *                                         osc_brw_fini_request 2200
 *                                         (WR_SuccessApply)
 *     osc_import_event()       3896-3970  IMP_EVENT_DISCON 3907-3913
 *                                         (EV_ClientZero)
 *   lustre/osc/osc_cache.c osc_reserve_grant 1515-1525 and
 *     osc_unreserve_grant_no_wake 1527-1545 (Writer)
 *
 * Validated against: lustre-release master 47638add78 (2026-09-06)
 * Validation notes:
 *   - Bug C (LU-17933) re-modeled: WR_ServerProcess now lets the server
 *     allocate one unit of extra grant for the RPC (wr_extra), which the
 *     client only applies on success; the bug variant keeps it recorded
 *     on failure, the fix variant deallocates it as tgt_grant_dealloc()
 *     does.  The previous injection ("server zeroes ted_grant on
 *     failure") does not correspond to any code path.  Both LU17933 cfgs
 *     keep their @expect (bug: QuiescentConsistency, fix: pass).
 *   - Bug A/B "analogues" referred to pre-2.10 names (ofd_grant_connect,
 *     ofd_tot_granted, ofd_grant_shrink) and to a server-initiated
 *     shrink.  In the tree shrink is client-initiated (see Source); the
 *     model's shrink_msg/shrink_ack order is a simplification, the
 *     accounting steps (client reduces first, server records on
 *     receipt) are the same.
 *   - Bug E (LU-13766) is Resolved/Fixed in JIRA with no dedicated
 *     commit; the "claims X GRANT, real grant 0" symptom was addressed
 *     by LU-9704 38c78ac2e3 (ignore grant info on resent/replayed
 *     RPCs).  The "phase = connected" guard stands in for the import
 *     state machine not sending BRW RPCs before the connection is
 *     re-established.
 *)

EXTENDS Integers, TLC

CONSTANTS
    TOTAL_GRANT,           \* Initial grant allocation (server pool)
    SHRINK_AMOUNT,         \* How much the server shrinks by
    MAX_ITER,              \* Writer loop iterations
    INITIAL_DIRTY,         \* Pre-existing dirty (0=initial connect, >0=reconnect after reboot)
    InjectBugA,            \* TRUE = server doesn't record grant on connect
    InjectBugB,            \* TRUE = server doesn't record shrink ack
    InjectBugC,            \* TRUE = server zeroes grant on write RPC failure (LU-17933)
    InjectBugD,            \* TRUE = server doesn't clamp grant on disconnect (LU-14543)
    InjectBugE             \* TRUE = write RPC allowed before connect (LU-13766)

(* --algorithm PlusCal
variables
    \* Server-side grant tracking
    srv_client_grant = 0,           \* Server's record of what client holds

    \* Client-side grant accounting (protected by loi_lock)
    cl_import_grant = INITIAL_DIRTY,  \* Client's view of total authorized grant
    cl_avail_grant = 0,             \* Available for reservation
    cl_dirty_grant = INITIAL_DIRTY, \* Consumed by dirty pages (pre-existing for reconnect)
    cl_reserved_grant = 0,          \* Reserved but not yet dirty

    \* Message channels (in-flight grant operations)
    grant_msg = 0,                  \* Grant amount: server -> client (connect)
    shrink_msg = 0,                 \* Shrink amount: server -> client
    shrink_ack = FALSE,             \* Shrink ack: client -> server

    \* Eviction tracking
    \* ev_in_progress is TRUE between server-side reclaim and client-side
    \* processing.  During this window, server and client records may
    \* legitimately disagree (server has already zeroed, client hasn't yet).
    ev_in_progress = FALSE,         \* Eviction operation in flight

    \* Connection phase
    phase = "disconnected",         \* disconnected -> connected -> evicted
    evicted = FALSE,

    \* Client-side lock (cl_loi_list_lock)
    loi_lock = "free",

    \* Write RPC in-flight tracking
    write_rpc_amt = 0;              \* Amount of dirty data in write RPC

define
    \* === Quiescent consistency (main safety property) ===

    \* System is quiescent: connected, no in-flight grant operations.
    \* All message channels empty AND no eviction or write RPC in progress.
    Quiescent ==
        phase = "connected" /\
        grant_msg = 0 /\ shrink_msg = 0 /\ ~shrink_ack /\
        ~ev_in_progress /\
        write_rpc_amt = 0

    \* When quiescent, server and client must agree on grant amount.
    \* This is the key invariant that Bug A, Bug B, and Bug C violate.
    QuiescentConsistency ==
        Quiescent => srv_client_grant = cl_import_grant

    \* === Bound invariants ===

    \* No grant variable goes negative
    NoNegativeGrant ==
        cl_import_grant >= 0 /\ cl_avail_grant >= 0 /\
        cl_dirty_grant >= 0 /\ cl_reserved_grant >= 0 /\
        srv_client_grant >= 0

    \* Client pool bounded by import grant (when connected)
    ClientPoolBounded ==
        phase = "connected" =>
            cl_avail_grant + cl_dirty_grant + cl_reserved_grant <= cl_import_grant

    \* Server's record bounded by total
    ServerGrantBounded ==
        srv_client_grant <= TOTAL_GRANT

    \* Message channels non-negative
    MsgNonNegative ==
        grant_msg >= 0 /\ shrink_msg >= 0

    \* === Write RPC safety ===

    \* Write RPCs must not fire while disconnected (LU-13766).
    \* Without this guard, a write can race with reconnect and arrive
    \* before the server has re-established per-export grant.
    \* Note: phase = "evicted" is OK (eviction can interrupt an in-flight write).
    WriteRequiresConnection ==
        write_rpc_amt > 0 => phase /= "disconnected"

end define;

\* ---------------------------------------------------------------
\* GrantConnect: server allocates initial grant to client
\*
\*   Real code path:
\*     1. Server decides grant amount in ofd_grant_connect()
\*     2. Server records in ofd->ofd_tot_granted
\*     3. Grant sent in CONNECT reply (ocd->ocd_grant)
\*     4. Client processes via osc_init_grant()
\*
\*   Bug A: step 2 is skipped - server sends grant but doesn't
\*   update its own record.
\* ---------------------------------------------------------------
fair process GrantConnect = "GC"
begin
GC_ServerAllocate:
    \* Server allocates TOTAL_GRANT to client
    if ~InjectBugA then
        \* CORRECT: record the allocation
        srv_client_grant := TOTAL_GRANT;
    end if;
    \* Bug A: srv_client_grant stays 0 (not recorded)
    \* Send grant to client via CONNECT reply
    grant_msg := TOTAL_GRANT;

GC_ClientAcquireLock:
    \* Client receives CONNECT reply, acquires lock to process
    await loi_lock = "free";
    loi_lock := "GC";

GC_ClientApply:
    \* osc_init_grant: set import and compute avail
    cl_import_grant := grant_msg;
    cl_avail_grant := grant_msg - cl_dirty_grant - cl_reserved_grant;
    grant_msg := 0;
    phase := "connected";
    loi_lock := "free";

GC_Done:
    skip;
end process;

\* ---------------------------------------------------------------
\* ShrinkOp: server initiates grant shrink, client processes, acks
\*
\*   Real code path:
\*     1. Server decides to shrink via ofd_grant_shrink()
\*     2. Server sends OBD_BRW_DECREASE_GRANT to client
\*     3. Client processes via osc_shrink_grant() under lock
\*     4. Client acks (implicit in next BRW RPC)
\*     5. Server records reduction in ofd_after_request
\*
\*   Bug B: step 5 is skipped - server doesn't update
\*   srv_client_grant after receiving the ack.
\* ---------------------------------------------------------------
fair process ShrinkOp = "SK"
begin
SK_ServerInitiate:
    \* Server decides to shrink client's grant
    \* Don't shrink if eviction in progress (export being destroyed)
    await phase = "connected" /\ ~ev_in_progress;
    shrink_msg := SHRINK_AMOUNT;

SK_ClientAcquireLock:
    \* Client receives shrink notification
    await loi_lock = "free";
    loi_lock := "SK";

SK_ClientProcess:
    \* osc_shrink_grant: reduce import and avail (under lock)
    if phase = "connected" /\ shrink_msg > 0 then
        cl_import_grant := cl_import_grant - shrink_msg;
        if cl_avail_grant >= shrink_msg then
            cl_avail_grant := cl_avail_grant - shrink_msg;
        else
            cl_avail_grant := 0;
        end if;
        shrink_ack := TRUE;
    end if;
    shrink_msg := 0;
    loi_lock := "free";

SK_ServerAck:
    \* Server processes the client's implicit ack
    \* Also unblocks if evicted (no ack coming)
    \* Guard: don't process ack if eviction in progress (export destroyed,
    \* server rejects RPCs from evicted clients)
    await shrink_ack \/ evicted;
    if shrink_ack /\ ~ev_in_progress then
        if ~InjectBugB then
            \* CORRECT: record the shrink
            srv_client_grant := srv_client_grant - SHRINK_AMOUNT;
        end if;
        \* Bug B: srv_client_grant stays at old value (not updated)
    end if;
    if shrink_ack then
        shrink_ack := FALSE;
    end if;

SK_Done:
    skip;
end process;

\* ---------------------------------------------------------------
\* Eviction: server evicts client, reclaims all grant
\*
\*   Real code path:
\*     1. Server marks client evicted (obd_export_close)
\*     2. Server reclaims grant (ofd_tot_granted -= client grant)
\*     3. Client receives IMP_EVENT_DISCON
\*     4. Client zeros grant state (osc_import_event)
\*
\*   Between steps 2 and 4, server and client legitimately disagree
\*   (server zeroed, client hasn't yet).  ev_in_progress tracks this.
\*
\*   Bug D (LU-14543): step 2 uses blind subtraction instead of
\*   safe zeroing.  If prior errors (e.g., Bug C) have corrupted
\*   srv_client_grant, the subtraction underflows.
\* ---------------------------------------------------------------
fair process Eviction = "EV"
begin
EV_Wait:
    \* Only evict after connection established
    await phase = "connected";

EV_ServerReclaim:
    \* Server reclaims all grant for this client
    \* Mark eviction in progress so QuiescentConsistency excludes
    \* the transient disagreement between server and client.
    \* Also discard any pending shrink ack (export is being destroyed,
    \* server won't process acks for a dead export).
    if InjectBugD then
        \* BUG D (LU-14543): blind subtraction of TOTAL_GRANT
        \* If srv_client_grant < TOTAL_GRANT (due to prior Bug C),
        \* this underflows, violating NoNegativeGrant.
        srv_client_grant := srv_client_grant - TOTAL_GRANT;
    else
        \* CORRECT: safe cleanup - set to 0
        srv_client_grant := 0;
    end if;
    ev_in_progress := TRUE;
    shrink_ack := FALSE;

EV_ClientAcquireLock:
    \* Client processes eviction notification
    await loi_lock = "free";
    loi_lock := "EV";

EV_ClientZero:
    \* osc_import_event(IMP_EVENT_DISCON): zero all grant state
    cl_import_grant := 0;
    cl_avail_grant := 0;
    cl_dirty_grant := 0;
    cl_reserved_grant := 0;
    \* Clear in-flight messages (connection lost)
    shrink_msg := 0;
    shrink_ack := FALSE;
    ev_in_progress := FALSE;
    phase := "evicted";
    evicted := TRUE;
    loi_lock := "free";

EV_Done:
    skip;
end process;

\* ---------------------------------------------------------------
\* Writer: background IO consuming grants (simplified)
\*   Loops MAX_ITER times: reserve from avail, consume to dirty.
\*   Creates interference for grant accounting races.
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
    if phase = "connected" /\ cl_avail_grant >= 1 then
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
    \* Guard against eviction clearing reserved between lock releases
    if cl_reserved_grant >= 1 then
        cl_reserved_grant := cl_reserved_grant - 1;
        cl_dirty_grant := cl_dirty_grant + 1;
    end if;
    loi_lock := "free";
    goto W_Start;

W_Done:
    skip;
end process;

\* ---------------------------------------------------------------
\* WriteRPC: client sends dirty pages to server via write BRW RPC
\*
\*   Real code path:
\*     1. Client has dirty pages (from Writer process)
\*     2. Client sends BRW_WRITE with dirty data
\*     3. Server receives, processes write
\*     4. Success: dirty pages written to disk, client clears dirty
\*     5. Failure: server error path, client retries
\*
\*   Bug C (LU-17933): in step 3 the server may allocate extra grant
\*     for the reply (tgt_grant_alloc, tgt_grant.c:954-955).  On
\*     failure (step 5) the reply carries no grant (o_grant = 0,
\*     tgt_grant.c:1222) but the server keeps the allocation recorded.
\*     Server overstates the client's grant; a later write triggers
\*     "claims X GRANT, real grant 0".  Fix: tgt_grant_dealloc()
\*     (tgt_grant.c:988-1006) takes the undelivered grant back.
\*
\*   Bug E (LU-13766): write RPC fires before connect establishes
\*     per-export grant.  After server reboot, client has dirty from
\*     pre-reboot session (INITIAL_DIRTY > 0) and sends writes before
\*     reconnect completes.  Server has srv_client_grant = 0.
\* ---------------------------------------------------------------
fair process WriteRPC = "WR"
variables
    wr_extra = 0;   \* grant allocated by the server for this RPC's reply
begin
WR_WaitDirty:
    \* Wait for dirty pages to write.
    \* Bug E bypasses the phase check, allowing writes before connect.
    await (InjectBugE \/ phase = "connected") /\ cl_dirty_grant > 0 /\ ~ev_in_progress;

WR_ClientAcquireLock:
    await loi_lock = "free";
    loi_lock := "WR";

WR_ClientSend:
    \* Client sends 1 unit of dirty in write RPC
    if cl_dirty_grant >= 1 then
        write_rpc_amt := 1;
    end if;
    loi_lock := "free";

WR_ServerProcess:
    \* Server receives write RPC: tgt_grant_prepare_write ->
    \* tgt_grant_alloc() may allocate more grant to the export and
    \* records it at once (tgt_grant.c:954-955); the amount travels
    \* back to the client in the reply (oa->o_grant).  Only a
    \* connected, non-failed export is granted to (tgt_grant_alloc
    \* returns 0 for exp_failed), and never beyond the pool.
    if phase = "connected" /\ ~ev_in_progress /\
       srv_client_grant < TOTAL_GRANT then
        wr_extra := 1;
        srv_client_grant := srv_client_grant + 1;
    else
        wr_extra := 0;
    end if;
    \* Nondeterministic: write succeeds or fails.
    either
        goto WR_SuccessLock;
    or
        goto WR_Failure;
    end either;

WR_SuccessLock:
    \* Write committed to disk.  Client acquires lock to clear dirty.
    await loi_lock = "free";
    loi_lock := "WR";

WR_SuccessApply:
    \* Client clears dirty pages (data written to disk) and adds the
    \* grant carried in the reply (osc_brw_fini_request ->
    \* osc_update_grant, osc_request.c:2200 / 756-762).
    \* Guard: eviction may have zeroed dirty between lock releases.
    \* In real code, client checks import state before applying results.
    if cl_dirty_grant >= write_rpc_amt then
        cl_dirty_grant := cl_dirty_grant - write_rpc_amt;
        cl_avail_grant := cl_avail_grant + write_rpc_amt + wr_extra;
        cl_import_grant := cl_import_grant + wr_extra;
    end if;
    write_rpc_amt := 0;
    wr_extra := 0;
    loi_lock := "free";
    goto WR_Done;

WR_Failure:
    \* Write failed on server.  The reply carries no grant
    \* (tgt_grant_prepare_read zeroes oa->o_grant, tgt_grant.c:1222),
    \* so the client never learns about wr_extra.
    if InjectBugC then
        \* BUG C (LU-17933): the server keeps the grant it allocated in
        \* tgt_grant_prepare_write; ted_grant now overstates what the
        \* client holds by wr_extra.
        skip;
    elsif phase = "connected" /\ ~ev_in_progress then
        \* FIXED: tgt_grant_dealloc() (tgt_grant.c:988-1006) takes the
        \* undelivered grant back, unless the export is already
        \* disconnected (1000).
        srv_client_grant := srv_client_grant - wr_extra;
    end if;
    \* Client will retry; write_rpc_amt cleared.
    write_rpc_amt := 0;
    wr_extra := 0;

WR_Done:
    skip;
end process;

end algorithm; *)
\* BEGIN TRANSLATION
VARIABLES srv_client_grant, cl_import_grant, cl_avail_grant, cl_dirty_grant,
          cl_reserved_grant, grant_msg, shrink_msg, shrink_ack,
          ev_in_progress, phase, evicted, loi_lock, write_rpc_amt, pc

(* define statement *)
Quiescent ==
    phase = "connected" /\
    grant_msg = 0 /\ shrink_msg = 0 /\ ~shrink_ack /\
    ~ev_in_progress /\
    write_rpc_amt = 0



QuiescentConsistency ==
    Quiescent => srv_client_grant = cl_import_grant




NoNegativeGrant ==
    cl_import_grant >= 0 /\ cl_avail_grant >= 0 /\
    cl_dirty_grant >= 0 /\ cl_reserved_grant >= 0 /\
    srv_client_grant >= 0


ClientPoolBounded ==
    phase = "connected" =>
        cl_avail_grant + cl_dirty_grant + cl_reserved_grant <= cl_import_grant


ServerGrantBounded ==
    srv_client_grant <= TOTAL_GRANT


MsgNonNegative ==
    grant_msg >= 0 /\ shrink_msg >= 0







WriteRequiresConnection ==
    write_rpc_amt > 0 => phase /= "disconnected"

VARIABLES w_iter, wr_extra

vars == << srv_client_grant, cl_import_grant, cl_avail_grant, cl_dirty_grant,
           cl_reserved_grant, grant_msg, shrink_msg, shrink_ack,
           ev_in_progress, phase, evicted, loi_lock, write_rpc_amt, pc,
           w_iter, wr_extra >>

ProcSet == {"GC"} \cup {"SK"} \cup {"EV"} \cup {"W"} \cup {"WR"}

Init == (* Global variables *)
        /\ srv_client_grant = 0
        /\ cl_import_grant = INITIAL_DIRTY
        /\ cl_avail_grant = 0
        /\ cl_dirty_grant = INITIAL_DIRTY
        /\ cl_reserved_grant = 0
        /\ grant_msg = 0
        /\ shrink_msg = 0
        /\ shrink_ack = FALSE
        /\ ev_in_progress = FALSE
        /\ phase = "disconnected"
        /\ evicted = FALSE
        /\ loi_lock = "free"
        /\ write_rpc_amt = 0
        (* Process Writer *)
        /\ w_iter = 0
        (* Process WriteRPC *)
        /\ wr_extra = 0
        /\ pc = [self \in ProcSet |-> CASE self = "GC" -> "GC_ServerAllocate"
                                        [] self = "SK" -> "SK_ServerInitiate"
                                        [] self = "EV" -> "EV_Wait"
                                        [] self = "W" -> "W_Start"
                                        [] self = "WR" -> "WR_WaitDirty"]

GC_ServerAllocate == /\ pc["GC"] = "GC_ServerAllocate"
                     /\ IF ~InjectBugA
                           THEN /\ srv_client_grant' = TOTAL_GRANT
                           ELSE /\ TRUE
                                /\ UNCHANGED srv_client_grant
                     /\ grant_msg' = TOTAL_GRANT
                     /\ pc' = [pc EXCEPT !["GC"] = "GC_ClientAcquireLock"]
                     /\ UNCHANGED << cl_import_grant, cl_avail_grant,
                                     cl_dirty_grant, cl_reserved_grant,
                                     shrink_msg, shrink_ack, ev_in_progress,
                                     phase, evicted, loi_lock, write_rpc_amt,
                                     w_iter, wr_extra >>

GC_ClientAcquireLock == /\ pc["GC"] = "GC_ClientAcquireLock"
                        /\ loi_lock = "free"
                        /\ loi_lock' = "GC"
                        /\ pc' = [pc EXCEPT !["GC"] = "GC_ClientApply"]
                        /\ UNCHANGED << srv_client_grant, cl_import_grant,
                                        cl_avail_grant, cl_dirty_grant,
                                        cl_reserved_grant, grant_msg,
                                        shrink_msg, shrink_ack, ev_in_progress,
                                        phase, evicted, write_rpc_amt, w_iter, wr_extra >>

GC_ClientApply == /\ pc["GC"] = "GC_ClientApply"
                  /\ cl_import_grant' = grant_msg
                  /\ cl_avail_grant' = grant_msg - cl_dirty_grant - cl_reserved_grant
                  /\ grant_msg' = 0
                  /\ phase' = "connected"
                  /\ loi_lock' = "free"
                  /\ pc' = [pc EXCEPT !["GC"] = "GC_Done"]
                  /\ UNCHANGED << srv_client_grant, cl_dirty_grant,
                                  cl_reserved_grant, shrink_msg, shrink_ack,
                                  ev_in_progress, evicted, write_rpc_amt,
                                  w_iter, wr_extra >>

GC_Done == /\ pc["GC"] = "GC_Done"
           /\ TRUE
           /\ pc' = [pc EXCEPT !["GC"] = "Done"]
           /\ UNCHANGED << srv_client_grant, cl_import_grant, cl_avail_grant,
                           cl_dirty_grant, cl_reserved_grant, grant_msg,
                           shrink_msg, shrink_ack, ev_in_progress, phase,
                           evicted, loi_lock, write_rpc_amt, w_iter, wr_extra >>

GrantConnect == GC_ServerAllocate \/ GC_ClientAcquireLock \/ GC_ClientApply
                   \/ GC_Done

SK_ServerInitiate == /\ pc["SK"] = "SK_ServerInitiate"
                     /\ phase = "connected" /\ ~ev_in_progress
                     /\ shrink_msg' = SHRINK_AMOUNT
                     /\ pc' = [pc EXCEPT !["SK"] = "SK_ClientAcquireLock"]
                     /\ UNCHANGED << srv_client_grant, cl_import_grant,
                                     cl_avail_grant, cl_dirty_grant,
                                     cl_reserved_grant, grant_msg, shrink_ack,
                                     ev_in_progress, phase, evicted, loi_lock,
                                     write_rpc_amt, w_iter, wr_extra >>

SK_ClientAcquireLock == /\ pc["SK"] = "SK_ClientAcquireLock"
                        /\ loi_lock = "free"
                        /\ loi_lock' = "SK"
                        /\ pc' = [pc EXCEPT !["SK"] = "SK_ClientProcess"]
                        /\ UNCHANGED << srv_client_grant, cl_import_grant,
                                        cl_avail_grant, cl_dirty_grant,
                                        cl_reserved_grant, grant_msg,
                                        shrink_msg, shrink_ack, ev_in_progress,
                                        phase, evicted, write_rpc_amt, w_iter, wr_extra >>

SK_ClientProcess == /\ pc["SK"] = "SK_ClientProcess"
                    /\ IF phase = "connected" /\ shrink_msg > 0
                          THEN /\ cl_import_grant' = cl_import_grant - shrink_msg
                               /\ IF cl_avail_grant >= shrink_msg
                                     THEN /\ cl_avail_grant' = cl_avail_grant - shrink_msg
                                     ELSE /\ cl_avail_grant' = 0
                               /\ shrink_ack' = TRUE
                          ELSE /\ TRUE
                               /\ UNCHANGED << cl_import_grant, cl_avail_grant,
                                               shrink_ack >>
                    /\ shrink_msg' = 0
                    /\ loi_lock' = "free"
                    /\ pc' = [pc EXCEPT !["SK"] = "SK_ServerAck"]
                    /\ UNCHANGED << srv_client_grant, cl_dirty_grant,
                                    cl_reserved_grant, grant_msg,
                                    ev_in_progress, phase, evicted,
                                    write_rpc_amt, w_iter, wr_extra >>

SK_ServerAck == /\ pc["SK"] = "SK_ServerAck"
                /\ shrink_ack \/ evicted
                /\ IF shrink_ack /\ ~ev_in_progress
                      THEN /\ IF ~InjectBugB
                                 THEN /\ srv_client_grant' = srv_client_grant - SHRINK_AMOUNT
                                 ELSE /\ TRUE
                                      /\ UNCHANGED srv_client_grant
                      ELSE /\ TRUE
                           /\ UNCHANGED srv_client_grant
                /\ IF shrink_ack
                      THEN /\ shrink_ack' = FALSE
                      ELSE /\ TRUE
                           /\ UNCHANGED shrink_ack
                /\ pc' = [pc EXCEPT !["SK"] = "SK_Done"]
                /\ UNCHANGED << cl_import_grant, cl_avail_grant,
                                cl_dirty_grant, cl_reserved_grant, grant_msg,
                                shrink_msg, ev_in_progress, phase, evicted,
                                loi_lock, write_rpc_amt, w_iter, wr_extra >>

SK_Done == /\ pc["SK"] = "SK_Done"
           /\ TRUE
           /\ pc' = [pc EXCEPT !["SK"] = "Done"]
           /\ UNCHANGED << srv_client_grant, cl_import_grant, cl_avail_grant,
                           cl_dirty_grant, cl_reserved_grant, grant_msg,
                           shrink_msg, shrink_ack, ev_in_progress, phase,
                           evicted, loi_lock, write_rpc_amt, w_iter, wr_extra >>

ShrinkOp == SK_ServerInitiate \/ SK_ClientAcquireLock \/ SK_ClientProcess
               \/ SK_ServerAck \/ SK_Done

EV_Wait == /\ pc["EV"] = "EV_Wait"
           /\ phase = "connected"
           /\ pc' = [pc EXCEPT !["EV"] = "EV_ServerReclaim"]
           /\ UNCHANGED << srv_client_grant, cl_import_grant, cl_avail_grant,
                           cl_dirty_grant, cl_reserved_grant, grant_msg,
                           shrink_msg, shrink_ack, ev_in_progress, phase,
                           evicted, loi_lock, write_rpc_amt, w_iter, wr_extra >>

EV_ServerReclaim == /\ pc["EV"] = "EV_ServerReclaim"
                    /\ IF InjectBugD
                          THEN /\ srv_client_grant' = srv_client_grant - TOTAL_GRANT
                          ELSE /\ srv_client_grant' = 0
                    /\ ev_in_progress' = TRUE
                    /\ shrink_ack' = FALSE
                    /\ pc' = [pc EXCEPT !["EV"] = "EV_ClientAcquireLock"]
                    /\ UNCHANGED << cl_import_grant, cl_avail_grant,
                                    cl_dirty_grant, cl_reserved_grant,
                                    grant_msg, shrink_msg, phase, evicted,
                                    loi_lock, write_rpc_amt, w_iter, wr_extra >>

EV_ClientAcquireLock == /\ pc["EV"] = "EV_ClientAcquireLock"
                        /\ loi_lock = "free"
                        /\ loi_lock' = "EV"
                        /\ pc' = [pc EXCEPT !["EV"] = "EV_ClientZero"]
                        /\ UNCHANGED << srv_client_grant, cl_import_grant,
                                        cl_avail_grant, cl_dirty_grant,
                                        cl_reserved_grant, grant_msg,
                                        shrink_msg, shrink_ack, ev_in_progress,
                                        phase, evicted, write_rpc_amt, w_iter, wr_extra >>

EV_ClientZero == /\ pc["EV"] = "EV_ClientZero"
                 /\ cl_import_grant' = 0
                 /\ cl_avail_grant' = 0
                 /\ cl_dirty_grant' = 0
                 /\ cl_reserved_grant' = 0
                 /\ shrink_msg' = 0
                 /\ shrink_ack' = FALSE
                 /\ ev_in_progress' = FALSE
                 /\ phase' = "evicted"
                 /\ evicted' = TRUE
                 /\ loi_lock' = "free"
                 /\ pc' = [pc EXCEPT !["EV"] = "EV_Done"]
                 /\ UNCHANGED << srv_client_grant, grant_msg, write_rpc_amt,
                                 w_iter, wr_extra >>

EV_Done == /\ pc["EV"] = "EV_Done"
           /\ TRUE
           /\ pc' = [pc EXCEPT !["EV"] = "Done"]
           /\ UNCHANGED << srv_client_grant, cl_import_grant, cl_avail_grant,
                           cl_dirty_grant, cl_reserved_grant, grant_msg,
                           shrink_msg, shrink_ack, ev_in_progress, phase,
                           evicted, loi_lock, write_rpc_amt, w_iter, wr_extra >>

Eviction == EV_Wait \/ EV_ServerReclaim \/ EV_ClientAcquireLock
               \/ EV_ClientZero \/ EV_Done

W_Start == /\ pc["W"] = "W_Start"
           /\ IF w_iter >= MAX_ITER
                 THEN /\ pc' = [pc EXCEPT !["W"] = "W_Done"]
                      /\ UNCHANGED w_iter
                 ELSE /\ w_iter' = w_iter + 1
                      /\ pc' = [pc EXCEPT !["W"] = "W_AcquireLock1"]
           /\ UNCHANGED << srv_client_grant, cl_import_grant, cl_avail_grant,
                           cl_dirty_grant, cl_reserved_grant, grant_msg,
                           shrink_msg, shrink_ack, ev_in_progress, phase,
                           evicted, loi_lock, write_rpc_amt, wr_extra >>

W_AcquireLock1 == /\ pc["W"] = "W_AcquireLock1"
                  /\ loi_lock = "free"
                  /\ loi_lock' = "W"
                  /\ pc' = [pc EXCEPT !["W"] = "W_Reserve"]
                  /\ UNCHANGED << srv_client_grant, cl_import_grant,
                                  cl_avail_grant, cl_dirty_grant,
                                  cl_reserved_grant, grant_msg, shrink_msg,
                                  shrink_ack, ev_in_progress, phase, evicted,
                                  write_rpc_amt, w_iter, wr_extra >>

W_Reserve == /\ pc["W"] = "W_Reserve"
             /\ IF phase = "connected" /\ cl_avail_grant >= 1
                   THEN /\ cl_avail_grant' = cl_avail_grant - 1
                        /\ cl_reserved_grant' = cl_reserved_grant + 1
                        /\ loi_lock' = "free"
                        /\ pc' = [pc EXCEPT !["W"] = "W_AcquireLock2"]
                   ELSE /\ loi_lock' = "free"
                        /\ pc' = [pc EXCEPT !["W"] = "W_Start"]
                        /\ UNCHANGED << cl_avail_grant, cl_reserved_grant >>
             /\ UNCHANGED << srv_client_grant, cl_import_grant, cl_dirty_grant,
                             grant_msg, shrink_msg, shrink_ack, ev_in_progress,
                             phase, evicted, write_rpc_amt, w_iter, wr_extra >>

W_AcquireLock2 == /\ pc["W"] = "W_AcquireLock2"
                  /\ loi_lock = "free"
                  /\ loi_lock' = "W"
                  /\ pc' = [pc EXCEPT !["W"] = "W_ConsumeDirty"]
                  /\ UNCHANGED << srv_client_grant, cl_import_grant,
                                  cl_avail_grant, cl_dirty_grant,
                                  cl_reserved_grant, grant_msg, shrink_msg,
                                  shrink_ack, ev_in_progress, phase, evicted,
                                  write_rpc_amt, w_iter, wr_extra >>

W_ConsumeDirty == /\ pc["W"] = "W_ConsumeDirty"
                  /\ IF cl_reserved_grant >= 1
                        THEN /\ cl_reserved_grant' = cl_reserved_grant - 1
                             /\ cl_dirty_grant' = cl_dirty_grant + 1
                        ELSE /\ TRUE
                             /\ UNCHANGED << cl_dirty_grant, cl_reserved_grant >>
                  /\ loi_lock' = "free"
                  /\ pc' = [pc EXCEPT !["W"] = "W_Start"]
                  /\ UNCHANGED << srv_client_grant, cl_import_grant,
                                  cl_avail_grant, grant_msg, shrink_msg,
                                  shrink_ack, ev_in_progress, phase, evicted,
                                  write_rpc_amt, w_iter, wr_extra >>

W_Done == /\ pc["W"] = "W_Done"
          /\ TRUE
          /\ pc' = [pc EXCEPT !["W"] = "Done"]
          /\ UNCHANGED << srv_client_grant, cl_import_grant, cl_avail_grant,
                          cl_dirty_grant, cl_reserved_grant, grant_msg,
                          shrink_msg, shrink_ack, ev_in_progress, phase,
                          evicted, loi_lock, write_rpc_amt, w_iter, wr_extra >>

Writer == W_Start \/ W_AcquireLock1 \/ W_Reserve \/ W_AcquireLock2
             \/ W_ConsumeDirty \/ W_Done

WR_WaitDirty == /\ pc["WR"] = "WR_WaitDirty"
                /\ (InjectBugE \/ phase = "connected") /\ cl_dirty_grant > 0 /\ ~ev_in_progress
                /\ pc' = [pc EXCEPT !["WR"] = "WR_ClientAcquireLock"]
                /\ UNCHANGED << srv_client_grant, cl_import_grant,
                                cl_avail_grant, cl_dirty_grant,
                                cl_reserved_grant, grant_msg, shrink_msg,
                                shrink_ack, ev_in_progress, phase, evicted,
                                loi_lock, write_rpc_amt, w_iter, wr_extra >>

WR_ClientAcquireLock == /\ pc["WR"] = "WR_ClientAcquireLock"
                        /\ loi_lock = "free"
                        /\ loi_lock' = "WR"
                        /\ pc' = [pc EXCEPT !["WR"] = "WR_ClientSend"]
                        /\ UNCHANGED << srv_client_grant, cl_import_grant,
                                        cl_avail_grant, cl_dirty_grant,
                                        cl_reserved_grant, grant_msg,
                                        shrink_msg, shrink_ack, ev_in_progress,
                                        phase, evicted, write_rpc_amt, w_iter, wr_extra >>

WR_ClientSend == /\ pc["WR"] = "WR_ClientSend"
                 /\ IF cl_dirty_grant >= 1
                       THEN /\ write_rpc_amt' = 1
                       ELSE /\ TRUE
                            /\ UNCHANGED write_rpc_amt
                 /\ loi_lock' = "free"
                 /\ pc' = [pc EXCEPT !["WR"] = "WR_ServerProcess"]
                 /\ UNCHANGED << srv_client_grant, cl_import_grant,
                                 cl_avail_grant, cl_dirty_grant,
                                 cl_reserved_grant, grant_msg, shrink_msg,
                                 shrink_ack, ev_in_progress, phase, evicted,
                                 w_iter, wr_extra >>

WR_ServerProcess == /\ pc["WR"] = "WR_ServerProcess"
                    /\ IF phase = "connected" /\ ~ev_in_progress /\
                          srv_client_grant < TOTAL_GRANT
                          THEN /\ wr_extra' = 1
                               /\ srv_client_grant' = srv_client_grant + 1
                          ELSE /\ wr_extra' = 0
                               /\ UNCHANGED srv_client_grant
                    /\ \/ /\ pc' = [pc EXCEPT !["WR"] = "WR_SuccessLock"]
                       \/ /\ pc' = [pc EXCEPT !["WR"] = "WR_Failure"]
                    /\ UNCHANGED << cl_import_grant, cl_avail_grant,
                                    cl_dirty_grant, cl_reserved_grant,
                                    grant_msg, shrink_msg, shrink_ack,
                                    ev_in_progress, phase, evicted, loi_lock,
                                    write_rpc_amt, w_iter >>

WR_SuccessLock == /\ pc["WR"] = "WR_SuccessLock"
                  /\ loi_lock = "free"
                  /\ loi_lock' = "WR"
                  /\ pc' = [pc EXCEPT !["WR"] = "WR_SuccessApply"]
                  /\ UNCHANGED << srv_client_grant, cl_import_grant,
                                  cl_avail_grant, cl_dirty_grant,
                                  cl_reserved_grant, grant_msg, shrink_msg,
                                  shrink_ack, ev_in_progress, phase, evicted,
                                  write_rpc_amt, w_iter, wr_extra >>

WR_SuccessApply == /\ pc["WR"] = "WR_SuccessApply"
                   /\ IF cl_dirty_grant >= write_rpc_amt
                         THEN /\ cl_dirty_grant' = cl_dirty_grant - write_rpc_amt
                              /\ cl_avail_grant' = cl_avail_grant + write_rpc_amt + wr_extra
                              /\ cl_import_grant' = cl_import_grant + wr_extra
                         ELSE /\ TRUE
                              /\ UNCHANGED << cl_import_grant, cl_avail_grant,
                                              cl_dirty_grant >>
                   /\ write_rpc_amt' = 0
                   /\ wr_extra' = 0
                   /\ loi_lock' = "free"
                   /\ pc' = [pc EXCEPT !["WR"] = "WR_Done"]
                   /\ UNCHANGED << srv_client_grant, cl_reserved_grant,
                                   grant_msg, shrink_msg, shrink_ack,
                                   ev_in_progress, phase, evicted, w_iter >>

WR_Failure == /\ pc["WR"] = "WR_Failure"
              /\ IF InjectBugC
                    THEN /\ TRUE
                         /\ UNCHANGED srv_client_grant
                    ELSE /\ IF phase = "connected" /\ ~ev_in_progress
                               THEN /\ srv_client_grant' = srv_client_grant - wr_extra
                               ELSE /\ TRUE
                                    /\ UNCHANGED srv_client_grant
              /\ write_rpc_amt' = 0
              /\ wr_extra' = 0
              /\ pc' = [pc EXCEPT !["WR"] = "WR_Done"]
              /\ UNCHANGED << cl_import_grant, cl_avail_grant, cl_dirty_grant,
                              cl_reserved_grant, grant_msg, shrink_msg,
                              shrink_ack, ev_in_progress, phase, evicted,
                              loi_lock, w_iter >>

WR_Done == /\ pc["WR"] = "WR_Done"
           /\ TRUE
           /\ pc' = [pc EXCEPT !["WR"] = "Done"]
           /\ UNCHANGED << srv_client_grant, cl_import_grant, cl_avail_grant,
                           cl_dirty_grant, cl_reserved_grant, grant_msg,
                           shrink_msg, shrink_ack, ev_in_progress, phase,
                           evicted, loi_lock, write_rpc_amt, w_iter, wr_extra >>

WriteRPC == WR_WaitDirty \/ WR_ClientAcquireLock \/ WR_ClientSend
               \/ WR_ServerProcess \/ WR_SuccessLock \/ WR_SuccessApply
               \/ WR_Failure \/ WR_Done

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == GrantConnect \/ ShrinkOp \/ Eviction \/ Writer \/ WriteRPC
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(GrantConnect)
        /\ WF_vars(ShrinkOp)
        /\ WF_vars(Eviction)
        /\ WF_vars(Writer)
        /\ WF_vars(WriteRPC)

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

====
