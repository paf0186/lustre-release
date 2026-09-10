--------------------------- MODULE ofd_brw_grant ---------------------------
(*
 * TLA+ specification of OFD server-side BRW and grant handling.
 *
 * Models the server (OFD/TGT) perspective of grant management for
 * Bulk Read/Write operations with multiple clients.
 *
 * Source: lustre/ofd/ofd_io.c (ofd_preprw_write, ofd_commitrw_write)
 *         lustre/target/tgt_grant.c (tgt_grant_alloc, tgt_grant_check,
 *         tgt_grant_shrink, tgt_grant_connect, tgt_grant_discard,
 *         tgt_grant_commit)
 *
 * Server-side accounting model:
 *   tgd_tot_granted = total space committed to all clients
 *                   = sum(ted_grant[c] + ted_pending[c]) for all c
 *   tgd_tot_pending = total in-flight bytes = sum(ted_pending[c])
 *   ted_grant[c]    = client c's idle grant (available for new writes)
 *   ted_pending[c]  = client c's in-flight bytes (write started, not committed)
 *
 * Grant lifecycle per BRW:
 *   1. tgt_grant_check: ted_grant -= G, ted_pending += G
 *      (tgd_tot_granted unchanged, tgd_tot_pending += G)
 *   2. tgt_grant_commit: ted_pending -= G, tgd_tot_granted -= G,
 *      tgd_tot_pending -= G  (space permanently consumed by filesystem)
 *
 * Processes:
 *   GC1, GC2    - Grant connect (one per client)
 *   BW1, BW2    - BRW write (one per client)
 *   SK          - Grant shrink
 *   RC1         - Client C1 reconnect
 *   EV1, EV2    - Client eviction (one per client)
 *   RS1         - RPC resend for C1
 *
 * Known bugs modeled:
 *   LU-8895:  Server over-grants via concurrent inflight RPCs.
 *   LU-14543: tgt_grant_discard unsigned underflow (no clamp).
 *   LU-9704:  Read resend double-accounts grant.
 *
 * Source (lustre-release master 47638add78), all under tgd_grant_lock:
 *   lustre/target/tgt_grant.c
 *     tgt_grant_space_left()   416-467    left = free - (tot_granted +
 *                                         reserved), 456 (the model's
 *                                         TOTAL_GRANT capacity check)
 *     tgt_grant_incoming()     483-565    o_dropped: tgd_tot_granted and
 *                                         ted_grant both -= dropped,
 *                                         553-554
 *     tgt_grant_shrink()       581-615    ted_grant/tgd_tot_granted -=
 *                                         o_grant 606-607 (SK_Shrink)
 *     tgt_grant_check()        698-861    replay/OBD_FL_RECOV_RESEND skip
 *                                         715-728; ted_grant -= granted,
 *                                         ted_pending += used,
 *                                         tgd_tot_granted += ungranted,
 *                                         tgd_tot_pending += used at
 *                                         828-831 (BWn_GrantCheck)
 *     tgt_grant_alloc()        884-977    curgrant guard 922; per-export
 *                                         cap want+chunk 949-951 (LU-8895
 *                                         82e494a36e, LU-11288 fcbd8c9812);
 *                                         tgd_tot_granted/ted_grant +=
 *                                         grant 954-955 (BWn_GrantAlloc,
 *                                         GCn_Allocate, RC1_ResetGrant)
 *     tgt_grant_dealloc()      988-1006   failed write: undo alloc unless
 *                                         disconnected (LU-17933)
 *     tgt_grant_connect()      1024-1091  lock 1054-1084, alloc at 1068
 *     tgt_grant_discard()      1104-1153  tgd_tot_granted -= ted_grant
 *                                         1139, recalc from exports when
 *                                         tot < ted 1116-1137 (LU-14543
 *                                         bb5d81ea95); ted_pending left
 *                                         for tgt_grant_commit 1150
 *                                         (EVn_Discard)
 *     tgt_grant_prepare_write() 1252-1336 lock 1270-1334: incoming 1312,
 *                                         check 1315, shrink 1326 or
 *                                         alloc 1329 in ONE lock hold
 *     tgt_grant_commit()       1452-1512  ted_pending -= 1491,
 *                                         tgd_tot_granted -= 1500,
 *                                         tgd_tot_pending -= 1509
 *                                         (BWn_Commit)
 *   lustre/ofd/ofd_io.c
 *     ofd_preprw_write()       701-879    tgt_grant_prepare_write 771;
 *                                         error path commit+dealloc 869-872
 *     ofd_commitrw_write()     1230-1426  commit cb 1386-1388 / commit
 *                                         1420-1421, dealloc on error 1424
 *   lustre/ofd/ofd_obd.c     ofd_obd_disconnect 422, ofd_destroy_export
 *                              510 -> tgt_grant_discard
 *   lustre/target/tgt_handler.c tgt_brw_read 2466-2469 and
 *   lustre/ofd/ofd_dev.c ofd_set_info_hdl 855-860: clear OBD_MD_FLGRANT
 *                              on MSG_RESENT|MSG_REPLAY (LU-9704 fix
 *                              38c78ac2e3)
 *
 * Validated against: lustre-release master 47638add78 (2026-09-06)
 * Validation notes:
 *   - LU-8895: the real defect was a missing per-export cap in
 *     tgt_grant_alloc() (each in-flight RPC got a fresh chunk); the
 *     lock was never dropped.  BWn_BuggyAlloc's "allocate outside the
 *     lock without a capacity check" is an abstraction of that missing
 *     cap; the fix variant (alloc under the same hold, bounded by
 *     TOTAL_GRANT) matches tgt_grant_prepare_write/tgt_grant_alloc.
 *   - LU-14543: the fix variant (discard subtracts only ted_grant,
 *     ted_pending drained by commit) is the normal path of
 *     tgt_grant_discard(); the clamp/recalculation branch 1116-1137 is
 *     not modeled because the model has no other corruption source.
 *   - LU-9704: DISCREPANCY-OPEN.  RS1_Process injects "ted_grant -= 1
 *     without updating tgd_tot_granted", but tgt_grant_incoming()
 *     always updates both counters (553-554).  The real bug was a
 *     client/server desync: a resent read/shrink RPC re-applied stale
 *     grant info after reconnect had already resynchronised the
 *     counters, and the fix ignores grant info on resent/replayed
 *     RPCs.  This server-only model has no client view, so it cannot
 *     express that; the injection is kept as a stand-in and the cfg
 *     expectations are unchanged.
 *)

EXTENDS Integers, TLC

CONSTANTS
    TOTAL_GRANT,       \* Total server grant capacity
    GRANT_CHUNK,       \* Per-client allocation unit (tgt_grant_chunk)
    MAX_BRW,           \* Maximum BRW write size (in grant units)
    InjectBug8895,     \* TRUE = concurrent over-allocation race
    InjectBug14543,    \* TRUE = discard underflow (no clamp)
    InjectBug9704      \* TRUE = double accounting on resend

Clients == {"C1", "C2"}

VARIABLES
    tgd_tot_granted,    \* total committed to all clients (ted_grant + ted_pending)
    tgd_tot_pending,    \* total in-flight (sum of ted_pending)
    ted_grant,          \* [Clients -> Int] idle grant per client
    ted_pending,        \* [Clients -> Int] in-flight per client
    client_phase,       \* [Clients -> {"disconnected","connected","evicted"}]
    grant_lock,         \* "free" or holder process id
    bw1_write_size, bw1_granted, bw1_alloc,
    bw2_write_size, bw2_granted, bw2_alloc,
    sk_target,
    pc

\* ================================================================
\* Derived operators and invariants
\* ================================================================

\* (a) Total grant committed to clients never exceeds capacity
TotalGrantBounded == tgd_tot_granted <= TOTAL_GRANT

\* (b) Pending is non-negative for all clients
PendingWithinGrant == \A c \in Clients : ted_pending[c] >= 0

\* (c) Evicted client's idle grant fully reclaimed.
\* Note: ted_pending may still be non-zero after eviction because
\* in-flight writes complete independently via tgt_grant_commit().
EvictedGrantReclaimed ==
    \A c \in Clients :
        client_phase[c] = "evicted" => ted_grant[c] = 0

\* tgd_tot_granted = sum(ted_grant + ted_pending) for all clients
GrantSumConsistency ==
    tgd_tot_granted = ted_grant["C1"] + ted_pending["C1"]
                    + ted_grant["C2"] + ted_pending["C2"]

\* tgd_tot_pending = sum(ted_pending) for all clients
PendingSumConsistency ==
    tgd_tot_pending = ted_pending["C1"] + ted_pending["C2"]

\* No negative grants (catches underflow bugs like LU-14543)
GrantsNonNegative ==
    tgd_tot_granted >= 0 /\ tgd_tot_pending >= 0 /\
    \A c \in Clients : ted_grant[c] >= 0 /\ ted_pending[c] >= 0

\* Per-client grant bounded by total
PerClientGrantBounded ==
    \A c \in Clients : ted_grant[c] + ted_pending[c] <= TOTAL_GRANT

\* Server capacity respected (same as TotalGrantBounded, kept for cfg compat)
ServerCapacityRespected == tgd_tot_granted <= TOTAL_GRANT

\* ================================================================

vars == << tgd_tot_granted, tgd_tot_pending, ted_grant, ted_pending,
           client_phase, grant_lock, pc,
           bw1_write_size, bw1_granted, bw1_alloc,
           bw2_write_size, bw2_granted, bw2_alloc, sk_target >>

ProcSet == {"GC1", "GC2", "BW1", "BW2", "SK", "RC1", "EV1", "EV2", "RS1"}

Init == /\ tgd_tot_granted = 0
        /\ tgd_tot_pending = 0
        /\ ted_grant = [c \in Clients |-> 0]
        /\ ted_pending = [c \in Clients |-> 0]
        /\ client_phase = [c \in Clients |-> "disconnected"]
        /\ grant_lock = "free"
        /\ bw1_write_size = 0 /\ bw1_granted = 0 /\ bw1_alloc = 0
        /\ bw2_write_size = 0 /\ bw2_granted = 0 /\ bw2_alloc = 0
        /\ sk_target = "C1"
        /\ pc = [self \in ProcSet |->
                    CASE self = "GC1" -> "GC1_AcquireLock"
                      [] self = "GC2" -> "GC2_AcquireLock"
                      [] self = "BW1" -> "BW1_Start"
                      [] self = "BW2" -> "BW2_Start"
                      [] self = "SK"  -> "SK_Start"
                      [] self = "RC1" -> "RC1_Wait"
                      [] self = "EV1" -> "EV1_Wait"
                      [] self = "EV2" -> "EV2_Wait"
                      [] self = "RS1" -> "RS1_Wait"]

\* Unchanged helper (all non-pc, non-lock, non-grant vars)
LOCAL other1 == << bw1_write_size, bw1_granted, bw1_alloc,
                   bw2_write_size, bw2_granted, bw2_alloc, sk_target >>

\* ================================================================
\* GrantConnect: tgt_grant_connect()
\*   Server allocates initial grant to client under tgd_grant_lock.
\*   tgd_tot_granted += chunk, ted_grant += chunk.
\* ================================================================

GC1_AcquireLock ==
    /\ pc["GC1"] = "GC1_AcquireLock"
    /\ grant_lock = "free" /\ client_phase["C1"] = "disconnected"
    /\ grant_lock' = "GC1"
    /\ pc' = [pc EXCEPT !["GC1"] = "GC1_Allocate"]
    /\ UNCHANGED << tgd_tot_granted, tgd_tot_pending, ted_grant, ted_pending,
                    client_phase, other1 >>

GC1_Allocate ==
    /\ pc["GC1"] = "GC1_Allocate"
    /\ IF tgd_tot_granted + GRANT_CHUNK <= TOTAL_GRANT
          THEN /\ ted_grant' = [ted_grant EXCEPT !["C1"] = ted_grant["C1"] + GRANT_CHUNK]
               /\ tgd_tot_granted' = tgd_tot_granted + GRANT_CHUNK
          ELSE /\ UNCHANGED << tgd_tot_granted, ted_grant >>
    /\ client_phase' = [client_phase EXCEPT !["C1"] = "connected"]
    /\ grant_lock' = "free"
    /\ pc' = [pc EXCEPT !["GC1"] = "Done"]
    /\ UNCHANGED << tgd_tot_pending, ted_pending, other1 >>

GC2_AcquireLock ==
    /\ pc["GC2"] = "GC2_AcquireLock"
    /\ grant_lock = "free" /\ client_phase["C2"] = "disconnected"
    /\ grant_lock' = "GC2"
    /\ pc' = [pc EXCEPT !["GC2"] = "GC2_Allocate"]
    /\ UNCHANGED << tgd_tot_granted, tgd_tot_pending, ted_grant, ted_pending,
                    client_phase, other1 >>

GC2_Allocate ==
    /\ pc["GC2"] = "GC2_Allocate"
    /\ IF tgd_tot_granted + GRANT_CHUNK <= TOTAL_GRANT
          THEN /\ ted_grant' = [ted_grant EXCEPT !["C2"] = ted_grant["C2"] + GRANT_CHUNK]
               /\ tgd_tot_granted' = tgd_tot_granted + GRANT_CHUNK
          ELSE /\ UNCHANGED << tgd_tot_granted, ted_grant >>
    /\ client_phase' = [client_phase EXCEPT !["C2"] = "connected"]
    /\ grant_lock' = "free"
    /\ pc' = [pc EXCEPT !["GC2"] = "Done"]
    /\ UNCHANGED << tgd_tot_pending, ted_pending, other1 >>

\* ================================================================
\* BRW_Write_C1: Server-side BRW write for client C1
\*
\*   GrantCheck: ted_grant -= G, ted_pending += G, tgd_tot_pending += G
\*               (tgd_tot_granted unchanged -- total commitment doesn't change)
\*   GrantAlloc: ted_grant += chunk, tgd_tot_granted += chunk (new commitment)
\*   Commit: ted_pending -= G, tgd_tot_pending -= G, tgd_tot_granted -= G
\*           (space permanently consumed by disk, commitment decreases)
\*
\*   LU-8895: grant alloc outside lock (concurrent RPCs each alloc)
\* ================================================================

BW1_Start ==
    /\ pc["BW1"] = "BW1_Start"
    /\ client_phase["C1"] = "connected"
    /\ \E sz \in 1..MAX_BRW : bw1_write_size' = sz
    /\ pc' = [pc EXCEPT !["BW1"] = "BW1_AcquireLock"]
    /\ UNCHANGED << tgd_tot_granted, tgd_tot_pending, ted_grant, ted_pending,
                    client_phase, grant_lock, bw1_granted, bw1_alloc,
                    bw2_write_size, bw2_granted, bw2_alloc, sk_target >>

BW1_AcquireLock ==
    /\ pc["BW1"] = "BW1_AcquireLock"
    /\ grant_lock = "free"
    /\ grant_lock' = "BW1"
    /\ pc' = [pc EXCEPT !["BW1"] = "BW1_GrantCheck"]
    /\ UNCHANGED << tgd_tot_granted, tgd_tot_pending, ted_grant, ted_pending,
                    client_phase, other1 >>

BW1_GrantCheck ==
    /\ pc["BW1"] = "BW1_GrantCheck"
    /\ IF client_phase["C1"] # "connected"
          THEN /\ grant_lock' = "free"
               /\ pc' = [pc EXCEPT !["BW1"] = "BW1_Done"]
               /\ UNCHANGED << tgd_tot_granted, tgd_tot_pending, ted_grant,
                                ted_pending, bw1_granted >>
          ELSE \* tgt_grant_check: move from ted_grant to ted_pending
               /\ LET avail == ted_grant["C1"]
                      approved == IF avail >= bw1_write_size THEN bw1_write_size
                                  ELSE IF avail > 0 THEN avail ELSE 0
                  IN /\ bw1_granted' = approved
                     /\ IF approved > 0
                           THEN /\ ted_grant' = [ted_grant EXCEPT !["C1"] = ted_grant["C1"] - approved]
                                /\ ted_pending' = [ted_pending EXCEPT !["C1"] = ted_pending["C1"] + approved]
                                /\ tgd_tot_pending' = tgd_tot_pending + approved
                           ELSE /\ UNCHANGED << ted_grant, ted_pending, tgd_tot_pending >>
                     \* tgd_tot_granted unchanged: total commitment stays same
                     /\ UNCHANGED tgd_tot_granted
               /\ pc' = [pc EXCEPT !["BW1"] = "BW1_GrantAlloc"]
               /\ UNCHANGED grant_lock
    /\ UNCHANGED << client_phase, bw1_write_size, bw1_alloc,
                    bw2_write_size, bw2_granted, bw2_alloc, sk_target >>

BW1_GrantAlloc ==
    /\ pc["BW1"] = "BW1_GrantAlloc"
    /\ IF ~InjectBug8895
          THEN \* CORRECT: alloc under same lock hold
               /\ IF tgd_tot_granted + GRANT_CHUNK <= TOTAL_GRANT
                     THEN /\ bw1_alloc' = GRANT_CHUNK
                          /\ ted_grant' = [ted_grant EXCEPT !["C1"] = ted_grant["C1"] + GRANT_CHUNK]
                          /\ tgd_tot_granted' = tgd_tot_granted + GRANT_CHUNK
                     ELSE /\ UNCHANGED << tgd_tot_granted, ted_grant, bw1_alloc >>
          ELSE \* Bug 8895: skip alloc here (will do outside lock)
               /\ UNCHANGED << tgd_tot_granted, ted_grant, bw1_alloc >>
    /\ grant_lock' = "free"
    /\ pc' = [pc EXCEPT !["BW1"] = "BW1_BuggyAlloc"]
    /\ UNCHANGED << tgd_tot_pending, ted_pending, client_phase,
                    bw1_write_size, bw1_granted,
                    bw2_write_size, bw2_granted, bw2_alloc, sk_target >>

BW1_BuggyAlloc ==
    /\ pc["BW1"] = "BW1_BuggyAlloc"
    /\ IF InjectBug8895
          THEN \* LU-8895: re-acquire lock, alloc WITHOUT checking capacity.
               \* Models: each inflight RPC sees client "needs more" and
               \* allocates independently, ignoring how much was already
               \* allocated to this client via other concurrent RPCs.
               /\ grant_lock = "free"
               /\ grant_lock' = "BW1"
               /\ bw1_alloc' = GRANT_CHUNK
               /\ ted_grant' = [ted_grant EXCEPT !["C1"] = ted_grant["C1"] + GRANT_CHUNK]
               /\ tgd_tot_granted' = tgd_tot_granted + GRANT_CHUNK
               /\ pc' = [pc EXCEPT !["BW1"] = "BW1_BuggyRelease"]
          ELSE /\ pc' = [pc EXCEPT !["BW1"] = "BW1_Commit"]
               /\ UNCHANGED << tgd_tot_granted, ted_grant, grant_lock, bw1_alloc >>
    /\ UNCHANGED << tgd_tot_pending, ted_pending, client_phase,
                    bw1_write_size, bw1_granted,
                    bw2_write_size, bw2_granted, bw2_alloc, sk_target >>

BW1_BuggyRelease ==
    /\ pc["BW1"] = "BW1_BuggyRelease"
    /\ grant_lock' = "free"
    /\ pc' = [pc EXCEPT !["BW1"] = "BW1_Commit"]
    /\ UNCHANGED << tgd_tot_granted, tgd_tot_pending, ted_grant, ted_pending,
                    client_phase, other1 >>

BW1_Commit ==
    /\ pc["BW1"] = "BW1_Commit"
    /\ IF bw1_granted > 0
          THEN \* tgt_grant_commit: space permanently consumed
               /\ grant_lock = "free"
               /\ grant_lock' = "BW1"
               /\ ted_pending' = [ted_pending EXCEPT !["C1"] = ted_pending["C1"] - bw1_granted]
               /\ tgd_tot_pending' = tgd_tot_pending - bw1_granted
               /\ tgd_tot_granted' = tgd_tot_granted - bw1_granted
               /\ pc' = [pc EXCEPT !["BW1"] = "BW1_CommitRelease"]
          ELSE /\ pc' = [pc EXCEPT !["BW1"] = "BW1_Done"]
               /\ UNCHANGED << tgd_tot_granted, tgd_tot_pending, ted_pending, grant_lock >>
    /\ UNCHANGED << ted_grant, client_phase,
                    bw1_write_size, bw1_granted, bw1_alloc,
                    bw2_write_size, bw2_granted, bw2_alloc, sk_target >>

BW1_CommitRelease ==
    /\ pc["BW1"] = "BW1_CommitRelease"
    /\ grant_lock' = "free"
    /\ pc' = [pc EXCEPT !["BW1"] = "BW1_Done"]
    /\ UNCHANGED << tgd_tot_granted, tgd_tot_pending, ted_grant, ted_pending,
                    client_phase, other1 >>

BW1_Done ==
    /\ pc["BW1"] = "BW1_Done"
    /\ bw1_write_size' = 0 /\ bw1_granted' = 0 /\ bw1_alloc' = 0
    /\ pc' = [pc EXCEPT !["BW1"] = "Done"]
    /\ UNCHANGED << tgd_tot_granted, tgd_tot_pending, ted_grant, ted_pending,
                    client_phase, grant_lock,
                    bw2_write_size, bw2_granted, bw2_alloc, sk_target >>

\* ================================================================
\* BRW_Write_C2: symmetric to C1
\* ================================================================

BW2_Start ==
    /\ pc["BW2"] = "BW2_Start"
    /\ client_phase["C2"] = "connected"
    /\ \E sz \in 1..MAX_BRW : bw2_write_size' = sz
    /\ pc' = [pc EXCEPT !["BW2"] = "BW2_AcquireLock"]
    /\ UNCHANGED << tgd_tot_granted, tgd_tot_pending, ted_grant, ted_pending,
                    client_phase, grant_lock, bw2_granted, bw2_alloc,
                    bw1_write_size, bw1_granted, bw1_alloc, sk_target >>

BW2_AcquireLock ==
    /\ pc["BW2"] = "BW2_AcquireLock"
    /\ grant_lock = "free"
    /\ grant_lock' = "BW2"
    /\ pc' = [pc EXCEPT !["BW2"] = "BW2_GrantCheck"]
    /\ UNCHANGED << tgd_tot_granted, tgd_tot_pending, ted_grant, ted_pending,
                    client_phase, other1 >>

BW2_GrantCheck ==
    /\ pc["BW2"] = "BW2_GrantCheck"
    /\ IF client_phase["C2"] # "connected"
          THEN /\ grant_lock' = "free"
               /\ pc' = [pc EXCEPT !["BW2"] = "BW2_Done"]
               /\ UNCHANGED << tgd_tot_granted, tgd_tot_pending, ted_grant,
                                ted_pending, bw2_granted >>
          ELSE /\ LET avail == ted_grant["C2"]
                      approved == IF avail >= bw2_write_size THEN bw2_write_size
                                  ELSE IF avail > 0 THEN avail ELSE 0
                  IN /\ bw2_granted' = approved
                     /\ IF approved > 0
                           THEN /\ ted_grant' = [ted_grant EXCEPT !["C2"] = ted_grant["C2"] - approved]
                                /\ ted_pending' = [ted_pending EXCEPT !["C2"] = ted_pending["C2"] + approved]
                                /\ tgd_tot_pending' = tgd_tot_pending + approved
                           ELSE /\ UNCHANGED << ted_grant, ted_pending, tgd_tot_pending >>
                     /\ UNCHANGED tgd_tot_granted
               /\ pc' = [pc EXCEPT !["BW2"] = "BW2_GrantAlloc"]
               /\ UNCHANGED grant_lock
    /\ UNCHANGED << client_phase, bw2_write_size, bw2_alloc,
                    bw1_write_size, bw1_granted, bw1_alloc, sk_target >>

BW2_GrantAlloc ==
    /\ pc["BW2"] = "BW2_GrantAlloc"
    /\ IF ~InjectBug8895
          THEN /\ IF tgd_tot_granted + GRANT_CHUNK <= TOTAL_GRANT
                     THEN /\ bw2_alloc' = GRANT_CHUNK
                          /\ ted_grant' = [ted_grant EXCEPT !["C2"] = ted_grant["C2"] + GRANT_CHUNK]
                          /\ tgd_tot_granted' = tgd_tot_granted + GRANT_CHUNK
                     ELSE /\ UNCHANGED << tgd_tot_granted, ted_grant, bw2_alloc >>
          ELSE /\ UNCHANGED << tgd_tot_granted, ted_grant, bw2_alloc >>
    /\ grant_lock' = "free"
    /\ pc' = [pc EXCEPT !["BW2"] = "BW2_BuggyAlloc"]
    /\ UNCHANGED << tgd_tot_pending, ted_pending, client_phase,
                    bw2_write_size, bw2_granted,
                    bw1_write_size, bw1_granted, bw1_alloc, sk_target >>

BW2_BuggyAlloc ==
    /\ pc["BW2"] = "BW2_BuggyAlloc"
    /\ IF InjectBug8895
          THEN \* LU-8895: alloc without capacity check
               /\ grant_lock = "free"
               /\ grant_lock' = "BW2"
               /\ bw2_alloc' = GRANT_CHUNK
               /\ ted_grant' = [ted_grant EXCEPT !["C2"] = ted_grant["C2"] + GRANT_CHUNK]
               /\ tgd_tot_granted' = tgd_tot_granted + GRANT_CHUNK
               /\ pc' = [pc EXCEPT !["BW2"] = "BW2_BuggyRelease"]
          ELSE /\ pc' = [pc EXCEPT !["BW2"] = "BW2_Commit"]
               /\ UNCHANGED << tgd_tot_granted, ted_grant, grant_lock, bw2_alloc >>
    /\ UNCHANGED << tgd_tot_pending, ted_pending, client_phase,
                    bw2_write_size, bw2_granted,
                    bw1_write_size, bw1_granted, bw1_alloc, sk_target >>

BW2_BuggyRelease ==
    /\ pc["BW2"] = "BW2_BuggyRelease"
    /\ grant_lock' = "free"
    /\ pc' = [pc EXCEPT !["BW2"] = "BW2_Commit"]
    /\ UNCHANGED << tgd_tot_granted, tgd_tot_pending, ted_grant, ted_pending,
                    client_phase, other1 >>

BW2_Commit ==
    /\ pc["BW2"] = "BW2_Commit"
    /\ IF bw2_granted > 0
          THEN /\ grant_lock = "free"
               /\ grant_lock' = "BW2"
               /\ ted_pending' = [ted_pending EXCEPT !["C2"] = ted_pending["C2"] - bw2_granted]
               /\ tgd_tot_pending' = tgd_tot_pending - bw2_granted
               /\ tgd_tot_granted' = tgd_tot_granted - bw2_granted
               /\ pc' = [pc EXCEPT !["BW2"] = "BW2_CommitRelease"]
          ELSE /\ pc' = [pc EXCEPT !["BW2"] = "BW2_Done"]
               /\ UNCHANGED << tgd_tot_granted, tgd_tot_pending, ted_pending, grant_lock >>
    /\ UNCHANGED << ted_grant, client_phase,
                    bw2_write_size, bw2_granted, bw2_alloc,
                    bw1_write_size, bw1_granted, bw1_alloc, sk_target >>

BW2_CommitRelease ==
    /\ pc["BW2"] = "BW2_CommitRelease"
    /\ grant_lock' = "free"
    /\ pc' = [pc EXCEPT !["BW2"] = "BW2_Done"]
    /\ UNCHANGED << tgd_tot_granted, tgd_tot_pending, ted_grant, ted_pending,
                    client_phase, other1 >>

BW2_Done ==
    /\ pc["BW2"] = "BW2_Done"
    /\ bw2_write_size' = 0 /\ bw2_granted' = 0 /\ bw2_alloc' = 0
    /\ pc' = [pc EXCEPT !["BW2"] = "Done"]
    /\ UNCHANGED << tgd_tot_granted, tgd_tot_pending, ted_grant, ted_pending,
                    client_phase, grant_lock,
                    bw1_write_size, bw1_granted, bw1_alloc, sk_target >>

\* ================================================================
\* GrantShrink: tgt_grant_shrink()
\*   Server reclaims idle grant. ted_grant -= 1, tgd_tot_granted -= 1.
\* ================================================================

SK_Start ==
    /\ pc["SK"] = "SK_Start"
    /\ \E c \in Clients :
         IF client_phase[c] = "connected"
            THEN /\ sk_target' = c
                 /\ pc' = [pc EXCEPT !["SK"] = "SK_AcquireLock"]
            ELSE /\ pc' = [pc EXCEPT !["SK"] = "SK_Done"]
                 /\ UNCHANGED sk_target
    /\ UNCHANGED << tgd_tot_granted, tgd_tot_pending, ted_grant, ted_pending,
                    client_phase, grant_lock,
                    bw1_write_size, bw1_granted, bw1_alloc,
                    bw2_write_size, bw2_granted, bw2_alloc >>

SK_AcquireLock ==
    /\ pc["SK"] = "SK_AcquireLock"
    /\ grant_lock = "free"
    /\ grant_lock' = "SK"
    /\ pc' = [pc EXCEPT !["SK"] = "SK_Shrink"]
    /\ UNCHANGED << tgd_tot_granted, tgd_tot_pending, ted_grant, ted_pending,
                    client_phase, other1 >>

SK_Shrink ==
    /\ pc["SK"] = "SK_Shrink"
    /\ IF client_phase[sk_target] = "connected" /\ ted_grant[sk_target] >= 1
          THEN /\ ted_grant' = [ted_grant EXCEPT ![sk_target] = ted_grant[sk_target] - 1]
               /\ tgd_tot_granted' = tgd_tot_granted - 1
          ELSE /\ UNCHANGED << tgd_tot_granted, ted_grant >>
    /\ grant_lock' = "free"
    /\ pc' = [pc EXCEPT !["SK"] = "SK_Done"]
    /\ UNCHANGED << tgd_tot_pending, ted_pending, client_phase,
                    bw1_write_size, bw1_granted, bw1_alloc,
                    bw2_write_size, bw2_granted, bw2_alloc, sk_target >>

SK_Done ==
    /\ pc["SK"] = "SK_Done"
    /\ pc' = [pc EXCEPT !["SK"] = "Done"]
    /\ UNCHANGED << tgd_tot_granted, tgd_tot_pending, ted_grant, ted_pending,
                    client_phase, grant_lock, other1 >>

\* ================================================================
\* Reconnect_C1: tgt_grant_connect() on reconnect
\*   Reset ted_grant (subtract old, alloc new).
\*   ted_pending NOT touched -- in-flight writes complete independently.
\*   tgd_tot_granted adjusted: subtract old ted_grant, add new.
\* ================================================================

RC1_Wait ==
    /\ pc["RC1"] = "RC1_Wait"
    /\ client_phase["C1"] = "connected"
    /\ pc' = [pc EXCEPT !["RC1"] = "RC1_AcquireLock"]
    /\ UNCHANGED << tgd_tot_granted, tgd_tot_pending, ted_grant, ted_pending,
                    client_phase, grant_lock, other1 >>

RC1_AcquireLock ==
    /\ pc["RC1"] = "RC1_AcquireLock"
    /\ grant_lock = "free"
    /\ grant_lock' = "RC1"
    /\ pc' = [pc EXCEPT !["RC1"] = "RC1_ResetGrant"]
    /\ UNCHANGED << tgd_tot_granted, tgd_tot_pending, ted_grant, ted_pending,
                    client_phase, other1 >>

RC1_ResetGrant ==
    /\ pc["RC1"] = "RC1_ResetGrant"
    /\ IF client_phase["C1"] = "connected"
          THEN LET old_grant == ted_grant["C1"]
                   after_sub == tgd_tot_granted - old_grant
                   can_alloc == after_sub + GRANT_CHUNK <= TOTAL_GRANT
                   new_grant == IF can_alloc THEN GRANT_CHUNK ELSE 0
               IN /\ tgd_tot_granted' = after_sub + new_grant
                  /\ ted_grant' = [ted_grant EXCEPT !["C1"] = new_grant]
          ELSE /\ UNCHANGED << tgd_tot_granted, ted_grant >>
    /\ grant_lock' = "free"
    /\ pc' = [pc EXCEPT !["RC1"] = "RC1_Done"]
    /\ UNCHANGED << tgd_tot_pending, ted_pending, client_phase,
                    bw1_write_size, bw1_granted, bw1_alloc,
                    bw2_write_size, bw2_granted, bw2_alloc, sk_target >>

RC1_Done ==
    /\ pc["RC1"] = "RC1_Done"
    /\ pc' = [pc EXCEPT !["RC1"] = "Done"]
    /\ UNCHANGED << tgd_tot_granted, tgd_tot_pending, ted_grant, ted_pending,
                    client_phase, grant_lock, other1 >>

\* ================================================================
\* Evict_C1: tgt_grant_discard()
\*   Reclaim all grant for this client.
\*   tgd_tot_granted -= (ted_grant + ted_pending).
\*   LU-14543: subtract without clamping causes underflow.
\* ================================================================

EV1_Wait ==
    /\ pc["EV1"] = "EV1_Wait"
    /\ client_phase["C1"] = "connected"
    /\ pc' = [pc EXCEPT !["EV1"] = "EV1_AcquireLock"]
    /\ UNCHANGED << tgd_tot_granted, tgd_tot_pending, ted_grant, ted_pending,
                    client_phase, grant_lock, other1 >>

EV1_AcquireLock ==
    /\ pc["EV1"] = "EV1_AcquireLock"
    /\ grant_lock = "free"
    /\ grant_lock' = "EV1"
    /\ pc' = [pc EXCEPT !["EV1"] = "EV1_Discard"]
    /\ UNCHANGED << tgd_tot_granted, tgd_tot_pending, ted_grant, ted_pending,
                    client_phase, other1 >>

EV1_Discard ==
    /\ pc["EV1"] = "EV1_Discard"
    /\ IF ~InjectBug14543
          THEN \* CORRECT: only subtract ted_grant from tgd_tot_granted.
               \* ted_pending is NOT touched -- in-flight writes complete
               \* independently via tgt_grant_commit().
               /\ tgd_tot_granted' = tgd_tot_granted - ted_grant["C1"]
               /\ UNCHANGED << tgd_tot_pending, ted_pending >>
          ELSE \* BUG LU-14543: over-eager reclaim -- subtract BOTH
               \* ted_grant AND ted_pending from tgd_tot_granted.
               \* But pending writes still complete (tgt_grant_commit),
               \* subtracting pending AGAIN. Double-subtraction causes
               \* tgd_tot_granted underflow.
               /\ tgd_tot_granted' = tgd_tot_granted - ted_grant["C1"] - ted_pending["C1"]
               /\ UNCHANGED << tgd_tot_pending, ted_pending >>
    /\ ted_grant' = [ted_grant EXCEPT !["C1"] = 0]
    /\ client_phase' = [client_phase EXCEPT !["C1"] = "evicted"]
    /\ grant_lock' = "free"
    /\ pc' = [pc EXCEPT !["EV1"] = "EV1_Done"]
    /\ UNCHANGED << bw1_write_size, bw1_granted, bw1_alloc,
                    bw2_write_size, bw2_granted, bw2_alloc, sk_target >>

EV1_Done ==
    /\ pc["EV1"] = "EV1_Done"
    /\ pc' = [pc EXCEPT !["EV1"] = "Done"]
    /\ UNCHANGED << tgd_tot_granted, tgd_tot_pending, ted_grant, ted_pending,
                    client_phase, grant_lock, other1 >>

\* ================================================================
\* Evict_C2: symmetric
\* ================================================================

EV2_Wait ==
    /\ pc["EV2"] = "EV2_Wait"
    /\ client_phase["C2"] = "connected"
    /\ pc' = [pc EXCEPT !["EV2"] = "EV2_AcquireLock"]
    /\ UNCHANGED << tgd_tot_granted, tgd_tot_pending, ted_grant, ted_pending,
                    client_phase, grant_lock, other1 >>

EV2_AcquireLock ==
    /\ pc["EV2"] = "EV2_AcquireLock"
    /\ grant_lock = "free"
    /\ grant_lock' = "EV2"
    /\ pc' = [pc EXCEPT !["EV2"] = "EV2_Discard"]
    /\ UNCHANGED << tgd_tot_granted, tgd_tot_pending, ted_grant, ted_pending,
                    client_phase, other1 >>

EV2_Discard ==
    /\ pc["EV2"] = "EV2_Discard"
    /\ IF ~InjectBug14543
          THEN /\ tgd_tot_granted' = tgd_tot_granted - ted_grant["C2"]
               /\ UNCHANGED << tgd_tot_pending, ted_pending >>
          ELSE /\ tgd_tot_granted' = tgd_tot_granted - ted_grant["C2"] - ted_pending["C2"]
               /\ UNCHANGED << tgd_tot_pending, ted_pending >>
    /\ ted_grant' = [ted_grant EXCEPT !["C2"] = 0]
    /\ client_phase' = [client_phase EXCEPT !["C2"] = "evicted"]
    /\ grant_lock' = "free"
    /\ pc' = [pc EXCEPT !["EV2"] = "EV2_Done"]
    /\ UNCHANGED << bw1_write_size, bw1_granted, bw1_alloc,
                    bw2_write_size, bw2_granted, bw2_alloc, sk_target >>

EV2_Done ==
    /\ pc["EV2"] = "EV2_Done"
    /\ pc' = [pc EXCEPT !["EV2"] = "Done"]
    /\ UNCHANGED << tgd_tot_granted, tgd_tot_pending, ted_grant, ted_pending,
                    client_phase, grant_lock, other1 >>

\* ================================================================
\* ResendRPC_C1: LU-9704 - resent RPC double-accounts grant
\* ================================================================

RS1_Wait ==
    /\ pc["RS1"] = "RS1_Wait"
    /\ client_phase["C1"] = "connected"
    /\ pc' = [pc EXCEPT !["RS1"] = "RS1_AcquireLock"]
    /\ UNCHANGED << tgd_tot_granted, tgd_tot_pending, ted_grant, ted_pending,
                    client_phase, grant_lock, other1 >>

RS1_AcquireLock ==
    /\ pc["RS1"] = "RS1_AcquireLock"
    /\ grant_lock = "free"
    /\ grant_lock' = "RS1"
    /\ pc' = [pc EXCEPT !["RS1"] = "RS1_Process"]
    /\ UNCHANGED << tgd_tot_granted, tgd_tot_pending, ted_grant, ted_pending,
                    client_phase, other1 >>

RS1_Process ==
    /\ pc["RS1"] = "RS1_Process"
    /\ IF client_phase["C1"] = "connected" /\ InjectBug9704
          THEN \* BUG LU-9704: re-process grant info on resend.
               \* Server subtracts "dropped" grant from ted_grant
               \* (double-counting the client's reported o_dropped),
               \* but does NOT update tgd_tot_granted correspondingly.
               \* This breaks the sum invariant and creates drift.
               IF ted_grant["C1"] >= 1
                  THEN /\ ted_grant' = [ted_grant EXCEPT !["C1"] = ted_grant["C1"] - 1]
                       /\ UNCHANGED tgd_tot_granted  \* BUG: forgot to update global
                  ELSE /\ UNCHANGED << tgd_tot_granted, ted_grant >>
          ELSE /\ UNCHANGED << tgd_tot_granted, ted_grant >>
    /\ grant_lock' = "free"
    /\ pc' = [pc EXCEPT !["RS1"] = "RS1_Done"]
    /\ UNCHANGED << tgd_tot_pending, ted_pending, client_phase,
                    bw1_write_size, bw1_granted, bw1_alloc,
                    bw2_write_size, bw2_granted, bw2_alloc, sk_target >>

RS1_Done ==
    /\ pc["RS1"] = "RS1_Done"
    /\ pc' = [pc EXCEPT !["RS1"] = "Done"]
    /\ UNCHANGED << tgd_tot_granted, tgd_tot_pending, ted_grant, ted_pending,
                    client_phase, grant_lock, other1 >>

\* ================================================================
\* Termination and Next
\* ================================================================

Terminating == /\ \A self \in ProcSet : pc[self] = "Done"
               /\ UNCHANGED vars

Next == \/ GC1_AcquireLock \/ GC1_Allocate
        \/ GC2_AcquireLock \/ GC2_Allocate
        \/ BW1_Start \/ BW1_AcquireLock \/ BW1_GrantCheck
        \/ BW1_GrantAlloc \/ BW1_BuggyAlloc \/ BW1_BuggyRelease
        \/ BW1_Commit \/ BW1_CommitRelease \/ BW1_Done
        \/ BW2_Start \/ BW2_AcquireLock \/ BW2_GrantCheck
        \/ BW2_GrantAlloc \/ BW2_BuggyAlloc \/ BW2_BuggyRelease
        \/ BW2_Commit \/ BW2_CommitRelease \/ BW2_Done
        \/ SK_Start \/ SK_AcquireLock \/ SK_Shrink \/ SK_Done
        \/ RC1_Wait \/ RC1_AcquireLock \/ RC1_ResetGrant \/ RC1_Done
        \/ EV1_Wait \/ EV1_AcquireLock \/ EV1_Discard \/ EV1_Done
        \/ EV2_Wait \/ EV2_AcquireLock \/ EV2_Discard \/ EV2_Done
        \/ RS1_Wait \/ RS1_AcquireLock \/ RS1_Process \/ RS1_Done
        \/ Terminating

Spec == Init /\ [][Next]_vars

============================================================================
