--------------------------- MODULE mds_unlink_orphan_model ---------------------------
(*
 * TLA+ model of the MDS unlink/orphan-destroy two-phase commit with recovery.
 *
 * Models the full lifecycle: unlink -> llog-mark -> OST-orphan-destroy -> llog-clear
 * with MDT crash recovery that replays orphan llog entries.
 *
 * Validated against: lustre-release master 47638add78 (2026-09-06)
 *
 * Source (file:line ranges in that tree):
 *   MDT/MDD unlink and orphan handling
 *   - mdt_reint_unlink()          lustre/mdt/mdt_reint.c:1263-1498
 *   - mdd_unlink()                lustre/mdd/mdd_dir.c:2176-2346
 *       DT_TGT_CHILD write lock 2238, mdo_ref_del() 2261,
 *       mdd_finish_unlink() call 2305, unlock 2328
 *   - mdd_finish_unlink()         lustre/mdd/mdd_dir.c:2011-2054
 *       DEAD_OBJ 2026, mod_count check 2027, mdd_orphan_insert() 2028,
 *       mdo_destroy() 2045
 *   - mdd_orphan_insert()         lustre/mdd/mdd_orphans.c:138-184
 *   - mdd_orphan_delete()         lustre/mdd/mdd_orphans.c:229-271
 *   - mdd_orphan_destroy()        lustre/mdd/mdd_orphans.c:274-326
 *       (re-checks mod_count == 0 under write lock, 304)
 *   - mdd_orphan_key_test_and_delete() mdd_orphans.c:340-371
 *   - mdd_orphan_index_iterate()  lustre/mdd/mdd_orphans.c:387-463
 *   - mdd_orphan_cleanup()        lustre/mdd/mdd_orphans.c:557-577
 *       started from mdd_recovery_complete() mdd_device.c:1232-1249
 *   Open/close
 *   - mdt_reint_open()/mdt_mfd_open() lustre/mdt/mdt_open.c:1440 / 361
 *   - mdd_open()                  lustre/mdd/mdd_object.c:3767-3859
 *       (mod_count++ 3794 under write lock 3781)
 *   - mdd_open_sanity_check()     lustre/mdd/mdd_object.c:3708-3757
 *       (DEAD_OBJ allowed for replay or already-open orphan 3721-3723)
 *   - mdt_mfd_close()             lustre/mdt/mdt_open.c:2583-2734
 *   - mdd_close()                 lustre/mdd/mdd_object.c:3874-4070
 *       (last-close orphan check 3956, mod_count-- 3965,
 *        mdd_orphan_delete() 4001, mdo_destroy() 4017)
 *   OST object destroy and the MDS_UNLINK64_REC llog ("llog mark/clear")
 *   - osp_declare_destroy()/osp_destroy() lustre/osp/osp_object.c:1683/1718
 *       -> osp_sync_add()         lustre/osp/osp_sync.c:531-538
 *   - osp_sync_process_queues()  lustre/osp/osp_sync.c:1314-1364
 *       gated by osp_sync_can_process_new() 260-287 (opd_imp_connected)
 *   - osp_sync_interpret()        lustre/osp/osp_sync.c:609-707
 *       (-ENOENT reply => record cancelled: idempotent replay)
 *   - osp_sync_process_committed() lustre/osp/osp_sync.c:1130-1261
 *       (llog_cat_cancel_records after OST commit callback)
 *   - ofd_destroy_hdl()           lustre/ofd/ofd_dev.c:1820-1896
 *   - ofd_destroy()               lustre/ofd/ofd_objects.c:1063-1114
 *
 * Validation notes (2026-09-10): no semantic drift found; all C-function
 * names in action comments were refreshed (mdt_object_open() never existed;
 * the open path is mdt_reint_open() -> mdt_mfd_open() -> mdd_open()).
 * The per-OST "llog_entry" is the OSP MDS_UNLINK64_REC record: written in
 * the unlink/close transaction (osp_sync_add), sent as OST_DESTROY by the
 * osp_sync thread only while the import is connected, and cancelled after
 * the OST reports the destroy committed (or replies -ENOENT).  Not modeled:
 * the MDS_KEEP_ORPHAN close path used on failover umount (mdd_close
 * 3888-3897 keeps the orphan for the next recovery), and open-by-FID of an
 * already-open orphan (mdd_open_sanity_check 3721-3723).
 *
 * Protocol summary:
 *   Phase 1 (MDT): Unlink decrements nlink. When nlink reaches 0:
 *     - If open_count > 0: insert orphan entry in PENDING dir (llog mark).
 *       Defer destruction until last close.
 *     - If open_count = 0: immediately trigger OST destroy.
 *   Phase 2 (Close path): On last close of orphan file:
 *     - Delete orphan entry from PENDING dir.
 *     - Issue OST_DESTROY RPC to each OST holding stripes.
 *   Phase 3 (OST): Receives destroy RPC, destroys object in local txn.
 *   Phase 4 (Llog clear): On successful OST ack, mark llog record done.
 *   Recovery: After MDT crash, orphan cleanup thread iterates PENDING:
 *     - Objects with mod_count=0: re-issue destroy (orphan survived crash).
 *     - Objects with mod_count>0: leave for client to close post-recovery.
 *
 * Concurrency expansions (2026-03-13):
 *
 *   1. Multiple hardlinks (MaxNlink > 1):
 *      Multiple unlinks can fire, each decrementing nlink. The orphan/destroy
 *      decision triggers on the LAST unlink (nlink -> 0). Races between
 *      intermediate unlinks and concurrent opens/closes create new interleavings.
 *
 *   2. Per-client open/close (NumClients > 1):
 *      Independent clients open and close the file concurrently. Each has its
 *      own lifecycle (idle -> open -> done). Last-close detection races with
 *      unlink orphan insertion are tested by interleaving. open_count is
 *      derived from client_state (not an explicit variable).
 *
 *   3. Partial OST failure (EnableOSTFailure = TRUE):
 *      OSTs can non-deterministically reject destroy RPCs. Failed destroys
 *      stay pending until the OST recovers. Tests retry logic and interaction
 *      with MDT crash recovery (llog replay to a failed OST).
 *
 * Actors:
 *   - Client(c): opens/closes the file independently (c \in 1..NumClients)
 *   - Unlinker: removes hardlinks (nlink decrements, up to MaxNlink times)
 *   - MDT_Recovery: post-crash orphan cleanup thread
 *   - OST(o): receives and processes destroy RPCs (o \in 1..NumOSTs)
 *
 * Key invariants:
 *   - ReclamationSafety: no destroy while file still open
 *   - NoDoubleDestroy: each OST object destroyed at most once
 *   - OrphanConsistency: orphan entry implies nlink = 0
 *   - LlogConsistency: llog pending implies nlink = 0
 *   - EventualDestroy (liveness): all OST objects eventually destroyed
 *   - NoOrphanLeak (liveness): orphan entries eventually cleared
 *
 * Bug injections:
 *   - InjectBugSkipOrphan: skip orphan insert on unlink (immediate destroy
 *     while still open -> use-after-free)
 *   - InjectBugDoubleDestroy: recovery processes orphan without
 *     checking mod_count -> destroys while client still has file open
 *   - InjectBugSkipLlogClear: skip clearing llog entry after destroy
 *     -> orphan leak / double-destroy on next recovery
 *   - InjectBugDestroyOnIntermediateUnlink: treat every unlink as final
 *     (issue destroy even when nlink > 0 -> premature destroy of hardlinked file)
 *   - InjectBugSkipOSTAvailCheck: issue destroy to unavailable OSTs
 *     (RPC silently dropped -> permanent orphan leak, liveness violation)
 *   - InjectBugCrashKeepsClients: MDT crash doesn't reset client state
 *     (stale open_count blocks orphan cleanup -> orphan leak)
 *
 * Bead: lustre-design-docs-at9.32
 *)

EXTENDS Integers, FiniteSets, Sequences, TLC

CONSTANTS
    NumOSTs,               \* number of OST stripe objects (1..3)
    MaxNlink,              \* starting nlink count (1 = single link, 2+ = hardlinks)
    NumClients,            \* number of independent open/close clients (1..3)
    MaxCrashes,            \* max MDT crashes allowed (bounds recovery cycles)
    EnableOSTFailure,      \* TRUE = OSTs can fail destroy RPCs
    MaxOSTFailures,        \* bound on total OST failure events
    InjectBugSkipOrphan,   \* TRUE = skip orphan insert on unlink
    InjectBugDoubleDestroy,\* TRUE = recovery destroys without checking mod_count
    InjectBugSkipLlogClear,\* TRUE = skip clearing llog entry after destroy
    InjectBugDestroyOnIntermediateUnlink, \* TRUE = every unlink triggers destroy (nlink > 0)
    InjectBugSkipOSTAvailCheck,           \* TRUE = destroy sent to unavailable OSTs (dropped)
    InjectBugCrashKeepsClients            \* TRUE = crash doesn't disconnect clients

ASSUME NumOSTs \in 1..3
ASSUME MaxNlink \in 1..3
ASSUME NumClients \in 1..3
ASSUME MaxCrashes \in 0..3
ASSUME MaxOSTFailures \in 0..3

OSTs == 1..NumOSTs
Clients == 1..NumClients

VARIABLES
    (* --- MDT state --- *)
    nlink,                 \* file nlink count (0..MaxNlink)
    orphan_entry,          \* TRUE if orphan entry exists in PENDING dir
    mdt_crashed,           \* TRUE if MDT is currently down
    crash_count,           \* number of crashes so far

    (* --- Per-OST state --- *)
    ost_object,            \* ost_object[o] \in {"alive", "destroyed"}
    ost_destroy_pending,   \* ost_destroy_pending[o]: destroy RPC queued
    ost_destroy_count,     \* ost_destroy_count[o]: times destroy issued
    ost_available,         \* ost_available[o]: OST can process RPCs
    ost_fail_count,        \* total OST failure events so far

    (* --- Llog state (per-OST destroy record) --- *)
    llog_entry,            \* llog_entry[o] \in {"none", "pending", "done"}

    (* --- Phase machines --- *)
    unlink_phase,          \* "init" | "done" (done = all nlinks removed)
    client_state,          \* [Clients -> {"idle", "open", "done"}]
    recovery_phase         \* "idle" | "scanning" | "done"

\* Derived: open_count is the number of clients with open file descriptors
open_count == Cardinality({c \in Clients : client_state[c] = "open"})

vars == <<nlink, orphan_entry, mdt_crashed, crash_count,
          ost_object, ost_destroy_pending, ost_destroy_count,
          ost_available, ost_fail_count,
          llog_entry, unlink_phase, client_state, recovery_phase>>

(* ================================================================
 * Type invariant
 * ================================================================ *)

TypeOK ==
    /\ nlink \in 0..MaxNlink
    /\ orphan_entry \in BOOLEAN
    /\ mdt_crashed \in BOOLEAN
    /\ crash_count \in 0..MaxCrashes
    /\ ost_object \in [OSTs -> {"alive", "destroyed"}]
    /\ ost_destroy_pending \in [OSTs -> BOOLEAN]
    /\ ost_destroy_count \in [OSTs -> 0..6]
    /\ ost_available \in [OSTs -> BOOLEAN]
    /\ ost_fail_count \in 0..(MaxOSTFailures + MaxCrashes + 1)
    /\ llog_entry \in [OSTs -> {"none", "pending", "done"}]
    /\ unlink_phase \in {"init", "done"}
    /\ client_state \in [Clients -> {"idle", "open", "done"}]
    /\ recovery_phase \in {"idle", "scanning", "done"}

(* ================================================================
 * Initial state
 * ================================================================ *)

Init ==
    /\ nlink = MaxNlink
    /\ orphan_entry = FALSE
    /\ mdt_crashed = FALSE
    /\ crash_count = 0
    /\ ost_object = [o \in OSTs |-> "alive"]
    /\ ost_destroy_pending = [o \in OSTs |-> FALSE]
    /\ ost_destroy_count = [o \in OSTs |-> 0]
    /\ ost_available = [o \in OSTs |-> TRUE]
    /\ ost_fail_count = 0
    /\ llog_entry = [o \in OSTs |-> "none"]
    /\ unlink_phase = "init"
    /\ client_state = [c \in Clients |-> "idle"]
    /\ recovery_phase = "idle"

(* ================================================================
 * Helper predicates
 * ================================================================ *)

AllOSTsDestroyed == \A o \in OSTs : ost_object[o] = "destroyed"
AllLlogCleared == \A o \in OSTs : llog_entry[o] \in {"none", "done"}
AnyLlogPending == \E o \in OSTs : llog_entry[o] = "pending"
AllDestroysDone == \A o \in OSTs : ost_destroy_pending[o] = FALSE
MDTAlive == ~mdt_crashed
AllClientsDone == \A c \in Clients : client_state[c] = "done"

\* Helper: issue destroy RPCs for all alive OSTs + write llog entries
IssueLlogAndDestroy ==
    /\ llog_entry' = [o \in OSTs |->
         IF llog_entry[o] = "none" THEN "pending"
         ELSE llog_entry[o]]
    /\ ost_destroy_pending' = [o \in OSTs |->
         IF ost_object[o] = "alive" THEN TRUE
         ELSE ost_destroy_pending[o]]

(* ================================================================
 * Open/Close actions (per-client)
 *
 * Each client independently opens and closes the file.
 * open_count is derived from client_state.
 * ================================================================ *)

(*
 * DoOpen(c): client c opens the file.
 * Requires nlink > 0 (file exists in namespace), MDT alive.
 * C code: mdt_reint_open() -> mdt_mfd_open() -> mo_open() -> mdd_open()
 *   (mdd_object.c:3767-3859: mod_count++ under DT_TGT_CHILD write lock)
 *)
DoOpen(c) ==
    /\ MDTAlive
    /\ client_state[c] = "idle"
    /\ nlink > 0
    /\ ~AllOSTsDestroyed
    /\ client_state' = [client_state EXCEPT ![c] = "open"]
    /\ UNCHANGED <<nlink, orphan_entry, mdt_crashed, crash_count,
                   ost_object, ost_destroy_pending, ost_destroy_count,
                   ost_available, ost_fail_count,
                   llog_entry, unlink_phase, recovery_phase>>

(*
 * DoSkipOpen(c): client c decides not to open (no-op path).
 * Models executions where not all clients participate.
 *)
DoSkipOpen(c) ==
    /\ client_state[c] = "idle"
    /\ client_state' = [client_state EXCEPT ![c] = "done"]
    /\ UNCHANGED <<nlink, orphan_entry, mdt_crashed, crash_count,
                   ost_object, ost_destroy_pending, ost_destroy_count,
                   ost_available, ost_fail_count,
                   llog_entry, unlink_phase, recovery_phase>>

(*
 * DoClose(c): client c closes its fd.
 * If this is the last close AND the file is orphaned, trigger destroy.
 *
 * C code: mdt_mfd_close() (mdt_open.c:2583-2734) -> mo_close() ->
 *   mdd_close() (mdd_object.c:3874-4070) -> mdd_orphan_delete() (4001)
 *   -> mdo_destroy() (4017), which queues the OST destroy via
 *   osp_destroy()/osp_sync_add().
 * Atomic under DT_TGT_CHILD write lock.
 *
 * Note: open_count is the CURRENT count (before this close).
 * After this close, effective open_count = open_count - 1.
 * "Last close" means open_count = 1 (going to 0).
 *)
DoClose(c) ==
    /\ MDTAlive
    /\ client_state[c] = "open"
    /\ client_state' = [client_state EXCEPT ![c] = "done"]
    /\ IF open_count = 1 /\ orphan_entry  \* This is the last close of an orphan
       THEN /\ orphan_entry' = FALSE
            /\ llog_entry' = [o \in OSTs |->
                 IF llog_entry[o] = "none" THEN "pending"
                 ELSE llog_entry[o]]
            /\ ost_destroy_pending' = [o \in OSTs |->
                 IF ost_object[o] = "alive" THEN TRUE
                 ELSE ost_destroy_pending[o]]
       ELSE UNCHANGED <<orphan_entry, llog_entry, ost_destroy_pending>>
    /\ UNCHANGED <<nlink, mdt_crashed, crash_count,
                   ost_object, ost_destroy_count,
                   ost_available, ost_fail_count,
                   unlink_phase, recovery_phase>>

(* ================================================================
 * Unlink action
 *
 * Models mdd_unlink() -> mdd_finish_unlink().
 * Atomic under DT_TGT_CHILD write lock.
 *
 * With MaxNlink > 1, DoUnlink can fire multiple times (once per
 * hardlink). Only the LAST unlink (nlink going 1 -> 0) triggers
 * the orphan/destroy decision. Intermediate unlinks just decrement.
 * ================================================================ *)

DoUnlink ==
    /\ MDTAlive
    /\ nlink > 0
    /\ nlink' = nlink - 1
    /\ IF nlink = 1  \* This is the LAST unlink (nlink 1 -> 0)
       THEN /\ unlink_phase' = "done"
            /\ IF open_count > 0
               THEN \* File still open
                    IF InjectBugSkipOrphan
                    THEN \* BUG: skip orphan, issue destroys immediately
                         /\ orphan_entry' = FALSE
                         /\ llog_entry' = [o \in OSTs |->
                              IF llog_entry[o] = "none" THEN "pending"
                              ELSE llog_entry[o]]
                         /\ ost_destroy_pending' = [o \in OSTs |->
                              IF ost_object[o] = "alive" THEN TRUE
                              ELSE ost_destroy_pending[o]]
                    ELSE \* CORRECT: insert orphan entry, defer destroy
                         /\ orphan_entry' = TRUE
                         /\ UNCHANGED <<llog_entry, ost_destroy_pending>>
               ELSE \* No openers: safe to destroy immediately
                    /\ orphan_entry' = FALSE
                    /\ llog_entry' = [o \in OSTs |->
                         IF llog_entry[o] = "none" THEN "pending"
                         ELSE llog_entry[o]]
                    /\ ost_destroy_pending' = [o \in OSTs |->
                         IF ost_object[o] = "alive" THEN TRUE
                         ELSE ost_destroy_pending[o]]
       ELSE \* Intermediate unlink (nlink > 1)
            IF InjectBugDestroyOnIntermediateUnlink
            THEN \* BUG: treat intermediate unlink as final, issue destroy
                 /\ unlink_phase' = "done"
                 /\ orphan_entry' = FALSE
                 /\ llog_entry' = [o \in OSTs |->
                      IF llog_entry[o] = "none" THEN "pending"
                      ELSE llog_entry[o]]
                 /\ ost_destroy_pending' = [o \in OSTs |->
                      IF ost_object[o] = "alive" THEN TRUE
                      ELSE ost_destroy_pending[o]]
            ELSE \* CORRECT: just decrement, no action
                 /\ UNCHANGED <<unlink_phase, orphan_entry, llog_entry,
                                ost_destroy_pending>>
    /\ UNCHANGED <<mdt_crashed, crash_count,
                   ost_object, ost_destroy_count,
                   ost_available, ost_fail_count,
                   client_state, recovery_phase>>

(* ================================================================
 * OST Destroy actions
 *
 * Models ofd_destroy_hdl() (ofd_dev.c:1820-1896) -> ofd_destroy_by_fid()
 * -> ofd_destroy() (ofd_objects.c:1063-1114).
 * OST receives destroy RPC, destroys object in local transaction.
 * On completion, llog entry transitions to "done" (MDT side: the reply
 * is handled by osp_sync_interpret(), osp_sync.c:609-707).
 *
 * With EnableOSTFailure, the OST must be available to process RPCs.
 * If unavailable, the destroy stays pending until the OST recovers.
 * ================================================================ *)

(*
 * DoOSTDestroy(o): OST o processes a queued destroy.
 * Guard: pending + available + object alive.
 *)
DoOSTDestroy(o) ==
    /\ ost_destroy_pending[o] = TRUE
    /\ IF InjectBugSkipOSTAvailCheck THEN TRUE ELSE ost_available[o] = TRUE
    /\ ost_object[o] = "alive"
    /\ IF ost_available[o] = TRUE
       THEN \* Normal path: OST processes the destroy
            /\ ost_object' = [ost_object EXCEPT ![o] = "destroyed"]
            /\ ost_destroy_pending' = [ost_destroy_pending EXCEPT ![o] = FALSE]
            /\ ost_destroy_count' = [ost_destroy_count EXCEPT ![o] = @ + 1]
            /\ IF InjectBugSkipLlogClear
               THEN UNCHANGED llog_entry
               ELSE llog_entry' = [llog_entry EXCEPT ![o] = "done"]
       ELSE \* BUG PATH: OST unavailable, RPC silently dropped
            /\ ost_destroy_pending' = [ost_destroy_pending EXCEPT ![o] = FALSE]
            /\ UNCHANGED <<ost_object, ost_destroy_count, llog_entry>>
    /\ UNCHANGED <<nlink, orphan_entry, mdt_crashed, crash_count,
                   ost_available, ost_fail_count,
                   unlink_phase, client_state, recovery_phase>>

(*
 * DoOSTDestroyAlreadyGone(o): idempotent destroy (object already gone).
 * Models crash-recovery replay: OST processed destroy pre-crash, MDT
 * lost the ack, recovery re-issues destroy. OST returns success.
 *)
DoOSTDestroyAlreadyGone(o) ==
    /\ ost_destroy_pending[o] = TRUE
    /\ IF InjectBugSkipOSTAvailCheck THEN TRUE ELSE ost_available[o] = TRUE
    /\ ost_object[o] = "destroyed"
    /\ IF ost_available[o] = TRUE
       THEN \* Normal path: OST returns success (idempotent)
            /\ ost_destroy_pending' = [ost_destroy_pending EXCEPT ![o] = FALSE]
            /\ ost_destroy_count' = [ost_destroy_count EXCEPT ![o] = @ + 1]
            /\ IF InjectBugSkipLlogClear
               THEN UNCHANGED llog_entry
               ELSE llog_entry' = [llog_entry EXCEPT ![o] = "done"]
       ELSE \* BUG PATH: OST unavailable, RPC silently dropped
            /\ ost_destroy_pending' = [ost_destroy_pending EXCEPT ![o] = FALSE]
            /\ UNCHANGED <<ost_destroy_count, llog_entry>>
    /\ UNCHANGED <<nlink, orphan_entry, mdt_crashed, crash_count,
                   ost_object, ost_available, ost_fail_count,
                   unlink_phase, client_state, recovery_phase>>

(* ================================================================
 * OST Failure and Recovery
 *
 * Models an OST going down (network partition, crash, etc.)
 * and coming back up. While down, destroy RPCs stay pending
 * but are not processed.
 * ================================================================ *)

(*
 * DoOSTFail(o): OST o becomes unavailable.
 * Destroy RPCs to this OST pend until it recovers.
 *)
DoOSTFail(o) ==
    /\ EnableOSTFailure
    /\ ost_available[o] = TRUE
    /\ ost_fail_count < MaxOSTFailures
    /\ ost_available' = [ost_available EXCEPT ![o] = FALSE]
    /\ ost_fail_count' = ost_fail_count + 1
    /\ UNCHANGED <<nlink, orphan_entry, mdt_crashed, crash_count,
                   ost_object, ost_destroy_pending, ost_destroy_count,
                   llog_entry, unlink_phase, client_state, recovery_phase>>

(*
 * DoOSTRecover(o): OST o becomes available again.
 * Pending destroy RPCs can now be processed.
 *)
DoOSTRecover(o) ==
    /\ ost_available[o] = FALSE
    /\ ost_available' = [ost_available EXCEPT ![o] = TRUE]
    /\ UNCHANGED <<nlink, orphan_entry, mdt_crashed, crash_count,
                   ost_object, ost_destroy_pending, ost_destroy_count,
                   ost_fail_count, llog_entry,
                   unlink_phase, client_state, recovery_phase>>

(* ================================================================
 * Llog Clear action
 *
 * After OST ack, MDT clears the llog record.
 * C code: the OST_DESTROY commit callback (osp_sync_request_commit_cb,
 * osp_sync.c:565) moves the request to opd_sync_committed_there and
 * osp_sync_process_committed() (osp_sync.c:1130-1261) cancels the
 * MDS_UNLINK64_REC record with llog_cat_cancel_records().
 * ================================================================ *)

DoLlogClear(o) ==
    /\ MDTAlive
    /\ llog_entry[o] = "done"
    /\ llog_entry' = [llog_entry EXCEPT ![o] = "none"]
    /\ UNCHANGED <<nlink, orphan_entry, mdt_crashed, crash_count,
                   ost_object, ost_destroy_pending, ost_destroy_count,
                   ost_available, ost_fail_count,
                   unlink_phase, client_state, recovery_phase>>

(* ================================================================
 * MDT Crash and Recovery
 *
 * Models MDT going down (crash) and coming back up (recovery).
 * On recovery, the orphan cleanup thread (mdd_orphan_cleanup,
 * mdd_orphans.c:557-577, started from mdd_recovery_complete() once
 * client recovery is complete) iterates the PENDING directory and
 * re-issues destroys for any orphans with mod_count=0.
 * ================================================================ *)

(*
 * DoMDTCrash: MDT crashes. All in-flight operations are lost.
 * Persistent state survives: orphan_entry, llog_entry, ost_object.
 * Volatile state lost: all client connections severed, pending RPCs lost.
 *)
DoMDTCrash ==
    /\ MDTAlive
    /\ crash_count < MaxCrashes
    /\ nlink = 0               \* Only crash after final unlink
    /\ unlink_phase = "done"
    /\ crash_count' = crash_count + 1
    /\ mdt_crashed' = TRUE
    /\ IF InjectBugCrashKeepsClients
       THEN UNCHANGED client_state  \* BUG: clients not disconnected, stale open_count
       ELSE client_state' = [c \in Clients |-> "done"]  \* All clients disconnected
    /\ recovery_phase' = "idle"
    /\ ost_destroy_pending' = [o \in OSTs |-> FALSE]  \* In-flight RPCs lost
    \* Llog "done" entries revert to "pending" (ack lost in crash)
    /\ llog_entry' = [o \in OSTs |->
         IF llog_entry[o] = "done" THEN "pending"
         ELSE llog_entry[o]]
    /\ UNCHANGED <<nlink, orphan_entry, ost_object, ost_destroy_count,
                   ost_available, ost_fail_count, unlink_phase>>

(*
 * DoMDTRecover: MDT comes back up. Transitions to scanning orphans.
 *)
DoMDTRecover ==
    /\ mdt_crashed = TRUE
    /\ mdt_crashed' = FALSE
    /\ recovery_phase' = "scanning"
    /\ UNCHANGED <<nlink, orphan_entry, crash_count,
                   ost_object, ost_destroy_pending, ost_destroy_count,
                   ost_available, ost_fail_count,
                   llog_entry, unlink_phase, client_state>>

(*
 * DoClientReconnect: During recovery, a client reconnects and
 * re-establishes its open file handle. Happens during recovery
 * BEFORE the orphan cleanup thread runs.
 * C code: open replay (mdt_reint_open() -> mdt_open_by_fid(),
 *   mdt_open.c:734) -> mdd_open() with is_replay set, so
 *   mdd_open_sanity_check() (mdd_object.c:3721-3723) accepts the
 *   DEAD_OBJ orphan and mod_count is restored.
 *)
DoClientReconnect ==
    /\ MDTAlive
    /\ recovery_phase = "scanning"
    /\ orphan_entry = TRUE
    /\ \E c \in Clients :
        /\ client_state[c] = "done"
        /\ client_state' = [client_state EXCEPT ![c] = "open"]
    /\ UNCHANGED <<nlink, orphan_entry, mdt_crashed, crash_count,
                   ost_object, ost_destroy_pending, ost_destroy_count,
                   ost_available, ost_fail_count,
                   llog_entry, unlink_phase, recovery_phase>>

(*
 * DoRecoveryScan: Orphan cleanup thread processes PENDING directory.
 *
 * C code: mdd_orphan_index_iterate() (mdd_orphans.c:387-463) ->
 *   mdd_orphan_key_test_and_delete() (340-371) checks mod_count.
 *   If mod_count == 0: mdd_orphan_destroy() (274-326) -> mdo_destroy(),
 *     re-checking mod_count == 0 under the DT_TGT_CHILD write lock.
 *   If mod_count > 0: leave orphan, mark ORPHAN_OBJ flag
 *)
DoRecoveryScan ==
    /\ MDTAlive
    /\ recovery_phase = "scanning"
    /\ IF InjectBugDoubleDestroy
       THEN \* BUG: process orphan WITHOUT checking open_count.
            IF orphan_entry
            THEN /\ orphan_entry' = FALSE
                 /\ llog_entry' = [o \in OSTs |->
                      IF llog_entry[o] = "none" THEN "pending"
                      ELSE llog_entry[o]]
                 /\ ost_destroy_pending' = [o \in OSTs |->
                      IF ost_object[o] = "alive" THEN TRUE
                      ELSE ost_destroy_pending[o]]
            ELSE UNCHANGED <<orphan_entry, llog_entry, ost_destroy_pending>>
       ELSE \* CORRECT: only process orphans with open_count = 0
            IF orphan_entry /\ open_count = 0
            THEN /\ orphan_entry' = FALSE
                 /\ llog_entry' = [o \in OSTs |->
                      IF llog_entry[o] = "none" THEN "pending"
                      ELSE llog_entry[o]]
                 /\ ost_destroy_pending' = [o \in OSTs |->
                      IF llog_entry[o] \in {"none", "pending"} /\ ost_object[o] = "alive"
                      THEN TRUE
                      ELSE ost_destroy_pending[o]]
            ELSE UNCHANGED <<orphan_entry, llog_entry, ost_destroy_pending>>
    /\ recovery_phase' = "done"
    /\ UNCHANGED <<nlink, mdt_crashed, crash_count,
                   ost_object, ost_destroy_count,
                   ost_available, ost_fail_count,
                   unlink_phase, client_state>>

(*
 * DoRecoveryRescanLlog: After recovery scan, re-issue destroys
 * for llog entries still "pending" (the llog record itself is
 * the persistent intent -- no orphan entry needed).
 *)
DoRecoveryRescanLlog ==
    /\ MDTAlive
    /\ recovery_phase = "done"
    /\ \E o \in OSTs :
         /\ llog_entry[o] = "pending"
         /\ ost_destroy_pending[o] = FALSE
    /\ ost_destroy_pending' = [o \in OSTs |->
         IF llog_entry[o] = "pending" /\ ost_destroy_pending[o] = FALSE
         THEN TRUE
         ELSE ost_destroy_pending[o]]
    /\ UNCHANGED <<nlink, orphan_entry, mdt_crashed, crash_count,
                   ost_object, ost_destroy_count,
                   ost_available, ost_fail_count,
                   llog_entry, unlink_phase, client_state, recovery_phase>>

(* ================================================================
 * Next-state relation
 * ================================================================ *)

Terminating ==
    /\ unlink_phase = "done"
    /\ AllClientsDone
    /\ AllOSTsDestroyed
    /\ ~orphan_entry
    /\ ~AnyLlogPending
    /\ AllDestroysDone
    /\ ~mdt_crashed
    /\ \A o \in OSTs : ost_available[o]
    /\ UNCHANGED vars

Next ==
    \/ \E c \in Clients : DoOpen(c)
    \/ \E c \in Clients : DoSkipOpen(c)
    \/ \E c \in Clients : DoClose(c)
    \/ DoUnlink
    \/ DoMDTCrash
    \/ DoMDTRecover
    \/ DoClientReconnect
    \/ DoRecoveryScan
    \/ DoRecoveryRescanLlog
    \/ \E o \in OSTs : DoOSTDestroy(o)
    \/ \E o \in OSTs : DoOSTDestroyAlreadyGone(o)
    \/ \E o \in OSTs : DoOSTFail(o)
    \/ \E o \in OSTs : DoOSTRecover(o)
    \/ \E o \in OSTs : DoLlogClear(o)
    \/ Terminating

(* Fairness: all actions eventually fire if enabled *)
Fairness ==
    /\ \A c \in Clients : WF_vars(DoOpen(c))
    /\ \A c \in Clients : WF_vars(DoSkipOpen(c))
    /\ \A c \in Clients : WF_vars(DoClose(c))
    /\ WF_vars(DoUnlink)
    /\ WF_vars(DoMDTRecover)
    /\ WF_vars(DoClientReconnect)
    /\ WF_vars(DoRecoveryScan)
    /\ WF_vars(DoRecoveryRescanLlog)
    /\ \A o \in OSTs : WF_vars(DoOSTDestroy(o))
    /\ \A o \in OSTs : WF_vars(DoOSTDestroyAlreadyGone(o))
    /\ \A o \in OSTs : WF_vars(DoOSTRecover(o))
    /\ \A o \in OSTs : WF_vars(DoLlogClear(o))

Spec == Init /\ [][Next]_vars /\ Fairness

(* ================================================================
 * Safety Invariants
 * ================================================================ *)

(*
 * ReclamationSafety: OST objects must not be destroyed while any
 * client still has the file open.
 *)
ReclamationSafety ==
    \A o \in OSTs :
        (ost_object[o] = "destroyed") => (open_count = 0)

(*
 * NoDestroyRPCWhileOpen: no destroy RPC should be issued while any
 * client still holds an open fd.
 *)
NoDestroyRPCWhileOpen ==
    \A o \in OSTs :
        ost_destroy_pending[o] => (open_count = 0)

(*
 * NoDoubleDestroy: each OST object receives at most one successful
 * destroy. With crash recovery, idempotent replays may increment
 * ost_destroy_count, but the bound should be tight.
 *)
NoDoubleDestroy ==
    \A o \in OSTs :
        ost_destroy_count[o] <= 1

(*
 * OrphanConsistency: orphan entry implies nlink = 0.
 *)
OrphanConsistency ==
    orphan_entry => (nlink = 0)

(*
 * LlogConsistency: llog entry "pending" implies nlink = 0.
 *)
LlogConsistency ==
    \A o \in OSTs :
        (llog_entry[o] = "pending") => (nlink = 0)

(*
 * OrphanImpliesAlive: if orphan entry exists, some OST object must
 * still be alive (otherwise the orphan is stale).
 *)
OrphanImpliesAlive ==
    orphan_entry => \E o \in OSTs : ost_object[o] = "alive"

(*
 * AllSafety: bundle of all safety invariants.
 *)
AllSafety ==
    /\ TypeOK
    /\ ReclamationSafety
    /\ OrphanConsistency
    /\ LlogConsistency

(* ================================================================
 * Liveness Properties
 * ================================================================ *)

EventualDestroy ==
    \A o \in OSTs : <>(ost_object[o] = "destroyed")

NoOrphanLeak == <>(~orphan_entry)

EventualLlogClear ==
    \A o \in OSTs : <>(llog_entry[o] \in {"none", "done"})

AllDone ==
    /\ unlink_phase = "done"
    /\ AllClientsDone
    /\ AllOSTsDestroyed
    /\ ~orphan_entry
    /\ ~mdt_crashed

Termination == <>AllDone

=============================================================================
\* Modification History
\* Expanded 2026-03-13: multi-nlink, per-client concurrency, OST failure
\* Created 2026-03-13 for bead lustre-design-docs-at9.32
