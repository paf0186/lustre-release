--------------------------- MODULE dne_striped_dir_ops ---------------------------
(*
 * TLA+ specification of DNE (Distributed Namespace) cross-MDT directory
 * operations: mkdir, rmdir, and link in striped directories.
 *
 * Models the distributed locking and two-phase commit protocol for
 * operations that span multiple MDTs in Lustre's DNE architecture.
 *
 * Topology:
 *   - 2 MDTs: "mdt1" (master), "mdt2" (remote)
 *   - 1 striped directory with a stripe on each MDT
 *   - 2 concurrent operations (Op1, Op2)
 *
 * Operations modeled:
 *   - CrossMdtMkdir: create a new entry on the remote MDT stripe
 *     (parent lock on master, object+entry creation on remote via 2PC)
 *   - CrossMdtRmdir: remove a striped directory
 *     (parent lock + child lock + stripe locks, 2PC to remove all stripes)
 *   - CrossMdtLink: hardlink creation requiring cross-MDT coordination
 *     (parent lock on target MDT, ref_add on source MDT via 2PC)
 *
 * Protocol per operation:
 *   1. Acquire LDLM locks (parent dir lock, optionally child/stripe locks)
 *      Lock ordering: by MDT index (lower first) to prevent deadlock
 *   2. Phase 1 (Prepare): write update log on master MDT, execute
 *      local changes, start distributed transaction
 *   3. Phase 2 (Commit): write update log on remote MDT, commit
 *      sub-transactions on all MDTs
 *   4. Release locks
 *
 * Crash model:
 *   A crash can occur between Phase 1 and Phase 2. After crash,
 *   a recovery process reads the master's update log and re-drives
 *   incomplete transactions to remote MDTs.
 *
 * Known bugs / atomicity gaps modeled:
 *   - InjectBugLockOrder: acquire locks in operation order (src-first)
 *     instead of MDT index order -> deadlock between concurrent ops
 *     (cf. LU-4725, LU-11104)
 *   - InjectBugNoRecovery: skip recovery after crash -> orphaned
 *     entries / inconsistent entry counts across MDTs
 *   - InjectBugPartialPhase1: master commits Phase 1 but does not
 *     write the update log record -> recovery cannot re-drive remote
 *     MDT, leaving inconsistent state
 *
 * Validated against: lustre-release master 47638add78 (2026-09-06)
 *
 * Source (file:line ranges in that tree):
 *   lustre/mdt/mdt_reint.c
 *   - mdt_reint_create() 1211-1261 -> mdt_create() 520-1209
 *       (parent PDO lock 709; child/stripe lock for restripe 818)
 *   - mdt_reint_unlink() 1263-1498
 *       (parent PDO lock 1304; child + stripes 1424)
 *   - mdt_reint_link()   1504-1634
 *       (target parent PDO lock 1567; source EX lock 1586)
 *   - mdt_object_stripes_lock() 317-360 -> mdt_stripes_lock() 278-300
 *       (stripes locked in stripe-index order via lod_object_lock)
 *   - mdt_rename_determine_lock_order() 2662-2747
 *       (stripe index ordering, LU-11104, 2740)
 *   lustre/mdd/mdd_dir.c
 *   - mdd_create() 3214-3627, mdd_unlink() 2176-2346, mdd_link() 1853-1965
 *   lustre/target/update_trans.c
 *   - top_trans_stop() 916-1096
 *       step 1 write update log on master 953-985 (inside the master
 *       transaction), step 2 stop master 988-1020, step 3 send updates
 *       to other MDTs 1022-1063, step 4 stop other MDTs 1066-1085
 *   - distribute_txn_cancel_records() 1279-1319, called from
 *     distribute_txn_commit_thread() 1524-1654 once all sub-transactions
 *     are committed (the model's Phase2Log/Phase2Commit log cleanup)
 *   lustre/target/update_recovery.c
 *   - distribute_txn_replay_handle() 1288-1446
 *   - update_recovery_exec() 1130-1267 (update_is_committed() 1187 skips
 *     MDTs where the update already exists: replay only what is missing)
 *
 * Validation notes (2026-09-10): the 2PC / update-log protocol and the
 * replay-only-missing-updates recovery match the code.  Abstractions to be
 * aware of: (1) the per-operation "two parent locks ordered by MDT index"
 * is a stand-in; in the code mkdir takes one PDO lock on the master stripe
 * (mdt_create), link takes target-parent PDO + source EX (mdt_reint_link),
 * and only operations that lock several stripes (rmdir via
 * mdt_object_stripes_lock, rename via mdt_rename_determine_lock_order)
 * order them by stripe index.  (2) Phase1Master and Phase1Log are never
 * separated by Crash (Crash needs phase2_remote/phase2_log), matching the
 * code where the update log record is written inside the master
 * transaction; InjectBugPartialPhase1 is therefore a hypothetical gap.
 * (3) LU-18847 (layout version on open), LU-17170 (mdt_cross_open ENOENT
 * noise, closed Not a Bug) and LU-5344 (llite inode lookup) turned out to
 * be unrelated to striped-dir mkdir/rmdir/link; the ordering rules modeled
 * come from LU-4725 and LU-11104 only.
 *
 * JIRA references: LU-4725, LU-11104 (LU-18847, LU-17170, LU-5344 kept
 * for history only; see note 3 above)
 *)

EXTENDS Integers, FiniteSets, Sequences, TLC

CONSTANTS
    \* Operation types for each concurrent operation
    Op1Type,        \* "mkdir", "rmdir", or "link"
    Op2Type,        \* "mkdir", "rmdir", or "link"

    \* Which MDT each operation targets for its remote work
    \* (the "other" MDT from where the parent stripe lives)
    Op1MasterMdt,   \* 1 or 2: MDT holding the parent/source
    Op1RemoteMdt,   \* 1 or 2: MDT for remote sub-operation
    Op2MasterMdt,
    Op2RemoteMdt,

    \* Bug injection
    InjectBugLockOrder,     \* TRUE: acquire locks op-order, not MDT-order
    InjectBugNoRecovery,    \* TRUE: skip recovery after crash
    InjectBugPartialPhase1, \* TRUE: master commits but no update log

    \* Crash injection
    EnableCrash             \* TRUE: allow crash between Phase1 and Phase2

\* MDT set
MDTs == {1, 2}
\* Operation set
Ops == {"Op1", "Op2"}

(*
 * --algorithm PlusCal
 *
 * This model is written directly in TLA+ (no PlusCal) because the
 * crash/recovery semantics require non-standard control flow that
 * is more naturally expressed in raw TLA+.
 *)

VARIABLES
    (*
     * Lock state: each MDT has a parent directory lock.
     * Values: "free", "Op1", "Op2", "recovery"
     *)
    parent_lock,    \* [mdt \in MDTs |-> lock_holder]
    stripe_lock,    \* [mdt \in MDTs |-> lock_holder]

    (*
     * Directory state: entry counts and object existence per MDT stripe.
     * entries[m] = number of directory entries on MDT m's stripe
     * objects[m] = number of objects (inodes) on MDT m
     *)
    entries,        \* [mdt \in MDTs |-> Nat]
    objects,        \* [mdt \in MDTs |-> Nat]

    (*
     * Update log: persistent record of in-flight distributed transactions.
     * update_log[m] = set of {op, type, master, remote} records
     *)
    update_log,     \* [mdt \in MDTs |-> set of records]

    (*
     * Per-operation state machine
     * Phases: "idle", "lock1", "lock2", "phase1_master", "phase1_log",
     *         "phase2_remote", "phase2_log", "phase2_commit",
     *         "unlock1", "unlock2", "done"
     *)
    op_phase,       \* [op \in Ops |-> phase string]

    (*
     * What each operation has done (for tracking partial state)
     * master_committed[op] = TRUE if master MDT changes committed
     * remote_committed[op] = TRUE if remote MDT changes committed
     *)
    master_committed,
    remote_committed,

    (*
     * Crash/recovery state
     *)
    system_crashed,     \* TRUE if a crash has occurred
    recovery_done,      \* TRUE if recovery has completed
    crash_used          \* TRUE if crash opportunity was taken or skipped

vars == << parent_lock, stripe_lock, entries, objects, update_log,
           op_phase, master_committed, remote_committed,
           system_crashed, recovery_done, crash_used >>

\* Helper: get operation config
OpType(op) == IF op = "Op1" THEN Op1Type ELSE Op2Type
MasterMdt(op) == IF op = "Op1" THEN Op1MasterMdt ELSE Op2MasterMdt
RemoteMdt(op) == IF op = "Op1" THEN Op1RemoteMdt ELSE Op2RemoteMdt

\* Helper: lock ordering - which MDT to lock first
FirstLockMdt(op) ==
    IF InjectBugLockOrder
    THEN MasterMdt(op)     \* BUG: always master first
    ELSE IF MasterMdt(op) < RemoteMdt(op)
         THEN MasterMdt(op)
         ELSE RemoteMdt(op)

SecondLockMdt(op) ==
    IF InjectBugLockOrder
    THEN RemoteMdt(op)     \* BUG: always remote second
    ELSE IF MasterMdt(op) < RemoteMdt(op)
         THEN RemoteMdt(op)
         ELSE MasterMdt(op)

\* Whether an operation needs stripe locks (rmdir needs them)
NeedsStripeLocks(op) == OpType(op) = "rmdir"

\* The "other" op
OtherOp(op) == IF op = "Op1" THEN "Op2" ELSE "Op1"

\* ================================================================
\* Initial state
\* ================================================================

Init ==
    /\ parent_lock = [m \in MDTs |-> "free"]
    /\ stripe_lock = [m \in MDTs |-> "free"]
    /\ entries = [m \in MDTs |-> 1]      \* each stripe starts with 1 entry
    /\ objects = [m \in MDTs |-> 1]      \* each stripe has 1 object
    /\ update_log = [m \in MDTs |-> {}]
    /\ op_phase = [op \in Ops |-> "idle"]
    /\ master_committed = [op \in Ops |-> FALSE]
    /\ remote_committed = [op \in Ops |-> FALSE]
    /\ system_crashed = FALSE
    /\ recovery_done = FALSE
    /\ crash_used = FALSE

\* ================================================================
\* Operation steps (parameterized by op ID)
\* ================================================================

(*
 * Step 1: Acquire first parent directory lock (lower MDT index)
 *)
AcquireLock1(op) ==
    /\ op_phase[op] = "idle"
    /\ ~system_crashed
    /\ parent_lock[FirstLockMdt(op)] = "free"
    /\ parent_lock' = [parent_lock EXCEPT ![FirstLockMdt(op)] = op]
    /\ op_phase' = [op_phase EXCEPT ![op] = "lock1"]
    /\ UNCHANGED << stripe_lock, entries, objects, update_log,
                    master_committed, remote_committed,
                    system_crashed, recovery_done, crash_used >>

(*
 * Step 2: Acquire second parent directory lock (higher MDT index)
 * For same-MDT operations (master = remote), skip this step.
 *)
AcquireLock2(op) ==
    /\ op_phase[op] = "lock1"
    /\ ~system_crashed
    /\ IF MasterMdt(op) = RemoteMdt(op)
       THEN \* Same MDT: no second lock needed
            /\ op_phase' = [op_phase EXCEPT ![op] =
                IF NeedsStripeLocks(op) THEN "stripe_lock1" ELSE "phase1_master"]
            /\ UNCHANGED parent_lock
       ELSE \* Different MDTs: acquire second parent lock
            /\ parent_lock[SecondLockMdt(op)] = "free"
            /\ parent_lock' = [parent_lock EXCEPT ![SecondLockMdt(op)] = op]
            /\ op_phase' = [op_phase EXCEPT ![op] =
                IF NeedsStripeLocks(op) THEN "stripe_lock1" ELSE "phase1_master"]
    /\ UNCHANGED << stripe_lock, entries, objects, update_log,
                    master_committed, remote_committed,
                    system_crashed, recovery_done, crash_used >>

(*
 * Step 2a: Acquire stripe lock on first MDT (rmdir only)
 *)
AcquireStripeLock1(op) ==
    /\ op_phase[op] = "stripe_lock1"
    /\ ~system_crashed
    /\ stripe_lock[FirstLockMdt(op)] = "free"
    /\ stripe_lock' = [stripe_lock EXCEPT ![FirstLockMdt(op)] = op]
    /\ op_phase' = [op_phase EXCEPT ![op] = "stripe_lock2"]
    /\ UNCHANGED << parent_lock, entries, objects, update_log,
                    master_committed, remote_committed,
                    system_crashed, recovery_done, crash_used >>

(*
 * Step 2b: Acquire stripe lock on second MDT (rmdir only)
 *)
AcquireStripeLock2(op) ==
    /\ op_phase[op] = "stripe_lock2"
    /\ ~system_crashed
    /\ IF MasterMdt(op) = RemoteMdt(op)
       THEN /\ op_phase' = [op_phase EXCEPT ![op] = "phase1_master"]
            /\ UNCHANGED stripe_lock
       ELSE /\ stripe_lock[SecondLockMdt(op)] = "free"
            /\ stripe_lock' = [stripe_lock EXCEPT ![SecondLockMdt(op)] = op]
            /\ op_phase' = [op_phase EXCEPT ![op] = "phase1_master"]
    /\ UNCHANGED << parent_lock, entries, objects, update_log,
                    master_committed, remote_committed,
                    system_crashed, recovery_done, crash_used >>

(*
 * Step 3: Phase 1 - Execute and commit on master MDT
 *
 * For mkdir: create object on master, increment entry count
 * For rmdir: mark object for deletion on master, decrement entry count
 * For link:  increment link count (ref_add) on master
 *)
Phase1Master(op) ==
    /\ op_phase[op] = "phase1_master"
    /\ ~system_crashed
    /\ LET m == MasterMdt(op)
           t == OpType(op)
       IN
        /\ IF t = "mkdir"
           THEN entries' = [entries EXCEPT ![m] = entries[m] + 1]
                /\ objects' = [objects EXCEPT ![m] = objects[m] + 1]
           ELSE IF t = "rmdir"
           THEN entries' = [entries EXCEPT ![m] = entries[m] - 1]
                /\ objects' = [objects EXCEPT ![m] = objects[m] - 1]
           ELSE \* link: add entry in parent, ref_add on source
                entries' = [entries EXCEPT ![m] = entries[m] + 1]
                /\ UNCHANGED objects
        /\ master_committed' = [master_committed EXCEPT ![op] = TRUE]
        /\ op_phase' = [op_phase EXCEPT ![op] = "phase1_log"]
    /\ UNCHANGED << parent_lock, stripe_lock, update_log,
                    remote_committed, system_crashed,
                    recovery_done, crash_used >>

(*
 * Step 4: Phase 1 - Write update log on master MDT
 *
 * The update log is the durable intent record. Once written,
 * recovery can re-drive the remote operation after a crash.
 * With InjectBugPartialPhase1, this step is skipped.
 *)
Phase1Log(op) ==
    /\ op_phase[op] = "phase1_log"
    /\ ~system_crashed
    /\ LET m == MasterMdt(op)
           rec == [op |-> op, type |-> OpType(op),
                   master |-> MasterMdt(op), remote |-> RemoteMdt(op)]
       IN
        IF InjectBugPartialPhase1
        THEN \* BUG: skip writing the update log
             /\ UNCHANGED update_log
             /\ op_phase' = [op_phase EXCEPT ![op] = "phase2_remote"]
        ELSE \* Correct: write update log on master
             /\ update_log' = [update_log EXCEPT ![m] = update_log[m] \union {rec}]
             /\ op_phase' = [op_phase EXCEPT ![op] = "phase2_remote"]
    /\ UNCHANGED << parent_lock, stripe_lock, entries, objects,
                    master_committed, remote_committed,
                    system_crashed, recovery_done, crash_used >>

(*
 * Step 5: Phase 2 - Execute on remote MDT
 *
 * For mkdir: create entry on remote stripe, create object
 * For rmdir: remove entry on remote stripe, destroy object
 * For link:  add entry on remote stripe
 *
 * THIS is where crash can intervene (between Phase1 and Phase2).
 *)
Phase2Remote(op) ==
    /\ op_phase[op] = "phase2_remote"
    /\ ~system_crashed
    /\ LET r == RemoteMdt(op)
           t == OpType(op)
       IN
        /\ IF t = "mkdir"
           THEN entries' = [entries EXCEPT ![r] = entries[r] + 1]
                /\ objects' = [objects EXCEPT ![r] = objects[r] + 1]
           ELSE IF t = "rmdir"
           THEN entries' = [entries EXCEPT ![r] = entries[r] - 1]
                /\ objects' = [objects EXCEPT ![r] = objects[r] - 1]
           ELSE \* link
                entries' = [entries EXCEPT ![r] = entries[r] + 1]
                /\ UNCHANGED objects
        /\ remote_committed' = [remote_committed EXCEPT ![op] = TRUE]
        /\ op_phase' = [op_phase EXCEPT ![op] = "phase2_log"]
    /\ UNCHANGED << parent_lock, stripe_lock, update_log,
                    master_committed, system_crashed,
                    recovery_done, crash_used >>

(*
 * Step 6: Phase 2 - Write update log on remote MDT and clean up master log
 *)
Phase2Log(op) ==
    /\ op_phase[op] = "phase2_log"
    /\ ~system_crashed
    /\ LET m == MasterMdt(op)
           r == RemoteMdt(op)
           rec == [op |-> op, type |-> OpType(op),
                   master |-> MasterMdt(op), remote |-> RemoteMdt(op)]
       IN
        \* Write log on remote, remove from master (committed)
        /\ update_log' = [update_log EXCEPT
            ![r] = update_log[r] \union {rec},
            ![m] = update_log[m] \ {rec}]
        /\ op_phase' = [op_phase EXCEPT ![op] = "phase2_commit"]
    /\ UNCHANGED << parent_lock, stripe_lock, entries, objects,
                    master_committed, remote_committed,
                    system_crashed, recovery_done, crash_used >>

(*
 * Step 7: Phase 2 commit - clean up remote log, transition to unlock
 *)
Phase2Commit(op) ==
    /\ op_phase[op] = "phase2_commit"
    /\ ~system_crashed
    /\ LET r == RemoteMdt(op)
           rec == [op |-> op, type |-> OpType(op),
                   master |-> MasterMdt(op), remote |-> RemoteMdt(op)]
       IN
        /\ update_log' = [update_log EXCEPT
            ![r] = update_log[r] \ {rec}]
        /\ op_phase' = [op_phase EXCEPT ![op] = "unlock1"]
    /\ UNCHANGED << parent_lock, stripe_lock, entries, objects,
                    master_committed, remote_committed,
                    system_crashed, recovery_done, crash_used >>

(*
 * Step 8: Release locks (reverse order)
 *)
ReleaseLock1(op) ==
    /\ op_phase[op] = "unlock1"
    /\ ~system_crashed
    /\ IF NeedsStripeLocks(op)
       THEN \* Release stripe locks first (reverse order)
            /\ IF MasterMdt(op) /= RemoteMdt(op)
               THEN stripe_lock' = [stripe_lock EXCEPT ![SecondLockMdt(op)] = "free"]
               ELSE UNCHANGED stripe_lock
            /\ op_phase' = [op_phase EXCEPT ![op] = "unlock1b"]
            /\ UNCHANGED parent_lock
       ELSE \* No stripe locks: release second parent lock
            /\ IF MasterMdt(op) /= RemoteMdt(op)
               THEN parent_lock' = [parent_lock EXCEPT ![SecondLockMdt(op)] = "free"]
               ELSE UNCHANGED parent_lock
            /\ op_phase' = [op_phase EXCEPT ![op] = "unlock2"]
            /\ UNCHANGED stripe_lock
    /\ UNCHANGED << entries, objects, update_log,
                    master_committed, remote_committed,
                    system_crashed, recovery_done, crash_used >>

\* Release first stripe lock (rmdir only)
ReleaseLock1b(op) ==
    /\ op_phase[op] = "unlock1b"
    /\ ~system_crashed
    /\ stripe_lock' = [stripe_lock EXCEPT ![FirstLockMdt(op)] = "free"]
    /\ IF MasterMdt(op) /= RemoteMdt(op)
       THEN parent_lock' = [parent_lock EXCEPT ![SecondLockMdt(op)] = "free"]
       ELSE UNCHANGED parent_lock
    /\ op_phase' = [op_phase EXCEPT ![op] = "unlock2"]
    /\ UNCHANGED << entries, objects, update_log,
                    master_committed, remote_committed,
                    system_crashed, recovery_done, crash_used >>

ReleaseLock2(op) ==
    /\ op_phase[op] = "unlock2"
    /\ ~system_crashed
    /\ parent_lock' = [parent_lock EXCEPT ![FirstLockMdt(op)] = "free"]
    /\ op_phase' = [op_phase EXCEPT ![op] = "done"]
    /\ UNCHANGED << stripe_lock, entries, objects, update_log,
                    master_committed, remote_committed,
                    system_crashed, recovery_done, crash_used >>

\* ================================================================
\* Crash action: can occur when any operation is between Phase1 and Phase2
\* ================================================================

Crash ==
    /\ EnableCrash
    /\ ~system_crashed
    /\ ~crash_used
    /\ \E op \in Ops :
        \/ op_phase[op] = "phase2_remote"
        \/ op_phase[op] = "phase2_log"
    \* Crash: all in-flight operations are aborted.
    \* Locks are implicitly released (server restart).
    \* Only persisted state (update_log, committed data) survives.
    /\ system_crashed' = TRUE
    /\ crash_used' = TRUE
    \* Release all locks
    /\ parent_lock' = [m \in MDTs |-> "free"]
    /\ stripe_lock' = [m \in MDTs |-> "free"]
    \* entries/objects/update_log are NOT modified by crash:
    \* - ops at "phase2_remote": Phase2Remote hasn't fired yet,
    \*   so remote changes were never applied to entries/objects
    \* - ops at "phase2_log": Phase2Remote already fired,
    \*   remote changes are in entries/objects and persist (OSD committed)
    \* - ops at other phases: their changes (if any) already committed
    \*   to the master OSD and persist
    \* - update_log persists across crash (it's on stable storage)
    /\ UNCHANGED << entries, objects, update_log >>
    \* remote_committed stays as-is:
    \* - ops at "phase2_remote": remote_committed is FALSE (correct)
    \* - ops at "phase2_log": remote_committed is TRUE (correct)
    /\ UNCHANGED remote_committed
    \* All in-flight operations move to crashed state.
    \* Idle ops (not yet started) are abandoned (moved to "done").
    \* Already-done ops stay done.
    /\ op_phase' = [op \in Ops |->
        IF op_phase[op] = "done" THEN "done"
        ELSE IF op_phase[op] = "idle" THEN "done"
        ELSE "crashed"]
    /\ UNCHANGED recovery_done
    /\ UNCHANGED master_committed

\* ================================================================
\* Skip crash: if crash is enabled, we nondeterministically choose
\* not to crash. This ensures we explore both crash and no-crash paths.
\* ================================================================
SkipCrash ==
    /\ EnableCrash
    /\ ~crash_used
    \* Only skip crash when all ops are past the crash window or done
    /\ \A op \in Ops :
        op_phase[op] \notin {"phase2_remote", "phase2_log"}
    /\ \A op \in Ops :
        \/ op_phase[op] = "done"
        \/ op_phase[op] \in {"unlock1", "unlock1b", "unlock2", "phase2_commit"}
    /\ crash_used' = TRUE
    /\ UNCHANGED << parent_lock, stripe_lock, entries, objects, update_log,
                    op_phase, master_committed, remote_committed,
                    system_crashed, recovery_done >>

\* ================================================================
\* Recovery: read master update logs and re-drive remote operations
\* ================================================================

Recovery ==
    /\ system_crashed
    /\ ~recovery_done
    \* Recovery re-drives all operations in the master update log
    \* that haven't been committed on the remote MDT
    /\ LET pending == UNION {update_log[m] : m \in MDTs}
       IN
        \* For each pending record, re-execute the remote operation
        /\ IF InjectBugNoRecovery
           THEN \* BUG: skip recovery entirely
                /\ UNCHANGED << entries, objects >>
           ELSE
                /\ entries' = [m \in MDTs |->
                    entries[m]
                    + IF \E rec \in pending :
                          /\ rec.remote = m
                          /\ ~remote_committed[rec.op]
                      THEN LET rec == CHOOSE rec \in pending :
                                /\ rec.remote = m
                                /\ ~remote_committed[rec.op]
                           IN IF rec.type = "mkdir" THEN 1
                              ELSE IF rec.type = "rmdir" THEN -1
                              ELSE IF rec.type = "link" THEN 1
                              ELSE 0
                      ELSE 0]
                /\ objects' = [m \in MDTs |->
                    objects[m]
                    + IF \E rec \in pending :
                          /\ rec.remote = m
                          /\ ~remote_committed[rec.op]
                      THEN LET rec == CHOOSE rec \in pending :
                                /\ rec.remote = m
                                /\ ~remote_committed[rec.op]
                           IN IF rec.type = "mkdir" THEN 1
                              ELSE IF rec.type = "rmdir" THEN -1
                              ELSE 0
                      ELSE 0]
    \* Mark all pending ops as recovered
    /\ remote_committed' = [op \in Ops |->
        IF ~InjectBugNoRecovery
           /\ \E rec \in UNION {update_log[m] : m \in MDTs} :
               /\ rec.op = op
               /\ ~remote_committed[op]
        THEN TRUE
        ELSE remote_committed[op]]
    \* Clean up all update logs
    /\ update_log' = [m \in MDTs |-> {}]
    /\ recovery_done' = TRUE
    \* Move crashed ops to done
    /\ op_phase' = [op \in Ops |->
        IF op_phase[op] = "crashed" THEN "done"
        ELSE op_phase[op]]
    /\ UNCHANGED << parent_lock, stripe_lock,
                    master_committed, system_crashed, crash_used >>

\* ================================================================
\* Combined operation actions
\* ================================================================

OpAction(op) ==
    \/ AcquireLock1(op)
    \/ AcquireLock2(op)
    \/ AcquireStripeLock1(op)
    \/ AcquireStripeLock2(op)
    \/ Phase1Master(op)
    \/ Phase1Log(op)
    \/ Phase2Remote(op)
    \/ Phase2Log(op)
    \/ Phase2Commit(op)
    \/ ReleaseLock1(op)
    \/ ReleaseLock1b(op)
    \/ ReleaseLock2(op)

\* Allow infinite stuttering to prevent deadlock on termination
Terminating ==
    /\ \A op \in Ops : op_phase[op] = "done"
    /\ IF EnableCrash /\ system_crashed
       THEN recovery_done
       ELSE TRUE
    /\ UNCHANGED vars

Next ==
    \/ \E op \in Ops : OpAction(op)
    \/ Crash
    \/ SkipCrash
    \/ Recovery
    \/ Terminating

Spec == Init /\ [][Next]_vars
            /\ WF_vars(\E op \in Ops : OpAction(op))
            /\ WF_vars(Recovery)
            /\ WF_vars(SkipCrash)

\* ================================================================
\* Invariants
\* ================================================================

(*
 * TypeOK: basic type correctness
 *)
TypeOK ==
    /\ \A m \in MDTs : parent_lock[m] \in {"free", "Op1", "Op2", "recovery"}
    /\ \A m \in MDTs : stripe_lock[m] \in {"free", "Op1", "Op2", "recovery"}
    /\ \A m \in MDTs : entries[m] \in -1..10
    /\ \A m \in MDTs : objects[m] \in -1..10

(*
 * NoLocksHeldByDone: when an operation finishes, it must not hold any locks
 *)
NoLocksHeldByDone ==
    \A op \in Ops :
        op_phase[op] = "done" =>
            /\ \A m \in MDTs : parent_lock[m] /= op
            /\ \A m \in MDTs : stripe_lock[m] /= op

(*
 * EntryCountConsistent: when all operations complete (and recovery
 * finishes if there was a crash), the total entry count across MDTs
 * must reflect the net effect of all completed operations.
 *
 * Starting state: entries = [1, 1], total = 2
 * Each completed mkdir adds 2 (1 per MDT for cross-MDT)
 * Each completed rmdir removes 2
 * Each completed link adds 2
 *
 * For same-MDT ops: adds/removes on one MDT only, but we constrain
 * the model to cross-MDT ops where master /= remote.
 *)
EntryCountConsistent ==
    (\A op \in Ops : op_phase[op] = "done") =>
    (IF system_crashed /\ ~recovery_done
     THEN TRUE  \* Don't check during recovery
     ELSE
        LET total == entries[1] + entries[2]
            base == 2  \* initial total entries
            mkdirDelta(op) ==
                IF OpType(op) = "mkdir" /\ master_committed[op] /\ remote_committed[op]
                THEN 2 ELSE 0
            rmdirDelta(op) ==
                IF OpType(op) = "rmdir" /\ master_committed[op] /\ remote_committed[op]
                THEN -2 ELSE 0
            linkDelta(op) ==
                IF OpType(op) = "link" /\ master_committed[op] /\ remote_committed[op]
                THEN 2 ELSE 0
            expected == base
                + mkdirDelta("Op1") + rmdirDelta("Op1") + linkDelta("Op1")
                + mkdirDelta("Op2") + rmdirDelta("Op2") + linkDelta("Op2")
        IN total = expected)

(*
 * NoOrphansAfterRecovery: after crash recovery completes,
 * no operation should have its master side committed but remote
 * side uncommitted (which would leave orphaned/dangling entries).
 *)
NoOrphansAfterRecovery ==
    (system_crashed /\ recovery_done) =>
        \A op \in Ops :
            master_committed[op] => remote_committed[op]

(*
 * NoNegativeEntries: entry counts should never go negative
 * (safety invariant - indicates an impossible state)
 *)
NoNegativeEntries ==
    \A m \in MDTs : entries[m] >= 0 /\ objects[m] >= 0

(*
 * LockOrderingPreventsDeadlock: combined liveness + safety check.
 * All operations eventually complete (no deadlock).
 *)
Termination == <>(\A op \in Ops : op_phase[op] = "done")

=============================================================================
