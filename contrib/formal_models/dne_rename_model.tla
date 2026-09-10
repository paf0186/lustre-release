---------------------------- MODULE dne_rename_model ----------------------------
(*
 * TLA+ specification of the DNE cross-MDT rename two-phase commit protocol.
 *
 * Models the atomicity window in Lustre's Distributed Namespace (DNE) rename
 * operation when source and destination directories reside on different MDTs.
 * This is the COMMIT protocol model, complementing mdt_rename_lock.tla which
 * models the LOCK ordering.
 *
 * Protocol (as implemented by the DNE update-log distributed transaction):
 *   Phase 1: Lock src_dir and dst_dir (ordered by FID, see
 *            mdt_rename_lock.tla).  The MDT executing the rename (the one
 *            holding the target directory, "master") inserts the new name
 *            in dst_dir, writes the update-log record in the same
 *            transaction and commits.
 *   Phase 2: The remote MDT holding src_dir applies the update that
 *            removes the old name; the update-log records are cancelled
 *            once every sub-transaction is committed.
 *   Crash window: Between phase 1 complete and phase 2 complete, both the
 *            old name (src_entry) and the new name (dst_entry) exist.
 *
 * Concurrent actors:
 *   - One rename thread performing the cross-MDT two-phase commit
 *   - One lookup client reading entries from both MDTs (separate RPCs)
 *   - One crash injector (non-deterministic MDT failure between phases)
 *
 * Known bugs modeled:
 *   InjectNoRecovery: after a crash between phase 1 and phase 2 the
 *            update log is not replayed, so both names stay visible after
 *            recovery (AtMostOneVisible violated).  The correct behaviour
 *            is roll-forward: distribute_txn_replay_handle() re-executes
 *            the missing remote update (old name removed), never a
 *            rollback of the master's committed insert.
 *   The cfgs are tagged LU-5559, but LU-5559 in JIRA is an unrelated
 *   ptlrpc "req wrong generation" BL AST resend issue (closed Duplicate);
 *   no lustre-release commit references LU-5559.  The cross-reference is
 *   left as-is pending a correct ticket (see validation notes).
 *
 * Validated against: lustre-release master 47638add78 (2026-09-06)
 *
 * Source (file:line ranges in that tree):
 *   - mdt_reint_rename()          lustre/mdt/mdt_reint.c:2792-3271
 *       (remote source dir / object allowed by mdt_enable_remote_rename
 *        2894 / 2998; remote target object -> -EXDEV 3053-3062)
 *   - mdt_rename_lock()           lustre/mdt/mdt_reint.c:1645-1669 (BFL,
 *       not the directory locks; those come from mdt_lock_two_dirs()
 *       2752-2785 via mdt_parent_lock())
 *   - mdd_rename()                lustre/mdd/mdd_dir.c:3637-3971
 *       one transaction: delete old name 3761, insert new name 3785,
 *       linkEA update 3806, target-object nlink drop 3825-3838
 *   - top_trans_stop()            lustre/target/update_trans.c:916-1096
 *       (update log written on master 953-985, master commit 988-1020,
 *        remote updates sent 1022-1063)
 *   - distribute_txn_replay_handle() lustre/target/update_recovery.c:
 *       1288-1446 with update_recovery_exec() 1130-1267 (replays only the
 *       updates missing on an MDT: update_is_committed() 1187)
 *
 * Validation notes (2026-09-10): recovery direction corrected.  The old
 * C_Recover removed dst_entry ("recovery detects orphaned linkEA and
 * removes it"), which no code path does; update-log replay rolls the
 * rename forward, so C_Recover now removes src_entry.  Both invariants are
 * direction-independent and all three cfgs keep their @expect.  Remaining
 * abstractions: the model's dst_entry/src_entry are the new and old
 * directory names (there is no separate "destination linkEA" phase; the
 * child's linkEA is rewritten inside the same transaction), and
 * rename_state "aborted" after a crash really means "master committed,
 * remote pending".
 *)

EXTENDS Integers, FiniteSets, TLC

CONSTANTS
    InjectCrash,          \* Enable crash injection between phase 1 and phase 2
    InjectNoRecovery      \* Bug: update-log replay does not re-drive the
                          \* remote (old-name removal) update after a crash

(* --algorithm DNERenameCommit
variables
    \* Filesystem state
    src_entry = TRUE,        \* Old name exists in src_dir (remote MDT)
    dst_entry = FALSE,       \* New name exists in dst_dir (master MDT)

    \* Rename protocol state
    rename_state = "idle",   \* idle | locked | phase1_done | phase2_done
                             \* | committed | aborted

    \* Directory locks (EX locks held by rename, blocking lookups)
    src_dir_lock = "free",   \* "free" | "rename"
    dst_dir_lock = "free",   \* "free" | "rename"

    \* Crash/recovery state
    mdt_crashed = FALSE,     \* An MDT has crashed
    mdt_recovering = FALSE,  \* MDT in recovery (blocks new client requests)
    recovery_done = FALSE,   \* Recovery completed

    \* Lookup observation (what the concurrent client saw)
    lookup_src = "unread",   \* "present" | "absent" | "unread"
    lookup_dst = "unread";   \* "present" | "absent" | "unread"

define
    (*
     * Core safety invariant: the file must be visible under at most one
     * name at any point where a client could observe it.
     *
     * Both entries may temporarily coexist during the rename, but only
     * while protected by exclusive directory locks OR during MDT recovery
     * (when no client requests are served).
     *)
    AtMostOneVisible ==
        (src_entry /\ dst_entry) =>
            ((src_dir_lock = "rename" /\ dst_dir_lock = "rename")
             \/ mdt_recovering)

    (*
     * No file loss: after the operation completes (either committed or
     * recovered from crash), the file must still be accessible somewhere.
     *)
    NoFileLoss ==
        (/\ rename_state \in {"committed", "aborted"}
         /\ (mdt_crashed => recovery_done))
        => (src_entry \/ dst_entry)

    TypeOK ==
        /\ src_entry \in BOOLEAN
        /\ dst_entry \in BOOLEAN
        /\ rename_state \in {"idle", "locked", "phase1_done",
                              "phase2_done", "committed", "aborted"}
        /\ src_dir_lock \in {"free", "rename"}
        /\ dst_dir_lock \in {"free", "rename"}
        /\ mdt_crashed \in BOOLEAN
        /\ mdt_recovering \in BOOLEAN
        /\ recovery_done \in BOOLEAN
        /\ lookup_src \in {"present", "absent", "unread"}
        /\ lookup_dst \in {"present", "absent", "unread"}
end define;

(*
 * ================================================================
 * Rename: cross-MDT rename two-phase commit
 *
 * Phase 1: acquire dir locks, insert new name + update log on master
 *          (mdd_rename insert 3785; top_trans_stop steps 1-2)
 * Phase 2: remote MDT removes the old name (top_trans_stop steps 3-4)
 * ================================================================
 *)
fair process Rename = "rename"
begin
    R_LockSrc:
        await src_dir_lock = "free";
        src_dir_lock := "rename";
    R_LockDst:
        await dst_dir_lock = "free";
        dst_dir_lock := "rename";
        rename_state := "locked";
    R_Phase1:
        \* Phase 1: new name inserted and update log committed on master
        dst_entry := TRUE;
        rename_state := "phase1_done";
    R_Phase2:
        \* Phase 2: old name removed on the remote MDT
        if ~mdt_crashed then
            src_entry := FALSE;
            rename_state := "phase2_done";
        end if;
    R_Commit:
        \* Commit both MDT transactions
        if ~mdt_crashed then
            rename_state := "committed";
        end if;
    R_Unlock:
        \* Release directory locks
        if ~mdt_crashed then
            src_dir_lock := "free";
            dst_dir_lock := "free";
        end if;
end process;

(*
 * ================================================================
 * Lookup: concurrent client observing entries on both MDTs
 *
 * Models a client that looks up the file first on src_mdt then on
 * dst_mdt. Each lookup is a separate RPC that is blocked by the
 * rename's EX lock on the directory.
 * ================================================================
 *)
fair process Lookup = "lookup"
begin
    L_ReadSrc:
        await src_dir_lock /= "rename" /\ ~mdt_recovering;
        lookup_src := IF src_entry THEN "present" ELSE "absent";
    L_ReadDst:
        await dst_dir_lock /= "rename" /\ ~mdt_recovering;
        lookup_dst := IF dst_entry THEN "present" ELSE "absent";
end process;

(*
 * ================================================================
 * CrashInjector: non-deterministic MDT crash
 *
 * Models a crash between phase 1 and phase 2 of the rename.
 * The crash releases all locks (MDT restart) and triggers recovery.
 * Fair process: will eventually run, but crash only fires if
 * rename_state = "phase1_done" when C_MaybeCrash executes.
 * ================================================================
 *)
fair process CrashInjector = "crash"
begin
    C_MaybeCrash:
        if InjectCrash /\ rename_state = "phase1_done" /\ ~mdt_crashed then
            \* MDT crashes: release locks, enter recovery
            mdt_crashed := TRUE;
            mdt_recovering := TRUE;
            rename_state := "aborted";
            src_dir_lock := "free";
            dst_dir_lock := "free";
        end if;
    C_Recover:
        if mdt_crashed /\ ~recovery_done then
            if ~InjectNoRecovery then
                \* FIX: update-log replay (distribute_txn_replay_handle)
                \* re-drives the missing remote update: the old name is
                \* removed (roll-forward).  Validation 2026-09-10: this
                \* used to clear dst_entry (rollback), which no code does.
                src_entry := FALSE;
            end if;
            \* End recovery, allow client requests
            recovery_done := TRUE;
            mdt_recovering := FALSE;
        end if;
end process;

end algorithm; *)
\* BEGIN TRANSLATION
VARIABLES src_entry, dst_entry, rename_state, src_dir_lock, dst_dir_lock,
          mdt_crashed, mdt_recovering, recovery_done, lookup_src, lookup_dst,
          pc

(* define statement *)
AtMostOneVisible ==
    (src_entry /\ dst_entry) =>
        ((src_dir_lock = "rename" /\ dst_dir_lock = "rename")
         \/ mdt_recovering)

NoFileLoss ==
    (/\ rename_state \in {"committed", "aborted"}
     /\ (mdt_crashed => recovery_done))
    => (src_entry \/ dst_entry)

TypeOK ==
    /\ src_entry \in BOOLEAN
    /\ dst_entry \in BOOLEAN
    /\ rename_state \in {"idle", "locked", "phase1_done",
                          "phase2_done", "committed", "aborted"}
    /\ src_dir_lock \in {"free", "rename"}
    /\ dst_dir_lock \in {"free", "rename"}
    /\ mdt_crashed \in BOOLEAN
    /\ mdt_recovering \in BOOLEAN
    /\ recovery_done \in BOOLEAN
    /\ lookup_src \in {"present", "absent", "unread"}
    /\ lookup_dst \in {"present", "absent", "unread"}

vars == << src_entry, dst_entry, rename_state, src_dir_lock, dst_dir_lock,
           mdt_crashed, mdt_recovering, recovery_done, lookup_src, lookup_dst,
           pc >>

ProcSet == {"rename"} \cup {"lookup"} \cup {"crash"}

Init == /\ src_entry = TRUE
        /\ dst_entry = FALSE
        /\ rename_state = "idle"
        /\ src_dir_lock = "free"
        /\ dst_dir_lock = "free"
        /\ mdt_crashed = FALSE
        /\ mdt_recovering = FALSE
        /\ recovery_done = FALSE
        /\ lookup_src = "unread"
        /\ lookup_dst = "unread"
        /\ pc = [self \in ProcSet |->
                    CASE self = "rename" -> "R_LockSrc"
                      [] self = "lookup" -> "L_ReadSrc"
                      [] self = "crash"  -> "C_MaybeCrash"]

(* Rename process actions *)

R_LockSrc == /\ pc["rename"] = "R_LockSrc"
             /\ src_dir_lock = "free"
             /\ src_dir_lock' = "rename"
             /\ pc' = [pc EXCEPT !["rename"] = "R_LockDst"]
             /\ UNCHANGED << src_entry, dst_entry, rename_state, dst_dir_lock,
                             mdt_crashed, mdt_recovering, recovery_done,
                             lookup_src, lookup_dst >>

R_LockDst == /\ pc["rename"] = "R_LockDst"
             /\ dst_dir_lock = "free"
             /\ dst_dir_lock' = "rename"
             /\ rename_state' = "locked"
             /\ pc' = [pc EXCEPT !["rename"] = "R_Phase1"]
             /\ UNCHANGED << src_entry, dst_entry, src_dir_lock,
                             mdt_crashed, mdt_recovering, recovery_done,
                             lookup_src, lookup_dst >>

R_Phase1 == /\ pc["rename"] = "R_Phase1"
            /\ dst_entry' = TRUE
            /\ rename_state' = "phase1_done"
            /\ pc' = [pc EXCEPT !["rename"] = "R_Phase2"]
            /\ UNCHANGED << src_entry, src_dir_lock, dst_dir_lock,
                            mdt_crashed, mdt_recovering, recovery_done,
                            lookup_src, lookup_dst >>

R_Phase2 == /\ pc["rename"] = "R_Phase2"
            /\ IF ~mdt_crashed
                  THEN /\ src_entry' = FALSE
                       /\ rename_state' = "phase2_done"
                  ELSE /\ UNCHANGED << src_entry, rename_state >>
            /\ pc' = [pc EXCEPT !["rename"] = "R_Commit"]
            /\ UNCHANGED << dst_entry, src_dir_lock, dst_dir_lock,
                            mdt_crashed, mdt_recovering, recovery_done,
                            lookup_src, lookup_dst >>

R_Commit == /\ pc["rename"] = "R_Commit"
            /\ IF ~mdt_crashed
                  THEN /\ rename_state' = "committed"
                  ELSE /\ UNCHANGED rename_state
            /\ pc' = [pc EXCEPT !["rename"] = "R_Unlock"]
            /\ UNCHANGED << src_entry, dst_entry, src_dir_lock, dst_dir_lock,
                            mdt_crashed, mdt_recovering, recovery_done,
                            lookup_src, lookup_dst >>

R_Unlock == /\ pc["rename"] = "R_Unlock"
            /\ IF ~mdt_crashed
                  THEN /\ src_dir_lock' = "free"
                       /\ dst_dir_lock' = "free"
                  ELSE /\ UNCHANGED << src_dir_lock, dst_dir_lock >>
            /\ pc' = [pc EXCEPT !["rename"] = "Done"]
            /\ UNCHANGED << src_entry, dst_entry, rename_state,
                            mdt_crashed, mdt_recovering, recovery_done,
                            lookup_src, lookup_dst >>

(* Lookup process actions *)

L_ReadSrc == /\ pc["lookup"] = "L_ReadSrc"
             /\ src_dir_lock /= "rename"
             /\ ~mdt_recovering
             /\ lookup_src' = (IF src_entry THEN "present" ELSE "absent")
             /\ pc' = [pc EXCEPT !["lookup"] = "L_ReadDst"]
             /\ UNCHANGED << src_entry, dst_entry, rename_state,
                             src_dir_lock, dst_dir_lock,
                             mdt_crashed, mdt_recovering, recovery_done,
                             lookup_dst >>

L_ReadDst == /\ pc["lookup"] = "L_ReadDst"
             /\ dst_dir_lock /= "rename"
             /\ ~mdt_recovering
             /\ lookup_dst' = (IF dst_entry THEN "present" ELSE "absent")
             /\ pc' = [pc EXCEPT !["lookup"] = "Done"]
             /\ UNCHANGED << src_entry, dst_entry, rename_state,
                             src_dir_lock, dst_dir_lock,
                             mdt_crashed, mdt_recovering, recovery_done,
                             lookup_src >>

(* CrashInjector process actions *)

C_MaybeCrash == /\ pc["crash"] = "C_MaybeCrash"
                /\ IF InjectCrash /\ rename_state = "phase1_done"
                      /\ ~mdt_crashed
                      THEN /\ mdt_crashed' = TRUE
                           /\ mdt_recovering' = TRUE
                           /\ rename_state' = "aborted"
                           /\ src_dir_lock' = "free"
                           /\ dst_dir_lock' = "free"
                      ELSE /\ UNCHANGED << mdt_crashed, mdt_recovering,
                                           rename_state, src_dir_lock,
                                           dst_dir_lock >>
                /\ pc' = [pc EXCEPT !["crash"] = "C_Recover"]
                /\ UNCHANGED << src_entry, dst_entry, recovery_done,
                                lookup_src, lookup_dst >>

C_Recover == /\ pc["crash"] = "C_Recover"
             /\ IF mdt_crashed /\ ~recovery_done
                   THEN /\ IF ~InjectNoRecovery
                              THEN /\ src_entry' = FALSE
                              ELSE /\ UNCHANGED src_entry
                        /\ recovery_done' = TRUE
                        /\ mdt_recovering' = FALSE
                   ELSE /\ UNCHANGED << src_entry, recovery_done,
                                        mdt_recovering >>
             /\ pc' = [pc EXCEPT !["crash"] = "Done"]
             /\ UNCHANGED << dst_entry, rename_state, src_dir_lock,
                             dst_dir_lock, mdt_crashed, lookup_src,
                             lookup_dst >>

(* Process compositions *)

Rename == R_LockSrc \/ R_LockDst \/ R_Phase1 \/ R_Phase2
             \/ R_Commit \/ R_Unlock

Lookup == L_ReadSrc \/ L_ReadDst

CrashInj == C_MaybeCrash \/ C_Recover

(* Allow stuttering after all processes terminate *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == Rename \/ Lookup \/ CrashInj
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Rename)
        /\ WF_vars(Lookup)
        /\ WF_vars(CrashInj)

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

=============================================================================
