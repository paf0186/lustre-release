---------------------------- MODULE mdt_rename_lock ----------------------------
(*
 * PlusCal/TLA+ specification of MDT rename locking protocol.
 *
 * Models the lock acquisition ordering for rename operations on the
 * Lustre MDS (lustre/mdt/mdt_reint.c: mdt_reint_rename).
 *
 * Concurrent actors:
 *   - Two rename threads operating on potentially overlapping objects
 *
 * Locks modeled (three levels):
 *   - BFL (Big File Lock): global rename serialization lock
 *   - Dir locks: LDLM locks on parent directory objects. Cross-dir
 *     renames contend on these; ordered by dir FID.
 *   - PDO hash locks: per-name-hash locks within a directory.
 *     Same-dir renames contend on these; ordered by hash value.
 *   - Child locks: EX locks on source/target child objects (by FID)
 *
 * Lock ordering in correct code:
 *   1. BFL (if needed)
 *   2. dir_lock[first_dir] (lower FID)
 *   3. pdo[first_dir][hash]
 *   4. dir_lock[second_dir] (higher FID, if different dir)
 *   5. pdo[second_dir][hash]
 *   6. child_lock[lower_fid]
 *   7. child_lock[higher_fid]
 *
 * Known bugs modeled:
 *   LU-15285: Same-directory rename deadlock (mv a b || mv b a)
 *             PDO name hash locks acquired source-first without
 *             hash-based ordering -> ABBA on pdo[dir][hash].
 *
 *   LU-15491: Cross-directory rename deadlock via hardlinks.
 *             Child locks acquired source-first without FID
 *             ordering. When hardlinks alias objects across two
 *             concurrent renames -> ABBA on child_lock[fid].
 *
 *   LU-4725:  Cross-directory rename deadlock. Parent directory
 *             locks acquired source-first without FID ordering.
 *             Two renames in opposite dir directions -> ABBA on
 *             dir_lock[fid].
 *
 *   LU-11104: Striped directory rename deadlock. Same mechanism
 *             as LU-4725: two stripes of the same striped dir
 *             locked without stripe index (FID) ordering.
 *
 * Validated against: lustre-release master 47638add78 (2026-09-06)
 *
 * Source (file:line ranges in that tree):
 *   lustre/mdt/mdt_reint.c
 *   - mdt_reint_rename()          2792-3271  main rename handler
 *       need_bfl decision 2897-2903 and 3002-3004; BFL taken first
 *       only on the second pass 2905-2913 (see note on LU-17427)
 *       LU-15285 same-dir hash ordering 2945-2950
 *       parent locks via mdt_lock_two_dirs() 2954-2959
 *       LU-15491 child FID ordering 3077-3090 / 3122-3128
 *       LU-17427 BFL trylock two-phase 3149-3206
 *       unlock order 3237-3258
 *   - mdt_rename_determine_lock_order() 2662-2747
 *       stripe-index ordering (LU-11104) 2740, FID ordering 2742-2746
 *   - mdt_lock_two_dirs()         2752-2785
 *       same dir: second PDO hash lock only if hashes differ 2772-2777
 *   - mdt_rename_lock()           1645-1669  BFL (EX UPDATE on
 *       LUSTRE_BFL_FID, 1663)
 *   - mdt_rename_source_lock()    1724-1755
 *   lustre/mdt/mdt_handler.c
 *   - mdt_lock_pdo_init()         170-196   name hash for PDO locks
 *   - mdt_lock_pdo_mode()         198-270   whole-dir lock mode (PW->CW)
 *   - mdt_object_pdo_lock()       4103-4174
 *   - mdt_object_check_lock()     4317-4352
 *   - mdt_parent_lock()           4368-4387
 *
 * Validation notes (2026-09-10): lock ordering rules match the code:
 * parents ordered by subdir relation / stripe index / FID
 * (mdt_rename_determine_lock_order), same-dir PDO hash locks ordered by
 * hash (LU-15285), child locks ordered by FID (LU-15491), BFL before
 * everything when needed.  Three abstraction caveats, none of which is
 * code drift: (1) since LU-17427 mdt_reint_rename first takes the parent
 * and child locks, trylocks the BFL and, if contended, drops all locks and
 * restarts with the BFL taken first; UseBFL=TRUE models that second
 * (blocking) pass.  (2) The model's dir_lock is exclusive, but the
 * whole-directory half of a PDO lock is LCK_CW for LCK_PW users
 * (mdt_lock_pdo_mode), so two renames alone never conflict on it in the
 * code; the LU-4725 / LU-11104 deadlocks involved another thread holding
 * PW/EX on a parent or stripe (e.g. mdt_object_stripes_lock).  The
 * exclusive dir_lock is a conservative stand-in that lets two renames
 * exhibit the ABBA the ordering rule prevents.  (3) mdt_lock_two_dirs
 * takes a single PDO lock when both names hash equally in the same dir;
 * this model would self-block if R*_SrcHash = R*_TgtHash, so no cfg uses
 * equal hashes.
 *)

EXTENDS Integers, FiniteSets, TLC

CONSTANTS
    InjectBug15285,     \* Same-dir PDO deadlock (no hash ordering)
    InjectBug15491,     \* Hardlink child lock deadlock (no FID ordering)
    InjectBug4725,      \* Cross-dir parent lock ordering deadlock
    InjectBug11104,     \* Striped dir stripe index ordering deadlock
    UseBFL,             \* Whether BFL (global rename lock) is required

    \* R1 scenario parameters
    R1_SrcDir,          \* Source parent directory FID (1 or 2)
    R1_TgtDir,          \* Target parent directory FID (1 or 2)
    R1_SrcHash,         \* Source name PDO hash (1-4)
    R1_TgtHash,         \* Target name PDO hash (1-4)
    R1_SrcChild,        \* Source child object FID (3-6)
    R1_TgtChild,        \* Target child object FID (3-6)

    \* R2 scenario parameters
    R2_SrcDir,
    R2_TgtDir,
    R2_SrcHash,
    R2_TgtHash,
    R2_SrcChild,
    R2_TgtChild

(* --algorithm PlusCal
variables
    (*
     * Lock state: each lock is "free" or held by a thread ID.
     *
     * Three lock levels:
     *   1. bfl - global rename lock
     *   2. dir_lock[fid] - directory-level LDLM lock (FID 1,2)
     *   3. pdo[dir][hash] - per-name-hash lock within a directory
     *   4. child_lock[fid] - child object EX lock (FID 3-6)
     *)

    bfl = "free",
    dir_lock = [d \in {1, 2} |-> "free"],
    pdo = [d \in {1, 2} |->
              [h \in {1, 2, 3, 4} |-> "free"]],
    child_lock = [f \in {3, 4, 5, 6} |-> "free"],
    done = [t \in {"R1", "R2"} |-> FALSE];

define
    NoLocksHeldByDone ==
        \A t \in {"R1", "R2"} :
            done[t] =>
                /\ bfl /= t
                /\ \A d \in {1, 2} : dir_lock[d] /= t
                /\ \A d \in {1, 2} : \A h \in {1, 2, 3, 4} :
                    pdo[d][h] /= t
                /\ \A f \in {3, 4, 5, 6} :
                    child_lock[f] /= t

    TypeOK ==
        /\ bfl \in {"free", "R1", "R2"}
        /\ \A d \in {1, 2} :
            dir_lock[d] \in {"free", "R1", "R2"}
        /\ \A d \in {1, 2} : \A h \in {1, 2, 3, 4} :
            pdo[d][h] \in {"free", "R1", "R2"}
        /\ \A f \in {3, 4, 5, 6} :
            child_lock[f] \in {"free", "R1", "R2"}
end define;

(*
 * ================================================================
 * Rename1: first concurrent rename thread
 * ================================================================
 *)
fair process Rename1 = "R1"
variables
    r1_first_dir = 0,
    r1_second_dir = 0,
    r1_first_hash = 0,
    r1_second_hash = 0;
begin

R1_BFL:
    if UseBFL then
        await bfl = "free";
        bfl := "R1";
    end if;

R1_OrderPDO:
    if R1_SrcDir = R1_TgtDir then
        \* Same directory: one dir lock, order PDO hashes
        r1_first_dir := R1_SrcDir;
        r1_second_dir := R1_TgtDir;
        if InjectBug15285 then
            \* BUG LU-15285: always source hash first
            r1_first_hash := R1_SrcHash;
            r1_second_hash := R1_TgtHash;
        else
            \* FIX: order by hash value
            if R1_SrcHash < R1_TgtHash then
                r1_first_hash := R1_SrcHash;
                r1_second_hash := R1_TgtHash;
            else
                r1_first_hash := R1_TgtHash;
                r1_second_hash := R1_SrcHash;
            end if;
        end if;
    else
        \* Different directories: order by dir FID
        if InjectBug4725 \/ InjectBug11104 then
            \* BUG: always src dir first
            r1_first_dir := R1_SrcDir;
            r1_second_dir := R1_TgtDir;
            r1_first_hash := R1_SrcHash;
            r1_second_hash := R1_TgtHash;
        else
            \* FIX: lower FID dir first
            if R1_SrcDir < R1_TgtDir then
                r1_first_dir := R1_SrcDir;
                r1_second_dir := R1_TgtDir;
                r1_first_hash := R1_SrcHash;
                r1_second_hash := R1_TgtHash;
            else
                r1_first_dir := R1_TgtDir;
                r1_second_dir := R1_SrcDir;
                r1_first_hash := R1_TgtHash;
                r1_second_hash := R1_SrcHash;
            end if;
        end if;
    end if;

R1_DirLock1:
    \* For cross-dir renames, acquire dir-level lock on first dir.
    \* Same-dir renames use PDO mode (hash-based) so no dir_lock
    \* contention - concurrent renames on same dir with different
    \* name hashes proceed in parallel (that's the whole point of PDO).
    if R1_SrcDir /= R1_TgtDir then
        await dir_lock[r1_first_dir] = "free";
        dir_lock[r1_first_dir] := "R1";
    end if;

R1_PDO1:
    await pdo[r1_first_dir][r1_first_hash] = "free";
    pdo[r1_first_dir][r1_first_hash] := "R1";

R1_DirLock2:
    if R1_SrcDir /= R1_TgtDir then
        await dir_lock[r1_second_dir] = "free";
        dir_lock[r1_second_dir] := "R1";
    end if;

R1_PDO2:
    await pdo[r1_second_dir][r1_second_hash] = "free";
    pdo[r1_second_dir][r1_second_hash] := "R1";

R1_Child1:
    if InjectBug15491 then
        await child_lock[R1_SrcChild] = "free";
        child_lock[R1_SrcChild] := "R1";
    else
        if R1_SrcChild < R1_TgtChild then
            await child_lock[R1_SrcChild] = "free";
            child_lock[R1_SrcChild] := "R1";
        else
            await child_lock[R1_TgtChild] = "free";
            child_lock[R1_TgtChild] := "R1";
        end if;
    end if;

R1_Child2:
    if InjectBug15491 then
        await child_lock[R1_TgtChild] = "free";
        child_lock[R1_TgtChild] := "R1";
    else
        if R1_SrcChild < R1_TgtChild then
            await child_lock[R1_TgtChild] = "free";
            child_lock[R1_TgtChild] := "R1";
        else
            await child_lock[R1_SrcChild] = "free";
            child_lock[R1_SrcChild] := "R1";
        end if;
    end if;

R1_DoRename:
    skip;

R1_UnlockChild2:
    if R1_SrcChild < R1_TgtChild then
        child_lock[R1_TgtChild] := "free";
    else
        child_lock[R1_SrcChild] := "free";
    end if;

R1_UnlockChild1:
    if R1_SrcChild < R1_TgtChild then
        child_lock[R1_SrcChild] := "free";
    else
        child_lock[R1_TgtChild] := "free";
    end if;

R1_UnlockPDO2:
    pdo[r1_second_dir][r1_second_hash] := "free";

R1_UnlockDir2:
    if R1_SrcDir /= R1_TgtDir then
        dir_lock[r1_second_dir] := "free";
    end if;

R1_UnlockPDO1:
    pdo[r1_first_dir][r1_first_hash] := "free";

R1_UnlockDir1:
    if R1_SrcDir /= R1_TgtDir then
        dir_lock[r1_first_dir] := "free";
    end if;

R1_UnlockBFL:
    if UseBFL then
        bfl := "free";
    end if;

R1_Done:
    done["R1"] := TRUE;

end process;

(*
 * ================================================================
 * Rename2: second concurrent rename thread
 * ================================================================
 *)
fair process Rename2 = "R2"
variables
    r2_first_dir = 0,
    r2_second_dir = 0,
    r2_first_hash = 0,
    r2_second_hash = 0;
begin

R2_BFL:
    if UseBFL then
        await bfl = "free";
        bfl := "R2";
    end if;

R2_OrderPDO:
    if R2_SrcDir = R2_TgtDir then
        r2_first_dir := R2_SrcDir;
        r2_second_dir := R2_TgtDir;
        if InjectBug15285 then
            r2_first_hash := R2_SrcHash;
            r2_second_hash := R2_TgtHash;
        else
            if R2_SrcHash < R2_TgtHash then
                r2_first_hash := R2_SrcHash;
                r2_second_hash := R2_TgtHash;
            else
                r2_first_hash := R2_TgtHash;
                r2_second_hash := R2_SrcHash;
            end if;
        end if;
    else
        if InjectBug4725 \/ InjectBug11104 then
            r2_first_dir := R2_SrcDir;
            r2_second_dir := R2_TgtDir;
            r2_first_hash := R2_SrcHash;
            r2_second_hash := R2_TgtHash;
        else
            if R2_SrcDir < R2_TgtDir then
                r2_first_dir := R2_SrcDir;
                r2_second_dir := R2_TgtDir;
                r2_first_hash := R2_SrcHash;
                r2_second_hash := R2_TgtHash;
            else
                r2_first_dir := R2_TgtDir;
                r2_second_dir := R2_SrcDir;
                r2_first_hash := R2_TgtHash;
                r2_second_hash := R2_SrcHash;
            end if;
        end if;
    end if;

R2_DirLock1:
    if R2_SrcDir /= R2_TgtDir then
        await dir_lock[r2_first_dir] = "free";
        dir_lock[r2_first_dir] := "R2";
    end if;

R2_PDO1:
    await pdo[r2_first_dir][r2_first_hash] = "free";
    pdo[r2_first_dir][r2_first_hash] := "R2";

R2_DirLock2:
    if R2_SrcDir /= R2_TgtDir then
        await dir_lock[r2_second_dir] = "free";
        dir_lock[r2_second_dir] := "R2";
    end if;

R2_PDO2:
    await pdo[r2_second_dir][r2_second_hash] = "free";
    pdo[r2_second_dir][r2_second_hash] := "R2";

R2_Child1:
    if InjectBug15491 then
        await child_lock[R2_SrcChild] = "free";
        child_lock[R2_SrcChild] := "R2";
    else
        if R2_SrcChild < R2_TgtChild then
            await child_lock[R2_SrcChild] = "free";
            child_lock[R2_SrcChild] := "R2";
        else
            await child_lock[R2_TgtChild] = "free";
            child_lock[R2_TgtChild] := "R2";
        end if;
    end if;

R2_Child2:
    if InjectBug15491 then
        await child_lock[R2_TgtChild] = "free";
        child_lock[R2_TgtChild] := "R2";
    else
        if R2_SrcChild < R2_TgtChild then
            await child_lock[R2_TgtChild] = "free";
            child_lock[R2_TgtChild] := "R2";
        else
            await child_lock[R2_SrcChild] = "free";
            child_lock[R2_SrcChild] := "R2";
        end if;
    end if;

R2_DoRename:
    skip;

R2_UnlockChild2:
    if R2_SrcChild < R2_TgtChild then
        child_lock[R2_TgtChild] := "free";
    else
        child_lock[R2_SrcChild] := "free";
    end if;

R2_UnlockChild1:
    if R2_SrcChild < R2_TgtChild then
        child_lock[R2_SrcChild] := "free";
    else
        child_lock[R2_TgtChild] := "free";
    end if;

R2_UnlockPDO2:
    pdo[r2_second_dir][r2_second_hash] := "free";

R2_UnlockDir2:
    if R2_SrcDir /= R2_TgtDir then
        dir_lock[r2_second_dir] := "free";
    end if;

R2_UnlockPDO1:
    pdo[r2_first_dir][r2_first_hash] := "free";

R2_UnlockDir1:
    if R2_SrcDir /= R2_TgtDir then
        dir_lock[r2_first_dir] := "free";
    end if;

R2_UnlockBFL:
    if UseBFL then
        bfl := "free";
    end if;

R2_Done:
    done["R2"] := TRUE;

end process;

end algorithm; *)
\* BEGIN TRANSLATION
VARIABLES bfl, dir_lock, pdo, child_lock, done, pc

(* define statement *)
NoLocksHeldByDone ==
    \A t \in {"R1", "R2"} :
        done[t] =>
            /\ bfl /= t
            /\ \A d \in {1, 2} : dir_lock[d] /= t
            /\ \A d \in {1, 2} : \A h \in {1, 2, 3, 4} :
                pdo[d][h] /= t
            /\ \A f \in {3, 4, 5, 6} :
                child_lock[f] /= t

TypeOK ==
    /\ bfl \in {"free", "R1", "R2"}
    /\ \A d \in {1, 2} :
        dir_lock[d] \in {"free", "R1", "R2"}
    /\ \A d \in {1, 2} : \A h \in {1, 2, 3, 4} :
        pdo[d][h] \in {"free", "R1", "R2"}
    /\ \A f \in {3, 4, 5, 6} :
        child_lock[f] \in {"free", "R1", "R2"}

VARIABLES r1_first_dir, r1_second_dir, r1_first_hash, r1_second_hash,
          r2_first_dir, r2_second_dir, r2_first_hash, r2_second_hash

vars == << bfl, dir_lock, pdo, child_lock, done, pc, r1_first_dir,
           r1_second_dir, r1_first_hash, r1_second_hash, r2_first_dir,
           r2_second_dir, r2_first_hash, r2_second_hash >>

ProcSet == {"R1"} \cup {"R2"}

Init == (* Global variables *)
        /\ bfl = "free"
        /\ dir_lock = [d \in {1, 2} |-> "free"]
        /\ pdo = [d \in {1, 2} |->
                     [h \in {1, 2, 3, 4} |-> "free"]]
        /\ child_lock = [f \in {3, 4, 5, 6} |-> "free"]
        /\ done = [t \in {"R1", "R2"} |-> FALSE]
        (* Process Rename1 *)
        /\ r1_first_dir = 0
        /\ r1_second_dir = 0
        /\ r1_first_hash = 0
        /\ r1_second_hash = 0
        (* Process Rename2 *)
        /\ r2_first_dir = 0
        /\ r2_second_dir = 0
        /\ r2_first_hash = 0
        /\ r2_second_hash = 0
        /\ pc = [self \in ProcSet |-> CASE self = "R1" -> "R1_BFL"
                                        [] self = "R2" -> "R2_BFL"]

R1_BFL == /\ pc["R1"] = "R1_BFL"
          /\ IF UseBFL
                THEN /\ bfl = "free"
                     /\ bfl' = "R1"
                ELSE /\ TRUE
                     /\ bfl' = bfl
          /\ pc' = [pc EXCEPT !["R1"] = "R1_OrderPDO"]
          /\ UNCHANGED << dir_lock, pdo, child_lock, done, r1_first_dir,
                          r1_second_dir, r1_first_hash, r1_second_hash,
                          r2_first_dir, r2_second_dir, r2_first_hash,
                          r2_second_hash >>

R1_OrderPDO == /\ pc["R1"] = "R1_OrderPDO"
               /\ IF R1_SrcDir = R1_TgtDir
                     THEN /\ r1_first_dir' = R1_SrcDir
                          /\ r1_second_dir' = R1_TgtDir
                          /\ IF InjectBug15285
                                THEN /\ r1_first_hash' = R1_SrcHash
                                     /\ r1_second_hash' = R1_TgtHash
                                ELSE /\ IF R1_SrcHash < R1_TgtHash
                                           THEN /\ r1_first_hash' = R1_SrcHash
                                                /\ r1_second_hash' = R1_TgtHash
                                           ELSE /\ r1_first_hash' = R1_TgtHash
                                                /\ r1_second_hash' = R1_SrcHash
                     ELSE /\ IF InjectBug4725 \/ InjectBug11104
                                THEN /\ r1_first_dir' = R1_SrcDir
                                     /\ r1_second_dir' = R1_TgtDir
                                     /\ r1_first_hash' = R1_SrcHash
                                     /\ r1_second_hash' = R1_TgtHash
                                ELSE /\ IF R1_SrcDir < R1_TgtDir
                                           THEN /\ r1_first_dir' = R1_SrcDir
                                                /\ r1_second_dir' = R1_TgtDir
                                                /\ r1_first_hash' = R1_SrcHash
                                                /\ r1_second_hash' = R1_TgtHash
                                           ELSE /\ r1_first_dir' = R1_TgtDir
                                                /\ r1_second_dir' = R1_SrcDir
                                                /\ r1_first_hash' = R1_TgtHash
                                                /\ r1_second_hash' = R1_SrcHash
               /\ pc' = [pc EXCEPT !["R1"] = "R1_DirLock1"]
               /\ UNCHANGED << bfl, dir_lock, pdo, child_lock, done,
                               r2_first_dir, r2_second_dir, r2_first_hash,
                               r2_second_hash >>

R1_DirLock1 == /\ pc["R1"] = "R1_DirLock1"
               /\ IF R1_SrcDir /= R1_TgtDir
                     THEN /\ dir_lock[r1_first_dir] = "free"
                          /\ dir_lock' = [dir_lock EXCEPT ![r1_first_dir] = "R1"]
                     ELSE /\ TRUE
                          /\ UNCHANGED dir_lock
               /\ pc' = [pc EXCEPT !["R1"] = "R1_PDO1"]
               /\ UNCHANGED << bfl, pdo, child_lock, done, r1_first_dir,
                               r1_second_dir, r1_first_hash, r1_second_hash,
                               r2_first_dir, r2_second_dir, r2_first_hash,
                               r2_second_hash >>

R1_PDO1 == /\ pc["R1"] = "R1_PDO1"
           /\ pdo[r1_first_dir][r1_first_hash] = "free"
           /\ pdo' = [pdo EXCEPT ![r1_first_dir][r1_first_hash] = "R1"]
           /\ pc' = [pc EXCEPT !["R1"] = "R1_DirLock2"]
           /\ UNCHANGED << bfl, dir_lock, child_lock, done, r1_first_dir,
                           r1_second_dir, r1_first_hash, r1_second_hash,
                           r2_first_dir, r2_second_dir, r2_first_hash,
                           r2_second_hash >>

R1_DirLock2 == /\ pc["R1"] = "R1_DirLock2"
               /\ IF R1_SrcDir /= R1_TgtDir
                     THEN /\ dir_lock[r1_second_dir] = "free"
                          /\ dir_lock' = [dir_lock EXCEPT ![r1_second_dir] = "R1"]
                     ELSE /\ TRUE
                          /\ UNCHANGED dir_lock
               /\ pc' = [pc EXCEPT !["R1"] = "R1_PDO2"]
               /\ UNCHANGED << bfl, pdo, child_lock, done, r1_first_dir,
                               r1_second_dir, r1_first_hash, r1_second_hash,
                               r2_first_dir, r2_second_dir, r2_first_hash,
                               r2_second_hash >>

R1_PDO2 == /\ pc["R1"] = "R1_PDO2"
           /\ pdo[r1_second_dir][r1_second_hash] = "free"
           /\ pdo' = [pdo EXCEPT ![r1_second_dir][r1_second_hash] = "R1"]
           /\ pc' = [pc EXCEPT !["R1"] = "R1_Child1"]
           /\ UNCHANGED << bfl, dir_lock, child_lock, done, r1_first_dir,
                           r1_second_dir, r1_first_hash, r1_second_hash,
                           r2_first_dir, r2_second_dir, r2_first_hash,
                           r2_second_hash >>

R1_Child1 == /\ pc["R1"] = "R1_Child1"
             /\ IF InjectBug15491
                   THEN /\ child_lock[R1_SrcChild] = "free"
                        /\ child_lock' = [child_lock EXCEPT ![R1_SrcChild] = "R1"]
                   ELSE /\ IF R1_SrcChild < R1_TgtChild
                              THEN /\ child_lock[R1_SrcChild] = "free"
                                   /\ child_lock' = [child_lock EXCEPT ![R1_SrcChild] = "R1"]
                              ELSE /\ child_lock[R1_TgtChild] = "free"
                                   /\ child_lock' = [child_lock EXCEPT ![R1_TgtChild] = "R1"]
             /\ pc' = [pc EXCEPT !["R1"] = "R1_Child2"]
             /\ UNCHANGED << bfl, dir_lock, pdo, done, r1_first_dir,
                             r1_second_dir, r1_first_hash, r1_second_hash,
                             r2_first_dir, r2_second_dir, r2_first_hash,
                             r2_second_hash >>

R1_Child2 == /\ pc["R1"] = "R1_Child2"
             /\ IF InjectBug15491
                   THEN /\ child_lock[R1_TgtChild] = "free"
                        /\ child_lock' = [child_lock EXCEPT ![R1_TgtChild] = "R1"]
                   ELSE /\ IF R1_SrcChild < R1_TgtChild
                              THEN /\ child_lock[R1_TgtChild] = "free"
                                   /\ child_lock' = [child_lock EXCEPT ![R1_TgtChild] = "R1"]
                              ELSE /\ child_lock[R1_SrcChild] = "free"
                                   /\ child_lock' = [child_lock EXCEPT ![R1_SrcChild] = "R1"]
             /\ pc' = [pc EXCEPT !["R1"] = "R1_DoRename"]
             /\ UNCHANGED << bfl, dir_lock, pdo, done, r1_first_dir,
                             r1_second_dir, r1_first_hash, r1_second_hash,
                             r2_first_dir, r2_second_dir, r2_first_hash,
                             r2_second_hash >>

R1_DoRename == /\ pc["R1"] = "R1_DoRename"
               /\ TRUE
               /\ pc' = [pc EXCEPT !["R1"] = "R1_UnlockChild2"]
               /\ UNCHANGED << bfl, dir_lock, pdo, child_lock, done,
                               r1_first_dir, r1_second_dir, r1_first_hash,
                               r1_second_hash, r2_first_dir, r2_second_dir,
                               r2_first_hash, r2_second_hash >>

R1_UnlockChild2 == /\ pc["R1"] = "R1_UnlockChild2"
                   /\ IF R1_SrcChild < R1_TgtChild
                         THEN /\ child_lock' = [child_lock EXCEPT ![R1_TgtChild] = "free"]
                         ELSE /\ child_lock' = [child_lock EXCEPT ![R1_SrcChild] = "free"]
                   /\ pc' = [pc EXCEPT !["R1"] = "R1_UnlockChild1"]
                   /\ UNCHANGED << bfl, dir_lock, pdo, done, r1_first_dir,
                                   r1_second_dir, r1_first_hash,
                                   r1_second_hash, r2_first_dir, r2_second_dir,
                                   r2_first_hash, r2_second_hash >>

R1_UnlockChild1 == /\ pc["R1"] = "R1_UnlockChild1"
                   /\ IF R1_SrcChild < R1_TgtChild
                         THEN /\ child_lock' = [child_lock EXCEPT ![R1_SrcChild] = "free"]
                         ELSE /\ child_lock' = [child_lock EXCEPT ![R1_TgtChild] = "free"]
                   /\ pc' = [pc EXCEPT !["R1"] = "R1_UnlockPDO2"]
                   /\ UNCHANGED << bfl, dir_lock, pdo, done, r1_first_dir,
                                   r1_second_dir, r1_first_hash,
                                   r1_second_hash, r2_first_dir, r2_second_dir,
                                   r2_first_hash, r2_second_hash >>

R1_UnlockPDO2 == /\ pc["R1"] = "R1_UnlockPDO2"
                 /\ pdo' = [pdo EXCEPT ![r1_second_dir][r1_second_hash] = "free"]
                 /\ pc' = [pc EXCEPT !["R1"] = "R1_UnlockDir2"]
                 /\ UNCHANGED << bfl, dir_lock, child_lock, done, r1_first_dir,
                                 r1_second_dir, r1_first_hash, r1_second_hash,
                                 r2_first_dir, r2_second_dir, r2_first_hash,
                                 r2_second_hash >>

R1_UnlockDir2 == /\ pc["R1"] = "R1_UnlockDir2"
                 /\ IF R1_SrcDir /= R1_TgtDir
                       THEN /\ dir_lock' = [dir_lock EXCEPT ![r1_second_dir] = "free"]
                       ELSE /\ TRUE
                            /\ UNCHANGED dir_lock
                 /\ pc' = [pc EXCEPT !["R1"] = "R1_UnlockPDO1"]
                 /\ UNCHANGED << bfl, pdo, child_lock, done, r1_first_dir,
                                 r1_second_dir, r1_first_hash, r1_second_hash,
                                 r2_first_dir, r2_second_dir, r2_first_hash,
                                 r2_second_hash >>

R1_UnlockPDO1 == /\ pc["R1"] = "R1_UnlockPDO1"
                 /\ pdo' = [pdo EXCEPT ![r1_first_dir][r1_first_hash] = "free"]
                 /\ pc' = [pc EXCEPT !["R1"] = "R1_UnlockDir1"]
                 /\ UNCHANGED << bfl, dir_lock, child_lock, done, r1_first_dir,
                                 r1_second_dir, r1_first_hash, r1_second_hash,
                                 r2_first_dir, r2_second_dir, r2_first_hash,
                                 r2_second_hash >>

R1_UnlockDir1 == /\ pc["R1"] = "R1_UnlockDir1"
                 /\ IF R1_SrcDir /= R1_TgtDir
                       THEN /\ dir_lock' = [dir_lock EXCEPT ![r1_first_dir] = "free"]
                       ELSE /\ TRUE
                            /\ UNCHANGED dir_lock
                 /\ pc' = [pc EXCEPT !["R1"] = "R1_UnlockBFL"]
                 /\ UNCHANGED << bfl, pdo, child_lock, done, r1_first_dir,
                                 r1_second_dir, r1_first_hash, r1_second_hash,
                                 r2_first_dir, r2_second_dir, r2_first_hash,
                                 r2_second_hash >>

R1_UnlockBFL == /\ pc["R1"] = "R1_UnlockBFL"
                /\ IF UseBFL
                      THEN /\ bfl' = "free"
                      ELSE /\ TRUE
                           /\ bfl' = bfl
                /\ pc' = [pc EXCEPT !["R1"] = "R1_Done"]
                /\ UNCHANGED << dir_lock, pdo, child_lock, done, r1_first_dir,
                                r1_second_dir, r1_first_hash, r1_second_hash,
                                r2_first_dir, r2_second_dir, r2_first_hash,
                                r2_second_hash >>

R1_Done == /\ pc["R1"] = "R1_Done"
           /\ done' = [done EXCEPT !["R1"] = TRUE]
           /\ pc' = [pc EXCEPT !["R1"] = "Done"]
           /\ UNCHANGED << bfl, dir_lock, pdo, child_lock, r1_first_dir,
                           r1_second_dir, r1_first_hash, r1_second_hash,
                           r2_first_dir, r2_second_dir, r2_first_hash,
                           r2_second_hash >>

Rename1 == R1_BFL \/ R1_OrderPDO \/ R1_DirLock1 \/ R1_PDO1 \/ R1_DirLock2
              \/ R1_PDO2 \/ R1_Child1 \/ R1_Child2 \/ R1_DoRename
              \/ R1_UnlockChild2 \/ R1_UnlockChild1 \/ R1_UnlockPDO2
              \/ R1_UnlockDir2 \/ R1_UnlockPDO1 \/ R1_UnlockDir1
              \/ R1_UnlockBFL \/ R1_Done

R2_BFL == /\ pc["R2"] = "R2_BFL"
          /\ IF UseBFL
                THEN /\ bfl = "free"
                     /\ bfl' = "R2"
                ELSE /\ TRUE
                     /\ bfl' = bfl
          /\ pc' = [pc EXCEPT !["R2"] = "R2_OrderPDO"]
          /\ UNCHANGED << dir_lock, pdo, child_lock, done, r1_first_dir,
                          r1_second_dir, r1_first_hash, r1_second_hash,
                          r2_first_dir, r2_second_dir, r2_first_hash,
                          r2_second_hash >>

R2_OrderPDO == /\ pc["R2"] = "R2_OrderPDO"
               /\ IF R2_SrcDir = R2_TgtDir
                     THEN /\ r2_first_dir' = R2_SrcDir
                          /\ r2_second_dir' = R2_TgtDir
                          /\ IF InjectBug15285
                                THEN /\ r2_first_hash' = R2_SrcHash
                                     /\ r2_second_hash' = R2_TgtHash
                                ELSE /\ IF R2_SrcHash < R2_TgtHash
                                           THEN /\ r2_first_hash' = R2_SrcHash
                                                /\ r2_second_hash' = R2_TgtHash
                                           ELSE /\ r2_first_hash' = R2_TgtHash
                                                /\ r2_second_hash' = R2_SrcHash
                     ELSE /\ IF InjectBug4725 \/ InjectBug11104
                                THEN /\ r2_first_dir' = R2_SrcDir
                                     /\ r2_second_dir' = R2_TgtDir
                                     /\ r2_first_hash' = R2_SrcHash
                                     /\ r2_second_hash' = R2_TgtHash
                                ELSE /\ IF R2_SrcDir < R2_TgtDir
                                           THEN /\ r2_first_dir' = R2_SrcDir
                                                /\ r2_second_dir' = R2_TgtDir
                                                /\ r2_first_hash' = R2_SrcHash
                                                /\ r2_second_hash' = R2_TgtHash
                                           ELSE /\ r2_first_dir' = R2_TgtDir
                                                /\ r2_second_dir' = R2_SrcDir
                                                /\ r2_first_hash' = R2_TgtHash
                                                /\ r2_second_hash' = R2_SrcHash
               /\ pc' = [pc EXCEPT !["R2"] = "R2_DirLock1"]
               /\ UNCHANGED << bfl, dir_lock, pdo, child_lock, done,
                               r1_first_dir, r1_second_dir, r1_first_hash,
                               r1_second_hash >>

R2_DirLock1 == /\ pc["R2"] = "R2_DirLock1"
               /\ IF R2_SrcDir /= R2_TgtDir
                     THEN /\ dir_lock[r2_first_dir] = "free"
                          /\ dir_lock' = [dir_lock EXCEPT ![r2_first_dir] = "R2"]
                     ELSE /\ TRUE
                          /\ UNCHANGED dir_lock
               /\ pc' = [pc EXCEPT !["R2"] = "R2_PDO1"]
               /\ UNCHANGED << bfl, pdo, child_lock, done, r1_first_dir,
                               r1_second_dir, r1_first_hash, r1_second_hash,
                               r2_first_dir, r2_second_dir, r2_first_hash,
                               r2_second_hash >>

R2_PDO1 == /\ pc["R2"] = "R2_PDO1"
           /\ pdo[r2_first_dir][r2_first_hash] = "free"
           /\ pdo' = [pdo EXCEPT ![r2_first_dir][r2_first_hash] = "R2"]
           /\ pc' = [pc EXCEPT !["R2"] = "R2_DirLock2"]
           /\ UNCHANGED << bfl, dir_lock, child_lock, done, r1_first_dir,
                           r1_second_dir, r1_first_hash, r1_second_hash,
                           r2_first_dir, r2_second_dir, r2_first_hash,
                           r2_second_hash >>

R2_DirLock2 == /\ pc["R2"] = "R2_DirLock2"
               /\ IF R2_SrcDir /= R2_TgtDir
                     THEN /\ dir_lock[r2_second_dir] = "free"
                          /\ dir_lock' = [dir_lock EXCEPT ![r2_second_dir] = "R2"]
                     ELSE /\ TRUE
                          /\ UNCHANGED dir_lock
               /\ pc' = [pc EXCEPT !["R2"] = "R2_PDO2"]
               /\ UNCHANGED << bfl, pdo, child_lock, done, r1_first_dir,
                               r1_second_dir, r1_first_hash, r1_second_hash,
                               r2_first_dir, r2_second_dir, r2_first_hash,
                               r2_second_hash >>

R2_PDO2 == /\ pc["R2"] = "R2_PDO2"
           /\ pdo[r2_second_dir][r2_second_hash] = "free"
           /\ pdo' = [pdo EXCEPT ![r2_second_dir][r2_second_hash] = "R2"]
           /\ pc' = [pc EXCEPT !["R2"] = "R2_Child1"]
           /\ UNCHANGED << bfl, dir_lock, child_lock, done, r1_first_dir,
                           r1_second_dir, r1_first_hash, r1_second_hash,
                           r2_first_dir, r2_second_dir, r2_first_hash,
                           r2_second_hash >>

R2_Child1 == /\ pc["R2"] = "R2_Child1"
             /\ IF InjectBug15491
                   THEN /\ child_lock[R2_SrcChild] = "free"
                        /\ child_lock' = [child_lock EXCEPT ![R2_SrcChild] = "R2"]
                   ELSE /\ IF R2_SrcChild < R2_TgtChild
                              THEN /\ child_lock[R2_SrcChild] = "free"
                                   /\ child_lock' = [child_lock EXCEPT ![R2_SrcChild] = "R2"]
                              ELSE /\ child_lock[R2_TgtChild] = "free"
                                   /\ child_lock' = [child_lock EXCEPT ![R2_TgtChild] = "R2"]
             /\ pc' = [pc EXCEPT !["R2"] = "R2_Child2"]
             /\ UNCHANGED << bfl, dir_lock, pdo, done, r1_first_dir,
                             r1_second_dir, r1_first_hash, r1_second_hash,
                             r2_first_dir, r2_second_dir, r2_first_hash,
                             r2_second_hash >>

R2_Child2 == /\ pc["R2"] = "R2_Child2"
             /\ IF InjectBug15491
                   THEN /\ child_lock[R2_TgtChild] = "free"
                        /\ child_lock' = [child_lock EXCEPT ![R2_TgtChild] = "R2"]
                   ELSE /\ IF R2_SrcChild < R2_TgtChild
                              THEN /\ child_lock[R2_TgtChild] = "free"
                                   /\ child_lock' = [child_lock EXCEPT ![R2_TgtChild] = "R2"]
                              ELSE /\ child_lock[R2_SrcChild] = "free"
                                   /\ child_lock' = [child_lock EXCEPT ![R2_SrcChild] = "R2"]
             /\ pc' = [pc EXCEPT !["R2"] = "R2_DoRename"]
             /\ UNCHANGED << bfl, dir_lock, pdo, done, r1_first_dir,
                             r1_second_dir, r1_first_hash, r1_second_hash,
                             r2_first_dir, r2_second_dir, r2_first_hash,
                             r2_second_hash >>

R2_DoRename == /\ pc["R2"] = "R2_DoRename"
               /\ TRUE
               /\ pc' = [pc EXCEPT !["R2"] = "R2_UnlockChild2"]
               /\ UNCHANGED << bfl, dir_lock, pdo, child_lock, done,
                               r1_first_dir, r1_second_dir, r1_first_hash,
                               r1_second_hash, r2_first_dir, r2_second_dir,
                               r2_first_hash, r2_second_hash >>

R2_UnlockChild2 == /\ pc["R2"] = "R2_UnlockChild2"
                   /\ IF R2_SrcChild < R2_TgtChild
                         THEN /\ child_lock' = [child_lock EXCEPT ![R2_TgtChild] = "free"]
                         ELSE /\ child_lock' = [child_lock EXCEPT ![R2_SrcChild] = "free"]
                   /\ pc' = [pc EXCEPT !["R2"] = "R2_UnlockChild1"]
                   /\ UNCHANGED << bfl, dir_lock, pdo, done, r1_first_dir,
                                   r1_second_dir, r1_first_hash,
                                   r1_second_hash, r2_first_dir, r2_second_dir,
                                   r2_first_hash, r2_second_hash >>

R2_UnlockChild1 == /\ pc["R2"] = "R2_UnlockChild1"
                   /\ IF R2_SrcChild < R2_TgtChild
                         THEN /\ child_lock' = [child_lock EXCEPT ![R2_SrcChild] = "free"]
                         ELSE /\ child_lock' = [child_lock EXCEPT ![R2_TgtChild] = "free"]
                   /\ pc' = [pc EXCEPT !["R2"] = "R2_UnlockPDO2"]
                   /\ UNCHANGED << bfl, dir_lock, pdo, done, r1_first_dir,
                                   r1_second_dir, r1_first_hash,
                                   r1_second_hash, r2_first_dir, r2_second_dir,
                                   r2_first_hash, r2_second_hash >>

R2_UnlockPDO2 == /\ pc["R2"] = "R2_UnlockPDO2"
                 /\ pdo' = [pdo EXCEPT ![r2_second_dir][r2_second_hash] = "free"]
                 /\ pc' = [pc EXCEPT !["R2"] = "R2_UnlockDir2"]
                 /\ UNCHANGED << bfl, dir_lock, child_lock, done, r1_first_dir,
                                 r1_second_dir, r1_first_hash, r1_second_hash,
                                 r2_first_dir, r2_second_dir, r2_first_hash,
                                 r2_second_hash >>

R2_UnlockDir2 == /\ pc["R2"] = "R2_UnlockDir2"
                 /\ IF R2_SrcDir /= R2_TgtDir
                       THEN /\ dir_lock' = [dir_lock EXCEPT ![r2_second_dir] = "free"]
                       ELSE /\ TRUE
                            /\ UNCHANGED dir_lock
                 /\ pc' = [pc EXCEPT !["R2"] = "R2_UnlockPDO1"]
                 /\ UNCHANGED << bfl, pdo, child_lock, done, r1_first_dir,
                                 r1_second_dir, r1_first_hash, r1_second_hash,
                                 r2_first_dir, r2_second_dir, r2_first_hash,
                                 r2_second_hash >>

R2_UnlockPDO1 == /\ pc["R2"] = "R2_UnlockPDO1"
                 /\ pdo' = [pdo EXCEPT ![r2_first_dir][r2_first_hash] = "free"]
                 /\ pc' = [pc EXCEPT !["R2"] = "R2_UnlockDir1"]
                 /\ UNCHANGED << bfl, dir_lock, child_lock, done, r1_first_dir,
                                 r1_second_dir, r1_first_hash, r1_second_hash,
                                 r2_first_dir, r2_second_dir, r2_first_hash,
                                 r2_second_hash >>

R2_UnlockDir1 == /\ pc["R2"] = "R2_UnlockDir1"
                 /\ IF R2_SrcDir /= R2_TgtDir
                       THEN /\ dir_lock' = [dir_lock EXCEPT ![r2_first_dir] = "free"]
                       ELSE /\ TRUE
                            /\ UNCHANGED dir_lock
                 /\ pc' = [pc EXCEPT !["R2"] = "R2_UnlockBFL"]
                 /\ UNCHANGED << bfl, pdo, child_lock, done, r1_first_dir,
                                 r1_second_dir, r1_first_hash, r1_second_hash,
                                 r2_first_dir, r2_second_dir, r2_first_hash,
                                 r2_second_hash >>

R2_UnlockBFL == /\ pc["R2"] = "R2_UnlockBFL"
                /\ IF UseBFL
                      THEN /\ bfl' = "free"
                      ELSE /\ TRUE
                           /\ bfl' = bfl
                /\ pc' = [pc EXCEPT !["R2"] = "R2_Done"]
                /\ UNCHANGED << dir_lock, pdo, child_lock, done, r1_first_dir,
                                r1_second_dir, r1_first_hash, r1_second_hash,
                                r2_first_dir, r2_second_dir, r2_first_hash,
                                r2_second_hash >>

R2_Done == /\ pc["R2"] = "R2_Done"
           /\ done' = [done EXCEPT !["R2"] = TRUE]
           /\ pc' = [pc EXCEPT !["R2"] = "Done"]
           /\ UNCHANGED << bfl, dir_lock, pdo, child_lock, r1_first_dir,
                           r1_second_dir, r1_first_hash, r1_second_hash,
                           r2_first_dir, r2_second_dir, r2_first_hash,
                           r2_second_hash >>

Rename2 == R2_BFL \/ R2_OrderPDO \/ R2_DirLock1 \/ R2_PDO1 \/ R2_DirLock2
              \/ R2_PDO2 \/ R2_Child1 \/ R2_Child2 \/ R2_DoRename
              \/ R2_UnlockChild2 \/ R2_UnlockChild1 \/ R2_UnlockPDO2
              \/ R2_UnlockDir2 \/ R2_UnlockPDO1 \/ R2_UnlockDir1
              \/ R2_UnlockBFL \/ R2_Done

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == Rename1 \/ Rename2
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Rename1)
        /\ WF_vars(Rename2)

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

=============================================================================
