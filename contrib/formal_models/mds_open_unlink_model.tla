---------------------------- MODULE mds_open_unlink_model ----------------------------
(*
 * TLA+ model of the MDS open/unlink nlink race.
 *
 * Models MDT orphan tracking in Lustre: a client holds an open file
 * descriptor while another client unlinks the file. The critical
 * invariant (ReclamationSafety): the inode must not be reclaimed
 * while any client still has it open.
 *
 * Scope:
 *   - 2 clients: OpenerClient (open/close/eviction) and UnlinkerClient
 *   - 1 file, open_count bounded at MaxOpen, nlink bounded at MaxNlink
 *   - File starts with MaxNlink hard links; opener can open up to MaxOpen times
 *   - Actions: Open, CommitOpen, Close, ClientDisconnect (eviction), Unlink
 *   - Target: <10K states
 *
 * Opener phase machine:
 *   "init"   -- deciding how many opens to issue (DoOpen stays in "init";
 *               DoCommitOpen transitions to "open" once done opening;
 *               DoSkipOpen ends with zero opens)
 *   "open"   -- done opening; now draining fds via DoClose or DoDisconnect
 *   "done"   -- all fds closed (open_count = 0)
 *
 * This two-phase design (opening vs. closing) avoids liveness violations
 * from open/close cycles while still exercising all open_count interleavings.
 *
 * Multi-link support (MaxNlink > 1):
 *   File starts with MaxNlink hard links. UnlinkerClient can perform
 *   multiple unlinks (one per DoUnlink firing, staying in "init") until
 *   nlink reaches 0. Orphan logic only triggers on the final unlink.
 *
 * Multi-open support (MaxOpen > 1):
 *   OpenerClient issues up to MaxOpen Opens in "init" phase, then commits
 *   to closing. DoDisconnect (eviction) closes ALL open fds atomically
 *   (models mdt_export_cleanup() draining med_open_head through
 *   mdt_mfd_close()).
 *
 * Bug injection (InjectBugOrphan = TRUE):
 *   When nlink drops to 0 and open_count > 0, skip setting the orphan
 *   flag. The MDS reclaims the inode immediately -- a use-after-free
 *   scenario because the opener still holds a live file descriptor.
 *
 * Correct behavior (InjectBugOrphan = FALSE):
 *   Set is_orphan when nlink reaches 0 with open_count > 0. Defer
 *   reclamation until the last close/eviction drains open_count to 0.
 *   This is the "orphan inode" path in mdt_reint_unlink() -> mdo_unlink()
 *   -> mdd_unlink() -> mdd_finish_unlink().
 *
 * Validated against: lustre-release master 47638add78 (2026-09-06)
 *
 * Source (file:line ranges in that tree):
 *   - mdt_reint_unlink()        lustre/mdt/mdt_reint.c:1263-1498
 *   - mdd_unlink()              lustre/mdd/mdd_dir.c:2176-2346
 *       write lock 2238, mdo_ref_del() 2261, mdd_finish_unlink() 2305,
 *       write unlock 2328
 *   - mdd_declare_finish_unlink() lustre/mdd/mdd_dir.c:1985-2009
 *   - mdd_finish_unlink()       lustre/mdd/mdd_dir.c:2011-2054
 *       LASSERT(write locked) 2022, DEAD_OBJ 2026, mod_count check 2027,
 *       mdd_orphan_insert() 2028, mdo_destroy() 2045
 *   - mdd_open()                lustre/mdd/mdd_object.c:3767-3859
 *       write lock 3781, mod_count++ 3794
 *   - mdd_open_sanity_check()   lustre/mdd/mdd_object.c:3708-3757
 *   - mdd_close()               lustre/mdd/mdd_object.c:3874-4070
 *       MDS_KEEP_ORPHAN path 3888-3897, lockless pre-check 3903,
 *       locked re-check 3956, retry 3960-3962, mod_count-- 3965,
 *       mdd_orphan_delete() 4001, mdo_destroy() 4017
 *   - mdd_orphan_insert()       lustre/mdd/mdd_orphans.c:138-184 (149-150)
 *   - mdd_orphan_delete()       lustre/mdd/mdd_orphans.c:229-271 (238-240)
 *   - mdt_mfd_close()           lustre/mdt/mdt_open.c:2583-2734
 *       mot_open_count dec 2708, mdt_handle_last_unlink() 2709,
 *       mo_close() 2712
 *   - mdt_export_cleanup()      lustre/mdt/mdt_handler.c:7360-7443
 *       (MDS_KEEP_ORPHAN on failover/stopping 7425-7428,
 *        mdt_mfd_close() per mfd 7431)
 *   - mdt_handle_last_unlink()  lustre/mdt/mdt_lib.c:1095-1195
 *   - mdt_reint_open()/mdt_mfd_open() lustre/mdt/mdt_open.c:1440 / 361
 *
 * Validation notes (2026-09-10): no semantic drift; the lock discipline
 * described below is unchanged.  Function names that never existed
 * (mdt_client_del, mdt_close_unpack, mdt_iput_final, mdt->mdt_lock) were
 * replaced in comments.  Scope limits relative to the code: (1) eviction
 * on failover umount / OBDF_STOPPING closes with MDS_KEEP_ORPHAN and does
 * NOT reclaim (the orphan is left for the next recovery); DoDisconnect
 * models the normal eviction case only.  (2) mdd_open_sanity_check() lets
 * an already-open orphan be re-opened by FID (mod_count++ with nlink=0);
 * DoOpen requires nlink > 0 and does not model that path.  (3) The MDT
 * layer keeps a second counter, mot_open_count, used only by
 * mdt_handle_last_unlink() for HSM RAoLU; open_count here is mod_count.
 *
 * C code verification (2026-03-13, lustre-design-docs-at9.21):
 *   Each TLA+ action is atomic because the C code holds the DT_TGT_CHILD
 *   write lock (mdd_write_lock) on the child MDD object for the entire
 *   critical section.  Specifically:
 *     - mdd_open()     : write lock -> mod_count++              -> unlock
 *     - mdd_close()    : write lock -> mod_count-- + cleanup    -> unlock
 *     - mdd_unlink()   : write lock -> nlink-- + orphan-or-destroy -> unlock
 *   The nlink decrement and mod_count check in mdd_finish_unlink() are in
 *   the same lock hold as the orphan-or-destroy decision, so the race
 *   modeled by InjectBugOrphan=TRUE cannot occur.
 *   See: mds_open_unlink_analysis.md for full trace.
 *)

EXTENDS Integers, FiniteSets, TLC

CONSTANTS
    MaxNlink,        (* upper bound on nlink (file starts with MaxNlink links) *)
    MaxOpen,         (* upper bound on open_count *)
    InjectBugOrphan  (* TRUE = skip orphan flag on unlink; FALSE = correct *)

VARIABLES
    nlink,           (* number of hard links to the file [0..MaxNlink] *)
    open_count,      (* number of open file descriptors [0..MaxOpen] *)
    is_orphan,       (* TRUE: nlink=0 set while open_count>0 (defer reclaim) *)
    reclaimed,       (* TRUE: inode has been freed (set reclaimed once) *)
    opener_phase,    (* "init" | "open" | "done" *)
    unlinker_phase   (* "init" | "done" *)

vars == <<nlink, open_count, is_orphan, reclaimed, opener_phase, unlinker_phase>>

(* ================================================================
 * Type invariant
 * ================================================================ *)

TypeOK ==
    /\ nlink \in 0..MaxNlink
    /\ open_count \in 0..MaxOpen
    /\ is_orphan \in BOOLEAN
    /\ reclaimed \in BOOLEAN
    /\ opener_phase \in {"init", "open", "done"}
    /\ unlinker_phase \in {"init", "done"}

(* ================================================================
 * Initial state
 * File exists with MaxNlink hard links; no clients have it open.
 * ================================================================ *)

Init ==
    /\ nlink = MaxNlink
    /\ open_count = 0
    /\ is_orphan = FALSE
    /\ reclaimed = FALSE
    /\ opener_phase = "init"
    /\ unlinker_phase = "init"

(* ================================================================
 * MDS Actions
 *
 * Each action models one atomic MDS operation (serialized through
 * the MDS lock implicitly).  The C code holds the DT_TGT_CHILD
 * mdd_write_lock() on the child object while modifying these fields
 * (see the Source block in the header).
 * ================================================================ *)

(*
 * Open: OpenerClient sends OPEN RPC to MDS (while still in init phase).
 * Precondition: file still exists (nlink > 0) and not yet reclaimed;
 *   open_count must be below MaxOpen; opener is still accumulating opens.
 * Effect: MDS increments open_count (mfd inserted into med_open_head).
 * Opener stays in "init" to allow additional opens up to MaxOpen.
 *)
DoOpen ==
    /\ opener_phase = "init"
    /\ nlink > 0
    /\ ~reclaimed
    /\ open_count < MaxOpen
    /\ open_count' = open_count + 1
    /\ opener_phase' = "init"
    /\ UNCHANGED <<nlink, is_orphan, reclaimed, unlinker_phase>>

(*
 * CommitOpen: OpenerClient is done opening; transition to closing phase.
 * Requires at least one fd is open.  After this point the opener only
 * closes (DoClose) or gets evicted (DoDisconnect).
 *)
DoCommitOpen ==
    /\ opener_phase = "init"
    /\ open_count > 0
    /\ opener_phase' = "open"
    /\ UNCHANGED <<nlink, open_count, is_orphan, reclaimed, unlinker_phase>>

(*
 * SkipOpen: OpenerClient never opens (open RPC fails, or client
 * simply doesn't open the file in this execution).
 * Requires no fds have been opened yet.
 *)
DoSkipOpen ==
    /\ opener_phase = "init"
    /\ open_count = 0
    /\ opener_phase' = "done"
    /\ UNCHANGED <<nlink, open_count, is_orphan, reclaimed, unlinker_phase>>

(*
 * Close: OpenerClient sends CLOSE RPC to MDS (normal file close).
 * Effect: MDS decrements open_count via mdt_mfd_close.
 *   If is_orphan AND open_count drops to 0: reclaim the inode.
 *   (mdd_close(): mdd_orphan_delete() + mdo_destroy() on last close,
 *    mdd_object.c:3956-4017)
 *   Stays in "open" while more fds remain; moves to "done" on last close.
 *)
DoClose ==
    /\ opener_phase = "open"
    /\ open_count > 0
    /\ open_count' = open_count - 1
    /\ IF open_count = 1
       THEN /\ opener_phase' = "done"
            /\ IF is_orphan THEN reclaimed' = TRUE ELSE reclaimed' = reclaimed
       ELSE /\ opener_phase' = "open"
            /\ reclaimed' = reclaimed
    /\ UNCHANGED <<nlink, is_orphan, unlinker_phase>>

(*
 * ClientDisconnect: OpenerClient is evicted (network partition, crash).
 * MDS recovery path: closes ALL open file descriptors from that client
 * atomically (mdt_export_cleanup(), mdt_handler.c:7360-7443, drains
 * med_open_head calling mdt_mfd_close() -> mdd_close() per mfd).
 * If is_orphan: all fds gone -> reclaim now.  (Not modeled: on failover
 * umount the close carries MDS_KEEP_ORPHAN and the orphan is retained.)
 *)
DoDisconnect ==
    /\ opener_phase = "open"
    /\ open_count > 0
    /\ open_count' = 0
    /\ opener_phase' = "done"
    /\ IF is_orphan THEN reclaimed' = TRUE ELSE reclaimed' = reclaimed
    /\ UNCHANGED <<nlink, is_orphan, unlinker_phase>>

(*
 * Unlink: UnlinkerClient removes a directory entry (mdt_reint_unlink).
 * Decrements nlink.  When nlink reaches 0:
 *   - open_count > 0: file still in use.
 *       FIXED (InjectBugOrphan=FALSE): set is_orphan flag; defer reclaim.
 *       BUG   (InjectBugOrphan=TRUE ): skip orphan flag; reclaim now.
 *   - open_count = 0: no openers; safe to reclaim immediately.
 * Unlinker stays in "init" to allow multi-link paths (MaxNlink > 1).
 * DoSkipUnlink terminates the unlinker.
 *)
DoUnlink ==
    /\ unlinker_phase = "init"
    /\ nlink > 0
    /\ ~reclaimed
    /\ nlink' = nlink - 1
    /\ unlinker_phase' = "init"
    /\ open_count' = open_count
    /\ opener_phase' = opener_phase
    /\ IF nlink = 1                  (* nlink' = 0 *)
       THEN IF open_count > 0
            THEN IF InjectBugOrphan
                 THEN (* BUG: skip orphan flag -> immediate reclaim -> UAF *)
                      /\ reclaimed' = TRUE
                      /\ is_orphan' = FALSE
                 ELSE (* FIXED: set orphan flag; reclaim deferred to last close *)
                      /\ is_orphan' = TRUE
                      /\ reclaimed' = FALSE
            ELSE (* open_count = 0: safe to reclaim now *)
                 /\ reclaimed' = TRUE
                 /\ is_orphan' = is_orphan
       ELSE (* nlink still > 0: no reclaim decision yet *)
            /\ is_orphan' = is_orphan
            /\ reclaimed' = reclaimed

(*
 * SkipUnlink: UnlinkerClient stops without further unlinks.
 * This is the only way for unlinker to transition to "done".
 * (Available at any point when unlinker_phase = "init".)
 *)
DoSkipUnlink ==
    /\ unlinker_phase = "init"
    /\ unlinker_phase' = "done"
    /\ UNCHANGED <<nlink, open_count, is_orphan, reclaimed, opener_phase>>

(* ================================================================
 * Next-state relation
 * ================================================================ *)

(* Allow infinite stuttering at terminal state to prevent deadlock detection. *)
Terminating ==
    /\ opener_phase = "done"
    /\ unlinker_phase = "done"
    /\ UNCHANGED vars

Next ==
    \/ DoOpen
    \/ DoCommitOpen
    \/ DoClose
    \/ DoDisconnect
    \/ DoSkipOpen
    \/ DoUnlink
    \/ DoSkipUnlink
    \/ Terminating

(* ================================================================
 * Specification
 * Safety only (no liveness): TLC explores all reachable states.
 * ================================================================ *)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

(* ================================================================
 * Invariants
 * ================================================================ *)

(*
 * ReclamationSafety: inode must not be reclaimed while any client
 * still has it open.  Violation = use-after-free.
 *
 * This is the primary property under test.  InjectBugOrphan=TRUE
 * creates a counterexample; InjectBugOrphan=FALSE preserves it.
 *)
ReclamationSafety == reclaimed => open_count = 0

(*
 * OrphanConsistency: reclaim is only legal after all links are gone.
 *)
OrphanConsistency == reclaimed => nlink = 0

(*
 * OrphanFlagCorrect: orphan flag is set iff nlink=0 with open_count>0
 * at time of last unlink (structural sanity).
 *)
OrphanFlagCorrect ==
    is_orphan => nlink = 0

(*
 * AllSafety: all three invariants bundled.
 *)
AllSafety ==
    /\ TypeOK
    /\ ReclamationSafety
    /\ OrphanConsistency
    /\ OrphanFlagCorrect

(* ================================================================
 * Liveness / termination
 * ================================================================ *)

AllDone == opener_phase = "done" /\ unlinker_phase = "done"

Termination == <>AllDone

=============================================================================
\* Modification History
\* Last modified 2026-03-13 for bead lustre-design-docs-at9.20
\* Created 2026-03-13 for bead lustre-design-docs-09r
