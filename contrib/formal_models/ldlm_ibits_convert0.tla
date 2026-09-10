---------------------------- MODULE ldlm_ibits_convert0 ----------------------------
(*
 * Model: LDLM IBITS lock conversion race - lr_lock drop/reacquire window
 *
 * Models the lr_lock drop/reacquire window of the CLIENT-side convert
 * ldlm_cli_inodebits_convert (ldlm_inodebits.c:501-603, window at
 * 556-560), where the converter drops lr_lock during the callback
 * sequence:
 *   1. Acquire lr_lock, check lock state
 *   2. DROP lr_lock for is_lock_converted() wait + blocking_ast execution
 *   3. Reacquire lr_lock
 *   4. Continue conversion (drop bits)
 *
 * NOTE (validation 2026-09-10): earlier revisions of this header named
 * the function ldlm_handle_convert0.  That is the SERVER-side handler
 * (ldlm_lockd.c:1625-1708); it holds lr_lock from 1657 through the
 * ldlm_inodebits_drop at 1687 to the unlock at 1690 and has no
 * drop/reacquire window and no blocking_ast call.  The sequence above,
 * and the line range 556-560, are ldlm_cli_inodebits_convert:
 * is_lock_converted wait 515-521, ldlm_set_converting 549, unlock 556,
 * blocking_ast 557, ldlm_cli_convert_req 559, relock 560, post-relock
 * checks ldlm_is_failed 569 (LU-17278) and ldlm_is_canceling 575
 * (LU-17415), ldlm_inodebits_drop 579.  The model's fl_CANCEL /
 * fl_DESTROYED are stand-ins for those CANCELING / FAILED checks; the
 * CV_InitCheck early abort corresponds to ldlm_is_canceling at 528.
 *
 * Race window (steps 2-3): A concurrent cancel or destroy can acquire
 * lr_lock and set LDLM_FL_CANCEL or LDLM_FL_DESTROYED.  The convert
 * handler must check these flags after reacquiring lr_lock before
 * modifying the lock bits.
 *
 * Bug injection (original):
 *   InjectBugNoPostCheck = TRUE: skip post-relock flag check, allowing
 *     convert to corrupt a cancelled or destroyed lock.
 *
 * ==========================================================================
 * Extension 1 (ns_lock ordering): ldlm_handle_convert outer wrapper
 * ==========================================================================
 * CORRECTED MODEL (bead lustre-design-docs-nhu, 2026-03-12):
 * ConvertHandler now correctly uses ONLY lr_lock, matching real source code.
 * ldlm_handle_convert0() acquires only lr_lock; it is called without any
 * outer ns_lock held.  The ns_lock acquisition modeled here previously was
 * hypothetical and has been removed from ConvertHandler.
 *
 * NsLockCancelPath is retained as a guard-rail: it models the cancel path
 * that acquires lr_lock -> ns_lock (real order) or ns_lock -> lr_lock (bug),
 * and verifies that neither creates a deadlock with the corrected
 * ConvertHandler.  Since ConvertHandler never holds ns_lock, no ABBA can
 * form regardless of which order NsLockCancelPath uses.
 *
 * Enable NsLockCancelPath with: EnableNsLock = TRUE
 * Bug:         InjectBugNsLockInversion = TRUE (cancel takes ns->lr, inverted)
 * Invariant:   NoDeadlock (= ConvertHandler must never hold ns_lock)
 *
 * --------------------------------------------------------------------------
 * Investigation result (bead lustre-design-docs-95a, 2026-03-12):
 * --------------------------------------------------------------------------
 * Source code examined: lustre/ldlm/ldlm_lockd.c, ldlm_lock.c,
 *   ldlm_inodebits.c, ldlm_request.c (master branch, 2026-03-12).
 *
 * Finding: The ns_lock -> lr_lock ordering modeled in ConvertHandler was
 * HYPOTHETICAL - it does not correspond to the current source code.
 *
 * (a) There is no outer ldlm_handle_convert() wrapper.  ldlm_handle_convert0()
 *     is called directly from ldlm_lockd.c (callback dispatch, LDLM_CONVERT
 *     opcode) and tgt_handler.c (tgt_convert()), neither of which holds
 *     ns_lock.  ldlm_handle_convert0() itself only acquires lr_lock.
 *
 * (b) The cancel paths use a consistent lr_lock -> ns_lock ordering:
 *     - ldlm_lock_cancel(): acquires lr_lock, then ns_lock (via
 *       ldlm_lock_destroy_nolock -> ldlm_lock_remove_from_lru) for client
 *       locks (LDLM_FL_NS_SRV clear); server locks skip LRU, no ns_lock.
 *     - ldlm_cli_inodebits_convert(): called with lr_lock held, drops it,
 *       reacquires it, then acquires ns_lock (lr_lock -> ns_lock).
 *
 * (c) The LRU shrink path (ldlm_prepare_lru_list) releases ns_lock before
 *     acquiring lr_lock - no nesting in that direction either.
 *
 * (d) Cross-referenced with ldlm_lock_order_audit.tla: no real race paths
 *     involving ns_lock exist for the server-side convert handler.  No new
 *     bug injection added for Extension 1.
 *
 * Fix: ConvertHandler CV_NsLock/CV_NsUnlock are now true no-ops.  The model
 * enforces via NoDeadlock that ns_lock is never acquired by ConvertHandler.
 * --------------------------------------------------------------------------
 *
 * ==========================================================================
 * Extension 2 (downgrade race): DowngradeHandler
 * ==========================================================================
 * The downgrade path acquires lr_lock, drops some ibits (e.g., LOOKUP),
 * releases lr_lock, then fires a blocking_ast.  If the downgrade bit-drop
 * races with an in-flight convert (convert has dropped lr_lock for its own
 * blocking_ast), the lock enters a partially-converted state: bits are
 * dropped by two independent paths, and a BL AST fired by downgrade sees
 * a lock that is concurrently being converted.
 *
 * Enable with: EnableDowngradeRace = TRUE
 * Bug:         InjectBugDowngradeNoCheck = TRUE (downgrade ignores window)
 * Fix:         InjectBugDowngradeNoCheck = FALSE (downgrade awaits ~callback)
 * Invariants:  NoCancelledBitDrop (unchanged), NoPartialDowngradeAccess (new)
 *
 * ==========================================================================
 * Extension 3 (reprocess race): ReprocessHandler
 * ==========================================================================
 * ldlm_reprocess_queue can wake up and evaluate the converting lock as a
 * grant candidate while ConvertHandler holds lr_lock dropped (callback
 * window open, callback_running = TRUE).  Reprocess seeing and granting
 * a mid-convert lock violates convert's assumption of exclusive access.
 *
 * Enable with: EnableReprocessRace = TRUE
 * Bug:         InjectBugReprocessNoCheck = TRUE (reprocess ignores window)
 * Fix:         InjectBugReprocessNoCheck = FALSE (reprocess awaits ~callback)
 * Invariant:   NoReprocessMidConvertGrant
 *
 * ==========================================================================
 * Extension 4 (glimpse callback race): GlimpseHandler
 * ==========================================================================
 * KNOWN RACE -- ALREADY MITIGATED IN LUSTRE CODE (2026-03-13 correction):
 *
 * The server sends a glimpse AST to the lock holder (e.g., to get file
 * size for a conflicting open).  The model captures a simplified version
 * of the locking pattern:
 *   1. Acquire lr_lock, verify lock is alive
 *   2. DROP lr_lock, send glimpse RPC (race window opens)
 *   3. Glimpse reply arrives, reacquire lr_lock
 *   4. Process glimpse reply data
 *
 * Race window (steps 2-3): a concurrent cancel can set fl_CANCEL while
 * the glimpse RPC is in flight.
 *
 * CODE REALITY vs MODEL:
 *   - In the real code (ofd_intent_policy, ofd_dlm.c:176-335), lr_lock
 *     is dropped at line 306 BEFORE ldlm_glimpse_locks() (319), and the
 *     reply handler (ldlm_cb_interpret, ldlm_lockd.c:758-814) never reacquires
 *     lr_lock in the same context.  The model's acquire/drop/reacquire
 *     pattern is a simplification.
 *   - The lock struct is protected by reference counting (ldlm_lock_get
 *     in ldlm_ast_fini, ldlm_lockd.c:839) -- no use-after-free.
 *   - The reply IS processed without checking fl_CANCEL, but the code
 *     uses increase_only semantics (ofd_lvb.c:257) and a disk fallback
 *     (ofd_lvb.c:290 disk_update, 303) as safety nets.
 *   - The Lustre developers document this race explicitly in ofd_lvb.c
 *     lines 173-186, and test it in sanityn.sh test_105 ("Glimpse and
 *     lock cancel race").
 *
 * CONCLUSION: The race exists but is a known, intentionally tolerated
 * design trade-off with adequate mitigations (refcounting, increase_only
 * LVB updates, disk fallback).  No JIRA ticket needed.
 *
 * The model remains useful as formal documentation of the race window and
 * the invariant that would be violated without mitigations.
 *
 * Enable with: EnableGlimpseRace = TRUE
 * Bug:         InjectBugGlimpseNoCheck = TRUE (process reply regardless)
 * Fix:         InjectBugGlimpseNoCheck = FALSE (check lock state first)
 * Invariant:   NoStaleGlimpse
 *
 * Safety invariants:
 *   NoCancelledBitDrop: convert must not modify bits after fl_CANCEL/fl_DESTROYED.
 *   NoDeadlock: no state where convert holds ns_lock awaiting lr_lock while
 *     cancel holds lr_lock awaiting ns_lock.
 *   NoPartialDowngradeAccess: downgrade must not drop bits during convert
 *     callback window (callback_running = TRUE).
 *   NoReprocessMidConvertGrant: reprocess must not grant a mid-convert lock.
 *   NoStaleGlimpse: server must not process glimpse reply on canceled lock.
 *   TypeOK: type correctness for all variables.
 *
 * NOTE: Parallel converters (LU-11276) are modeled separately in
 * ldlm_convert.tla (bead 1s5.9, closed) -- not duplicated here.
 *
 * Validated against: lustre-release master 47638add78 (2026-09-06)
 * Validation notes: header function name corrected (see NOTE at the
 * top: the modeled window is ldlm_cli_inodebits_convert, client side);
 * Extension 4 line refs refreshed.  Model semantics left unchanged.
 * DISCREPANCY-OPEN: Extensions 2 and 3 race server-only actors
 * against that client-side window.  ldlm_lock_mode_downgrade
 * (ldlm_lock.c:2711-2750) is compiled only under
 * CONFIG_LUSTRE_FS_SERVER, and __ldlm_reprocess_all
 * (ldlm_lock.c:2383-2398) returns immediately for client namespaces,
 * so neither can run against ldlm_cli_inodebits_convert in the real
 * code, and their modeled "fix" (await ~callback_running) has no
 * source counterpart.  The server-side ldlm_handle_convert0 never
 * drops lr_lock, so there is no window for them there either.
 * Extension 4 (glimpse) is documented above as a simplification.
 *)

EXTENDS Integers, FiniteSets, TLC

CONSTANTS
    InjectBugNoPostCheck,       \* TRUE = skip post-relock flag check (original bug)
    EnableNsLock,               \* TRUE = model outer ns_lock acquisition
    InjectBugNsLockInversion,   \* TRUE = cancel takes lr_lock->ns_lock (inverted)
    EnableDowngradeRace,        \* TRUE = add DowngradeHandler
    InjectBugDowngradeNoCheck,  \* TRUE = downgrade ignores callback window
    EnableReprocessRace,        \* TRUE = add ReprocessHandler
    InjectBugReprocessNoCheck,  \* TRUE = reprocess ignores callback window
    EnableGlimpseRace,          \* TRUE = add GlimpseHandler
    InjectBugGlimpseNoCheck     \* TRUE = glimpse ignores cancel during window

\* IBITS bit definitions (as integers for set operations)
LOOKUP == 1
UPDATE == 2
LAYOUT == 4

AllBits == {LOOKUP, UPDATE, LAYOUT}

(* --algorithm ldlm_ibits_convert0

variables
    lr_lock = "free",
    ns_lock = "free",              \* namespace lock (held by outer ldlm_handle_convert)

    \* LDLM lock flags (protected by lr_lock)
    fl_CANCEL = FALSE,
    fl_DESTROYED = FALSE,

    \* IBITS lock state
    lock_bits = {LOOKUP, UPDATE},       \* Current bits held by the lock
    convert_req_bits = {UPDATE},        \* Bits client wants to drop (convert)
    downgrade_drop_bits = {LOOKUP},     \* Bits the downgrade path wants to drop

    \* Race window tracking
    callback_running = FALSE,           \* blocking_ast in flight (lr_lock dropped)

    \* Result and bug-witness tracking
    convert_result = "init",
    bits_modified_while_flagged = FALSE,    \* Witness: convert modified bits w/ flag set
    downgrade_bits_dropped = FALSE,         \* Witness: downgrade raced with convert window
    reprocess_granted_mid_convert = FALSE,  \* Witness: reprocess acted mid-convert
    stale_glimpse_processed = FALSE;        \* Witness: glimpse reply processed on canceled lock

define
    \* ========== SAFETY INVARIANTS ==========

    \* Original: converting a cancelled/destroyed lock must not modify lock bits.
    NoCancelledBitDrop ==
        ~bits_modified_while_flagged

    \* Extension 1: guard that ConvertHandler never holds ns_lock.
    \* In the corrected model ConvertHandler only uses lr_lock, so this
    \* invariant is always satisfied.  It protects against any future
    \* regression that re-introduces ns_lock into ConvertHandler.
    NoDeadlock ==
        ns_lock /= "convert"

    \* Extension 2: downgrade must not modify bits during convert callback window.
    NoPartialDowngradeAccess ==
        ~downgrade_bits_dropped

    \* Extension 3: reprocess must not grant a lock that is mid-convert.
    NoReprocessMidConvertGrant ==
        ~reprocess_granted_mid_convert

    \* Extension 4: server must not process glimpse reply on canceled lock.
    NoStaleGlimpse ==
        ~stale_glimpse_processed

    \* Type correctness
    TypeOK ==
        /\ lock_bits \subseteq AllBits
        /\ convert_req_bits \subseteq AllBits
        /\ downgrade_drop_bits \subseteq AllBits
        /\ fl_CANCEL \in BOOLEAN
        /\ fl_DESTROYED \in BOOLEAN
        /\ callback_running \in BOOLEAN
        /\ bits_modified_while_flagged \in BOOLEAN
        /\ downgrade_bits_dropped \in BOOLEAN
        /\ reprocess_granted_mid_convert \in BOOLEAN
        /\ stale_glimpse_processed \in BOOLEAN
        /\ convert_result \in {"init", "done", "aborted"}
end define;

\* ================================================================
\* ConvertHandler: client converts an IBITS lock (drops cancel_bits)
\* Models: ldlm_cli_inodebits_convert (ldlm_inodebits.c:501-603;
\* lr_lock only -- no outer ns_lock; see header NOTE)
\*
\* Key sequence:
\*   1. Acquire lr_lock (lock_res_and_lock)
\*   2. Initial state check (if already dead, abort early)
\*   3. Drop lr_lock for blocking_ast (race window opens)
\*   4. Run blocking_ast (without lr_lock)
\*   5. Reacquire lr_lock
\*   6. Post-relock check: [BUG: skip | FIX: check CANCEL/DESTROYED]
\*   7. Modify lock bits (drop convert_req_bits)
\*   8. Release lr_lock
\*
\* CV_NsLock / CV_NsUnlock are retained as no-op labels (structural
\* placeholders); they do NOT acquire ns_lock.  Extension 1 guard-rail
\* is enforced via NoDeadlock = (ns_lock /= "convert").
\* ================================================================
fair process ConvertHandler = "convert"
begin
CV_NsLock:
    \* [FIXED] ConvertHandler does NOT acquire ns_lock.
    \* ldlm_handle_convert0() holds only lr_lock in real code.
    skip;

CV_Lock:
    \* Acquire lr_lock (lock_res_and_lock)
    await lr_lock = "free";
    lr_lock := "convert";

CV_InitCheck:
    \* Pre-callback check: if lock already dead, abort immediately.
    if fl_CANCEL \/ fl_DESTROYED then
        convert_result := "aborted";
        goto CV_Done;
    end if;

CV_Unlock:
    \* Drop lr_lock before blocking_ast -- race window opens here.
    lr_lock := "free";
    callback_running := TRUE;

CV_Callback:
    \* blocking_ast runs WITHOUT lr_lock held.
    skip;

CV_CallbackDone:
    callback_running := FALSE;

CV_Relock:
    \* Reacquire lr_lock after blocking_ast completes.
    await lr_lock = "free";
    lr_lock := "convert";

CV_PostCheck:
    \* Post-relock: check if cancel/destroy raced in during window.
    \* BUG (InjectBugNoPostCheck=TRUE): skip this check.
    if ~InjectBugNoPostCheck /\ (fl_CANCEL \/ fl_DESTROYED) then
        convert_result := "aborted";
        goto CV_Done;
    end if;

CV_Update:
    \* Bug witness: record if modifying bits with flags set.
    if fl_CANCEL \/ fl_DESTROYED then
        bits_modified_while_flagged := TRUE;
    end if;
    lock_bits := lock_bits \ convert_req_bits;
    convert_result := "done";

CV_Done:
    lr_lock := "free";

CV_NsUnlock:
    \* [FIXED] ConvertHandler does not hold ns_lock, nothing to release.
    skip;
end process;

\* ================================================================
\* ConcurrentCanceller: concurrent cancel path racing with convert
\* Models: ldlm_lock_cancel acquiring lr_lock during callback window
\* ================================================================
fair process ConcurrentCanceller = "canceller"
begin
CC_Lock:
    await lr_lock = "free";
    lr_lock := "canceller";

CC_Cancel:
    fl_CANCEL := TRUE;

CC_Unlock:
    lr_lock := "free";
end process;

\* ================================================================
\* ConcurrentDestroyer: concurrent destroy path racing with convert
\* Models: lock destroy acquiring lr_lock during callback window
\* ================================================================
fair process ConcurrentDestroyer = "destroyer"
begin
CD_Lock:
    await lr_lock = "free";
    lr_lock := "destroyer";

CD_Destroy:
    fl_DESTROYED := TRUE;

CD_Unlock:
    lr_lock := "free";
end process;

\* ================================================================
\* NsLockCancelPath: cancel path with configurable lock acquisition order.
\* Extension 1: models the deadlock from lock ordering inversion.
\*
\* ConvertHandler acquires ns_lock -> lr_lock.
\* With InjectBugNsLockInversion=TRUE (bug):
\*   This process acquires lr_lock -> ns_lock (inverted).
\*   Deadlock: convert holds ns_lock, waits for lr_lock;
\*             cancel holds lr_lock, waits for ns_lock.
\* With InjectBugNsLockInversion=FALSE (fix):
\*   This process acquires ns_lock -> lr_lock (same as convert).
\*   Both serialize at ns_lock; no circular dependency.
\*
\* With EnableNsLock=FALSE this process is inert.
\* ================================================================
fair process NsLockCancelPath = "ns_cancel"
begin
NCP_FirstLock:
    \* BUG: acquire lr_lock first (inversion)
    \* FIX: acquire ns_lock first (same as convert)
    await ~EnableNsLock \/
          (InjectBugNsLockInversion  /\ lr_lock = "free") \/
          (~InjectBugNsLockInversion /\ ns_lock = "free");
    if EnableNsLock then
        if InjectBugNsLockInversion then
            lr_lock := "ns_cancel";
        else
            ns_lock := "ns_cancel";
        end if;
    end if;

NCP_SecondLock:
    \* BUG: acquire ns_lock second (may deadlock if convert holds it)
    \* FIX: acquire lr_lock second (convert already released it or will)
    await ~EnableNsLock \/
          (InjectBugNsLockInversion  /\ ns_lock = "free") \/
          (~InjectBugNsLockInversion /\ lr_lock = "free");
    if EnableNsLock then
        if InjectBugNsLockInversion then
            ns_lock := "ns_cancel";
        else
            lr_lock := "ns_cancel";
        end if;
    end if;

NCP_Cancel:
    if EnableNsLock then fl_CANCEL := TRUE; end if;

NCP_Release:
    if EnableNsLock then
        ns_lock := "free" || lr_lock := "free";
    end if;
end process;

\* ================================================================
\* DowngradeHandler: drops some ibits before firing blocking_ast.
\* Extension 2: races with convert's lr_lock-free callback window.
\*
\* With InjectBugDowngradeNoCheck=TRUE (bug): drops bits unconditionally,
\*   which may race with the convert callback window.
\* With InjectBugDowngradeNoCheck=FALSE (fix): awaits ~callback_running
\*   before dropping bits, ensuring no race with convert's window.
\*
\* With EnableDowngradeRace=FALSE this process is inert.
\* ================================================================
fair process DowngradeHandler = "downgrade"
begin
DG_Lock:
    \* Acquire lr_lock to inspect and modify lock bits.
    await ~EnableDowngradeRace \/ lr_lock = "free";
    if EnableDowngradeRace then lr_lock := "downgrade"; end if;

DG_ConvertCheck:
    \* FIX: wait until convert is not in the callback window.
    \* BUG (InjectBugDowngradeNoCheck=TRUE): skip this wait.
    await ~EnableDowngradeRace \/
          InjectBugDowngradeNoCheck \/
          ~callback_running;

DG_DropBits:
    \* Drop bits. Record if we raced with the convert callback window.
    if EnableDowngradeRace then
        if callback_running then
            downgrade_bits_dropped := TRUE;
        end if;
        lock_bits := lock_bits \ downgrade_drop_bits;
    end if;

DG_Unlock:
    if EnableDowngradeRace then lr_lock := "free"; end if;
end process;

\* ================================================================
\* ReprocessHandler: ldlm_reprocess_queue evaluates the converting
\* lock as a grant candidate during convert's callback window.
\* Extension 3: models reprocess racing with mid-convert lock.
\*
\* With InjectBugReprocessNoCheck=TRUE (bug): reprocess acts while
\*   callback_running=TRUE, granting a lock that is mid-convert.
\* With InjectBugReprocessNoCheck=FALSE (fix): reprocess awaits
\*   ~callback_running before evaluating the lock.
\*
\* With EnableReprocessRace=FALSE this process is inert.
\* ================================================================
fair process ReprocessHandler = "reprocess"
begin
RP_Lock:
    \* Acquire lr_lock to scan the grant queue.
    await ~EnableReprocessRace \/ lr_lock = "free";
    if EnableReprocessRace then lr_lock := "reprocess"; end if;

RP_ConvertCheck:
    \* FIX: wait until convert is not in the callback window.
    \* BUG (InjectBugReprocessNoCheck=TRUE): skip this wait.
    await ~EnableReprocessRace \/
          InjectBugReprocessNoCheck \/
          ~callback_running;

RP_Eval:
    \* Evaluate lock as grant candidate. Record if mid-convert.
    if EnableReprocessRace then
        if callback_running then
            reprocess_granted_mid_convert := TRUE;
        end if;
    end if;

RP_Unlock:
    if EnableReprocessRace then lr_lock := "free"; end if;
end process;

\* ================================================================
\* GlimpseHandler: server sends glimpse AST, processes reply.
\* Extension 4: races with cancel during glimpse RPC window.
\*
\* NOTE: This is a KNOWN RACE in Lustre, already mitigated via
\* refcounting (ldlm_lock_get), increase_only LVB semantics, and
\* disk fallback.  Documented in ofd_lvb.c:173-186 and tested in
\* sanityn.sh test_105.  See header comment for full details.
\*
\* The model simplifies the real locking pattern (which does not
\* reacquire lr_lock in the reply handler), but correctly captures
\* the core race: cancel can intervene while glimpse RPC is in flight.
\*
\* With InjectBugGlimpseNoCheck=TRUE (bug): process reply regardless
\*   of lock state -- acts on stale glimpse data.
\* With InjectBugGlimpseNoCheck=FALSE (fix): check lock state after
\*   reacquiring lr_lock; discard reply if lock is now canceled.
\*
\* With EnableGlimpseRace=FALSE this process is inert.
\* ================================================================
fair process GlimpseHandler = "glimpse"
begin
GL_Lock:
    \* Acquire lr_lock to send glimpse.
    await ~EnableGlimpseRace \/ lr_lock = "free";
    if EnableGlimpseRace then lr_lock := "glimpse"; end if;

GL_SendGlimpse:
    \* Drop lr_lock, send glimpse RPC.  Race window opens.
    if EnableGlimpseRace then
        lr_lock := "free";
    end if;

GL_Relock:
    \* Glimpse reply received, reacquire lr_lock.
    await ~EnableGlimpseRace \/ lr_lock = "free";
    if EnableGlimpseRace then lr_lock := "glimpse"; end if;

GL_PostCheck:
    \* FIX: check if lock was canceled during glimpse window.
    \* BUG (InjectBugGlimpseNoCheck=TRUE): skip this check.
    if EnableGlimpseRace /\ ~InjectBugGlimpseNoCheck /\ (fl_CANCEL \/ fl_DESTROYED) then
        goto GL_Unlock;
    end if;

GL_ProcessReply:
    \* Process glimpse reply.  Record if lock is now canceled (stale).
    if EnableGlimpseRace then
        if fl_CANCEL \/ fl_DESTROYED then
            stale_glimpse_processed := TRUE;
        end if;
    end if;

GL_Unlock:
    if EnableGlimpseRace then lr_lock := "free"; end if;
end process;

end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "placeholder" /\ chksum(tla) = "placeholder")
VARIABLES lr_lock, ns_lock, fl_CANCEL, fl_DESTROYED, lock_bits,
          convert_req_bits, downgrade_drop_bits, callback_running,
          convert_result, bits_modified_while_flagged, downgrade_bits_dropped,
          reprocess_granted_mid_convert, stale_glimpse_processed, pc

(* define statement *)
NoCancelledBitDrop ==
    ~bits_modified_while_flagged




NoDeadlock ==
    ns_lock /= "convert"


NoPartialDowngradeAccess ==
    ~downgrade_bits_dropped


NoReprocessMidConvertGrant ==
    ~reprocess_granted_mid_convert


NoStaleGlimpse ==
    ~stale_glimpse_processed


TypeOK ==
    /\ lock_bits \subseteq AllBits
    /\ convert_req_bits \subseteq AllBits
    /\ downgrade_drop_bits \subseteq AllBits
    /\ fl_CANCEL \in BOOLEAN
    /\ fl_DESTROYED \in BOOLEAN
    /\ callback_running \in BOOLEAN
    /\ bits_modified_while_flagged \in BOOLEAN
    /\ downgrade_bits_dropped \in BOOLEAN
    /\ reprocess_granted_mid_convert \in BOOLEAN
    /\ stale_glimpse_processed \in BOOLEAN
    /\ convert_result \in {"init", "done", "aborted"}


vars == << lr_lock, ns_lock, fl_CANCEL, fl_DESTROYED, lock_bits,
           convert_req_bits, downgrade_drop_bits, callback_running,
           convert_result, bits_modified_while_flagged,
           downgrade_bits_dropped, reprocess_granted_mid_convert,
           stale_glimpse_processed, pc >>

ProcSet == {"convert"} \cup {"canceller"} \cup {"destroyer"} \cup {"ns_cancel"} \cup {"downgrade"} \cup {"reprocess"} \cup {"glimpse"}

Init == (* Global variables *)
        /\ lr_lock = "free"
        /\ ns_lock = "free"
        /\ fl_CANCEL = FALSE
        /\ fl_DESTROYED = FALSE
        /\ lock_bits = {LOOKUP, UPDATE}
        /\ convert_req_bits = {UPDATE}
        /\ downgrade_drop_bits = {LOOKUP}
        /\ callback_running = FALSE
        /\ convert_result = "init"
        /\ bits_modified_while_flagged = FALSE
        /\ downgrade_bits_dropped = FALSE
        /\ reprocess_granted_mid_convert = FALSE
        /\ stale_glimpse_processed = FALSE
        /\ pc = [self \in ProcSet |-> CASE self = "convert" -> "CV_NsLock"
                                        [] self = "canceller" -> "CC_Lock"
                                        [] self = "destroyer" -> "CD_Lock"
                                        [] self = "ns_cancel" -> "NCP_FirstLock"
                                        [] self = "downgrade" -> "DG_Lock"
                                        [] self = "reprocess" -> "RP_Lock"
                                        [] self = "glimpse" -> "GL_Lock"]

CV_NsLock == /\ pc["convert"] = "CV_NsLock"
             /\ TRUE
             /\ pc' = [pc EXCEPT !["convert"] = "CV_Lock"]
             /\ UNCHANGED << lr_lock, ns_lock, fl_CANCEL, fl_DESTROYED, lock_bits,
                             convert_req_bits, downgrade_drop_bits,
                             callback_running, convert_result,
                             bits_modified_while_flagged,
                             downgrade_bits_dropped,
                             reprocess_granted_mid_convert,
                             stale_glimpse_processed >>

CV_Lock == /\ pc["convert"] = "CV_Lock"
           /\ lr_lock = "free"
           /\ lr_lock' = "convert"
           /\ pc' = [pc EXCEPT !["convert"] = "CV_InitCheck"]
           /\ UNCHANGED << ns_lock, fl_CANCEL, fl_DESTROYED, lock_bits,
                           convert_req_bits, downgrade_drop_bits,
                           callback_running, convert_result,
                           bits_modified_while_flagged, downgrade_bits_dropped,
                           reprocess_granted_mid_convert,
                           stale_glimpse_processed >>

CV_InitCheck == /\ pc["convert"] = "CV_InitCheck"
                /\ IF fl_CANCEL \/ fl_DESTROYED
                      THEN /\ convert_result' = "aborted"
                           /\ pc' = [pc EXCEPT !["convert"] = "CV_Done"]
                      ELSE /\ pc' = [pc EXCEPT !["convert"] = "CV_Unlock"]
                           /\ UNCHANGED convert_result
                /\ UNCHANGED << lr_lock, ns_lock, fl_CANCEL, fl_DESTROYED,
                                lock_bits, convert_req_bits,
                                downgrade_drop_bits, callback_running,
                                bits_modified_while_flagged,
                                downgrade_bits_dropped,
                                reprocess_granted_mid_convert,
                                stale_glimpse_processed >>

CV_Unlock == /\ pc["convert"] = "CV_Unlock"
             /\ lr_lock' = "free"
             /\ callback_running' = TRUE
             /\ pc' = [pc EXCEPT !["convert"] = "CV_Callback"]
             /\ UNCHANGED << ns_lock, fl_CANCEL, fl_DESTROYED, lock_bits,
                             convert_req_bits, downgrade_drop_bits,
                             convert_result, bits_modified_while_flagged,
                             downgrade_bits_dropped,
                             reprocess_granted_mid_convert,
                             stale_glimpse_processed >>

CV_Callback == /\ pc["convert"] = "CV_Callback"
               /\ TRUE
               /\ pc' = [pc EXCEPT !["convert"] = "CV_CallbackDone"]
               /\ UNCHANGED << lr_lock, ns_lock, fl_CANCEL, fl_DESTROYED,
                               lock_bits, convert_req_bits,
                               downgrade_drop_bits, callback_running,
                               convert_result, bits_modified_while_flagged,
                               downgrade_bits_dropped,
                               reprocess_granted_mid_convert,
                               stale_glimpse_processed >>

CV_CallbackDone == /\ pc["convert"] = "CV_CallbackDone"
                   /\ callback_running' = FALSE
                   /\ pc' = [pc EXCEPT !["convert"] = "CV_Relock"]
                   /\ UNCHANGED << lr_lock, ns_lock, fl_CANCEL, fl_DESTROYED,
                                   lock_bits, convert_req_bits,
                                   downgrade_drop_bits, convert_result,
                                   bits_modified_while_flagged,
                                   downgrade_bits_dropped,
                                   reprocess_granted_mid_convert,
                                   stale_glimpse_processed >>

CV_Relock == /\ pc["convert"] = "CV_Relock"
             /\ lr_lock = "free"
             /\ lr_lock' = "convert"
             /\ pc' = [pc EXCEPT !["convert"] = "CV_PostCheck"]
             /\ UNCHANGED << ns_lock, fl_CANCEL, fl_DESTROYED, lock_bits,
                             convert_req_bits, downgrade_drop_bits,
                             callback_running, convert_result,
                             bits_modified_while_flagged,
                             downgrade_bits_dropped,
                             reprocess_granted_mid_convert,
                             stale_glimpse_processed >>

CV_PostCheck == /\ pc["convert"] = "CV_PostCheck"
                /\ IF ~InjectBugNoPostCheck /\ (fl_CANCEL \/ fl_DESTROYED)
                      THEN /\ convert_result' = "aborted"
                           /\ pc' = [pc EXCEPT !["convert"] = "CV_Done"]
                      ELSE /\ pc' = [pc EXCEPT !["convert"] = "CV_Update"]
                           /\ UNCHANGED convert_result
                /\ UNCHANGED << lr_lock, ns_lock, fl_CANCEL, fl_DESTROYED,
                                lock_bits, convert_req_bits,
                                downgrade_drop_bits, callback_running,
                                bits_modified_while_flagged,
                                downgrade_bits_dropped,
                                reprocess_granted_mid_convert,
                                stale_glimpse_processed >>

CV_Update == /\ pc["convert"] = "CV_Update"
             /\ IF fl_CANCEL \/ fl_DESTROYED
                   THEN /\ bits_modified_while_flagged' = TRUE
                   ELSE /\ TRUE
                        /\ UNCHANGED bits_modified_while_flagged
             /\ lock_bits' = lock_bits \ convert_req_bits
             /\ convert_result' = "done"
             /\ pc' = [pc EXCEPT !["convert"] = "CV_Done"]
             /\ UNCHANGED << lr_lock, ns_lock, fl_CANCEL, fl_DESTROYED,
                             convert_req_bits, downgrade_drop_bits,
                             callback_running, downgrade_bits_dropped,
                             reprocess_granted_mid_convert,
                             stale_glimpse_processed >>

CV_Done == /\ pc["convert"] = "CV_Done"
           /\ lr_lock' = "free"
           /\ pc' = [pc EXCEPT !["convert"] = "CV_NsUnlock"]
           /\ UNCHANGED << ns_lock, fl_CANCEL, fl_DESTROYED, lock_bits,
                           convert_req_bits, downgrade_drop_bits,
                           callback_running, convert_result,
                           bits_modified_while_flagged, downgrade_bits_dropped,
                           reprocess_granted_mid_convert,
                           stale_glimpse_processed >>

CV_NsUnlock == /\ pc["convert"] = "CV_NsUnlock"
               /\ TRUE
               /\ pc' = [pc EXCEPT !["convert"] = "Done"]
               /\ UNCHANGED << lr_lock, ns_lock, fl_CANCEL, fl_DESTROYED, lock_bits,
                               convert_req_bits, downgrade_drop_bits,
                               callback_running, convert_result,
                               bits_modified_while_flagged,
                               downgrade_bits_dropped,
                               reprocess_granted_mid_convert,
                               stale_glimpse_processed >>

ConvertHandler == CV_NsLock \/ CV_Lock \/ CV_InitCheck \/ CV_Unlock
                     \/ CV_Callback \/ CV_CallbackDone \/ CV_Relock
                     \/ CV_PostCheck \/ CV_Update \/ CV_Done \/ CV_NsUnlock

CC_Lock == /\ pc["canceller"] = "CC_Lock"
           /\ lr_lock = "free"
           /\ lr_lock' = "canceller"
           /\ pc' = [pc EXCEPT !["canceller"] = "CC_Cancel"]
           /\ UNCHANGED << ns_lock, fl_CANCEL, fl_DESTROYED, lock_bits,
                           convert_req_bits, downgrade_drop_bits,
                           callback_running, convert_result,
                           bits_modified_while_flagged, downgrade_bits_dropped,
                           reprocess_granted_mid_convert,
                           stale_glimpse_processed >>

CC_Cancel == /\ pc["canceller"] = "CC_Cancel"
             /\ fl_CANCEL' = TRUE
             /\ pc' = [pc EXCEPT !["canceller"] = "CC_Unlock"]
             /\ UNCHANGED << lr_lock, ns_lock, fl_DESTROYED, lock_bits,
                             convert_req_bits, downgrade_drop_bits,
                             callback_running, convert_result,
                             bits_modified_while_flagged,
                             downgrade_bits_dropped,
                             reprocess_granted_mid_convert,
                             stale_glimpse_processed >>

CC_Unlock == /\ pc["canceller"] = "CC_Unlock"
             /\ lr_lock' = "free"
             /\ pc' = [pc EXCEPT !["canceller"] = "Done"]
             /\ UNCHANGED << ns_lock, fl_CANCEL, fl_DESTROYED, lock_bits,
                             convert_req_bits, downgrade_drop_bits,
                             callback_running, convert_result,
                             bits_modified_while_flagged,
                             downgrade_bits_dropped,
                             reprocess_granted_mid_convert,
                             stale_glimpse_processed >>

ConcurrentCanceller == CC_Lock \/ CC_Cancel \/ CC_Unlock

CD_Lock == /\ pc["destroyer"] = "CD_Lock"
           /\ lr_lock = "free"
           /\ lr_lock' = "destroyer"
           /\ pc' = [pc EXCEPT !["destroyer"] = "CD_Destroy"]
           /\ UNCHANGED << ns_lock, fl_CANCEL, fl_DESTROYED, lock_bits,
                           convert_req_bits, downgrade_drop_bits,
                           callback_running, convert_result,
                           bits_modified_while_flagged, downgrade_bits_dropped,
                           reprocess_granted_mid_convert,
                           stale_glimpse_processed >>

CD_Destroy == /\ pc["destroyer"] = "CD_Destroy"
              /\ fl_DESTROYED' = TRUE
              /\ pc' = [pc EXCEPT !["destroyer"] = "CD_Unlock"]
              /\ UNCHANGED << lr_lock, ns_lock, fl_CANCEL, lock_bits,
                              convert_req_bits, downgrade_drop_bits,
                              callback_running, convert_result,
                              bits_modified_while_flagged,
                              downgrade_bits_dropped,
                              reprocess_granted_mid_convert,
                              stale_glimpse_processed >>

CD_Unlock == /\ pc["destroyer"] = "CD_Unlock"
             /\ lr_lock' = "free"
             /\ pc' = [pc EXCEPT !["destroyer"] = "Done"]
             /\ UNCHANGED << ns_lock, fl_CANCEL, fl_DESTROYED, lock_bits,
                             convert_req_bits, downgrade_drop_bits,
                             callback_running, convert_result,
                             bits_modified_while_flagged,
                             downgrade_bits_dropped,
                             reprocess_granted_mid_convert,
                             stale_glimpse_processed >>

ConcurrentDestroyer == CD_Lock \/ CD_Destroy \/ CD_Unlock

NCP_FirstLock == /\ pc["ns_cancel"] = "NCP_FirstLock"
                 /\ ~EnableNsLock \/
                    (InjectBugNsLockInversion  /\ lr_lock = "free") \/
                    (~InjectBugNsLockInversion /\ ns_lock = "free")
                 /\ IF EnableNsLock
                       THEN /\ IF InjectBugNsLockInversion
                                  THEN /\ lr_lock' = "ns_cancel"
                                       /\ UNCHANGED ns_lock
                                  ELSE /\ ns_lock' = "ns_cancel"
                                       /\ UNCHANGED lr_lock
                       ELSE /\ TRUE
                            /\ UNCHANGED << lr_lock, ns_lock >>
                 /\ pc' = [pc EXCEPT !["ns_cancel"] = "NCP_SecondLock"]
                 /\ UNCHANGED << fl_CANCEL, fl_DESTROYED, lock_bits,
                                 convert_req_bits, downgrade_drop_bits,
                                 callback_running, convert_result,
                                 bits_modified_while_flagged,
                                 downgrade_bits_dropped,
                                 reprocess_granted_mid_convert,
                                 stale_glimpse_processed >>

NCP_SecondLock == /\ pc["ns_cancel"] = "NCP_SecondLock"
                  /\ ~EnableNsLock \/
                     (InjectBugNsLockInversion  /\ ns_lock = "free") \/
                     (~InjectBugNsLockInversion /\ lr_lock = "free")
                  /\ IF EnableNsLock
                        THEN /\ IF InjectBugNsLockInversion
                                   THEN /\ ns_lock' = "ns_cancel"
                                        /\ UNCHANGED lr_lock
                                   ELSE /\ lr_lock' = "ns_cancel"
                                        /\ UNCHANGED ns_lock
                        ELSE /\ TRUE
                             /\ UNCHANGED << lr_lock, ns_lock >>
                  /\ pc' = [pc EXCEPT !["ns_cancel"] = "NCP_Cancel"]
                  /\ UNCHANGED << fl_CANCEL, fl_DESTROYED, lock_bits,
                                  convert_req_bits, downgrade_drop_bits,
                                  callback_running, convert_result,
                                  bits_modified_while_flagged,
                                  downgrade_bits_dropped,
                                  reprocess_granted_mid_convert,
                                  stale_glimpse_processed >>

NCP_Cancel == /\ pc["ns_cancel"] = "NCP_Cancel"
              /\ IF EnableNsLock
                    THEN /\ fl_CANCEL' = TRUE
                    ELSE /\ TRUE
                         /\ UNCHANGED fl_CANCEL
              /\ pc' = [pc EXCEPT !["ns_cancel"] = "NCP_Release"]
              /\ UNCHANGED << lr_lock, ns_lock, fl_DESTROYED, lock_bits,
                              convert_req_bits, downgrade_drop_bits,
                              callback_running, convert_result,
                              bits_modified_while_flagged,
                              downgrade_bits_dropped,
                              reprocess_granted_mid_convert,
                              stale_glimpse_processed >>

NCP_Release == /\ pc["ns_cancel"] = "NCP_Release"
               /\ IF EnableNsLock
                     THEN /\ /\ lr_lock' = "free"
                             /\ ns_lock' = "free"
                     ELSE /\ TRUE
                          /\ UNCHANGED << lr_lock, ns_lock >>
               /\ pc' = [pc EXCEPT !["ns_cancel"] = "Done"]
               /\ UNCHANGED << fl_CANCEL, fl_DESTROYED, lock_bits,
                               convert_req_bits, downgrade_drop_bits,
                               callback_running, convert_result,
                               bits_modified_while_flagged,
                               downgrade_bits_dropped,
                               reprocess_granted_mid_convert,
                               stale_glimpse_processed >>

NsLockCancelPath == NCP_FirstLock \/ NCP_SecondLock \/ NCP_Cancel
                       \/ NCP_Release

DG_Lock == /\ pc["downgrade"] = "DG_Lock"
           /\ ~EnableDowngradeRace \/ lr_lock = "free"
           /\ IF EnableDowngradeRace
                 THEN /\ lr_lock' = "downgrade"
                 ELSE /\ TRUE
                      /\ UNCHANGED lr_lock
           /\ pc' = [pc EXCEPT !["downgrade"] = "DG_ConvertCheck"]
           /\ UNCHANGED << ns_lock, fl_CANCEL, fl_DESTROYED, lock_bits,
                           convert_req_bits, downgrade_drop_bits,
                           callback_running, convert_result,
                           bits_modified_while_flagged, downgrade_bits_dropped,
                           reprocess_granted_mid_convert,
                           stale_glimpse_processed >>

DG_ConvertCheck == /\ pc["downgrade"] = "DG_ConvertCheck"
                   /\ ~EnableDowngradeRace \/
                      InjectBugDowngradeNoCheck \/
                      ~callback_running
                   /\ pc' = [pc EXCEPT !["downgrade"] = "DG_DropBits"]
                   /\ UNCHANGED << lr_lock, ns_lock, fl_CANCEL, fl_DESTROYED,
                                   lock_bits, convert_req_bits,
                                   downgrade_drop_bits, callback_running,
                                   convert_result, bits_modified_while_flagged,
                                   downgrade_bits_dropped,
                                   reprocess_granted_mid_convert,
                                   stale_glimpse_processed >>

DG_DropBits == /\ pc["downgrade"] = "DG_DropBits"
               /\ IF EnableDowngradeRace
                     THEN /\ IF callback_running
                                THEN /\ downgrade_bits_dropped' = TRUE
                                ELSE /\ TRUE
                                     /\ UNCHANGED downgrade_bits_dropped
                          /\ lock_bits' = lock_bits \ downgrade_drop_bits
                     ELSE /\ TRUE
                          /\ UNCHANGED << lock_bits, downgrade_bits_dropped >>
               /\ pc' = [pc EXCEPT !["downgrade"] = "DG_Unlock"]
               /\ UNCHANGED << lr_lock, ns_lock, fl_CANCEL, fl_DESTROYED,
                               convert_req_bits, downgrade_drop_bits,
                               callback_running, convert_result,
                               bits_modified_while_flagged,
                               reprocess_granted_mid_convert,
                               stale_glimpse_processed >>

DG_Unlock == /\ pc["downgrade"] = "DG_Unlock"
             /\ IF EnableDowngradeRace
                   THEN /\ lr_lock' = "free"
                   ELSE /\ TRUE
                        /\ UNCHANGED lr_lock
             /\ pc' = [pc EXCEPT !["downgrade"] = "Done"]
             /\ UNCHANGED << ns_lock, fl_CANCEL, fl_DESTROYED, lock_bits,
                             convert_req_bits, downgrade_drop_bits,
                             callback_running, convert_result,
                             bits_modified_while_flagged,
                             downgrade_bits_dropped,
                             reprocess_granted_mid_convert,
                             stale_glimpse_processed >>

DowngradeHandler == DG_Lock \/ DG_ConvertCheck \/ DG_DropBits \/ DG_Unlock

RP_Lock == /\ pc["reprocess"] = "RP_Lock"
           /\ ~EnableReprocessRace \/ lr_lock = "free"
           /\ IF EnableReprocessRace
                 THEN /\ lr_lock' = "reprocess"
                 ELSE /\ TRUE
                      /\ UNCHANGED lr_lock
           /\ pc' = [pc EXCEPT !["reprocess"] = "RP_ConvertCheck"]
           /\ UNCHANGED << ns_lock, fl_CANCEL, fl_DESTROYED, lock_bits,
                           convert_req_bits, downgrade_drop_bits,
                           callback_running, convert_result,
                           bits_modified_while_flagged, downgrade_bits_dropped,
                           reprocess_granted_mid_convert,
                           stale_glimpse_processed >>

RP_ConvertCheck == /\ pc["reprocess"] = "RP_ConvertCheck"
                   /\ ~EnableReprocessRace \/
                      InjectBugReprocessNoCheck \/
                      ~callback_running
                   /\ pc' = [pc EXCEPT !["reprocess"] = "RP_Eval"]
                   /\ UNCHANGED << lr_lock, ns_lock, fl_CANCEL, fl_DESTROYED,
                                   lock_bits, convert_req_bits,
                                   downgrade_drop_bits, callback_running,
                                   convert_result, bits_modified_while_flagged,
                                   downgrade_bits_dropped,
                                   reprocess_granted_mid_convert,
                                   stale_glimpse_processed >>

RP_Eval == /\ pc["reprocess"] = "RP_Eval"
           /\ IF EnableReprocessRace
                 THEN /\ IF callback_running
                            THEN /\ reprocess_granted_mid_convert' = TRUE
                            ELSE /\ TRUE
                                 /\ UNCHANGED reprocess_granted_mid_convert
                 ELSE /\ TRUE
                      /\ UNCHANGED reprocess_granted_mid_convert
           /\ pc' = [pc EXCEPT !["reprocess"] = "RP_Unlock"]
           /\ UNCHANGED << lr_lock, ns_lock, fl_CANCEL, fl_DESTROYED,
                           lock_bits, convert_req_bits, downgrade_drop_bits,
                           callback_running, convert_result,
                           bits_modified_while_flagged, downgrade_bits_dropped,
                           stale_glimpse_processed >>

RP_Unlock == /\ pc["reprocess"] = "RP_Unlock"
             /\ IF EnableReprocessRace
                   THEN /\ lr_lock' = "free"
                   ELSE /\ TRUE
                        /\ UNCHANGED lr_lock
             /\ pc' = [pc EXCEPT !["reprocess"] = "Done"]
             /\ UNCHANGED << ns_lock, fl_CANCEL, fl_DESTROYED, lock_bits,
                             convert_req_bits, downgrade_drop_bits,
                             callback_running, convert_result,
                             bits_modified_while_flagged,
                             downgrade_bits_dropped,
                             reprocess_granted_mid_convert,
                             stale_glimpse_processed >>

ReprocessHandler == RP_Lock \/ RP_ConvertCheck \/ RP_Eval \/ RP_Unlock

GL_Lock == /\ pc["glimpse"] = "GL_Lock"
           /\ ~EnableGlimpseRace \/ lr_lock = "free"
           /\ IF EnableGlimpseRace
                 THEN /\ lr_lock' = "glimpse"
                 ELSE /\ TRUE
                      /\ UNCHANGED lr_lock
           /\ pc' = [pc EXCEPT !["glimpse"] = "GL_SendGlimpse"]
           /\ UNCHANGED << ns_lock, fl_CANCEL, fl_DESTROYED, lock_bits,
                           convert_req_bits, downgrade_drop_bits,
                           callback_running, convert_result,
                           bits_modified_while_flagged, downgrade_bits_dropped,
                           reprocess_granted_mid_convert,
                           stale_glimpse_processed >>

GL_SendGlimpse == /\ pc["glimpse"] = "GL_SendGlimpse"
                  /\ IF EnableGlimpseRace
                        THEN /\ lr_lock' = "free"
                        ELSE /\ TRUE
                             /\ UNCHANGED lr_lock
                  /\ pc' = [pc EXCEPT !["glimpse"] = "GL_Relock"]
                  /\ UNCHANGED << ns_lock, fl_CANCEL, fl_DESTROYED, lock_bits,
                                  convert_req_bits, downgrade_drop_bits,
                                  callback_running, convert_result,
                                  bits_modified_while_flagged,
                                  downgrade_bits_dropped,
                                  reprocess_granted_mid_convert,
                                  stale_glimpse_processed >>

GL_Relock == /\ pc["glimpse"] = "GL_Relock"
             /\ ~EnableGlimpseRace \/ lr_lock = "free"
             /\ IF EnableGlimpseRace
                   THEN /\ lr_lock' = "glimpse"
                   ELSE /\ TRUE
                        /\ UNCHANGED lr_lock
             /\ pc' = [pc EXCEPT !["glimpse"] = "GL_PostCheck"]
             /\ UNCHANGED << ns_lock, fl_CANCEL, fl_DESTROYED, lock_bits,
                             convert_req_bits, downgrade_drop_bits,
                             callback_running, convert_result,
                             bits_modified_while_flagged,
                             downgrade_bits_dropped,
                             reprocess_granted_mid_convert,
                             stale_glimpse_processed >>

GL_PostCheck == /\ pc["glimpse"] = "GL_PostCheck"
                /\ IF EnableGlimpseRace /\ ~InjectBugGlimpseNoCheck /\ (fl_CANCEL \/ fl_DESTROYED)
                      THEN /\ pc' = [pc EXCEPT !["glimpse"] = "GL_Unlock"]
                      ELSE /\ pc' = [pc EXCEPT !["glimpse"] = "GL_ProcessReply"]
                /\ UNCHANGED << lr_lock, ns_lock, fl_CANCEL, fl_DESTROYED,
                                lock_bits, convert_req_bits,
                                downgrade_drop_bits, callback_running,
                                convert_result, bits_modified_while_flagged,
                                downgrade_bits_dropped,
                                reprocess_granted_mid_convert,
                                stale_glimpse_processed >>

GL_ProcessReply == /\ pc["glimpse"] = "GL_ProcessReply"
                   /\ IF EnableGlimpseRace
                         THEN /\ IF fl_CANCEL \/ fl_DESTROYED
                                    THEN /\ stale_glimpse_processed' = TRUE
                                    ELSE /\ TRUE
                                         /\ UNCHANGED stale_glimpse_processed
                         ELSE /\ TRUE
                              /\ UNCHANGED stale_glimpse_processed
                   /\ pc' = [pc EXCEPT !["glimpse"] = "GL_Unlock"]
                   /\ UNCHANGED << lr_lock, ns_lock, fl_CANCEL, fl_DESTROYED,
                                   lock_bits, convert_req_bits,
                                   downgrade_drop_bits, callback_running,
                                   convert_result, bits_modified_while_flagged,
                                   downgrade_bits_dropped,
                                   reprocess_granted_mid_convert >>

GL_Unlock == /\ pc["glimpse"] = "GL_Unlock"
             /\ IF EnableGlimpseRace
                   THEN /\ lr_lock' = "free"
                   ELSE /\ TRUE
                        /\ UNCHANGED lr_lock
             /\ pc' = [pc EXCEPT !["glimpse"] = "Done"]
             /\ UNCHANGED << ns_lock, fl_CANCEL, fl_DESTROYED, lock_bits,
                             convert_req_bits, downgrade_drop_bits,
                             callback_running, convert_result,
                             bits_modified_while_flagged,
                             downgrade_bits_dropped,
                             reprocess_granted_mid_convert,
                             stale_glimpse_processed >>

GlimpseHandler == GL_Lock \/ GL_SendGlimpse \/ GL_Relock
                     \/ GL_PostCheck \/ GL_ProcessReply \/ GL_Unlock

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == ConvertHandler \/ ConcurrentCanceller \/ ConcurrentDestroyer
           \/ NsLockCancelPath \/ DowngradeHandler \/ ReprocessHandler
           \/ GlimpseHandler
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(ConvertHandler)
        /\ WF_vars(ConcurrentCanceller)
        /\ WF_vars(ConcurrentDestroyer)
        /\ WF_vars(NsLockCancelPath)
        /\ WF_vars(DowngradeHandler)
        /\ WF_vars(ReprocessHandler)
        /\ WF_vars(GlimpseHandler)

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

=============================================================================
