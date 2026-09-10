--------------------------- MODULE ldlm_convert ---------------------------
(*
 * Model: LDLM client-side lock convert races (LU-17415, LU-17278, LU-11276)
 *
 * Models three race conditions in ldlm_cli_inodebits_convert() where
 * the client drops lr_lock to execute the blocking_ast callback and
 * send a convert RPC to the server.  During this window, concurrent
 * actors can interfere:
 *
 *   LU-17415: A cancel races in during the convert window and sets
 *             LDLM_FL_CANCELING.  Without a post-reacquire check the
 *             convert proceeds on a cancelled lock.
 *             Fix: check ldlm_is_canceling() after reacquiring lr_lock.
 *
 *   LU-17278: Import invalidation sets LDLM_FL_FAILED during the
 *             convert window, destroying the lock's validity.
 *             Without a post-reacquire check the convert proceeds on
 *             a failed lock.
 *             Fix: check ldlm_is_failed() after reacquiring lr_lock.
 *
 *   LU-11276: A BL_AST arrives during the convert window and
 *             accumulates additional bits into cancel_bits.  The
 *             converter holds a stale snapshot (drop_bits) and misses
 *             the newly-requested drops.
 *             Fix: compare drop_bits with cancel_bits after reacquire;
 *             return -EAGAIN so ldlm_cli_convert() retries.
 *
 * Source (lustre-release master 47638add78):
 *   lustre/ldlm/ldlm_inodebits.c  ldlm_cli_inodebits_convert (lines 501-603)
 *     CV_SetConverting: drop_bits = cancel_bits 535, ldlm_set_converting
 *     549; CV_DropLock/CV_RPC/CV_ReacquireLock: unlock 556, blocking_ast
 *     557, ldlm_cli_convert_req 559, relock 560; CV_CheckFailed:
 *     ldlm_is_failed 569-570; CV_CheckCanceling: ldlm_is_canceling
 *     575-576; CV_UpdateBits: ldlm_inodebits_drop(drop_bits) 579;
 *     CV_CheckBits: cancel_bits re-check -> -EAGAIN 582-583;
 *     CV_Commit: cancel_bits = 0 at full_cancel 598-599,
 *     ldlm_clear_converting 601.
 *   lustre/ldlm/ldlm_request.c    ldlm_cli_convert retry loop (lines 1726-1744;
 *     do { } while (rc == -EAGAIN) 1735-1738)
 *   lustre/ldlm/ldlm_lockd.c      ldlm_bl_desc2lock (lines 1856-1893;
 *     cancel_bits |= 1881-1882, BL_AddBits)
 *   Fix commits: 6c0b676e41 (LU-11276), f3b45a0547 (LU-17278),
 *   1714b65e47 (LU-17415).
 *
 * Validated against: lustre-release master 47638add78 (2026-09-06)
 * Validation notes: the model previously did the cancel_bits re-check
 * (CV_CheckBits) BEFORE dropping the bits (CV_UpdateBits).  In the code
 * ldlm_inodebits_drop(lock, drop_bits) at 579 comes first and the
 * re-check at 582 follows; that has been the order since 6c0b676e41
 * (LU-17415 only moved the CANCELING check above the drop).  The
 * Converter was reordered to drop, re-check, commit, and
 * CancelBitsConsistent now fires at CV_Commit (where cancel_bits is
 * zeroed) instead of at the bit drop.
 *
 * Actors:
 *   Converter     - the thread executing ldlm_cli_inodebits_convert()
 *   Canceller     - concurrent ldlm_cancel setting CANCELING flag
 *   Invalidator   - import invalidation setting FAILED flag
 *   BLASTReceiver - BL_AST callback accumulating cancel_bits
 *
 * Each racing actor is non-deterministically active or inactive
 * (cn_active, iv_active, bl_active \in {TRUE, FALSE}).  TLC explores
 * all 2^3 = 8 combinations of actor presence.
 *)
EXTENDS Integers, FiniteSets, TLC

CONSTANTS InjectBug17415, InjectBug17278, InjectBug11276

\* Inode bit definitions (as integers for set operations)
LOOKUP == 1
UPDATE == 2
LAYOUT == 4

AllBits == {LOOKUP, UPDATE, LAYOUT}

(* --algorithm ldlm_convert

variables
    lr_lock = "free",
    fl_converting = FALSE,
    fl_canceling = FALSE,
    fl_failed = FALSE,
    lock_granted = TRUE,
    \* Lock holds LOOKUP + UPDATE; cancel_bits requests UPDATE be dropped
    lock_bits = {LOOKUP, UPDATE},
    cancel_bits = {UPDATE},
    convert_done = FALSE,
    convert_result = "none";

define
    TypeOK ==
        /\ lr_lock \in {"free", "converter", "canceller", "invalidator", "blast"}
        /\ fl_converting \in BOOLEAN
        /\ fl_canceling \in BOOLEAN
        /\ fl_failed \in BOOLEAN
        /\ lock_granted \in BOOLEAN
        /\ lock_bits \subseteq AllBits
        /\ cancel_bits \subseteq AllBits
        /\ convert_done \in BOOLEAN
        /\ convert_result \in {"none", "ok", "cancelled", "eagain"}

    \* LU-17415: At the point of dropping the bits, CANCELING must be clear
    NoConvertAfterCancel ==
        (pc["converter"] = "CV_UpdateBits") => ~fl_canceling

    \* LU-17278: At the point of dropping the bits, FAILED must be clear
    NoConvertAfterFailed ==
        (pc["converter"] = "CV_UpdateBits") => ~fl_failed

    \* LU-11276: At the point of zeroing cancel_bits (successful return),
    \* drop_bits must match cancel_bits: bits added by a racing BL_AST
    \* during the window would otherwise be discarded without a convert.
    \* Checked at CV_Commit, not CV_UpdateBits, because the code drops
    \* the snapshot bits first and only then re-checks cancel_bits.
    CancelBitsConsistent ==
        (pc["converter"] = "CV_Commit") => (drop_bits = cancel_bits)
end define;

\* ================================================================
\* Converter: executes ldlm_cli_inodebits_convert()
\* Acquires lr_lock, sets CONVERTING, snapshots cancel_bits,
\* drops lr_lock for blocking_ast + RPC, reacquires, checks state.
\* ================================================================
fair process Converter = "converter"
variables drop_bits = {};
begin
    CV_Lock:
        await lr_lock = "free";
        lr_lock := "converter";

    CV_SetConverting:
        \* ldlm_set_converting(lock); drop_bits = cancel_bits
        fl_converting := TRUE;
        drop_bits := cancel_bits;

    CV_DropLock:
        \* unlock_res_and_lock(lock)  --- RACE WINDOW OPENS ---
        lr_lock := "free";

    CV_RPC:
        \* blocking_ast callback + ldlm_cli_convert_req to server
        skip;

    CV_ReacquireLock:
        \* lock_res_and_lock(lock)  --- RACE WINDOW CLOSES ---
        await lr_lock = "free";
        lr_lock := "converter";

    CV_CheckFailed:
        \* LU-17278 fix: if (ldlm_is_failed(lock)) GOTO(full_cancel)
        if ~InjectBug17278 then
            if fl_failed then
                goto CV_FullCancel;
            end if;
        end if;

    CV_CheckCanceling:
        \* LU-17415 fix: if (ldlm_is_canceling(lock)) GOTO(full_cancel)
        if ~InjectBug17415 then
            if fl_canceling then
                goto CV_FullCancel;
            end if;
        end if;

    CV_UpdateBits:
        \* ldlm_inodebits_drop(lock, drop_bits) (ldlm_inodebits.c:579).
        \* The snapshot bits are dropped BEFORE the cancel_bits
        \* re-check below: that has been the order since the LU-11276
        \* fix (6c0b676e41); LU-17415 (1714b65e47) only moved the
        \* CANCELING check above this drop.
        lock_bits := lock_bits \ drop_bits;

    CV_CheckBits:
        \* LU-11276 fix: if (drop_bits != cancel_bits) return -EAGAIN
        \* (ldlm_inodebits.c:582-583).  cancel_bits is left intact on
        \* this path (goto clear_converting), so the ldlm_cli_convert()
        \* retry drops the bits that were added during the window.
        if ~InjectBug11276 then
            if drop_bits /= cancel_bits then
                fl_converting := FALSE;
                convert_result := "eagain";
                lr_lock := "free";
                goto Done;
            end if;
        end if;

    CV_Commit:
        \* Convert succeeds: cancel_bits = 0 (full_cancel label,
        \* ldlm_inodebits.c:598-599), clear CONVERTING (601).
        cancel_bits := {};
        fl_converting := FALSE;
        convert_done := TRUE;
        convert_result := "ok";
        lr_lock := "free";
        goto Done;

    CV_FullCancel:
        \* Cancel the lock entirely (full_cancel label in source)
        lock_granted := FALSE;
        fl_converting := FALSE;
        convert_result := "cancelled";
        lr_lock := "free";
end process;

\* ================================================================
\* Canceller: concurrent cancel sets CANCELING flag (LU-17415)
\* Non-deterministically active or inactive.
\* ================================================================
fair process Canceller = "canceller"
variables cn_active \in {TRUE, FALSE};
begin
    CN_Start:
        if ~cn_active then
            goto Done;
        end if;

    CN_Lock:
        await lr_lock = "free";
        lr_lock := "canceller";

    CN_SetCancel:
        fl_canceling := TRUE;

    CN_Unlock:
        lr_lock := "free";
end process;

\* ================================================================
\* Invalidator: import invalidation sets FAILED flag (LU-17278)
\* Non-deterministically active or inactive.
\* ================================================================
fair process Invalidator = "invalidator"
variables iv_active \in {TRUE, FALSE};
begin
    IV_Start:
        if ~iv_active then
            goto Done;
        end if;

    IV_Lock:
        await lr_lock = "free";
        lr_lock := "invalidator";

    IV_SetFailed:
        fl_failed := TRUE;
        lock_granted := FALSE;

    IV_Unlock:
        lr_lock := "free";
end process;

\* ================================================================
\* BLASTReceiver: BL_AST adds LOOKUP to cancel_bits (LU-11276)
\* Models ldlm_bl_desc2lock accumulating bits under lr_lock.
\* Non-deterministically active or inactive.
\* ================================================================
fair process BLASTReceiver = "blast"
variables bl_active \in {TRUE, FALSE};
begin
    BL_Start:
        if ~bl_active then
            goto Done;
        end if;

    BL_Lock:
        await lr_lock = "free";
        lr_lock := "blast";

    BL_AddBits:
        \* cancel_bits |= new_cancel_bits (LOOKUP)
        cancel_bits := cancel_bits \cup {LOOKUP};

    BL_Unlock:
        lr_lock := "free";
end process;

end algorithm; *)
\* BEGIN TRANSLATION
VARIABLES lr_lock, fl_converting, fl_canceling, fl_failed, lock_granted,
          lock_bits, cancel_bits, convert_done, convert_result, pc,
          drop_bits, cn_active, iv_active, bl_active

(* define statement *)
TypeOK ==
    /\ lr_lock \in {"free", "converter", "canceller", "invalidator", "blast"}
    /\ fl_converting \in BOOLEAN
    /\ fl_canceling \in BOOLEAN
    /\ fl_failed \in BOOLEAN
    /\ lock_granted \in BOOLEAN
    /\ lock_bits \subseteq AllBits
    /\ cancel_bits \subseteq AllBits
    /\ convert_done \in BOOLEAN
    /\ convert_result \in {"none", "ok", "cancelled", "eagain"}

NoConvertAfterCancel ==
    (pc["converter"] = "CV_UpdateBits") => ~fl_canceling

NoConvertAfterFailed ==
    (pc["converter"] = "CV_UpdateBits") => ~fl_failed

CancelBitsConsistent ==
    (pc["converter"] = "CV_Commit") => (drop_bits = cancel_bits)


vars == << lr_lock, fl_converting, fl_canceling, fl_failed, lock_granted,
           lock_bits, cancel_bits, convert_done, convert_result, pc,
           drop_bits, cn_active, iv_active, bl_active >>

ProcSet == {"converter"} \cup {"canceller"} \cup {"invalidator"} \cup {"blast"}

Init == (* Global variables *)
        /\ lr_lock = "free"
        /\ fl_converting = FALSE
        /\ fl_canceling = FALSE
        /\ fl_failed = FALSE
        /\ lock_granted = TRUE
        /\ lock_bits = {LOOKUP, UPDATE}
        /\ cancel_bits = {UPDATE}
        /\ convert_done = FALSE
        /\ convert_result = "none"
        (* Process Converter *)
        /\ drop_bits = {}
        (* Process Canceller *)
        /\ cn_active \in {TRUE, FALSE}
        (* Process Invalidator *)
        /\ iv_active \in {TRUE, FALSE}
        (* Process BLASTReceiver *)
        /\ bl_active \in {TRUE, FALSE}
        /\ pc = [self \in ProcSet |-> CASE self = "converter" -> "CV_Lock"
                                        [] self = "canceller" -> "CN_Start"
                                        [] self = "invalidator" -> "IV_Start"
                                        [] self = "blast" -> "BL_Start"]

\* ---- Converter actions ----

CV_Lock == /\ pc["converter"] = "CV_Lock"
           /\ lr_lock = "free"
           /\ lr_lock' = "converter"
           /\ pc' = [pc EXCEPT !["converter"] = "CV_SetConverting"]
           /\ UNCHANGED << fl_converting, fl_canceling, fl_failed, lock_granted,
                           lock_bits, cancel_bits, convert_done, convert_result,
                           drop_bits, cn_active, iv_active, bl_active >>

CV_SetConverting == /\ pc["converter"] = "CV_SetConverting"
                    /\ fl_converting' = TRUE
                    /\ drop_bits' = cancel_bits
                    /\ pc' = [pc EXCEPT !["converter"] = "CV_DropLock"]
                    /\ UNCHANGED << lr_lock, fl_canceling, fl_failed, lock_granted,
                                    lock_bits, cancel_bits, convert_done,
                                    convert_result, cn_active, iv_active,
                                    bl_active >>

CV_DropLock == /\ pc["converter"] = "CV_DropLock"
               /\ lr_lock' = "free"
               /\ pc' = [pc EXCEPT !["converter"] = "CV_RPC"]
               /\ UNCHANGED << fl_converting, fl_canceling, fl_failed, lock_granted,
                               lock_bits, cancel_bits, convert_done, convert_result,
                               drop_bits, cn_active, iv_active, bl_active >>

CV_RPC == /\ pc["converter"] = "CV_RPC"
          /\ TRUE
          /\ pc' = [pc EXCEPT !["converter"] = "CV_ReacquireLock"]
          /\ UNCHANGED << lr_lock, fl_converting, fl_canceling, fl_failed,
                          lock_granted, lock_bits, cancel_bits, convert_done,
                          convert_result, drop_bits, cn_active, iv_active,
                          bl_active >>

CV_ReacquireLock == /\ pc["converter"] = "CV_ReacquireLock"
                    /\ lr_lock = "free"
                    /\ lr_lock' = "converter"
                    /\ pc' = [pc EXCEPT !["converter"] = "CV_CheckFailed"]
                    /\ UNCHANGED << fl_converting, fl_canceling, fl_failed,
                                    lock_granted, lock_bits, cancel_bits,
                                    convert_done, convert_result, drop_bits,
                                    cn_active, iv_active, bl_active >>

CV_CheckFailed == /\ pc["converter"] = "CV_CheckFailed"
                  /\ IF ~InjectBug17278 /\ fl_failed
                        THEN /\ pc' = [pc EXCEPT !["converter"] = "CV_FullCancel"]
                        ELSE /\ pc' = [pc EXCEPT !["converter"] = "CV_CheckCanceling"]
                  /\ UNCHANGED << lr_lock, fl_converting, fl_canceling, fl_failed,
                                  lock_granted, lock_bits, cancel_bits, convert_done,
                                  convert_result, drop_bits, cn_active, iv_active,
                                  bl_active >>

CV_CheckCanceling == /\ pc["converter"] = "CV_CheckCanceling"
                     /\ IF ~InjectBug17415 /\ fl_canceling
                           THEN /\ pc' = [pc EXCEPT !["converter"] = "CV_FullCancel"]
                           ELSE /\ pc' = [pc EXCEPT !["converter"] = "CV_UpdateBits"]
                     /\ UNCHANGED << lr_lock, fl_converting, fl_canceling, fl_failed,
                                     lock_granted, lock_bits, cancel_bits,
                                     convert_done, convert_result, drop_bits,
                                     cn_active, iv_active, bl_active >>

CV_UpdateBits == /\ pc["converter"] = "CV_UpdateBits"
                 /\ lock_bits' = lock_bits \ drop_bits
                 /\ pc' = [pc EXCEPT !["converter"] = "CV_CheckBits"]
                 /\ UNCHANGED << lr_lock, fl_converting, fl_canceling, fl_failed,
                                 lock_granted, cancel_bits, convert_done,
                                 convert_result, drop_bits, cn_active, iv_active,
                                 bl_active >>

CV_CheckBits == /\ pc["converter"] = "CV_CheckBits"
                /\ IF ~InjectBug11276 /\ drop_bits /= cancel_bits
                      THEN /\ fl_converting' = FALSE
                           /\ convert_result' = "eagain"
                           /\ lr_lock' = "free"
                           /\ pc' = [pc EXCEPT !["converter"] = "Done"]
                      ELSE /\ pc' = [pc EXCEPT !["converter"] = "CV_Commit"]
                           /\ UNCHANGED << fl_converting, convert_result, lr_lock >>
                /\ UNCHANGED << fl_canceling, fl_failed, lock_granted, lock_bits,
                                cancel_bits, convert_done, drop_bits, cn_active,
                                iv_active, bl_active >>

CV_Commit == /\ pc["converter"] = "CV_Commit"
             /\ cancel_bits' = {}
             /\ fl_converting' = FALSE
             /\ convert_done' = TRUE
             /\ convert_result' = "ok"
             /\ lr_lock' = "free"
             /\ pc' = [pc EXCEPT !["converter"] = "Done"]
             /\ UNCHANGED << fl_canceling, fl_failed, lock_granted, lock_bits,
                             drop_bits, cn_active, iv_active, bl_active >>

CV_FullCancel == /\ pc["converter"] = "CV_FullCancel"
                 /\ lock_granted' = FALSE
                 /\ fl_converting' = FALSE
                 /\ convert_result' = "cancelled"
                 /\ lr_lock' = "free"
                 /\ pc' = [pc EXCEPT !["converter"] = "Done"]
                 /\ UNCHANGED << fl_canceling, fl_failed, lock_bits, cancel_bits,
                                 convert_done, drop_bits, cn_active, iv_active,
                                 bl_active >>

Converter == CV_Lock \/ CV_SetConverting \/ CV_DropLock \/ CV_RPC
                \/ CV_ReacquireLock \/ CV_CheckFailed \/ CV_CheckCanceling
                \/ CV_UpdateBits \/ CV_CheckBits \/ CV_Commit \/ CV_FullCancel

\* ---- Canceller actions ----

CN_Start == /\ pc["canceller"] = "CN_Start"
            /\ IF cn_active
                  THEN /\ pc' = [pc EXCEPT !["canceller"] = "CN_Lock"]
                  ELSE /\ pc' = [pc EXCEPT !["canceller"] = "Done"]
            /\ UNCHANGED << lr_lock, fl_converting, fl_canceling, fl_failed,
                            lock_granted, lock_bits, cancel_bits, convert_done,
                            convert_result, drop_bits, cn_active, iv_active,
                            bl_active >>

CN_Lock == /\ pc["canceller"] = "CN_Lock"
           /\ lr_lock = "free"
           /\ lr_lock' = "canceller"
           /\ pc' = [pc EXCEPT !["canceller"] = "CN_SetCancel"]
           /\ UNCHANGED << fl_converting, fl_canceling, fl_failed, lock_granted,
                           lock_bits, cancel_bits, convert_done, convert_result,
                           drop_bits, cn_active, iv_active, bl_active >>

CN_SetCancel == /\ pc["canceller"] = "CN_SetCancel"
                /\ fl_canceling' = TRUE
                /\ pc' = [pc EXCEPT !["canceller"] = "CN_Unlock"]
                /\ UNCHANGED << lr_lock, fl_converting, fl_failed, lock_granted,
                                lock_bits, cancel_bits, convert_done,
                                convert_result, drop_bits, cn_active, iv_active,
                                bl_active >>

CN_Unlock == /\ pc["canceller"] = "CN_Unlock"
             /\ lr_lock' = "free"
             /\ pc' = [pc EXCEPT !["canceller"] = "Done"]
             /\ UNCHANGED << fl_converting, fl_canceling, fl_failed, lock_granted,
                             lock_bits, cancel_bits, convert_done, convert_result,
                             drop_bits, cn_active, iv_active, bl_active >>

Canceller == CN_Start \/ CN_Lock \/ CN_SetCancel \/ CN_Unlock

\* ---- Invalidator actions ----

IV_Start == /\ pc["invalidator"] = "IV_Start"
            /\ IF iv_active
                  THEN /\ pc' = [pc EXCEPT !["invalidator"] = "IV_Lock"]
                  ELSE /\ pc' = [pc EXCEPT !["invalidator"] = "Done"]
            /\ UNCHANGED << lr_lock, fl_converting, fl_canceling, fl_failed,
                            lock_granted, lock_bits, cancel_bits, convert_done,
                            convert_result, drop_bits, cn_active, iv_active,
                            bl_active >>

IV_Lock == /\ pc["invalidator"] = "IV_Lock"
           /\ lr_lock = "free"
           /\ lr_lock' = "invalidator"
           /\ pc' = [pc EXCEPT !["invalidator"] = "IV_SetFailed"]
           /\ UNCHANGED << fl_converting, fl_canceling, fl_failed, lock_granted,
                           lock_bits, cancel_bits, convert_done, convert_result,
                           drop_bits, cn_active, iv_active, bl_active >>

IV_SetFailed == /\ pc["invalidator"] = "IV_SetFailed"
                /\ fl_failed' = TRUE
                /\ lock_granted' = FALSE
                /\ pc' = [pc EXCEPT !["invalidator"] = "IV_Unlock"]
                /\ UNCHANGED << lr_lock, fl_converting, fl_canceling, lock_bits,
                                cancel_bits, convert_done, convert_result,
                                drop_bits, cn_active, iv_active, bl_active >>

IV_Unlock == /\ pc["invalidator"] = "IV_Unlock"
             /\ lr_lock' = "free"
             /\ pc' = [pc EXCEPT !["invalidator"] = "Done"]
             /\ UNCHANGED << fl_converting, fl_canceling, fl_failed, lock_granted,
                             lock_bits, cancel_bits, convert_done, convert_result,
                             drop_bits, cn_active, iv_active, bl_active >>

Invalidator == IV_Start \/ IV_Lock \/ IV_SetFailed \/ IV_Unlock

\* ---- BLASTReceiver actions ----

BL_Start == /\ pc["blast"] = "BL_Start"
            /\ IF bl_active
                  THEN /\ pc' = [pc EXCEPT !["blast"] = "BL_Lock"]
                  ELSE /\ pc' = [pc EXCEPT !["blast"] = "Done"]
            /\ UNCHANGED << lr_lock, fl_converting, fl_canceling, fl_failed,
                            lock_granted, lock_bits, cancel_bits, convert_done,
                            convert_result, drop_bits, cn_active, iv_active,
                            bl_active >>

BL_Lock == /\ pc["blast"] = "BL_Lock"
           /\ lr_lock = "free"
           /\ lr_lock' = "blast"
           /\ pc' = [pc EXCEPT !["blast"] = "BL_AddBits"]
           /\ UNCHANGED << fl_converting, fl_canceling, fl_failed, lock_granted,
                           lock_bits, cancel_bits, convert_done, convert_result,
                           drop_bits, cn_active, iv_active, bl_active >>

BL_AddBits == /\ pc["blast"] = "BL_AddBits"
              /\ cancel_bits' = cancel_bits \cup {LOOKUP}
              /\ pc' = [pc EXCEPT !["blast"] = "BL_Unlock"]
              /\ UNCHANGED << lr_lock, fl_converting, fl_canceling, fl_failed,
                              lock_granted, lock_bits, convert_done,
                              convert_result, drop_bits, cn_active, iv_active,
                              bl_active >>

BL_Unlock == /\ pc["blast"] = "BL_Unlock"
             /\ lr_lock' = "free"
             /\ pc' = [pc EXCEPT !["blast"] = "Done"]
             /\ UNCHANGED << fl_converting, fl_canceling, fl_failed, lock_granted,
                             lock_bits, cancel_bits, convert_done, convert_result,
                             drop_bits, cn_active, iv_active, bl_active >>

BLASTReceiver == BL_Start \/ BL_Lock \/ BL_AddBits \/ BL_Unlock

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == Converter \/ Canceller \/ Invalidator \/ BLASTReceiver
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Converter)
        /\ WF_vars(Canceller)
        /\ WF_vars(Invalidator)
        /\ WF_vars(BLASTReceiver)

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

=============================================================================
