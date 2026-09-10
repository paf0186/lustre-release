---------------------- MODULE ldlm_refcount_cbpending ----------------------
(*
 * Model: LDLM lock reader/writer refcount vs CBPENDING flag
 *
 * Models the race between ldlm_lock_addref_try (ldlm_lock.c:786)
 * and ldlm_lock_decref_internal (ldlm_lock.c:850) with the
 * CBPENDING flag guarding the transition to BL callback and
 * eventual ldlm_lock_cancel.
 *
 * Protocol:
 *   - addref_try: under lock_res_and_lock, checks:
 *       if (readers > 0 || writers > 0 || !CBPENDING):
 *           readers++ (or writers++)
 *       else: return -EAGAIN
 *
 *   - decref_internal: under lock_res_and_lock:
 *       readers-- (or writers--)
 *       if (readers == 0 && writers == 0 && CBPENDING):
 *           trigger BL callback -> eventually cancel
 *
 *   - ldlm_lock_cancel: under lock_res_and_lock:
 *       LBUG if readers > 0 || writers > 0
 *
 * The key safety property (phik's LBUG guard):
 *   ldlm_lock_cancel must never be called when refs > 0.
 *
 * Bug injection:
 *   InjectBugNoEAGAIN: addref_try always succeeds (ignores
 *     CBPENDING check when refs == 0).  This allows a new ref
 *     to be added after the last decref triggered the BL callback
 *     path, causing cancel to see refs > 0 -> LBUG.
 *
 * Modeled scenario:
 *   - Lock starts with 1 reader (initial holder)
 *   - BL_AST arrives -> sets CBPENDING
 *   - Holder decrefs -> triggers BL callback
 *   - Meanwhile, another thread tries addref_try
 *   - Cancel runs after BL callback completes
 *
 * Source (lustre-release master 47638add78):
 *   lustre/ldlm/ldlm_lock.c  ldlm_lock_addref_try (786-804)
 *     AT_Check: under lock_res_and_lock 794-800, -EAGAIN unless
 *     l_readers || l_writers || !CBPENDING 795-796.
 *   lustre/ldlm/ldlm_lock.c  ldlm_lock_decref_internal (850-924)
 *     HD_Lock/AD_Decref: decref 860; HD_Check/AD_Check: last ref with
 *     CBPENDING 877, unlock 891, ldlm_handle_bl_callback directly or
 *     via the bl thread 896-900.
 *   lustre/ldlm/ldlm_lockd.c ldlm_handle_bl_callback (1900-1936)
 *     BL_SetFlag: ldlm_set_cbpending under lock_res_and_lock
 *     1909-1916; blocking_ast only when unreferenced 1915-1924.
 *   lustre/ldlm/ldlm_lock.c  ldlm_lock_cancel (2496-2538)
 *     CN_Lock: LBUG if l_readers || l_writers 2509-2513.
 *
 * Validated against: lustre-release master 47638add78 (2026-09-06)
 *)
EXTENDS Integers, TLC

CONSTANT InjectBugNoEAGAIN

(* --algorithm ldlm_refcount_cbpending

variables
    \* Lock state (protected by lock_res_and_lock)
    readers = 1,       \* Initial holder has one reader ref
    writers = 0,
    cbpending = FALSE, \* Set by BL_AST handler
    cancelled = FALSE, \* Set by ldlm_lock_cancel
    bl_callback_running = FALSE,

    \* Result tracking
    addref_result = "none",  \* "ok", "eagain", or "none"
    lbug_hit = FALSE;        \* TRUE if cancel sees refs > 0

define
    TotalRefs == readers + writers

    \* ========== SAFETY INVARIANTS ==========

    \* The phik LBUG guard: cancel never called with refs
    NoCancelWithRefs ==
        cancelled => (readers = 0 /\ writers = 0)

    \* Equivalent: the LBUG flag should never be set
    NoLBUG == ~lbug_hit

    \* If addref returned ok, refs must be > 0 at that point
    \* (checked locally, not as a global invariant)

    \* CBPENDING must be set before cancel
    CBPendingBeforeCancel ==
        cancelled => cbpending

    TypeOK ==
        /\ readers \in 0..3
        /\ writers \in 0..2
        /\ addref_result \in {"none", "ok", "eagain"}
end define;

\* ================================================================
\* BLASTHandler: Blocking AST arrives, sets CBPENDING
\* Models: server sends BL_AST, client's callback sets the flag
\* Must happen before the holder decrefs (in response to BL_AST)
\* ================================================================
fair process BLASTHandler = "blast_handler"
begin
BL_SetFlag:
    \* In real code: lock_res_and_lock, set CBPENDING,
    \* unlock_res_and_lock.  Atomic.
    cbpending := TRUE;
end process;

\* ================================================================
\* HolderDecref: The original holder releases its reference.
\* This is the decref that potentially triggers the BL callback.
\* Models: ldlm_lock_decref_internal for the lock holder
\* ================================================================
fair process HolderDecref = "holder_decref"
begin
HD_Wait:
    \* Holder decrefs after receiving BL_AST
    await cbpending;

HD_Lock:
    \* lock_res_and_lock
    readers := readers - 1;

HD_Check:
    \* Check if this was the last ref with CBPENDING
    if readers = 0 /\ writers = 0 /\ cbpending then
        \* unlock_res_and_lock, then trigger BL callback
        bl_callback_running := TRUE;
    end if;
    \* unlock_res_and_lock (implicit -- next step can proceed)
end process;

\* ================================================================
\* AddrefThread: Another thread tries ldlm_lock_addref_try.
\* This can run at any time -- before, during, or after the
\* holder's decref.
\*
\* Models: ldlm_lock_addref_try (ldlm_lock.c:786-804)
\* ================================================================
fair process AddrefThread = "addref_thread"
begin
AT_Lock:
    \* lock_res_and_lock
    skip;

AT_Check:
    \* The critical check from ldlm_lock_addref_try:
    \* if (l_readers != 0 || l_writers != 0 || !(l_flags & CBPENDING))
    if InjectBugNoEAGAIN then
        \* BUG: ignore CBPENDING check, always addref
        readers := readers + 1;
        addref_result := "ok";
    elsif readers > 0 \/ writers > 0 \/ ~cbpending then
        \* Normal case: refs exist OR not CBPENDING -> addref ok
        readers := readers + 1;
        addref_result := "ok";
    else
        \* CBPENDING set and no refs -> refuse
        addref_result := "eagain";
    end if;
    \* unlock_res_and_lock
end process;

\* ================================================================
\* AddrefDecref: If addref succeeded, the new ref holder must
\* eventually release it.
\* ================================================================
fair process AddrefDecref = "addref_decref"
begin
AD_Wait:
    await addref_result = "ok";

AD_Decref:
    \* lock_res_and_lock
    readers := readers - 1;

AD_Check:
    \* Check BL callback trigger
    if readers = 0 /\ writers = 0 /\ cbpending /\ ~bl_callback_running then
        bl_callback_running := TRUE;
    end if;
    \* unlock_res_and_lock
end process;

\* ================================================================
\* CancelThread: Runs after BL callback completes.
\* Models: ldlm_lock_cancel (ldlm_lock.c:2496-2538)
\* ================================================================
fair process CancelThread = "cancel_thread"
begin
CN_Wait:
    \* Cancel runs after BL callback path completes
    await bl_callback_running;

CN_Lock:
    \* lock_res_and_lock
    \* Check the phik LBUG guard
    if readers > 0 \/ writers > 0 then
        lbug_hit := TRUE;
    end if;

CN_Cancel:
    cancelled := TRUE;
    \* unlock_res_and_lock
end process;

end algorithm; *)
\* BEGIN TRANSLATION
VARIABLES readers, writers, cbpending, cancelled, bl_callback_running,
          addref_result, lbug_hit, pc

(* define statement *)
TotalRefs == readers + writers




NoCancelWithRefs ==
    cancelled => (readers = 0 /\ writers = 0)


NoLBUG == ~lbug_hit





CBPendingBeforeCancel ==
    cancelled => cbpending

TypeOK ==
    /\ readers \in 0..3
    /\ writers \in 0..2
    /\ addref_result \in {"none", "ok", "eagain"}


vars == << readers, writers, cbpending, cancelled, bl_callback_running,
           addref_result, lbug_hit, pc >>

ProcSet == {"blast_handler"} \cup {"holder_decref"} \cup {"addref_thread"} \cup {"addref_decref"} \cup {"cancel_thread"}

Init == (* Global variables *)
        /\ readers = 1
        /\ writers = 0
        /\ cbpending = FALSE
        /\ cancelled = FALSE
        /\ bl_callback_running = FALSE
        /\ addref_result = "none"
        /\ lbug_hit = FALSE
        /\ pc = [self \in ProcSet |-> CASE self = "blast_handler" -> "BL_SetFlag"
                                        [] self = "holder_decref" -> "HD_Wait"
                                        [] self = "addref_thread" -> "AT_Lock"
                                        [] self = "addref_decref" -> "AD_Wait"
                                        [] self = "cancel_thread" -> "CN_Wait"]

BL_SetFlag == /\ pc["blast_handler"] = "BL_SetFlag"
              /\ cbpending' = TRUE
              /\ pc' = [pc EXCEPT !["blast_handler"] = "Done"]
              /\ UNCHANGED << readers, writers, cancelled, bl_callback_running,
                              addref_result, lbug_hit >>

BLASTHandler == BL_SetFlag

HD_Wait == /\ pc["holder_decref"] = "HD_Wait"
           /\ cbpending
           /\ pc' = [pc EXCEPT !["holder_decref"] = "HD_Lock"]
           /\ UNCHANGED << readers, writers, cbpending, cancelled,
                           bl_callback_running, addref_result, lbug_hit >>

HD_Lock == /\ pc["holder_decref"] = "HD_Lock"
           /\ readers' = readers - 1
           /\ pc' = [pc EXCEPT !["holder_decref"] = "HD_Check"]
           /\ UNCHANGED << writers, cbpending, cancelled, bl_callback_running,
                           addref_result, lbug_hit >>

HD_Check == /\ pc["holder_decref"] = "HD_Check"
            /\ IF readers = 0 /\ writers = 0 /\ cbpending
                  THEN /\ bl_callback_running' = TRUE
                  ELSE /\ TRUE
                       /\ UNCHANGED bl_callback_running
            /\ pc' = [pc EXCEPT !["holder_decref"] = "Done"]
            /\ UNCHANGED << readers, writers, cbpending, cancelled,
                            addref_result, lbug_hit >>

HolderDecref == HD_Wait \/ HD_Lock \/ HD_Check

AT_Lock == /\ pc["addref_thread"] = "AT_Lock"
           /\ TRUE
           /\ pc' = [pc EXCEPT !["addref_thread"] = "AT_Check"]
           /\ UNCHANGED << readers, writers, cbpending, cancelled,
                           bl_callback_running, addref_result, lbug_hit >>

AT_Check == /\ pc["addref_thread"] = "AT_Check"
            /\ IF InjectBugNoEAGAIN
                  THEN /\ readers' = readers + 1
                       /\ addref_result' = "ok"
                  ELSE /\ IF readers > 0 \/ writers > 0 \/ ~cbpending
                             THEN /\ readers' = readers + 1
                                  /\ addref_result' = "ok"
                             ELSE /\ addref_result' = "eagain"
                                  /\ UNCHANGED readers
            /\ pc' = [pc EXCEPT !["addref_thread"] = "Done"]
            /\ UNCHANGED << writers, cbpending, cancelled, bl_callback_running,
                            lbug_hit >>

AddrefThread == AT_Lock \/ AT_Check

AD_Wait == /\ pc["addref_decref"] = "AD_Wait"
           /\ addref_result = "ok"
           /\ pc' = [pc EXCEPT !["addref_decref"] = "AD_Decref"]
           /\ UNCHANGED << readers, writers, cbpending, cancelled,
                           bl_callback_running, addref_result, lbug_hit >>

AD_Decref == /\ pc["addref_decref"] = "AD_Decref"
             /\ readers' = readers - 1
             /\ pc' = [pc EXCEPT !["addref_decref"] = "AD_Check"]
             /\ UNCHANGED << writers, cbpending, cancelled,
                             bl_callback_running, addref_result, lbug_hit >>

AD_Check == /\ pc["addref_decref"] = "AD_Check"
            /\ IF readers = 0 /\ writers = 0 /\ cbpending /\ ~bl_callback_running
                  THEN /\ bl_callback_running' = TRUE
                  ELSE /\ TRUE
                       /\ UNCHANGED bl_callback_running
            /\ pc' = [pc EXCEPT !["addref_decref"] = "Done"]
            /\ UNCHANGED << readers, writers, cbpending, cancelled,
                            addref_result, lbug_hit >>

AddrefDecref == AD_Wait \/ AD_Decref \/ AD_Check

CN_Wait == /\ pc["cancel_thread"] = "CN_Wait"
           /\ bl_callback_running
           /\ pc' = [pc EXCEPT !["cancel_thread"] = "CN_Lock"]
           /\ UNCHANGED << readers, writers, cbpending, cancelled,
                           bl_callback_running, addref_result, lbug_hit >>

CN_Lock == /\ pc["cancel_thread"] = "CN_Lock"
           /\ IF readers > 0 \/ writers > 0
                 THEN /\ lbug_hit' = TRUE
                 ELSE /\ TRUE
                      /\ UNCHANGED lbug_hit
           /\ pc' = [pc EXCEPT !["cancel_thread"] = "CN_Cancel"]
           /\ UNCHANGED << readers, writers, cbpending, cancelled,
                           bl_callback_running, addref_result >>

CN_Cancel == /\ pc["cancel_thread"] = "CN_Cancel"
             /\ cancelled' = TRUE
             /\ pc' = [pc EXCEPT !["cancel_thread"] = "Done"]
             /\ UNCHANGED << readers, writers, cbpending, bl_callback_running,
                             addref_result, lbug_hit >>

CancelThread == CN_Wait \/ CN_Lock \/ CN_Cancel

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == BLASTHandler \/ HolderDecref \/ AddrefThread \/ AddrefDecref
           \/ CancelThread
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(BLASTHandler)
        /\ WF_vars(HolderDecref)
        /\ WF_vars(AddrefThread)
        /\ WF_vars(AddrefDecref)
        /\ WF_vars(CancelThread)

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

=============================================================================
