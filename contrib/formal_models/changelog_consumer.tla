---------------------------- MODULE changelog_consumer ----------------------------
(*
 * PlusCal/TLA+ model of the Lustre MDD changelog consumer lifecycle.
 *
 * Models three concurrent actors:
 *   - Writer:    initializes the changelog consumer (mdd_changelog_init /
 *                mdd_changelog_llog_init, protected by init_mu)
 *   - Reader:    accesses the consumer during mask recalculation
 *                (mdd_changelog_recalc_mask via mdd_changelog_mask_seq_write)
 *   - GC Thread: decides whether to trigger changelog GC
 *                (mdd_changelog_is_space_safe, called from the changelog
 *                write path)
 *
 * Validated against: lustre-release master 47638add78 (2026-09-06)
 *
 * Source (file:line ranges in that tree):
 *   lustre/mdd/mdd_device.c
 *   - mdd_changelog_init()        656-681 (mdd_changelog_mutex 661/678)
 *       -> mdd_changelog_llog_init() 502-654 (opens the changelog and
 *          changelog_users catalogs: the UNINIT -> INIT -> ACTIVE window)
 *   - mdd_changelog_fini()        683-739 (mutex 692/738; STOPPING)
 *   - mdd_changelog_recalc_mask() 1901-1941 (mutex 1912/1938;
 *       no ctxt -> -ENXIO 1915-1916 is the "UNINIT safe no-op")
 *   - mdd_changelog_user_register()   1760-1872
 *   - mdd_changelog_user_purge()      2010-2074
 *   - mdd_changelog_user_deregister() 2241-2286 (recalc_mask at 2281)
 *   - mdd_changelog_llog_cancel()     745-788 (llog_changelog_cancel)
 *   lustre/mdd/mdd_lproc.c
 *   - mdd_changelog_mask_seq_write()  95-162 (recalc_mask at 152)
 *   lustre/mdd/mdd_dir.c
 *   - mdd_changelog_is_space_safe()   918-969 (estimate uses
 *       llh_count + 1 plain llogs, 954)
 *   - mdd_changelog_emrg_cleanup()    983-1006 (llog_cat_free_space()
 *       987 is still used for the catalog-slot exhaustion check 993,
 *       a separate criterion not modeled here)
 *   - mdd_changelog_need_gc()         1009-1017
 *   - mdd_changelog_store()           1026-1098 (GC trigger 1072-1093)
 *   lustre/mdd/mdd_trans.c
 *   - mdd_chlg_garbage_collect()      106-187 (GC thread)
 *   lustre/obdclass/llog_cat_server.c
 *   - llog_cat_free_space()           770-786
 *   lustre/mdd/mdd_internal.h:155  struct mutex mdd_changelog_mutex
 *
 * Validation notes (2026-09-10): both fixes are in the tree.  LU-18552
 * (b12c15b4bd) added mdd->mdd_changelog_mutex, taken by
 * mdd_changelog_init/fini and by mdd_changelog_recalc_mask; init_mu below
 * is that mutex (the reader in the fixed code blocks on it, which the
 * model expresses as "await ACTIVE or UNINIT").  LU-19411 (0c2e3c52cb)
 * replaced the pre-fix estimate
 *   (LLOG_HDR_BITMAP_SIZE - 1 - llog_cat_free_space()) * plain_llog_max
 * with (llh_count + 1) * plain_llog_max; the model's "CatFreeSlots = 0
 * triggers GC" is a simplification of that over-count.  mdd_cl->mc_dev
 * mentioned below does not exist; the pointer the pre-fix reader could
 * dereference before init is ctxt->loc_handle->lgh_hdr (recalc_mask
 * 1918).  The GC thread here is the trigger decision in
 * mdd_changelog_store() -> mdd_changelog_need_gc(), not the thread that
 * purges users.
 *
 * Consumer lifecycle states (4):
 *   UNINIT   -- consumer not yet initialized / not registered
 *   INIT     -- initialization in progress (partially set up, NOT yet safe
 *               to access -- the changelog llog ctxt / loc_handle may be
 *               NULL or half-initialized)
 *   ACTIVE   -- fully initialized; safe to access and use
 *   STOPPING -- shutdown in progress (terminal, not modeled in detail)
 *
 * Known bugs modeled:
 *
 *   LU-18552: Race between changelog consumer init and reader access.
 *             mdd_changelog_recalc_mask() is called by mdd_changelog_mask_seq_write
 *             without verifying that mdd->mdd_cl is fully initialized.
 *             If invoked during the UNINIT->INIT->ACTIVE transition window,
 *             the reader dereferences a NULL or partially-set mdd->mdd_cl
 *             pointer, triggering a kernel NULL pointer dereference at
 *             mdd_changelog_recalc_mask+0xd4.
 *             Fix: serialize access -- reader must wait until cl_state is
 *             ACTIVE (safe to access) or UNINIT (safe no-op).
 *             Set InjectBug18552 = TRUE to reproduce.
 *
 *   LU-19411: Wrong GC trigger due to pessimistic space estimation.
 *             mdd_changelog_is_space_safe() uses llog_cat_free_space()
 *             as a proxy for consumed log space. This function returns the
 *             number of catalog slots available for NEW plain llog files,
 *             not the amount of space already consumed by existing logs.
 *             When CatFreeSlots = 0 (all catalog slots allocated), GC is
 *             triggered even when the actual log count (LogCount / llh_count)
 *             is well below the space threshold -- GC fires without real need.
 *             Fix: use LogCount (llh_count) as the space estimation metric;
 *             only trigger GC when LogCount > SpaceThreshold.
 *             Set InjectBug19411 = TRUE to reproduce.
 *)

EXTENDS Integers, TLC

CONSTANTS
    LogCount,         \* Current number of plain llogs in use (llh_count)
    CatFreeSlots,     \* Catalog free slot count (llog_cat_free_space() result)
    SpaceThreshold,   \* Log count above which GC is genuinely warranted
    InjectBug18552,   \* TRUE = reader skips init-state check (LU-18552 bug)
    InjectBug19411    \* TRUE = GC uses CatFreeSlots as space proxy (LU-19411 bug)

ASSUME LogCount \in Nat
ASSUME CatFreeSlots \in Nat
ASSUME SpaceThreshold \in Nat

(* --algorithm changelog_consumer

variables
    \* ---- Changelog consumer lifecycle state ----
    \* Represents the state of mdd->mdd_cl (the changelog consumer struct).
    cl_state = "UNINIT",

    \* ---- Init serialization mutex ----
    \* Protects the multi-step UNINIT -> INIT -> ACTIVE transition.
    \* Models mdd->mdd_changelog_mutex (mdd_internal.h:155, added by
    \* LU-18552), taken in mdd_changelog_init/fini and recalc_mask.
    init_mu = "free",

    \* ---- LU-18552 violation tracker ----
    \* Set TRUE when reader accesses consumer while not yet fully initialized.
    \* Represents the NULL pointer dereference at mdd_changelog_recalc_mask.
    reader_saw_null = FALSE,

    \* ---- LU-19411 violation trackers ----
    \* gc_triggered: GC operation was initiated by the space-check logic.
    gc_triggered = FALSE,
    \* gc_needed: GC was genuinely warranted (LogCount > SpaceThreshold).
    gc_needed = FALSE,

    \* ---- Per-process completion flags ----
    thread_done = [t \in {"writer", "reader", "gc"} |-> FALSE];

define
    TypeOK ==
        /\ cl_state \in {"UNINIT", "INIT", "ACTIVE", "STOPPING"}
        /\ init_mu \in {"free", "writer"}
        /\ reader_saw_null \in BOOLEAN
        /\ gc_triggered \in BOOLEAN
        /\ gc_needed \in BOOLEAN

    \* LU-18552: Reader must never access an uninitialized/partially-init consumer.
    \* A NULL dereference occurs when mdd_changelog_recalc_mask() reads
    \* mdd->mdd_cl->mc_dev before mdd->mdd_cl has been fully set up.
    NoAccessWhileUninit == ~reader_saw_null

    \* LU-19411: GC must not trigger when space is genuinely available.
    \* CatFreeSlots == 0 (catalog slot exhaustion) does NOT imply disk full;
    \* only LogCount > SpaceThreshold justifies GC.
    NoFalseGC == gc_triggered => gc_needed

    \* Sanity: after writer finishes, consumer is in a usable state.
    InitComplete ==
        thread_done["writer"] => cl_state \in {"ACTIVE", "STOPPING"}

end define;

\* ================================================================
\* Writer: mdd_changelog_init / mdd_changelog_create_init
\* Initializes the changelog consumer under init_mu.
\* State machine: UNINIT -> INIT (partial) -> ACTIVE (complete)
\*
\* The INIT state is the race window for LU-18552: between W_SetInit
\* and W_SetActive, mdd->mdd_cl exists but mc_dev and other fields
\* have not yet been set up (they may be NULL / zeroed).
\* ================================================================
fair process WriterThread = "writer"
begin
W_AcquireLock:
    \* mutex_lock(&mdd->mdd_changelog_mutex) (mdd_device.c:661)
    await init_mu = "free";
    init_mu := "writer";

W_SetInit:
    \* mdd->mdd_cl allocated; initialization begins.
    \* LU-18552 RACE WINDOW STARTS HERE: mdd_cl is partially initialized.
    cl_state := "INIT";

W_SetActive:
    \* mdd->mdd_cl fully initialized: llog catalogs opened, loc_handle
    \* valid (mdd_changelog_llog_init returned).
    \* LU-18552 RACE WINDOW ENDS HERE.
    cl_state := "ACTIVE";

W_ReleaseLock:
    \* Release init mutex -- consumer is now publicly accessible.
    init_mu := "free";

W_Done:
    thread_done["writer"] := TRUE;
end process;

\* ================================================================
\* Reader: mdd_changelog_mask_seq_write -> mdd_changelog_recalc_mask
\* Accesses the changelog consumer to recalculate the event mask.
\*
\* LU-18552 BUG: mdd_changelog_recalc_mask() is called without verifying
\*   that mdd->mdd_cl is initialized. Accessing during INIT state (or before
\*   UNINIT clears to ACTIVE) dereferences a NULL or garbage pointer.
\*
\* LU-18552 FIX: Serialize with the init path. The reader must only
\*   proceed if cl_state is ACTIVE (safe to access) or UNINIT (safe no-op;
\*   no consumer registered, nothing to recalculate).
\*   INIT state means "writer is mid-initialization" -- must wait.
\* ================================================================
fair process ReaderThread = "reader"
begin
R_Start:
    if InjectBug18552 then
        \* BUG: access mdd->mdd_cl without serialization.
        \* If cl_state is INIT or UNINIT, consumer is not ready.
        \* This models the NULL pointer dereference at mdd_changelog_recalc_mask+0xd4.
        if cl_state /= "ACTIVE" then
            reader_saw_null := TRUE;
        end if;
    else
        \* FIX: wait until consumer is in a stable, safe state.
        \*   UNINIT = no consumer registered -> safe no-op (nothing to recalc).
        \*   ACTIVE = fully initialized      -> safe to access.
        \*   INIT   = init in progress       -> must wait for writer to finish.
        await cl_state = "ACTIVE" \/ cl_state = "UNINIT";
        skip;
    end if;

R_Done:
    thread_done["reader"] := TRUE;
end process;

\* ================================================================
\* GC Thread: mdd_changelog_is_space_safe (changelog GC trigger path)
\* Evaluates whether to trigger changelog garbage collection.
\*
\* LU-19411 BUG: uses CatFreeSlots (llog_cat_free_space()) as space proxy.
\*   llog_cat_free_space() returns the number of catalog entries available
\*   for NEW plain llog files -- NOT the amount of space consumed by logs.
\*   A llog catalog with CatFreeSlots = 0 has allocated all its header slots,
\*   but existing plain llogs may have plenty of free space inside them.
\*   This causes GC to fire prematurely (when LogCount is still low).
\*
\* LU-19411 FIX: use LogCount (llh_count -- number of plain llogs in use)
\*   as the actual space metric. Only trigger GC when LogCount > SpaceThreshold.
\* ================================================================
fair process GCThread = "gc"
begin
GC_WaitActive:
    \* GC only runs once the consumer is live (has logs to manage).
    await cl_state = "ACTIVE";

GC_CheckSpace:
    \* mdd_changelog_is_space_safe decision logic.
    if InjectBug19411 then
        \* BUG: use catalog slot availability as space proxy.
        \* CatFreeSlots = 0 -> GC fires, even when LogCount is below threshold.
        if CatFreeSlots = 0 then
            gc_triggered := TRUE;
            gc_needed := (LogCount > SpaceThreshold);
        end if;
    else
        \* FIX: use actual plain llog count (llh_count) as space metric.
        \* GC fires only when LogCount genuinely exceeds the threshold.
        if LogCount > SpaceThreshold then
            gc_triggered := TRUE;
            gc_needed := TRUE;
        end if;
    end if;

GC_Done:
    thread_done["gc"] := TRUE;
end process;

end algorithm; *)

\* BEGIN TRANSLATION
VARIABLES cl_state, init_mu, reader_saw_null, gc_triggered, gc_needed,
          thread_done, pc

(* define statement *)
TypeOK ==
    /\ cl_state \in {"UNINIT", "INIT", "ACTIVE", "STOPPING"}
    /\ init_mu \in {"free", "writer"}
    /\ reader_saw_null \in BOOLEAN
    /\ gc_triggered \in BOOLEAN
    /\ gc_needed \in BOOLEAN

NoAccessWhileUninit == ~reader_saw_null

NoFalseGC == gc_triggered => gc_needed

InitComplete ==
    thread_done["writer"] => cl_state \in {"ACTIVE", "STOPPING"}


vars == << cl_state, init_mu, reader_saw_null, gc_triggered, gc_needed,
           thread_done, pc >>

ProcSet == {"writer"} \cup {"reader"} \cup {"gc"}

Init == (* Global variables *)
        /\ cl_state = "UNINIT"
        /\ init_mu = "free"
        /\ reader_saw_null = FALSE
        /\ gc_triggered = FALSE
        /\ gc_needed = FALSE
        /\ thread_done = [t \in {"writer", "reader", "gc"} |-> FALSE]
        /\ pc = [self \in ProcSet |-> CASE self = "writer" -> "W_AcquireLock"
                                        [] self = "reader" -> "R_Start"
                                        [] self = "gc"     -> "GC_WaitActive"]

W_AcquireLock == /\ pc["writer"] = "W_AcquireLock"
                 /\ init_mu = "free"
                 /\ init_mu' = "writer"
                 /\ pc' = [pc EXCEPT !["writer"] = "W_SetInit"]
                 /\ UNCHANGED << cl_state, reader_saw_null, gc_triggered,
                                 gc_needed, thread_done >>

W_SetInit == /\ pc["writer"] = "W_SetInit"
             /\ cl_state' = "INIT"
             /\ pc' = [pc EXCEPT !["writer"] = "W_SetActive"]
             /\ UNCHANGED << init_mu, reader_saw_null, gc_triggered,
                             gc_needed, thread_done >>

W_SetActive == /\ pc["writer"] = "W_SetActive"
               /\ cl_state' = "ACTIVE"
               /\ pc' = [pc EXCEPT !["writer"] = "W_ReleaseLock"]
               /\ UNCHANGED << init_mu, reader_saw_null, gc_triggered,
                               gc_needed, thread_done >>

W_ReleaseLock == /\ pc["writer"] = "W_ReleaseLock"
                 /\ init_mu' = "free"
                 /\ pc' = [pc EXCEPT !["writer"] = "W_Done"]
                 /\ UNCHANGED << cl_state, reader_saw_null, gc_triggered,
                                 gc_needed, thread_done >>

W_Done == /\ pc["writer"] = "W_Done"
          /\ thread_done' = [thread_done EXCEPT !["writer"] = TRUE]
          /\ pc' = [pc EXCEPT !["writer"] = "Done"]
          /\ UNCHANGED << cl_state, init_mu, reader_saw_null,
                          gc_triggered, gc_needed >>

WriterThread == W_AcquireLock \/ W_SetInit \/ W_SetActive
                  \/ W_ReleaseLock \/ W_Done

R_Start == /\ pc["reader"] = "R_Start"
           /\ IF InjectBug18552
                 THEN /\ IF cl_state /= "ACTIVE"
                             THEN /\ reader_saw_null' = TRUE
                             ELSE /\ TRUE
                                  /\ UNCHANGED reader_saw_null
                 ELSE /\ (cl_state = "ACTIVE" \/ cl_state = "UNINIT")
                      /\ UNCHANGED reader_saw_null
           /\ pc' = [pc EXCEPT !["reader"] = "R_Done"]
           /\ UNCHANGED << cl_state, init_mu, gc_triggered,
                           gc_needed, thread_done >>

R_Done == /\ pc["reader"] = "R_Done"
          /\ thread_done' = [thread_done EXCEPT !["reader"] = TRUE]
          /\ pc' = [pc EXCEPT !["reader"] = "Done"]
          /\ UNCHANGED << cl_state, init_mu, reader_saw_null,
                          gc_triggered, gc_needed >>

ReaderThread == R_Start \/ R_Done

GC_WaitActive == /\ pc["gc"] = "GC_WaitActive"
                 /\ cl_state = "ACTIVE"
                 /\ pc' = [pc EXCEPT !["gc"] = "GC_CheckSpace"]
                 /\ UNCHANGED << cl_state, init_mu, reader_saw_null,
                                 gc_triggered, gc_needed, thread_done >>

GC_CheckSpace == /\ pc["gc"] = "GC_CheckSpace"
                 /\ IF InjectBug19411
                       THEN /\ IF CatFreeSlots = 0
                                   THEN /\ gc_triggered' = TRUE
                                        /\ gc_needed' = (LogCount > SpaceThreshold)
                                   ELSE /\ TRUE
                                        /\ UNCHANGED << gc_triggered, gc_needed >>
                       ELSE /\ IF LogCount > SpaceThreshold
                                   THEN /\ gc_triggered' = TRUE
                                        /\ gc_needed' = TRUE
                                   ELSE /\ TRUE
                                        /\ UNCHANGED << gc_triggered, gc_needed >>
                 /\ pc' = [pc EXCEPT !["gc"] = "GC_Done"]
                 /\ UNCHANGED << cl_state, init_mu, reader_saw_null, thread_done >>

GC_Done == /\ pc["gc"] = "GC_Done"
           /\ thread_done' = [thread_done EXCEPT !["gc"] = TRUE]
           /\ pc' = [pc EXCEPT !["gc"] = "Done"]
           /\ UNCHANGED << cl_state, init_mu, reader_saw_null,
                           gc_triggered, gc_needed >>

GCThread == GC_WaitActive \/ GC_CheckSpace \/ GC_Done

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == WriterThread \/ ReaderThread \/ GCThread \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(WriterThread)
        /\ WF_vars(ReaderThread)
        /\ WF_vars(GCThread)

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

\* ================================================================
\* Liveness: all threads eventually complete
\* ================================================================
AllComplete == <>(\A t \in {"writer", "reader", "gc"} : thread_done[t])

=============================================================================
