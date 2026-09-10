--------------------------- MODULE TransferPin ---------------------------
(*
 * TLA+ model of the cl_page transfer pin lifecycle in Lustre OSC.
 *
 * Models the interaction between:
 *   - Transfer submission (osc_page_cache_add / osc_page_submit)
 *   - Transfer completion (osc_completion)
 *   - Page deletion (osc_page_delete, called from cl_page_delete)
 *
 * The cl_page state machine enforces:
 *   CPS_PAGEOUT -> CPS_CACHED  (via cl_page_complete, allowed)
 *   CPS_PAGEOUT -> CPS_FREEING (via cl_page_delete, FORBIDDEN)
 *   CPS_CACHED  -> CPS_FREEING (via cl_page_delete, allowed)
 *
 * This means cl_page_delete can only run AFTER cl_page_complete
 * transitions the page to CPS_CACHED.
 *
 * Three code variants modeled (selected by FIX_VERSION constant):
 *
 *   "buggy"   - Original code: flag cleared directly (decoupled from
 *               ref drop).  On weakly-ordered architectures the flag
 *               clear can be delayed, causing double-put.
 *
 *   "v64472"  - Alternative fix attempt: cl_page_complete first,
 *               then osc_page_transfer_put.  Delete has LASSERT.
 *               MODEL FINDS BUG: delete can race between complete
 *               and transfer_put, hitting the LASSERT.
 *
 *   "v64472b" - Corrected alternative (Gerrit 64472, revised):
 *               cl_page_complete first, then osc_page_transfer_put.
 *               Delete keeps osc_page_transfer_put (idempotent
 *               safety net instead of LASSERT).  Ref accounting is
 *               correct (whoever runs transfer_put first clears
 *               pin+ref, the other is a no-op), but the pin is still
 *               set while the page is already CPS_CACHED, so a new
 *               submission can hit LASSERT(!ops_transfer_pinned) in
 *               osc_page_transfer_get (NoPinWhileCached).
 *
 *   "v64440"  - Proposed fix (Gerrit 64440; patchset 9 and later,
 *               same shape through patchset 14): take temp ref,
 *               osc_page_transfer_put (clears pin while still PAGEOUT),
 *               then cl_page_complete, then drop temp ref.  Delete
 *               still calls osc_page_transfer_put (idempotent).
 *
 * To run:  cd contrib/formal_models && ./run_model.sh TransferPin
 *          (or ./run_model.sh --run-cfg clio/TransferPin__<cfg>.cfg)
 * Lives:   formal_models/clio/
 *
 * Source (lustre-release master 47638add78):
 *   lustre/osc/osc_page.c
 *     osc_page_transfer_get   36-43   LASSERT(!pinned); cl_page_get;
 *                                     ops_transfer_pinned = 1
 *     osc_page_transfer_put   45-54   if (pinned) { pinned = 0;
 *                                     cl_page_put }  (idempotent)
 *     osc_page_cache_add      56-70   transfer_get for async writes
 *     osc_page_delete        129-165  transfer_put at 140 (delete
 *                                     safety net), from cl_page_delete
 *     osc_page_submit        288-311  transfer_get at 308 (sync IO)
 *   lustre/osc/osc_cache.c
 *     osc_completion        1398-1451 ops_transfer_pinned = 0 at
 *                                     1419-1421 (direct clear),
 *                                     cl_page_complete at 1446,
 *                                     unconditional cl_page_put 1448
 *                                     == the "buggy" variant
 *   lustre/obdclass/cl_page.c
 *     __cl_page_state_set    470-527  allowed_transitions[][] 477-511:
 *                                     PAGEOUT->CACHED only; no
 *                                     PAGEOUT->FREEING
 *     __cl_page_delete       934-960  CPS_FREEING at 950, then
 *                                     cpo_delete bottom-up
 *     cl_page_delete         984-991
 *     cl_page_complete      1106-1149 CPS_CACHED at 1121, then
 *                                     cpo_complete bottom-up
 *
 * Validated against: lustre-release master 47638add78 (2026-09-06)
 * Validation notes:
 *   - LU-19956 has NOT landed in this tree: Gerrit 64440 is still
 *     NEW (patchset 14) and Gerrit 64472 is ABANDONED.  osc_completion
 *     in this tree is the "buggy" variant above (direct flag clear,
 *     then cl_page_complete, then unconditional cl_page_put), so
 *     TransferPin__LU19956_original.cfg is the configuration that
 *     matches the current code.  Patchset 14 of 64440 still has the
 *     v64440 shape (cl_page_get; osc_page_transfer_put;
 *     cl_page_complete; cl_page_put) and osc_page_delete keeps the
 *     idempotent transfer_put.
 *   - State machine, transfer_get/put and delete paths match the
 *     model; no semantic change was needed.
 *)

EXTENDS Integers, TLC

CONSTANTS
    FIX_VERSION,    \* "buggy", "v64472", "v64472b", or "v64440"
    MAX_TRANSFERS   \* How many transfer cycles to model (keep small: 2 is enough)

VARIABLES
    page_state,         \* CPS_CACHED, CPS_PAGEOUT, CPS_FREEING
    transfer_pinned,    \* The ops_transfer_pinned flag
    cp_ref,             \* cl_page reference count (>0 = alive)
    temp_ref,           \* Whether completion holds a temporary ref (v64440)
    transfer_count,     \* How many transfers have been submitted
    completion_pc,      \* Completion process program counter
    delete_pc,          \* Delete process program counter
    submit_pc           \* Submit process program counter

vars == <<page_state, transfer_pinned, cp_ref, temp_ref, transfer_count,
          completion_pc, delete_pc, submit_pc>>

(*
 * Initial state: page is cached with a base reference (from VFS).
 *)
Init ==
    /\ page_state = "CPS_CACHED"
    /\ transfer_pinned = FALSE
    /\ cp_ref = 1              \* VFS page cache holds one ref
    /\ temp_ref = FALSE
    /\ transfer_count = 0
    /\ completion_pc = "idle"
    /\ delete_pc = "idle"
    /\ submit_pc = "idle"

(* ================================================================
 * SUBMIT: osc_page_cache_add -> osc_page_transfer_get
 * Transitions page CPS_CACHED -> CPS_PAGEOUT, takes transfer pin.
 * ================================================================ *)
Submit ==
    /\ submit_pc = "idle"
    /\ transfer_count < MAX_TRANSFERS
    /\ page_state = "CPS_CACHED"
    /\ ~transfer_pinned           \* LASSERT(!ops_transfer_pinned)
    /\ submit_pc' = "done"
    /\ page_state' = "CPS_PAGEOUT"
    /\ transfer_pinned' = TRUE
    /\ cp_ref' = cp_ref + 1      \* cl_page_get (transfer pin ref)
    /\ transfer_count' = transfer_count + 1
    /\ UNCHANGED <<temp_ref, completion_pc, delete_pc>>

SubmitReset ==
    /\ submit_pc = "done"
    /\ submit_pc' = "idle"
    /\ UNCHANGED <<page_state, transfer_pinned, cp_ref, temp_ref,
                   transfer_count, completion_pc, delete_pc>>

(* ================================================================
 * COMPLETION: osc_completion
 *
 * BUGGY:  clear flag (separate store, may be delayed on weak archs),
 *         then cl_page_complete, then unconditional cl_page_put.
 *
 * V64472: cl_page_complete first, then osc_page_transfer_put.
 *
 * V64440: cl_page_get (temp ref), osc_page_transfer_put (clears pin
 *         while still PAGEOUT), cl_page_complete, cl_page_put (temp).
 * ================================================================ *)

\* ---- BUGGY completion ----
\* Step 1: cl_page_complete runs, state -> CACHED.
\* The separate flag clear store may not yet be visible.
CompletionBuggyStart ==
    /\ FIX_VERSION = "buggy"
    /\ completion_pc = "idle"
    /\ page_state = "CPS_PAGEOUT"
    /\ page_state' = "CPS_CACHED"
    /\ completion_pc' = "buggy_state_changed"
    /\ UNCHANGED <<transfer_pinned, cp_ref, temp_ref,
                   transfer_count, delete_pc, submit_pc>>

\* Step 2 (BUGGY): flag clear becomes visible (separate store).
\* On aarch64, this store can be delayed arbitrarily after the
\* state change store, allowing delete to see CPS_CACHED with
\* transfer_pinned still TRUE.
CompletionBuggyFlagClear ==
    /\ FIX_VERSION = "buggy"
    /\ completion_pc = "buggy_state_changed"
    /\ transfer_pinned' = FALSE
    /\ completion_pc' = "buggy_flag_cleared"
    /\ UNCHANGED <<page_state, cp_ref, temp_ref, transfer_count,
                   delete_pc, submit_pc>>

\* Step 3 (BUGGY): unconditional cl_page_put
CompletionBuggyPut ==
    /\ FIX_VERSION = "buggy"
    /\ completion_pc = "buggy_flag_cleared"
    /\ cp_ref' = cp_ref - 1
    /\ completion_pc' = "done"
    /\ UNCHANGED <<page_state, transfer_pinned, temp_ref,
                   transfer_count, delete_pc, submit_pc>>

\* ---- V64472/V64472b completion (complete first, then transfer_put) ----
\* Step 1: cl_page_complete (state -> CACHED)
CompletionV64472Start ==
    /\ FIX_VERSION \in {"v64472", "v64472b"}
    /\ completion_pc = "idle"
    /\ page_state = "CPS_PAGEOUT"
    /\ page_state' = "CPS_CACHED"
    /\ completion_pc' = "v64472_completed"
    /\ UNCHANGED <<transfer_pinned, cp_ref, temp_ref,
                   transfer_count, delete_pc, submit_pc>>

\* Step 2: osc_page_transfer_put (flag + ref together)
CompletionV64472Put ==
    /\ FIX_VERSION \in {"v64472", "v64472b"}
    /\ completion_pc = "v64472_completed"
    /\ IF transfer_pinned
       THEN /\ transfer_pinned' = FALSE
            /\ cp_ref' = cp_ref - 1
       ELSE /\ UNCHANGED <<transfer_pinned, cp_ref>>
    /\ completion_pc' = "done"
    /\ UNCHANGED <<page_state, temp_ref, transfer_count,
                   delete_pc, submit_pc>>

\* ---- V64440 completion (temp ref, put before complete) ----
\* Step 1: cl_page_get (temp ref) + osc_page_transfer_put
\* These happen atomically from the model's perspective because
\* they execute on the same CPU with no interleaving point.
CompletionV64440TempRefAndPut ==
    /\ FIX_VERSION = "v64440"
    /\ completion_pc = "idle"
    /\ page_state = "CPS_PAGEOUT"
    /\ IF transfer_pinned
       THEN \* get(+1) then transfer_put(-1): net ref = 0 change
            /\ transfer_pinned' = FALSE
            /\ cp_ref' = cp_ref   \* +1 -1 = 0 net
            /\ temp_ref' = TRUE
       ELSE \* get(+1), transfer_put is no-op (pin already clear)
            /\ cp_ref' = cp_ref + 1
            /\ temp_ref' = TRUE
            /\ UNCHANGED transfer_pinned
    /\ completion_pc' = "v64440_pin_cleared"
    /\ UNCHANGED <<page_state, transfer_count, delete_pc, submit_pc>>

\* Step 2: cl_page_complete (state -> CACHED)
\* Pin is already clear at this point, so delete seeing CACHED
\* will also see pin=FALSE.
CompletionV64440Complete ==
    /\ FIX_VERSION = "v64440"
    /\ completion_pc = "v64440_pin_cleared"
    /\ page_state' = "CPS_CACHED"
    /\ completion_pc' = "v64440_completed"
    /\ UNCHANGED <<transfer_pinned, cp_ref, temp_ref,
                   transfer_count, delete_pc, submit_pc>>

\* Step 3: cl_page_put (drop temp ref)
CompletionV64440DropTemp ==
    /\ FIX_VERSION = "v64440"
    /\ completion_pc = "v64440_completed"
    /\ temp_ref = TRUE
    /\ cp_ref' = cp_ref - 1
    /\ temp_ref' = FALSE
    /\ completion_pc' = "done"
    /\ UNCHANGED <<page_state, transfer_pinned, transfer_count,
                   delete_pc, submit_pc>>

\* ---- Completion reset (all versions) ----
CompletionReset ==
    /\ completion_pc = "done"
    /\ completion_pc' = "idle"
    /\ UNCHANGED <<page_state, transfer_pinned, cp_ref, temp_ref,
                   transfer_count, delete_pc, submit_pc>>

(* ================================================================
 * DELETE: osc_page_delete (called from cl_page_delete)
 *
 * State machine: can only run when page is CPS_CACHED (not PAGEOUT).
 * Transitions CPS_CACHED -> CPS_FREEING.
 *
 * BUGGY:   calls osc_page_transfer_put (might drop ref)
 * V64472:  asserts !transfer_pinned, does NOT call transfer_put
 * V64472b: calls osc_page_transfer_put (idempotent safety net)
 * V64440:  calls osc_page_transfer_put (idempotent, pin already clear)
 * ================================================================ *)

DeleteStart ==
    /\ delete_pc = "idle"
    /\ page_state = "CPS_CACHED"
    /\ page_state' = "CPS_FREEING"
    /\ IF FIX_VERSION = "v64472"
       THEN \* V64472: assert only, no transfer_put
            /\ UNCHANGED <<transfer_pinned, cp_ref>>
       ELSE \* BUGGY, V64472b, V64440: osc_page_transfer_put
            /\ IF transfer_pinned
               THEN /\ transfer_pinned' = FALSE
                    /\ cp_ref' = cp_ref - 1
               ELSE /\ UNCHANGED <<transfer_pinned, cp_ref>>
    /\ delete_pc' = "done"
    /\ UNCHANGED <<temp_ref, transfer_count, completion_pc, submit_pc>>

DeleteReset ==
    /\ delete_pc = "done"
    /\ delete_pc' = "idle"
    /\ UNCHANGED <<page_state, transfer_pinned, cp_ref, temp_ref,
                   transfer_count, completion_pc, submit_pc>>

(* ================================================================
 * Next-state relation: any enabled action can fire.
 * ================================================================ *)
Done ==
    /\ page_state = "CPS_FREEING"
    /\ UNCHANGED vars

Next ==
    \/ Submit
    \/ SubmitReset
    \* Buggy completion
    \/ CompletionBuggyStart
    \/ CompletionBuggyFlagClear
    \/ CompletionBuggyPut
    \* V64472 completion
    \/ CompletionV64472Start
    \/ CompletionV64472Put
    \* V64440 completion
    \/ CompletionV64440TempRefAndPut
    \/ CompletionV64440Complete
    \/ CompletionV64440DropTemp
    \* Completion reset (all)
    \/ CompletionReset
    \* Delete
    \/ DeleteStart
    \/ DeleteReset
    \/ Done

(* ================================================================
 * INVARIANTS: properties that must hold in every reachable state.
 * ================================================================ *)

\* The page reference count must never go negative.
\* A ref of 0 is a use-after-free.
NoRefLeak ==
    cp_ref >= 0

\* While page is alive (not freeing), must have at least the base ref.
NoUseAfterFree ==
    (page_state # "CPS_FREEING") => (cp_ref >= 1)

\* After delete (CPS_FREEING), once both completion and delete are
\* done, the transfer pin must be clear and only the base ref remains.
NoOrphanedRef ==
    (page_state = "CPS_FREEING" /\ delete_pc = "done"
     /\ completion_pc = "done") =>
        (cp_ref = 1 /\ transfer_pinned = FALSE)

\* The transfer pin flag must only be set when the page is in
\* transfer (PAGEOUT) or completion is in progress.
\* In CACHED state with completion done, pin must be clear.
PinClearedBeforeReuse ==
    (page_state = "CPS_CACHED" /\ completion_pc = "done") =>
        (transfer_pinned = FALSE)

\* V64472 adds LASSERT(!transfer_pinned) in osc_page_delete.
\* This invariant checks whether that assert can fire.
DeleteNeverSeesPinSet ==
    (FIX_VERSION = "v64472" /\ delete_pc = "done") =>
        (transfer_pinned = FALSE)

\* V64440: pin is always cleared before page becomes CACHED.
\* This is the key ordering guarantee of the temp-ref approach.
PinClearBeforeCached ==
    (FIX_VERSION = "v64440" /\ page_state = "CPS_CACHED") =>
        (transfer_pinned = FALSE)

\* Universal: the transfer pin must NEVER be set when the page is
\* CPS_CACHED.  Once CACHED, new I/O can re-submit the page, and
\* osc_page_transfer_get asserts the pin is clear.  Any variant
\* that leaves the pin set in CACHED state has a re-submission crash.
NoPinWhileCached ==
    (page_state = "CPS_CACHED") => (transfer_pinned = FALSE)

(* ================================================================
 * SPEC
 * ================================================================ *)
Spec == Init /\ [][Next]_vars

==========================================================================
