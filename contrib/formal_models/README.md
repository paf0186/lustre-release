# Formal Models for Lustre

TLA+/PlusCal models of Lustre concurrency protocols, checked with TLC.

Each model captures one protocol -- a lock lifecycle, a grant
accounting scheme, a request state machine -- as a small set of
interleaved processes plus the invariants the C code must preserve.
Historical bugs are modeled as `InjectBug*` constants: a `_bug.cfg`
must violate an invariant and the matching `_fix.cfg` must pass, so
every model demonstrates both that it can find the bug and that the
fix resolves it.

Validated against lustre-release master 47638add78
(v2_17_58-38, 2026-09-06). Each spec carries a `Validated against:`
line in its header.

42 specifications, 352 TLC configurations, 67 LU tickets modeled.
`./run_model.sh --list-bugs` prints the current index from the cfg
metadata.

## Quick start

    # TLC (tla2tools.jar) is looked up in $TLA2TOOLS, $HOME, /tmp,
    # /usr/local/lib.  Java 11+ required.
    curl -sSL -o ~/tla2tools.jar \
        https://github.com/tlaplus/tlaplus/releases/download/v1.7.4/tla2tools.jar

    cd contrib/formal_models
    ./run_model.sh --list-bugs                 # what is modeled
    ./run_model.sh --verify-fix 13692          # bug cfg fails, fix cfg passes
    ./run_model.sh ldlm_reprocess              # every cfg for one model
    ./run_model.sh --timeout 10m --run-cfg clio/ClPage__baseline.cfg

Always go through `run_model.sh`: it enforces per-cfg timeouts and
state budgets, prints progress, and detects stalled or unbounded
models.  A bare `java tlc2.TLC` has none of that and will run
indefinitely on the larger models.  See `GUIDE.md` for the cfg
metadata format and the workflow for adding a bug to a model.

## Models

| Model | Subsystem | LU tickets |
|---|---|---|
| ldlm_lock_model | LDLM lock granting baseline | -- |
| ldlm_reprocess | LDLM waiting-queue reprocess | 13692, 14522 |
| ldlm_dual_reprocess | LDLM concurrent reprocess paths | 13692, 14522 |
| ldlm_enqueue_reprocess_race | LDLM enqueue vs reprocess | -- |
| ldlm_recovery_reprocess | LDLM reprocess during recovery | 10841 |
| ldlm_unified_lifecycle | LDLM grant/cancel/callback lifecycle | 6416, 8246, 8391 |
| ldlm_lock_order_audit | LDLM lock ordering constraints | -- |
| ldlm_bl_ast_race | LDLM BL_AST vs cancel | 13989 |
| ldlm_cancel_sync | LDLM cancel callback sync | 6416 |
| ldlm_change_resource | LDLM resource migration | 18483 |
| ldlm_convert | LDLM lock mode convert | 11276, 17278, 17415 |
| ldlm_ibits_convert | LDLM inodebits convert | -- |
| ldlm_ibits_convert0 | LDLM inodebits convert, downgrade, reprocess | -- |
| ldlm_refcount_cbpending | LDLM refcount vs CBPENDING | -- |
| osc_grant_model | OSC client grant accounting | 11288, 12687, 13100, 14125, 14901, 19709, 19755 |
| osc_grant_eviction_race | OSC grant vs eviction | 19977 |
| osc_grant_multiclient | OSC grant, multiple clients | 14543, 19976 |
| osc_grant_server_tracking | OST per-export grant tracking | 11939, 13766, 14543, 17933 |
| osc_grant_shrink_reconnect | OSC grant shrink vs reconnect | -- |
| ofd_brw_grant | OFD BRW grant handling | 8895, 9704, 14543 |
| quota_grant_model | Quota acquire/release (QSD/QMT) | 6382, 11929, 14764, 16097, 18612, 19018, 19503, 19791 |
| osc_extent_model | OSC extent lifecycle | 1755, 4852, 7164, 15477, 19956 |
| clio/ClPage | cl_page lifecycle, seqlock, transfer pin | 4581, 14541, 15815, 16160, 16276, 16612, 16649, 16935, 19956 |
| clio/TransferPin | cl_page transfer pin atomicity | 19956 |
| clio/clio_page_writeback_model | writeback vs truncate (focused) | 4581 |
| dio_bio_deadlock | DIO/BIO page pinning deadlock | 19427 |
| dio_bio_deadlock_eviction | DIO/BIO deadlock with eviction | 19427 |
| lov_pfl_layout | LOV PFL layout change vs I/O | 9839, 18435 |
| import_model | ptlrpc import state machine | 19055 |
| rqphase_model | ptlrpc request phases | 7434 |
| ptlrpc_phases | ptlrpc request phases with bulk | 5696, 7434, 11647, 12816, 13509 |
| recovery_model | VBR recovery, replay ordering | 2257, 6928, 10251 |
| recovery_model_multiclient | recovery, multiple clients | -- |
| recovery_model_multiepoch | recovery across epochs | -- |
| lnet_health_model | LNet peer/NI health | 13472, 14783, 18444 |
| mds_open_unlink_model | MDS open vs unlink orphan | -- |
| mds_unlink_orphan_model | MDS unlink, orphans, OST destroy, crash | -- |
| mdt_rename_lock | MDT rename lock ordering | 4725, 11104, 15285, 15491 |
| dne_rename_model | DNE cross-MDT rename | 5559 |
| dne_striped_dir_ops | DNE striped dir ops, distributed txn | 4725, 11104 |
| hsm_coordinator_model | HSM coordinator state machine | 19579, 19829 |
| changelog_consumer | changelog user register/purge | 18552, 19411 |

Models with no ticket carry baseline and exploratory cfgs only.

## Analyses

Findings from the models are checked against the C source before
anything is filed; the write-ups are kept here so the reasoning is
reviewable:

- `ldlm_cancel_callback_analysis.md` -- a `NoGrantDuringCallback`
  violation in ldlm_unified_lifecycle traced to a modeling error
  (writeback on the cancel path is synchronous); no bug.
- `mds_open_unlink_analysis.md` -- the open/unlink orphan race is
  excluded by the DT_TGT_CHILD write lock; no bug.

## Layout

    run_model.sh            runner (the only supported entry point)
    GUIDE.md                cfg metadata, naming, adding a bug to a model
    <model>.tla             one spec per protocol
    <model>__<id>.cfg       TLC configs; the cfg is the registry
    clio/                   cl_page models and clio/README.md
    *_analysis.md           model findings checked against the code

## Keeping models in sync with the code

A model is only useful while it reflects the code.  When fixing a
concurrency bug in a modeled path, add the bug to the model and run
`--verify-fix`; the output belongs in the commit message.  The
`Validated against:` line in each spec records the last tree the
spec was checked against; the source references in each header say
which functions to re-read.

## Validation status (2026-09-10, master 47638add78)

Every spec was checked function-by-function against the tree: the
functions it names were re-read, lock windows and transitions
compared, line references re-anchored, and every cfg rerun to
confirm its `@expect`.  Each header carries a Source block and,
where the model abstracts the code, Validation notes saying how.

Fixed during validation:

- `clio/ClPage.tla` defined two operators twice, which SANY
  rejects, so none of its 34 cfgs had been checked as committed.
- Four cfgs referenced undefined invariants or properties and had
  never been parsed; `run_model.sh` reported the TLC config error
  as a caught bug.  The runner now reports TLC errors as ERROR.
- `ldlm_convert`: the LU-11276 cancel_bits re-check was modeled
  before the bit drop; the code has always dropped first.
- `osc_grant_server_tracking`: LU-17933 was modeled backwards (the
  model's "fix" was the bug); re-modeled from df2b5d99ad.
- `quota_grant_model`: LU-19791 was attributed to osc_page_submit;
  the fix (e1af85a420) is server-side in osd_declare_write_commit.
- `import_model`: the connect guard now also bails on EVICTED, as
  ptlrpc_connect_import_locked does.
- `dne_rename_model`: recovery was modeled as a rollback (remove the
  new name); DNE update recovery rolls forward (re-executes the
  missing remote updates), so C_Recover now removes the old name.
- A dozen comments named functions that do not exist
  (mdt_reint_rename_internal, mdt_object_open, mdd_cl_init, ...);
  corrected to the real ones.

Divergences left open (details in each header):

- `ldlm_unified_lifecycle`: the LU-8246 fix transition was reshaped
  by LU-13692 (server sets BLOCK_GRANTED unconditionally, client
  compensates); the model still has the pre-13692 shape.
- `ldlm_ibits_convert0`: extensions 2 and 3 run server-side actors
  (downgrade, reprocess) against a window that only exists in the
  client-side ldlm_cli_inodebits_convert.
- `osc_extent_model`: the LU-4852 fix (28de66844b, the
  oe_trunc_pending guard in osc_extent_wait) exists only on b2_5;
  master matches the InjectBug4852 = TRUE variant.  A concurrent
  fsync can still reach the assertion by a second path that the
  b2_5 fix does not guard; traced in
  lu4852_truncate_fsync_analysis.md.
- `dio_bio_deadlock`, `dio_bio_deadlock_eviction`: the reserved-slot
  fix has no code counterpart; the landed LU-19427 fix was reverted
  and the ticket reopened.  The eviction extension's premise (ASTs
  consuming BRW slots) is not how eviction works.
- `osc_grant_model`: the LU-14901 SyncFallback process reserves and
  leaks grant; in the code the fallback is taken without a
  reservation.
- `ofd_brw_grant`: the LU-9704 injection has no code path; the real
  bug was a client/server desync on resent RPCs.
- `dne_rename_model`: the LU-5559 it cites is an unrelated ptlrpc
  BL-AST resend ticket and no commit references it; the right ticket
  for the cross-MDT rename crash was not identified.
- `hsm_coordinator_model`: the LU-19579 fix (re-queue all STARTED
  requests) is not in the tree for archive/remove, and the landed
  LU-19829 fix (78c41cd38b, mark the file dirty) is not the dispatch
  dedup the model checks.
- `mdt_rename_lock`: self-blocks if a same-directory rename has equal
  source and target hashes, where the code takes one PDO lock; no cfg
  exercises it.

Tickets whose fix is not in master, so the fix cfg describes a
proposal: LU-19956 (Gerrit 64440), LU-19709, LU-19755, LU-19976,
LU-19579,
LU-14783, LU-16276.  Tickets closed without a code change, so the
bug cfg is hypothetical: LU-19055, LU-2257, LU-6928, LU-19503,
LU-11929, LU-6382.

## Runtime

Most cfgs finish in seconds.  The exceptions, with the default four
TLC workers: the `osc_grant_model` fix cfgs take 8-15 minutes each,
the `dirty_page_accounting*` cfgs carry `@states` budgets of 65M and
110M, and `rqphase_model__LU7434_fix.cfg` has an unbounded state
space at its current constants (past 1e9 states without finishing)
and is given a 200M `@states` budget so a suite run aborts it with
the unbounded-model diagnostic rather than running to the timeout.
Run suites one model at a time: concurrent runner instances in the
same directory can make SANY fail spuriously.
