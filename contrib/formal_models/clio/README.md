# TLA+ Formal Models for Lustre CLIO (cl_page)

## Overview

This directory contains TLA+ formal models that verify concurrent
protocols in the CLIO (Client IO) layer -- the cl_page lifecycle
spanning cl_page.c, vvp_page.c, osc_page.c, and llite (mmap/rw).

Validated against lustre-release master 47638add78 (2026-09-06).
Each spec header carries a Source block with the functions and
file:line ranges it models, and a Validated against line.

## Models

### clio_page_writeback_model.tla -- Writeback vs Truncation Race (Focused)

Minimal model of the race between a writeback thread and a truncation
thread on a single page.  Isolated from the full ClPage lifecycle for
clarity and fast iteration.

**State:**
- `page_state` in {CACHE, WRITEBACK, FREEABLE}
- `in_flight` boolean (TRUE while write I/O is outstanding)

**Threads:**
- `WritebackThread`: CACHE -> WRITEBACK (submit I/O) -> CACHE (I/O completes)
- `TruncateThread`: -> FREEABLE (atomically, with or without guard)

**Invariant:** `NoStaleWrite` -- page never FREEABLE while `in_flight = TRUE`.

**Bug injection:** `INJECT_TRUNCATE_NO_WAIT = TRUE` omits the
`page_state != WRITEBACK` guard on the FREEABLE transition.  This is
the abstract form of the LU-4581 hang: the historical fix was LU-2779
(26345bee6b), which made osc_extent_wait uninterruptible so that
osc_lock_flush waits for in-flight writes before discarding pages.
In the current tree __cl_page_own also waits on or rejects
PageWriteback (cl_page.c:731-738, moved there by LU-10994) and
ll_invalidate_folio asserts !PageWriteback, so the guard exists at
both the extent and the page level.

The fix models the guard and the state transition as a **single
atomic action**, capturing the mutual exclusion the code provides --
preventing new writebacks from starting after the guard check passes.

| Config file | Expected | What it models |
|-------------|----------|----------------|
| clio_page_writeback_model__baseline.cfg | PASS | Fix mode -- NoStaleWrite holds (5 states) |
| clio_page_writeback_model__LU4581_bug.cfg | CAUGHT BUG | No guard -- truncate races write I/O |
| clio_page_writeback_model__LU4581_fix.cfg | PASS | Atomic guard -- writeback-complete check before FREEABLE |

TLC result: 5 distinct states in each config.  The bug is caught in
the interleaving where WritebackThread starts (CACHE -> WRITEBACK,
in_flight=TRUE) and TruncateThread then fires without waiting --
NoStaleWrite violated.

### TransferPin.tla -- Transfer Pin Lifecycle

Models the `ops_transfer_pinned` flag lifecycle -- the interaction
between transfer submission, RPC completion, and page deletion.
Focused on LU-19956.

As of master 47638add78 the LU-19956 fix has NOT merged: Gerrit
64440 is still under review and 64472 was abandoned.  The tree's
osc_completion therefore still has the original shape (clear
ops_transfer_pinned as a separate store, then unconditional
cl_page_put), which is the FAIL variant below; the PASS config
describes the proposed 64440 patch.

| Config file                       | Expected | What it models |
|-----------------------------------|----------|----------------|
| TransferPin__LU19956_original.cfg | FAIL     | Original (current) code - flag clear decoupled from ref drop |
| TransferPin__GR64472.cfg          | FAIL     | Gerrit 64472 - complete first then transfer_put; pin still set one step after cl_page_complete |
| TransferPin__GR64472r2.cfg        | FAIL     | Gerrit 64472 revised - same ordering; re-submission crash (same as 64440 ps10) |
| TransferPin__GR64440.cfg          | PASS     | Gerrit 64440 (proposed, unmerged) - temp ref, pin cleared before CACHED, idempotent transfer_put |

### ClPage.tla -- Full cl_page Lifecycle

Models the complete cl_page reference counting, state machine,
vmpage flag management, and seqlock-based fault protection.

**Processes modeled:**
- Write IO: own -> make_ready(PAGEOUT, SetPageWriteback) -> complete(CACHED) -> end_writeback -> transfer_put
  - OR: own -> disown (flush failure / error before submit)
  - Note: the model takes the transfer pin at make_ready.  The code
    takes it at osc_page_cache_add (when the page is queued into an
    extent) and holds it while the page sits CPS_CACHED, so
    TransferPinOnlyDuringIO is a model-level invariant.
- Read IO: own -> submit(PAGEIN) -> complete(CACHED, set uptodate) -> transfer_put
  - OR: own -> disown (error before submit)
- Read Error: own -> submit -> error_complete(CACHED, NO uptodate) -> discard -> delete
  - Models rc!=0 completion: cl_page_discard calls cl_page_delete
    directly (cl_page.c:920) and then generic_error_remove_folio;
    vvp_page_discard only updates readahead statistics (LU-16935)
- Delete: own -> delete(FREEING) -> vvp_page_delete + osc_page_delete (9 fine-grained steps)
- Fault / Buffered Read: seqlock-protected read of page data (LU-16160, LU-16649)
- BL_AST (ENABLE_BL_AST): lock cancellation holding a vmpage
  reference while releasepage runs (LU-16276)

**Bug injection:**
- `INJECT_NO_CLEAR_UPTODATE`: skips ClearPageUptodate in delete (pre-LU-14541)
- `INJECT_NO_SEQLOCK`: removes seqlock from vvp_page_delete (LU-14541 fix v1)
- `INJECT_NO_WB_CHECK`: removes PageWriteback check from delete own (pre-LU-4581)
- `INJECT_NO_ERROR_SEQLOCK`: skips seqlock in error discard path (hypothetical variant; see LU-16935 below)
- `INJECT_NO_READ_SEQLOCK`: reader skips seqlock retry (pre-LU-16649 read())
- `INJECT_EARLY_UNLOCK`: unlock vmpage before io_start in make_ready (LU-16612)
- `INJECT_BUGGY_TRANSFER`: flag clear decoupled from ref drop on weak memory (LU-19956; this is the current tree)
- `INJECT_NO_VMREF_CHECK`: releasepage does not check for a BL_AST-held reference (LU-16276)

**Stale data / SIGBUS bug chain (LU-14541 -> LU-15815 -> LU-16160):**

The model demonstrates a multi-year bug chain where each fix
attempt introduced new issues:

| Phase | Config | Invariant violated | What went wrong |
|-------|--------|-------------------|-----------------|
| Original | LU14541_v0_bug | UptodateRequiresPrivate | No ClearPageUptodate: stale data after reclaim |
| Fix v1 | LU15815_bug | FaultSeesConsistentState | ClearPageUptodate without seqlock: fault SIGBUS |
| Fix v2 | LU14541_v2_fix | (none -- PASS) | Seqlock protects ClearPageUptodate: correct |

**Error discard seqlock (LU-16935):**

The error discard path (read error -> cl_page_discard ->
cl_page_delete -> vvp_page_delete) bumps the seqlock to protect
concurrent faults.  LU-16935 showed this seqlock bump can cause
infinite fault retry loops.  The landed fix (f5564c35ed) bumps the
seqlock only when the page is PageUptodate (vvp_page.c:69-73) and
adds ci_tried_all_mirrors in cl_io_loop to break the retry loop;
the model's uptodate-only bump matches that.  The
INJECT_NO_ERROR_SEQLOCK config is a hypothetical "no bump at all"
variant showing why the seqlock is needed -- without it, faults miss
the invalidation and read stale data.

| Config | Invariant violated | What it shows |
|--------|-------------------|---------------|
| LU16935_bug | FaultSeesConsistentState | Error path without seqlock: fault reads stale data |
| LU16935_fix | (none -- PASS) | Error path with seqlock: fault detects invalidation |

**Buffered read without seqlock (LU-16649):**

The mmap fault path (ll_filemap_fault) had seqlock retry since
LU-16160, but the buffered read() path (vvp_io_read) did not.
A concurrent page deletion during generic_file_read_iter would
cause a short read or EIO to be returned to userspace instead
of being retried.

| Config | Invariant violated | What it shows |
|--------|-------------------|---------------|
| LU16649_bug | FaultSeesConsistentState | read() without seqlock: stale data on delete race |
| LU16649_fix | (none -- PASS) | read() with seqlock retry: detects invalidation |

**Readahead assume vs pageout race (LU-16612):**

Before the fix, `cl_page_make_ready()` called `unlock_page(vmpage)`
before `cl_page_io_start()`, creating a window where the page is
`CPS_OWNED` but the vmpage is unlocked.  During this window,
readahead (`ll_read_ahead_page`) can lock the vmpage and call
`cl_page_assume()`, which LBUGs on the invalid `CPS_OWNED -> CPS_OWNED`
state transition.  The fix (d03b038d0d) keeps the vmpage locked
until after `cl_page_io_start()` sets `CPS_PAGEOUT`.

| Config | Invariant violated | What it shows |
|--------|-------------------|---------------|
| LU16612_bug | OwnedImpliesLocked | Early unlock: CPS_OWNED with vmpage unlocked |
| LU16612_fix | (none -- PASS) | Atomic make_ready: vmpage locked through io_start |

**BL_AST vmpage reference vs releasepage (LU-16276):**

A blocking AST can hold a vmpage reference while the VM calls
releasepage on the same page; if releasepage clears pg_private
anyway, __remove_mapping fails and the page is left with no
cl_page backing.  The modeled "fix" is a reference check in
releasepage.  The page_count-based version of that check
(c524079f4f) was reverted (e3cfb688ed); the guard in the current
tree is do_release_page's cl_page_in_use() on cp_ref (rw26.c:170),
and LU-16276 remains open.  DeleteAbortVmref keys on vmpage_ref,
which is equivalent here only because BlAstGetRef raises cp_ref and
vmpage_ref together.

| Config | Invariant violated | What it shows |
|--------|-------------------|---------------|
| LU16276_bug | VmpageNotRemovedWhileReferenced | BL AST holds vmpage ref while releasepage clears pg_private |
| LU16276_fix | (none -- PASS) | releasepage aborts when a BL AST holds a reference |

**Transfer pin double-put on weak memory (LU-19956):**

The current `osc_completion` clears `ops_transfer_pinned` as a
separate store from the ref drop (`cl_page_put`).  On weakly-ordered
architectures (aarch64), this store can be delayed past the
`cl_page_complete` state change.  Delete then sees `CPS_CACHED` with
`transfer_pinned=TRUE`, calls `transfer_put` (clearing flag + dropping
ref), and completion's unconditional `cl_page_put` double-drops the
ref.  The proposed fix (Gerrit 64440, not merged as of 47638add78)
uses idempotent `transfer_put` that atomically clears flag and ref
together.

Previously modeled only in the standalone TransferPin.tla; now
unified into ClPage for comprehensive lifecycle coverage.

| Config | Invariant violated | What it shows |
|--------|-------------------|---------------|
| LU19956_bug | CleanAfterDelete | Current completion: double ref drop (cp_ref=0 not 1) |
| LU19956_fix | (none -- PASS) | Idempotent transfer_put: flag+ref atomic |

**Three-way race: writeback completion x truncate x fault:**

The three-way race occurs when writeback completes (RPC callback
fires, transitions PAGEOUT->CACHED, clears PageWriteback), truncate
starts (sees CPS_CACHED + !PageWriteback, takes ownership), and a
page fault reads page data -- all concurrently on the same page.

The critical window is between `end_page_writeback` and
`osc_page_transfer_put` in the write completion path.  During this
window, the transfer pin ref is still held but the page appears
"free" (CPS_CACHED, !PageWriteback, !pg_locked).  Truncate can
own and delete the page while the write's transfer_put is pending.
Meanwhile, a fault can read page data under seqlock protection.

Four invariants verify the three-way race properties:

| Invariant | What it checks |
|-----------|---------------|
| WritebackClearRefSafe | After WB clear but before transfer_put, cp_ref >= 2 if pin held |
| NoFaultRestartDuringTruncate | After truncate severs page, fault must retry (seqlock) or be idle |
| NoDoubleCompletion | Write completion cannot re-enter CPS_PAGEOUT in same cycle |
| RefcountSanity | cp_ref = 1 + vvp_ref + transfer_ref + bl_ast_ref at all times |

All interleavings are checked with no violations.  The existing
seqlock mechanism, idempotent transfer_put, and vmpage lock
correctly prevent all three-way race hazards.

Note: before the 2026-09 validation, ClPage.tla defined
PageoutHasWriteback and WritebackWindowConsistency twice, which
SANY rejects, so none of its configs could actually be checked from
the tree as committed.  The duplicates were removed (the earlier,
identical definitions remain) and every config below was rerun.

**All configs** (`run_model.sh ClPage`):

Bug injection configs inject historical bugs and must find
violations (CAUGHT BUG).  Fix configs verify the fix is correct
(PASS).  Both outcomes are expected -- a "CAUGHT BUG" is a
success, proving the model has enough fidelity to find that bug.

| Config file                                  | Result      | What it checks |
|----------------------------------------------|-------------|----------------|
| ClPage__baseline.cfg                         | PASS        | Full lifecycle with fault (write+read+delete+fault) |
| ClPage__baseline_nofault.cfg                 | PASS        | Lifecycle without fault (more IO cycles) |
| ClPage__error_completion.cfg                 | PASS        | Error read completion + fault (LU-16935 context) |
| ClPage__error_nofault.cfg                    | PASS        | Error read completion without fault |
| ClPage__LU14541_v0_bug.cfg                   | CAUGHT BUG  | Original: no ClearPageUptodate (stale data) |
| ClPage__LU14541_v2_fix.cfg                   | PASS        | Final fix: seqlock + ClearPageUptodate |
| ClPage__LU15815_bug.cfg                      | CAUGHT BUG  | Fix v1: ClearPageUptodate without seqlock (SIGBUS) |
| ClPage__LU15815_fix.cfg                      | PASS        | Seqlock resolves LU-15815 SIGBUS |
| ClPage__LU16160_bug.cfg                      | CAUGHT BUG  | No seqlock: fault reads stale uptodate |
| ClPage__LU16160_fix.cfg                      | PASS        | Seqlock protects fault from stale uptodate |
| ClPage__LU16276_bug.cfg                      | CAUGHT BUG  | BL AST holds vmpage ref while releasepage clears pg_private |
| ClPage__LU16276_fix.cfg                      | PASS        | releasepage aborts when a BL AST holds a reference |
| ClPage__LU16612_bug.cfg                      | CAUGHT BUG  | Early unlock: readahead assume on CPS_OWNED |
| ClPage__LU16612_fix.cfg                      | PASS        | Atomic make_ready: no assume race window |
| ClPage__LU16649_bug.cfg                      | CAUGHT BUG  | read() without seqlock: EIO on delete race |
| ClPage__LU16649_fix.cfg                      | PASS        | read() with seqlock retry: detects invalidation |
| ClPage__LU16935_bug.cfg                      | CAUGHT BUG  | Error discard without seqlock: fault misses invalidation |
| ClPage__LU16935_fix.cfg                      | PASS        | Error discard with seqlock: fault detects invalidation |
| ClPage__LU19956_bug.cfg                      | CAUGHT BUG  | Current transfer: flag clear decoupled, double-put |
| ClPage__LU19956_fix.cfg                      | PASS        | Idempotent transfer_put: flag+ref atomic |
| ClPage__LU4581_bug.cfg                       | CAUGHT BUG  | No writeback check: delete during async write |
| ClPage__LU4581_fix.cfg                       | PASS        | Writeback check prevents delete during write |
| ClPage__explore_novel.cfg                    | PASS        | Full concurrency: 2w+2r+fault+error (novel search) |
| ClPage__explore_novel_3w.cfg                 | PASS        | High write concurrency: 3w+2r+fault+error |
| ClPage__explore_novel_3r.cfg                 | PASS        | High read concurrency: 2w+3r+fault+error |
| ClPage__explore_wb_truncate_fault.cfg        | PASS        | Writeback+truncate+fault three-way races, 5 invariants |
| ClPage__threeway_race.cfg                    | PASS        | Three-way race: writeback completion + truncate + fault |
| ClPage__threeway_race_explore.cfg            | PASS        | Three-way race exploration: 2w+2r+fault+error + refcount sanity |
| ClPage__wb_truncate_fault_no_wb_check_bug.cfg | CAUGHT BUG | Delete without writeback check: CPS_FREEING while PageWriteback (LU-4581) |
| ClPage__wb_truncate_fault_no_wb_check_fix.cfg | PASS       | Writeback check in delete prevents CPS_FREEING during writeback |
| ClPage__wb_truncate_fault_no_seqlock_bug.cfg | CAUGHT BUG  | Delete without seqlock: fault misses invalidation (LU-16160) |
| ClPage__wb_truncate_fault_no_seqlock_fix.cfg | PASS        | Seqlock in delete protects fault from stale uptodate |
| ClPage__wb_truncate_fault_no_err_seqlock_bug.cfg | CAUGHT BUG | Error discard without seqlock: fault misses invalidation (LU-16935) |
| ClPage__wb_truncate_fault_no_err_seqlock_fix.cfg | PASS    | Error discard uses seqlock to protect concurrent faults |

## Running

```bash
# Run all configs for a model
cd contrib/formal_models/
./run_model.sh TransferPin
./run_model.sh ClPage

# Verify the LU-19956 fix
./run_model.sh --verify-fix 19956

# Verify the LU-16160 seqlock fix
./run_model.sh --verify-fix 16160

# Run a single config
./run_model.sh --run-cfg clio/TransferPin__GR64440.cfg
```

## How These Models Are Built

### Mapping C Code to TLA+

Each concurrent code path becomes a "process" with a program counter
variable (`write_pc`, `delete_pc`, `fault_pc`, etc.).  Each step
that can be interleaved with another process becomes a separate
TLA+ action.

**Key principle:** A TLA+ action is atomic.  If two C operations
can have another thread run between them, they must be separate
actions.  If they execute on the same CPU with no preemption
point, they can be a single action.

### State Machine Constraints

The cl_page state machine (in `cl_page.c`) constrains which
transitions are legal.  Encode these as preconditions on actions:

```tla
\* Delete can only own when page is CPS_CACHED
DeleteOwn ==
    /\ page_state = "CPS_CACHED"
    /\ ~pg_locked
    /\ page_state' = "CPS_OWNED"
```

State machine constraints are CRITICAL -- they are often the reason
a protocol is correct.  The TransferPin model's key insight is that
`CPS_PAGEOUT -> CPS_FREEING` is forbidden, so delete cannot race
with a page in transfer.

### Reference Counting

Model each ref source as a boolean (held/not held) plus a single
integer `cp_ref` that tracks the sum.  This catches:
- Double-free (ref goes negative)
- Leaked refs (ref > expected after cleanup)
- Use-after-free (accessing freed page)

### Modeling Locks

Locks serialize actions.  Model them as boolean variables that
constrain which actions can fire:

```tla
\* Own requires vmpage not locked (lock_page would block)
WriteOwn ==
    /\ ~pg_locked           \* Would block if locked
    /\ pg_locked' = TRUE    \* Now we hold the lock
```

### Modeling Seqlocks

Seqlocks detect concurrent modifications without blocking.
Model as an integer counter:

```tla
\* Writer: bump sequence (even -> odd -> even)
DeleteExecute ==
    /\ inv_seq' = inv_seq + 2    \* Write-side seqlock

\* Reader: capture seq, do work, check if seq changed
FaultBegin ==
    /\ fault_seq' = inv_seq      \* read_seqbegin
FaultCheck ==
    /\ IF inv_seq # fault_seq
       THEN retry                \* read_seqretry detected change
       ELSE success
```

### Modeling Weak Memory Ordering

TLA+ doesn't natively model memory ordering.  The workaround
is to model reordered stores as separate interleaved actions.
This over-approximates (conservative: more interleavings than
reality) -- if the model passes, the code is correct on all
architectures.

### Choosing Invariants

Start with safety properties derived from code assertions:
- Reference counting: `cp_ref >= 0`, alive pages have refs
- Flag consistency: paired flags stay in sync
- Cleanup: after delete, everything is clean

Then add invariants for specific code assertions (LASSERT):
- The TransferPin model proved an LASSERT can fire in practice

### Keeping Models in Sync with Code

1. **Reference source files** in model headers.  If those
   files change, the model needs review.
2. **Model the bug first.**  A model that finds a known bug
   proves it has sufficient fidelity.
3. **Run configs** when modifying the modeled code paths.
4. **Document the mapping** -- each action comments which C
   function it corresponds to.
