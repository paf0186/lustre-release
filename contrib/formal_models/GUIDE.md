# Formal Models for Lustre - Usage Guide

## Quick Start

```bash
cd contrib/formal_models/

# Run all configs for a model
./run_model.sh import_model

# Verify a fix catches the bug and the fix resolves it
./run_model.sh import_model --verify-fix 19055

# List all modeled bugs across all models
./run_model.sh --list-bugs

# Run a single cfg file
./run_model.sh --run-cfg clio/TransferPin__GR64440.cfg

# Override timeout (default 1h)
./run_model.sh --timeout 10m --run-cfg clio/ClPage__baseline.cfg
TLC_TIMEOUT=30m ./run_model.sh ClPage
```

### Progress and Timeouts

TLC prints a progress line every ~30 seconds while running:

```
[ClPage__baseline.cfg] (expect: pass)
  Progress: 1,243,891 states (1:00 elapsed)
  Progress: 2,891,034 states (2:00 elapsed)
  PASS (2,891,034 distinct states, 2:12)
```

If TLC is killed by the timeout, you see the last known state count:

```
  TIMEOUT after 60:00 (last: 47,832,109 states generated)
```

If state count stops changing, a stall warning fires after 5 minutes:

```
  WARNING: no new states for 300s -- possibly stuck or at fixpoint
```

If a cfg has `@states: 5M` and TLC exceeds it, the run aborts early:

```
  WARNING: exceeded state budget 5,000,000 (5,243,891 states explored)
           -- model may be unbounded; check CONSTANTS
```

**Environment variables:**

| Variable | Default | Description |
|---|---|---|
| `TLC_TIMEOUT` | `3600` (1h) | Default timeout per cfg |
| `TLC_STATES` | `0` (none) | Default state budget |
| `TLC_WORKERS` | `4` | TLC worker threads |
| `TLA2TOOLS` | (searched: `$HOME`, `/tmp`, `/usr/local/lib`) | Path to tla2tools.jar |

Per-cfg `@timeout` and `@states` tags override the environment defaults.

## Config File Convention

### Naming

Config files follow the pattern `Model__<identifier>.cfg`:

```
model__LUNNNNN_fix.cfg          Fix for LU-NNNNN (expect: pass)
model__LUNNNNN_bug.cfg          Bug reproduction (expect: fail)
model__LUNNNNN_original.cfg     Original broken code (expect: fail)
model__GRNNNNN.cfg              Specific Gerrit change
model__GRNNNNNr2.cfg            Revised version of a Gerrit change
model__LUNNNNN_fix_scenario.cfg Fix under specific conditions
model__baseline.cfg             No bug injection, general safety check
```

The double underscore `__` separates the model name from the
bug/fix identifier. `run_model.sh` uses this to discover cfgs.

### Metadata Tags

Every cfg file has structured metadata as TLA+ comments at the
top. These are machine-parsed by `run_model.sh`:

```
\* @model: TransferPin
\* @lu: 19956
\* @gerrit: 64440
\* @patchset: 9
\* @constant: FIX_VERSION = "v64440"
\* @expect: pass
\* @violated:
\* @description: Landed fix - temp ref, pin cleared while still PAGEOUT
```

Required tags:
- **@model** -- TLA+ spec name (without .tla)
- **@expect** -- `pass` or `fail` (what TLC should do)

Optional tags:
- **@lu** -- JIRA ticket number(s), comma-separated
- **@gerrit** -- Gerrit change number
- **@patchset** -- Gerrit patchset number
- **@constant** -- Which constant(s) this cfg sets to select the
  code variant
- **@violated** -- Which invariant/property TLC should violate
  (for expect: fail)
- **@timeout** -- Override default timeout for this cfg
  (e.g. `30m`, `1h`, `3600`). Use for known-large models.
- **@states** -- State budget; abort and warn if exceeded
  (e.g. `5M`, `10M`). Use to catch unbounded models early.
- **@description** -- Human-readable description

### How It Ties Together

The cfg IS the registry. Each cfg says:
1. Which spec it runs against (@model -> SPECIFICATION)
2. Which code variant it exercises (@constant -> CONSTANTS)
3. Which properties it checks (INVARIANTS, PROPERTIES)
4. What result to expect (@expect)
5. Which bug it relates to (@lu)

`run_model.sh --list-bugs` discovers everything by scanning
metadata tags across all cfg files. No separate index to maintain.

## Using Models to Verify a Fix

### The Pattern

Every modeled bug has at least two cfg files: one that
reproduces the bug (expect: fail) and one that proves the
fix (expect: pass). The `--verify-fix` flag runs both:

```
$ ./run_model.sh --verify-fix 19055
=== Verifying fix for LU-19055 ===

Step 1: Inject bug (should be caught)...
  [import_model__LU19055_bug.cfg] Missing unlock on error path
    CAUGHT BUG (violated: LockNotHeldByDone)
Step 2: Verify fix (should pass)...
  [import_model__LU19055_fix.cfg] Fixed - unlock on error path
    PASS (5094 distinct states found)

=== VERIFIED: Model catches LU-19055 and fix resolves it ===
```

This proves two things:
1. The model is precise enough to detect the bug
2. The fix actually eliminates the violation

### Workflow for a New Bug

Say you're fixing LU-XXXXX, a concurrency bug:

**1. Understand the bug.** What goes wrong? A missing unlock?
A bad state transition? A race between two paths?

**2. Add the bug injection constant** to the TLA+ spec:

```tla
CONSTANTS
    InjectBug19055,
    InjectBugXXXXX    \* <-- new
```

**3. Model the buggy vs fixed behavior.**

Find the right spot in the spec and add a conditional:
```tla
if InjectBugXXXXX then
    \* BUG: describe what goes wrong
    skip
else
    \* FIXED: describe the correct behavior
    imp_lock_holder := "none"
end if
```

**4. Create cfg files with metadata.**

Bug cfg (`model__LUXXXXX_bug.cfg`):
```
\* @model: import_model
\* @lu: XXXXX
\* @constant: InjectBugXXXXX = TRUE
\* @expect: fail
\* @violated: LockNotHeldByDone
\* @description: <what the bug is>
SPECIFICATION Spec

CONSTANTS
    InjectBugXXXXX = TRUE
    ...
```

Fix cfg (`model__LUXXXXX_fix.cfg`):
```
\* @model: import_model
\* @lu: XXXXX
\* @constant: InjectBugXXXXX = FALSE
\* @expect: pass
\* @violated:
\* @description: <what the fix does>
SPECIFICATION Spec

CONSTANTS
    InjectBugXXXXX = FALSE
    ...
```

**5. Verify.**

```bash
./run_model.sh --verify-fix XXXXX
```

**6. Include the output in your commit message.**

```
Verified with formal model:
  $ ./run_model.sh --verify-fix XXXXX
  Step 1: Inject bug... CAUGHT BUG
  Step 2: Verify fix... PASS
```

### Multiple Fix Approaches

When evaluating multiple Gerrit changes for the same bug,
create a cfg per approach. Example from TransferPin/LU-19956:

```
TransferPin__LU19956_original.cfg   Original code (fail)
TransferPin__GR64472.cfg            First attempt (fail - wrong)
TransferPin__GR64472r2.cfg          Revised attempt (pass)
TransferPin__GR64440.cfg            Landed fix (pass)
```

The metadata tells you which ones pass and which fail.
`--verify-fix 19956` runs all of them.

## What Kinds of Bugs Can Be Modeled?

**Good candidates** (the model excels at these):
- Missing lock release on error/early-return paths
- Invalid state transitions (state A should never go to state B)
- Races between concurrent paths (idle vs reconnect, etc.)
- Deadlocks from lock ordering or leaked locks
- Recovery protocol violations (skipping states, going backward)

**Poor candidates** (don't try to model these):
- Memory corruption / use-after-free
- Performance issues
- Data content correctness (checksums, data integrity)
- Anything that depends on specific timing/latency

## Adding a New Model (New Subsystem)

When modeling a new subsystem, follow this template:

**1. Identify the state variable(s)** -- what enum or flag set
defines the subsystem's state?

**2. Identify the concurrent actors** -- which threads/contexts
can modify the state? Each becomes a PlusCal `process`.

**3. Identify the lock(s)** -- model each lock as a variable.

**4. Write the PlusCal** -- one process per actor, with labels
at lock acquire, lock release, and external operations (RPCs).

**5. Define invariants** -- what must always be true?

**6. Start small** -- 2-3 processes, verify it works, then add
complexity. Each process roughly doubles the state space.

**7. Create cfg files** -- at minimum a `__baseline.cfg`. If
modeling a specific bug, create `__LUXXXXX_bug.cfg` and
`__LUXXXXX_fix.cfg` with full metadata.

### PlusCal Gotchas

- No `await` inside macros -- inline lock acquire at each site
- Labels required after `either/or` blocks and before `goto`
- Use `||` for simultaneous assignment: `a := x || b := y`
- Each label = one atomic step = one grain of interleaving
- Too few labels = miss races; too many = state explosion

## Keeping Models in Sync

The model is only useful if it reflects the actual code. Options:

**Per-patch (recommended for bug fixes):** When fixing a
concurrency bug, add it to the model and run `--verify-fix`.
The model grows organically with each bug found.

**Periodic audit:** An agent reads the model and the C code,
diffs them, flags any transitions in the code not in the model.

**Runtime invariants:** Translate model invariants into `LASSERT`
in the C code. Even if the model drifts, the assertions protect
the running code.

## Layout

```
contrib/formal_models/
    run_model.sh            runner
    README.md               overview and model index
    GUIDE.md                this file
    <model>.tla             one spec per protocol
    <model>__<id>.cfg       TLC configs for that spec (see above)
    clio/                   cl_page lifecycle models (ClPage,
                            TransferPin, clio_page_writeback_model)
                            and clio/README.md
    *_analysis.md           model findings checked against the C code
```

`./run_model.sh --list-bugs` prints the current model/bug index.  It
is generated from the cfg metadata, so it is always current; there is
no hand-maintained file list to keep in sync.
