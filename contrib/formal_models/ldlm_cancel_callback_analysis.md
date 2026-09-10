# LDLM Grant-During-Active-Cancel-Callback Race Analysis

**Date:** 2026-03-13 (corrected 2026-03-13)
**Validated against:** lustre-release master 47638add78 (2026-09-06); line references updated
**Model:** ldlm_unified_lifecycle.tla (NoGrantDuringCallback invariant)

## Summary

The `NoGrantDuringCallback` invariant in the `ldlm_unified_lifecycle` TLA+ model
is violated: the server can grant a new lock to a waiting client while the
holder's blocking_ast cancel callback (data flush) is still in progress.

**However, this model violation does NOT correspond to a real bug in the Lustre
C code.** The model incorrectly treats the data writeback as asynchronous. In
reality, when `hp=1` (the cancel path), `osc_cache_writeback_range()` **blocks
synchronously** until all BRW_WRITE RPCs complete before returning. The cancel
RPC is only sent after writeback finishes.

**Verdict: FALSE POSITIVE -- the model's async assumption is wrong; writeback
is synchronous on the cancel path (hp=1)**

## Correction: Why the Writeback Is Synchronous

The original analysis (below) only examined Phase 1 of
`osc_cache_writeback_range()` -- the extent queuing logic. It missed **Phase 2**
(`osc_cache.c:3458-3463`):

```c
if (hp || discard) {
    int rc;
    rc = osc_cache_wait_range(env, obj, start, end);
    if (result >= 0 && rc < 0)
        result = rc;
}
```

When `hp=1`, the function calls `osc_cache_wait_range()`, which iterates over
all extents with `oe_fsync_wait` set and calls `osc_extent_wait(env, ext,
OES_INV)` for each. `osc_extent_wait()` uses `wait_event_idle_timeout()` to
block until each extent reaches state `OES_INV` (write completed).

The actual call chain on the cancel path:

```
osc_lock_flush()                              [osc_lock.c:347]
  -> osc_cache_writeback_range(hp=1)           [osc_cache.c:3316]
      Phase 1: move extents to oo_hp_exts     [line 3365]
      Phase 1: osc_io_unplug()                [line 3456 -- kicks I/O daemon]
      Phase 2: osc_cache_wait_range()         [line 3460 -- BLOCKS]
          -> osc_extent_wait(OES_INV)           [line 3290]
              -> wait_event_idle_timeout()      [line 993 -- sleeps until BRW_WRITE done]
  <- returns ONLY AFTER all dirty data written to server
```

Therefore the cancel RPC is NOT sent before writeback completes. The sequence is:

1. `ldlm_cancel_callback()` -> `osc_lock_flush()` -> **blocks until writes done**
2. `osc_lock_flush()` returns -> BL_DONE set
3. `ldlm_cli_cancel_list()` sends cancel RPC

The dirty data is guaranteed on the server before the cancel RPC arrives.

## Model Deficiency

The TLA+ model treats the callback as a non-blocking flag set:
`h_callback_running := TRUE` (runs) then proceeds without waiting. This allows
`ServerCancel` to race ahead. In reality, the blocking_ast callback on the
cancel path includes a synchronous wait, so the cancel RPC cannot be sent until
the writeback is complete.

To correctly model this, `CancellerA` should not send the cancel RPC
(`h_cancel_rpc_sent`) until after the callback's writeback wait completes.
The `NoGrantDuringCallback` invariant would then hold because the server
cannot see the cancel until data is flushed.

---

## Original Analysis (preserved for reference -- contains errors noted above)

## Original Analysis: The Race in the TLA+ Model

The model defines (lines 699-700):

```tla
NoGrantDuringCallback ==
    h_callback_running => (w_server_grant_calls = 0)
```

The violation path:

1. **CancellerA** sets `h_fl_CANCEL := TRUE` (line 310)
2. **CancellerA** begins callback: `h_callback_running := TRUE` (line 329)
3. **ServerCancel** sees `h_fl_CANCEL`, removes holder: `h_active := FALSE`, signals `reprocess_ready` (lines 484-497)
4. **Reprocessor** sees `~h_active` and `w_list = "waiting"`, grants W: `w_server_grant_calls := 1` (lines 515-520)
5. **CancellerA** callback is still running (`h_callback_running = TRUE`)

The model correctly captures that `ServerCancel` only waits for `h_fl_CANCEL`
(the cancel RPC arrival), NOT for `h_fl_BL_DONE` (callback completion).

## The Race in Lustre C Code

### Architecture: Client-Server Split

The LDLM cancel involves two machines communicating via RPCs:

- **Client side**: Runs the blocking_ast callback (data flush), then sends cancel RPC
- **Server side**: Receives cancel RPC, removes lock, reprocesses waiting queue

There is **no mechanism** for the server to know whether the client's data flush
has completed. The cancel RPC arrival IS the only signal.

### Client-Side Cancel Path

When the server needs a client's lock (conflict with new request):

```
Server                          Client A
  |                               |
  |--- BL_AST RPC --------------> |
  |                               | osc_ldlm_blocking_ast(LDLM_CB_BLOCKING)
  |                               |   -> ldlm_cli_cancel(&lockh, LCF_ASYNC)
  |                               |     -> ldlm_cli_cancel_local(lock)
  |                               |       -> ldlm_cancel_callback(lock)
  |                               |         -> osc_ldlm_blocking_ast(LDLM_CB_CANCELING)
  |                               |           -> osc_dlm_blocking_ast0()
  |                               |             -> osc_lock_flush()
  |                               |               -> osc_cache_writeback_range(hp=1)  <--- ASYNC!
  |                               |                 (queues extents to oo_hp_exts list)
  |                               |               -> osc_lock_discard_pages()
  |                               |                 (discards clean pages, skips in-flight)
  |                               |             <- returns (flush NOT complete)
  |                               |       <- BL_DONE flag set
  |                               |     -> ldlm_lock_cancel(lock)
  |                               |   -> ldlm_cli_cancel_list()
  | <---- CANCEL RPC ------------ |  <--- sent BEFORE writeback completes!
  |                               |
  | ldlm_request_cancel()        |     [async BRW_WRITE RPCs still in flight
  |   -> ldlm_lock_cancel()       |      or not even sent yet]
  |   -> ldlm_reprocess_all()     |
  |     -> grant lock to Client B |
  |                               |
  |--- CP_AST to Client B ------> Client B
  |                               |  reads data -> MAY GET STALE DATA
```

### Key Code Locations

**1. osc_lock_flush()** -- `lustre/osc/osc_lock.c:347-393`

```c
static int osc_lock_flush(struct osc_object *obj, pgoff_t start, pgoff_t end,
                          enum cl_lock_mode mode, bool discard)
{
    /* ... */
    if (mode == CLM_WRITE) {
        rc = osc_cache_writeback_range(env, obj, start, end, 1,
                                       discard, IO_PRIO_NORMAL);
        /* ^^^ hp=1: moves extents to oo_hp_exts list. DOES NOT WAIT. */
    }

    rc2 = osc_lock_discard_pages(env, obj, start, end,
                                  mode == CLM_WRITE || discard);
    /* ^^^ Discards pages from radix tree. Skips in-flight pages. */
    return rc;
}
```

**2. osc_cache_writeback_range()** -- `lustre/osc/osc_cache.c:3316-3482`

For cached extents with `hp=1`: moves them to `oo_hp_exts` list and returns.
Does NOT wait for I/O completion. The OSC I/O daemon picks them up later.

```c
case OES_CACHE:
    if (hp) {
        ext->oe_hp = 1;
        list = &obj->oo_hp_exts;   /* queue for async write */
    }
    if (list != NULL)
        list_move_tail(&ext->oe_link, list);
    unplug = true;                  /* signal daemon */
    break;
```

**3. ldlm_cli_cancel_local()** -- `lustre/ldlm/ldlm_request.c:1382-1423`

Runs the cancel callback synchronously, then returns. The cancel RPC is sent
afterward by `ldlm_cli_cancel_list()`.

```c
static __u64 ldlm_cli_cancel_local(struct ldlm_lock *lock)
{
    lock_res_and_lock(lock);
    ldlm_cancel_callback(lock);     /* runs blocking_ast(CANCELING) */
    /* ... BL_DONE set ... */
    unlock_res_and_lock(lock);
    ldlm_lock_cancel(lock);
    return rc;                      /* caller sends cancel RPC */
}
```

**4. ldlm_request_cancel()** -- `lustre/ldlm/ldlm_lockd.c:1716-1810`

Server processes cancel RPC. Calls reprocess immediately -- no waiting.

```c
int ldlm_request_cancel(struct ptlrpc_request *req,
                        const struct ldlm_request *dlm_req, int first, ...)
{
    for (i = first; i < count; i++) {
        lock = ldlm_handle2lock(&dlm_req->lock_handle[i]);
        /* ... */
        ldlm_lock_cancel(lock);         /* server-side cancel (lightweight) */
    }
    ldlm_reprocess_all(pres, 0);        /* grant waiting locks IMMEDIATELY */
}
```

**5. ldlm_cancel_callback()** -- `lustre/ldlm/ldlm_lock.c:2459-2482`

Sets CANCEL flag, runs blocking_ast, sets BL_DONE. On the server side, the
blocking_ast is lightweight (no data flush). The BL_DONE flag is meaningful
only for local thread synchronization, not cross-node.

```c
void ldlm_cancel_callback(struct ldlm_lock *lock)
{
    if (!(lock->l_flags & LDLM_FL_CANCEL)) {
        lock->l_flags |= LDLM_FL_CANCEL;
        if (lock->l_blocking_ast) {
            unlock_res_and_lock(lock);
            lock->l_blocking_ast(lock, NULL, lock->l_ast_data,
                                 LDLM_CB_CANCELING);
            lock_res_and_lock(lock);
        }
        lock->l_flags |= LDLM_FL_BL_DONE;   /* set AFTER callback returns */
        wake_up(&lock->l_waitq);
    }
}
```

## The Race Window

### Preconditions

- Client A holds a PW (write) extent lock on resource R
- Client A has dirty data in its OSC page cache for the locked extent
- Client B requests a conflicting lock on R

### Sequence

| Step | Actor | Action | State |
|------|-------|--------|-------|
| 1 | Server | Sends BL_AST to Client A | Client A lock marked AST_SENT |
| 2 | Client A | Receives BL_AST, calls `ldlm_cli_cancel` | Cancel process starts |
| 3 | Client A | `ldlm_cancel_callback` -> `osc_lock_flush` | Dirty extents queued to hp_exts (ASYNC) |
| 4 | Client A | `osc_lock_flush` returns | **Writeback NOT complete** |
| 5 | Client A | BL_DONE set, lock unlinked locally | Local cancel done |
| 6 | Client A | Sends CANCEL RPC to server | **Write RPCs may not be sent yet** |
| 7 | Server | `ldlm_lock_cancel(A's lock)` | Lock removed from granted list |
| 8 | Server | `ldlm_reprocess_all(R)` | Waiting queue scanned |
| 9 | Server | `ldlm_grant_lock(B's lock)` | **Client B granted while A's data in flight** |
| 10 | Server | Sends CP_AST to Client B | Client B can now access data |
| 11 | Client A | OSC daemon sends BRW_WRITE RPCs | Data arrives at server (LATE) |

### The Gap

Between steps 6 and 11, the server has already granted Client B's lock (step 9).
Client B may read data from the range before Client A's dirty data arrives at the
server, seeing stale content.

### Why This Is Not Caught by Existing Mechanisms

1. **BL_DONE flag**: Only synchronizes local threads on the same client. The
   server has no visibility into client-side BL_DONE.

2. **PTLRPC ordering**: Write RPCs (OST_IO_PORTAL) and cancel RPCs
   (LDLM_CANCEL_PORTAL) use different portals. No ordering guarantee between
   them. Even on the same connection, different service threads process them.

3. **Server-side ldlm_cancel_callback**: On the server, this runs the server's
   blocking_ast which is lightweight (no data I/O). The server has no way to
   know the client is still flushing.

4. **ldlm_lvbo_update**: Called in `ldlm_request_cancel` for size/KMS updates,
   but does not synchronize with data writes.

## Impact Assessment

### Severity: Medium-High (Data Consistency)

The race can cause:

1. **Stale reads**: Client B reads data from a range that Client A is still
   writing back. Client B sees old data instead of Client A's updates.

2. **Write-write conflicts**: If Client B writes to the same range, the final
   state depends on which writes arrive at the server last -- a classic
   last-writer-wins race without proper ordering.

3. **Torn reads**: Client B may see a mix of old and new data if Client A's
   writeback spans multiple RPCs that are partially complete.

### Conditions Required

- Client A must have **dirty cached data** under the lock being cancelled
- Client B must **read or write the same byte range** quickly after acquiring the lock
- The race window is the time between the cancel RPC arriving at the server and
  Client A's BRW_WRITE RPCs completing at the server

### Mitigating Factors

1. **HP writeback priority**: The extents are queued as high-priority (`oe_hp=1`),
   which causes the OSC daemon to process them before regular I/O. This shrinks
   the race window but does not eliminate it.

2. **Network latency**: The cancel RPC and write RPCs travel over the same network.
   Write RPCs queued first may arrive first in practice. But under load or with
   multiple OSTs, ordering is not guaranteed.

3. **OST write completion**: The OST processes BRW_WRITE RPCs atomically per
   extent. If the write arrives before Client B's read, data is consistent.
   The race requires the read to arrive in the gap.

4. **Practical rarity**: The window is small -- the time between `osc_lock_flush`
   queuing writeback and the BRW_WRITE RPCs completing. Under normal load, this
   is milliseconds. But under heavy contention or network congestion, it widens.

## Related JIRA Tickets

The cancel-callback-reprocess interaction is a known problem area with multiple
related bugs:

| Ticket | Summary | Status | Relevance |
|--------|---------|--------|-----------|
| **LU-18422** | GPF in ldlm_process_inodebits_lock (use-after-free during reprocess from cancel-in-blocking-callback) | Open, Major | Direct |
| **LU-14548** | sanityn 31a hang (voluntary cancel / blocking_ast race test) | Open, Minor | Direct |
| **LU-14522** | Missing lock reprocessing causes timeouts (locks stuck on waiting list) | Resolved | Direct |
| **LU-13692** | MDS hung threads -- reprocess after AST error (the primary reprocess-after-cancel bug) | Resolved | Direct |
| **LU-13201** | Soft lockup in ldlm_reprocess_all (contention storm) | Open, Critical | Direct |
| **LU-16629** | Crash in osd_object_delete via reprocess-cancel-callback chain | Resolved | Direct |
| **LU-13089** | Assertion failed in ldlm_lock_put (glimpse cb vs cancel cb race) | Resolved (Dup) | Direct |
| LU-18671 | Blocking AST flush race -- ESTALE on DoM read during lock revocation | Resolved | Moderate |
| LU-15821 | Blocking callbacks delayed behind LRU cleanup (widens race window) | Resolved | Moderate |
| LU-14582 | Nested LDLM locks cause callback deadlock/eviction | Open | Moderate |

**No existing ticket directly describes the data consistency issue** (stale reads
due to async writeback racing with lock grant). The existing tickets focus on
crashes, hangs, and missed reprocessing -- not the data content race.

## Comparison: Model vs Reality

| Aspect | TLA+ Model | Lustre C Code |
|--------|-----------|---------------|
| Cancel signal | `h_fl_CANCEL` flag | CANCEL RPC over network |
| Callback | `h_callback_running` flag | `osc_lock_flush` + async writeback |
| Server cancel | Same node, reads flag | Different node, receives RPC |
| Reprocess trigger | `reprocess_ready` flag | Immediate after `ldlm_lock_cancel` |
| BL_DONE check | Not checked by Reprocessor | Not checked by `ldlm_reprocess_all` |
| Race window | Between CA_RunCallback and RP_Scan | Between cancel RPC and BRW_WRITE completion |

The model accurately captures the protocol-level race. The real-world
manifestation differs in that the client and server are on separate machines
(making the race harder to detect and fix), and the "callback" involves actual
network I/O (making the window wider than a simple flag-set).

## No Fix Required

The code already implements the correct behavior: `osc_cache_writeback_range()`
with `hp=1` waits for all writeback to complete before returning. This is
exactly what "Option A" below would have recommended -- and it is already in
the code (`osc_cache.c:3458-3463`).

The model needs to be corrected to reflect the synchronous wait on the cancel
path. The `NoGrantDuringCallback` invariant is architecturally sound -- the
Lustre code does in fact ensure it holds.

## Appendix: Key Source Files

| File | Functions |
|------|-----------|
| `lustre/ldlm/ldlm_lockd.c` | `ldlm_handle_cancel`, `ldlm_request_cancel`, `ldlm_bl_to_thread` |
| `lustre/ldlm/ldlm_lock.c` | `ldlm_lock_cancel`, `ldlm_cancel_callback`, `ldlm_reprocess_all`, `ldlm_reprocess_queue`, `ldlm_grant_lock` |
| `lustre/ldlm/ldlm_request.c` | `ldlm_cli_cancel`, `ldlm_cli_cancel_local`, `ldlm_cli_cancel_list` |
| `lustre/ldlm/ldlm_plain.c` | `ldlm_process_plain_lock` |
| `lustre/ldlm/ldlm_internal.h` | `is_bl_done` |
| `lustre/osc/osc_lock.c` | `osc_ldlm_blocking_ast`, `osc_dlm_blocking_ast0`, `osc_lock_flush` |
| `lustre/osc/osc_cache.c` | `osc_cache_writeback_range`, `osc_lock_discard_pages` |
| TLA+ model | `contrib/formal_models/ldlm_unified_lifecycle.tla` |
