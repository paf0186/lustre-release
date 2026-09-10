# MDS Open/Unlink Orphan Race Analysis

**Model:** `mds_open_unlink_model.tla`
**Date:** 2026-03-13
**Validated against:** lustre-release master 47638add78 (2026-09-06); line references updated
**Verdict:** Safe -- no bug in current code

## 1. What the Model Shows

The TLA+ model (`mds_open_unlink_model.tla`) explores the interaction between
two MDS operations on the same file:

- **Client A** opens the file (`open_count++`)
- **Client B** unlinks the last hard link (`nlink -> 0`)

The safety property (`ReclamationSafety`):
> The inode must not be reclaimed while any client still has it open.

The model's bug-injection mode (`InjectBugOrphan = TRUE`) demonstrates that if
the MDS skips the orphan flag when `nlink` drops to 0 with `open_count > 0`,
the inode is reclaimed immediately -- a use-after-free because Client A still
holds a live file descriptor.

## 2. The Actual C Code

### 2.1 Key Data Structures

The MDD layer tracks open count and orphan state per-inode:

```c
/* mdd_internal.h */
struct mdd_object {
    u32              mod_count;   /* open file descriptor count */
    unsigned long    mod_flags;   /* DEAD_OBJ | ORPHAN_OBJ */
    ...
};

enum mod_flags {
    DEAD_OBJ    = BIT(0),   /* nlink=0; inode is unlinked */
    ORPHAN_OBJ  = BIT(1),   /* inode is in the orphan list */
};
```

The MDT layer has a separate atomic open count (`mot_open_count`) used for
RAoLU (Remove Archive on Last Unlink) policy -- but the **authoritative
orphan decision** uses `mod_count` at the MDD layer.

### 2.2 The Critical Function: `mdd_finish_unlink()`

**File:** `lustre/mdd/mdd_dir.c:2011-2054`

This is the orphan-or-reclaim decision point, called from `mdd_unlink()`:

```c
int mdd_finish_unlink(const struct lu_env *env,
                      struct mdd_object *obj, struct md_attr *ma, ...)
{
    LASSERT(mdd_write_locked(env, obj) != 0);       /* MUST hold write lock */

    if (ma->ma_attr.la_nlink == 0 || is_dir) {
        obj->mod_flags |= DEAD_OBJ;

        if (obj->mod_count) {
            /* ORPHAN PATH: file still open -- defer reclamation */
            rc = mdd_orphan_insert(env, obj, th);
            rc = mdd_mark_orphan_object(env, obj, th, false);
        } else {
            /* RECLAIM PATH: no openers -- destroy immediately */
            rc = mdo_destroy(env, obj, th);
        }
    }
}
```

This corresponds exactly to the model's `DoUnlink` action with
`InjectBugOrphan = FALSE`: when `nlink` reaches 0 and `open_count > 0`,
set the orphan flag and defer reclamation.

### 2.3 Lock Protection Chain

The `DT_TGT_CHILD` write lock on the MDD object serializes **all three**
operations that modify `nlink` or `mod_count`:

| Operation | Lock acquisition | Protected mutation |
|-----------|------------------|--------------------|
| `mdd_open()` (mdd_object.c:3767) | `mdd_write_lock(env, obj, DT_TGT_CHILD)` | `mod_count++` (line 3794) |
| `mdd_unlink()` (mdd_dir.c:2176) | `mdd_write_lock(env, obj, DT_TGT_CHILD)` | `mdo_ref_del` -> nlink-- (line 2261), then `mdd_finish_unlink` checks `mod_count` (line 2027) |
| `mdd_close()` (mdd_object.c:3874) | `mdd_write_lock(env, obj, DT_TGT_CHILD)` | `mod_count--` (line 3965), orphan cleanup if last close |

The entire unlink sequence -- nlink decrement, updated nlink fetch, and the
orphan-or-destroy decision in `mdd_finish_unlink` -- executes under a single
write-lock hold from line 2238 to line 2328 of `mdd_unlink()`.

### 2.4 Why the Race Cannot Happen

The modeled race requires a window where:
1. Client B's unlink reads `open_count` (seeing 0)
2. Client A's open increments `open_count` (to 1)
3. Client B destroys the inode (reclaim with open_count = 1)

This window **does not exist** because:

- When `mdd_finish_unlink` checks `mod_count` at line 2027, the `DT_TGT_CHILD`
  write lock is held (asserted at line 2022).
- Any concurrent `mdd_open` attempting to increment `mod_count` is blocked by
  the same write lock.
- The nlink decrement (line 2261) and `mod_count` check (line 2027) are in the
  **same critical section** -- no interleaving is possible.

### 2.5 Declare Phase

The declare phase (`mdd_declare_finish_unlink`, mdd_dir.c:1985-2009) pre-allocates
transaction credits for **both** possible outcomes:

```c
/* Sigh, we do not know if the unlink object will become orphan in
 * declare phase, but fortunately the flags here does not matter
 * in current declare implementation */
rc = mdd_mark_orphan_object(env, obj, handle, true);   /* declare orphan */
rc = mdo_declare_destroy(env, obj, handle);             /* declare destroy */
rc = mdd_orphan_declare_insert(env, obj, ..., handle);  /* declare insert */
```

Since the declare phase cannot predict which path will execute (that depends on
the runtime value of `mod_count`), it declares credits for both. This is correct
and safe -- the actual decision is deferred to execution time under the write lock.

### 2.6 Close Path (Orphan Cleanup)

`mdd_close()` (mdd_object.c:3874-4070) uses a **double-check locking pattern**:

1. **Lockless pre-check** (line 3903): `mod_count == 1 && (flags & (ORPHAN_OBJ | DEAD_OBJ))`
   -- fast path to skip transaction setup for non-orphans
2. **Locked re-check** (line 3956): Same check under `DT_TGT_CHILD` write lock,
   also including `la_nlink == 0` as fallback (handles `mdd_orphan_insert` failure)
3. **Retry** (line 3960-3962): If the re-check detects orphan status that the
   pre-check missed, releases lock and retries with a transaction handle

Under the write lock, `mod_count--` (line 3965) and the orphan cleanup
(`mdd_orphan_delete` + `mdo_destroy`) happen atomically.

### 2.7 Client Eviction Path

`mdt_export_cleanup()` (mdt_handler.c:7360-7443) processes all open files for
an evicted client:

- Iterates `med_open_head` under `med_open_lock` spinlock
- Calls `mdt_mfd_close()` for each open file descriptor
- During failover (`OBD_OPT_FAILOVER` or `OBDF_STOPPING`), sets `MDS_KEEP_ORPHAN`
  flag to retain orphans in the list for recovery processing

This matches the model's `DoDisconnect` action -- eviction decrements open
count and triggers orphan cleanup if this was the last opener.

### 2.8 Orphan List Assertions

The orphan management functions have strong precondition assertions:

```c
/* mdd_orphan_insert (mdd_orphans.c:149-150) */
LASSERT(mdd_write_locked(env, obj) != 0);
LASSERT(!(obj->mod_flags & ORPHAN_OBJ));  /* not already an orphan */

/* mdd_orphan_delete (mdd_orphans.c:238-240) */
LASSERT(mdd_write_locked(env, obj) != 0);
LASSERT(obj->mod_flags & ORPHAN_OBJ);     /* must be an orphan */
LASSERT(obj->mod_count == 0);             /* all openers must be gone */
```

These assertions would fire (kernel panic in debug builds) if the invariants
modeled in TLA+ were ever violated at runtime.

## 3. Model-to-Code Correspondence

| TLA+ Element | C Code | Notes |
|--------------|--------|-------|
| `open_count` | `mdd_object.mod_count` | u32 at MDD layer |
| `nlink` | `la_attr.la_nlink` | Fetched via `mdd_la_get` after `mdo_ref_del` |
| `is_orphan` | `mod_flags & ORPHAN_OBJ` | Set in `mdd_orphan_insert` |
| `reclaimed` | `mdo_destroy()` called | Irreversible object destruction |
| `DoOpen` | `mdd_open()` | `mod_count++` under write lock |
| `DoClose` | `mdd_close()` | `mod_count--` + orphan cleanup under write lock |
| `DoDisconnect` | `mdt_export_cleanup()` -> `mdt_mfd_close()` -> `mdd_close()` | Same path, with optional `MDS_KEEP_ORPHAN` |
| `DoUnlink` | `mdd_unlink()` -> `mdd_finish_unlink()` | nlink-- and orphan decision under write lock |
| Implicit serialization | `DT_TGT_CHILD` write lock | All actions on same inode are mutually exclusive |

## 4. Conclusion

**The modeled race does not exist in the Lustre code.** The `DT_TGT_CHILD`
write lock on the MDD object provides the serialization that the TLA+ model
assumes via implicit atomicity of each action.

The model is still valuable:
- It documents the **correct invariant** (`ReclamationSafety`) that the lock protects
- The `InjectBugOrphan = TRUE` mode demonstrates what would happen without proper locking
- It provides a regression specification -- if anyone ever changes the locking
  discipline, the TLA+ model shows exactly which safety property would be violated

**No JIRA ticket filed** -- the code correctly implements the orphan protocol.

## 5. Model Annotation

The TLA+ model should be annotated with the lock mapping. See the comment
block added to `mds_open_unlink_model.tla` documenting the `DT_TGT_CHILD`
write lock as the serialization mechanism that makes each TLA+ action atomic
with respect to the others.
