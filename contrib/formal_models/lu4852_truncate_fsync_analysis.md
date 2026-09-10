# LU-4852 Truncate vs Fsync Race Analysis

**Model:** `osc_extent_model.tla` (cfgs `osc_extent_model__LU4852_bug/fix.cfg`)
**Date:** 2026-09-10
**Validated against:** lustre-release master 47638add78 (2026-09-06)
**Verdict:** Live bug in master. The fix landed only on b2_5, and that
fix would not close the path analysed below.

## 1. Summary

`osc_extent_truncate()` asserts that the extent it is about to truncate
is not urgent:

```c
LASSERT(!ext->oe_urgent);           /* osc_cache.c:1046 */
```

A concurrent fsync can set `oe_urgent` on an extent that truncate has
already claimed, after truncate has dropped the object lock and before
the extent reaches `OES_TRUNC`.  Nothing clears `oe_urgent` on that
transition, so the assertion fires.

JIRA LU-4852 reads Resolved/Fixed, which is why this is not on anyone's
list: the fix was applied to b2_5 and the ticket closed on that basis.

## 2. The invariant being violated

An extent in `OES_TRUNC` must not be urgent.  A fsync that arrives while
a truncate is in progress is recorded in `oe_fsync_wait` and honoured
after the truncate finishes, in `osc_cache_truncate_end` (3209-3234):

```c
EASSERT(ext->oe_state == OES_TRUNC, ext);
EASSERT(!ext->oe_urgent, ext);                  /* 3217 */
...
osc_extent_state_set(ext, OES_CACHE);
if (ext->oe_fsync_wait && !ext->oe_urgent) {    /* 3222 */
        ext->oe_urgent = 1;
        list_move_tail(&ext->oe_link, &obj->oo_urgent_exts);
        unplug = true;
}
```

So `oe_fsync_wait` is the correct way to remember a fsync across a
truncate; setting `oe_urgent` during one is the error.

## 3. The race

All line numbers are `lustre/osc/osc_cache.c` at 47638add78 unless
noted.

**T (truncate; holds i_rwsem via notify_change -> ll_setattr_raw)**

`osc_cache_truncate_start` takes the object lock, finds extent E in
`OES_ACTIVE`, and claims it (3118-3126):

```c
if (ext->oe_state == OES_ACTIVE) {
        /* though we grab inode mutex for write path, but we
         * release it before releasing extent(in osc_io_end()),
         * so there is a race window that an extent is still
         * in OES_ACTIVE when truncate starts. */
        LASSERT(!ext->oe_trunc_pending);
        ext->oe_trunc_pending = 1;
}
```

E stays `OES_ACTIVE` with `oe_trunc_pending = 1` and `oe_urgent = 0`.
The object lock is dropped at 3140.  The comment documents the window.

**F (fsync; holds no inode lock)**

`ll_fsync` does not take the inode lock.  It calls
`cl_sync_file_range(inode, start, end, CL_FSYNC_ALL, 0, ...)`, which
reaches `osc_io_fsync_start` (osc_io.c:1094) and then
`osc_cache_writeback_range(env, osc, start, end, 0, 0, prio)` with
`hp = 0` and `discard = 0`.

That loop applies no `oe_trunc_pending` filter.  It sets
`oe_fsync_wait` on every extent in range (3346) and then, for an
`OES_ACTIVE` extent (3401-3407):

```c
case OES_ACTIVE:
        LASSERT(hp == 0 && discard == 0);
        ext->oe_urgent = 1;             /* 3407 */
```

E is now `OES_ACTIVE`, `oe_trunc_pending = 1`, `oe_urgent = 1`.

**W (the writer that was holding E)**

`osc_io_end` -> `osc_extent_release` drops the last user (606-626):

```c
if (ext->oe_trunc_pending) {
        if (ext->oe_state != OES_ACTIVE) {
                ...osc_extent_wait(env, ext, OES_INV);
        }
        osc_extent_state_set(ext, OES_TRUNC);   /* 623 */
        ext->oe_trunc_pending = 0;
```

E is `OES_ACTIVE`, so the inner wait is skipped and E goes straight to
`OES_TRUNC`.  `oe_urgent` is not cleared;
`osc_extent_state_set` (296-307) only stores the state and wakes the
wait queue.

**T resumes**

`osc_extent_wait(env, ext, OES_TRUNC)` (3153) returns at once because E
is already `OES_TRUNC`, then `osc_extent_truncate` hits
`LASSERT(!ext->oe_urgent)` at 1046.  LBUG.

`oe_urgent` is never cleared anywhere: all 22 references to it in
`lustre/osc` and `lustre/mdc` are tests or assignments to 1.  Nothing
can rescue E between 3407 and 1046.

## 4. Why the b2_5 fix does not cover this

Commit 28de66844b (review 10204, on origin/b2_5 only; not an ancestor
of master, and its Change-Id appears on no other commit) adds one
guard, to the kick in `osc_extent_wait` (979-986):

```c
-       if (state == OES_INV && !ext->oe_urgent && !ext->oe_hp) {
+       if (state == OES_INV && !ext->oe_urgent && !ext->oe_hp &&
+           !ext->oe_trunc_pending) {
```

That closes the `osc_extent_wait(..., OES_INV)` route.  It does not
touch `osc_cache_writeback_range`, which sets `oe_urgent` directly at
3407.  That code is byte-identical in the b2_5 tree at 28de66844b, so
the fsync route described in section 3 was open there too.

Forward-porting 28de66844b is therefore necessary but not sufficient.

## 5. Note for whoever writes the fix

`__osc_extent_sanity_check` requires `oe_fsync_wait -> oe_urgent` for
`OES_ACTIVE` extents (187-188, rc 55) and for `OES_CACHE` extents
(193-194, rc 65).  So the obvious patch -- skip the `oe_urgent` set for
`oe_trunc_pending` extents while still setting `oe_fsync_wait` -- trips
a different assertion.

Clearing `oe_urgent` alongside the `OES_TRUNC` transition in
`osc_extent_release` (623) fits the design better: `oe_fsync_wait`
survives, and `osc_cache_truncate_end` re-establishes urgency at 3222
exactly as intended.  Not attempted here.

## 6. Reachability and limits of this analysis

This is static analysis.  The race was not reproduced.

It needs a three-way interleaving on one object: a write that has
released i_rwsem but still holds its extent `OES_ACTIVE`, a truncate
that claims that extent, and a fsync landing between the unlock at 3140
and `osc_extent_release`.  Truncate holds i_rwsem and fsync does not, so
the VFS does not serialise them.  `filemap_invalidate_lock` does not
either: `ci_invalidate_page_cache` is set only by
`osc_lock_discard_pages` (3733), the lock-cancellation path.

The window is narrow, which is consistent with the original report
(iozone, 2014) and with eleven quiet years.

## 7. Model correspondence

`osc_extent_model.tla` reproduces the assertion under
`InjectBug4852 = TRUE`, violating `TruncNotUrgent`:

```
./run_model.sh --verify-fix 4852
```

The model's `InjectBug4852 = FALSE` variant corresponds to the b2_5
code, not to master.  Per section 4 it is a partial fix, and the model
does not currently distinguish the two urgency-setting paths: its Fsync
process stands for `osc_cache_writeback_range` while the historical
injection point is `osc_extent_wait`.  Splitting them would let the
model show that the b2_5 guard alone leaves a violation reachable.
