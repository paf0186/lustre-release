// SPDX-License-Identifier: GPL-2.0
/*
 * This file is part of Lustre, http://www.lustre.org/
 *
 * A lockdep for server-side ldlm enqueues.
 *
 * Each operation context (one request handler, or one unit of a server
 * thread's work) records the locks it holds.  A blocking enqueue adds an
 * edge from the class of every held lock to the class being requested; a
 * class is (call site, resource kind, mode, bits).  A new edge that closes
 * a cycle in the class graph is reported once.  Nothing ever blocks or
 * fails the operation, unless ldlm.lockdep=2, which turns a report into an
 * LBUG for test runs.
 *
 * Limits: two locks of one class are not ordered here, chains serialised by
 * a common exclusive BFL are exempt, and client pins are invisible.
 */

#define DEBUG_SUBSYSTEM S_LDLM

#include <linux/hashtable.h>
#include <linux/jhash.h>
#include <linux/kallsyms.h>
#include <linux/sched.h>
#include <linux/stacktrace.h>
#include <linux/vmalloc.h>
#include <lustre_dlm.h>
#include "ldlm_internal.h"

/* 0 off, 1 report, 2 report and LBUG */
int ldlm_lockdep;
static atomic_t lockdep_ncycles = ATOMIC_INIT(0);
static atomic_t lockdep_nrereq = ATOMIC_INIT(0);

#define PRESID(r)	(unsigned long long)(r)->name[0],		\
			(unsigned long long)(r)->name[1],		\
			(unsigned long long)(r)->name[2],		\
			(unsigned long long)(r)->name[3]

/* LDK_REMOTE is or'ed in for a lock taken through OSP */
enum lockdep_kind { LDK_OBJ, LDK_BUCKET, LDK_BFL, LDK_REMOTE = 4 };
static const char * const lockdep_kind_name[] = {
	"obj", "bucket", "bfl", "", "remote obj", "remote bucket", "remote bfl"
};

#define LOCKDEP_EDGES	32
#define LOCKDEP_HELD	16
#define LOCKDEP_DEPTH	16
#define LOCKDEP_RNODES	16384
#define LOCKDEP_REDGES	16
#define LOCKDEP_RDEPTH	4

struct lockdep_class;

struct lockdep_edge {
	struct lockdep_class	*le_to;
	/* the exclusive BFL class held when the edge was made, if any */
	struct lockdep_class	*le_gate;
	struct ldlm_res_id	 le_from_res;
	struct ldlm_res_id	 le_to_res;
};

struct lockdep_class {
	struct hlist_node	 lc_hash;
	u64			 lc_key;
	unsigned long		 lc_site;
	enum lockdep_kind	 lc_kind;
	enum ldlm_mode		 lc_mode;
	__u64			 lc_bits;
	int			 lc_nedges;
	struct lockdep_edge	 lc_edges[LOCKDEP_EDGES];
	/* DFS mark */
	unsigned int		 lc_visit;
};

struct lockdep_held {
	struct ldlm_namespace	*lh_ns;
	struct ldlm_lock	*lh_lock;
	struct lockdep_class	*lh_class;
	struct ldlm_res_id	 lh_res;
};

struct lockdep_ctx {
	struct hlist_node	 lx_hash;
	struct task_struct	*lx_task;
	/* which invocation made an edge: one can wait for one lock only */
	u64			 lx_inv;
	int			 lx_n;
	struct lockdep_held	 lx_held[LOCKDEP_HELD];
};

static DEFINE_HASHTABLE(lockdep_classes, 10);
static DEFINE_HASHTABLE(lockdep_ctxs, 8);
static DEFINE_SPINLOCK(lockdep_lock);
static unsigned int lockdep_visit_gen;
static u64 lockdep_inv_gen;
/* cycles already reported, by the XOR of their class keys */
#define LOCKDEP_SEEN	256
static u64 lockdep_seen[LOCKDEP_SEEN];
static int lockdep_nseen;

/* generic lock helpers are not call sites */
static const char * const lockdep_skip[] = {
	"ldlm_", "lockdep", "osp_md_object_lock", "lod_object_lock",
	"mdd_object_lock", "mdt_object_lock", "mdt_object_local_lock",
	"mdt_object_find_lock", "mdt_reint_object_lock",
	"mdt_remote_object_lock", "mdt_object_pdo_lock", "mdt_parent_lock",
	"mdt_object_check_lock", "mdt_object_lookup_lock", "dt_object_lock",
	"mdt_object_stripes_lock", "mdt_fid_lock",
	"mo_object_lock", "mdo_object_lock", "stack_trace",
};

/* whether each return address seen is in a generic lock helper */
struct lockdep_frame {
	struct hlist_node	 lf_hash;
	unsigned long		 lf_addr;
	bool			 lf_skip;
};

static DEFINE_HASHTABLE(lockdep_frames, 12);
static DEFINE_SPINLOCK(lockdep_frame_lock);

static bool lockdep_frame_skip(unsigned long addr)
{
	char name[KSYM_NAME_LEN];
	struct lockdep_frame *lf;
	unsigned long flags;
	bool skip = false;
	int j;

	spin_lock_irqsave(&lockdep_frame_lock, flags);
	hash_for_each_possible(lockdep_frames, lf, lf_hash, addr)
		if (lf->lf_addr == addr) {
			skip = lf->lf_skip;
			spin_unlock_irqrestore(&lockdep_frame_lock, flags);
			return skip;
		}
	spin_unlock_irqrestore(&lockdep_frame_lock, flags);

	if (!sprint_symbol_no_offset(name, addr))
		return true;
	for (j = 0; j < ARRAY_SIZE(lockdep_skip); j++)
		if (!strncmp(name, lockdep_skip[j], strlen(lockdep_skip[j])))
			skip = true;

	lf = kmalloc(sizeof(*lf), GFP_ATOMIC);
	if (lf) {
		lf->lf_addr = addr;
		lf->lf_skip = skip;
		spin_lock_irqsave(&lockdep_frame_lock, flags);
		hash_add(lockdep_frames, &lf->lf_hash, addr);
		spin_unlock_irqrestore(&lockdep_frame_lock, flags);
	}
	return skip;
}

/* a reloaded module can put other code at a cached address */
static void lockdep_frames_free(void)
{
	struct lockdep_frame *lf;
	struct hlist_node *tmp;
	unsigned long flags;
	int b;

	spin_lock_irqsave(&lockdep_frame_lock, flags);
	hash_for_each_safe(lockdep_frames, b, tmp, lf, lf_hash) {
		hash_del(&lf->lf_hash);
		kfree(lf);
	}
	spin_unlock_irqrestore(&lockdep_frame_lock, flags);
}

static unsigned long lockdep_site(void)
{
	unsigned long trace[LOCKDEP_DEPTH];
	unsigned int n;
	unsigned int i;

	n = stack_trace_save(trace, LOCKDEP_DEPTH, 1);
	for (i = 0; i < n; i++)
		if (!lockdep_frame_skip(trace[i]))
			return trace[i];
	return n ? trace[n - 1] : 0;
}

static enum lockdep_kind lockdep_res_kind(const struct ldlm_res_id *res)
{
	if (res->name[0] == FID_SEQ_SPECIAL &&
	    res->name[1] == FID_OID_SPECIAL_BFL)
		return LDK_BFL;
	return res->name[LUSTRE_RES_ID_HSH_OFF] ? LDK_BUCKET : LDK_OBJ;
}

/* called under lockdep_lock */
static struct lockdep_class *lockdep_class_get(unsigned long site,
					       enum lockdep_kind kind,
					       enum ldlm_mode mode, __u64 bits)
{
	struct lockdep_class *lc;
	u64 key;

	key = jhash_3words((u32)site, (u32)(site >> 32), kind,
			   (u32)mode) ^ ((u64)bits << 32);
	hash_for_each_possible(lockdep_classes, lc, lc_hash, key)
		if (lc->lc_key == key && lc->lc_site == site &&
		    lc->lc_kind == kind && lc->lc_mode == mode &&
		    lc->lc_bits == bits)
			return lc;

	lc = kzalloc(sizeof(*lc), GFP_ATOMIC);
	if (!lc)
		return NULL;
	lc->lc_key = key;
	lc->lc_site = site;
	lc->lc_kind = kind;
	lc->lc_mode = mode;
	lc->lc_bits = bits;
	hash_add(lockdep_classes, &lc->lc_hash, key);
	return lc;
}

/* called under lockdep_lock */
static struct lockdep_ctx *lockdep_ctx_get(bool create)
{
	struct lockdep_ctx *lx;

	hash_for_each_possible(lockdep_ctxs, lx, lx_hash,
			       (unsigned long)current)
		if (lx->lx_task == current)
			return lx;
	if (!create)
		return NULL;
	lx = kzalloc(sizeof(*lx), GFP_ATOMIC);
	if (!lx)
		return NULL;
	lx->lx_task = current;
	lx->lx_inv = ++lockdep_inv_gen;
	hash_add(lockdep_ctxs, &lx->lx_hash, (unsigned long)current);
	return lx;
}

/* not CERROR: a report is several lines and must not be rate limited */
static void lockdep_print_class(const char *pfx, struct lockdep_class *lc,
				const struct ldlm_res_id *res)
{
	pr_err("LustreError: lockdep:   %s %pS %s %s bits %#llx res "DLDLMRES"\n",
	       pfx, (void *)lc->lc_site, lockdep_kind_name[lc->lc_kind],
	       ldlm_lockname[lc->lc_mode], (unsigned long long)lc->lc_bits,
	       PRESID(res));
}

/* called under lockdep_lock; true the first time @sig is seen */
static bool lockdep_first(u64 sig)
{
	int i;

	for (i = 0; i < lockdep_nseen; i++)
		if (lockdep_seen[i] == sig)
			return false;
	if (lockdep_nseen < LOCKDEP_SEEN)
		lockdep_seen[lockdep_nseen++] = sig;
	return true;
}

static bool lockdep_class_same(struct lockdep_class *a,
			       struct lockdep_class *b)
{
	return a->lc_site == b->lc_site && a->lc_mode == b->lc_mode &&
	       a->lc_bits == b->lc_bits &&
	       (a->lc_kind & ~LDK_REMOTE) == (b->lc_kind & ~LDK_REMOTE);
}

/*
 * The resource graph: an edge from a held resource to one then wanted, per
 * invocation.  Class order misses cycles through two locks one helper
 * takes (a rename's parents, a directory's stripes); resources do not.
 */
struct lockdep_redge {
	struct lockdep_rnode	*re_to;
	struct lockdep_class	*re_from_cls;
	struct lockdep_class	*re_to_cls;
	u64			 re_inv;
	bool			 re_gated;
};

struct lockdep_rnode {
	struct hlist_node	 rn_hash;
	struct ldlm_res_id	 rn_res;
	bool			 rn_remote;
	unsigned int		 rn_visit;
	int			 rn_nedges;
	/* the newest LOCKDEP_REDGES edges, oldest overwritten */
	struct lockdep_redge	 rn_edges[LOCKDEP_REDGES];
};

static DEFINE_HASHTABLE(lockdep_rhash, 14);
static struct lockdep_rnode *lockdep_rnodes;
static int lockdep_nrnodes;

static bool lockdep_conflict(struct lockdep_class *a, struct lockdep_class *b)
{
	return !lockmode_compat(a->lc_mode, b->lc_mode) &&
	       (a->lc_bits & b->lc_bits);
}

/* called under lockdep_lock */
static struct lockdep_rnode *lockdep_rnode_get(const struct ldlm_res_id *res,
					       bool remote)
{
	struct lockdep_rnode *rn;
	u32 key = jhash(res, sizeof(*res), remote);

	hash_for_each_possible(lockdep_rhash, rn, rn_hash, key)
		if (rn->rn_remote == remote && ldlm_res_eq(&rn->rn_res, res))
			return rn;
	if (!lockdep_rnodes || lockdep_nrnodes == LOCKDEP_RNODES)
		return NULL;
	rn = &lockdep_rnodes[lockdep_nrnodes++];
	rn->rn_res = *res;
	rn->rn_remote = remote;
	hash_add(lockdep_rhash, &rn->rn_hash, key);
	return rn;
}

static struct lockdep_redge *lockdep_rpath[LOCKDEP_RDEPTH + 1];

/*
 * A path from @rn to @to whose edges are all from different invocations,
 * at most one made under the exclusive BFL, and at most one resource where
 * the holder and the waiter are compatible (a single queued writer), the
 * new edge already in lockdep_rpath[0].
 */
static int lockdep_rsearch(struct lockdep_rnode *rn, struct lockdep_rnode *to,
			   int depth, int gated, int compat, int maxcompat)
{
	int i;
	int j;

	if (rn == to)
		return compat + !lockdep_conflict(lockdep_rpath[0]->re_from_cls,
				lockdep_rpath[depth - 1]->re_to_cls) >
		       maxcompat ? -1 : depth;
	if (depth > LOCKDEP_RDEPTH - 1 || rn->rn_visit == lockdep_visit_gen)
		return -1;
	rn->rn_visit = lockdep_visit_gen;
	for (i = 0; i < min(rn->rn_nedges, LOCKDEP_REDGES); i++) {
		struct lockdep_redge *re = &rn->rn_edges[i];
		int c = compat + !lockdep_conflict(re->re_from_cls,
				lockdep_rpath[depth - 1]->re_to_cls);
		int d;

		if ((re->re_gated && gated) || c > maxcompat)
			continue;
		for (j = 0; j < depth; j++)
			if (lockdep_rpath[j]->re_inv == re->re_inv)
				break;
		if (j < depth)
			continue;
		lockdep_rpath[depth] = re;
		d = lockdep_rsearch(re->re_to, to, depth + 1,
				    gated + re->re_gated, c, maxcompat);
		if (d >= 0)
			return d;
	}
	return -1;
}

/* called under lockdep_lock: @from on @fn is held and @lc on @tn wanted */
static void lockdep_redge_add(struct lockdep_rnode *fn,
			      struct lockdep_class *from,
			      struct lockdep_rnode *tn, struct lockdep_class *lc,
			      u64 inv, bool gated)
{
	struct lockdep_redge *re;
	struct lockdep_rnode *src;
	bool direct = true;
	u64 sig = 0;
	int n;
	int i;

	for (i = 0; i < min(fn->rn_nedges, LOCKDEP_REDGES); i++) {
		re = &fn->rn_edges[i];
		if (re->re_to == tn && re->re_from_cls == from &&
		    re->re_to_cls == lc && re->re_gated == gated) {
			re->re_inv = inv;
			return;
		}
	}
	re = &fn->rn_edges[fn->rn_nedges++ % LOCKDEP_REDGES];
	re->re_to = tn;
	re->re_from_cls = from;
	re->re_to_cls = lc;
	re->re_inv = inv;
	re->re_gated = gated;

	/* a cycle that deadlocks by itself first, then one a writer bridges */
	lockdep_rpath[0] = re;
	lockdep_visit_gen++;
	n = lockdep_rsearch(tn, fn, 1, gated, 0, 0);
	if (n < 0) {
		lockdep_visit_gen++;
		n = lockdep_rsearch(tn, fn, 1, gated, 0, 1);
	}
	if (n < 0)
		return;

	/* at each resource, the edge leaving holds it, the one entering wants */
	for (i = 0; i < n; i++) {
		struct lockdep_redge *in = lockdep_rpath[(i + n - 1) % n];

		if (!lockdep_conflict(lockdep_rpath[i]->re_from_cls,
				      in->re_to_cls))
			direct = false;
		sig += lockdep_rpath[i]->re_from_cls->lc_key * 3 +
		       lockdep_rpath[i]->re_to_cls->lc_key;
	}
	if (!lockdep_first(sig))
		return;

	atomic_inc(&lockdep_ncycles);
	pr_err("LustreError: lockdep: resource cycle of %d edges%s, the last new in %s:%d\n",
	       n, direct ? "" : " (compatible: needs a queued writer)",
	       current->comm, current->pid);
	src = fn;
	for (i = 0; i < n; i++) {
		lockdep_print_class("holds", lockdep_rpath[i]->re_from_cls,
				    &src->rn_res);
		lockdep_print_class(" then", lockdep_rpath[i]->re_to_cls,
				    &lockdep_rpath[i]->re_to->rn_res);
		src = lockdep_rpath[i]->re_to;
	}
	if (ldlm_lockdep > 1 && direct)
		LBUG();
}

/* depth-first search for a path from @from to @to; fills @path */
static int lockdep_path(struct lockdep_class *from, struct lockdep_class *to,
			struct lockdep_edge **path, int depth)
{
	int i;

	if (from == to)
		return depth;
	if (depth >= LOCKDEP_DEPTH || from->lc_visit == lockdep_visit_gen)
		return -1;
	from->lc_visit = lockdep_visit_gen;
	for (i = 0; i < from->lc_nedges; i++) {
		int d;

		path[depth] = &from->lc_edges[i];
		d = lockdep_path(from->lc_edges[i].le_to, to, path, depth + 1);
		if (d >= 0)
			return d;
	}
	return -1;
}

/* called under lockdep_lock, with the new edge @e from @from already added */
static void lockdep_check_cycle(struct lockdep_class *from,
				struct lockdep_edge *e)
{
	struct lockdep_edge *path[LOCKDEP_DEPTH + 1];
	struct lockdep_class *gate;
	struct lockdep_class *src;
	bool shared = true;
	bool exempt;
	u64 sig;
	int n;
	int i;

	lockdep_visit_gen++;
	path[0] = e;
	n = lockdep_path(e->le_to, from, path + 1, 0);
	if (n < 0)
		return;
	n++;

	/* serialised by one exclusive BFL on every edge: not a deadlock */
	gate = path[0]->le_gate;
	exempt = gate != NULL;
	sig = 0;
	for (i = 0; i < n; i++) {
		if (path[i]->le_gate != gate)
			exempt = false;
		if (!(path[i]->le_to->lc_mode & (LCK_PR | LCK_CR)))
			shared = false;
		sig ^= path[i]->le_to->lc_key;
	}
	if (exempt || !lockdep_first(sig))
		return;

	atomic_inc(&lockdep_ncycles);
	pr_err("LustreError: lockdep: lock order cycle of %d edges%s, the first new in %s:%d\n",
	       n, shared ? " (all shared: needs a queued writer)" : "",
	       current->comm, current->pid);
	src = from;
	for (i = 0; i < n; i++) {
		lockdep_print_class("holds", src, &path[i]->le_from_res);
		lockdep_print_class(" then", path[i]->le_to,
				    &path[i]->le_to_res);
		src = path[i]->le_to;
	}
	if (ldlm_lockdep > 1)
		LBUG();
}

/**
 * ldlm_lockdep_acquire() - record a blocking enqueue about to be made
 * @ns: the namespace, a client one for a lock taken through OSP
 * @res: the resource
 * @mode: the mode
 * @bits: the inodebits
 * @blocking: false for a try, which orders nothing
 *
 * Returns the class for ldlm_lockdep_held(), or NULL.
 */
void *ldlm_lockdep_acquire(struct ldlm_namespace *ns,
			   const struct ldlm_res_id *res, enum ldlm_mode mode,
			   __u64 bits, bool blocking)
{
	struct lockdep_class *lc;
	struct lockdep_class *gate = NULL;
	struct lockdep_rnode *tn;
	struct lockdep_ctx *lx;
	unsigned long site;
	unsigned long flags;
	int i;

	if (!ldlm_lockdep)
		return NULL;
	site = lockdep_site();

	spin_lock_irqsave(&lockdep_lock, flags);
	lc = lockdep_class_get(site, lockdep_res_kind(res) |
			       (ns_is_client(ns) ? LDK_REMOTE : 0), mode, bits);
	lx = lockdep_ctx_get(false);
	if (!lc || !lx || !blocking)
		goto out;

	for (i = 0; i < lx->lx_n; i++)
		if ((lx->lx_held[i].lh_class->lc_kind & ~LDK_REMOTE) == LDK_BFL &&
		    lx->lx_held[i].lh_class->lc_mode == LCK_EX)
			gate = lx->lx_held[i].lh_class;

	tn = lockdep_rnode_get(res, ns_is_client(ns));
	for (i = 0; i < lx->lx_n; i++) {
		struct lockdep_held *h = &lx->lx_held[i];
		struct lockdep_class *from = h->lh_class;
		struct lockdep_edge *e;
		int k;

		/* rule 1: a second blocking request on a held resource */
		if (h->lh_ns == ns && ldlm_res_eq(&h->lh_res, res) &&
		    lockdep_first(from->lc_key * 31 + lc->lc_key)) {
			atomic_inc(&lockdep_nrereq);
			pr_err("LustreError: lockdep: second request in %s:%d on held resource "DLDLMRES"\n",
			       current->comm, current->pid, PRESID(res));
			lockdep_print_class("holds", from, &h->lh_res);
			lockdep_print_class(" then", lc, res);
		}

		if (!ldlm_res_eq(&h->lh_res, res) && tn) {
			struct lockdep_rnode *fn;

			fn = lockdep_rnode_get(&h->lh_res,
					       ns_is_client(h->lh_ns));
			if (fn)
				lockdep_redge_add(fn, from, tn, lc, lx->lx_inv,
						  gate != NULL);
		}
		/*
		 * two locks of one class need a declared rule; stripes locked
		 * in index order differ only in being local or remote
		 */
		if (lockdep_class_same(from, lc))
			continue;
		for (k = 0; k < from->lc_nedges; k++)
			if (from->lc_edges[k].le_to == lc &&
			    from->lc_edges[k].le_gate == gate)
				break;
		if (k < from->lc_nedges || from->lc_nedges == LOCKDEP_EDGES)
			continue;
		e = &from->lc_edges[from->lc_nedges++];
		e->le_to = lc;
		e->le_gate = gate;
		e->le_from_res = h->lh_res;
		e->le_to_res = *res;
		lockdep_check_cycle(from, e);
	}
out:
	spin_unlock_irqrestore(&lockdep_lock, flags);
	return lc;
}
EXPORT_SYMBOL(ldlm_lockdep_acquire);

/**
 * ldlm_lockdep_held() - record a lock the context now holds
 * @lock: the granted lock
 * @cls: what ldlm_lockdep_acquire() returned
 */
void ldlm_lockdep_held(struct ldlm_lock *lock, void *cls)
{
	struct lockdep_ctx *lx;
	unsigned long flags;

	if (!ldlm_lockdep || !cls)
		return;
	spin_lock_irqsave(&lockdep_lock, flags);
	lx = lockdep_ctx_get(true);
	if (lx && lx->lx_n < LOCKDEP_HELD) {
		lx->lx_held[lx->lx_n].lh_ns = ldlm_lock_to_ns(lock);
		lx->lx_held[lx->lx_n].lh_lock = lock;
		lx->lx_held[lx->lx_n].lh_class = cls;
		lx->lx_held[lx->lx_n].lh_res = lock->l_resource->lr_name;
		lx->lx_n++;
	}
	spin_unlock_irqrestore(&lockdep_lock, flags);
}
EXPORT_SYMBOL(ldlm_lockdep_held);

/* the context released @lock */
void ldlm_lockdep_release(struct ldlm_lock *lock)
{
	struct lockdep_ctx *lx;
	unsigned long flags;
	int i;

	if (!ldlm_lockdep)
		return;
	spin_lock_irqsave(&lockdep_lock, flags);
	lx = lockdep_ctx_get(false);
	if (lx) {
		for (i = lx->lx_n - 1; i >= 0; i--)
			if (lx->lx_held[i].lh_lock == lock)
				break;
		if (i >= 0) {
			lx->lx_n--;
			memmove(&lx->lx_held[i], &lx->lx_held[i + 1],
				(lx->lx_n - i) * sizeof(lx->lx_held[0]));
		}
	}
	spin_unlock_irqrestore(&lockdep_lock, flags);
}

/*
 * The end of one operation context: locks saved in a reply are released
 * later by another thread, so forget whatever this one still records.
 */
void ldlm_lockdep_ctx_end(void)
{
	struct lockdep_ctx *lx;
	unsigned long flags;

	if (!ldlm_lockdep)
		return;
	spin_lock_irqsave(&lockdep_lock, flags);
	lx = lockdep_ctx_get(false);
	if (lx) {
		hash_del(&lx->lx_hash);
		kfree(lx);
	}
	spin_unlock_irqrestore(&lockdep_lock, flags);
}
EXPORT_SYMBOL(ldlm_lockdep_ctx_end);

int ldlm_lockdep_cycles(void)
{
	return atomic_read(&lockdep_ncycles);
}

int ldlm_lockdep_rerequests(void)
{
	return atomic_read(&lockdep_nrereq);
}

/* print the graph for merging with other servers' */
void ldlm_lockdep_dump(void)
{
	struct lockdep_class *lc;
	unsigned long flags;
	int b;
	int i;

	spin_lock_irqsave(&lockdep_lock, flags);
	hash_for_each(lockdep_classes, b, lc, lc_hash) {
		for (i = 0; i < lc->lc_nedges; i++) {
			struct lockdep_edge *e = &lc->lc_edges[i];

			pr_info("lockdep-edge: %pS|%s|%s|%#llx %pS|%s|%s|%#llx %d "DLDLMRES" "DLDLMRES"\n",
				(void *)lc->lc_site,
				lockdep_kind_name[lc->lc_kind],
				ldlm_lockname[lc->lc_mode],
				(unsigned long long)lc->lc_bits,
				(void *)e->le_to->lc_site,
				lockdep_kind_name[e->le_to->lc_kind],
				ldlm_lockname[e->le_to->lc_mode],
				(unsigned long long)e->le_to->lc_bits,
				e->le_gate != NULL, PRESID(&e->le_from_res),
				PRESID(&e->le_to_res));
		}
	}
	for (b = 0; b < lockdep_nrnodes; b++) {
		struct lockdep_rnode *rn = &lockdep_rnodes[b];

		for (i = 0; i < min(rn->rn_nedges, LOCKDEP_REDGES); i++) {
			struct lockdep_redge *re = &rn->rn_edges[i];

			pr_info("lockdep-redge: %pS|%s|%s|%#llx %pS|%s|%s|%#llx %d %llu "DLDLMRES" "DLDLMRES"\n",
				(void *)re->re_from_cls->lc_site,
				lockdep_kind_name[re->re_from_cls->lc_kind],
				ldlm_lockname[re->re_from_cls->lc_mode],
				(unsigned long long)re->re_from_cls->lc_bits,
				(void *)re->re_to_cls->lc_site,
				lockdep_kind_name[re->re_to_cls->lc_kind],
				ldlm_lockname[re->re_to_cls->lc_mode],
				(unsigned long long)re->re_to_cls->lc_bits,
				re->re_gated, re->re_inv, PRESID(&rn->rn_res),
				PRESID(&re->re_to->rn_res));
		}
	}
	spin_unlock_irqrestore(&lockdep_lock, flags);
}

/* set ldlm.lockdep, forgetting the graph */
int ldlm_lockdep_set(int val)
{
	struct lockdep_rnode *rn;

	if (val && !lockdep_rnodes) {
		rn = vzalloc(LOCKDEP_RNODES * sizeof(*rn));
		if (!rn)
			return -ENOMEM;
		spin_lock(&lockdep_lock);
		if (!lockdep_rnodes)
			swap(lockdep_rnodes, rn);
		spin_unlock(&lockdep_lock);
		vfree(rn);
	}
	ldlm_lockdep = 0;
	ldlm_lockdep_reset();
	lockdep_frames_free();
	ldlm_lockdep = val;
	return 0;
}

void ldlm_lockdep_fini(void)
{
	ldlm_lockdep = 0;
	ldlm_lockdep_reset();
	vfree(lockdep_rnodes);
	lockdep_rnodes = NULL;
	lockdep_frames_free();
}

/* forget the graph, e.g. between tests */
void ldlm_lockdep_reset(void)
{
	struct lockdep_class *lc;
	struct lockdep_ctx *lx;
	struct hlist_node *tmp;
	unsigned long flags;
	int b;

	spin_lock_irqsave(&lockdep_lock, flags);
	hash_for_each_safe(lockdep_classes, b, tmp, lc, lc_hash) {
		hash_del(&lc->lc_hash);
		kfree(lc);
	}
	hash_for_each_safe(lockdep_ctxs, b, tmp, lx, lx_hash) {
		hash_del(&lx->lx_hash);
		kfree(lx);
	}
	lockdep_nseen = 0;
	hash_init(lockdep_rhash);
	if (lockdep_rnodes)
		memset(lockdep_rnodes, 0,
		       lockdep_nrnodes * sizeof(*lockdep_rnodes));
	lockdep_nrnodes = 0;
	atomic_set(&lockdep_ncycles, 0);
	atomic_set(&lockdep_nrereq, 0);
	spin_unlock_irqrestore(&lockdep_lock, flags);
}
