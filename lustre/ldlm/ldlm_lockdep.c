// SPDX-License-Identifier: GPL-2.0
/*
 * This file is part of Lustre, http://www.lustre.org/
 *
 * A lock order checker for server-side inodebits enqueues.
 *
 * An operation context (a request handler, or a server thread from its first
 * hold to its last release) records each lock it is granted, with the mode
 * and bits it got.  A request that waits for its grant adds an edge from
 * every held lock to the request in two graphs: one of call sites, and one
 * of resources keyed by the target that owns the lock namespace.  A new edge
 * that closes a cycle is reported, and so is a second waiting request on a
 * resource the context holds (rule 1).  Reports are kept in a bounded table
 * read through debugfs and printed from a worker.  The checker never blocks,
 * fails or panics an operation.
 */

#define DEBUG_SUBSYSTEM S_LDLM

#include <linux/debugfs.h>
#include <linux/hashtable.h>
#include <linux/jhash.h>
#include <linux/kallsyms.h>
#include <linux/sched.h>
#include <linux/seq_file.h>
#ifdef HAVE_STACK_TRACE_SAVE
#include <linux/stacktrace.h>
#endif
#include <linux/utsname.h>
#include <linux/vmalloc.h>
#include <linux/workqueue.h>
#include <lprocfs_status.h>
#include <lustre_dlm.h>
#include <obd.h>
#include "ldlm_internal.h"

#define LOCKDEP_CLASSES		512
#define LOCKDEP_CEDGES		48
#define LOCKDEP_CDEPTH		8
#define LOCKDEP_REDGES		16
#define LOCKDEP_RDEPTH		4
#define LOCKDEP_SHAPES		1024
#define LOCKDEP_REPORTS		256
#define LOCKDEP_PRINT		32
#define LOCKDEP_BUDGET		2048
#define LOCKDEP_CTXS		2048
#define LOCKDEP_HOLDS		16384
#define LOCKDEP_NS		64
#define LOCKDEP_FRAMES		4096
#define LOCKDEP_STACK		16
#define LOCKDEP_LABEL		48
#define LOCKDEP_LINE		512

static unsigned int lockdep_rnodes = 16384;
module_param(lockdep_rnodes, uint, 0644);
MODULE_PARM_DESC(lockdep_rnodes, "resources the lock order checker keeps per epoch");

/* read without lockdep_lock only to skip the checker when it is off */
int ldlm_lockdep;

enum lockdep_kind { LDK_OBJ, LDK_BUCKET, LDK_BFL };
static const char * const lockdep_kind_name[] = { "obj", "bucket", "bfl" };

enum lockdep_check { LDC_CLASS, LDC_RES, LDC_RULE1 };
static const char * const lockdep_check_name[] = {
	"class", "resource", "rule1"
};

enum lockdep_cat {
	LDR_ORDER,
	LDR_ORDER_COMPAT,
	LDR_CONFLICT,
	LDR_BRIDGED,
	LDR_R1_SELF,
	LDR_R1_BRIDGED,
	LDR_R1_UNBRIDGED,
	LDR_NR
};

static const char * const lockdep_cat_name[] = {
	[LDR_ORDER]		= "order",
	[LDR_ORDER_COMPAT]	= "order-compat",
	[LDR_CONFLICT]		= "conflict",
	[LDR_BRIDGED]		= "bridged",
	[LDR_R1_SELF]		= "rule1-self",
	[LDR_R1_BRIDGED]	= "rule1-bridged",
	[LDR_R1_UNBRIDGED]	= "rule1-unbridged",
};

/* the others are kept in the table only */
static const bool lockdep_cat_print[LDR_NR] = {
	[LDR_ORDER]		= true,
	[LDR_CONFLICT]		= true,
	[LDR_BRIDGED]		= true,
	[LDR_R1_SELF]		= true,
	[LDR_R1_BRIDGED]	= true,
};

/* the counters before LDS_LOSSES count evidence the checker dropped */
enum lockdep_stat {
	LDS_REPORTS_FULL,
	LDS_CLASSES_FULL,
	LDS_CEDGES_FULL,
	LDS_RNODES_FULL,
	LDS_REDGES_OVERWRITTEN,
	LDS_SHAPES_FULL,
	LDS_SEARCH_BUDGET,
	LDS_HOLDS_FULL,
	LDS_CTXS_FULL,
	LDS_NS_FULL,
	LDS_STALE,
	LDS_UNSUPPORTED,
	LDS_LOSSES,
	LDS_CEDGES = LDS_LOSSES,
	LDS_REDGES,
	LDS_SEARCHES,
	LDS_HITS,
	LDS_PRINT_SUPPRESSED,
	LDS_DETACH_SAVE,
	LDS_DETACH_END,
	LDS_HOLDS_MAX,
	LDS_NR
};

static const char * const lockdep_stat_name[] = {
	[LDS_REPORTS_FULL]		= "lost_reports_full",
	[LDS_CLASSES_FULL]		= "lost_classes_full",
	[LDS_CEDGES_FULL]		= "lost_class_edges_full",
	[LDS_RNODES_FULL]		= "lost_resources_full",
	[LDS_REDGES_OVERWRITTEN]	= "lost_resource_edges_overwritten",
	[LDS_SHAPES_FULL]		= "lost_shapes_full",
	[LDS_SEARCH_BUDGET]		= "lost_search_budget",
	[LDS_HOLDS_FULL]		= "lost_holds_full",
	[LDS_CTXS_FULL]			= "lost_contexts_full",
	[LDS_NS_FULL]			= "lost_namespaces_full",
	[LDS_STALE]			= "lost_stale_holds",
	[LDS_UNSUPPORTED]		= "lost_unsupported_modes",
	[LDS_CEDGES]			= "class_edges",
	[LDS_REDGES]			= "resource_edges",
	[LDS_SEARCHES]			= "searches",
	[LDS_HITS]			= "report_hits",
	[LDS_PRINT_SUPPRESSED]		= "print_suppressed",
	[LDS_DETACH_SAVE]		= "holds_saved_in_reply",
	[LDS_DETACH_END]		= "holds_left_at_end",
	[LDS_HOLDS_MAX]			= "holds_max",
};

struct lockdep_cedge {
	u16			ce_to;
	u16			ce_from_mode;
	u16			ce_from_bits;
	u16			ce_to_mode;
	u16			ce_to_bits;
	u32			ce_gate;
	/* the first resources seen */
	u32			ce_from_ns;
	u32			ce_to_ns;
	struct ldlm_res_id	ce_from_res;
	struct ldlm_res_id	ce_to_res;
};

/* a call site and the kind of resource locked there */
struct lockdep_class {
	struct hlist_node	lc_hash;
	unsigned long		lc_site;
	u8			lc_kind;
	u8			lc_nedges;
	struct lockdep_cedge	lc_edges[LOCKDEP_CEDGES];
};

/* the two most recent invocations that made the edge */
struct lockdep_redge {
	u32			re_to;
	u32			re_gate;
	u32			re_inv[2];
	u16			re_from_cls;
	u16			re_from_mode;
	u16			re_from_bits;
	u16			re_to_cls;
	u16			re_to_mode;
	u16			re_to_bits;
};

struct lockdep_rnode {
	struct hlist_node	rn_hash;
	struct ldlm_res_id	rn_res;
	u32			rn_ns;
	/* edges ever added; the newest LOCKDEP_REDGES are kept */
	u32			rn_nedges;
	struct lockdep_redge	rn_edges[LOCKDEP_REDGES];
};

/* a request seen queueing: the evidence for a bridge */
struct lockdep_shape {
	struct hlist_node	ls_hash;
	u16			ls_cls;
	u16			ls_mode;
	u16			ls_bits;
	u8			ls_kind;
};

/* one edge of a witness as it is deduplicated */
struct lockdep_key {
	u16			k_from_cls;
	u16			k_from_mode;
	u16			k_from_bits;
	u16			k_to_cls;
	u16			k_to_mode;
	u16			k_to_bits;
};

/* and the resources of its first sighting */
struct lockdep_wit {
	u32			w_from_ns;
	u32			w_to_ns;
	u32			w_inv;
	u32			w_gate;
	struct ldlm_res_id	w_from_res;
	struct ldlm_res_id	w_to_res;
};

/* at a compatible join: what a queued bridge must conflict with */
struct lockdep_need {
	bool			n_set;
	u8			n_kind;
	u16			n_hmode;
	u16			n_hbits;
	u16			n_wmode;
	u16			n_wbits;
};

struct lockdep_report {
	struct hlist_node	rp_hash;
	u32			rp_sig;
	u32			rp_hits;
	u8			rp_check;
	u8			rp_cat;
	u8			rp_n;
	bool			rp_printed;
	struct lockdep_need	rp_need;
	s16			rp_bshape;
	pid_t			rp_pid;
	char			rp_comm[TASK_COMM_LEN];
	struct lockdep_key	rp_key[LOCKDEP_CDEPTH];
	struct lockdep_wit	rp_wit[LOCKDEP_CDEPTH];
};

/* the graphs of one capture epoch */
struct lockdep_gen {
	atomic_t		lg_ref;
	u32			lg_epoch;
	time64_t		lg_start;
	char			lg_label[LOCKDEP_LABEL];
	u32			lg_nrnodes_max;
	u32			lg_nrnodes;
	int			lg_nclasses;
	int			lg_nshapes;
	int			lg_nreports;
	int			lg_nprinted;
	bool			lg_print_due;
	bool			lg_noticed;
	unsigned long		lg_ncat[LDR_NR];
	unsigned long		lg_stat[LDS_NR];
	DECLARE_HASHTABLE(lg_chash, 9);
	DECLARE_HASHTABLE(lg_shash, 10);
	DECLARE_HASHTABLE(lg_phash, 8);
	DECLARE_HASHTABLE(lg_rhash, 14);
	struct lockdep_class	lg_classes[LOCKDEP_CLASSES];
	struct lockdep_shape	lg_shapes[LOCKDEP_SHAPES];
	struct lockdep_report	lg_reports[LOCKDEP_REPORTS];
	struct lockdep_rnode	lg_rnodes[];
};

struct lockdep_ctx;

struct lockdep_hold {
	struct hlist_node	lh_hash;
	struct list_head	lh_list;
	struct lockdep_ctx	*lh_ctx;
	u64			lh_cookie;
	unsigned long		lh_site;
	struct ldlm_res_id	lh_res;
	u32			lh_ns;
	u16			lh_mode;
	u16			lh_bits;
	u8			lh_kind;
	/* lh_cls and lh_rn are indices in epoch lh_epoch */
	u32			lh_epoch;
	int			lh_cls;
	int			lh_rn;
};

/* an empty context is freed, so its next hold starts a new invocation */
struct lockdep_ctx {
	struct hlist_node	lx_hash;
	struct list_head	lx_link;
	struct list_head	lx_holds;
	struct task_struct	*lx_task;
	pid_t			lx_pid;
	u32			lx_inv;
};

/* who holds what; kept across epochs while the checker is on */
struct lockdep_track {
	DECLARE_HASHTABLE(lt_xhash, 10);
	DECLARE_HASHTABLE(lt_hhash, 12);
	struct list_head	lt_free_ctxs;
	struct list_head	lt_free_holds;
	unsigned long		lt_nholds;
	struct lockdep_ctx	lt_ctx[LOCKDEP_CTXS];
	struct lockdep_hold	lt_hold[LOCKDEP_HOLDS];
};

struct lockdep_nsname {
	u32			nn_id;
	char			nn_name[UUID_MAX];
};

/*
 * Every caller runs in process context, and nothing below sleeps, allocates
 * or calls back into ldlm while holding it.
 */
static DEFINE_SPINLOCK(lockdep_lock);
static DEFINE_MUTEX(lockdep_cfg);
static struct lockdep_gen *lockdep_cur;
static struct lockdep_track *lockdep_trk;
static u32 lockdep_epoch;
/* a token from an earlier epoch was issued while the checker was off */
static u32 lockdep_on_since;
static bool lockdep_paused;
static u32 lockdep_inv_next;
static struct lockdep_nsname lockdep_ns[LOCKDEP_NS];
static int lockdep_nns;

static void lockdep_print_fn(struct work_struct *work);
static DECLARE_WORK(lockdep_print_work, lockdep_print_fn);

#define LOCKDEP_RES	(4 * 19 + UUID_MAX + 8)

/* the resource and its namespace, as a FID with the hash after it */
static char *lockdep_res_str(char *buf, const struct ldlm_res_id *res,
			     const char *ns)
{
	snprintf(buf, LOCKDEP_RES, "[0x%llx:0x%llx:0x%llx].0x%llx@%s",
		 (unsigned long long)res->name[0],
		 (unsigned long long)res->name[1],
		 (unsigned long long)res->name[2],
		 (unsigned long long)res->name[3], ns);
	return buf;
}

static bool lockdep_conflict(u16 amode, u16 abits, u16 bmode, u16 bbits)
{
	return !lockmode_compat(amode, bmode) && (abits & bbits);
}

static enum lockdep_kind lockdep_res_kind(const struct ldlm_res_id *res)
{
	if (res->name[0] == FID_SEQ_SPECIAL &&
	    res->name[1] == FID_OID_SPECIAL_BFL)
		return LDK_BFL;
	return res->name[LUSTRE_RES_ID_HSH_OFF] ? LDK_BUCKET : LDK_OBJ;
}

static bool lockdep_mode_supported(u16 mode)
{
	return !(mode & (LCK_GROUP | LCK_COS | LCK_TXN));
}

/* the target owning the namespace: this MDT, or the one OSP talks to */
static u32 lockdep_ns_id(struct ldlm_namespace *ns, const char **name)
{
	struct obd_device *obd = ns->ns_obd;
	const char *uuid;

	if (!obd)
		uuid = ldlm_ns_name(ns);
	else if (ns_is_client(ns))
		uuid = obd->u.cli.cl_target_uuid.uuid;
	else
		uuid = obd->obd_uuid.uuid;
	*name = uuid;
	return jhash(uuid, strnlen(uuid, UUID_MAX), 0) | 1;
}

static u32 lockdep_gate_id(u32 ns, const struct ldlm_res_id *res)
{
	return jhash(res, sizeof(*res), ns) | 1;
}

/* called under lockdep_lock */
static void lockdep_ns_note(struct lockdep_gen *g, u32 id, const char *name)
{
	int i;

	for (i = 0; i < lockdep_nns; i++)
		if (lockdep_ns[i].nn_id == id)
			return;
	if (lockdep_nns == LOCKDEP_NS) {
		g->lg_stat[LDS_NS_FULL]++;
		return;
	}
	lockdep_ns[lockdep_nns].nn_id = id;
	strscpy(lockdep_ns[lockdep_nns].nn_name, name, UUID_MAX);
	lockdep_nns++;
}

/* called under lockdep_lock */
static void lockdep_ns_copy(u32 id, char *name)
{
	int i;

	for (i = 0; i < lockdep_nns; i++)
		if (lockdep_ns[i].nn_id == id) {
			strscpy(name, lockdep_ns[i].nn_name, UUID_MAX);
			return;
		}
	snprintf(name, UUID_MAX, "ns-%#x", id);
}

#ifdef HAVE_STACK_TRACE_SAVE
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
	struct hlist_node	lf_hash;
	unsigned long		lf_addr;
	bool			lf_skip;
};

static DEFINE_HASHTABLE(lockdep_frames, 12);
static DEFINE_SPINLOCK(lockdep_frame_lock);
static int lockdep_nframes;

static bool lockdep_frame_skip(unsigned long addr)
{
	char name[KSYM_SYMBOL_LEN];
	struct lockdep_frame *lf;
	bool skip = false;
	int j;

	spin_lock(&lockdep_frame_lock);
	hash_for_each_possible(lockdep_frames, lf, lf_hash, addr)
		if (lf->lf_addr == addr) {
			skip = lf->lf_skip;
			spin_unlock(&lockdep_frame_lock);
			return skip;
		}
	spin_unlock(&lockdep_frame_lock);

	if (!sprint_symbol_no_offset(name, addr))
		return true;
	for (j = 0; j < ARRAY_SIZE(lockdep_skip); j++)
		if (!strncmp(name, lockdep_skip[j], strlen(lockdep_skip[j])))
			skip = true;

	if (READ_ONCE(lockdep_nframes) >= LOCKDEP_FRAMES)
		return skip;
	lf = kmalloc(sizeof(*lf), GFP_NOWAIT);
	if (lf) {
		lf->lf_addr = addr;
		lf->lf_skip = skip;
		spin_lock(&lockdep_frame_lock);
		hash_add(lockdep_frames, &lf->lf_hash, addr);
		lockdep_nframes++;
		spin_unlock(&lockdep_frame_lock);
	}
	return skip;
}

/* a reloaded module can put other code at a cached address */
static void lockdep_frames_free(void)
{
	struct lockdep_frame *lf;
	struct hlist_node *tmp;
	int b;

	spin_lock(&lockdep_frame_lock);
	hash_for_each_safe(lockdep_frames, b, tmp, lf, lf_hash) {
		hash_del(&lf->lf_hash);
		kfree(lf);
	}
	lockdep_nframes = 0;
	spin_unlock(&lockdep_frame_lock);
}

static unsigned long lockdep_site(void)
{
	unsigned long trace[LOCKDEP_STACK];
	unsigned int n;
	unsigned int i;

	n = stack_trace_save(trace, LOCKDEP_STACK, 1);
	for (i = 0; i < n; i++)
		if (!lockdep_frame_skip(trace[i]))
			return trace[i];
	return n ? trace[n - 1] : 0;
}
#else
/* every call site of a kind is one class */
static unsigned long lockdep_site(void)
{
	return 0;
}

static void lockdep_frames_free(void)
{
}
#endif

/* called under lockdep_lock, like everything that takes a gen below */
static int lockdep_class_get(struct lockdep_gen *g, unsigned long site,
			     u8 kind)
{
	struct lockdep_class *lc;
	u32 key = jhash_2words((u32)site, (u32)((u64)site >> 32), kind);

	hash_for_each_possible(g->lg_chash, lc, lc_hash, key)
		if (lc->lc_site == site && lc->lc_kind == kind)
			return lc - g->lg_classes;
	if (g->lg_nclasses == LOCKDEP_CLASSES) {
		g->lg_stat[LDS_CLASSES_FULL]++;
		return -1;
	}
	lc = &g->lg_classes[g->lg_nclasses++];
	lc->lc_site = site;
	lc->lc_kind = kind;
	hash_add(g->lg_chash, &lc->lc_hash, key);
	return lc - g->lg_classes;
}

static int lockdep_rnode_get(struct lockdep_gen *g, u32 ns,
			     const struct ldlm_res_id *res)
{
	struct lockdep_rnode *rn;
	u32 key = jhash(res, sizeof(*res), ns);

	hash_for_each_possible(g->lg_rhash, rn, rn_hash, key)
		if (rn->rn_ns == ns && ldlm_res_eq(&rn->rn_res, res))
			return rn - g->lg_rnodes;
	if (g->lg_nrnodes == g->lg_nrnodes_max) {
		g->lg_stat[LDS_RNODES_FULL]++;
		return -1;
	}
	rn = &g->lg_rnodes[g->lg_nrnodes++];
	rn->rn_res = *res;
	rn->rn_ns = ns;
	hash_add(g->lg_rhash, &rn->rn_hash, key);
	return rn - g->lg_rnodes;
}

/* one end of an edge: a hold, or a request */
struct lockdep_end {
	struct ldlm_res_id	e_res;
	u32			e_ns;
	int			e_cls;
	int			e_rn;
	u16			e_mode;
	u16			e_bits;
	u8			e_kind;
};

/* a queued request of shape @s blocks a waiter behind a holder */
static bool lockdep_bridges(const struct lockdep_shape *s,
			    const struct lockdep_need *n)
{
	return s->ls_kind == n->n_kind &&
	       lockdep_conflict(s->ls_mode, s->ls_bits, n->n_hmode,
				n->n_hbits) &&
	       lockdep_conflict(s->ls_mode, s->ls_bits, n->n_wmode,
				n->n_wbits);
}

static int lockdep_bridge_find(struct lockdep_gen *g,
			       const struct lockdep_need *n)
{
	int i;

	for (i = 0; i < g->lg_nshapes; i++)
		if (lockdep_bridges(&g->lg_shapes[i], n))
			return i;
	return -1;
}

static void lockdep_shape_add(struct lockdep_gen *g,
			      const struct lockdep_end *e)
{
	struct lockdep_shape *ls;
	u32 key = e->e_cls | e->e_mode << 16 | (u32)e->e_bits << 25;
	int i;

	hash_for_each_possible(g->lg_shash, ls, ls_hash, key)
		if (ls->ls_cls == e->e_cls && ls->ls_mode == e->e_mode &&
		    ls->ls_bits == e->e_bits)
			return;
	if (g->lg_nshapes == LOCKDEP_SHAPES) {
		g->lg_stat[LDS_SHAPES_FULL]++;
		return;
	}
	ls = &g->lg_shapes[g->lg_nshapes];
	ls->ls_cls = e->e_cls;
	ls->ls_mode = e->e_mode;
	ls->ls_bits = e->e_bits;
	ls->ls_kind = e->e_kind;
	hash_add(g->lg_shash, &ls->ls_hash, key);

	/* a report that was waiting for its bridge */
	for (i = 0; i < g->lg_nreports; i++) {
		struct lockdep_report *rp = &g->lg_reports[i];

		if (!rp->rp_need.n_set || rp->rp_bshape >= 0 ||
		    !lockdep_bridges(ls, &rp->rp_need))
			continue;
		rp->rp_bshape = g->lg_nshapes;
		if (rp->rp_cat == LDR_R1_UNBRIDGED) {
			g->lg_ncat[rp->rp_cat]--;
			rp->rp_cat = LDR_R1_BRIDGED;
			g->lg_ncat[rp->rp_cat]++;
		}
		rp->rp_printed = false;
		g->lg_print_due = true;
	}
	g->lg_nshapes++;
}

/* scratch for the one search lockdep_lock allows at a time */
static struct lockdep_key lockdep_kbuf[LOCKDEP_CDEPTH];
static struct lockdep_wit lockdep_wbuf[LOCKDEP_CDEPTH];
static struct lockdep_key lockdep_krot[LOCKDEP_CDEPTH];
static struct lockdep_wit lockdep_wrot[LOCKDEP_CDEPTH];

/* rotate a cycle to start at its least edge */
static void lockdep_canon(int n, struct lockdep_key *key,
			  struct lockdep_wit *wit)
{
	struct lockdep_key *k = lockdep_krot;
	struct lockdep_wit *w = lockdep_wrot;
	int best = 0;
	int r;
	int i;

	for (r = 1; r < n; r++) {
		int c = 0;

		for (i = 0; i < n && !c; i++)
			c = memcmp(&key[(r + i) % n], &key[(best + i) % n],
				   sizeof(*key));
		if (c < 0)
			best = r;
	}
	if (!best)
		return;
	for (i = 0; i < n; i++) {
		k[i] = key[(best + i) % n];
		w[i] = wit[(best + i) % n];
	}
	memcpy(key, k, n * sizeof(*key));
	memcpy(wit, w, n * sizeof(*wit));
}

static struct lockdep_report *
lockdep_report_find(struct lockdep_gen *g, u8 check, int n,
		    const struct lockdep_key *key, u32 *sig)
{
	struct lockdep_report *rp;

	*sig = jhash(key, n * sizeof(*key), check);
	hash_for_each_possible(g->lg_phash, rp, rp_hash, *sig)
		if (rp->rp_sig == *sig && rp->rp_check == check &&
		    rp->rp_n == n &&
		    !memcmp(rp->rp_key, key, n * sizeof(*key)))
			return rp;
	return NULL;
}

static struct lockdep_report *
lockdep_report_add(struct lockdep_gen *g, u32 sig, u8 check, u8 cat, int n,
		   const struct lockdep_key *key,
		   const struct lockdep_wit *wit,
		   const struct lockdep_need *need)
{
	struct lockdep_report *rp;

	if (g->lg_nreports == LOCKDEP_REPORTS) {
		g->lg_stat[LDS_REPORTS_FULL]++;
		return NULL;
	}
	rp = &g->lg_reports[g->lg_nreports++];
	rp->rp_sig = sig;
	rp->rp_hits = 1;
	rp->rp_check = check;
	rp->rp_n = n;
	memcpy(rp->rp_key, key, n * sizeof(*key));
	memcpy(rp->rp_wit, wit, n * sizeof(*wit));
	rp->rp_bshape = -1;
	if (need && need->n_set) {
		rp->rp_need = *need;
		rp->rp_bshape = lockdep_bridge_find(g, need);
		if (rp->rp_bshape >= 0 && cat == LDR_R1_UNBRIDGED)
			cat = LDR_R1_BRIDGED;
	}
	rp->rp_cat = cat;
	rp->rp_pid = current->pid;
	strscpy(rp->rp_comm, current->comm, sizeof(rp->rp_comm));
	hash_add(g->lg_phash, &rp->rp_hash, sig);
	g->lg_ncat[cat]++;
	if (lockdep_cat_print[cat])
		g->lg_print_due = true;
	return rp;
}

/*
 * A cycle through the new edge s_edge[0], back to s_node[0].  Its edges come
 * from different invocations, no two made under one exclusive gate, with
 * s_want compatible joins.  At the join on s_node[i], edge i holds and edge
 * i - 1 waits.
 */
struct lockdep_rsearch {
	struct lockdep_gen	*s_g;
	int			s_budget;
	int			s_want;
	bool			s_done;
	bool			s_hit;
	u32			s_node[LOCKDEP_RDEPTH + 1];
	struct lockdep_redge	*s_edge[LOCKDEP_RDEPTH];
	u32			s_inv[LOCKDEP_RDEPTH];
};

static struct lockdep_rsearch lockdep_rs;

static bool lockdep_rjoin(const struct lockdep_redge *hold,
			  const struct lockdep_redge *wait)
{
	return lockdep_conflict(hold->re_from_mode, hold->re_from_bits,
				wait->re_to_mode, wait->re_to_bits);
}

static void lockdep_rcycle(struct lockdep_rsearch *s, int n)
{
	struct lockdep_gen *g = s->s_g;
	struct lockdep_need need = { .n_set = false };
	struct lockdep_report *rp;
	u32 sig;
	int i;

	for (i = 0; i < n; i++) {
		struct lockdep_redge *re = s->s_edge[i];
		struct lockdep_redge *in = s->s_edge[(i + n - 1) % n];
		struct lockdep_rnode *fn = &g->lg_rnodes[s->s_node[i]];
		struct lockdep_rnode *tn = &g->lg_rnodes[re->re_to];

		lockdep_kbuf[i] = (struct lockdep_key) {
			.k_from_cls	= re->re_from_cls,
			.k_from_mode	= re->re_from_mode,
			.k_from_bits	= re->re_from_bits,
			.k_to_cls	= re->re_to_cls,
			.k_to_mode	= re->re_to_mode,
			.k_to_bits	= re->re_to_bits,
		};
		lockdep_wbuf[i] = (struct lockdep_wit) {
			.w_from_ns	= fn->rn_ns,
			.w_to_ns	= tn->rn_ns,
			.w_inv		= s->s_inv[i],
			.w_gate		= re->re_gate,
			.w_from_res	= fn->rn_res,
			.w_to_res	= tn->rn_res,
		};
		if (!lockdep_rjoin(re, in)) {
			need.n_set = true;
			need.n_kind = lockdep_res_kind(&fn->rn_res);
			need.n_hmode = re->re_from_mode;
			need.n_hbits = re->re_from_bits;
			need.n_wmode = in->re_to_mode;
			need.n_wbits = in->re_to_bits;
		}
	}
	lockdep_canon(n, lockdep_kbuf, lockdep_wbuf);
	rp = lockdep_report_find(g, LDC_RES, n, lockdep_kbuf, &sig);
	if (rp) {
		if (!s->s_hit) {
			rp->rp_hits++;
			g->lg_stat[LDS_HITS]++;
			s->s_hit = true;
		}
		return;
	}
	lockdep_report_add(g, sig, LDC_RES,
			   s->s_want ? LDR_BRIDGED : LDR_CONFLICT, n,
			   lockdep_kbuf, lockdep_wbuf, &need);
	s->s_done = true;
}

static void lockdep_rsearch(struct lockdep_rsearch *s, int d, int compat)
{
	struct lockdep_gen *g = s->s_g;
	struct lockdep_rnode *rn = &g->lg_rnodes[s->s_node[d]];
	int i;

	for (i = 0; i < min_t(u32, rn->rn_nedges, LOCKDEP_REDGES); i++) {
		struct lockdep_redge *re = &rn->rn_edges[i];
		int c = compat + !lockdep_rjoin(re, s->s_edge[d - 1]);
		int j;
		int k;

		if (s->s_done)
			return;
		if (--s->s_budget < 0) {
			g->lg_stat[LDS_SEARCH_BUDGET]++;
			s->s_done = true;
			return;
		}
		if (c > s->s_want)
			continue;
		for (j = 1; j <= d; j++)
			if (s->s_node[j] == re->re_to)
				break;
		if (j <= d)
			continue;
		for (j = 0; j < d; j++)
			if (re->re_gate && re->re_gate == s->s_edge[j]->re_gate)
				break;
		if (j < d)
			continue;
		for (k = 0; k < 2 && !s->s_done; k++) {
			u32 inv = re->re_inv[k];

			if (!inv)
				continue;
			for (j = 0; j < d; j++)
				if (s->s_inv[j] == inv)
					break;
			if (j < d)
				continue;
			s->s_edge[d] = re;
			s->s_inv[d] = inv;
			s->s_node[d + 1] = re->re_to;
			if (re->re_to == s->s_node[0]) {
				if (c + !lockdep_rjoin(s->s_edge[0], re) ==
				    s->s_want)
					lockdep_rcycle(s, d + 1);
			} else if (d + 1 < LOCKDEP_RDEPTH) {
				lockdep_rsearch(s, d + 1, c);
			}
		}
	}
}

/* a cycle with no compatible join first, then one needing a bridge */
static void lockdep_rsearch_run(struct lockdep_gen *g, int from,
				struct lockdep_redge *re, u32 inv)
{
	struct lockdep_rsearch *s = &lockdep_rs;

	s->s_g = g;
	s->s_budget = LOCKDEP_BUDGET;
	s->s_done = false;
	s->s_hit = false;
	s->s_node[0] = from;
	s->s_node[1] = re->re_to;
	s->s_edge[0] = re;
	s->s_inv[0] = inv;
	g->lg_stat[LDS_SEARCHES]++;
	for (s->s_want = 0; s->s_want <= 1 && !s->s_done; s->s_want++)
		lockdep_rsearch(s, 1, 0);
}

static void lockdep_redge_add(struct lockdep_gen *g,
			      const struct lockdep_end *from,
			      const struct lockdep_end *to, u32 inv, u32 gate)
{
	struct lockdep_rnode *fn = &g->lg_rnodes[from->e_rn];
	struct lockdep_redge *re;
	int i;

	for (i = 0; i < min_t(u32, fn->rn_nedges, LOCKDEP_REDGES); i++) {
		re = &fn->rn_edges[i];
		if (re->re_to != to->e_rn || re->re_gate != gate ||
		    re->re_from_cls != from->e_cls ||
		    re->re_from_mode != from->e_mode ||
		    re->re_from_bits != from->e_bits ||
		    re->re_to_cls != to->e_cls ||
		    re->re_to_mode != to->e_mode ||
		    re->re_to_bits != to->e_bits)
			continue;
		if (re->re_inv[0] == inv || re->re_inv[1] == inv)
			return;
		/* a second invocation can make a rejected cycle valid */
		if (!re->re_inv[1]) {
			re->re_inv[1] = inv;
			lockdep_rsearch_run(g, from->e_rn, re, inv);
		} else {
			re->re_inv[0] = re->re_inv[1];
			re->re_inv[1] = inv;
		}
		return;
	}
	if (fn->rn_nedges >= LOCKDEP_REDGES)
		g->lg_stat[LDS_REDGES_OVERWRITTEN]++;
	re = &fn->rn_edges[fn->rn_nedges++ % LOCKDEP_REDGES];
	re->re_to = to->e_rn;
	re->re_gate = gate;
	re->re_inv[0] = inv;
	re->re_inv[1] = 0;
	re->re_from_cls = from->e_cls;
	re->re_from_mode = from->e_mode;
	re->re_from_bits = from->e_bits;
	re->re_to_cls = to->e_cls;
	re->re_to_mode = to->e_mode;
	re->re_to_bits = to->e_bits;
	g->lg_stat[LDS_REDGES]++;
	lockdep_rsearch_run(g, from->e_rn, re, inv);
}

/* as lockdep_rsearch, over call sites, with s_min to s_max compatible joins */
struct lockdep_csearch {
	struct lockdep_gen	*s_g;
	int			s_budget;
	int			s_min;
	int			s_max;
	bool			s_done;
	bool			s_hit;
	u16			s_node[LOCKDEP_CDEPTH + 1];
	struct lockdep_cedge	*s_edge[LOCKDEP_CDEPTH];
};

static struct lockdep_csearch lockdep_cs;

static bool lockdep_cjoin(const struct lockdep_cedge *hold,
			  const struct lockdep_cedge *wait)
{
	return lockdep_conflict(hold->ce_from_mode, hold->ce_from_bits,
				wait->ce_to_mode, wait->ce_to_bits);
}

static void lockdep_ccycle(struct lockdep_csearch *s, int n, int compat)
{
	struct lockdep_gen *g = s->s_g;
	struct lockdep_report *rp;
	u32 sig;
	int i;

	for (i = 0; i < n; i++) {
		struct lockdep_cedge *ce = s->s_edge[i];

		lockdep_kbuf[i] = (struct lockdep_key) {
			.k_from_cls	= s->s_node[i],
			.k_from_mode	= ce->ce_from_mode,
			.k_from_bits	= ce->ce_from_bits,
			.k_to_cls	= ce->ce_to,
			.k_to_mode	= ce->ce_to_mode,
			.k_to_bits	= ce->ce_to_bits,
		};
		lockdep_wbuf[i] = (struct lockdep_wit) {
			.w_from_ns	= ce->ce_from_ns,
			.w_to_ns	= ce->ce_to_ns,
			.w_gate		= ce->ce_gate,
			.w_from_res	= ce->ce_from_res,
			.w_to_res	= ce->ce_to_res,
		};
	}
	lockdep_canon(n, lockdep_kbuf, lockdep_wbuf);
	rp = lockdep_report_find(g, LDC_CLASS, n, lockdep_kbuf, &sig);
	if (rp) {
		if (!s->s_hit) {
			rp->rp_hits++;
			g->lg_stat[LDS_HITS]++;
			s->s_hit = true;
		}
		return;
	}
	lockdep_report_add(g, sig, LDC_CLASS,
			   compat ? LDR_ORDER_COMPAT : LDR_ORDER, n,
			   lockdep_kbuf, lockdep_wbuf, NULL);
	s->s_done = true;
}

static void lockdep_csearch(struct lockdep_csearch *s, int d, int compat)
{
	struct lockdep_gen *g = s->s_g;
	struct lockdep_class *lc = &g->lg_classes[s->s_node[d]];
	int i;

	for (i = 0; i < lc->lc_nedges; i++) {
		struct lockdep_cedge *ce = &lc->lc_edges[i];
		int c = compat + !lockdep_cjoin(ce, s->s_edge[d - 1]);
		int j;

		if (s->s_done)
			return;
		if (--s->s_budget < 0) {
			g->lg_stat[LDS_SEARCH_BUDGET]++;
			s->s_done = true;
			return;
		}
		if (c > s->s_max)
			continue;
		for (j = 1; j <= d; j++)
			if (s->s_node[j] == ce->ce_to)
				break;
		if (j <= d)
			continue;
		for (j = 0; j < d; j++)
			if (ce->ce_gate && ce->ce_gate == s->s_edge[j]->ce_gate)
				break;
		if (j < d)
			continue;
		s->s_edge[d] = ce;
		s->s_node[d + 1] = ce->ce_to;
		if (ce->ce_to == s->s_node[0]) {
			c += !lockdep_cjoin(s->s_edge[0], ce);
			if (c >= s->s_min && c <= s->s_max)
				lockdep_ccycle(s, d + 1, c);
		} else if (d + 1 < LOCKDEP_CDEPTH) {
			lockdep_csearch(s, d + 1, c);
		}
	}
}

static void lockdep_cedge_add(struct lockdep_gen *g,
			      const struct lockdep_end *from,
			      const struct lockdep_end *to, u32 gate)
{
	struct lockdep_class *lc = &g->lg_classes[from->e_cls];
	struct lockdep_csearch *s = &lockdep_cs;
	struct lockdep_cedge *ce;
	int i;

	for (i = 0; i < lc->lc_nedges; i++) {
		ce = &lc->lc_edges[i];
		if (ce->ce_to == to->e_cls && ce->ce_gate == gate &&
		    ce->ce_from_mode == from->e_mode &&
		    ce->ce_from_bits == from->e_bits &&
		    ce->ce_to_mode == to->e_mode &&
		    ce->ce_to_bits == to->e_bits)
			return;
	}
	if (lc->lc_nedges == LOCKDEP_CEDGES) {
		g->lg_stat[LDS_CEDGES_FULL]++;
		return;
	}
	ce = &lc->lc_edges[lc->lc_nedges++];
	ce->ce_to = to->e_cls;
	ce->ce_from_mode = from->e_mode;
	ce->ce_from_bits = from->e_bits;
	ce->ce_to_mode = to->e_mode;
	ce->ce_to_bits = to->e_bits;
	ce->ce_gate = gate;
	ce->ce_from_ns = from->e_ns;
	ce->ce_to_ns = to->e_ns;
	ce->ce_from_res = from->e_res;
	ce->ce_to_res = to->e_res;
	g->lg_stat[LDS_CEDGES]++;

	s->s_g = g;
	s->s_budget = LOCKDEP_BUDGET;
	s->s_done = false;
	s->s_hit = false;
	s->s_node[0] = from->e_cls;
	s->s_node[1] = to->e_cls;
	s->s_edge[0] = ce;
	g->lg_stat[LDS_SEARCHES]++;
	s->s_min = 0;
	s->s_max = 0;
	lockdep_csearch(s, 1, 0);
	if (s->s_done)
		return;
	s->s_min = 1;
	s->s_max = LOCKDEP_CDEPTH;
	lockdep_csearch(s, 1, 0);
}

/* a second waiting request on a resource the context holds */
static void lockdep_rule1(struct lockdep_gen *g,
			  const struct lockdep_end *have,
			  const struct lockdep_end *want)
{
	struct lockdep_key key = {
		.k_from_cls	= have->e_cls,
		.k_from_mode	= have->e_mode,
		.k_from_bits	= have->e_bits,
		.k_to_cls	= want->e_cls,
		.k_to_mode	= want->e_mode,
		.k_to_bits	= want->e_bits,
	};
	struct lockdep_wit wit = {
		.w_from_ns	= have->e_ns,
		.w_to_ns	= want->e_ns,
		.w_from_res	= have->e_res,
		.w_to_res	= want->e_res,
	};
	struct lockdep_need need = {
		.n_set		= true,
		.n_kind		= want->e_kind,
		.n_hmode	= have->e_mode,
		.n_hbits	= have->e_bits,
		.n_wmode	= want->e_mode,
		.n_wbits	= want->e_bits,
	};
	struct lockdep_report *rp;
	u32 sig;

	rp = lockdep_report_find(g, LDC_RULE1, 1, &key, &sig);
	if (rp) {
		rp->rp_hits++;
		g->lg_stat[LDS_HITS]++;
		return;
	}
	if (lockdep_conflict(have->e_mode, have->e_bits, want->e_mode,
			     want->e_bits))
		lockdep_report_add(g, sig, LDC_RULE1, LDR_R1_SELF, 1, &key,
				   &wit, NULL);
	else
		lockdep_report_add(g, sig, LDC_RULE1, LDR_R1_UNBRIDGED, 1,
				   &key, &wit, &need);
}

static struct lockdep_ctx *lockdep_ctx_find(struct lockdep_track *t)
{
	struct lockdep_ctx *lx;

	hash_for_each_possible(t->lt_xhash, lx, lx_hash,
			       (unsigned long)current)
		if (lx->lx_task == current && lx->lx_pid == current->pid)
			return lx;
	return NULL;
}

static struct lockdep_hold *lockdep_hold_find(struct lockdep_track *t,
					      u64 cookie)
{
	struct lockdep_hold *lh;

	hash_for_each_possible(t->lt_hhash, lh, lh_hash, cookie)
		if (lh->lh_cookie == cookie)
			return lh;
	return NULL;
}

static void lockdep_hold_put(struct lockdep_track *t, struct lockdep_hold *lh)
{
	struct lockdep_ctx *lx = lh->lh_ctx;

	hash_del(&lh->lh_hash);
	list_move(&lh->lh_list, &t->lt_free_holds);
	t->lt_nholds--;
	if (list_empty(&lx->lx_holds)) {
		hash_del(&lx->lx_hash);
		list_add(&lx->lx_link, &t->lt_free_ctxs);
	}
}

static void lockdep_hold_end(struct lockdep_gen *g, struct lockdep_hold *lh,
			     struct lockdep_end *e)
{
	if (lh->lh_epoch != g->lg_epoch) {
		lh->lh_epoch = g->lg_epoch;
		lh->lh_cls = lockdep_class_get(g, lh->lh_site, lh->lh_kind);
		lh->lh_rn = lockdep_rnode_get(g, lh->lh_ns, &lh->lh_res);
	}
	e->e_res = lh->lh_res;
	e->e_ns = lh->lh_ns;
	e->e_cls = lh->lh_cls;
	e->e_rn = lh->lh_rn;
	e->e_mode = lh->lh_mode;
	e->e_bits = lh->lh_bits;
	e->e_kind = lh->lh_kind;
}

/* @lx waits for @want while holding everything on its list */
static void lockdep_wait(struct lockdep_gen *g, struct lockdep_ctx *lx,
			 struct lockdep_end *want)
{
	struct lockdep_hold *lh;
	u32 gate = 0;

	list_for_each_entry(lh, &lx->lx_holds, lh_list)
		if (lh->lh_kind == LDK_BFL && lh->lh_mode == LCK_EX)
			gate = lockdep_gate_id(lh->lh_ns, &lh->lh_res);

	want->e_rn = lockdep_rnode_get(g, want->e_ns, &want->e_res);
	list_for_each_entry(lh, &lx->lx_holds, lh_list) {
		struct lockdep_end have;

		if (!lockdep_mode_supported(lh->lh_mode)) {
			g->lg_stat[LDS_UNSUPPORTED]++;
			continue;
		}
		lockdep_hold_end(g, lh, &have);
		if (have.e_cls < 0)
			continue;
		if (have.e_ns == want->e_ns &&
		    ldlm_res_eq(&have.e_res, &want->e_res)) {
			lockdep_rule1(g, &have, want);
			continue;
		}
		/* stripes locked in index order at one site are one class */
		if (have.e_cls != want->e_cls)
			lockdep_cedge_add(g, &have, want, gate);
		if (have.e_rn >= 0 && want->e_rn >= 0)
			lockdep_redge_add(g, &have, want, lx->lx_inv, gate);
	}
}

/**
 * ldlm_lockdep_acquire() - record a request about to be enqueued
 * @tok: filled in for ldlm_lockdep_held()
 * @ns: the namespace, a client one for a lock taken through OSP
 * @res: the resource
 * @mode: the mode
 * @policy: the inodebits; only the mandatory ones can wait
 * @flags: the enqueue flags
 * @completion: the completion callback; only ldlm_completion_ast() waits
 */
void ldlm_lockdep_acquire(struct ldlm_lockdep_token *tok,
			  struct ldlm_namespace *ns,
			  const struct ldlm_res_id *res, enum ldlm_mode mode,
			  const union ldlm_policy_data *policy, __u64 flags,
			  ldlm_completion_callback completion)
{
	struct lockdep_end want;
	struct lockdep_ctx *lx;
	struct lockdep_gen *g;
	const char *nsname;
	bool queues;
	bool due = false;

	tok->ldt_epoch = 0;
	if (!READ_ONCE(ldlm_lockdep))
		return;

	/* a try, or a request with only optional bits, never queues */
	queues = policy->l_inodebits.bits && !(flags & LDLM_FL_BLOCK_NOWAIT);
	tok->ldt_site = lockdep_site();
	want.e_res = *res;
	want.e_ns = lockdep_ns_id(ns, &nsname);
	want.e_mode = mode;
	want.e_bits = policy->l_inodebits.bits;
	want.e_kind = lockdep_res_kind(res);

	spin_lock(&lockdep_lock);
	g = lockdep_cur;
	if (!g)
		goto out;
	tok->ldt_epoch = lockdep_epoch;
	if (lockdep_paused || !queues)
		goto out;
	if (!lockdep_mode_supported(mode)) {
		g->lg_stat[LDS_UNSUPPORTED]++;
		goto out;
	}
	lockdep_ns_note(g, want.e_ns, nsname);
	want.e_cls = lockdep_class_get(g, tok->ldt_site, want.e_kind);
	if (want.e_cls < 0)
		goto out;
	lockdep_shape_add(g, &want);
	/* an asynchronous request queues, but the context does not wait */
	if (completion != ldlm_completion_ast)
		goto out;
	lx = lockdep_ctx_find(lockdep_trk);
	if (lx)
		lockdep_wait(g, lx, &want);
out:
	if (g) {
		due = g->lg_print_due;
		g->lg_print_due = false;
	}
	spin_unlock(&lockdep_lock);
	if (due)
		schedule_work(&lockdep_print_work);
}
EXPORT_SYMBOL(ldlm_lockdep_acquire);

/**
 * ldlm_lockdep_held() - record a lock the context now holds
 * @lock: the lock, recorded only if it is granted
 * @tok: from ldlm_lockdep_acquire()
 */
void ldlm_lockdep_held(struct ldlm_lock *lock,
		       const struct ldlm_lockdep_token *tok)
{
	struct lockdep_track *t;
	struct lockdep_hold *lh;
	struct lockdep_ctx *lx;
	struct ldlm_res_id res;
	enum ldlm_mode mode;
	const char *nsname;
	bool granted;
	u64 bits;
	u32 ns;

	if (!tok->ldt_epoch)
		return;
	lock_res_and_lock(lock);
	granted = ldlm_is_granted(lock);
	mode = lock->l_granted_mode;
	bits = lock->l_policy_data.l_inodebits.bits;
	res = lock->l_resource->lr_name;
	unlock_res_and_lock(lock);
	if (!granted)
		return;
	ns = lockdep_ns_id(ldlm_lock_to_ns(lock), &nsname);

	spin_lock(&lockdep_lock);
	t = lockdep_trk;
	if (!t)
		goto out;
	if (tok->ldt_epoch < lockdep_on_since) {
		lockdep_cur->lg_stat[LDS_STALE]++;
		goto out;
	}
	lx = lockdep_ctx_find(t);
	if (!lx) {
		if (list_empty(&t->lt_free_ctxs)) {
			lockdep_cur->lg_stat[LDS_CTXS_FULL]++;
			goto out;
		}
		lx = list_first_entry(&t->lt_free_ctxs, struct lockdep_ctx,
				      lx_link);
		list_del(&lx->lx_link);
		lx->lx_task = current;
		lx->lx_pid = current->pid;
		lx->lx_inv = ++lockdep_inv_next ?: ++lockdep_inv_next;
		hash_add(t->lt_xhash, &lx->lx_hash, (unsigned long)current);
	}
	if (list_empty(&t->lt_free_holds)) {
		lockdep_cur->lg_stat[LDS_HOLDS_FULL]++;
		if (list_empty(&lx->lx_holds)) {
			hash_del(&lx->lx_hash);
			list_add(&lx->lx_link, &t->lt_free_ctxs);
		}
		goto out;
	}
	lh = list_first_entry(&t->lt_free_holds, struct lockdep_hold, lh_list);
	list_move_tail(&lh->lh_list, &lx->lx_holds);
	lh->lh_ctx = lx;
	lh->lh_cookie = lock->l_handle.h_cookie;
	lh->lh_site = tok->ldt_site;
	lh->lh_res = res;
	lh->lh_ns = ns;
	lh->lh_mode = mode;
	lh->lh_bits = bits;
	lh->lh_kind = lockdep_res_kind(&res);
	lh->lh_epoch = 0;
	hash_add(t->lt_hhash, &lh->lh_hash, lh->lh_cookie);
	if (++t->lt_nholds > lockdep_cur->lg_stat[LDS_HOLDS_MAX])
		lockdep_cur->lg_stat[LDS_HOLDS_MAX] = t->lt_nholds;
out:
	spin_unlock(&lockdep_lock);
}
EXPORT_SYMBOL(ldlm_lockdep_held);

/* the last reference to @lock went; called with the lock's resource locked */
void ldlm_lockdep_release(struct ldlm_lock *lock)
{
	struct lockdep_hold *lh;

	if (!READ_ONCE(ldlm_lockdep))
		return;
	spin_lock(&lockdep_lock);
	if (lockdep_trk) {
		lh = lockdep_hold_find(lockdep_trk, lock->l_handle.h_cookie);
		if (lh)
			lockdep_hold_put(lockdep_trk, lh);
	}
	spin_unlock(&lockdep_lock);
}

/* bits dropped or the mode downgraded; called with the resource locked */
void ldlm_lockdep_update(struct ldlm_lock *lock)
{
	struct lockdep_hold *lh;

	if (!READ_ONCE(ldlm_lockdep))
		return;
	spin_lock(&lockdep_lock);
	if (lockdep_trk) {
		lh = lockdep_hold_find(lockdep_trk, lock->l_handle.h_cookie);
		if (lh) {
			lh->lh_mode = lock->l_granted_mode;
			lh->lh_bits = lock->l_policy_data.l_inodebits.bits;
		}
	}
	spin_unlock(&lockdep_lock);
}

/**
 * ldlm_lockdep_detach() - the lock is saved in a reply
 * @lockh: its handle
 *
 * The reply's ACK or commit releases it, independently of the operation.
 */
void ldlm_lockdep_detach(const struct lustre_handle *lockh)
{
	struct lockdep_hold *lh;

	if (!READ_ONCE(ldlm_lockdep))
		return;
	spin_lock(&lockdep_lock);
	if (lockdep_trk) {
		lh = lockdep_hold_find(lockdep_trk, lockh->cookie);
		if (lh) {
			lockdep_cur->lg_stat[LDS_DETACH_SAVE]++;
			lockdep_hold_put(lockdep_trk, lh);
		}
	}
	spin_unlock(&lockdep_lock);
}
EXPORT_SYMBOL(ldlm_lockdep_detach);

/*
 * The end of a request: what the context still holds was handed to the
 * client or to the reply, and is released later by another thread.
 */
void ldlm_lockdep_ctx_end(void)
{
	struct lockdep_hold *lh;
	struct lockdep_hold *tmp;
	struct lockdep_ctx *lx;

	if (!READ_ONCE(ldlm_lockdep))
		return;
	spin_lock(&lockdep_lock);
	if (lockdep_trk) {
		lx = lockdep_ctx_find(lockdep_trk);
		if (lx)
			list_for_each_entry_safe(lh, tmp, &lx->lx_holds,
						 lh_list) {
				lockdep_cur->lg_stat[LDS_DETACH_END]++;
				lockdep_hold_put(lockdep_trk, lh);
			}
	}
	spin_unlock(&lockdep_lock);
}
EXPORT_SYMBOL(ldlm_lockdep_ctx_end);

/* a report with the names it needs, copied out of the gen for printing */
struct lockdep_copy {
	struct lockdep_report	c_rp;
	u32			c_epoch;
	int			c_idx;
	unsigned long		c_site[LOCKDEP_CDEPTH][2];
	u8			c_kind[LOCKDEP_CDEPTH][2];
	char			c_ns[LOCKDEP_CDEPTH][2][UUID_MAX];
	unsigned long		c_bsite;
	u16			c_bmode;
	u16			c_bbits;
	char			c_res[2][LOCKDEP_RES];
	char			c_line[LOCKDEP_LINE];
};

static void lockdep_copy(struct lockdep_gen *g, int idx,
			 struct lockdep_copy *c)
{
	struct lockdep_report *rp = &g->lg_reports[idx];
	int i;

	c->c_rp = *rp;
	c->c_epoch = g->lg_epoch;
	c->c_idx = idx;
	for (i = 0; i < rp->rp_n; i++) {
		struct lockdep_class *from;
		struct lockdep_class *to;

		from = &g->lg_classes[rp->rp_key[i].k_from_cls];
		to = &g->lg_classes[rp->rp_key[i].k_to_cls];
		c->c_site[i][0] = from->lc_site;
		c->c_kind[i][0] = from->lc_kind;
		c->c_site[i][1] = to->lc_site;
		c->c_kind[i][1] = to->lc_kind;
		lockdep_ns_copy(rp->rp_wit[i].w_from_ns, c->c_ns[i][0]);
		lockdep_ns_copy(rp->rp_wit[i].w_to_ns, c->c_ns[i][1]);
	}
	if (rp->rp_bshape >= 0) {
		struct lockdep_shape *ls = &g->lg_shapes[rp->rp_bshape];

		c->c_bsite = g->lg_classes[ls->ls_cls].lc_site;
		c->c_bmode = ls->ls_mode;
		c->c_bbits = ls->ls_bits;
	}
}

static void lockdep_format(struct lockdep_copy *c,
			   void (*emit)(void *arg, const char *line),
			   void *arg)
{
	struct lockdep_report *rp = &c->c_rp;
	char *s = c->c_line;
	int len;
	int i;

	len = scnprintf(s, LOCKDEP_LINE,
			"report=%u.%d check=%s category=%s edges=%d hits=%u first=%s:%d",
			c->c_epoch, c->c_idx, lockdep_check_name[rp->rp_check],
			lockdep_cat_name[rp->rp_cat], rp->rp_n, rp->rp_hits,
			rp->rp_comm, rp->rp_pid);
	if (rp->rp_need.n_set && rp->rp_bshape >= 0)
		scnprintf(s + len, LOCKDEP_LINE - len,
			  " bridge=%pS/%s/%s/%#x", (void *)c->c_bsite,
			  lockdep_kind_name[rp->rp_need.n_kind],
			  ldlm_lockname[c->c_bmode], c->c_bbits);
	else if (rp->rp_need.n_set)
		scnprintf(s + len, LOCKDEP_LINE - len,
			  " bridge=none-seen/%s/%s/%#x/%s/%#x",
			  lockdep_kind_name[rp->rp_need.n_kind],
			  ldlm_lockname[rp->rp_need.n_hmode],
			  rp->rp_need.n_hbits,
			  ldlm_lockname[rp->rp_need.n_wmode],
			  rp->rp_need.n_wbits);
	emit(arg, s);
	for (i = 0; i < rp->rp_n; i++) {
		struct lockdep_key *k = &rp->rp_key[i];
		struct lockdep_wit *w = &rp->rp_wit[i];

		scnprintf(s, LOCKDEP_LINE,
			  "  edge=%d holds %pS %s %s %#x %s wants %pS %s %s %#x %s inv=%u gate=%#x",
			  i, (void *)c->c_site[i][0],
			  lockdep_kind_name[c->c_kind[i][0]],
			  ldlm_lockname[k->k_from_mode], k->k_from_bits,
			  lockdep_res_str(c->c_res[0], &w->w_from_res,
					  c->c_ns[i][0]),
			  (void *)c->c_site[i][1],
			  lockdep_kind_name[c->c_kind[i][1]],
			  ldlm_lockname[k->k_to_mode], k->k_to_bits,
			  lockdep_res_str(c->c_res[1], &w->w_to_res,
					  c->c_ns[i][1]),
			  w->w_inv, w->w_gate);
		emit(arg, s);
	}
}

static void lockdep_emit_console(void *arg, const char *line)
{
	pr_warn("Lustre: lockdep: %s\n", line);
}

static void lockdep_emit_seq(void *arg, const char *line)
{
	seq_printf(arg, "%s\n", line);
}

static void lockdep_print_fn(struct work_struct *work)
{
	struct lockdep_copy *c;

	c = kmalloc(sizeof(*c), GFP_KERNEL);
	if (!c)
		return;
	for (;;) {
		struct lockdep_gen *g;
		bool notice = false;
		int found = -1;
		int i;

		spin_lock(&lockdep_lock);
		g = lockdep_cur;
		for (i = 0; g && i < g->lg_nreports; i++) {
			struct lockdep_report *rp = &g->lg_reports[i];

			if (rp->rp_printed || !lockdep_cat_print[rp->rp_cat])
				continue;
			rp->rp_printed = true;
			if (g->lg_nprinted == LOCKDEP_PRINT) {
				g->lg_stat[LDS_PRINT_SUPPRESSED]++;
				notice = !g->lg_noticed;
				g->lg_noticed = true;
				continue;
			}
			g->lg_nprinted++;
			lockdep_copy(g, i, c);
			found = i;
			break;
		}
		spin_unlock(&lockdep_lock);
		if (notice)
			pr_warn("Lustre: lockdep: further reports are only in ldlm.lockdep_reports\n");
		if (found < 0)
			break;
		lockdep_format(c, lockdep_emit_console, NULL);
	}
	kfree(c);
}

static struct lockdep_gen *lockdep_gen_alloc(u32 nrnodes, const char *label)
{
	struct lockdep_gen *g;

	g = vzalloc(struct_size(g, lg_rnodes, nrnodes));
	if (!g)
		return NULL;
	atomic_set(&g->lg_ref, 1);
	g->lg_nrnodes_max = nrnodes;
	g->lg_start = ktime_get_real_seconds();
	strscpy(g->lg_label, label, sizeof(g->lg_label));
	return g;
}

/* not under lockdep_lock: vfree() can sleep */
static void lockdep_gen_put(struct lockdep_gen *g)
{
	if (g && atomic_dec_and_test(&g->lg_ref))
		vfree(g);
}

static struct lockdep_gen *lockdep_gen_get(void)
{
	struct lockdep_gen *g;

	spin_lock(&lockdep_lock);
	g = lockdep_cur;
	if (g)
		atomic_inc(&g->lg_ref);
	spin_unlock(&lockdep_lock);
	return g;
}

static struct lockdep_track *lockdep_track_alloc(void)
{
	struct lockdep_track *t;
	int i;

	t = vzalloc(sizeof(*t));
	if (!t)
		return NULL;
	INIT_LIST_HEAD(&t->lt_free_ctxs);
	INIT_LIST_HEAD(&t->lt_free_holds);
	for (i = 0; i < LOCKDEP_CTXS; i++) {
		INIT_LIST_HEAD(&t->lt_ctx[i].lx_holds);
		list_add_tail(&t->lt_ctx[i].lx_link, &t->lt_free_ctxs);
	}
	for (i = 0; i < LOCKDEP_HOLDS; i++)
		list_add_tail(&t->lt_hold[i].lh_list, &t->lt_free_holds);
	return t;
}

static u32 lockdep_nrnodes(void)
{
	return clamp_t(u32, READ_ONCE(lockdep_rnodes), 16, 1U << 20);
}

/* ldlm.lockdep: turning it on starts epoch "", off forgets everything */
int ldlm_lockdep_set(int val)
{
	struct lockdep_track *t = NULL;
	struct lockdep_gen *g = NULL;
	struct lockdep_track *oldt;
	struct lockdep_gen *oldg;

	mutex_lock(&lockdep_cfg);
	if (!!val == !!ldlm_lockdep)
		goto out;
	if (val) {
		g = lockdep_gen_alloc(lockdep_nrnodes(), "");
		t = lockdep_track_alloc();
		if (!g || !t) {
			vfree(t);
			lockdep_gen_put(g);
			mutex_unlock(&lockdep_cfg);
			return -ENOMEM;
		}
	}
	lockdep_frames_free();
	spin_lock(&lockdep_lock);
	oldg = lockdep_cur;
	oldt = lockdep_trk;
	lockdep_cur = g;
	lockdep_trk = t;
	lockdep_epoch++;
	if (g) {
		g->lg_epoch = lockdep_epoch;
		lockdep_on_since = lockdep_epoch;
		lockdep_paused = false;
		lockdep_nns = 0;
	}
	WRITE_ONCE(ldlm_lockdep, !!val);
	spin_unlock(&lockdep_lock);
	vfree(oldt);
	lockdep_gen_put(oldg);
out:
	mutex_unlock(&lockdep_cfg);
	return 0;
}

/*
 * ldlm.lockdep_epoch: start new graphs, keeping the holds.  A test sets the
 * same label on every server before its actors run.
 */
int ldlm_lockdep_new_epoch(const char *label)
{
	struct lockdep_gen *old;
	struct lockdep_gen *g;
	int rc = 0;

	mutex_lock(&lockdep_cfg);
	if (!ldlm_lockdep) {
		rc = -ENODEV;
		goto out;
	}
	g = lockdep_gen_alloc(lockdep_nrnodes(), label);
	if (!g) {
		rc = -ENOMEM;
		goto out;
	}
	spin_lock(&lockdep_lock);
	old = lockdep_cur;
	g->lg_epoch = ++lockdep_epoch;
	lockdep_cur = g;
	spin_unlock(&lockdep_lock);
	lockdep_gen_put(old);
out:
	mutex_unlock(&lockdep_cfg);
	return rc;
}

int ldlm_lockdep_epoch_show(char *buf, size_t size)
{
	int rc;

	spin_lock(&lockdep_lock);
	if (lockdep_cur)
		rc = scnprintf(buf, size, "%u %s\n", lockdep_cur->lg_epoch,
			       lockdep_cur->lg_label);
	else
		rc = scnprintf(buf, size, "0\n");
	spin_unlock(&lockdep_lock);
	return rc;
}

/* ldlm.lockdep_pause: keep tracking holds, add nothing to the graphs */
void ldlm_lockdep_pause(bool pause)
{
	spin_lock(&lockdep_lock);
	lockdep_paused = pause;
	spin_unlock(&lockdep_lock);
}

bool ldlm_lockdep_paused(void)
{
	return READ_ONCE(lockdep_paused);
}

static unsigned long lockdep_ncat(int a, int b, int c)
{
	unsigned long n = 0;

	spin_lock(&lockdep_lock);
	if (lockdep_cur)
		n = lockdep_cur->lg_ncat[a] + lockdep_cur->lg_ncat[b] +
		    (c < 0 ? 0 : lockdep_cur->lg_ncat[c]);
	spin_unlock(&lockdep_lock);
	return n;
}

/* the cycles and rule 1 reports worth a look, in this epoch */
unsigned long ldlm_lockdep_cycles(void)
{
	return lockdep_ncat(LDR_ORDER, LDR_CONFLICT, LDR_BRIDGED);
}

unsigned long ldlm_lockdep_rerequests(void)
{
	return lockdep_ncat(LDR_R1_SELF, LDR_R1_BRIDGED, -1);
}

void ldlm_lockdep_fini(void)
{
	ldlm_lockdep_set(0);
	cancel_work_sync(&lockdep_print_work);
	lockdep_frames_free();
}

struct lockdep_stats {
	u32			ls_epoch;
	char			ls_label[LOCKDEP_LABEL];
	unsigned long		ls_stat[LDS_NR];
	unsigned long		ls_ncat[LDR_NR];
	unsigned long		ls_holds;
	u32			ls_nrnodes;
	u32			ls_nrnodes_max;
	int			ls_nclasses;
	int			ls_nshapes;
	int			ls_nreports;
	bool			ls_paused;
};

static int lockdep_stats_seq_show(struct seq_file *m, void *v)
{
	struct lockdep_stats *st;
	bool complete = true;
	int i;

	st = kzalloc(sizeof(*st), GFP_KERNEL);
	if (!st)
		return -ENOMEM;
	spin_lock(&lockdep_lock);
	if (lockdep_cur) {
		struct lockdep_gen *g = lockdep_cur;

		st->ls_epoch = g->lg_epoch;
		memcpy(st->ls_label, g->lg_label, sizeof(st->ls_label));
		memcpy(st->ls_stat, g->lg_stat, sizeof(st->ls_stat));
		memcpy(st->ls_ncat, g->lg_ncat, sizeof(st->ls_ncat));
		st->ls_holds = lockdep_trk->lt_nholds;
		st->ls_nrnodes = g->lg_nrnodes;
		st->ls_nrnodes_max = g->lg_nrnodes_max;
		st->ls_nclasses = g->lg_nclasses;
		st->ls_nshapes = g->lg_nshapes;
		st->ls_nreports = g->lg_nreports;
		st->ls_paused = lockdep_paused;
	}
	spin_unlock(&lockdep_lock);

	for (i = 0; i < LDS_LOSSES; i++)
		if (st->ls_stat[i])
			complete = false;
	seq_printf(m, "enabled: %d\n", READ_ONCE(ldlm_lockdep));
	seq_printf(m, "epoch: %u\n", st->ls_epoch);
	seq_printf(m, "label: %s\n", st->ls_label);
	seq_printf(m, "paused: %d\n", st->ls_paused);
	seq_printf(m, "complete: %d\n", complete);
#ifdef HAVE_STACK_TRACE_SAVE
	seq_puts(m, "call_sites: 1\n");
#else
	seq_puts(m, "call_sites: 0\n");
#endif
	seq_printf(m, "classes: %d/%d\n", st->ls_nclasses, LOCKDEP_CLASSES);
	seq_printf(m, "resources: %u/%u\n", st->ls_nrnodes,
		   st->ls_nrnodes_max);
	seq_printf(m, "shapes: %d/%d\n", st->ls_nshapes, LOCKDEP_SHAPES);
	seq_printf(m, "reports: %d/%d\n", st->ls_nreports, LOCKDEP_REPORTS);
	seq_printf(m, "holds: %lu/%d\n", st->ls_holds, LOCKDEP_HOLDS);
	for (i = 0; i < LDR_NR; i++)
		seq_printf(m, "%s: %lu\n", lockdep_cat_name[i], st->ls_ncat[i]);
	for (i = 0; i < LDS_NR; i++)
		seq_printf(m, "%s: %lu\n", lockdep_stat_name[i],
			   st->ls_stat[i]);
	kfree(st);
	return 0;
}
LDEBUGFS_SEQ_FOPS_RO(lockdep_stats);

/* the reports, or the graphs, of the epoch current at open */
struct lockdep_seq {
	struct lockdep_gen	*q_g;
	int			q_nreports;
	int			q_nclasses;
	u32			q_nrnodes;
	int			q_nns;
	struct lockdep_nsname	q_ns[LOCKDEP_NS];
	char			q_nsbuf[2][UUID_MAX];
	char			q_res[2][LOCKDEP_RES];
	union {
		struct lockdep_copy	q_copy;
		struct {
			struct lockdep_class	q_cls;
			unsigned long		q_to_site[LOCKDEP_CEDGES];
			u8			q_to_kind[LOCKDEP_CEDGES];
		};
		struct {
			struct lockdep_rnode	q_rn;
			unsigned long		q_rsite[LOCKDEP_REDGES][2];
			u8			q_rkind[LOCKDEP_REDGES][2];
			struct ldlm_res_id	q_rres[LOCKDEP_REDGES];
			u32			q_rns[LOCKDEP_REDGES];
		};
	};
};

static int lockdep_seq_open(struct inode *inode, struct file *file,
			    const struct seq_operations *ops)
{
	struct lockdep_seq *q;
	int rc;

	q = kvzalloc(sizeof(*q), GFP_KERNEL);
	if (!q)
		return -ENOMEM;
	q->q_g = lockdep_gen_get();
	spin_lock(&lockdep_lock);
	if (q->q_g) {
		q->q_nreports = q->q_g->lg_nreports;
		q->q_nclasses = q->q_g->lg_nclasses;
		q->q_nrnodes = q->q_g->lg_nrnodes;
	}
	q->q_nns = lockdep_nns;
	memcpy(q->q_ns, lockdep_ns, sizeof(q->q_ns));
	spin_unlock(&lockdep_lock);

	rc = seq_open(file, ops);
	if (rc) {
		lockdep_gen_put(q->q_g);
		kvfree(q);
		return rc;
	}
	((struct seq_file *)file->private_data)->private = q;
	return 0;
}

static int lockdep_seq_release(struct inode *inode, struct file *file)
{
	struct seq_file *m = file->private_data;
	struct lockdep_seq *q = m->private;

	lockdep_gen_put(q->q_g);
	kvfree(q);
	return seq_release(inode, file);
}

/* resource @i of a line: its text, with the name of namespace @id */
static char *lockdep_seq_res(struct lockdep_seq *q, int i,
			     const struct ldlm_res_id *res, u32 id)
{
	const char *ns = q->q_nsbuf[i];
	int j;

	snprintf(q->q_nsbuf[i], UUID_MAX, "ns-%#x", id);
	for (j = 0; j < q->q_nns; j++)
		if (q->q_ns[j].nn_id == id)
			ns = q->q_ns[j].nn_name;
	return lockdep_res_str(q->q_res[i], res, ns);
}

static void lockdep_seq_header(struct seq_file *m, const char *what)
{
	struct lockdep_seq *q = m->private;

	if (!q->q_g) {
		seq_printf(m, "# lockdep %s: off\n", what);
		return;
	}
	seq_printf(m, "# lockdep %s node=%s version=%s epoch=%u label=%s start=%lld\n",
		   what, init_utsname()->nodename, LUSTRE_VERSION_STRING,
		   q->q_g->lg_epoch, q->q_g->lg_label, q->q_g->lg_start);
}

static void *lockdep_reports_start(struct seq_file *m, loff_t *pos)
{
	struct lockdep_seq *q = m->private;

	return *pos <= q->q_nreports ? pos : NULL;
}

static void *lockdep_reports_next(struct seq_file *m, void *v, loff_t *pos)
{
	++*pos;
	return lockdep_reports_start(m, pos);
}

static void lockdep_seq_stop(struct seq_file *m, void *v)
{
}

static int lockdep_reports_show(struct seq_file *m, void *v)
{
	struct lockdep_seq *q = m->private;
	loff_t pos = *(loff_t *)v;

	if (pos == 0) {
		lockdep_seq_header(m, "reports");
		return 0;
	}
	spin_lock(&lockdep_lock);
	lockdep_copy(q->q_g, pos - 1, &q->q_copy);
	spin_unlock(&lockdep_lock);
	lockdep_format(&q->q_copy, lockdep_emit_seq, m);
	return 0;
}

static const struct seq_operations lockdep_reports_ops = {
	.start	= lockdep_reports_start,
	.next	= lockdep_reports_next,
	.stop	= lockdep_seq_stop,
	.show	= lockdep_reports_show,
};

static int lockdep_reports_open(struct inode *inode, struct file *file)
{
	return lockdep_seq_open(inode, file, &lockdep_reports_ops);
}

static const struct file_operations lockdep_reports_fops = {
	.owner		= THIS_MODULE,
	.open		= lockdep_reports_open,
	.read		= seq_read,
	.llseek		= seq_lseek,
	.release	= lockdep_seq_release,
};

/* position 0 is the header, then one per class, then one per resource */
static void *lockdep_graph_start(struct seq_file *m, loff_t *pos)
{
	struct lockdep_seq *q = m->private;

	return *pos <= q->q_nclasses + (loff_t)q->q_nrnodes ? pos : NULL;
}

static void *lockdep_graph_next(struct seq_file *m, void *v, loff_t *pos)
{
	++*pos;
	return lockdep_graph_start(m, pos);
}

static void lockdep_graph_class(struct seq_file *m, int idx)
{
	struct lockdep_seq *q = m->private;
	struct lockdep_class *lc = &q->q_cls;
	int i;

	spin_lock(&lockdep_lock);
	*lc = q->q_g->lg_classes[idx];
	for (i = 0; i < lc->lc_nedges; i++) {
		struct lockdep_class *to;

		to = &q->q_g->lg_classes[lc->lc_edges[i].ce_to];
		q->q_to_site[i] = to->lc_site;
		q->q_to_kind[i] = to->lc_kind;
	}
	spin_unlock(&lockdep_lock);

	for (i = 0; i < lc->lc_nedges; i++) {
		struct lockdep_cedge *ce = &lc->lc_edges[i];

		seq_printf(m, "cedge %pS %s %s %#x -> %pS %s %s %#x gate=%#x example %s %s\n",
			   (void *)lc->lc_site, lockdep_kind_name[lc->lc_kind],
			   ldlm_lockname[ce->ce_from_mode], ce->ce_from_bits,
			   (void *)q->q_to_site[i],
			   lockdep_kind_name[q->q_to_kind[i]],
			   ldlm_lockname[ce->ce_to_mode], ce->ce_to_bits,
			   ce->ce_gate,
			   lockdep_seq_res(q, 0, &ce->ce_from_res,
					   ce->ce_from_ns),
			   lockdep_seq_res(q, 1, &ce->ce_to_res, ce->ce_to_ns));
	}
}

static void lockdep_graph_rnode(struct seq_file *m, u32 idx)
{
	struct lockdep_seq *q = m->private;
	struct lockdep_rnode *rn = &q->q_rn;
	int n;
	int i;

	spin_lock(&lockdep_lock);
	*rn = q->q_g->lg_rnodes[idx];
	n = min_t(u32, rn->rn_nedges, LOCKDEP_REDGES);
	for (i = 0; i < n; i++) {
		struct lockdep_redge *re = &rn->rn_edges[i];
		struct lockdep_rnode *tn = &q->q_g->lg_rnodes[re->re_to];

		q->q_rsite[i][0] = q->q_g->lg_classes[re->re_from_cls].lc_site;
		q->q_rkind[i][0] = q->q_g->lg_classes[re->re_from_cls].lc_kind;
		q->q_rsite[i][1] = q->q_g->lg_classes[re->re_to_cls].lc_site;
		q->q_rkind[i][1] = q->q_g->lg_classes[re->re_to_cls].lc_kind;
		q->q_rres[i] = tn->rn_res;
		q->q_rns[i] = tn->rn_ns;
	}
	spin_unlock(&lockdep_lock);

	for (i = 0; i < n; i++) {
		struct lockdep_redge *re = &rn->rn_edges[i];

		seq_printf(m, "redge %s %pS %s %s %#x -> %s %pS %s %s %#x inv=%u,%u gate=%#x\n",
			   lockdep_seq_res(q, 0, &rn->rn_res, rn->rn_ns),
			   (void *)q->q_rsite[i][0],
			   lockdep_kind_name[q->q_rkind[i][0]],
			   ldlm_lockname[re->re_from_mode], re->re_from_bits,
			   lockdep_seq_res(q, 1, &q->q_rres[i], q->q_rns[i]),
			   (void *)q->q_rsite[i][1],
			   lockdep_kind_name[q->q_rkind[i][1]],
			   ldlm_lockname[re->re_to_mode], re->re_to_bits,
			   re->re_inv[0], re->re_inv[1], re->re_gate);
	}
}

static int lockdep_graph_show(struct seq_file *m, void *v)
{
	struct lockdep_seq *q = m->private;
	loff_t pos = *(loff_t *)v;
	int i;

	if (pos == 0) {
		lockdep_seq_header(m, "graph");
		for (i = 0; i < q->q_nns; i++)
			seq_printf(m, "ns %#x %s\n", q->q_ns[i].nn_id,
				   q->q_ns[i].nn_name);
	} else if (pos <= q->q_nclasses) {
		lockdep_graph_class(m, pos - 1);
	} else {
		lockdep_graph_rnode(m, pos - 1 - q->q_nclasses);
	}
	return 0;
}

static const struct seq_operations lockdep_graph_ops = {
	.start	= lockdep_graph_start,
	.next	= lockdep_graph_next,
	.stop	= lockdep_seq_stop,
	.show	= lockdep_graph_show,
};

static int lockdep_graph_open(struct inode *inode, struct file *file)
{
	return lockdep_seq_open(inode, file, &lockdep_graph_ops);
}

static const struct file_operations lockdep_graph_fops = {
	.owner		= THIS_MODULE,
	.open		= lockdep_graph_open,
	.read		= seq_read,
	.llseek		= seq_lseek,
	.release	= lockdep_seq_release,
};

void ldlm_lockdep_debugfs(struct dentry *dir)
{
	debugfs_create_file("lockdep_stats", 0444, dir, NULL,
			    &lockdep_stats_fops);
	debugfs_create_file("lockdep_reports", 0444, dir, NULL,
			    &lockdep_reports_fops);
	debugfs_create_file("lockdep_graph", 0444, dir, NULL,
			    &lockdep_graph_fops);
}

/* the self test drives the functions the hooks use, on private gens */
struct lockdep_test {
	struct lockdep_gen	*t_g;
	const char		*t_name;
	int			t_fail;
};

static void lockdep_t_end(struct lockdep_test *t, struct lockdep_end *e,
			  int r, int site, u16 mode, u16 bits)
{
	memset(e, 0, sizeof(*e));
	e->e_ns = 1;
	e->e_res.name[0] = FID_SEQ_NORMAL;
	e->e_res.name[1] = r;
	e->e_kind = LDK_OBJ;
	e->e_mode = mode;
	e->e_bits = bits;
	e->e_cls = lockdep_class_get(t->t_g, 0x1000 + site, LDK_OBJ);
	e->e_rn = lockdep_rnode_get(t->t_g, 1, &e->e_res);
}

/* @from held in @fm/@fb, then @to wanted in @tm/@tb, by invocation @inv */
static void lockdep_t_redge(struct lockdep_test *t, int from, u16 fm, u16 fb,
			    int to, u16 tm, u16 tb, u32 inv, u32 gate)
{
	struct lockdep_end f;
	struct lockdep_end w;

	lockdep_t_end(t, &f, from, from, fm, fb);
	lockdep_t_end(t, &w, to, to, tm, tb);
	if (f.e_rn >= 0 && w.e_rn >= 0)
		lockdep_redge_add(t->t_g, &f, &w, inv, gate);
}

#define LOCKDEP_U	MDS_INODELOCK_UPDATE

static void lockdep_t_ex(struct lockdep_test *t, int from, int to, u32 inv,
			 u32 gate)
{
	lockdep_t_redge(t, from, LCK_EX, LOCKDEP_U, to, LCK_EX, LOCKDEP_U,
			inv, gate);
}

static void lockdep_t_cedge(struct lockdep_test *t, int from, int to,
			    u32 gate)
{
	struct lockdep_end f;
	struct lockdep_end w;

	lockdep_t_end(t, &f, from, from, LCK_EX, LOCKDEP_U);
	lockdep_t_end(t, &w, to, to, LCK_EX, LOCKDEP_U);
	lockdep_cedge_add(t->t_g, &f, &w, gate);
}

static void lockdep_t_shape(struct lockdep_test *t, int site, u16 mode,
			    u16 bits)
{
	struct lockdep_end e;

	lockdep_t_end(t, &e, 100 + site, site, mode, bits);
	lockdep_shape_add(t->t_g, &e);
}

static void lockdep_t_rule1(struct lockdep_test *t, int r, u16 hm, u16 hb,
			    u16 wm, u16 wb)
{
	struct lockdep_end have;
	struct lockdep_end want;

	lockdep_t_end(t, &have, r, 1, hm, hb);
	lockdep_t_end(t, &want, r, 2, wm, wb);
	lockdep_rule1(t->t_g, &have, &want);
}

static void lockdep_t_expect(struct lockdep_test *t, const char *what,
			     long got, long want)
{
	if (got == want)
		return;
	pr_err("Lustre: lockdep selftest %s: %s is %ld, expected %ld\n",
	       t->t_name, what, got, want);
	t->t_fail++;
}

#define LOCKDEP_A	1
#define LOCKDEP_B	2
#define LOCKDEP_C	3
#define LOCKDEP_D	4
#define LOCKDEP_E	5
#define LOCKDEP_G1	0x11
#define LOCKDEP_G2	0x21

static void lockdep_t_abba(struct lockdep_test *t)
{
	struct lockdep_end have;
	struct lockdep_end want;

	lockdep_t_ex(t, LOCKDEP_A, LOCKDEP_B, 1, 0);
	lockdep_t_ex(t, LOCKDEP_B, LOCKDEP_A, 2, 0);
	lockdep_t_expect(t, "conflict", t->t_g->lg_ncat[LDR_CONFLICT], 1);
	lockdep_t_expect(t, "edges", t->t_g->lg_reports[0].rp_n, 2);
	/* the same classes on two other resources: one report, two hits */
	lockdep_t_end(t, &have, LOCKDEP_C, LOCKDEP_A, LCK_EX, LOCKDEP_U);
	lockdep_t_end(t, &want, LOCKDEP_D, LOCKDEP_B, LCK_EX, LOCKDEP_U);
	lockdep_redge_add(t->t_g, &have, &want, 3, 0);
	lockdep_t_end(t, &have, LOCKDEP_D, LOCKDEP_B, LCK_EX, LOCKDEP_U);
	lockdep_t_end(t, &want, LOCKDEP_C, LOCKDEP_A, LCK_EX, LOCKDEP_U);
	lockdep_redge_add(t->t_g, &have, &want, 4, 0);
	lockdep_t_expect(t, "reports", t->t_g->lg_nreports, 1);
	lockdep_t_expect(t, "hits", t->t_g->lg_reports[0].rp_hits, 2);
}

static void lockdep_t_one_invocation(struct lockdep_test *t)
{
	lockdep_t_ex(t, LOCKDEP_A, LOCKDEP_B, 1, 0);
	lockdep_t_ex(t, LOCKDEP_B, LOCKDEP_A, 1, 0);
	lockdep_t_expect(t, "reports", t->t_g->lg_nreports, 0);
}

static void lockdep_t_shared(struct lockdep_test *t)
{
	lockdep_t_redge(t, LOCKDEP_A, LCK_PR, LOCKDEP_U, LOCKDEP_B, LCK_PR,
			LOCKDEP_U, 1, 0);
	lockdep_t_redge(t, LOCKDEP_B, LCK_PR, LOCKDEP_U, LOCKDEP_A, LCK_PR,
			LOCKDEP_U, 2, 0);
	lockdep_t_expect(t, "reports", t->t_g->lg_nreports, 0);
}

static void lockdep_t_one_writer(struct lockdep_test *t)
{
	lockdep_t_redge(t, LOCKDEP_A, LCK_PR, LOCKDEP_U, LOCKDEP_B, LCK_PR,
			LOCKDEP_U, 1, 0);
	lockdep_t_redge(t, LOCKDEP_B, LCK_PR, LOCKDEP_U, LOCKDEP_A, LCK_EX,
			LOCKDEP_U, 2, 0);
	lockdep_t_expect(t, "bridged", t->t_g->lg_ncat[LDR_BRIDGED], 1);
	lockdep_t_expect(t, "bridge", t->t_g->lg_reports[0].rp_bshape, -1);
	lockdep_t_shape(t, 9, LCK_PW, LOCKDEP_U);
	lockdep_t_expect(t, "bridge", t->t_g->lg_reports[0].rp_bshape, 0);
}

static void lockdep_t_revisit_invocation(struct lockdep_test *t)
{
	lockdep_t_ex(t, LOCKDEP_B, LOCKDEP_C, 1, 0);
	lockdep_t_ex(t, LOCKDEP_C, LOCKDEP_D, 2, 0);
	lockdep_t_ex(t, LOCKDEP_D, LOCKDEP_A, 1, 0);
	lockdep_t_ex(t, LOCKDEP_B, LOCKDEP_D, 3, 0);
	lockdep_t_ex(t, LOCKDEP_A, LOCKDEP_B, 5, 0);
	lockdep_t_expect(t, "conflict", t->t_g->lg_ncat[LDR_CONFLICT], 1);
	lockdep_t_expect(t, "edges", t->t_g->lg_reports[0].rp_n, 3);
}

static void lockdep_t_revisit_depth(struct lockdep_test *t)
{
	lockdep_t_ex(t, LOCKDEP_B, LOCKDEP_C, 1, 0);
	lockdep_t_ex(t, LOCKDEP_C, LOCKDEP_D, 2, 0);
	lockdep_t_ex(t, LOCKDEP_D, LOCKDEP_E, 3, 0);
	lockdep_t_ex(t, LOCKDEP_E, LOCKDEP_A, 4, 0);
	lockdep_t_ex(t, LOCKDEP_B, LOCKDEP_D, 5, 0);
	lockdep_t_ex(t, LOCKDEP_A, LOCKDEP_B, 6, 0);
	lockdep_t_expect(t, "conflict", t->t_g->lg_ncat[LDR_CONFLICT], 1);
	lockdep_t_expect(t, "edges", t->t_g->lg_reports[0].rp_n, 4);
}

static void lockdep_t_second_invocation(struct lockdep_test *t)
{
	lockdep_t_ex(t, LOCKDEP_B, LOCKDEP_C, 1, 0);
	lockdep_t_ex(t, LOCKDEP_C, LOCKDEP_A, 2, 0);
	lockdep_t_ex(t, LOCKDEP_A, LOCKDEP_B, 1, 0);
	lockdep_t_expect(t, "reports", t->t_g->lg_nreports, 0);
	lockdep_t_ex(t, LOCKDEP_B, LOCKDEP_C, 3, 0);
	lockdep_t_expect(t, "conflict", t->t_g->lg_ncat[LDR_CONFLICT], 1);
	lockdep_t_expect(t, "edges", t->t_g->lg_reports[0].rp_n, 3);
}

static void lockdep_t_gated_revisit(struct lockdep_test *t)
{
	lockdep_t_ex(t, LOCKDEP_B, LOCKDEP_C, 1, LOCKDEP_G1);
	lockdep_t_ex(t, LOCKDEP_C, LOCKDEP_A, 2, LOCKDEP_G1);
	lockdep_t_ex(t, LOCKDEP_B, LOCKDEP_D, 3, 0);
	lockdep_t_ex(t, LOCKDEP_D, LOCKDEP_C, 4, 0);
	lockdep_t_ex(t, LOCKDEP_A, LOCKDEP_B, 5, 0);
	lockdep_t_expect(t, "conflict", t->t_g->lg_ncat[LDR_CONFLICT], 1);
	lockdep_t_expect(t, "edges", t->t_g->lg_reports[0].rp_n, 4);
}

static void lockdep_t_one_gate(struct lockdep_test *t)
{
	lockdep_t_ex(t, LOCKDEP_A, LOCKDEP_B, 1, LOCKDEP_G1);
	lockdep_t_ex(t, LOCKDEP_B, LOCKDEP_A, 2, LOCKDEP_G1);
	lockdep_t_expect(t, "reports", t->t_g->lg_nreports, 0);
}

static void lockdep_t_two_gates(struct lockdep_test *t)
{
	lockdep_t_ex(t, LOCKDEP_A, LOCKDEP_B, 1, LOCKDEP_G1);
	lockdep_t_ex(t, LOCKDEP_B, LOCKDEP_A, 2, LOCKDEP_G2);
	lockdep_t_expect(t, "conflict", t->t_g->lg_ncat[LDR_CONFLICT], 1);
}

static void lockdep_t_class_exempt_first(struct lockdep_test *t)
{
	lockdep_t_cedge(t, LOCKDEP_B, LOCKDEP_A, LOCKDEP_G1);
	lockdep_t_cedge(t, LOCKDEP_B, LOCKDEP_C, 0);
	lockdep_t_cedge(t, LOCKDEP_C, LOCKDEP_A, 0);
	lockdep_t_cedge(t, LOCKDEP_A, LOCKDEP_B, LOCKDEP_G1);
	lockdep_t_expect(t, "order", t->t_g->lg_ncat[LDR_ORDER], 1);
	lockdep_t_expect(t, "edges", t->t_g->lg_reports[0].rp_n, 3);
}

/* unlink's DOM discard: the getattr bridge has DOM only as a try */
static void lockdep_t_rule1_dom(struct lockdep_test *t)
{
	lockdep_t_shape(t, 7, LCK_PR, MDS_INODELOCK_LOOKUP |
			MDS_INODELOCK_UPDATE | MDS_INODELOCK_PERM);
	lockdep_t_rule1(t, LOCKDEP_A, LCK_EX, MDS_INODELOCK_LOOKUP |
			MDS_INODELOCK_UPDATE, LCK_PW, MDS_INODELOCK_DOM);
	lockdep_t_expect(t, "rule1-unbridged",
			 t->t_g->lg_ncat[LDR_R1_UNBRIDGED], 1);
	lockdep_t_expect(t, "rule1-bridged", t->t_g->lg_ncat[LDR_R1_BRIDGED],
			 0);
	lockdep_t_shape(t, 8, LCK_PR, MDS_INODELOCK_LOOKUP |
			MDS_INODELOCK_UPDATE | MDS_INODELOCK_PERM |
			MDS_INODELOCK_DOM);
	lockdep_t_expect(t, "rule1-unbridged",
			 t->t_g->lg_ncat[LDR_R1_UNBRIDGED], 0);
	lockdep_t_expect(t, "rule1-bridged", t->t_g->lg_ncat[LDR_R1_BRIDGED],
			 1);
}

static void lockdep_t_rule1_self(struct lockdep_test *t)
{
	lockdep_t_rule1(t, LOCKDEP_A, LCK_PR, LOCKDEP_U, LCK_EX, LOCKDEP_U);
	lockdep_t_expect(t, "rule1-self", t->t_g->lg_ncat[LDR_R1_SELF], 1);
}

static void lockdep_t_resources_full(struct lockdep_test *t)
{
	lockdep_t_ex(t, LOCKDEP_A, LOCKDEP_B, 1, 0);
	lockdep_t_ex(t, LOCKDEP_C, LOCKDEP_D, 2, 0);
	lockdep_t_ex(t, LOCKDEP_D, LOCKDEP_E, 3, 0);
	lockdep_t_expect(t, "lost", t->t_g->lg_stat[LDS_RNODES_FULL] > 0, 1);
}

static const struct {
	const char	*tc_name;
	u32		tc_nrnodes;
	void		(*tc_run)(struct lockdep_test *t);
} lockdep_tcases[] = {
	{ "abba",			64, lockdep_t_abba },
	{ "one-invocation",		64, lockdep_t_one_invocation },
	{ "shared",			64, lockdep_t_shared },
	{ "one-writer",			64, lockdep_t_one_writer },
	{ "revisit-invocation",		64, lockdep_t_revisit_invocation },
	{ "revisit-depth",		64, lockdep_t_revisit_depth },
	{ "second-invocation",		64, lockdep_t_second_invocation },
	{ "gated-revisit",		64, lockdep_t_gated_revisit },
	{ "one-gate",			64, lockdep_t_one_gate },
	{ "two-gates",			64, lockdep_t_two_gates },
	{ "class-exempt-first",		64, lockdep_t_class_exempt_first },
	{ "rule1-dom",			64, lockdep_t_rule1_dom },
	{ "rule1-self",			64, lockdep_t_rule1_self },
	{ "resources-full",		4, lockdep_t_resources_full },
};

/* ldlm.lockdep_selftest: build graphs in private gens and check them */
int ldlm_lockdep_selftest(void)
{
	struct lockdep_test t;
	int nfail = 0;
	int i;

	mutex_lock(&lockdep_cfg);
	for (i = 0; i < ARRAY_SIZE(lockdep_tcases); i++) {
		t.t_name = lockdep_tcases[i].tc_name;
		t.t_fail = 0;
		t.t_g = lockdep_gen_alloc(lockdep_tcases[i].tc_nrnodes,
					  t.t_name);
		if (!t.t_g) {
			mutex_unlock(&lockdep_cfg);
			return -ENOMEM;
		}
		spin_lock(&lockdep_lock);
		lockdep_tcases[i].tc_run(&t);
		spin_unlock(&lockdep_lock);
		lockdep_gen_put(t.t_g);
		if (t.t_fail)
			nfail++;
	}
	mutex_unlock(&lockdep_cfg);
	pr_info("Lustre: lockdep selftest: %d of %d cases failed\n", nfail,
		(int)ARRAY_SIZE(lockdep_tcases));
	return nfail ? -EINVAL : 0;
}
