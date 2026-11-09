/* getmany: ported from Java's bergdb.dag.GetMany and Dag.getMany; see
 * getmany.h. Java's names in comments, its order kept. */
#include "getmany.h"
#include <assert.h>
#include <string.h>
#include "keys.h"
#include "klong.h"
#include "opdata.h"

/* ======== The stop conditions ======== */

static int32_t dont_stop_handle(void *ctx, const struct kvt *kvt) {
    (void) ctx, (void) kvt;
    return GM_ADD;
}

/* DontStop */
struct gm_stop gm_dont_stop(void) {
    struct gm_stop s = { dont_stop_handle, NULL, NULL };
    return s;
}

/* Endpoint.handleKvt */
static int32_t endpoint_handle(void *ctx, const struct kvt *kvt) {
    struct gm_endpoint *s = ctx;
    assert(kvt != NULL);
    int32_t compare = keys_compare_keys(kvt->key, kvt->key_n, s->key, s->key_n);
    bool stop;
    if (s->backward) {
        stop = s->inclusive ? compare < 0 : compare <= 0;
    } else {
        stop = s->inclusive ? compare > 0 : compare >= 0;
    }
    return stop ? GM_STOP : GM_ADD;
}

static void endpoint_eod(void *ctx) {
    ((struct gm_endpoint *) ctx)->eod = true;
}

struct gm_stop gm_endpoint(struct gm_endpoint *s, const int64_t *key, int32_t key_n,
        bool inclusive, bool backward) {
    assert(key != NULL);
    s->inclusive = inclusive;
    s->key = key;
    s->key_n = key_n;
    s->backward = backward;
    s->eod = false;
    struct gm_stop r = { endpoint_handle, endpoint_eod, s };
    return r;
}

/* GetN.handleKvt: at most max_count, none for 0 (bergdb 020-27, C1, as Java's since
 * release 2026.4: GetN(0) gave every pair, as the count passed 0 before it was
 * compared). */
static int32_t get_n_handle(void *ctx, const struct kvt *kvt) {
    (void) kvt;
    struct gm_get_n *s = ctx;
    if (s->count >= s->max_count) {
        return GM_STOP;
    }
    s->count++;
    return s->count == s->max_count ? GM_ADD_AND_STOP : GM_ADD;
}

static void get_n_eod(void *ctx) {
    ((struct gm_get_n *) ctx)->eod = true;
}

struct gm_stop gm_get_n(struct gm_get_n *s, int32_t max_count) {
    assert(max_count >= 0);
    s->count = 0;
    s->max_count = max_count;
    s->eod = false;
    struct gm_stop r = { get_n_handle, get_n_eod, s };
    return r;
}

/* Prefix.handleKvt */
static int32_t prefix_handle(void *ctx, const struct kvt *kvt) {
    struct gm_prefix *s = ctx;
    return keys_is_prefix(s->prefix, s->prefix_n, kvt->key, kvt->key_n) ? GM_ADD : GM_STOP;
}

static void prefix_eod(void *ctx) {
    ((struct gm_prefix *) ctx)->eod = true;
}

struct gm_stop gm_prefix(struct gm_prefix *s, const int64_t *prefix, int32_t prefix_n) {
    assert(prefix != NULL);
    s->prefix = prefix;
    s->prefix_n = prefix_n;
    s->eod = false;
    struct gm_stop r = { prefix_handle, prefix_eod, s };
    return r;
}

/* PrefixN.handleKvt: at most max_count, none for 0, as GetN (bergdb 020-27, C1). */
static int32_t prefix_n_handle(void *ctx, const struct kvt *kvt) {
    struct gm_prefix_n *s = ctx;
    if (s->count >= s->max_count) {
        return GM_STOP;
    }
    s->count++;
    return keys_is_prefix(s->prefix, s->prefix_n, kvt->key, kvt->key_n)
            ? (s->count == s->max_count ? GM_ADD_AND_STOP : GM_ADD) : GM_STOP;
}

static void prefix_n_eod(void *ctx) {
    ((struct gm_prefix_n *) ctx)->eod = true;
}

struct gm_stop gm_prefix_n(struct gm_prefix_n *s, const int64_t *prefix, int32_t prefix_n,
        int32_t max_count) {
    s->prefix = prefix;
    s->prefix_n = prefix_n;
    s->max_count = max_count;
    s->count = 0;
    s->eod = false;
    struct gm_stop r = { prefix_n_handle, prefix_n_eod, s };
    return r;
}

/* ======== GetMany ======== */

/* new GetMany(), with Dag.newGetMany's GetData */
void gm_init(struct getmany *g, struct dag *d, struct mem *m) {
    memset(g, 0, sizeof *g);
    g->stop_condition = gm_dont_stop();
    g->start_key = NULL;
    g->start_key_n = 0;
    g->lookup_time = INT64_MAX;
    g->inclusive = true;
    g->forward = true;
    g->cache = true;
    dag_new_get_data(d, &g->gd);
    g->get_op_count = 0;
    g->mem = m;
}

void gm_set_backward(struct getmany *g) {
    g->forward = false;
}

/* GetMany.Chain: the links (node and compare value pairs) from the root to
 * the current leaf, and the key's segments passed so far. Its nodes are
 * counted (012-07, 6.4.2): addLink retains, removeLink releases. */
struct chain {
    struct knode **link_nodes;
    int64_t *link_compare_values;
    int32_t link_size;
    int32_t link_cap;           /* link_nodes' */
    int32_t link_cv_cap;        /* link_compare_values' */
    int64_t *key_segments;      /* the key so far, and room for the last segment */
    int32_t key_segment_size;
    int32_t key_segment_cap;
    struct kwp kwi;
    bool first;
    bool setup_eq_match;

    const int64_t *chain_start_key;
    int32_t chain_start_key_n;
    bool chain_forward;
    bool chain_inclusive;

    struct getmany *g;
    struct obj_ctx *cx;
};

/* Grows an array of n elements of size each to 2n (at least 4). */
static bool grow(struct mem *m, void **p, int32_t *cap, size_t size) {
    int32_t n = *cap;
    int32_t nn = n == 0 ? 4 : n * 2;
    void *q = mem_realloc(m, *p, (size_t) n * size, (size_t) nn * size, MEM_STATE);
    if (q == NULL) {
        return false;
    }
    *p = q;
    *cap = nn;
    return true;
}

/* new Chain() */
static bool chain_init(struct chain *c, struct getmany *g, struct obj_ctx *cx) {
    memset(c, 0, sizeof *c);
    c->chain_start_key = g->start_key;
    c->chain_start_key_n = g->start_key_n;
    c->chain_forward = g->forward;
    c->chain_inclusive = g->inclusive;
    c->first = true;
    c->setup_eq_match = false;
    c->g = g;
    c->cx = cx;
    kwp_init(&c->kwi);
    void *ks = NULL;
    if (!grow(g->mem, &ks, &c->key_segment_cap, sizeof(int64_t))) {
        return false;
    }
    c->key_segments = ks;
    return true;
}

/* The chain's end: its holds released, its arrays freed. */
static void chain_free(struct chain *c) {
    struct mem *m = c->g->mem;
    for (int32_t i = 0; i < c->link_size; i++) {
        obj_release(c->cx, &c->link_nodes[i]->n.o);
    }
    c->link_size = 0;
    mem_free(m, c->link_nodes, (size_t) c->link_cap * sizeof *c->link_nodes, MEM_STATE);
    mem_free(m, c->link_compare_values,
            (size_t) c->link_cv_cap * sizeof *c->link_compare_values, MEM_STATE);
    mem_free(m, c->key_segments, (size_t) c->key_segment_cap * sizeof *c->key_segments,
            MEM_STATE);
}

/* Chain.addLink */
static bool add_link(struct chain *c, struct knode *node, int64_t compareValue) {
    if (c->link_size == c->link_cap) {
        void *ln = c->link_nodes;
        if (!grow(c->g->mem, &ln, &c->link_cap, sizeof(struct knode *))) {
            return false;
        }
        c->link_nodes = ln;
    }
    if (c->link_size == c->link_cv_cap) {
        void *lv = c->link_compare_values;
        if (!grow(c->g->mem, &lv, &c->link_cv_cap, sizeof(int64_t))) {
            return false;
        }
        c->link_compare_values = lv;
    }

    obj_retain(&node->n.o);
    c->link_nodes[c->link_size] = node;
    c->link_compare_values[c->link_size] = compareValue;
    c->link_size++;
    return true;
}

/* Chain.removeLink */
static void remove_link(struct chain *c) {
    c->link_size--;
    struct knode *n = c->link_nodes[c->link_size];
    c->link_nodes[c->link_size] = NULL;
    obj_release(c->cx, &n->n.o);
}

/* Chain.addKeySegment; one more slot is kept for getKeySegments' last. */
static bool add_key_segment(struct chain *c, int64_t segment) {
    assert(c->key_segment_size <= c->key_segment_cap);
    if (c->key_segment_size + 1 >= c->key_segment_cap) {
        void *ks = c->key_segments;
        if (!grow(c->g->mem, &ks, &c->key_segment_cap, sizeof(int64_t))) {
            return false;
        }
        c->key_segments = ks;
    }
    c->key_segments[c->key_segment_size] = segment;
    c->key_segment_size++;
    return true;
}

/* Chain.removeKeySegment */
static void remove_key_segment(struct chain *c) {
    c->key_segment_size--;
}

/* Chain.eqMatch: the key segments passed and the last link are the start
 * key. */
static bool eq_match(const struct chain *c, const int64_t *start, int32_t startN) {
    if (c->key_segment_size + 1 != startN || c->link_size == 0) {
        return false;
    }

    for (int32_t i = 0; i < c->key_segment_size; i++) {
        if (c->key_segments[i] != kl_get_compare_value(start[i])) {
            return false;
        }
    }

    return c->link_compare_values[c->link_size - 1]
            == kl_get_compare_value(start[startN - 1]);
}

/* Chain.setup: the chain at or before the start key, "at" if it equals an
 * existing key. */
static bool chain_setup(struct chain *c, struct knode *root) {
    struct getmany *g = c->g;
    int64_t specialStart[1];
    const int64_t *start = c->chain_start_key;
    int32_t startN = c->chain_start_key_n;
    const int64_t lookupTime = g->actual_lookup_time;
    struct kwp *kwi = &c->kwi;

    assert(root != NULL);

    if (start == NULL) {
        if (g->forward) {
            specialStart[0] = -1;   /* A special "key" that is less than any real DB key. */
        } else {
            specialStart[0] = INT64_MAX;    /* greater than any real DB key */
        }
        start = specialStart;
        startN = 1;
    }

    assert(startN > 0 && "startKey.length = 0, not allowed");

    struct knode *node = root;
    const int32_t segmentCount = startN;
    int32_t index = 0;
    bool hasDiff = false;
        /* set to true when difference found between startKey and nearest db key. */

    while (true) {
        int64_t startKeySegment;

        if (index < segmentCount) {
            startKeySegment = start[index];
        } else {
            startKeySegment = g->forward ? INT64_MAX : -1;
        }

        if (hasDiff) {
            if (g->forward) {
                kn_search_lt(node, lookupTime, INT64_MAX, kwi);
            } else {
                kn_search_gt(node, lookupTime, -1, kwi);
            }
        } else {
            if (g->forward) {
                kn_search_lte(node, lookupTime, startKeySegment, kwi);
            } else if (kn_is_segment_leaf(node)) {
                kn_search_gte(node, lookupTime, startKeySegment, kwi);
            } else {
                /* 2026-10-13: above the leaf, the klong is the lower bound of
                 * its child, and the child that holds the start key is the last
                 * one at or before it, as for a forward scan. */
                kn_search_lte(node, lookupTime, startKeySegment, kwi);
            }
        }

        if (kwi->klong == KL_NULL) {
            /* Backward above the leaf: the start key is before every key of
             * the tree, so the position is before the first, not after the
             * last. */
            bool beforeFirst = !g->forward && !hasDiff && !kn_is_segment_leaf(node);
            if (!add_link(c, node, g->forward || beforeFirst ? -1 : INT64_MAX)) {
                return false;
            }
            break;  /* Done! */
        } else {
            if (!add_link(c, node, kl_get_compare_value(kwi->klong))) {
                return false;
            }
        }

        if (kn_is_segment_leaf(node) && kl_get_length(kwi->klong) < KL_MAX_SIZE) {
            /* No need to follow, we know it is a value node pointer. Done! */
            break;
        }

        struct node *next = op_follow_pointer(&g->gd.op, &node->n, kwi->pointer_index);
        /* Java's assert "next instanceof KeyNode", a check (its AssertionError) since a
         * damaged stream reaches it (bergdb 019-32's class): C read the node as a key
         * node. */
        if (next == NULL || !op_assert_key(&g->gd.op, next, "next=")) {
            return false;
        }

        if (kn_is_segment_leaf(node)) {
            int64_t compareValue = kl_get_compare_value(kwi->klong);
            if (compareValue != startKeySegment) {
                hasDiff = true;
            }
            if (!add_key_segment(c, compareValue)) {
                return false;
            }
            index++;
        }

        node = (struct knode *) next;
    }

    /* -- setupEqMatch true if setup results in an exact match. */
    assert(c->link_size > 0);
    c->setup_eq_match = eq_match(c, start, startN);
    return true;
}

/* Chain.next: the next pair into *out, *has false at the end. */
static bool chain_next(struct chain *c, struct kvt *out, bool *has) {
    struct getmany *g = c->g;
    struct kwp *kwi = &c->kwi;
    *has = false;

    while (true) {   /* dummy while just to be able to do "continue". */
        int32_t linkSize = c->link_size;
        if (linkSize == 0) {
            break;
        }

        struct knode *linkNode = c->link_nodes[linkSize - 1];
        int64_t linkCompareValue = c->link_compare_values[linkSize - 1];

        if (c->first && c->chain_inclusive && c->setup_eq_match) {
            if (c->chain_forward) {
                kn_search_gte(linkNode, g->actual_lookup_time, linkCompareValue, kwi);
            } else {
                kn_search_lte(linkNode, g->actual_lookup_time, linkCompareValue, kwi);
            }
        } else {
            if (c->chain_forward) {
                kn_search_gt(linkNode, g->actual_lookup_time, linkCompareValue, kwi);
            } else {
                kn_search_lt(linkNode, g->actual_lookup_time, linkCompareValue, kwi);
            }
        }
        c->first = false;

        if (kwi->klong == KL_NULL) {
            if (linkSize > 1) {
                struct knode *parent = c->link_nodes[linkSize - 2];
                if (kn_is_segment_leaf(parent)) {
                    remove_key_segment(c);
                }
            }

            remove_link(c);
            continue;
        }

        linkCompareValue = kl_get_compare_value(kwi->klong);
        c->link_compare_values[c->link_size - 1] = linkCompareValue;    /* setLinkCompareValue */

        struct node *next = op_follow_pointer(&g->gd.op, &linkNode->n, kwi->pointer_index);
        if (next == NULL) {
            return false;
        }

        if (next->o.kind == OBJ_VALUE) {
            /* Found next KV, creates result: getKeySegments, the key so far
             * and the last compare value, in the chain's buffer (one slot is
             * always free after the segments). */
            struct vnode *valueNode = (struct vnode *) next;
            assert(c->key_segment_size < c->key_segment_cap);
            c->key_segments[c->key_segment_size] = kl_get_compare_value(kwi->klong);
            out->key = c->key_segments;
            out->key_n = c->key_segment_size + 1;
            out->value = valueNode;     /* Note, no copy. */
            out->time = kwi->klong_time;
            out->spos = valueNode->n.spos;
            *has = true;
            break;  /* Done! */

        } else {
            /* Java's assert "next instanceof KeyNode", a check, as in chain_setup. */
            if (!op_assert_key(&g->gd.op, next, "")) {
                return false;
            }
            if (!add_link(c, (struct knode *) next, g->forward ? -1 : INT64_MAX)) {
                return false;
            }
            if (kn_is_segment_leaf(linkNode)) {
                if (!add_key_segment(c, linkCompareValue)) {
                    return false;
                }
            }
        }
    }

    return true;
}

/* Dag.getMany */
bool dag_get_many(struct dag *d, struct getmany *g) {
    struct knode *root;
    if (!tds_find_root(dag_get_top_ds(d), g->actual_lookup_time, &g->gd.op, &root)) {
        return false;
    }

    if (root == NULL) {
        /* No state at the lookup time, before the first transaction: the end at once,
         * and eod says so, as StopCondition promises (bergdb 020-27, C2, as Java's since
         * release 2026.4; it was not called). */
        if (g->stop_condition.eod != NULL) {
            g->stop_condition.eod(g->stop_condition.ctx);
        }
        return true;
    }

    struct chain chain;
    if (!chain_init(&chain, g, d->cx)) {
        chain_free(&chain);
        return false;
    }
    bool ok = chain_setup(&chain, root);

    while (ok) {
        struct kvt kvt;
        bool has;
        if (!chain_next(&chain, &kvt, &has)) {
            ok = false;
            break;
        }

        if (!has) {
            if (g->stop_condition.eod != NULL) {
                g->stop_condition.eod(g->stop_condition.ctx);
            }
            break;
        }

        g->get_op_count++;
        int32_t shouldStop = g->stop_condition.handle_kvt(g->stop_condition.ctx, &kvt);

        bool stop = false;
        switch (shouldStop) {
        case GM_STOP:
            stop = true;
            break;
        case GM_ADD:
            ok = g->result.add == NULL || g->result.add(g->result.ctx, &kvt);
            break;
        case GM_ADD_AND_STOP:
            ok = g->result.add == NULL || g->result.add(g->result.ctx, &kvt);
            stop = true;
            break;
        case GM_CONTINUE:
            break;
        default:
            assert(shouldStop < 0 && "Bad int value");
            ok = false;
            break;
        }
        if (!ok || stop) {
            break;
        }
        if (g->collect != NULL) {
            obj_collect(g->collect);    /* a safe point between pairs: the chain holds its links */
            if (g->safe_point != NULL) {
                g->safe_point(g->safe_point_ctx);
            }
        }
    }

    chain_free(&chain);
    return ok;
}
