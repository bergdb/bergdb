/* dag: ported from Java's bergdb.dag.Dag, with PutData, GetData and
 * KeyAccessPath; see dag.h. Java's names in comments, its order kept. */
#include "dag.h"
#include <assert.h>
#include <stdarg.h>
#include <string.h>
#include "handle.h"
#include "jsem.h"
#include "klong.h"
#include "spos.h"
#include "tnode.h"

/* ======== The listeners' calls: true if the function is NULL ======== */

static bool key_node_created(const struct op_node_change_listener *l, struct knode *n) {
    return l->key_node_created == NULL || l->key_node_created(l->ctx, n);
}

static bool key_node_changed(const struct op_node_change_listener *l, struct knode *n) {
    return l->key_node_changed == NULL || l->key_node_changed(l->ctx, n);
}

static bool key_node_replaced(const struct op_node_change_listener *l, struct knode *n) {
    return l->key_node_replaced == NULL || l->key_node_replaced(l->ctx, n);
}

/* Dag.NodeChangeListener.keyNodeTakenBack: keyNodeReplaced by default. */
static bool key_node_taken_back(const struct op_node_change_listener *l, struct knode *n) {
    if (l->key_node_taken_back != NULL) {
        return l->key_node_taken_back(l->ctx, n);
    }
    return key_node_replaced(l, n);
}

static bool value_node_created(const struct op_node_change_listener *l, struct vnode *n,
        const int64_t *key, int32_t key_n) {
    return l->value_node_created == NULL || l->value_node_created(l->ctx, n, key, key_n);
}

static void node_split(const struct dag_split_listener *l, int32_t splitType) {
    if (l->node_split != NULL) {
        l->node_split(l->ctx, splitType);
    }
}

/* ======== KeyAccessPath ======== */

/* KeyAccessPath.enlargeArrays: 16 at first, then floor(1.6 size) in
 * integers (bergdb 005-79, as Java's since release 2026.2; (int) (size *
 * 1.6) before). The nodes' array is zeroed, as a Java array is, so that an
 * entry above the high-water mark is NULL (pd_clear, 021-25). */
static bool kap_enlarge(struct kap *p) {
    int32_t size = p->cap;
    int32_t newSize = size == 0 ? 16 : size + size * 3 / 5;
    int64_t *klongs = mem_alloc(p->mem, (size_t) newSize * sizeof *klongs, MEM_STATE);
    struct knode **nodes = mem_zalloc(p->mem, (size_t) newSize * sizeof *nodes, MEM_STATE);
    if (klongs == NULL || nodes == NULL) {
        mem_free(p->mem, klongs, klongs == NULL ? 0 : (size_t) newSize * sizeof *klongs,
                MEM_STATE);
        mem_free(p->mem, nodes, nodes == NULL ? 0 : (size_t) newSize * sizeof *nodes, MEM_STATE);
        return false;
    }
    if (size > 0) {
        memcpy(klongs, p->klongs, (size_t) size * sizeof *klongs);
        memcpy(nodes, p->nodes, (size_t) size * sizeof *nodes);
    }
    mem_free(p->mem, p->klongs, (size_t) size * sizeof *p->klongs, MEM_STATE);
    mem_free(p->mem, p->nodes, (size_t) size * sizeof *p->nodes, MEM_STATE);
    p->klongs = klongs;
    p->nodes = nodes;
    p->cap = newSize;
    return true;
}

/* KeyAccessPath.add */
bool kap_add(struct kap *p, int64_t klong, struct knode *node) {
    if (p->cap < p->size + 1 && !kap_enlarge(p)) {
        return false;
    }
    p->size++;
    p->klongs[p->size - 1] = klong;
    p->nodes[p->size - 1] = node;
    if (p->used < p->size) {
        p->used = p->size;
    }
    return true;
}

/* KeyAccessPath.getKlong */
int64_t kap_get_klong(const struct kap *p, int32_t index) {
    assert(index < p->size);
    return p->klongs[index];
}

/* KeyAccessPath.get */
struct knode *kap_get(const struct kap *p, int32_t index) {
    assert(index < p->size && "index < size");
    return p->nodes[index];
}

/* ======== PutData and GetData ======== */

/* Dag.newPutData's pointer listener: the access path. */
static bool put_pointer_followed(void *ctx, struct node *predecessor, int32_t pointerIndex,
        struct node *result, int32_t pointerType) {
    (void) pointerType;
    struct putdata *p = ctx;
    if (result != NULL) {
        if (node_type(result) == NODE_TYPE_KEY_NODE) {
            if (node_type(predecessor) == NODE_TYPE_TOP_NODE) {
                return kap_add(&p->key_access_path, KL_NULL, (struct knode *) result);
            } else if (node_type(predecessor) == NODE_TYPE_KEY_NODE) {
                struct knode *pre = (struct knode *) predecessor;
                struct knode *res = (struct knode *) result;
                return kap_add(&p->key_access_path, kn_get_klong(pre, pointerIndex), res);
            }
        }
    }
    return true;
}

static bool nothing_accessed(void *ctx, struct tnode *superRoot) {
    (void) ctx, (void) superRoot;
    return true;
}

/* Dag.newPutData's split listener: the counts. */
static void put_node_split(void *ctx, int32_t splitType) {
    struct putdata *p = ctx;
    switch (splitType) {
    case DAG_TIME_SPLIT_1:
    case DAG_TIME_SPLIT_2:
        p->time_split_count += 1;
        break;
    case DAG_SPACE_SPLIT_1:
    case DAG_SPACE_SPLIT_2:
    case DAG_SPACE_SPLIT_3:
        p->space_split_count += 1;
        break;
    default:
        break;
    }
}

/* Dag.CACHE_ALL_EXCEPT_LARGE_VALUE_NODES */
static bool cache_all_except_large(void *ctx, const struct node *node) {
    (void) ctx;
    if (node_type(node) == NODE_TYPE_VALUE) {
        return ((const struct vnode *) node)->len <= 1024 * 1024;
    }
    return true;
}

/* ======== PutData.replaced (dag.h) ======== */

#define PD_REMOVED ((struct knode *) (uintptr_t) 1)

static uint32_t made_hash(const void *p) {
    uint64_t x = (uint64_t) (uintptr_t) p;
    x ^= x >> 33;
    x *= UINT64_C(0xff51afd7ed558ccd);
    x ^= x >> 33;
    return (uint32_t) x;
}

static void replaced_free(struct putdata *pd) {
    struct mem *m = pd->key_access_path.mem;
    mem_free(m, pd->replaced_made, (size_t) pd->replaced_cap * sizeof *pd->replaced_made,
            MEM_STATE);
    mem_free(m, pd->replaced_old, (size_t) pd->replaced_cap * sizeof *pd->replaced_old,
            MEM_STATE);
    pd->replaced_made = NULL;
    pd->replaced_old = NULL;
    pd->replaced_cap = 0;
    pd->replaced_used = 0;
}

/* replaced.clear(): a small table is emptied, a large one freed (a
 * transaction of many splits leaves no large table to every later one). */
static void replaced_clear(struct putdata *pd) {
    if (pd->replaced_used == 0) {
        return;
    }
    if (pd->replaced_cap > 256) {
        replaced_free(pd);
    } else {
        memset(pd->replaced_made, 0, (size_t) pd->replaced_cap * sizeof *pd->replaced_made);
        pd->replaced_used = 0;
    }
}

static bool replaced_grow(struct putdata *pd) {
    struct mem *m = pd->key_access_path.mem;
    const int32_t cap = pd->replaced_cap == 0 ? 16 : 2 * pd->replaced_cap;
    struct knode **made = mem_zalloc(m, (size_t) cap * sizeof *made, MEM_STATE);
    struct knode **old = mem_zalloc(m, (size_t) cap * sizeof *old, MEM_STATE);
    if (made == NULL || old == NULL) {
        mem_free(m, made, made == NULL ? 0 : (size_t) cap * sizeof *made, MEM_STATE);
        mem_free(m, old, old == NULL ? 0 : (size_t) cap * sizeof *old, MEM_STATE);
        return false;
    }
    int32_t used = 0;
    for (int32_t i = 0; i < pd->replaced_cap; i++) {
        struct knode *k = pd->replaced_made[i];
        if (k == NULL || k == PD_REMOVED) {
            continue;
        }
        uint32_t h = made_hash(k) & (uint32_t) (cap - 1);
        while (made[h] != NULL) {
            h = (h + 1) & (uint32_t) (cap - 1);
        }
        made[h] = k;
        old[h] = pd->replaced_old[i];
        used++;
    }
    replaced_free(pd);
    pd->replaced_made = made;
    pd->replaced_old = old;
    pd->replaced_cap = cap;
    pd->replaced_used = used;
    return true;
}

/* PutData.madeFor: 'made', made by the split at tt, replaces 'old'; NULL:
 * no such node. false: NOMEM. */
static bool pd_made_for(struct putdata *pd, struct knode *made, struct knode *old) {
    if (pd->replaced_time != pd->tt) {
        replaced_clear(pd);
        pd->replaced_time = pd->tt;
    }
    if (old == NULL) {
        return true;
    }
    if (2 * (pd->replaced_used + 1) > pd->replaced_cap && !replaced_grow(pd)) {
        return false;
    }
    const uint32_t mask = (uint32_t) (pd->replaced_cap - 1);
    uint32_t h = made_hash(made) & mask;
    while (pd->replaced_made[h] != NULL) {
        if (pd->replaced_made[h] == made) {
            pd->replaced_old[h] = old;
            return true;
        }
        h = (h + 1) & mask;
    }
    pd->replaced_made[h] = made;
    pd->replaced_old[h] = old;
    pd->replaced_used++;
    return true;
}

/* PutData.replacedBy: the node that 'made', made by a split of this
 * transaction, replaces; else NULL. */
static struct knode *pd_replaced_by(const struct putdata *pd, const struct knode *made) {
    if (pd->replaced_time != pd->tt || pd->replaced_cap == 0) {
        return NULL;
    }
    const uint32_t mask = (uint32_t) (pd->replaced_cap - 1);
    uint32_t h = made_hash(made) & mask;
    while (pd->replaced_made[h] != NULL) {
        if (pd->replaced_made[h] == made) {
            return pd->replaced_old[h];
        }
        h = (h + 1) & mask;
    }
    return NULL;
}

/* C's: the entry of 'made', taken back, leaves the map, so that the map
 * names no node that may be freed (dag.h). Java's entry stays and is never
 * read again. */
static void pd_replaced_remove(struct putdata *pd, const struct knode *made) {
    if (pd->replaced_time != pd->tt || pd->replaced_cap == 0) {
        return;
    }
    const uint32_t mask = (uint32_t) (pd->replaced_cap - 1);
    uint32_t h = made_hash(made) & mask;
    while (pd->replaced_made[h] != NULL) {
        if (pd->replaced_made[h] == made) {
            pd->replaced_made[h] = PD_REMOVED;
            pd->replaced_old[h] = NULL;
            return;
        }
        h = (h + 1) & mask;
    }
}

/* new PutData(), then Dag.newPutData's listeners */
void dag_new_put_data(struct dag *d, struct putdata *pd, struct mem *m) {
    (void) d;
    memset(pd, 0, sizeof *pd);
    op_init(&pd->op);
    pd->tt = 0;
    pd->op.access_data = ACCESS_DATA_DEFAULT;
    pd->space_split_count = 0;
    pd->time_split_count = 0;
    kwp_init(&pd->one_kwi[0]);
    kwp_init(&pd->two_kwis[0]);
    kwp_init(&pd->two_kwis[1]);
    pd->key_access_path.mem = m;
    pd->replaced_time = -1;
    pd->node_change_listener = OP_DO_NOTHING_NODE_CHANGE_LISTENER;
    pd->pointer_created_listener = OP_DO_NOTHING_POINTER_CREATED_LISTENER;
    pd->op.cache_policy.should_cache = cache_all_except_large;
    pd->op.pointer_listener.pointer_followed = put_pointer_followed;
    pd->op.pointer_listener.super_root_accessed = nothing_accessed;
    pd->op.pointer_listener.ctx = pd;
    pd->split_listener.node_split = put_node_split;
    pd->split_listener.ctx = pd;
}

void pd_free(struct putdata *pd) {
    struct kap *p = &pd->key_access_path;
    mem_free(p->mem, p->klongs, (size_t) p->cap * sizeof *p->klongs, MEM_STATE);
    mem_free(p->mem, p->nodes, (size_t) p->cap * sizeof *p->nodes, MEM_STATE);
    p->klongs = NULL;
    p->nodes = NULL;
    p->cap = 0;
    p->size = 0;
    p->used = 0;
    replaced_free(pd);
    pd->replaced_time = -1;
}

/* PutData.clearFast */
void pd_clear_fast(struct putdata *pd) {
    pd->key_access_path.size = 0;      /* KeyAccessPath.clearFast */
    pd->op.kwi.klong = KL_NULL;
    pd->op.kwi.node = NULL;
}

/* PutData.clear: no borrowed node is left for after a safe point.
 * KeyAccessPath.clear nulls the entries below the high-water mark, every
 * one set since the last clear, not the whole array, whose length is that
 * of the longest path ever followed (bergdb 021-25, fix (c), as Java's
 * since release 2026.4): a reclaim step's touch records every key node it
 * follows, and every later transaction nulled all of them. An enlargement
 * copies the whole array, so no entry is left above the mark. */
void pd_clear(struct putdata *pd) {
    struct kap *p = &pd->key_access_path;
    for (int32_t i = 0; i < p->used; i++) {     /* KeyAccessPath.clear */
        p->nodes[i] = NULL;
    }
    p->used = 0;
    p->size = 0;
    replaced_clear(pd);                         /* replaced.clear() */
    pd->replaced_time = -1;
    pd->op.temp_pointer.index = -1;
    pd->op.temp_pointer.node = NULL;
    pd->op.temp_pointer.pos = SPOS_NULL;

    pd->op.kwi.node = NULL;
    pd->op.kwi.klong = KL_NULL;
    pd->op.kwi.klong_time = -1;

    pd->one_kwi[0].node = NULL;
    pd->two_kwis[0].node = NULL;
    pd->two_kwis[1].node = NULL;
}

/* PutData.getParent */
struct knode *pd_get_parent(const struct putdata *pd, int32_t depth) {
    assert(depth >= 0 && "depth >= 0");
    int32_t parentDepth = depth - 1;
    return parentDepth < 0 ? NULL : kap_get(&pd->key_access_path, parentDepth);
}

/* Dag.newGetData's pointer listener: the counts. */
static bool get_pointer_followed(void *ctx, struct node *predecessor, int32_t pointerIndex,
        struct node *result, int32_t pointerType) {
    (void) predecessor, (void) pointerIndex, (void) result;
    struct getdata *g = ctx;
    switch (pointerType) {
    case PTR_TYPE_MEMORY:
        g->follow_memory_pointer_count++;
        break;
    case PTR_TYPE_STREAM:
        g->follow_stream_pointer_count++;
        break;
    default:
        assert(0 && "Bad pointer type");
        break;
    }
    return true;
}

/* new GetData(), then Dag.newGetData's listener */
void dag_new_get_data(struct dag *d, struct getdata *gd) {
    (void) d;
    memset(gd, 0, sizeof *gd);
    op_init(&gd->op);
    gd->op.cache_policy.should_cache = cache_all_except_large;
    gd->op.pointer_listener.pointer_followed = get_pointer_followed;
    gd->op.pointer_listener.super_root_accessed = nothing_accessed;
    gd->op.pointer_listener.ctx = gd;
}

/* ======== The Dag ======== */

/* new Dag(superRoot, maxNodeSize) */
void dag_init(struct dag *d, struct obj_ctx *cx, struct tnode *superRoot, int32_t maxNodeSize) {
    tds_init(&d->top_ds, superRoot);
    d->max_node_size = maxNodeSize;
    d->cx = cx;
}

/* Dag.createEmpty: TopDs.createFromFirstRoot(time, new KeyNode(), ...) */
bool dag_create_empty(struct dag *d, struct obj_ctx *cx, int64_t time, int32_t maxNodeSize,
        const struct op_pointer_created_listener *pointerCreationListener) {
    struct knode *root = kn_new(cx, true);
    if (root == NULL || !tds_create_from_first_root(cx, &d->top_ds, time, root,
            ACCESS_DATA_DEFAULT, pointerCreationListener)) {
        return false;
    }
    d->max_node_size = maxNodeSize;
    d->cx = cx;
    return true;
}

void dag_free(struct dag *d) {
    tds_free(d->cx, &d->top_ds);
}

struct topds *dag_get_top_ds(struct dag *d) {
    return &d->top_ds;
}

/* Dag.findNode */
bool dag_find_node(struct dag *d, const int32_t *choices, int32_t n, struct getdata *gd,
        struct node **out) {
    assert(choices != NULL && "choices == null not allowed");
    struct node *node = &tds_get_super_root(&d->top_ds)->n;

    for (int32_t i = 0; i < n; i++) {
        int32_t choice = choices[i];
        node = op_follow_pointer(&gd->op, node, choice);
        if (node == NULL) {
            /* Java's follower returns null for no node; C's NULL is a failure,
             * as no follower of C returns NULL otherwise. */
            return false;
        }
    }
    *out = node;
    return true;
}

/* Dag.getEqNodeInSegment */
static bool get_eq_node_in_segment(int64_t time, struct knode *segmentRoot, int64_t compareValue,
        struct getdata *gd, struct node **out) {
    struct kwp *kwi = &gd->op.kwi;
    struct knode *current = segmentRoot;
    struct node *result;
    op_descent_from(&gd->op, &current->n);

    while (true) {
        if (kn_is_segment_leaf(current)) {
            kn_search_eq(current, time, compareValue, kwi);

            if (kwi->klong == KL_NULL) {
                result = NULL;
            } else {
                assert(!kwp_is_null_pointer(kwi) && "KeyNode.searchEq() found result, but "
                        "there is no pointer");
                result = op_follow_pointer(&gd->op, &current->n, kwi->pointer_index);
                if (result == NULL) {
                    return false;
                }
                gd->kv_time = kwi->klong_time;
            }
            break;
        } else {
            kn_search_lte(current, time, compareValue, kwi);

            if (kwi->klong == KL_NULL) {
                result = NULL;
                break;
            } else {
                /* Java's assert, a check (its AssertionError) since a damaged stream
                 * reaches it (bergdb 019-32's class): C aborted. */
                if (kwi->node != NULL && !op_assert_key(&gd->op, kwi->node,
                        "Expected a KeyNode, got ")) {
                    return false;
                }
                struct node *nextCurrent = op_follow_pointer(&gd->op, &current->n,
                        kwi->pointer_index);
                if (nextCurrent == NULL || !op_cast_ok(&gd->op, nextCurrent,
                        NODE_TYPE_KEY_NODE) || !op_descent_to(&gd->op, nextCurrent)) {
                    return false;
                }
                current = (struct knode *) nextCurrent;
            }
        }
    }

    *out = result;
    return true;
}

/* Dag.getOne */
bool dag_get_one(struct dag *d, int64_t time, const int64_t *keySegments, int32_t n,
        struct getdata *gd, struct vnode **out) {
    assert(gd->op.pointer_listener.pointer_followed != NULL);
    assert(gd->op.cache_policy.should_cache != NULL);
    *out = NULL;

    struct knode *segmentRoot;
    if (!tds_find_root(&d->top_ds, time, &gd->op, &segmentRoot)) {
        return false;
    }
    if (segmentRoot == NULL) {
        return true;
    }

    struct node *item;
    struct knode *node;
    const int32_t segmentCount = n;
    const int32_t lastIndex = n - 1;
    struct vnode *result = NULL;

    for (int32_t i = 0; i < segmentCount; i++) {
        if (!get_eq_node_in_segment(time, segmentRoot, keySegments[i], gd, &item)) {
            return false;
        }

        if (i == lastIndex) {
            result = NULL;
            if (item != NULL && item->o.kind == OBJ_VALUE) {
                struct vnode *valueNode = (struct vnode *) item;
                /* valueNode.getValue(): null for a delete node, which no
                 * leaf names (012-02, 6.3.1); the value node itself here. */
                result = vn_is_delete(valueNode) ? NULL : valueNode;
                gd->tpos = vn_get_tpos(valueNode);
            }
            break;
        } else {
            if (item != NULL && item->o.kind == OBJ_KEY) {
                node = (struct knode *) item;
            } else {
                node = NULL;
            }

            if (node == NULL) {
                result = NULL;
                break;
            }
            gd->node_depth++;
            segmentRoot = node;
        }
    }

    *out = result;
    return true;
}

/* ======== putKv() with helpers ======== */

static bool append_klongs(struct dag *d, struct knode *node, int32_t depth,
        const struct kwp *toAppend, int32_t nAppend, struct putdata *pd);
static bool append_delete_klong(struct dag *d, struct knode *node, int32_t depth,
        int64_t compareValueToDelete, struct putdata *pd, bool *isNoop);
static bool handle_full_node(struct dag *d, struct knode *node, int32_t depth,
        const struct kwp *toInsert, int32_t nInsert, int64_t tTime, struct knode *last,
        struct putdata *pd);
static bool delete_upward(struct dag *d, struct knode *leaf, int32_t depth, int64_t compareValue,
        const int64_t *key, struct putdata *pd, bool *isNoop);
static int32_t link_index(const struct knode *parent, const struct knode *node, int64_t klong);
static int64_t last_time(const struct knode *node);

/* Dag.reportNewPointers */
static bool report_new_pointers(struct knode *node, const struct op_pointer_created_listener *l) {
    int32_t size = node->size;
    for (int32_t i = 0; i < size; i++) {
        struct node *pointee = kn_get_pointer_node(node, i);
        if (pointee != NULL) {
            if (!op_pointer_created(l, &node->n, i, pointee)) {
                return false;
            }
        }
    }
    return true;
}

/* Dag.checkFound (bergdb 019-32, as Java's since release 2026.3): a put
 * finds a klong at or below its key in every key node on its way that is
 * not a segment leaf (the graph's invariant). A node from a damaged stream
 * may have none (a segment leaf's flag changed, its checksum right): the put
 * fails, and so the database, or the start's rerun, which refuses the
 * stream. It was an assert, on which C aborted. */
static bool check_found(const struct knode *node, struct putdata *pd) {
    if (pd->op.kwi.klong == KL_NULL) {
        return op_fail(&pd->op, ERR_FORMAT, "DbException", "Key node %lld, not a segment leaf, "
                "has no klong at or below the key at time %lld: corrupt data.",
                (long long) node->n.id, (long long) pd->tt);
    }
    return true;
}

/* KeyNode.assertOk(maxNodeSize), Java's assert: a check that returns Java's
 * AssertionError (Java's tests and harness run with -ea), as a node from a
 * damaged stream reaches it; C aborted on it. Java's text, which names the
 * node where it names one (bergdb 021-15); C's added ", key node ID". */
static bool assert_ok(const struct knode *node, int32_t maxNodeSize, struct putdata *pd) {
    char buf[KN_TEXT];
    const char *msg = kn_check_max(node, maxNodeSize, buf);
    if (msg != NULL) {
        return op_fail(&pd->op, ERR_FORMAT, "AssertionError", "%s", msg);
    }
    return true;
}

/* Dag.setValue */
static bool set_value(struct dag *d, struct knode *node, int64_t compareValue,
        const int64_t *key, int32_t keyN, const uint8_t *value, int32_t len,
        struct putdata *pd) {
    assert(node != NULL && "node is null");

    op_descent_from(&pd->op, &node->n);
    while (!kn_is_segment_leaf(node)) {
        kn_search_lte(node, pd->tt, compareValue, &pd->op.kwi);
        if (!check_found(node, pd)) {
            return false;
        }

        struct node *next = op_follow_pointer(&pd->op, &node->n, pd->op.kwi.pointer_index);
        if (next == NULL || !op_cast_ok(&pd->op, next, NODE_TYPE_KEY_NODE)
                || !op_descent_to(&pd->op, next)) {
            return false;
        }
        node = (struct knode *) next;
    }

    if (value == NULL) {
        /* A delete operation. A ValueNode (of delete type) is created only
         * for the pd.nodeChangeListener. */
        bool isNoop;
        if (!delete_upward(d, node, pd->key_access_path.size - 1, compareValue, key, pd,
                &isNoop)) {
            return false;
        }
        if (!isNoop) {
            struct vnode *del = vn_create_delete(d->cx);
            if (del == NULL || !value_node_created(&pd->node_change_listener, del, key, keyN)) {
                return false;
            }
        }
    } else {
        struct vnode *valueNode = vn_new(d->cx, value, len, SPOS_NULL);
        if (valueNode == NULL
                || !value_node_created(&pd->node_change_listener, valueNode, key, keyN)) {
            return false;
        }

        /* "+1" is needed. We need to be able to fit two more klongs. A TIME
         * klong may be needed. */
        if (node->size + 1 < d->max_node_size) {
            if (!kn_add_klong(d->cx, node, pd->tt, kl_compare_value_to_key_klong(compareValue),
                    &valueNode->n, pd->op.access_data)
                    || !op_pointer_created(&pd->pointer_created_listener, &node->n,
                            node->size - 1, &valueNode->n)
                    || !key_node_changed(&pd->node_change_listener, node)) {
                return false;
            }
        } else {
            pd->one_kwi[0].klong = kl_compare_value_to_key_klong(compareValue);
            pd->one_kwi[0].node = &valueNode->n;
            pd->one_kwi[0].pos = pd->op.access_data;
            if (!append_klongs(d, node, pd->key_access_path.size - 1, pd->one_kwi, 1, pd)) {
                return false;
            }
        }
    }
    return true;
}

/* Dag.setNode: the next segment's root under compare_value, made (a new
 * segment leaf) if missing and create is true; *out NULL if it is missing
 * and create is false. */
static bool set_node(struct dag *d, struct knode *segmentRoot, int64_t compareValue,
        bool create, struct putdata *pd, struct knode **out) {
    struct knode *current = segmentRoot;
    struct knode *result;

    if (!assert_ok(current, d->max_node_size, pd)) {
        return false;
    }

    op_descent_from(&pd->op, &current->n);
    while (!kn_is_segment_leaf(current)) {
        kn_search_lte(current, pd->tt, compareValue, &pd->op.kwi);
        if (!check_found(current, pd)) {
            return false;
        }
        assert(pd->op.kwi.pointer_index >= 0 && "LTE search found klong, but pointerIndex < 0");

        struct node *next = op_follow_pointer(&pd->op, &current->n, pd->op.kwi.pointer_index);
        if (next == NULL || !op_cast_ok(&pd->op, next, NODE_TYPE_KEY_NODE)
                || !op_descent_to(&pd->op, next)) {
            return false;
        }
        current = (struct knode *) next;
        if (!assert_ok(current, d->max_node_size, pd)) {
            return false;
        }
    }

    kn_search_eq(current, pd->tt, compareValue, &pd->op.kwi);

    if (pd->op.kwi.klong == KL_NULL && !create) {
        result = NULL;

    } else if (pd->op.kwi.klong == KL_NULL) {
        /* If not found, create the node */

        struct knode *child = kn_new(d->cx, true);     /* New segment leaf node. */
        if (child == NULL || !key_node_created(&pd->node_change_listener, child)) {
            return false;
        }

        /* "+1" needed since there might be a need to insert a TIME klong too. */
        if (current->size + 1 < d->max_node_size) {
            if (!kn_add_klong(d->cx, current, pd->tt, kl_compare_value_to_key_klong(compareValue),
                    &child->n, pd->op.access_data)
                    || !op_pointer_created(&pd->pointer_created_listener, &current->n,
                            current->size - 1, &child->n)
                    || !key_node_changed(&pd->node_change_listener, current)) {
                return false;
            }
        } else {
            pd->one_kwi[0].klong = kl_compare_value_to_key_klong(compareValue);
            pd->one_kwi[0].node = &child->n;
            pd->one_kwi[0].pos = pd->op.access_data;
            if (!append_klongs(d, current, pd->key_access_path.size - 1, pd->one_kwi, 1, pd)) {
                return false;
            }
        }

        result = child;

    } else {
        /* If found */
        struct node *next = op_follow_pointer(&pd->op, &current->n, pd->op.kwi.pointer_index);
        if (next == NULL || !op_cast_ok(&pd->op, next, NODE_TYPE_KEY_NODE)) {
            return false;
        }
        result = (struct knode *) next;
    }

    *out = result;
    return true;
}

/* Dag.appendDeleteKlong: *isNoop true if the key is not there (or deleted
 * already) and nothing changed. */
static bool append_delete_klong(struct dag *d, struct knode *node, int32_t depth,
        int64_t compareValueToDelete, struct putdata *pd, bool *isNoop) {
    const int16_t sz = node->size;
    assert(sz <= d->max_node_size && "Bad node size");
    int64_t arrayTime = -1;
    int64_t tTime = pd->tt;
    int64_t arrayDel = kl_create_delete();
    int64_t del = kl_create_delete();
    bool hasTransDel = false;
        /* Set to true if last klong is a delete for the same time as this transaction. */

    for (int32_t i = 0; i < sz; i++) {
        int64_t klong = node->klongs[i];
        int32_t type = kl_get_int_type(klong);

        switch (type) {
        case KL_INT_TYPE_TIME:
            arrayTime = kl_get_time(klong);
            /* Java throws Bug: "Bad state of node, arrayTime > transaction time." */
            assert(arrayTime <= tTime && "Bad state of node, arrayTime > transaction time");
            break;
        case KL_INT_TYPE_KEY: {
            int64_t arrayCompareValue = kl_get_compare_value(klong);
            if (compareValueToDelete == arrayCompareValue) {
                del = kl_delete(del, i);
            }
            break;
        }
        case KL_INT_TYPE_DELETE_BITMAP:
            arrayDel = klong;
            if (arrayTime == tTime && i == sz - 1) {
                hasTransDel = true;
            }
            break;
        default:
            assert(0 && "Bad klong type");
            break;
        }
    }

    int64_t unionDel = (del | arrayDel);
    *isNoop = (unionDel == arrayDel);

    if (!*isNoop) {
        if (hasTransDel) {
            node->klongs[sz - 1] = unionDel;
            if (!key_node_changed(&pd->node_change_listener, node)) {
                return false;
            }
            /* Direct modification, but still OK. A reader will always have a
             * lookup time < trans.transTime. */
        } else {
            if (node->size + 1 < d->max_node_size) {
                if (!kn_add_delete_klong(d->cx, node, tTime, unionDel)
                        || !key_node_changed(&pd->node_change_listener, node)) {
                    return false;
                }
            } else {
                struct knode *last = kn_last_version_given_del(d->cx, node, sz, tTime, unionDel);
                if (last == NULL
                        || !handle_full_node(d, node, depth, NULL, 0, tTime, last, pd)) {
                    return false;
                }
            }
        }
    }
    return true;
}

/* Dag.appendKlongs: one or two klongs (not delete klongs) into node for the
 * current transaction, node and its ancestors split if needed. */
static bool append_klongs(struct dag *d, struct knode *node, int32_t depth,
        const struct kwp *toAppend, int32_t nAppend, struct putdata *pd) {
    assert(nAppend < 3 && "toAppend.length < 3");
    assert(nAppend > 0 && "toAppend.length > 0");
    assert(kn_check_max(node, d->max_node_size, NULL) == NULL);

    /* "+1" is needed since a TIME klong could be added along with the
     * toInsert klongs. */
    const bool isFull = node->size + nAppend + 1 > d->max_node_size;

    if (!isFull) {
        for (int32_t i = 0; i < nAppend; i++) {
            const struct kwp *kwi = &toAppend[i];
            if (!kn_add_klong(d->cx, node, pd->tt, kwi->klong, kwi->node, pd->op.access_data)) {
                return false;
            }
            if (kwi->node != NULL) {
                if (!op_pointer_created(&pd->pointer_created_listener, &node->n,
                        node->size - 1, kwi->node)) {
                    return false;
                }
            }
        }
        if (!key_node_changed(&pd->node_change_listener, node)) {
            return false;
        }
        assert(kn_check_max(node, d->max_node_size, NULL) == NULL);

    } else {
        /* 'node' is full: space-full or time-full. 'last' is made, but is not
         * always a node of the Dag: if 'node' is space-full, 'first' and
         * 'second' are used instead, so keyNodeCreated is not called here
         * for 'last'. */
        struct knode *last = kn_last_version(d->cx, node, pd->tt);
        if (last == NULL) {
            return false;
        }
        assert(kn_check_max(last, d->max_node_size, NULL) == NULL);
        if (!handle_full_node(d, node, depth, toAppend, nAppend, pd->tt, last, pd)) {
            return false;
        }
    }
    return true;
}

/* Dag.timeSplitInPlace */
static bool time_split_in_place(struct dag *d, int64_t tTime, struct knode *node,
        struct knode *last, const struct kwp *toAppend, int32_t nAppend, struct putdata *pd) {
    for (int32_t i = 0; i < nAppend; i++) {
        const struct kwp *kwi = &toAppend[i];
        bool replaced;
        if (!kn_replace_klong(d->cx, last, tTime, kwi->klong, kwi->node, pd->op.access_data,
                &replaced)) {
            return false;
        }
        if (!replaced && !kn_add_klong(d->cx, last, tTime, kwi->klong, kwi->node,
                pd->op.access_data)) {
            return false;
        }
    }

    if (!kn_set_content_from(d->cx, node, last)
            || !report_new_pointers(node, &pd->pointer_created_listener)
            || !key_node_changed(&pd->node_change_listener, node)) {
        return false;
    }
    node_split(&pd->split_listener, DAG_TIME_SPLIT_1);
    assert(kn_check(node, NULL) == NULL);
    return true;
}

/* Dag.spaceSplitInPlace */
static bool space_split_in_place(struct dag *d, struct knode *node, struct knode *last,
        int32_t depth, const struct kwp *toInsert, int32_t nInsert, struct putdata *pd) {
    const int64_t tt = pd->tt;
    const bool isSegmentLeaf = kn_is_segment_leaf(node);
    struct knode *first = kn_new(d->cx, isSegmentLeaf);     /* only holds the first half */
    struct knode *second = kn_new(d->cx, isSegmentLeaf);
    struct knode *parent = pd_get_parent(pd, depth);
    if (first == NULL || second == NULL) {
        return false;
    }

    if (!key_node_created(&pd->node_change_listener, second)
            || !pd_made_for(pd, second, pd_replaced_by(pd, node))) {
        return false;
    }
    int64_t secondKlong;
    if (!kn_first_and_second(d->cx, node, tt, last, toInsert, nInsert, first, second,
            &secondKlong)
            || !kn_set_content_from(d->cx, node, first)
            || !report_new_pointers(node, &pd->pointer_created_listener)
            || !report_new_pointers(second, &pd->pointer_created_listener)
            || !key_node_changed(&pd->node_change_listener, node)
            || !key_node_changed(&pd->node_change_listener, second)) {
        return false;
    }

    if (parent == NULL || kn_is_segment_leaf(parent)) {
        /* 'node' is the space root or a segment root: a new root above both
         * halves. */
        struct knode *newRoot = kn_new(d->cx, false);
        if (newRoot == NULL
                || !key_node_created(&pd->node_change_listener, newRoot)
                || !pd_made_for(pd, newRoot, pd_replaced_by(pd, node))
                || !kn_add_klong(d->cx, newRoot, tt, KL_EMPTY_KEY, &node->n, pd->op.access_data)
                || !op_pointer_created(&pd->pointer_created_listener, &newRoot->n,
                        newRoot->size - 1, &node->n)
                || !kn_add_klong(d->cx, newRoot, tt, secondKlong, &second->n, pd->op.access_data)
                || !op_pointer_created(&pd->pointer_created_listener, &newRoot->n,
                        newRoot->size - 1, &second->n)) {
            return false;
        }

        if (parent == NULL) {
            if (!tds_new_super_root(d->cx, &d->top_ds, tt, newRoot, pd->op.access_data,
                    &pd->pointer_created_listener, &pd->node_change_listener)) {
                return false;
            }
            node_split(&pd->split_listener, DAG_SPACE_SPLIT_3);
        } else {
            /* The segment leaf's klong of tt to 'node' is pointed to newRoot in
             * place, as TopDs.newSuperRoot does for the space root: a second
             * klong would shadow it and still name 'node', and if the
             * transaction then empties 'node' and takes it back, which points
             * klongs in its parent only (take_back, retarget, take_back_root),
             * a written node would name a node never written (bergdb 023-08,
             * review C, fault 12; as Java's since release 2026.4). The klong is
             * behind the leaf's time klong of tt, where every reader stops. */
            const int64_t klong1 = kap_get_klong(&pd->key_access_path, depth);
            assert(klong1 != KL_NULL && "Missing klong in keyAccessPath");
            const int32_t i = link_index(parent, node, klong1);
            if (i < 0 || last_time(parent) != tt) {
                return op_fail(&pd->op, ERR_FORMAT, "Bug", "Space split at %lld: no klong of "
                        "tt to segment root %lld in its segment leaf.", (long long) tt,
                        (long long) node->n.id);
            }
            if (!kn_repoint_klong(d->cx, parent, i, &newRoot->n)
                    || !op_pointer_created(&pd->pointer_created_listener, &parent->n, i,
                            &newRoot->n)
                    || !key_node_changed(&pd->node_change_listener, parent)) {
                return false;
            }
            node_split(&pd->split_listener, DAG_SPACE_SPLIT_2);
        }
        assert(kn_check(newRoot, NULL) == NULL);
    } else {
        /* The parent already points to 'node', the first half. */
        pd->one_kwi[0].klong = secondKlong;
        pd->one_kwi[0].node = &second->n;
        pd->one_kwi[0].pos = pd->op.access_data;
        if (!append_klongs(d, parent, depth - 1, pd->one_kwi, 1, pd)) {
            return false;
        }
        node_split(&pd->split_listener, DAG_SPACE_SPLIT_1);
    }
    return true;
}

/* Dag.timeSplit: the time-full node replaced by its last version
 * (time-split-1 and time-split-2). */
static bool time_split(struct dag *d, int64_t tTime, struct knode *last, int32_t depth,
        const struct kwp *toAppend, int32_t nAppend, struct putdata *pd) {
    struct knode *parent = pd_get_parent(pd, depth);

    for (int32_t i = 0; i < nAppend; i++) {
        const struct kwp *kwi = &toAppend[i];
        bool replaced;
        if (!kn_replace_klong(d->cx, last, tTime, kwi->klong, kwi->node, pd->op.access_data,
                &replaced)) {
            return false;
        }
        if (!replaced && !kn_add_klong(d->cx, last, tTime, kwi->klong, kwi->node,
                pd->op.access_data)) {
            return false;
        }
    }

    if (!key_node_created(&pd->node_change_listener, last)
            || !report_new_pointers(last, &pd->pointer_created_listener)) {
        return false;
    }

    if (parent == NULL) {
        /* time-split-2: no parent, 'last' is the new super root. */
        if (!tds_new_super_root(d->cx, &d->top_ds, tTime, last, pd->op.access_data,
                &pd->pointer_created_listener, &pd->node_change_listener)) {
            return false;
        }
        node_split(&pd->split_listener, DAG_TIME_SPLIT_2);
        assert(kn_check(last, NULL) == NULL);

    } else {
        /* time-split-1: there is a parent. */
        int64_t klong1 = kap_get_klong(&pd->key_access_path, depth);
        assert(klong1 != KL_NULL && "time-split-1, missing klong in keyAccessPath");

        pd->one_kwi[0].klong = klong1;
        pd->one_kwi[0].node = &last->n;
        pd->one_kwi[0].pos = pd->op.access_data;

        if (!append_klongs(d, parent, depth - 1, pd->one_kwi, 1, pd)) {
            return false;
        }
        node_split(&pd->split_listener, DAG_TIME_SPLIT_1);
        assert(kn_check(parent, NULL) == NULL);
    }
    return true;
}

/* Dag.spaceSplit: space-split-1 (not a segment root), -2 (a segment root:
 * the parent is a segment leaf), -3 (the space root: no parent). */
static bool space_split(struct dag *d, struct knode *node, struct knode *last, int32_t depth,
        const struct kwp *toInsert, int32_t nInsert, struct putdata *pd) {
    const int64_t tt = pd->tt;
    const bool isSegmentLeaf = kn_is_segment_leaf(node);
    struct knode *first = kn_new(d->cx, isSegmentLeaf);
    struct knode *second = kn_new(d->cx, isSegmentLeaf);
    struct knode *parent = pd_get_parent(pd, depth);
    if (first == NULL || second == NULL
            || !key_node_created(&pd->node_change_listener, first)
            || !key_node_created(&pd->node_change_listener, second)
            || !pd_made_for(pd, first, node)
            || !pd_made_for(pd, second, node)) {
        return false;
    }

    int64_t secondKlong;
    if (parent == NULL) {
        /* space-split-3: 'node' is the space root node. */
        struct knode *newRoot = kn_new(d->cx, false);
        if (newRoot == NULL
                || !key_node_created(&pd->node_change_listener, newRoot)
                || !pd_made_for(pd, newRoot, node)
                || !kn_first_and_second(d->cx, node, tt, last, toInsert, nInsert, first, second,
                        &secondKlong)
                || !report_new_pointers(first, &pd->pointer_created_listener)
                || !report_new_pointers(second, &pd->pointer_created_listener)
                || !kn_add_klong(d->cx, newRoot, tt, KL_EMPTY_KEY, &first->n, pd->op.access_data)
                || !op_pointer_created(&pd->pointer_created_listener, &newRoot->n,
                        newRoot->size - 1, &first->n)
                || !kn_add_klong(d->cx, newRoot, tt, secondKlong, &second->n, pd->op.access_data)
                || !op_pointer_created(&pd->pointer_created_listener, &newRoot->n,
                        newRoot->size - 1, &second->n)
                || !key_node_changed(&pd->node_change_listener, first)
                || !key_node_changed(&pd->node_change_listener, second)
                || !tds_new_super_root(d->cx, &d->top_ds, tt, newRoot, pd->op.access_data,
                        &pd->pointer_created_listener, &pd->node_change_listener)) {
            return false;
        }
        node_split(&pd->split_listener, DAG_SPACE_SPLIT_3);
        assert(kn_check(newRoot, NULL) == NULL);

    } else if (kn_is_segment_leaf(parent)) {
        /* space-split-2: 'node' is a segment root since parent is a segment leaf. */
        struct knode *newSegmentRoot = kn_new(d->cx, false);
        if (newSegmentRoot == NULL
                || !key_node_created(&pd->node_change_listener, newSegmentRoot)
                || !pd_made_for(pd, newSegmentRoot, node)
                || !kn_first_and_second(d->cx, node, tt, last, toInsert, nInsert, first, second,
                        &secondKlong)
                || !report_new_pointers(first, &pd->pointer_created_listener)
                || !report_new_pointers(second, &pd->pointer_created_listener)
                || !kn_add_klong(d->cx, newSegmentRoot, tt, KL_EMPTY_KEY, &first->n,
                        pd->op.access_data)
                || !op_pointer_created(&pd->pointer_created_listener, &newSegmentRoot->n,
                        newSegmentRoot->size - 1, &first->n)
                || !kn_add_klong(d->cx, newSegmentRoot, tt, secondKlong, &second->n,
                        pd->op.access_data)
                || !op_pointer_created(&pd->pointer_created_listener, &newSegmentRoot->n,
                        newSegmentRoot->size - 1, &second->n)
                || !key_node_changed(&pd->node_change_listener, first)
                || !key_node_changed(&pd->node_change_listener, second)) {
            return false;
        }

        int64_t klong1 = kap_get_klong(&pd->key_access_path, depth);
        assert(klong1 != KL_NULL && "Missing klong in keyAccessPath");

        pd->one_kwi[0].klong = klong1;
        pd->one_kwi[0].node = &newSegmentRoot->n;
        pd->one_kwi[0].pos = pd->op.access_data;
        if (!append_klongs(d, parent, depth - 1, pd->one_kwi, 1, pd)) {
            return false;
        }
        node_split(&pd->split_listener, DAG_SPACE_SPLIT_2);
        assert(kn_check(parent, NULL) == NULL);
        assert(kn_check(newSegmentRoot, NULL) == NULL);

    } else {
        /* space-split-1: 'node' is not a segment root since parent is not a
         * segment leaf. */
        if (!kn_first_and_second(d->cx, node, tt, last, toInsert, nInsert, first, second,
                &secondKlong)
                || !report_new_pointers(first, &pd->pointer_created_listener)
                || !report_new_pointers(second, &pd->pointer_created_listener)
                || !key_node_changed(&pd->node_change_listener, first)
                || !key_node_changed(&pd->node_change_listener, second)) {
            return false;
        }

        int64_t firstKlong = kap_get_klong(&pd->key_access_path, depth);

        pd->two_kwis[0].klong = firstKlong;
        pd->two_kwis[0].node = &first->n;
        pd->two_kwis[0].pos = pd->op.access_data;
        pd->two_kwis[1].klong = secondKlong;
        pd->two_kwis[1].node = &second->n;
        pd->two_kwis[1].pos = pd->op.access_data;

        if (!append_klongs(d, parent, depth - 1, pd->two_kwis, 2, pd)) {
            return false;
        }
        node_split(&pd->split_listener, DAG_SPACE_SPLIT_1);
        assert(kn_check(parent, NULL) == NULL);
    }
    return true;
}

/* Dag.handleFullNode: a space split if last.size > maxNodeSize / 2, else a
 * time split; in place for a node that the transaction made. A node that
 * existed before is replaced and cut back to before the transaction. */
static bool handle_full_node(struct dag *d, struct knode *node, int32_t depth,
        const struct kwp *toInsert, int32_t nInsert, int64_t tTime, struct knode *last,
        struct putdata *pd) {
    const bool newInTrans = kn_get_first_time(node) == tTime;

    if (last->size > d->max_node_size / 2) {
        if (newInTrans) {
            if (!space_split_in_place(d, node, last, depth, toInsert, nInsert, pd)) {
                return false;
            }
        } else {
            if (!space_split(d, node, last, depth, toInsert, nInsert, pd)) {
                return false;
            }
        }
    } else {
        if (newInTrans) {
            if (!time_split_in_place(d, tTime, node, last, toInsert, nInsert, pd)) {
                return false;
            }
        } else {
            if (!pd_made_for(pd, last, node)
                    || !time_split(d, tTime, last, depth, toInsert, nInsert, pd)) {
                return false;
            }
        }
    }

    if (!newInTrans) {
        /* 'node' is no longer current. Its klongs of tTime are in its
         * replacement, and no reader sees them, so they go. */
        kn_to_previous_state(d->cx, node, tTime - 1);
        if (!key_node_replaced(&pd->node_change_listener, node)) {
            return false;
        }
    }
    return true;
}

/* Dag.putKv */
bool dag_put_kv(struct dag *d, const int64_t *key, int32_t n, const uint8_t *value, int32_t len,
        struct putdata *pd) {
    assert(pd->tt >= 0);
    assert(pd->op.pointer_listener.pointer_followed != NULL);
    assert(key != NULL && n > 0 && "key not non-null and with length > 0");

    struct knode *root;
    if (!tds_find_root(&d->top_ds, pd->tt, &pd->op, &root)) {
        return false;
    }
    /* Java throws DbException: "Found no root node at t=..., cannot continue put." */
    assert(root != NULL && "Found no root node, cannot continue put");

    struct knode *segmentRoot = root;
    const int32_t segmentCount = n;
    const int32_t lastSegment = segmentCount - 1;

    for (int32_t i = 0; i < segmentCount; i++) {
        if (i == lastSegment) {
            if (!set_value(d, segmentRoot, key[i], key, n, value, len, pd)) {
                return false;
            }
        } else {
            struct knode *next;
            if (!set_node(d, segmentRoot, key[i], value != NULL, pd, &next)) {
                return false;
            }
            segmentRoot = next;
            if (segmentRoot == NULL) {
                /* A delete of a key that does not exist, a noop. No node must be
                 * created; noops are not stored, so the rerun at startup would
                 * not create it, and node ids would differ after a restart. */
                return true;
            }
        }
    }
    return true;
}

/* ======== The upward unlink at a delete (bergdb 023-07, section 5) ========
 *
 * Java's Dag.deleteUpward and its helpers, as release 2026.4 has them
 * (record format 6), in Java's order. A delete that leaves its segment leaf
 * with no live KEY klong at the transaction time tt does not write the
 * leaf: it deletes the parent's klong to it instead, and so on upward while
 * a node is left with no live klong, also across segment trees (an emptied
 * segment root takes the segment's klong in the segment leaf above). The
 * first node that keeps a live klong gets the delete (UP).
 *
 * Every inner node has the empty key (KL_EMPTY_KEY, compare value 0) as its
 * smallest live klong (LE-b): the roots that space splits make have it, and
 * a space split of an inner node gives its second half the empty key for its
 * first klong (kn_first_and_second). When the child of the empty key
 * empties, the empty key is pointed to the next live child, whose own klong
 * is deleted (empty_key_next).
 *
 * A node that the transaction made by a split (a last version, a half or a
 * new root, its first klong of tt) and that it empties is taken back
 * (take_back): never written, as if never made. Any other node made by the
 * transaction holds only puts of the transaction, which one operation a key
 * leaves live, so no delete empties it: Java's Bug.
 *
 * An unlinked node gets no entry of tt and loses those it got earlier in
 * the transaction (kn_to_previous_state), and is reported as replaced, so
 * that it leaves D if it got dirty in this transaction only. A space root
 * that is a segment leaf stays, empty; an inner one is never emptied, as
 * root collapse (RC, collapse_root) lowers it first.
 *
 * All of it is a function of the delete and the state at tt, so the
 * startup's rerun redoes it; a record of format 6 means it. */

static bool bug(struct putdata *pd, const char *format, ...) {
    if (pd->op.err != NULL && pd->op.err->code == ERR_OK) {
        va_list args;
        va_start(args, format);
        err_setv(pd->op.err, ERR_FORMAT, "Bug", format, args);
        va_end(args);
    }
    return false;
}

/* Dag.lastBitmap: the last delete bitmap of the node, or one with no bit set. */
static int64_t last_bitmap(const struct knode *node) {
    const int16_t sz = node->size;
    int64_t del = KL_DELETE_NONE_BITMAP;
    for (int32_t i = 0; i < sz; i++) {
        const int64_t klong = node->klongs[i];
        if (kl_get_int_type(klong) == KL_INT_TYPE_DELETE_BITMAP) {
            del = klong;
        }
    }
    return del;
}

/* Dag.lastTime: the time of the node's last time klong, -1 if none. */
static int64_t last_time(const struct knode *node) {
    for (int32_t i = node->size - 1; i >= 0; i--) {
        const int64_t klong = node->klongs[i];
        if (kl_get_int_type(klong) == KL_INT_TYPE_TIME) {
            return kl_get_time(klong);
        }
    }
    return -1;
}

/* Dag.bitsOf: the delete bits of every KEY klong of the node with the
 * compare value. */
static int64_t bits_of(const struct knode *node, int64_t compareValue) {
    const int16_t sz = node->size;
    int64_t del = kl_create_delete();
    for (int32_t i = 0; i < sz; i++) {
        const int64_t klong = node->klongs[i];
        if (kl_get_int_type(klong) == KL_INT_TYPE_KEY
                && kl_get_compare_value(klong) == compareValue) {
            del = kl_delete(del, i);
        }
    }
    return del;
}

/* Dag.allKeysIn: true if every KEY klong of the node is deleted by 'del'. */
static bool all_keys_in(const struct knode *node, int64_t del) {
    const int16_t sz = node->size;
    for (int32_t i = 0; i < sz; i++) {
        if (kl_get_int_type(node->klongs[i]) == KL_INT_TYPE_KEY && !kl_is_deleted(del, i)) {
            return false;
        }
    }
    return true;
}

/* Dag.smallestLive: the smallest live compare value of the node, at the
 * latest time; -1 if none. */
static int64_t smallest_live(const struct knode *node) {
    const int64_t del = last_bitmap(node);
    const int16_t sz = node->size;
    int64_t best = -1;
    for (int32_t i = 0; i < sz; i++) {
        const int64_t klong = node->klongs[i];
        if (kl_get_int_type(klong) == KL_INT_TYPE_KEY && !kl_is_deleted(del, i)) {
            const int64_t cv = kl_get_compare_value(klong);
            if (best == -1 || cv < best) {
                best = cv;
            }
        }
    }
    return best;
}

/* Dag.onlyLiveKlong: the index of the latest klong of the node's only live
 * compare value; -1 if it has none or more than one. */
static int32_t only_live_klong(const struct knode *node) {
    const int64_t del = last_bitmap(node);
    int32_t index = -1;
    int64_t cv = -1;
    for (int32_t i = 0; i < node->size; i++) {
        const int64_t klong = node->klongs[i];
        if (kl_get_int_type(klong) != KL_INT_TYPE_KEY || kl_is_deleted(del, i)) {
            continue;
        }
        const int64_t c = kl_get_compare_value(klong);
        if (index >= 0 && c != cv) {
            return -1;
        }
        index = i;
        cv = c;
    }
    return index;
}

/* Dag.linkIndex: the index of the live klong of 'parent' with the compare
 * value of 'klong' that points to 'node', or -1. */
static int32_t link_index(const struct knode *parent, const struct knode *node, int64_t klong) {
    const int64_t cv = kl_get_compare_value(klong);
    const int64_t del = last_bitmap(parent);
    for (int32_t i = parent->size - 1; i >= 0; i--) {
        const int64_t k = parent->klongs[i];
        if (kl_get_int_type(k) == KL_INT_TYPE_KEY && kl_get_compare_value(k) == cv) {
            return !kl_is_deleted(del, i) && kn_get_pointer_node(parent, i) == &node->n ? i : -1;
        }
    }
    return -1;
}

/* Dag.followQuietly: follows pointer 'index' of 'node' as the writer,
 * without telling pd's listener: the node is not marked, nor put on the key
 * access path. NULL: a failure. */
static struct knode *follow_quietly(struct knode *node, int32_t index, struct putdata *pd) {
    const struct op_pointer_listener listener = pd->op.pointer_listener;
    pd->op.pointer_listener = OP_DO_NOTHING_POINTER_LISTENER;
    struct node *next = op_follow_pointer(&pd->op, &node->n, index);
    pd->op.pointer_listener = listener;
    if (next == NULL || !op_cast_ok(&pd->op, next, NODE_TYPE_KEY_NODE)) {
        return NULL;
    }
    return (struct knode *) next;
}

/* Dag.descendToSegmentRoot: goes down from the space root at tt by the
 * key's segments before 'segment' to the root of that segment's tree, into
 * *out. Rebuilds pd's key access path. */
static bool descend_to_segment_root(struct dag *d, const int64_t *key, int32_t segment,
        struct putdata *pd, struct knode **out) {
    const int64_t tt = pd->tt;
    struct kwp *kwi = &pd->op.kwi;
    pd->key_access_path.size = 0;               /* keyAccessPath.clearFast() */
    struct knode *node;
    if (!tds_find_root(&d->top_ds, tt, &pd->op, &node)) {
        return false;
    }
    for (int32_t i = 0; i < segment; i++) {
        while (!kn_is_segment_leaf(node)) {
            kn_search_lte(node, tt, key[i], kwi);
            if (!check_found(node, pd)) {
                return false;
            }
            struct node *next = op_follow_pointer(&pd->op, &node->n, kwi->pointer_index);
            if (next == NULL || !op_cast_ok(&pd->op, next, NODE_TYPE_KEY_NODE)) {
                return false;
            }
            node = (struct knode *) next;
        }
        kn_search_eq(node, tt, key[i], kwi);
        if (kwi->klong == KL_NULL) {
            return bug(pd, "Descent at %lld: segment %d not found.", (long long) tt, (int) i);
        }
        struct node *next = op_follow_pointer(&pd->op, &node->n, kwi->pointer_index);
        if (next == NULL || !op_cast_ok(&pd->op, next, NODE_TYPE_KEY_NODE)) {
            return false;
        }
        node = (struct knode *) next;
    }
    *out = node;
    return true;
}

/* Dag.descendToRootQuietly: as descend_to_segment_root, but the segment
 * root itself is followed without being marked (follow_quietly) and put on
 * the key access path by hand: after a collapse it is the old root's child,
 * which does not change, and the model marks a node only if something below
 * it changed. The nodes above it are followed as by any descent. */
static bool descend_to_root_quietly(struct dag *d, const int64_t *key, int32_t segment,
        struct putdata *pd, struct knode **out) {
    const int64_t tt = pd->tt;
    if (segment == 0) {
        pd->key_access_path.size = 0;           /* keyAccessPath.clearFast() */
        const struct op_pointer_listener listener = pd->op.pointer_listener;
        pd->op.pointer_listener = OP_DO_NOTHING_POINTER_LISTENER;
        struct knode *root;
        const bool ok = tds_find_root(&d->top_ds, tt, &pd->op, &root);
        pd->op.pointer_listener = listener;
        if (!ok || !kap_add(&pd->key_access_path, KL_NULL, root)) {
            return false;
        }
        *out = root;
        return true;
    }
    struct kwp *kwi = &pd->op.kwi;
    struct knode *node;
    if (!descend_to_segment_root(d, key, segment - 1, pd, &node)) {
        return false;
    }
    while (!kn_is_segment_leaf(node)) {
        kn_search_lte(node, tt, key[segment - 1], kwi);
        if (!check_found(node, pd)) {
            return false;
        }
        struct node *next = op_follow_pointer(&pd->op, &node->n, kwi->pointer_index);
        if (next == NULL || !op_cast_ok(&pd->op, next, NODE_TYPE_KEY_NODE)) {
            return false;
        }
        node = (struct knode *) next;
    }
    kn_search_eq(node, tt, key[segment - 1], kwi);
    if (kwi->klong == KL_NULL) {
        return bug(pd, "Descent at %lld: segment %d not found.", (long long) tt,
                (int) (segment - 1));
    }
    const int64_t klong = kwi->klong;
    struct knode *root = follow_quietly(node, kwi->pointer_index, pd);
    if (root == NULL || !kap_add(&pd->key_access_path, klong, root)) {
        return false;
    }
    *out = root;
    return true;
}

/* Dag.unlink: unlinks 'node', which existed before the transaction, at tt:
 * it loses its klongs of tt and is reported as replaced. */
static bool unlink_node(struct dag *d, struct knode *node, struct putdata *pd) {
    assert(kn_get_first_time(node) != pd->tt && "unlink of a node made in the transaction");
    if (last_time(node) == pd->tt) {
        kn_to_previous_state(d->cx, node, pd->tt - 1);
    }
    if (!key_node_replaced(&pd->node_change_listener, node)) {
        return false;
    }
    pd->stat_unlinked++;
    return true;
}

/* Dag.canTakeBack: true if 'node', made by this transaction and linked by
 * its klong 'klong' of tt in 'parent', replaces a node that existed before
 * (a split's last version, half or new root), so that it can be taken back. */
static bool can_take_back(const struct knode *node, const struct knode *parent, int64_t klong,
        const struct putdata *pd) {
    return pd_replaced_by(pd, node) != NULL && link_index(parent, node, klong) >= 0;
}

/* Dag.retarget: points every KEY klong of tt in 'p' (behind its time klong
 * of tt, where every reader stops) that points to 'from', a node that the
 * transaction made and takes back, to 'to': no written node may point to a
 * node that is never written, not even by a deleted klong (023-07, section
 * 5.1, fault 6). */
static bool retarget(struct dag *d, struct knode *p, const struct knode *from, struct knode *to,
        int64_t tt) {
    if (last_time(p) != tt) {
        return true;
    }
    for (int32_t i = p->size - 1; i >= 0; i--) {
        const int64_t klong = p->klongs[i];
        if (kl_get_int_type(klong) == KL_INT_TYPE_TIME) {
            break;
        }
        if (kl_get_int_type(klong) == KL_INT_TYPE_KEY
                && kn_get_pointer_node(p, i) == &from->n) {
            if (!kn_repoint_klong(d->cx, p, i, &to->n)) {
                return false;
            }
        }
    }
    return true;
}

/* Dag.takeBack: takes back 'node', made by this transaction by a split and
 * emptied in it: its parent's klong of tt to it, and every other klong of
 * tt there that names it, deleted ones too (retarget), is pointed to the
 * node it replaced, which existed before the transaction and is not
 * current, so nothing points to 'node' any more; the climb then deletes
 * that klong in the parent, or points it to the next child if it is the
 * empty key's (empty_key_next), as for any emptied child. 'node' is reported
 * as taken back, so it leaves D and is never written. */
static bool take_back(struct dag *d, struct knode *node, struct knode *parent, int64_t klong,
        struct putdata *pd) {
    struct knode *old = pd_replaced_by(pd, node);
    if (old == NULL || link_index(parent, node, klong) < 0 || last_time(parent) != pd->tt) {
        return bug(pd, "Take back of key node %lld at %lld: no node it replaces, or no klong "
                "of tt to it.", (long long) node->n.id, (long long) pd->tt);
    }
    if (!retarget(d, parent, node, old, pd->tt)) {
        return false;
    }
    pd_replaced_remove(pd, node);       /* C's: see dag.h */
    if (!key_node_taken_back(&pd->node_change_listener, node)) {
        return false;
    }
    pd->stat_taken_back++;
    return true;
}

/* Dag.emptyKeyNext: LE-b, the empty key first. The child of the empty key
 * of the inner node 'node', at 'depth' of the key access path, its leftmost
 * child, has emptied: the empty key is pointed to the next live child, the
 * one with the smallest live compare value but the empty key's, and that
 * child's compare value is deleted. A new klong of the empty key, with a
 * copy of the child's pointer, shadows the old one, as a time split's klong
 * does. If the latest klong of the empty key is of tt, it is pointed to the
 * next child in place instead: it is behind the time klong of tt, where
 * every reader stops. Nothing below changes. A full node is replaced by its
 * last version, with the empty key instead of the next child's klong (the
 * order stays sorted), through handle_full_node with no klong to insert. */
static bool empty_key_next(struct dag *d, struct knode *node, int32_t depth,
        struct putdata *pd) {
    assert(!kn_is_segment_leaf(node));
    const int64_t tt = pd->tt;
    const int16_t sz = node->size;
    int64_t arrayDel = KL_DELETE_NONE_BITMAP;
    int64_t arrayTime = -1;
    int32_t timeIndex = -1;
    bool hasTransDel = false;
    int32_t e = -1;                         /* the latest klong of the empty key */
    for (int32_t i = 0; i < sz; i++) {
        const int64_t klong = node->klongs[i];
        switch (kl_get_int_type(klong)) {
        case KL_INT_TYPE_TIME:
            arrayTime = kl_get_time(klong);
            timeIndex = i;
            break;
        case KL_INT_TYPE_DELETE_BITMAP:
            arrayDel = klong;
            hasTransDel = arrayTime == tt && i == sz - 1;
            break;
        default:
            if (kl_get_compare_value(klong) == 0) {
                e = i;
            }
            break;
        }
    }
    /* The next live child: the smallest live compare value but the empty
     * key's, and its latest klong. */
    const int64_t del0 = arrayDel | bits_of(node, 0);
    int32_t j = -1;
    int64_t jcv = -1;
    for (int32_t i = 0; i < sz; i++) {
        const int64_t klong = node->klongs[i];
        if (kl_get_int_type(klong) != KL_INT_TYPE_KEY || kl_is_deleted(del0, i)) {
            continue;
        }
        const int64_t cv = kl_get_compare_value(klong);
        if (j == -1 || cv <= jcv) {
            j = i;
            jcv = cv;
        }
    }
    if (e == -1 || kl_is_deleted(arrayDel, e) || j == -1) {
        return bug(pd, "LE-b at %lld in key node %lld: %s", (long long) tt,
                (long long) node->n.id,
                j == -1 ? "no next child." : "no live klong of the empty key.");
    }
    const int64_t unionDel = arrayDel | bits_of(node, jcv);
    const bool inPlace = arrayTime == tt && e > timeIndex;
    const int32_t need = (hasTransDel ? 0 : 1) + (inPlace ? 0 : 1) + (arrayTime == tt ? 0 : 1);

    if (sz + need <= d->max_node_size) {
        /* The bitmap first: in the model's terms a bitmap deletes the klongs
         * before it with the compare values of its new bits; the empty key
         * is not one of them, so the order is free. */
        if (hasTransDel) {
            node->klongs[sz - 1] = unionDel;    /* the transaction's own bitmap */
        } else if (!kn_add_delete_klong(d->cx, node, tt, unionDel)) {
            return false;
        }
        int32_t index;
        if (inPlace) {
            kn_copy_pointer(d->cx, node, e, j);
            index = e;
        } else if (!kn_add_klong_copy_pointer(d->cx, node, tt, KL_EMPTY_KEY, j, &index)) {
            return false;
        }
        struct node *pointee = kn_get_pointer_node(node, index);
        if (pointee != NULL) {
            if (!op_pointer_created(&pd->pointer_created_listener, &node->n, index, pointee)) {
                return false;
            }
        }
        if (!key_node_changed(&pd->node_change_listener, node)) {
            return false;
        }
    } else {
        struct knode *last = kn_last_version_given_del(d->cx, node, sz, tt, del0);
        if (last == NULL) {
            return false;
        }
        assert(kl_get_type(last->klongs[0]) == KL_TYPE_TIME);
        if (last->size < 2 || kl_get_compare_value(last->klongs[1]) != jcv) {
            return bug(pd, "LE-b at %lld in key node %lld: the last version does not start "
                    "with the next child.", (long long) tt, (long long) node->n.id);
        }
        last->klongs[1] = KL_EMPTY_KEY;     /* sorted still: the empty key is below the rest */
        if (!handle_full_node(d, node, depth, NULL, 0, tt, last, pd)) {
            return false;
        }
    }
    return true;
}

/* Dag.takeBackRoot: root collapse of 'root', made by a split of the
 * transaction, at 'depth' of the key access path, whose one live child is
 * that of its klong at 'only': the child takes its place in the klong of tt
 * that links it, and 'root' is taken back (collapse_root). */
static bool take_back_root(struct dag *d, struct knode *root, int32_t depth, int32_t only,
        struct putdata *pd) {
    const int64_t tt = pd->tt;
    struct knode *child = follow_quietly(root, only, pd);
    if (child == NULL) {
        return false;
    }
    if (depth == 0) {
        /* The top node of tt is updated in place (TopDs.newSuperRoot). */
        if (!tds_new_super_root(d->cx, &d->top_ds, tt, child, pd->op.access_data,
                &pd->pointer_created_listener, &pd->node_change_listener)) {
            return false;
        }
    } else {
        struct knode *leaf = kap_get(&pd->key_access_path, depth - 1);
        const int32_t i = link_index(leaf, root, kap_get_klong(&pd->key_access_path, depth));
        if (i < 0 || last_time(leaf) != tt) {
            return bug(pd, "Root collapse at %lld: no klong of tt to root %lld in its segment "
                    "leaf.", (long long) tt, (long long) root->n.id);
        }
        if (!kn_repoint_klong(d->cx, leaf, i, &child->n)
                || !key_node_changed(&pd->node_change_listener, leaf)) {
            return false;
        }
    }
    pd_replaced_remove(pd, root);       /* C's: see dag.h */
    if (!key_node_taken_back(&pd->node_change_listener, root)) {
        return false;
    }
    pd->stat_taken_back++;
    pd->stat_roots_taken_back++;
    pd->stat_collapses++;
    return true;
}

/* Dag.replaceRoot: one step of root collapse: 'root', at 'depth' of the key
 * access path, is replaced by the child of its klong at 'only', its one
 * live child: the space root through a new super root, a segment root
 * through a klong with the same compare value in the segment leaf above.
 * The child is followed before 'root' is unlinked, as unlinking drops the
 * klongs of tt, and without being marked: it does not change. */
static bool replace_root(struct dag *d, struct knode *root, int32_t depth, int32_t only,
        struct putdata *pd) {
    const int64_t tt = pd->tt;
    struct knode *child = follow_quietly(root, only, pd);
    if (child == NULL) {
        return false;
    }
    if (depth == 0) {
        if (!unlink_node(d, root, pd)
                || !tds_new_super_root(d->cx, &d->top_ds, tt, child, pd->op.access_data,
                        &pd->pointer_created_listener, &pd->node_change_listener)) {
            return false;
        }
    } else {
        struct knode *leaf = kap_get(&pd->key_access_path, depth - 1);
        const int64_t klong = kap_get_klong(&pd->key_access_path, depth);
        if (!unlink_node(d, root, pd)) {
            return false;
        }
        pd->one_kwi[0].klong = klong;
        pd->one_kwi[0].node = &child->n;
        pd->one_kwi[0].pos = pd->op.access_data;
        if (!append_klongs(d, leaf, depth - 1, pd->one_kwi, 1, pd)) {
            return false;
        }
    }
    pd->stat_collapses++;
    return true;
}

/* Dag.collapseRoot: RC, root collapse, after a climb that ended in an inner
 * node of the tree of segment 'segment': while the root of that tree is an
 * inner node with one live klong, its only child takes its place: for the
 * space root through a new super root (as time-split-2 makes one), for a
 * segment root through a klong with the same compare value in the segment
 * leaf above, which shadows the old one. The old root is unlinked. A root
 * that a split of the transaction made is collapsed too, and taken back
 * (take_back_root); a root that the transaction made fresh ends it. */
static bool collapse_root(struct dag *d, const int64_t *key, int32_t segment,
        struct putdata *pd) {
    const int64_t tt = pd->tt;
    while (true) {
        struct knode *root;
        if (!descend_to_root_quietly(d, key, segment, pd, &root)) {
            return false;
        }
        if (kn_is_segment_leaf(root)) {
            return true;
        }
        const bool made = kn_get_first_time(root) == tt;
        if (made && pd_replaced_by(pd, root) == NULL) {
            return true;
        }
        const int32_t only = only_live_klong(root);
        if (only < 0) {
            return true;
        }
        if (kl_get_compare_value(root->klongs[only]) != 0) {
            return bug(pd, "Root collapse at %lld: the one live klong of root %lld is not the "
                    "empty key.", (long long) tt, (long long) root->n.id);
        }
        if (made) {
            if (!take_back_root(d, root, pd->key_access_path.size - 1, only, pd)) {
                return false;
            }
        } else {
            if (!replace_root(d, root, pd->key_access_path.size - 1, only, pd)) {
                return false;
            }
        }
    }
}

/* Dag.deleteUpward: a delete of 'compareValue', the key's last segment, in
 * the segment leaf 'leaf' at 'depth' of the key access path, with the
 * upward unlink (see above). *isNoop: the key has no live value. */
static bool delete_upward(struct dag *d, struct knode *leaf, int32_t depth, int64_t compareValue,
        const int64_t *key, struct putdata *pd, bool *isNoop) {
    const int64_t tt = pd->tt;
    const int64_t leafDel = last_bitmap(leaf);
    const int64_t leafUnion = leafDel | bits_of(leaf, compareValue);
    bool noop;
    if (leafUnion == leafDel) {
        *isNoop = true;
        return true;
    }
    *isNoop = false;
    if (!all_keys_in(leaf, leafUnion)) {
        return append_delete_klong(d, leaf, depth, compareValue, pd, &noop);
    }

    /* The leaf is empty after the delete. Find 'stop', the node that gets
     * the delete: the first above that keeps a live klong. Nothing is
     * changed until it is known, so a climb that cannot go on changes
     * nothing above the leaf. */
    const struct kap *path = &pd->key_access_path;
    int32_t top = depth;
    int32_t stop;
    while (true) {
        struct knode *n = kap_get(path, top);
        if (kn_get_first_time(n) == tt && top > 0
                && !can_take_back(n, kap_get(path, top - 1), kap_get_klong(path, top), pd)) {
            /* Made by this transaction, and not by a split of a node that
             * existed (X5 (c)): such a node, and every node below it, holds
             * only puts of the transaction, and a transaction reaches the
             * Dag with one operation a key (Db.putKvs), so no delete of it
             * empties the node. Nothing is changed yet. */
            return bug(pd, "The upward unlink at %lld: key node %lld, made by the transaction "
                    "and not by a split, is emptied: two operations on one key in a "
                    "transaction (bergdb 023-08, X5 (c)).", (long long) tt,
                    (long long) n->n.id);
        }
        if (top == 0) {
            /* The space root. A segment leaf stays, empty, with the delete,
             * also one that the transaction made. An inner one is never
             * emptied (bergdb 023-11, review A, S1). */
            if (!kn_is_segment_leaf(n)) {
                return bug(pd, "The upward unlink at %lld: inner space root %lld is emptied "
                        "(bergdb 023-11, S1).", (long long) tt, (long long) n->n.id);
            }
            if (kn_get_first_time(n) == tt) {
                pd->stat_kept_new++;
            }
            stop = 0;
            break;
        }
        const struct knode *p = kap_get(path, top - 1);
        const int64_t c = kl_get_compare_value(kap_get_klong(path, top));
        if (all_keys_in(p, last_bitmap(p) | bits_of(p, c))) {
            top--;
            continue;
        }
        stop = top - 1;
        break;
    }

    if (stop == depth) {
        return append_delete_klong(d, leaf, depth, compareValue, pd, &noop);
    }

    pd->stat_climbs++;

    /* The segment of 'stop''s tree, from the path before it changes, for
     * root collapse. */
    int32_t segment = 0;
    for (int32_t i = 0; i < stop; i++) {
        if (kn_is_segment_leaf(kap_get(path, i))) {
            segment++;
        }
    }

    for (int32_t k = depth; k > stop; k--) {
        struct knode *n = kap_get(path, k);
        if (kn_get_first_time(n) == tt) {
            if (!take_back(d, n, kap_get(path, k - 1), kap_get_klong(path, k), pd)) {
                return false;
            }
        } else {
            if (!unlink_node(d, n, pd)) {
                return false;
            }
        }
    }

    struct knode *s = kap_get(path, stop);
    const int64_t c = kl_get_compare_value(kap_get_klong(path, stop + 1));

    if (kn_is_segment_leaf(s)) {
        return append_delete_klong(d, s, stop, c, pd, &noop);
    }
    if (smallest_live(s) != 0) {
        return bug(pd, "The upward unlink at %lld: inner node %lld has no live klong of the "
                "empty key (bergdb 023-04, LE-b).", (long long) tt, (long long) s->n.id);
    }
    if (c != 0) {
        if (!append_delete_klong(d, s, stop, c, pd, &noop)) {
            return false;
        }
    } else {
        /* The leftmost child (023-04, LE-b). */
        pd->stat_relabels++;
        if (!empty_key_next(d, s, stop, pd)) {
            return false;
        }
    }
    return collapse_root(d, key, segment, pd);
}

/* ======== dirtyNodeBound() ======== */

/* A node that dirtyNodeBound walked (Dag.Walked). */
struct walked {
    struct knode *node;
    int32_t up;                 /* the node above it on the path, -1 for the space root */
    int64_t klongs;             /* that it gets */
    int32_t collapses;          /* root collapses of its tree at most, a tree's root */
    int32_t fresh_first;        /* its fresh keys: a list through fresh_next, -1 none */
    int32_t fresh_level;        /* the segment of the keys in its fresh list missing here */
};

/* The scratch of dirtyNodeBound, through the allocator (MEM_STATE). */
struct dnb {
    struct mem *m;
    struct walked *w;
    int32_t nw, capw;
    int32_t *table;             /* node to walked index + 1, open addressing; 0 empty */
    int32_t tcap;               /* a power of 2 */
    int32_t *fresh_next;        /* per key: the next key of the same walked's fresh list */
    int32_t *order;             /* per key: scratch for freshTreeBound */
    int64_t *work;              /* freshTreeBound's work: (start, end, level) triples */
    int32_t nwork, capwork;
    const int64_t *const *keys;
    const int32_t *key_n;
};

static uint32_t ptr_hash(const void *p) {
    uint64_t x = (uint64_t) (uintptr_t) p;
    x ^= x >> 33;
    x *= UINT64_C(0xff51afd7ed558ccd);
    x ^= x >> 33;
    return (uint32_t) x;
}

static bool dnb_rehash(struct dnb *s, int32_t cap) {
    int32_t *t = mem_zalloc(s->m, (size_t) cap * sizeof *t, MEM_STATE);
    if (t == NULL) {
        return false;
    }
    for (int32_t i = 0; i < s->nw; i++) {
        uint32_t h = ptr_hash(s->w[i].node) & (uint32_t) (cap - 1);
        while (t[h] != 0) {
            h = (h + 1) & (uint32_t) (cap - 1);
        }
        t[h] = i + 1;
    }
    mem_free(s->m, s->table, (size_t) s->tcap * sizeof *s->table, MEM_STATE);
    s->table = t;
    s->tcap = cap;
    return true;
}

/* Dag.walked: the node's Walked, made with up if new; *out its index. */
static bool dnb_walked(struct dnb *s, struct knode *node, int32_t up, int32_t *out) {
    if (s->tcap > 0) {
        uint32_t h = ptr_hash(node) & (uint32_t) (s->tcap - 1);
        while (s->table[h] != 0) {
            if (s->w[s->table[h] - 1].node == node) {
                *out = s->table[h] - 1;
                return true;
            }
            h = (h + 1) & (uint32_t) (s->tcap - 1);
        }
    }
    if (s->nw == s->capw) {
        int32_t cap = s->capw == 0 ? 16 : 2 * s->capw;
        struct walked *w = mem_realloc(s->m, s->w, (size_t) s->capw * sizeof *w,
                (size_t) cap * sizeof *w, MEM_STATE);
        if (w == NULL) {
            return false;
        }
        s->w = w;
        s->capw = cap;
    }
    if (2 * (s->nw + 1) > s->tcap && !dnb_rehash(s, s->tcap == 0 ? 32 : 2 * s->tcap)) {
        return false;
    }
    struct walked *w = &s->w[s->nw];
    w->node = node;
    w->up = up;
    w->klongs = 0;
    w->collapses = 0;
    w->fresh_first = -1;
    w->fresh_level = 0;
    s->nw++;
    uint32_t h = ptr_hash(node) & (uint32_t) (s->tcap - 1);
    while (s->table[h] != 0) {
        h = (h + 1) & (uint32_t) (s->tcap - 1);
    }
    s->table[h] = s->nw;
    *out = s->nw - 1;
    return true;
}

/* Walked.fresh: key k, whose segment i is not in this leaf: a new segment
 * tree below it. Java's adds one klong for each distinct segment i, the
 * pointer to its new tree, found in a HashMap; here dag_dirty_node_bound
 * adds them when it sorts the list by that segment, before the node's
 * klongs are read. Until 2026-11-09 a scan of the list for each key:
 * quadratic in the new keys of one node (bergdb 022-06: 8.3 s for 100,000
 * new keys in one transaction, where Java took 0.7 s). */
static void dnb_fresh(struct dnb *s, int32_t wi, int32_t k, int32_t i) {
    struct walked *w = &s->w[wi];
    if (w->fresh_first < 0) {
        w->fresh_level = i;
    }
    s->fresh_next[k] = w->fresh_first;
    w->fresh_first = k;
}

/* Math.max */
static int64_t max64(int64_t a, int64_t b) {
    return a >= b ? a : b;
}

/* Dag.overflows: how many times a node of 'size' klongs, given 'klongs' more
 * and a TIME klong, can overflow. */
static int64_t overflows(const struct dag *d, int64_t klongs, int32_t size) {
    if (klongs == 0) {
        return 0;
    }
    const int64_t k = klongs + 1;
    const int64_t room = max64(0, d->max_node_size - 2 - size);
    if (k <= room) {
        return 0;
    }
    const int64_t q = max64(2, d->max_node_size / 2 - 3);
    return 1 + (k - room - 1) / q;
}

/* The keys order[a..b) sorted by their segment 'level' (insertion sort on
 * small ranges, else a heap sort: no recursion, no allocation). */
static void sort_by_segment(struct dnb *s, int32_t a, int32_t b, int32_t level) {
    int32_t *o = s->order + a;
    int32_t n = b - a;
    const int64_t *const *keys = s->keys;
#define SEG(x) keys[o[(x)]][level]
    for (int32_t start = n / 2 - 1; start >= 0; start--) {
        int32_t root = start;
        while (2 * root + 1 < n) {
            int32_t child = 2 * root + 1;
            if (child + 1 < n && SEG(child) < SEG(child + 1)) {
                child++;
            }
            if (SEG(root) >= SEG(child)) {
                break;
            }
            int32_t t = o[root];
            o[root] = o[child];
            o[child] = t;
            root = child;
        }
    }
    for (int32_t end = n - 1; end > 0; end--) {
        int32_t t = o[0];
        o[0] = o[end];
        o[end] = t;
        int32_t root = 0;
        while (2 * root + 1 < end) {
            int32_t child = 2 * root + 1;
            if (child + 1 < end && SEG(child) < SEG(child + 1)) {
                child++;
            }
            if (SEG(root) >= SEG(child)) {
                break;
            }
            t = o[root];
            o[root] = o[child];
            o[child] = t;
            root = child;
        }
    }
#undef SEG
}

static bool push_work(struct dnb *s, int64_t a, int64_t b, int64_t level) {
    if (s->nwork + 3 > s->capwork) {
        int32_t cap = s->capwork == 0 ? 96 : 2 * s->capwork;
        int64_t *w = mem_realloc(s->m, s->work, (size_t) s->capwork * sizeof *w,
                (size_t) cap * sizeof *w, MEM_STATE);
        if (w == NULL) {
            return false;
        }
        s->work = w;
        s->capwork = cap;
    }
    s->work[s->nwork++] = a;
    s->work[s->nwork++] = b;
    s->work[s->nwork++] = level;
    return true;
}

/* Dag.freshTreeBound: the nodes of the new segment trees of the keys
 * order[a..b), which share their segments before 'level' and whose segment
 * 'level' is in a new tree: its root, the in-place splits of its new nodes,
 * a new node above each level of them, and the trees below. Java recurses
 * over the levels; here a work list does (keys may have many segments), and
 * the counts add up alike. */
static bool fresh_tree_bound(const struct dag *d, struct dnb *s, int32_t a0, int32_t b0,
        int32_t level0, int64_t *out) {
    int64_t count = 0;
    s->nwork = 0;
    if (!push_work(s, a0, b0, level0)) {
        return false;
    }
    while (s->nwork > 0) {
        int32_t level = (int32_t) s->work[--s->nwork];
        int32_t b = (int32_t) s->work[--s->nwork];
        int32_t a = (int32_t) s->work[--s->nwork];
        /* The values first (key.length == level + 1), then the others by
         * their segment 'level'. */
        int32_t values = a;
        for (int32_t i = a; i < b; i++) {
            if (s->key_n[s->order[i]] == level + 1) {
                int32_t t = s->order[values];
                s->order[values] = s->order[i];
                s->order[i] = t;
                values++;
            }
        }
        int64_t klongs = values - a;    /* a value each */
        sort_by_segment(s, values, b, level);
        for (int32_t i = values; i < b; ) {
            int32_t j = i;
            while (j < b && s->keys[s->order[j]][level] == s->keys[s->order[i]][level]) {
                j++;
            }
            klongs++;                   /* the pointer to the tree below */
            if (!push_work(s, i, j, level + 1)) {
                return false;
            }
            i = j;
        }
        count += 1;
        for (int64_t ov = overflows(d, klongs, 0); ov > 0; ov = overflows(d, ov, 1)) {
            count += ov + 1;            /* the splits, and a new node above them */
        }
    }
    *out = count;
    return true;
}

static void dnb_free(struct dnb *s, int32_t count) {
    mem_free(s->m, s->w, (size_t) s->capw * sizeof *s->w, MEM_STATE);
    mem_free(s->m, s->table, (size_t) s->tcap * sizeof *s->table, MEM_STATE);
    mem_free(s->m, s->fresh_next, (size_t) count * sizeof *s->fresh_next, MEM_STATE);
    mem_free(s->m, s->order, (size_t) count * sizeof *s->order, MEM_STATE);
    mem_free(s->m, s->work, (size_t) s->capwork * sizeof *s->work, MEM_STATE);
}

/* Dag.dirtyNodeBound */
bool dag_dirty_node_bound(struct dag *d, int64_t time, const int64_t *const *keys,
        const int32_t *key_n, const bool *deletes, int32_t n, struct getdata *gd,
        struct mem *m, int64_t *out) {
    return dag_dirty_node_bound_klongs(d, time, keys, key_n, deletes, n, gd, m, out, NULL,
            NULL);
}

/* Dag.dirtyNodeBound with klongsOut, for tests: the klongs counted for the
 * walked node 'probe', before the splits' klongs. */
bool dag_dirty_node_bound_klongs(struct dag *d, int64_t time, const int64_t *const *keys,
        const int32_t *key_n, const bool *deletes, int32_t n, struct getdata *gd,
        struct mem *m, int64_t *out, const struct knode *probe, int64_t *probeKlongs) {
    *out = 0;
    if (probeKlongs != NULL) {
        *probeKlongs = -1;
    }
    struct knode *root;
    if (!tds_find_root(&d->top_ds, time, &gd->op, &root)) {
        return false;
    }
    if (root == NULL) {
        return true;
    }
    struct dnb s;
    memset(&s, 0, sizeof s);
    s.m = m;
    s.keys = keys;
    s.key_n = key_n;
    bool ok = true;
    if (n > 0) {
        s.fresh_next = mem_alloc(m, (size_t) n * sizeof *s.fresh_next, MEM_STATE);
        s.order = mem_alloc(m, (size_t) n * sizeof *s.order, MEM_STATE);
        ok = s.fresh_next != NULL && s.order != NULL;
    }
    struct kwp *kwi = &gd->op.kwi;
    bool anyDelete = false;

    for (int32_t k = 0; ok && k < n; k++) {
        const int64_t *key = keys[k];
        struct knode *node = root;
        int32_t w;
        ok = dnb_walked(&s, node, -1, &w);
        op_descent_from(&gd->op, &node->n);
        for (int32_t i = 0; ok && i < key_n[k]; i++) {
            while (!kn_is_segment_leaf(node)) {
                kn_search_lte(node, time, key[i], kwi);
                if (kwi->klong == KL_NULL) {
                    break;
                }
                struct node *next = op_follow_pointer(&gd->op, &node->n, kwi->pointer_index);
                if (next == NULL || !op_cast_ok(&gd->op, next, NODE_TYPE_KEY_NODE)
                        || !op_descent_to(&gd->op, next)) {
                    ok = false;
                    break;
                }
                node = (struct knode *) next;
                if (!dnb_walked(&s, node, w, &w)) {
                    ok = false;
                    break;
                }
            }
            if (!ok) {
                break;
            }
            if (i == key_n[k] - 1) {
                if (deletes[k]) {
                    /* The upward unlink, LE-b and root collapse (bergdb 023-07,
                     * section 5.4, K4; 023-11, B1): two klongs in every node
                     * of the path, and the inner nodes of each segment tree on
                     * it, for the collapses, at the segment leaf above that
                     * tree. */
                    anyDelete = true;
                    int32_t inner = 0;
                    for (int32_t u = w, below = -1; u >= 0; below = u, u = s.w[u].up) {
                        s.w[u].klongs += 2;
                        if (kn_is_segment_leaf(s.w[u].node)) {
                            if (below >= 0 && s.w[below].collapses < inner) {
                                s.w[below].collapses = inner;   /* 'below' is a tree's root */
                            }
                            inner = 0;
                        } else {
                            inner++;
                        }
                    }
                } else {
                    s.w[w].klongs++;
                }
                break;
            }
            kn_search_eq(node, time, key[i], kwi);
            if (kwi->klong == KL_NULL) {
                if (!deletes[k]) {
                    dnb_fresh(&s, w, k, i);
                }
                break;
            }
            struct node *next = op_follow_pointer(&gd->op, &node->n, kwi->pointer_index);
            if (next == NULL || !op_cast_ok(&gd->op, next, NODE_TYPE_KEY_NODE)
                    || !op_descent_to(&gd->op, next)) {
                ok = false;
                break;
            }
            node = (struct knode *) next;
            ok = dnb_walked(&s, node, w, &w);
        }
    }

    int64_t count = s.nw;
    if (ok && anyDelete) {
        for (int32_t i = 0; i < s.nw; i++) {
            if (s.w[i].up >= 0) {
                s.w[s.w[i].up].klongs += s.w[i].collapses;  /* summed over the trees below a leaf */
            }
        }
    }
    if (ok && probeKlongs != NULL) {
        for (int32_t i = 0; i < s.nw; i++) {
            if (s.w[i].node == probe) {
                *probeKlongs = s.w[i].klongs;
            }
        }
    }
    /* Deepest first. Java sorts the walked nodes by depth, from the
     * largest, so that each node comes after the nodes whose up it is: their
     * overflows add to its klongs, and nothing else passes between the
     * nodes. A node is walked after its up (dnb_walked takes an up that is
     * walked already), so from the last walked to the first is such an order
     * too, in one pass, and the sum is Java's. Until 2026-11-09 this went
     * over every walked node once per depth: quadratic in a long key's chain
     * of walked nodes (bergdb 022-06, u2's U2-3: 4.3 s for a 2 MB key after a
     * 512 KB key with its prefix, where Java took 0.24 s). */
    for (int32_t i = s.nw - 1; ok && i >= 0; i--) {
        struct walked *w = &s.w[i];
        assert(w->up < i && "a node's up is walked before it");
        if (w->fresh_first >= 0) {
            /* for each list of freshKeys: the keys of one segment */
            int32_t nf = 0;
            for (int32_t j = w->fresh_first; j >= 0; j = s.fresh_next[j]) {
                s.order[nf++] = j;
            }
            sort_by_segment(&s, 0, nf, w->fresh_level);
            for (int32_t a = 0; ok && a < nf; ) {
                int32_t b = a;
                while (b < nf && keys[s.order[b]][w->fresh_level]
                        == keys[s.order[a]][w->fresh_level]) {
                    b++;
                }
                w->klongs++;                /* the pointer to the new segment tree */
                int64_t c;
                ok = fresh_tree_bound(d, &s, a, b, w->fresh_level + 1, &c);
                count += ok ? c : 0;
                a = b;
            }
        }
        const int64_t ov = overflows(d, w->klongs, w->node->size);
        if (ov > 0) {
            count += ov + 1;
            if (w->up >= 0) {
                s.w[w->up].klongs += ov + 1;
            } else {
                count += ov;                /* new roots */
            }
        }
    }
    dnb_free(&s, n);
    *out = count;
    return ok;
}
