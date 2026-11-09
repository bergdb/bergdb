/* mdb: a database of Level 0 in memory; see mdb.h. */
#include "mdb.h"
#include <assert.h>
#include <string.h>
#include "knode.h"
#include "node.h"
#include "spos.h"
#include "tnode.h"
#include "topds.h"

/* The follower: every pointer is a memory pointer (DagTester's
 * DUMMY_POINTER_FOLLOWER, which Level 0 is). A pointer without an object
 * would be a stream pointer, which Level 0 has not: a failure. */
static struct node *follow(void *ctx, struct node *predecessor, int32_t pointerIndex,
        struct opdata *op) {
    (void) ctx;
    assert(pointerIndex >= 0 && "pointerIndex >= 0");
    assert(predecessor != NULL && "predecessor is null");

    struct node *result = node_pointer_node(predecessor, pointerIndex);
    if (result == NULL) {
        return NULL;    /* "This NodeFollower does not support stream pointers." */
    }
    if (!op->pointer_listener.pointer_followed(op->pointer_listener.ctx, predecessor,
            pointerIndex, result, PTR_TYPE_MEMORY)) {
        return NULL;
    }
    return result;
}

/* Db's valueNodeCreated, as far as Level 0 has it: the replay's position,
 * id and record for the value node (setIdOfNode and the serializer's
 * prepareToSerialize in Java). */
static bool value_node_created(void *ctx, struct vnode *node, const int64_t *key, int32_t key_n) {
    (void) key, (void) key_n;
    struct mdb *db = ctx;
    if (db->have_value_pos) {
        node->n.spos = db->value_spos;
        node->n.id = db->value_id;
        node->offset_from_trans = (uint32_t) (db->value_spos - db->value_tpos);
    }
    return true;
}

bool mdb_create(struct mdb *db, struct mem *m, int64_t tt0, int32_t max_node_size) {
    memset(db, 0, sizeof *db);
    db->mem = m;
    obj_ctx_init(&db->cx, m);
    db->max_node_size = max_node_size;

    /* Db.writePrimordialTransaction's nodes, as the start reads them back. */
    struct knode *root = kn_new_with_time(&db->cx, tt0);
    struct tnode *superRoot = root == NULL ? NULL
            : tds_create_super_root_from_first_key_node(&db->cx, tt0, root,
                    ACCESS_DATA_DEFAULT, &OP_DO_NOTHING_POINTER_CREATED_LISTENER);
    if (superRoot == NULL) {
        obj_free_all(&db->cx, NULL, 0);
        return false;
    }
    dag_init(&db->dag, &db->cx, superRoot, max_node_size);

    dag_new_put_data(&db->dag, &db->pd, m);
    db->pd.op.pointer_follower.follow = follow;
    db->pd.op.pointer_follower.ctx = db;
    db->pd.node_change_listener.value_node_created = value_node_created;
    db->pd.node_change_listener.ctx = db;

    db->last_transaction_time = tt0;
    obj_collect(&db->cx);
    return true;
}

void mdb_free(struct mdb *db) {
    struct tnode *superRoot = tds_get_super_root(&db->dag.top_ds);
    struct obj *roots[1] = { superRoot == NULL ? NULL : &superRoot->n.o };
    obj_free_all(&db->cx, roots, superRoot == NULL ? 0 : 1);
    db->dag.top_ds.super_root = NULL;
    pd_free(&db->pd);
}

void mdb_begin(struct mdb *db, int64_t tt) {
    assert(!db->in_trans);
    assert(tt > db->last_transaction_time);
    db->in_trans = true;
    db->pd.tt = tt;
}

bool mdb_put(struct mdb *db, const int64_t *key, int32_t n, const uint8_t *value, int32_t len) {
    assert(db->in_trans);
    bool ok = dag_put_kv(&db->dag, key, n, value, len, &db->pd);
    pd_clear_fast(&db->pd);
    db->have_value_pos = false;
    if (ok) {
        obj_collect(&db->cx);       /* a safe point between the puts */
    }
    return ok;
}

void mdb_end(struct mdb *db) {
    assert(db->in_trans);
    pd_clear(&db->pd);
    db->last_transaction_time = db->pd.tt;
    db->in_trans = false;
    obj_collect(&db->cx);
}

/* DbClock.lookupTime */
int64_t mdb_lookup_time(const struct mdb *db, int64_t wantedLookupTime) {
    const int64_t last = db->last_transaction_time;
    return wantedLookupTime > last ? last : wantedLookupTime;
}

void mdb_new_get_data(struct mdb *db, struct getdata *gd) {
    dag_new_get_data(&db->dag, gd);
    gd->op.pointer_follower.follow = follow;
    gd->op.pointer_follower.ctx = db;
}

void mdb_new_get_many(struct mdb *db, struct getmany *g) {
    gm_init(g, &db->dag, db->mem);
    g->gd.op.pointer_follower.follow = follow;
    g->gd.op.pointer_follower.ctx = db;
    g->collect = &db->cx;
}

bool mdb_get_one(struct mdb *db, int64_t lookupTime, const int64_t *key, int32_t n,
        struct getdata *gd, struct vnode **out) {
    /* Limits the lookup time so that it is strictly less than the
     * transaction time of any running or future transaction. */
    int64_t time = mdb_lookup_time(db, lookupTime);
    gd->actual_lookup_time = time;
    gd->node_depth = 0;
    return dag_get_one(&db->dag, gd->actual_lookup_time, key, n, gd, out);
}

bool mdb_get_many(struct mdb *db, struct getmany *g) {
    g->actual_lookup_time = mdb_lookup_time(db, g->lookup_time);
    bool ok = dag_get_many(&db->dag, g);
    return ok;
}

int64_t mdb_recount(struct mdb *db) {
    struct tnode *superRoot = tds_get_super_root(&db->dag.top_ds);
    struct obj *roots[1] = { &superRoot->n.o };
    return obj_recount(&db->cx, roots, 1, NULL);
}
