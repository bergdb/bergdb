/* db: the database, Java's Db; see db.h. Java's names in the comments. */
#include "db.h"
#include <assert.h>
#include <inttypes.h>
#include <string.h>
#include "handle.h"
#include "jsem.h"
#include "keys.h"
#include "klong.h"
#include "knode.h"
#include "meta.h"
#include "node.h"
#include "nstream.h"
#include "nwrite.h"
#include "plat.h"
#include "recover.h"
#include "snode.h"
#include "spos.h"
#include "starter.h"
#include "strans.h"
#include "topds.h"
#include "vnode.h"

/* DbConstants.DUMMY_KEY, "/#i/-dummy", and RecoverableStream.META_BLOCK_DISTANCE,
 * the dummy value's size (Db.setStartupDistance). */
#define DUMMY_IKEY "/#i/-dummy"
#define DUMMY_VALUE_SIZE 200000

static enum err_code nomem(struct err *e) {
    return err_set(e, ERR_NOMEM, "OutOfMemoryError", "out of memory");
}

/* ======== The state ======== */

/* assertDbStateIsActive */
enum err_code db_check_active(const struct db *db, const char *method, struct err *e) {
    switch (db->state) {
    case DB_ACTIVE:
        return ERR_OK;
    case DB_STOPPING:
        return err_set(e, ERR_STATE, "DbStoppingException",
                "Cannot call %s() while DB is stopping.", method);
    case DB_FAILED:
        return err_set(e, ERR_FAILED, "DbFailedException", "Cannot call %s(): the database "
                "failed (the cause) and must be restarted. Cause: %s: %s", method,
                db->failure.java, db->failure.text);
    case DB_ZERO:
        break;
    }
    return err_set(e, ERR_STATE, "IllegalDbStateException",
            "Cannot call %s() when DB state is ZERO.", method);
}

/* setFailed: the first failure is kept, and the state is FAILED, if the
 * database is active. Returns the state before. */
static enum db_state set_failed(struct db *db, const struct err *cause) {
    enum db_state before = db->state;
    if (before == DB_ACTIVE) {
        db->failure = *cause;
        db->state = DB_FAILED;
    }
    return before;
}

/* fail(t, e): a failure after a transaction's go point (005-01). */
static enum err_code fail(struct db *db, const struct trans *t, struct err *e) {
    struct err cause = *e;
    if (set_failed(db, &cause) == DB_STOPPING) {
        return cause.code;
    }
    if (cause.code == ERR_FAILED) {
        return ERR_FAILED;
    }
    return err_set(e, ERR_FAILED, "DbFailedException", "The transaction at time %" PRId64
            " failed after it began (the cause); nothing is undone. The database takes no "
            "more transactions or reads and must be restarted. Cause: %s: %s",
            t == NULL ? (int64_t) -1 : t->tt, cause.java, cause.text);
}

/* failOnStorage: a read or a sync that failed on the storage (005-30). */
enum err_code db_fail_on_storage(struct db *db, const char *what, struct err *e) {
    struct err cause = *e;
    enum db_state before = set_failed(db, &cause);
    if (before != DB_ACTIVE && before != DB_FAILED) {
        return cause.code;
    }
    return err_set(e, ERR_FAILED, "DbFailedException", "%s failed on the storage (the "
            "cause). The database takes no more transactions or reads and must be "
            "restarted. Cause: %s: %s", what, cause.java, cause.text);
}

/* ======== Ids and the marking (Db's listeners) ======== */

/* setIdOfNode: the next vpos as the node's id and position. */
static void set_id_of_node(struct db *db, struct node *node) {
    int64_t vpos = db->next_vpos;
    node->id = vpos;
    node->spos = vpos;
    db->next_vpos = spos_next_vpos(db->next_vpos);     /* ExecuteData.increaseNextVpos */
}

/* registerNewNode: canonical, and in the node table (Cache3.register); the
 * table's access clock changes no byte. false: NOMEM. */
static bool register_new_node(struct db *db, struct node *node) {
    node_set_canonical(node, true);
    struct node *registered;
    if (!nt_register(&db->node_table, node, &registered)) {
        err_set(&db->op_err, ERR_NOMEM, "OutOfMemoryError", "out of memory");
        return false;
    }
    return true;
}

/* markAtEndOfOp */
static bool mark_at_end_of_op(struct db *db, struct node *node) {
    if (db->trans_info == NULL) {
        return true;
    }
    if (node == NULL || !node_is_index_node(node)) {
        return true;
    }
    if (db->n_op_marks == db->cap_op_marks) {
        int32_t ncap = db->cap_op_marks == 0 ? 64 : db->cap_op_marks * 2;
        struct node **n = mem_realloc(db->mem, db->op_marks,
                (size_t) db->cap_op_marks * sizeof *n, (size_t) ncap * sizeof *n, MEM_STATE);
        if (n == NULL) {
            return false;
        }
        db->op_marks = n;
        db->cap_op_marks = ncap;
    }
    db->op_marks[db->n_op_marks++] = node;
    return true;
}

/* The type of a got-dirty node for TransInfo (snode.h's NODE_TOP, NODE_KEY). */
static int32_t dirty_type(const struct node *node) {
    return node_is_top_node(node) ? NODE_TOP : NODE_KEY;
}

/* TransInfo.addGotDirtyNode, the list a counted holder of each node. */
static bool add_got_dirty_node(struct db *db, struct ts_info *info, struct node *node) {
    struct err e;
    if (ts_info_add_node(info, db->mem, node, node->id, dirty_type(node), &e) != ERR_OK) {
        return false;
    }
    obj_retain(&node->o);
    return true;
}

/* makeDirtyIfNeeded */
static bool make_dirty_if_needed(struct db *db, struct node *node) {
    if (db->trans_info == NULL) {
        return true;
    }
    if (!node_is_index_node(node)) {
        return true;
    }
    if (!node_is_dirty(node)) {
        if (!add_got_dirty_node(db, db->trans_info, node)) {
            return false;
        }
        node_set_dirty(node, true);
        if (db->trans->touch) {
            db->trans->dirtied_nodes++;
            db->trans->dirtied_bytes += node_is_top_node(node)
                    ? nw_top_byte_size((const struct tnode *) node)
                    : nw_key_byte_size((const struct knode *) node);
        }
    }
    return true;
}

/* endOfOp: the operation's marks become dirty if it changed something. */
static bool end_of_op(struct db *db, bool always) {
    bool ok = true;
    if (always || db->op_changed) {
        for (int32_t i = 0; i < db->n_op_marks && ok; i++) {
            ok = make_dirty_if_needed(db, db->op_marks[i]);
        }
    }
    db->n_op_marks = 0;
    db->op_changed = false;
    return ok;
}

/* replacedInTrans.add: an identity set, here a list of counted holders and
 * the flag OBJ_REPLACED. */
static bool add_replaced(struct db *db, struct node *node) {
    if ((node->o.flags & OBJ_REPLACED) != 0) {
        return true;
    }
    if (db->n_replaced == db->cap_replaced) {
        int32_t ncap = db->cap_replaced == 0 ? 16 : db->cap_replaced * 2;
        struct node **n = mem_realloc(db->mem, db->replaced,
                (size_t) db->cap_replaced * sizeof *n, (size_t) ncap * sizeof *n, MEM_STATE);
        if (n == NULL) {
            return false;
        }
        db->replaced = n;
        db->cap_replaced = ncap;
    }
    node->o.flags |= OBJ_REPLACED;
    obj_retain(&node->o);
    db->replaced[db->n_replaced++] = node;
    return true;
}

/* replacedInTrans.clear() */
static void clear_replaced(struct db *db) {
    for (int32_t i = 0; i < db->n_replaced; i++) {
        db->replaced[i]->o.flags &= (uint16_t) ~OBJ_REPLACED;
        obj_release(&db->cx, &db->replaced[i]->o);
    }
    db->n_replaced = 0;
}

/* endOfTrans: the nodes that the transaction replaced leave its got-dirty
 * list and are clean again, but those that its touch made dirty. */
static void end_of_trans(struct db *db) {
    struct ts_info *info = db->trans_info;
    if (db->n_replaced > 0 && info != NULL) {
        const int32_t keep = db->trans != NULL && db->trans->touch ? db->touch_marks : 0;
        int32_t kept = 0;
        for (int32_t i = 0; i < info->ndirty; i++) {
            struct node *n = info->gotDirtyNodes[i].node;
            if (i >= keep && (n->o.flags & OBJ_REPLACED) != 0) {
                node_set_dirty(n, false);
                obj_release(&db->cx, &n->o);
            } else {
                info->gotDirtyNodes[kept++] = info->gotDirtyNodes[i];
            }
        }
        info->ndirty = kept;
    }
    clear_replaced(db);
    db->touch_marks = 0;
}

/* The NodeChangeListener of Db.newPutData. A false return is a failure of
 * the listener's (NOMEM), which the Dag returns as its own. */
static bool l_top_node_created(void *ctx, struct tnode *node) {
    struct db *db = ctx;
    assert(!node_is_dirty(&node->n) && "node is dirty");
    set_id_of_node(db, &node->n);
    if (!register_new_node(db, &node->n)) {
        return false;
    }
    if (!mark_at_end_of_op(db, &node->n)) {
        return false;
    }
    db->op_changed = true;
    return true;
}

static bool l_key_node_created(void *ctx, struct knode *node) {
    struct db *db = ctx;
    set_id_of_node(db, &node->n);
    if (!register_new_node(db, &node->n)) {
        return false;
    }
    if (!mark_at_end_of_op(db, &node->n)) {
        return false;
    }
    db->op_changed = true;
    return true;
}

static bool l_key_node_changed(void *ctx, struct knode *node) {
    struct db *db = ctx;
    if (!mark_at_end_of_op(db, &node->n)) {
        return false;
    }
    db->op_changed = true;
    return true;
}

static bool l_value_node_created(void *ctx, struct vnode *node, const int64_t *key,
        int32_t key_n) {
    struct db *db = ctx;
    set_id_of_node(db, &node->n);
    if (!tns_add_value_node(&db->trans_nodes, node, key, key_n)) {
        return false;
    }
    db->op_changed = true;
    return true;
}

static bool l_key_node_replaced(void *ctx, struct knode *node) {
    struct db *db = ctx;
    return db->trans_info == NULL || add_replaced(db, &node->n);
}

static bool l_top_node_replaced(void *ctx, struct tnode *node) {
    struct db *db = ctx;
    return db->trans_info == NULL || add_replaced(db, &node->n);
}

/* The PointerListener of Db.newPutData: the Dag's (the access path), then
 * the mark. The Dag's own is kept in db->dag_listener. */
static bool l_super_root_accessed(void *ctx, struct tnode *superRoot);
static bool l_pointer_followed(void *ctx, struct node *predecessor, int32_t pointerIndex,
        struct node *result, int32_t pointerType);

/* ======== The followers ======== */

/* The writer's follower (NodeCollection.writer()) and the readers'
 * (NodeCollection.followPointer): ncoll.h's (012-10), which load a node that
 * is not in memory, with Rule R. A failure's text goes to db->op_err, unless
 * a listener has put its own there. */
static struct node *follow(struct db *db, struct node *predecessor, int32_t pointerIndex,
        struct opdata *op, bool writer) {
    err_clear(&db->node_coll.err);
    struct node *result = writer
            ? nc_follow_writer(&db->node_coll, predecessor, pointerIndex, op)
            : nc_follow_reader(&db->node_coll, predecessor, pointerIndex, op);
    if (result == NULL && db->op_err.code == ERR_OK) {
        db->op_err = db->node_coll.err;
        if (db->op_err.code == ERR_OK) {
            err_set(&db->op_err, ERR_NOMEM, "OutOfMemoryError", "out of memory");
        }
    }
    return result;
}

static struct node *writer_follow(void *ctx, struct node *predecessor, int32_t pointerIndex,
        struct opdata *op) {
    return follow(ctx, predecessor, pointerIndex, op, true);
}

static struct node *reader_follow(void *ctx, struct node *predecessor, int32_t pointerIndex,
        struct opdata *op) {
    return follow(ctx, predecessor, pointerIndex, op, false);
}

/* The maintenance follower (reclaim's, 012-11): nc_follow_maintenance, its
 * failure's text in db->op_err as follow's. */
static struct node *maintenance_follow(void *ctx, struct node *predecessor,
        int32_t pointerIndex, struct opdata *op) {
    struct db *db = ctx;
    err_clear(&db->node_coll.err);
    struct node *result = nc_follow_maintenance(&db->node_coll, predecessor, pointerIndex, op);
    if (result == NULL && db->op_err.code == ERR_OK) {
        db->op_err = db->node_coll.err;
        if (db->op_err.code == ERR_OK) {
            err_set(&db->op_err, ERR_NOMEM, "OutOfMemoryError", "out of memory");
        }
    }
    return result;
}

struct op_follower db_maintenance_follower(struct db *db) {
    struct op_follower f = { maintenance_follow, db };
    return f;
}

static bool l_super_root_accessed(void *ctx, struct tnode *superRoot) {
    struct db *db = ctx;
    if (!db->dag_listener.super_root_accessed(db->dag_listener.ctx, superRoot)) {
        return false;
    }
    if (!mark_at_end_of_op(db, &superRoot->n)) {
        err_set(&db->op_err, ERR_NOMEM, "OutOfMemoryError", "out of memory");
        return false;
    }
    return true;
}

static bool l_pointer_followed(void *ctx, struct node *predecessor, int32_t pointerIndex,
        struct node *result, int32_t pointerType) {
    struct db *db = ctx;
    if (!db->dag_listener.pointer_followed(db->dag_listener.ctx, predecessor, pointerIndex,
            result, pointerType)) {
        err_set(&db->op_err, ERR_NOMEM, "OutOfMemoryError", "out of memory");
        return false;
    }
    if (!mark_at_end_of_op(db, result)) {
        err_set(&db->op_err, ERR_NOMEM, "OutOfMemoryError", "out of memory");
        return false;
    }
    return true;
}

/* Db.newPutData's PointerCreatedListener: Eviction.largeValueCreated
 * (012-12). */
static bool l_pointer_created(void *ctx, struct node *from, int32_t index, struct node *to) {
    struct db *db = ctx;
    if (to->o.kind == OBJ_VALUE && ((struct vnode *) to)->len > EV_LARGE_VALUE
            && from->o.kind == OBJ_KEY) {
        if (!ev_large_value_created(&db->ev, (struct knode *) from, index,
                (struct vnode *) to)) {
            err_set(&db->op_err, ERR_NOMEM, "OutOfMemoryError", "out of memory");
            return false;
        }
    }
    return true;
}

/* createPutAndGetData: Db.newPutData and newGetData. */
static void create_put_and_get_data(struct db *db) {
    dag_new_put_data(&db->dag, &db->put_data, db->mem);
    struct putdata *pd = &db->put_data;
    pd->op.pointer_follower.follow = writer_follow;
    pd->op.pointer_follower.ctx = db;
    pd->node_change_listener.top_node_created = l_top_node_created;
    pd->node_change_listener.key_node_created = l_key_node_created;
    pd->node_change_listener.key_node_changed = l_key_node_changed;
    pd->node_change_listener.value_node_created = l_value_node_created;
    pd->node_change_listener.key_node_replaced = l_key_node_replaced;
    pd->node_change_listener.top_node_replaced = l_top_node_replaced;
    pd->node_change_listener.ctx = db;
    db->dag_listener = pd->op.pointer_listener;
    pd->op.pointer_listener.super_root_accessed = l_super_root_accessed;
    pd->op.pointer_listener.pointer_followed = l_pointer_followed;
    pd->op.pointer_listener.ctx = db;
    /* Db's PointerCreatedListener: eviction's large values (012-12); the
     * residents are the allocator's counts. No byte. */
    pd->pointer_created_listener.pointer_created = l_pointer_created;
    pd->pointer_created_listener.ctx = db;
    db_new_get_data(db, &db->get_data);
}

void db_new_get_data(struct db *db, struct getdata *gd) {
    dag_new_get_data(&db->dag, gd);
    gd->op.pointer_follower.follow = reader_follow;
    gd->op.pointer_follower.ctx = db;
}

void db_new_get_many(struct db *db, struct getmany *g) {
    gm_init(g, &db->dag, db->mem);
    g->gd.op.pointer_follower.follow = reader_follow;
    g->gd.op.pointer_follower.ctx = db;
    g->collect = NULL;
}

/* ======== The creation and the start ======== */

/* writePrimordialTransaction: the root key node and the first top node, in
 * a record of their own, at the stream's start; nothing stays in memory
 * (the start reads them back). */
static enum err_code write_primordial_transaction(struct db *db, struct err *e) {
    int64_t tt;
    /* transactionBegin() before the try (005-18): when it throws, no
     * transaction has begun. */
    enum err_code rc = dbclock_transaction_begin(&db->clock, &tt, e);
    if (rc != ERR_OK) {
        return rc;
    }
    dbclock_transaction_end(&db->clock);

    /* The root's id first, and canonical. */
    struct knode *root = kn_new_with_time(&db->cx, tt);
    if (root == NULL) {
        return nomem(e);
    }
    set_id_of_node(db, &root->n);
    node_set_canonical(&root->n, true);
    struct tnode *superRoot = tds_create_super_root_from_first_key_node(&db->cx, tt, root,
            ACCESS_DATA_DEFAULT, &OP_DO_NOTHING_POINTER_CREATED_LISTENER);
    if (superRoot == NULL) {
        return nomem(e);
    }
    set_id_of_node(db, &superRoot->n);

    struct meta *meta = &db->rs.meta;
    meta_set_id(meta, db->database_id);
    meta_set_startup_distance(meta, db->startup_distance);
    if (!meta_set_max_node_size(meta, db->max_node_size)) {       /* 005-50 */
        return err_set(e, ERR_ARG, "IllegalArgumentException", "bad maxNodeSize %d",
                (int) db->max_node_size);
    }
    meta_set_time(meta, tt);

    /* trans: tt, internal, startupPos 0; a TransNodes of its own. */
    struct transnodes tn;
    tns_init(&tn, &db->cx, db->mem);
    struct ser_out out;
    rc = ERR_OK;
    if (!tns_add_key_node(&tn, root) || !tns_add_top_node(&tn, superRoot)) {
        rc = nomem(e);
    } else {
        rc = ser_append_nodes(&db->serializer, &db->rs, &tn, tt, 0, NULL, superRoot,
                db->record_limit, &out, e);
    }
    tns_clear(&tn);
    tns_free(&tn);
    obj_collect(&db->cx);
    if (rc != ERR_OK) {
        return rc;
    }
    assert(out.last_pos + 1 == DB_CREATION_LENGTH && "creation length");
    /* This is needed to be able to use sync(). */
    db->end_of_last_trans = out.last_pos + 1;
    return ERR_OK;
}

static void free_all(struct db *db);

enum err_code db_open(struct db *db, const char *dir, const struct db_config *cfg,
        struct mem *m, struct db_start_info *info, struct err *e) {
    enum err_code rc;
    memset(db, 0, sizeof *db);
    memset(info, 0, sizeof *info);
    db->mem = m;
    rc_init(&db->reclaim, m);
    obj_ctx_init(&db->cx, m);
    nt_init(&db->node_table, &db->cx, m);
    err_clear(&db->failure);
    err_clear(&db->op_err);
    db->state = DB_ZERO;
    db->max_node_size = cfg->max_node_size;
    db->startup_distance = cfg->startup_distance;
    db->cache_size_indicator = cfg->cache_size_indicator;
    ev_init(&db->ev, &db->cx, m, cfg->cache_size_indicator < 1 ? 1 : cfg->cache_size_indicator);
    db->record_limit = cfg->record_limit > 0 ? cfg->record_limit : ST_MAX_RECORD_SIZE;
    db->second_top_ordinal = cfg->second_top_ordinal > 0 ? cfg->second_top_ordinal : 1;
    if (cfg->max_node_size != 8 && cfg->max_node_size != 14 && cfg->max_node_size != 30
            && cfg->max_node_size != 62) {
        return err_set(e, ERR_ARG, "IllegalArgumentException", "Bad maxNodeSize, %d.",
                (int) cfg->max_node_size);
    }
    if (cfg->cache_size_indicator < 1) {
        /* Cache3.setSizeIndicator's assert (C's asserts are on, as Java's -ea). */
        return err_set(e, ERR_ARG, "AssertionError", "a cache size indicator under 1, %lld",
                (long long) cfg->cache_size_indicator);
    }
    if (cfg->startup_distance < 10) {
        return err_set(e, ERR_ARG, "IllegalArgumentException", "Too small, %d",
                (int) cfg->startup_distance);
    }
    if (cfg->retain_duration < CLK_UNITS_PER_SEC) {
        return err_set(e, ERR_ARG, "IllegalArgumentException", "retainDuration is too small,"
                " must be at least one second (%lld), was %lld.",
                (long long) CLK_UNITS_PER_SEC, (long long) cfg->retain_duration);
    }
    /* reclaim.setStepReserve(b.reclaimStepReserve), setRetainDuration(b's) */
    if (cfg->step_reserve < 0) {
        return err_set(e, ERR_ARG, "IllegalArgumentException", "Illegal step reserve, %lld",
                (long long) cfg->step_reserve);
    }
    if (cfg->step_reserve > 0) {
        db->reclaim.stepReserve = cfg->step_reserve;
    }
    db->reclaim.retainDuration = cfg->retain_duration;

    /* The Db constructor. */
    if (dir != NULL) {
        rc = stream_open_dir_rw(&db->stream, dir, cfg->buffer_size, m, e);
        if (rc != ERR_OK) {
            return rc;
        }
    } else {
        stream_open_memory(&db->stream, m);
    }
    db->stream_open = true;
    nc_init(&db->node_coll, &db->cx, m, &db->stream, &db->node_table);
    ts_init(&db->trans_seq, m);
    tns_init(&db->trans_nodes, &db->cx, m);
    ser_init(&db->serializer, m);
    rc = kms_init(&db->key_mod_set, m, e);
    if (rc != ERR_OK) {
        free_all(db);
        return rc;
    }
    db->kms_made = true;
    db->end_of_last_trans = stream_length(&db->stream);
    rs_init(&db->rs, &db->stream);
    meta_set_startup_distance(&db->rs.meta, cfg->startup_distance);
    dbclock_init(&db->clock, cfg->clock, cfg->clock_ctx);
    rc = ts_startup_pos_init(&db->startup_pos, 0, e);
    assert(rc == ERR_OK);
    db->next_vpos = 0;

    /* start(): startInner */
    /* handleEmptyStream: determineDatabaseId and writePrimordialTransaction */
    if (stream_length(&db->stream) == 0) {
        if (cfg->random_id) {
            plat_random(db->database_id, 16);       /* DatabaseId.createRandom */
        } else {
            memcpy(db->database_id, cfg->id, 16);
        }
        rc = write_primordial_transaction(db, e);
        if (rc != ERR_OK) {
            free_all(db);
            return rc;
        }
        info->created = true;
    }
    /* Db.startInner's checks and recovery, then handleStartParams,
     * readTransactions and DbStarter (012-10, starter.h). */
    struct sr_env env = { m, &db->cx, &db->rs, &db->node_table, &db->node_coll, &db->dag,
            &db->trans_seq, db->max_node_size, db->second_top_ordinal };
    struct rs_recovery plan;
    struct sr_result res;
    rc = sr_check_and_recover(&env, &plan, e);
    if (rc == ERR_OK) {
        rc = sr_start(&env, &res, e);
        db->dag_made = res.dag_made;
        db->newest_written_top = res.newest_written_top;   /* its count taken over */
    }
    if (rc == ERR_OK) {
        /* handleStartParams, setLastTransTimeOfDbClock, createPutAndGetData */
        db->startup_distance = res.startup_distance;
        ts_startup_pos_set(&db->startup_pos, res.startup_pos);
        ts_startup_pos_release_for_evict(&db->startup_pos);
        dbclock_set_last_trans_time(&db->clock, res.last_trans_time);
        create_put_and_get_data(db);
        info->start_pos = res.start_pos;
        info->startup_distance = -1;
        info->start_time = res.start_time;
        info->trans_count = res.trans_count;
        info->last_pos = res.last_pos;
        db->state = DB_ACTIVE;
        rc = rc_init_from_db(db, e);    /* reclaim.initFromDb() */
    }
    if (rc != ERR_OK) {
        if (rc == ERR_FAILED) {
            /* A read of reclaim's table that failed on the storage: Java's
             * DbFailedException; here its cause, as no database is left to
             * fail (bergdb.h, bergdb_open). */
            *e = db->failure;
            rc = e->code;
        }
        /* A start that throws closes its storage: what it appended, recovery's
         * fill, is written (005-32). */
        db->state = DB_STOPPING;
        if (db->stream_open) {
            struct err e2;
            (void) stream_finish(&db->stream, &e2);
            db->stream_open = false;
        }
        free_all(db);
        return rc;
    }
    db_evict(db);       /* eviction.afterTransaction: after the startup's loads (012-12) */
    return ERR_OK;
}

/* ======== execute ======== */

/* checkSize (005-17): the value nodes at most StoredTrans.valueLimit(). */
static enum err_code check_size(const struct db *db, const struct trans *t, struct err *e) {
    int64_t bytes = 0;
    for (int32_t i = 0; i < t->nkvs; i++) {
        bytes += nw_value_byte_size_long(t->kvs[i]->len, t->kvs[i]->key_n);
    }
    const int64_t limit = db->record_limit / 8 * 7;
    if (bytes > limit) {
        return err_set(e, ERR_LIMIT, "DbException", "The transaction is too large: its values "
                "and keys take %lld bytes in the stream, more than %lld.", (long long) bytes,
                (long long) limit);
    }
    return ERR_OK;
}

/* getOneInternal: the first available time (reclaim's), the actual
 * lookup time, Dag.getOne, the get count. */
static enum err_code get_one_internal(struct db *db, int64_t lookupTime, const int64_t *key,
        int32_t n, struct getdata *gd, struct vnode **out, struct err *e) {
    const int64_t firstAvailable = db_first_available_time(db);
    if (lookupTime < firstAvailable) {
        return err_set(e, ERR_NOT_AVAILABLE, "LookupTimeNotAvailableException", "Cannot lookup "
                "at time %lld, the first time available for lookup is %lld.",
                (long long) lookupTime, (long long) firstAvailable);
    }
    gd->op.access_data = ACCESS_DATA_DEFAULT;
    int64_t time = dbclock_lookup_time(&db->clock, lookupTime);
    gd->actual_lookup_time = time;
    gd->node_depth = 0;
    err_clear(&db->op_err);
    if (!dag_get_one(&db->dag, gd->actual_lookup_time, key, n, gd, out)) {
        if (db->op_err.code != ERR_OK) {
            *e = db->op_err;
            return db_fail_on_storage(db, "A read", e);
        }
        return nomem(e);
    }
    db->get_op_count++;
    return ERR_OK;
}

/* warmup: the pairs' keys read at the latest time; no byte depends on it
 * (Trans.warmupGetData: no listener). */
static enum err_code warmup(struct db *db, const struct trans *t, struct err *e) {
    const int64_t readTime = dbclock_lookup_time(&db->clock, INT64_MAX);
    struct getdata gd;
    dag_new_get_data(&db->dag, &gd);
    gd.op.pointer_listener = OP_DO_NOTHING_POINTER_LISTENER;
    gd.op.pointer_follower.follow = reader_follow;
    gd.op.pointer_follower.ctx = db;
    for (int32_t i = 0; i < t->nkvs; i++) {
        struct vnode *v;
        enum err_code rc = get_one_internal(db, readTime, t->kvs[i]->key, t->kvs[i]->key_n,
                &gd, &v, e);
        if (rc != ERR_OK) {
            return rc;
        }
    }
    return ERR_OK;
}

/* checkDirtyNodes (005-31): a transaction whose index nodes could take more
 * than StoredTrans.dirtyLimit() bytes is refused. */
static enum err_code check_dirty_nodes(struct db *db, const struct trans *t, struct err *e) {
    const int64_t limit = db->record_limit - db->record_limit / 16;
    const int64_t nodeBytes = 32 + 16 * (int64_t) (db->max_node_size + 1) + 16;
    const int64_t topBytes = 2 * (40 + 16 * INT64_C(64) + 16);
    const int64_t len48 = stream_length(&db->stream) / 48;
    const int64_t height = 2 + 63 - j_nlz64(len48 > 1 ? len48 : 1);

    int64_t cheap = 0;
    for (int32_t i = 0; i < t->nkvs; i++) {
        cheap += 3 * height * t->kvs[i]->key_n + 3;
    }
    if (cheap <= (limit - topBytes) / nodeBytes) {
        return ERR_OK;
    }

    const int32_t count = t->nkvs;
    const int64_t **keys = mem_alloc(db->mem, (size_t) (count > 0 ? count : 1) * sizeof *keys,
            MEM_STATE);
    int32_t *keyN = mem_alloc(db->mem, (size_t) (count > 0 ? count : 1) * sizeof *keyN,
            MEM_STATE);
    bool *deletes = mem_alloc(db->mem, (size_t) (count > 0 ? count : 1) * sizeof *deletes,
            MEM_STATE);
    enum err_code rc = ERR_OK;
    if (keys == NULL || keyN == NULL || deletes == NULL) {
        rc = nomem(e);
    } else {
        int32_t n = 0;
        int64_t nodes = 0;
        for (int32_t i = 0; i < count; i++) {
            const struct tr_kv *kv = t->kvs[i];
            if (kv->has_tf && kv->tf.key != NULL) {
                nodes += 3 * height * kv->key_n + 3;
            } else {
                keys[n] = kv->key;
                keyN[n] = kv->key_n;
                deletes[n] = kv->len < 0 && !(kv->has_tf && kv->tf.value != NULL);
                n++;
            }
        }
        const int64_t time = dbclock_lookup_time(&db->clock, INT64_MAX);
        struct getdata gd;
        db_new_get_data(db, &gd);
        int64_t bound = 0;
        err_clear(&db->op_err);
        if (!dag_dirty_node_bound(&db->dag, time, keys, keyN, deletes, n, &gd, db->mem,
                &bound)) {
            if (db->op_err.code != ERR_OK) {
                *e = db->op_err;
                rc = db_fail_on_storage(db, "A read", e);
            } else {
                rc = nomem(e);
            }
        } else {
            nodes += bound;
            if (nodes > (limit - topBytes) / nodeBytes) {
                rc = err_set(e, ERR_LIMIT, "DbException", "The transaction is too large: the "
                        "index nodes it can make dirty or create, up to %lld, could take %lld "
                        "bytes in a record, more than %lld (bergdb 005-31). A larger update "
                        "must be split into transactions.", (long long) nodes,
                        (long long) (nodes * nodeBytes + topBytes), (long long) limit);
            }
        }
    }
    const size_t c = (size_t) (count > 0 ? count : 1);
    mem_free(db->mem, keys, c * sizeof *keys, MEM_STATE);
    mem_free(db->mem, keyN, c * sizeof *keyN, MEM_STATE);
    mem_free(db->mem, deletes, c * sizeof *deletes, MEM_STATE);
    return rc;
}

/* stmCheckConflicts: a key of the read set written after the read time. */
static enum err_code stm_check_conflicts(struct db *db, const struct trans *t, struct err *e) {
    for (int32_t i = 0; i < t->nread; i++) {
        if (kms_modified_after(&db->key_mod_set, t->read_time, t->read_key_hashes[i])) {
            return err_set(e, ERR_RERUN, "RerunException", "key hash %lld",
                    (long long) t->read_key_hashes[i]);
        }
    }
    return ERR_OK;
}

/* touchRange's stop condition: the keys up to 'to' (inclusive; NULL: all). */
struct touch_stop {
    const int64_t *to;
    int32_t to_n;
};

static int32_t touch_handle_kvt(void *ctx, const struct kvt *kvt) {
    const struct touch_stop *s = ctx;
    if (s->to != NULL && keys_compare_keys(kvt->key, kvt->key_n, s->to, s->to_n) > 0) {
        return GM_STOP;
    }
    return GM_CONTINUE;
}

/* touchRange(from, to): visits, as the writer, every node reachable at the
 * transaction time for the keys after 'from' (exclusive; NULL: from the
 * first key) up to 'to' (inclusive; NULL: to the last key), with the
 * putData's pointer listener, which marks them (reclaim's steps, 012-11;
 * Trans.touch). */
static enum err_code touch_range(struct db *db, const int64_t *from, int32_t from_n,
        const int64_t *to, int32_t to_n, struct err *e) {
    struct putdata *pd = &db->put_data;
    struct getmany g;
    gm_init(&g, &db->dag, db->mem);         /* dag.newGetMany() */
    g.gd.op.pointer_follower = pd->op.pointer_follower;
    g.gd.op.pointer_listener = pd->op.pointer_listener;    /* makes nodes dirty */
    g.gd.op.access_data = pd->op.access_data;
    g.lookup_time = db->trans->tt;
    g.actual_lookup_time = db->trans->tt;  /* Dag.getMany() uses this one. */
    g.start_key = from;
    g.start_key_n = from_n;
    g.inclusive = false;
    struct touch_stop ts = { to, to_n };
    g.stop_condition.handle_kvt = touch_handle_kvt;
    g.stop_condition.eod = NULL;
    g.stop_condition.ctx = &ts;
    err_clear(&db->op_err);
    if (!dag_get_many(&db->dag, &g)) {
        if (db->op_err.code != ERR_OK) {
            *e = db->op_err;
            return e->code;
        }
        return nomem(e);
    }
    return ERR_OK;
}

/* putKvs: the pairs applied in the transaction's order, each an operation
 * with its marking, then endOfTrans. A safe point after each operation. */
static enum err_code put_kvs(struct db *db, struct err *e) {
    struct trans *t = db->trans;
    struct putdata *pd = &db->put_data;
    pd->tt = t->tt;
    pd->op.access_data = ACCESS_DATA_DEFAULT;
    db->n_op_marks = 0;
    db->op_changed = false;
    clear_replaced(db);
    db->touch_marks = 0;

    if (t->touch) {
        /* Before the puts, the touch makes dirty every index node of the
         * range, so that the value transformation of the row of a reclaim
         * step, wherever its key sorts, can store what the step made dirty
         * (Trans.dirtiedBytes). */
        enum err_code rc = touch_range(db, t->touch_from, t->touch_from_n, t->touch_to,
                t->touch_to_n, e);
        if (rc != ERR_OK) {
            return rc;
        }
        if (!end_of_op(db, true)) {
            return nomem(e);
        }
        db->touch_marks = db->trans_info == NULL ? 0 : db->trans_info->ndirty;
        pd_clear_fast(pd);
        obj_collect(&db->cx);       /* a safe point, as after a put */
    }

    for (int32_t i = 0; i < t->nkvs; i++) {
        struct tr_kv *kv = t->kvs[i];
        enum err_code rc;
        if (kv->has_tf && kv->tf.key != NULL) {
            /* kv.getKeyTransformation().transform(x.trans, i); its write hash the
             * new key's (bergdb.h). */
            const size_t bsize = (size_t) keys_byte_size(kv->key, kv->key_n) + 1;
            uint8_t *bkey = mem_alloc(db->mem, bsize, MEM_CALLER);
            if (bkey == NULL) {
                return nomem(e);
            }
            int32_t blen = keys_to_bytes(kv->key, kv->key_n, bkey);
            const uint8_t *k = bkey;
            size_t klen = (size_t) blen;
            kv->tf.key(kv->tf.ctx, t->tt, &k, &klen);
            rc = tr_kv_set_key(kv, t->mem, k, (int32_t) klen, e);
            mem_free(db->mem, bkey, bsize, MEM_CALLER);
            if (rc != ERR_OK) {
                return rc;
            }
            t->write_key_hashes[i] = keys_hash(kv->key, kv->key_n);
        }
        if (kv->has_tf && kv->tf.value != NULL) {
            struct vnode *prev = NULL;
            rc = db_check_active(db, "getOne", e);
            if (rc == ERR_OK) {
                rc = get_one_internal(db, t->tt, kv->key, kv->key_n, &db->get_data, &prev, e);
            }
            if (rc != ERR_OK) {
                return rc;
            }
            const uint8_t *v = kv->value;
            size_t vlen = kv->len < 0 ? 0 : (size_t) kv->len;
            const uint8_t *pv = prev == NULL || prev->len < 0 ? NULL : prev->value;
            kv->tf.value(kv->tf.ctx, t->tt, pv, pv == NULL ? 0 : (size_t) prev->len, &v, &vlen);
            if (v != kv->value || (int64_t) vlen != (kv->len < 0 ? 0 : kv->len)) {
                rc = tr_kv_set_value(kv, t->mem, v, (int32_t) vlen, e);
                if (rc != ERR_OK) {
                    return rc;
                }
            }
        }
        err_clear(&db->op_err);
        bool ok = dag_put_kv(&db->dag, kv->key, kv->key_n,
                kv->len < 0 ? NULL : (kv->value == NULL ? (const uint8_t *) "" : kv->value),
                kv->len < 0 ? 0 : kv->len, pd);
        if (!ok) {
            if (db->op_err.code != ERR_OK) {
                *e = db->op_err;
                return e->code;
            }
            return nomem(e);
        }
        if (!end_of_op(db, false)) {
            return nomem(e);
        }
        pd_clear_fast(pd);
        obj_collect(&db->cx);       /* a safe point between the puts (012-07, 6.4.4) */
    }
    end_of_trans(db);
    pd_clear(pd);
    return ERR_OK;
}

/* TransSeq.recordBytes: what a transaction's got-dirty nodes add to a record. */
static int64_t record_bytes(void *ctx, const struct ts_info *info) {
    (void) ctx;
    int64_t bytes = 0;
    for (int32_t i = 0; i < info->ndirty; i++) {
        const struct node *node = info->gotDirtyNodes[i].node;
        switch (info->gotDirtyNodes[i].type) {
        case NODE_TOP:
            bytes += nw_top_byte_size((const struct tnode *) node) + 16;
            break;
        case NODE_KEY:
            bytes += nw_key_byte_size((const struct knode *) node) + 16;
            break;
        default:
            break;
        }
    }
    return bytes;
}

/* hasDirtyChild */
static bool has_dirty_child(const struct node *node) {
    const int32_t count = node_size(node);
    for (int32_t i = 0; i < count; i++) {
        struct pointer p;
        node_get_pointer(node, i, &p);
        if (!ptr_is_null(&p)) {
            struct node *child = node_pointer_node(node, i);
            if (child != NULL && node_is_dirty(child)) {
                return true;
            }
        }
    }
    return false;
}

/* handleStillDirtyNodes (Rule A): pass after pass over the record's index
 * nodes until a pass finds none. */
static bool handle_still_dirty_nodes(struct db *db) {
    int32_t stillDirtyCount;
    do {
        stillDirtyCount = 0;
        const int32_t total = db->trans_nodes.top_count + db->trans_nodes.key_count;
        for (int32_t i = 0; i < total; i++) {
            struct node *node = tns_get(&db->trans_nodes, i);
            if (!node_is_dirty(node) && has_dirty_child(node)) {
                if (!add_got_dirty_node(db, db->trans_info, node)) {
                    return false;
                }
                node_set_dirty(node, true);
                stillDirtyCount++;
            }
        }
    } while (stillDirtyCount > 0);
    return true;
}

/* store(): the take, the references, the still-dirty nodes, the newest
 * written top node, the record; then the record's TransInfo into D. */
static enum err_code store(struct db *db, struct err *e) {
    const int64_t currentSp = ts_startup_pos_get(&db->startup_pos);
    struct transnodes *tn = &db->trans_nodes;
    struct ts_info *info = db->trans_info;

    const int64_t ownBytes = ts_own_bytes(tn->value_record_bytes);
    int64_t fixedBytes = ownBytes + 16 * (int64_t) info->ndirty;
    for (int32_t i = 0; i < tn->top_count; i++) {
        fixedBytes += nw_top_byte_size(tn->top_nodes[i]) + 16;
    }
    for (int32_t i = 0; i < tn->key_count; i++) {
        fixedBytes += nw_key_byte_size(tn->key_nodes[i]) + 16;
    }

    struct ts_info *taken = NULL;
    int32_t ntaken = 0;
    const int64_t newSp = ts_take(&db->trans_seq, currentSp, stream_length(&db->stream),
            db->startup_distance, ownBytes, db->record_limit - fixedBytes, record_bytes, NULL,
            &taken, &ntaken);
    /* The taken transactions' nodes into the record, top nodes to the top
     * array, key nodes to the key array (TransNodesForMe); D's holds go. */
    bool ok = true;
    for (struct ts_info *x = taken; x != NULL; x = x->next) {
        for (int32_t i = 0; i < x->ndirty; i++) {
            struct node *node = x->gotDirtyNodes[i].node;
            if (ok) {
                ok = x->gotDirtyNodes[i].type == NODE_TOP
                        ? tns_add_top_node(tn, (struct tnode *) node)
                        : tns_add_key_node(tn, (struct knode *) node);
            }
            obj_release(&db->cx, &node->o);
        }
        x->ndirty = 0;
    }
    ts_info_free_chain(taken, db->mem);
    if (!ok) {
        return nomem(e);
    }
    db->trans->startup_pos = newSp;

    /* resolvePointersOfTakenNodes, before the record's nodes are cleaned. */
    for (int32_t i = 0; i < tn->top_count + tn->key_count; i++) {
        enum err_code rc = nc_resolve_pointers(&db->node_coll, tns_get(tn, i), e);
        if (rc != ERR_OK) {
            return rc;
        }
    }
    tns_clean(tn);
    if (!handle_still_dirty_nodes(db)) {
        return nomem(e);
    }

    struct tnode *top = db->newest_written_top;
    for (int32_t i = 0; i < tn->top_count; i++) {
        struct tnode *t = tn->top_nodes[i];
        if (top == NULL || t->top_node_id > top->top_node_id) {
            top = t;
        }
    }

    struct ser_out out;
    enum err_code rc = ser_append_nodes(&db->serializer, &db->rs, tn, db->trans->tt, newSp,
            info, top, db->record_limit, &out, e);
    if (rc != ERR_OK) {
        return rc;
    }
    db->trans->tpos = out.tpos;
    db->trans->last_pos = out.last_pos;
    db->trans->next_pos = out.next_pos;
    obj_set(&db->cx, (struct obj **) &db->newest_written_top, &top->n.o);
    ev_record_written(&db->ev, tn);     /* admission (Eviction.recordWritten, 012-12) */

    db->trans->node_count = tns_size(tn);
    info->tpos = out.tpos;
    info->lastPos = out.last_pos;
    info->tt = db->trans->tt;
    info->startupPos = newSp;
    info->ownBytes = ownBytes;
    rc = ts_add(&db->trans_seq, info, e);      /* D owns it now */
    if (rc != ERR_OK) {
        return rc;
    }
    ts_startup_pos_set(&db->startup_pos, newSp);
    return ERR_OK;
}

/* stmRecordKeys */
static enum err_code stm_record_keys(struct db *db, const struct trans *t, struct err *e) {
    for (int32_t i = 0; i < t->nkvs; i++) {
        enum err_code rc = kms_add(&db->key_mod_set, t->tt, t->write_key_hashes[i], e);
        if (rc != ERR_OK) {
            return rc;
        }
    }
    return ERR_OK;
}

enum err_code db_execute(struct db *db, struct trans *t, struct err *e) {
    enum err_code rc = db_check_active(db, "execute", e);
    if (rc != ERR_OK) {
        return rc;
    }
    /* executeInner */
    rc = check_size(db, t, e);
    if (rc == ERR_OK) {
        rc = warmup(db, t, e);
    }
    if (rc == ERR_OK) {
        rc = db_check_active(db, "execute", e);
    }
    if (rc == ERR_OK && !t->is_internal
            && tds_get_super_root(&db->dag.top_ds)->top_node_id >= DB_LAST_TOP_ORDINAL) {
        rc = err_set(e, ERR_LIMIT, "DbException", "The database has used its top node "
                "ordinals (up to %lld); it takes no more transactions.",
                (long long) DB_LAST_TOP_ORDINAL);
    }
    if (rc == ERR_OK && !t->is_internal) {
        rc = check_dirty_nodes(db, t, e);
    }
    if (rc != ERR_OK) {
        obj_collect(&db->cx);
        return rc;
    }

    /* x.begin(t) */
    assert(tns_size(&db->trans_nodes) == 0 && "the nodes of another transaction");
    struct ts_info *info = ts_info_new(db->mem);
    if (info == NULL) {
        return nomem(e);
    }
    db->trans = t;
    db->trans_info = info;
    db->next_vpos = rs_next_spos(stream_length(&db->stream)) + 1;
    db->put_data.space_split_count = 0;

    rc = stm_check_conflicts(db, t, e);
    if (rc == ERR_OK) {
        /* transactionBegin() refuses a clock out of range (005-18). */
        rc = dbclock_transaction_begin(&db->clock, &t->tt, e);
    }
    if (rc != ERR_OK) {
        db->trans = NULL;
        db->trans_info = NULL;
        ts_info_free(info, db->mem);
        return rc;
    }

    /* The go point. From here nothing refuses the transaction and nothing is
     * undone: whatever fails, fails the database (005-01). */
    rc = put_kvs(db, e);
    if (rc == ERR_OK) {
        dbclock_transaction_end(&db->clock);
        rc = stm_record_keys(db, t, e);
    }
    if (rc == ERR_OK) {
        rc = store(db, e);
    }
    if (rc != ERR_OK) {
        /* What the transaction left (its TransInfo if not in D, the record's
         * nodes) is freed by the close (free_all). */
        if (db->trans_info != NULL && db->trans_seq.last == db->trans_info) {
            db->trans_info = NULL;
        }
        return fail(db, t, e);
    }
    /* aux.updateStats */
    db->kv_count += t->nkvs;
    db->transaction_count++;
    ts_startup_pos_release_for_evict(&db->startup_pos);
    /* x.end() */
    db->end_of_last_trans = t->last_pos + 1;
    db->trans = NULL;
    db->trans_info = NULL;      /* D's now */
    tns_clear(&db->trans_nodes);
    /* eviction (012-12), the audit */
    obj_collect(&db->cx);
    db_evict(db);       /* eviction.afterTransaction (012-12) */
    /* reclaim.transactionCompleted(t), within the go point: what fails there
     * fails the database (an internal transaction that failed has failed it
     * already, and its ERR_FAILED is returned as it is). */
    rc = rc_transaction_completed(db, t, e);
    if (rc != ERR_OK) {
        return fail(db, t, e);
    }
    return ERR_OK;
}

/* ======== Settings ======== */

enum err_code db_set_startup_distance(struct db *db, int32_t newDistance, struct err *e) {
    if (newDistance < 0) {
        return err_set(e, ERR_ARG, "IllegalArgumentException", "Bad newDistance: %d.",
                (int) newDistance);
    }
    const int32_t min = DB_MIN_STARTUP_DISTANCE;
    const int32_t max = DB_MAX_STARTUP_DISTANCE;
    newDistance = newDistance < min ? min : newDistance;
    newDistance = newDistance > max ? max : newDistance;

    /* The state first, so that a refused call changes nothing (005-53). */
    enum err_code rc = db_check_active(db, "setStartupDistance", e);
    if (rc != ERR_OK) {
        return rc;
    }
    const int32_t old = db->startup_distance;
    if (newDistance == old) {
        return ERR_OK;
    }

    /* trans().put(DbConstants.DUMMY_KEY, new byte[META_BLOCK_DISTANCE]) */
    struct tr_builder b;
    struct trans t;
    tr_builder_init(&b, db->mem);
    tr_init(&t, db->mem);
    uint8_t ikey[] = DUMMY_IKEY;
    const int32_t klen = (int32_t) strlen(DUMMY_IKEY);
    uint8_t bkey[sizeof DUMMY_IKEY];
    keys_ikey_to_bkey(ikey, klen, bkey);
    uint8_t *dummy = mem_zalloc(db->mem, DUMMY_VALUE_SIZE, MEM_CALLER);
    if (dummy == NULL) {
        return nomem(e);
    }
    rc = tr_put(&b, bkey, klen, dummy, DUMMY_VALUE_SIZE, NULL, e);
    mem_free(db->mem, dummy, DUMMY_VALUE_SIZE, MEM_CALLER);
    if (rc == ERR_OK) {
        rc = tr_build(&b, &t, e);
    }
    if (rc == ERR_OK) {
        db->startup_distance = newDistance;
        meta_set_startup_distance(&db->rs.meta, newDistance);
        rc = db_execute(db, &t, e);
        if (rc != ERR_OK) {
            /* Refused, or the database failed and must be restarted, which reads
             * the stream's setting. */
            db->startup_distance = old;
            meta_set_startup_distance(&db->rs.meta, old);
        }
    }
    tr_free(&t);
    tr_builder_free(&b);
    return rc;
}

enum err_code db_set_retain_duration(struct db *db, int64_t d, struct err *e) {
    return rc_set_retain_duration(&db->reclaim, d, e);
}

enum err_code db_set_reclaim_internal_fraction(struct db *db, double f, struct err *e) {
    return rc_set_internal_fraction(&db->reclaim, f, e);
}

enum err_code db_set_cache_size_indicator(struct db *db, int64_t size, struct err *e) {
    if (size < 1) {
        return err_set(e, ERR_ARG, "IllegalArgumentException", "Bad sizeIndicator: %lld.",
                (long long) size);
    }
    db->cache_size_indicator = size;
    ev_set_budget(&db->ev, size);
    /* After a decrease, eviction to the new budget now, where Java wakes its
     * eviction thread (005-52): an idle database gives the memory back too. */
    db_evict(db);
    return ERR_OK;
}

/* ======== Eviction (012-12) ======== */

/* The capacity controller at a safe point: at the end of a call, or inside
 * one (in_call). */
static void evict_at(struct db *db, bool in_call) {
    obj_collect(&db->cx);
    if (db->state != DB_ACTIVE) {
        return;
    }
    struct ev_env env = { &db->node_table, tds_get_super_root(&db->dag.top_ds),
            db->newest_written_top, &db->trans_seq };
    ev_run(&db->ev, &env, in_call);
}

void db_evict(struct db *db) {
    evict_at(db, false);
}

void db_safe_point(void *ctx) {
    evict_at(ctx, true);
}

int64_t db_resident_bytes(const struct db *db) {
    return ev_resident_bytes(db->mem, &db->node_table);
}

int64_t db_pinned_bytes(struct db *db) {
    if (!db->dag_made) {
        return nt_bytes(&db->node_table);
    }
    struct ev_env env = { &db->node_table, tds_get_super_root(&db->dag.top_ds),
            db->newest_written_top, &db->trans_seq };
    return ev_pinned_bytes(&env);
}

/* ======== Reads, the clock, status ======== */

int64_t db_current_time(struct db *db) {
    return dbclock_current_time(&db->clock);
}

int64_t db_lookup_time(const struct db *db, int64_t wanted) {
    return dbclock_lookup_time(&db->clock, wanted);
}

int64_t db_stream_length(const struct db *db) {
    return stream_length((struct stream *) &db->stream);
}

int64_t db_first_available_pos(const struct db *db) {
    return db->reclaim.firstAvailablePos;
}

int64_t db_first_available_time(const struct db *db) {
    return db->reclaim.firstAvailableLookupTime;
}

enum err_code db_get_one(struct db *db, int64_t lookup_time, const int64_t *key, int32_t n,
        struct getdata *gd, struct vnode **out, struct err *e) {
    enum err_code rc = db_check_active(db, "getOne", e);
    if (rc != ERR_OK) {
        return rc;
    }
    /* No safe point here: *out is borrowed until the caller's next call. */
    return get_one_internal(db, lookup_time, key, n, gd, out, e);
}

enum err_code db_get_many(struct db *db, struct getmany *g, struct err *e) {
    enum err_code rc = db_check_active(db, "getMany", e);
    if (rc != ERR_OK) {
        return rc;
    }
    const int64_t first = db_first_available_time(db);
    if (g->lookup_time < first) {
        return err_set(e, ERR_NOT_AVAILABLE, "LookupTimeNotAvailableException", "Cannot lookup "
                "at time %lld, the first time available for lookup is %lld.",
                (long long) g->lookup_time, (long long) first);
    }
    g->gd.op.access_data = ACCESS_DATA_DEFAULT;
    g->actual_lookup_time = dbclock_lookup_time(&db->clock, g->lookup_time);
    err_clear(&db->op_err);
    if (!dag_get_many(&db->dag, g)) {
        if (db->op_err.code != ERR_OK) {
            *e = db->op_err;
            return db_fail_on_storage(db, "A read", e);
        }
        return nomem(e);
    }
    db->get_op_count += g->get_op_count;
    obj_collect(&db->cx);       /* the end of the call: a safe point (012-07, 6.4.4) */
    return ERR_OK;
}

enum err_code db_sync(struct db *db, int64_t pos, struct err *e) {
    (void) pos;     /* one stream, synced whole: every byte up to its length */
    enum err_code rc = stream_sync(&db->stream, e);
    if (rc != ERR_OK) {
        return db_fail_on_storage(db, "A sync", e);
    }
    return ERR_OK;
}

/* ======== Close ======== */

/* The number of roots that roots_of lists, at most. */
static int64_t roots_count(const struct db *db) {
    int64_t count = 2 + db->trans_nodes.top_count + db->trans_nodes.key_count
            + db->trans_nodes.value_count + db->n_replaced + nt_size(&db->node_table);
    for (struct ts_info *x = db->trans_seq.first; x != NULL; x = x->next) {
        count += x->ndirty;
    }
    if (db->trans_info != NULL) {
        count += db->trans_info->ndirty;
    }
    return count;
}

/* The roots of the database's objects (012-07, 6.4): the node table's
 * handles, the super root, the newest written top node, D's got-dirty
 * nodes, the record's nodes, the replaced nodes, and a running
 * transaction's got-dirty nodes; each one counted holder. *n their number;
 * NULL on NOMEM (n then 0). The array has roots_count(db) entries. */
static struct obj **roots_of(struct db *db, int32_t *n) {
    int64_t count = roots_count(db);
    struct obj **roots = mem_alloc(db->mem, (size_t) count * sizeof *roots, MEM_STATE);
    *n = 0;
    if (roots == NULL) {
        return NULL;
    }
    int32_t k = 0;
    for (int64_t i = 0; i < nt_slots(&db->node_table); i++) {
        struct handle *h = nt_slot(&db->node_table, i);
        if (h != NULL) {
            roots[k++] = &h->o;
        }
    }
    if (db->dag_made && db->dag.top_ds.super_root != NULL) {
        roots[k++] = &db->dag.top_ds.super_root->n.o;
    }
    if (db->newest_written_top != NULL) {
        roots[k++] = &db->newest_written_top->n.o;
    }
    for (struct ts_info *x = db->trans_seq.first; x != NULL; x = x->next) {
        for (int32_t i = 0; i < x->ndirty; i++) {
            roots[k++] = &((struct node *) x->gotDirtyNodes[i].node)->o;
        }
    }
    if (db->trans_info != NULL) {
        for (int32_t i = 0; i < db->trans_info->ndirty; i++) {
            roots[k++] = &((struct node *) db->trans_info->gotDirtyNodes[i].node)->o;
        }
    }
    for (int32_t i = 0; i < tns_size(&db->trans_nodes); i++) {
        roots[k++] = &tns_get(&db->trans_nodes, i)->o;
    }
    for (int32_t i = 0; i < db->n_replaced; i++) {
        roots[k++] = &db->replaced[i]->o;
    }
    *n = k;
    return roots;
}

int64_t db_recount(struct db *db) {
    int32_t n;
    int64_t count = roots_count(db);
    struct obj **roots = roots_of(db, &n);
    int64_t bad = obj_recount(&db->cx, roots, n, NULL);
    mem_free(db->mem, roots, (size_t) count * sizeof *roots, MEM_STATE);
    return bad;
}

/* Frees every object, without trusting the counts (obj_free_all), and every
 * buffer and array. Works after a failure. Without room for the roots' list,
 * every holder lets go and a safe point frees what the counts let go (the
 * recount checks them in the tests). */
static void free_all(struct db *db) {
    ev_free(&db->ev);       /* the large values' holds, before the roots are taken */
    int32_t n = 0;
    int64_t count = roots_count(db);
    struct obj **roots = roots_of(db, &n);
    if (roots == NULL) {
        nt_free(&db->node_table, true);
        if (db->dag_made) {
            dag_free(&db->dag);
        }
        obj_release(&db->cx, db->newest_written_top == NULL ? NULL
                : &db->newest_written_top->n.o);
        for (struct ts_info *x = db->trans_seq.first; x != NULL; x = x->next) {
            for (int32_t i = 0; i < x->ndirty; i++) {
                obj_release(&db->cx, &((struct node *) x->gotDirtyNodes[i].node)->o);
            }
            x->ndirty = 0;
        }
        if (db->trans_info != NULL) {
            for (int32_t i = 0; i < db->trans_info->ndirty; i++) {
                obj_release(&db->cx, &((struct node *) db->trans_info->gotDirtyNodes[i].node)->o);
            }
            db->trans_info->ndirty = 0;
        }
        tns_clear(&db->trans_nodes);
        for (int32_t i = 0; i < db->n_replaced; i++) {
            obj_release(&db->cx, &db->replaced[i]->o);
        }
        db->n_replaced = 0;
        obj_collect(&db->cx);
    } else {
        obj_free_all(&db->cx, roots, n);
        mem_free(db->mem, roots, (size_t) count * sizeof *roots, MEM_STATE);
        nt_free(&db->node_table, false);
    }
    nc_free(&db->node_coll);
    if (db->dag_made) {
        db->dag.top_ds.super_root = NULL;
        pd_free(&db->put_data);
    }
    db->newest_written_top = NULL;
    /* The arrays, without releases: their objects are gone. */
    db->trans_nodes.top_count = db->trans_nodes.key_count = db->trans_nodes.value_count = 0;
    tns_free(&db->trans_nodes);
    for (struct ts_info *x = db->trans_seq.first; x != NULL; x = x->next) {
        x->ndirty = 0;
    }
    ts_free(&db->trans_seq);
    if (db->trans_info != NULL) {
        ts_info_free(db->trans_info, db->mem);
        db->trans_info = NULL;
    }
    mem_free(db->mem, db->op_marks, (size_t) db->cap_op_marks * sizeof *db->op_marks,
            MEM_STATE);
    mem_free(db->mem, db->replaced, (size_t) db->cap_replaced * sizeof *db->replaced,
            MEM_STATE);
    db->op_marks = NULL;
    db->replaced = NULL;
    db->n_op_marks = db->cap_op_marks = db->n_replaced = db->cap_replaced = 0;
    ser_free(&db->serializer);
    rc_free(&db->reclaim);
    if (db->kms_made) {
        kms_free(&db->key_mod_set);
        db->kms_made = false;
    }
    if (db->stream_open) {
        stream_close(&db->stream);
        db->stream_open = false;
    }
}

enum err_code db_close(struct db *db, struct err *e) {
    enum err_code rc = ERR_OK;
    db->state = DB_STOPPING;
    if (db->stream_open) {
        rc = stream_finish(&db->stream, e);
        db->stream_open = false;
    }
    free_all(db);
    return rc;
}
