/* starter: Db.startInner's start and DbStarter; see starter.h. Java's names
 * in the comments. */
#include "starter.h"
#include <assert.h>
#include <inttypes.h>
#include <string.h>
#include "handle.h"
#include "klong.h"
#include "knode.h"
#include "nstream.h"
#include "nwrite.h"
#include "recover.h"
#include "snode.h"
#include "spos.h"
#include "strans.h"
#include "vnode.h"

#define M META_BLOCK_SIZE

static enum err_code nomem(struct err *e, const char *what) {
    return err_set(e, ERR_NOMEM, "OutOfMemoryError", "%s", what);
}

/* ======== Db.startInner's checks and the recovery ======== */

enum err_code sr_check_and_recover(struct sr_env *env, struct rs_recovery *plan,
        struct err *e) {
    struct stream *s = env->rs->s;
    memset(plan, 0, sizeof *plan);
    plan->last_whole = SPOS_NULL;
    plan->torn = SPOS_NULL;

    /* refuseIncompleteCreation (005-33) */
    bool incomplete;
    enum err_code rc = rs_is_incomplete_creation(s, SR_CREATION_LENGTH, &incomplete, e);
    if (rc != ERR_OK) {
        return rc;
    }
    if (incomplete) {
        return err_set(e, ERR_NOT_CREATED, "DatabaseNotCreatedException", "The database was not "
                "completely created (a crash or a power loss while it was created?): its "
                "stream, of length %" PRId64 ", holds an incomplete creation, and no data. "
                "Remove its files and start it again; the start then creates it (bergdb "
                "005-33).", stream_length(s));
    }

    /* refuseOtherNodeSize (005-50), then nodeStream.recover() */
    rc = rs_check_node_size(s, env->max_node_size, e);
    if (rc == ERR_OK && stream_length(s) < M) {
        rc = err_set(e, ERR_FORMAT, "StreamFormatException", "Cannot recover stream without "
                "complete first meta block, length: %" PRId64, stream_length(s));
    }
    if (rc == ERR_OK) {
        rc = rcv_recover(env->rs, plan, e);
    }
    if (rc != ERR_OK && strcmp(e->java, "BadMagicBytes") == 0) {
        err_set(e, ERR_FORMAT, "BadCryptoKey", "Invalid magic bytes in stream, and no crypto "
                "key was used: likely, the database is encrypted and needs its key; else the "
                "stream is not a BergDB stream, or it is damaged.");
    }
    return rc;
}

/* ======== The start ======== */

/* A record of the startup section: its bytes, and the record parsed (a view
 * into them). */
struct srec {
    uint8_t *bytes;
    int32_t size;
    struct st_record st;
};

struct starter {
    struct sr_env *env;
    struct sr_result *out;
    struct srec *recs;              /* transactions */
    int32_t nrecs;
    int32_t caprecs;
    /* posMap: a position to the index of its node in nodes, which holds
     * (counts) each node while the starter runs. */
    struct lmap pos_map;
    struct node **nodes;
    int32_t nnodes;
    int32_t capnodes;
    struct lmap new_by_id;          /* moved into the node collection (registerSectionNodes) */
    struct lmap pos_to_id;
    struct tnode *super_root;
    int64_t startup_pos;            /* firstTrans.tpos */
    int64_t startup_time;           /* firstTrans.tt */
    /* The rerun of one transaction. */
    const struct st_record *rerun;
    int64_t vpos;
    struct err lerr;                /* a listener's failure */
};

static void free_recs(struct starter *st) {
    struct mem *m = st->env->mem;
    for (int32_t i = 0; i < st->nrecs; i++) {
        st_free(&st->recs[i].st, m);
        mem_free(m, st->recs[i].bytes, (size_t) st->recs[i].size, MEM_BUFFER);
    }
    mem_free(m, st->recs, (size_t) st->caprecs * sizeof *st->recs, MEM_STATE);
    st->recs = NULL;
    st->nrecs = 0;
    st->caprecs = 0;
}

static void free_starter(struct starter *st) {
    struct sr_env *env = st->env;
    free_recs(st);
    for (int32_t i = 0; i < st->nnodes; i++) {
        obj_release(env->cx, &st->nodes[i]->o);
    }
    mem_free(env->mem, st->nodes, (size_t) st->capnodes * sizeof *st->nodes, MEM_STATE);
    lmap_free(&st->pos_map);
    lmap_free(&st->new_by_id);
    lmap_free(&st->pos_to_id);
}

/* posMap.put: the starter holds the node. */
static bool pos_map_put(struct starter *st, int64_t pos, struct node *node) {
    struct mem *m = st->env->mem;
    if (st->nnodes == st->capnodes) {
        int32_t ncap = st->capnodes == 0 ? 64 : 2 * st->capnodes;
        struct node **n = mem_realloc(m, st->nodes, (size_t) st->capnodes * sizeof *n,
                (size_t) ncap * sizeof *n, MEM_STATE);
        if (n == NULL) {
            return false;
        }
        st->nodes = n;
        st->capnodes = ncap;
    }
    int64_t old;
    if (lmap_get(&st->pos_map, pos, &old)) {
        /* Two versions at one position cannot be: Java's map keeps the last. */
        obj_retain(&node->o);
        obj_release(st->env->cx, &st->nodes[old]->o);
        st->nodes[old] = node;
        return true;
    }
    if (!lmap_put(&st->pos_map, pos, st->nnodes)) {
        return false;
    }
    obj_retain(&node->o);
    st->nodes[st->nnodes++] = node;
    return true;
}

static struct node *pos_map_get(const struct starter *st, int64_t pos) {
    int64_t i;
    return lmap_get(&st->pos_map, pos, &i) ? st->nodes[i] : NULL;
}

/* Db.getStartupPosFromLastTransaction: the startupPos of the last committed
 * record, walking from transPos (the meta block's last transaction); the
 * in-memory block's lastTrans becomes that record. */
static enum err_code startup_pos_from_last_transaction(struct starter *st, int64_t transPos,
        int64_t *out, struct err *e) {
    struct sr_env *env = st->env;
    if (transPos == SPOS_NULL) {
        transPos = M;   /* The first transaction. */
    }
    assert(transPos >= 0 && "bad transPos");
    struct ns_iter iter;
    struct st_record rec;
    ns_iter_init(&iter, env->rs->s, env->mem, transPos, true);
    st_init(&rec);
    int64_t result = transPos;
    int64_t lastTpos = SPOS_NULL;
    enum err_code rc = ERR_OK;
    while (true) {
        bool has;
        rc = ns_iter_next(&iter, &has, e);
        if (rc != ERR_OK || !has) {
            break;
        }
        st->out->walk_records++;
        st->out->walk_bytes += iter.size;
        rc = st_parse(&rec, iter.tpos, iter.buf.p, iter.size, env->mem, e);
        if (rc != ERR_OK) {
            break;
        }
        result = rec.startup_pos;
        if (result < 0) {
            rc = err_set(e, ERR_FORMAT, "AssertionError", "Bad storedTrans.startupPos: %" PRId64,
                    result);
            break;
        }
        lastTpos = rec.tpos;
    }
    st_free(&rec, env->mem);
    ns_iter_free(&iter);
    if (rc != ERR_OK) {
        return rc;
    }
    /* So that the next meta block written is the one without a restart. */
    if (lastTpos != SPOS_NULL) {
        meta_set_last_trans(&env->rs->meta, lastTpos);
    }
    *out = result;
    return ERR_OK;
}

/* Db.readTransactions: the section's committed records from startupPos,
 * each kept with its bytes. */
static enum err_code read_transactions(struct starter *st, int64_t startupPos, struct err *e) {
    struct sr_env *env = st->env;
    if (startupPos == 0) {
        startupPos = M;
    }
    struct ns_iter ti;
    ns_iter_init(&ti, env->rs->s, env->mem, startupPos, true);
    enum err_code rc = ERR_OK;
    while (true) {
        bool has;
        rc = ns_iter_next(&ti, &has, e);
        if (rc != ERR_OK || !has) {
            break;
        }
        st->out->section_records++;
        st->out->section_bytes += ti.size;
        if (st->nrecs == st->caprecs) {
            int32_t ncap = st->caprecs == 0 ? 16 : 2 * st->caprecs;
            struct srec *n = mem_realloc(env->mem, st->recs, (size_t) st->caprecs * sizeof *n,
                    (size_t) ncap * sizeof *n, MEM_STATE);
            if (n == NULL) {
                rc = nomem(e, "the startup section");
                break;
            }
            st->recs = n;
            st->caprecs = ncap;
        }
        struct srec *r = &st->recs[st->nrecs];
        r->size = ti.size;
        r->bytes = mem_alloc(env->mem, (size_t) ti.size, MEM_BUFFER);
        if (r->bytes == NULL) {
            rc = nomem(e, "a record of the startup section");
            break;
        }
        memcpy(r->bytes, ti.buf.p, (size_t) ti.size);
        st_init(&r->st);
        st->nrecs++;
        rc = st_parse(&r->st, ti.tpos, r->bytes, r->size, env->mem, e);
        if (rc != ERR_OK) {
            break;
        }
    }
    ns_iter_free(&ti);
    return rc;
}

/* ======== DbStarter ======== */

/* validateNode */
static enum err_code validate_node(struct starter *st, const struct sn_node *sn,
        struct err *e) {
    if (!spos_is_valid(sn->spos)) {
        return err_set(e, ERR_FORMAT, "StreamFormatException", "Bad spos of node, spos=%"
                PRId64, sn->spos);
    }
    if (sn->type == NODE_KEY) {
        struct knode *k = (struct knode *) nc_node_from_sn(st->env->cx, sn);
        if (k == NULL) {
            return nomem(e, "a key node");
        }
        const char *msg = kn_validate_stream_node(k, st->startup_time);
        if (msg != NULL) {
            return err_set(e, ERR_FORMAT, "StreamFormatException", "%s", msg);
        }
    }
    return ERR_OK;
}

/* validateTransactions */
static enum err_code validate_transactions(struct starter *st, struct err *e) {
    if (st->nrecs == 0) {
        return err_set(e, ERR_FORMAT, "StreamFormatException",
                "No transactions for startup algorithm.");
    }
    const int64_t tpos = -1;
    const int64_t tt = -1;
    for (int32_t i = 0; i < st->nrecs; i++) {
        const struct st_record *t = &st->recs[i].st;
        if (t->tpos < M) {
            return err_set(e, ERR_FORMAT, "StreamFormatException", "Bad spos of transaction, "
                    "tpos=%" PRId64, t->tpos);
        }
        if (t->tpos <= tpos) {
            return err_set(e, ERR_FORMAT, "StreamFormatException", "non-increasing tpos, tpos=%"
                    PRId64, t->tpos);
        }
        if (t->tt <= tt) {
            return err_set(e, ERR_FORMAT, "StreamFormatException", "non-increasing tt, tpos=%"
                    PRId64 ", tt=%" PRId64, t->tpos, t->tt);
        }
        /* Java never updates tpos and tt here, so the two checks above compare
         * with -1 only (012-10, 6.4: a finding); C does as Java. */
        for (int32_t j = 0; j < t->nnodes; j++) {
            enum err_code rc = validate_node(st, &t->nodes[j], e);
            if (rc != ERR_OK) {
                return rc;
            }
        }
        obj_collect(st->env->cx);      /* the key nodes made only for the check */
    }
    return ERR_OK;
}

/* isPrimordialTransaction */
static bool is_primordial_transaction(const struct starter *st) {
    return st->nrecs == 1 && st->recs[0].st.tpos == M;
}

/* Db.Internal.setDag: the Dag made on the super root, and the second top
 * node's ordinal given to its TopDs (DbBuilder.secondTopOrdinal, 005-02). */
static enum err_code set_dag(struct starter *st, struct tnode *superRoot, struct err *e) {
    struct sr_env *env = st->env;
    dag_init(env->dag, env->cx, superRoot, env->max_node_size);
    st->out->dag_made = true;
    int64_t ordinal = env->second_top_ordinal == 0 ? 1 : env->second_top_ordinal;
    if (!tds_set_second_ordinal(&env->dag->top_ds, ordinal)) {
        return err_set(e, ERR_ARG, "IllegalArgumentException", "Bad ordinal, %" PRId64 ".",
                ordinal);
    }
    return ERR_OK;
}

/* doPrimordialStartup */
static enum err_code do_primordial_startup(struct starter *st, struct err *e) {
    struct sr_env *env = st->env;
    const struct st_record *t = &st->recs[0].st;
    /* checkPrimordialTransaction */
    if (t->nnodes != 2) {
        return err_set(e, ERR_FORMAT, "StreamFormatException", "expected 2, got %d nodes.",
                (int) t->nnodes);
    }
    if (t->nodes[0].type != NODE_TOP) {
        return err_set(e, ERR_FORMAT, "StreamFormatException", "Expected TopNode, got a node "
                "of type %d", (int) t->nodes[0].type);
    }
    if (t->nodes[1].type != NODE_KEY) {
        return err_set(e, ERR_FORMAT, "StreamFormatException", "Expected KeyNode, got a node "
                "of type %d", (int) t->nodes[1].type);
    }
    struct tnode *superRoot = (struct tnode *) nc_node_from_sn(env->cx, &t->nodes[0]);
    struct knode *keyNode = (struct knode *) nc_node_from_sn(env->cx, &t->nodes[1]);
    if (superRoot == NULL || keyNode == NULL) {
        return nomem(e, "the creation's nodes");
    }
    struct handle *h = hd_of(env->cx, &keyNode->n);
    if (h == NULL) {
        return nomem(e, "a handle");
    }
    tn_set_pointer(env->cx, superRoot, 0, &h->o, keyNode->n.spos);
    node_set_canonical(&superRoot->n, true);
    node_set_canonical(&keyNode->n, true);
    struct node *reg;
    if (!nt_register(env->nt, &superRoot->n, &reg) || !nt_register(env->nt, &keyNode->n, &reg)) {
        return nomem(e, "the node table");
    }
    enum err_code rc = set_dag(st, superRoot, e);
    if (rc != ERR_OK) {
        return rc;
    }
    obj_retain(&superRoot->n.o);
    st->out->newest_written_top = superRoot;
    assert(!node_is_dirty(&keyNode->n));
    assert(!node_is_dirty(&superRoot->n));
    return ERR_OK;
}

/* wasCreatedInRerunSection: made by a transaction of the section after its
 * first one. node: the object of the parsed node sn. */
static bool was_created_in_rerun_section(const struct starter *st, const struct sn_node *sn,
        const struct node *node) {
    switch (sn->type) {
    case NODE_TOP:
        return ((const struct tnode *) node)->root_time > st->startup_time;
    case NODE_KEY:
        return kn_get_first_time((const struct knode *) node) > st->startup_time;
    default:
        return sn->spos > st->recs[0].st.last_pos;
    }
}

static bool is_index(int32_t type) {
    return type == NODE_TOP || type == NODE_KEY;
}

/* The stored node's prevPos: a key node's, else Spos.NULL. */
static int64_t prev_pos_of(const struct sn_node *sn) {
    return sn->type == NODE_KEY ? sn->prev_pos : SPOS_NULL;
}

/* createMaps: newById (Rule R), posToId, posMap. */
static enum err_code create_maps(struct starter *st, struct err *e) {
    for (int32_t i = 0; i < st->nrecs; i++) {
        const struct st_record *t = &st->recs[i].st;
        for (int32_t j = 0; j < t->nnodes; j++) {
            const struct sn_node *sn = &t->nodes[j];
            if (!is_index(sn->type)) {
                continue;
            }
            /* in stream order, so the newest version wins */
            if (!lmap_put(&st->new_by_id, sn->id, sn->spos)
                    || !lmap_put(&st->pos_to_id, sn->spos, sn->id)) {
                return nomem(e, "the startup's maps");
            }
            int64_t prevPos = prev_pos_of(sn);
            if (spos_is_valid(prevPos) && !lmap_put(&st->pos_to_id, prevPos, sn->id)) {
                return nomem(e, "the startup's maps");
            }
        }
    }

    for (int32_t i = 0; i < st->nrecs; i++) {
        const struct st_record *t = &st->recs[i].st;
        for (int32_t j = 0; j < t->nnodes; j++) {
            const struct sn_node *sn = &t->nodes[j];
            int64_t newest = 0;
            bool isNewest = !is_index(sn->type)
                    || (lmap_get(&st->new_by_id, sn->id, &newest) && newest == sn->spos);
            if (!isNewest) {
                continue;
            }
            if (!is_index(sn->type) && sn->spos > st->recs[0].st.last_pos) {
                continue;       /* a value of the rerun section: no object needed */
            }
            struct node *node = nc_node_from_sn(st->env->cx, sn);
            if (node == NULL) {
                return nomem(e, "a node of the startup section");
            }
            if (!was_created_in_rerun_section(st, sn, node)) {
                if (!pos_map_put(st, sn->spos, node)) {
                    return nomem(e, "posMap");
                }
            }
        }
    }
    return ERR_OK;
}

/* updateStreamPointers: Rule R for the pointers whose node id is known
 * without reading the stream (a vpos, or a position in posToId). */
static void update_stream_pointers(struct starter *st) {
    for (int32_t k = 0; k < st->nnodes; k++) {
        struct node *node = st->nodes[k];
        int32_t pointerCount = node_size(node);
        for (int32_t i = 0; i < pointerCount; i++) {
            struct pointer p;
            node_get_pointer(node, i, &p);
            if (ptr_is_null(&p)) {
                continue;
            }
            int64_t pos = p.pos;
            int64_t id = pos;
            bool haveId = spos_is_vpos(pos) || lmap_get(&st->pos_to_id, pos, &id);
            int64_t newPos;
            if (haveId && lmap_get(&st->new_by_id, id, &newPos) && spos_newer(newPos, pos)) {
                node_set_pointer(st->env->cx, node, i, NULL, newPos);
            }
        }
    }
}

/* changeKeyNodesToStateAtStartupTime: the section's key node versions (those
 * the start keeps, posMap's; the others are not used) cut back to the
 * startup time. */
static void change_key_nodes_to_state_at_startup_time(struct starter *st) {
    for (int32_t k = 0; k < st->nnodes; k++) {
        struct node *node = st->nodes[k];
        if (node_type(node) == NODE_TYPE_KEY_NODE) {
            kn_to_previous_state(st->env->cx, (struct knode *) node, st->startup_time);
        }
    }
}

/* checkStreamPointers(node): each stream pointer names a version in the
 * stream, not NULL or a vpos. */
static enum err_code check_stream_pointers_of(const struct node *node, struct err *e) {
    if (node_is_key_node(node)) {
        const struct knode *k = (const struct knode *) node;
        for (int32_t i = 0; i < k->size; i++) {
            int64_t klong = k->klongs[i];
            if (kl_is_key(klong) && kn_get_pointer_node(k, i) == NULL) {
                int64_t pos = kn_get_pointer_pos(k, i);
                if (spos_is_null(pos) || spos_is_vpos(pos)) {
                    return err_set(e, ERR_FORMAT, "StreamFormatException", "Unexpected stream "
                            "pointer from KeyNode, was %" PRId64 ", index %d, node: %" PRId64,
                            pos, (int) i, node->id);
                }
            }
        }
    } else {
        int32_t count = node_size(node);
        for (int32_t i = 0; i < count; i++) {
            struct pointer p;
            node_get_pointer(node, i, &p);
            if (!ptr_is_null(&p)) {
                if (spos_is_null(p.pos) || spos_is_vpos(p.pos)) {
                    return err_set(e, ERR_FORMAT, "StreamFormatException", "Unexpected stream "
                            "pointer, was %" PRId64 ", index %d, node: %" PRId64, p.pos, (int) i,
                            node->id);
                }
            }
        }
    }
    return ERR_OK;
}

static enum err_code check_stream_pointers(struct starter *st, struct err *e) {
    for (int32_t k = 0; k < st->nnodes; k++) {
        enum err_code rc = check_stream_pointers_of(st->nodes[k], e);
        if (rc != ERR_OK) {
            return rc;
        }
    }
    return ERR_OK;
}

/* createMemoryPointers: memory pointers from stream pointers to posMap's
 * nodes. */
static enum err_code create_memory_pointers(struct starter *st, struct err *e) {
    for (int32_t k = 0; k < st->nnodes; k++) {
        struct node *node = st->nodes[k];
        int32_t pointerCount = node_size(node);
        for (int32_t i = 0; i < pointerCount; i++) {
            struct pointer p;
            node_get_pointer(node, i, &p);
            if (ptr_is_null(&p)) {
                continue;
            }
            struct node *pointee = pos_map_get(st, p.pos);
            if (pointee != NULL) {
                struct obj *po;
                if (!hd_pointee_of(st->env->cx, pointee, &po)) {
                    return nomem(e, "a handle");
                }
                node_set_pointer(st->env->cx, node, i, po, p.pos);
            }
        }
    }
    return ERR_OK;
}

/* registerSectionNodes: posMap's nodes canonical, in the node table; Rule R
 * for the rest of the process. */
static enum err_code register_section_nodes(struct starter *st, struct err *e) {
    struct sr_env *env = st->env;
    for (int32_t k = 0; k < st->nnodes; k++) {
        struct node *node = st->nodes[k];
        node_set_canonical(node, true);
        struct node *reg;
        if (!nt_register(env->nt, node, &reg)) {
            return nomem(e, "the node table");
        }
    }
    nc_set_startup_section(env->nc, &st->new_by_id, st->startup_pos, st->startup_time);
    return ERR_OK;
}

/* topNodeOfLastTransaction: the canonical object of the top node whose
 * latest version the last record names (topPos), the newest written top
 * node (011-11, M18). */
static enum err_code top_node_of_last_transaction(struct starter *st, struct tnode **out,
        struct err *e) {
    struct sr_env *env = st->env;
    const struct st_record *last = &st->recs[st->nrecs - 1].st;
    int64_t pos = last->top_pos;
    if (!spos_is_valid(pos) || spos_is_vpos(pos)) {
        return err_set(e, ERR_FORMAT, "StreamFormatException", "The last transaction, at %"
                PRId64 ", names no top node (topPos %" PRId64 ").", last->tpos, pos);
    }
    int64_t id;
    if (!lmap_get(&st->pos_to_id, pos, &id)) {
        int32_t type;
        enum err_code rc = nc_read_node_header(env->nc, pos, &type, &id, e);
        if (rc != ERR_OK) {
            return rc;
        }
    }
    int64_t newPos;
    bool haveNew = nc_newest_in_section(env->nc, id, &newPos);
    /* Java's assert: topPos names the latest version anyway */
    if (haveNew && newPos != pos) {
        return err_set(e, ERR_FORMAT, "AssertionError", "topPos %" PRId64 " is not the newest "
                "version %" PRId64 " of top node %" PRId64, pos, newPos, id);
    }
    int64_t ref = haveNew && spos_newer(newPos, pos) ? newPos : pos;

    struct node *node = pos_map_get(st, ref);
    if (node == NULL) {
        struct node *inTable = nt_get_node(env->nt, id);
        if (inTable != NULL && node_is_canonical(inTable)) {
            node = inTable;
        } else {
            enum err_code rc = nc_read_node(env->nc, ref, &node, e);
            if (rc != ERR_OK) {
                return rc;
            }
            node_set_canonical(node, true);
            if (!nt_register(env->nt, node, &node)) {
                return nomem(e, "the node table");
            }
        }
    }
    if (node_type(node) != NODE_TYPE_TOP_NODE) {
        return err_set(e, ERR_FORMAT, "StreamFormatException", "topPos %" PRId64 " of the last "
                "transaction names a %s, not a top node.", pos,
                node_type(node) == NODE_TYPE_KEY_NODE ? "KeyNode" : "ValueNode");
    }
    *out = (struct tnode *) node;
    return ERR_OK;
}

/* findSuperNodeAtStartupTime */
static enum err_code find_super_node_at_startup_time(struct starter *st, struct err *e) {
    struct sr_env *env = st->env;
    struct tnode *lastSuperNode;
    enum err_code rc = top_node_of_last_transaction(st, &lastSuperNode, e);
    if (rc != ERR_OK) {
        return rc;
    }
    /* It is the super root at the startup time (011-11, 8.3). */
    struct dag tempDag;
    dag_init(&tempDag, env->cx, lastSuperNode, env->max_node_size);
    struct getdata gd;
    dag_new_get_data(&tempDag, &gd);
    gd.op.pointer_follower.follow = nc_follow_reader;
    gd.op.pointer_follower.ctx = env->nc;
    struct tnode *superRoot = NULL;
    bool ok = tds_find_super_root_at_time(&tempDag.top_ds, st->startup_time, &gd.op, &superRoot);
    dag_free(&tempDag);
    if (!ok) {
        *e = env->nc->err;
        return e->code;
    }
    if (superRoot == NULL) {
        return err_set(e, ERR_FORMAT, "StreamFormatException", "No super root at time %" PRId64
                " was found.", st->startup_time);
    }
    if (superRoot != lastSuperNode) {
        return err_set(e, ERR_FORMAT, "StreamFormatException", "The newest written top node %"
                PRId64 " is not the super root at the startup time, %" PRId64 ".",
                lastSuperNode->n.id, superRoot->n.id);
    }
    st->super_root = superRoot;
    obj_retain(&lastSuperNode->n.o);
    st->out->newest_written_top = lastSuperNode;     /* setNewestWrittenTop */
    return ERR_OK;
}

/* prepareDb: the Dag on the super root (setDag). */
static enum err_code prepare_db(struct starter *st, struct err *e) {
    return set_dag(st, st->super_root, e);
}

/* canonicalNode: the canonical object of a node of D: the node table's; or
 * its newest version in the section, cut back to the startup time; or the
 * version at spos. NULL in *out if none of these. */
static enum err_code canonical_node(struct starter *st, int64_t id, int64_t spos,
        struct node **out, struct err *e) {
    struct sr_env *env = st->env;
    struct node *node = nt_get_node(env->nt, id);
    if (node != NULL && node_is_canonical(node)) {
        *out = node;
        return ERR_OK;
    }
    int64_t newPos;
    bool haveNew = nc_newest_in_section(env->nc, id, &newPos);
    if (!haveNew && (!spos_is_valid(spos) || spos_is_vpos(spos))) {
        *out = NULL;
        return ERR_OK;
    }
    enum err_code rc = nc_read_node(env->nc, haveNew ? newPos : spos, &node, e);
    if (rc != ERR_OK) {
        return rc;
    }
    if (node->id != id) {
        return err_set(e, ERR_FORMAT, "AssertionError", "ids differ, %" PRId64 " != %" PRId64,
                node->id, id);
    }
    if (node_type(node) == NODE_TYPE_KEY_NODE) {
        kn_to_previous_state(env->cx, (struct knode *) node, st->startup_time);
    }
    node_set_canonical(node, true);
    if (!nt_register(env->nt, node, out)) {
        return nomem(e, "the node table");
    }
    return ERR_OK;
}

/* The rerun's NodeChangeListener: nodeCreated. */
static bool node_created(struct starter *st, struct node *node) {
    struct sr_env *env = st->env;
    int64_t id = st->vpos;
    st->vpos = spos_next_vpos(st->vpos);
    node->id = id;
    node->spos = id;           /* initially, we use vpos as spos */

    /* storedTrans.findNode(id) */
    const struct sn_node *n = NULL;
    for (int32_t i = 0; i < st->rerun->nnodes; i++) {
        if (st->rerun->nodes[i].id == id) {
            n = &st->rerun->nodes[i];
            break;
        }
    }
    if (n != NULL) {
        if (node_type(node) == NODE_TYPE_VALUE || node_type(node) == NODE_TYPE_DELETE) {
            if (n->type == NODE_VALUE || n->type == NODE_DELETE) {
                /* Its transaction's position, for a get (005-34). */
                ((struct vnode *) node)->offset_from_trans = (uint32_t) n->offset_from_trans;
            }
        }
        node->spos = n->spos;
    }

    if (node_is_index_node(node)) {
        /* A node created and written in the section: its spos is the
         * position of its newest version, as in the run without restarts. */
        int64_t newPos;
        if (nc_newest_in_section(env->nc, id, &newPos)) {
            node->spos = newPos;
        }
        node_set_canonical(node, true);
        struct node *reg;
        if (!nt_register(env->nt, node, &reg)) {
            err_set(&st->lerr, ERR_NOMEM, "OutOfMemoryError", "the node table");
            return false;
        }
    }
    return true;
}

static bool l_top_node_created(void *ctx, struct tnode *node) {
    return node_created(ctx, &node->n);
}

static bool l_key_node_created(void *ctx, struct knode *node) {
    return node_created(ctx, &node->n);
}

static bool l_value_node_created(void *ctx, struct vnode *node, const int64_t *key,
        int32_t key_n) {
    (void) key;
    (void) key_n;
    return node_created(ctx, &node->n);
}

static bool l_key_node_changed(void *ctx, struct knode *node) {
    (void) ctx;
    (void) node;
    return true;
}

/* rerunTransaction: the record's value and delete nodes put again at its
 * time, then D's TransInfo of it from its stored got-dirty ids. */
static enum err_code rerun_transaction(struct starter *st, const struct st_record *t,
        struct ts_info *tinfo, struct err *e) {
    struct sr_env *env = st->env;
    st->rerun = t;
    st->vpos = spos_next_vpos(t->tpos);
    int64_t valueBytes = 0;
    int64_t *key = NULL;
    int32_t keyCap = 0;
    enum err_code rc = ERR_OK;

    struct putdata pd;         /* createPutData() */
    dag_new_put_data(env->dag, &pd, env->mem);
    pd.op.pointer_follower.follow = nc_follow_writer;
    pd.op.pointer_follower.ctx = env->nc;
    pd.node_change_listener.top_node_created = l_top_node_created;
    pd.node_change_listener.key_node_created = l_key_node_created;
    pd.node_change_listener.value_node_created = l_value_node_created;
    pd.node_change_listener.key_node_changed = l_key_node_changed;
    pd.node_change_listener.key_node_replaced = NULL;
    pd.node_change_listener.top_node_replaced = NULL;
    pd.node_change_listener.ctx = st;

    for (int32_t i = 0; i < t->nnodes && rc == ERR_OK; i++) {
        const struct sn_node *n = &t->nodes[i];
        if (n->type != NODE_VALUE && n->type != NODE_DELETE) {
            continue;
        }
        if (n->key_n > keyCap) {
            int32_t ncap = n->key_n < 16 ? 16 : n->key_n;
            int64_t *k2 = mem_realloc(env->mem, key, (size_t) keyCap * sizeof *key,
                    (size_t) ncap * sizeof *key, MEM_BUFFER);
            if (k2 == NULL) {
                rc = nomem(e, "a key");
                break;
            }
            key = k2;
            keyCap = ncap;
        }
        for (int32_t j = 0; j < n->key_n; j++) {
            key[j] = sn_seg(n, j);
        }
        valueBytes += nw_value_byte_size_long(n->type == NODE_DELETE ? -1 : n->value_len,
                n->key_n);
        pd.tt = t->tt;
        err_clear(&st->lerr);
        err_clear(&env->nc->err);
        if (!dag_put_kv(env->dag, key, n->key_n, n->type == NODE_DELETE ? NULL : n->value,
                n->type == NODE_DELETE ? 0 : n->value_len, &pd)) {
            if (st->lerr.code != ERR_OK) {
                *e = st->lerr;
            } else if (env->nc->err.code != ERR_OK) {
                *e = env->nc->err;
            } else {
                nomem(e, "a put of the rerun");
            }
            rc = e->code;
            break;
        }
        pd_clear_fast(&pd);
        st->out->rerun_pairs++;
        obj_collect(env->cx);       /* a safe point between the puts */
    }
    pd_free(&pd);
    mem_free(env->mem, key, (size_t) keyCap * sizeof *key, MEM_BUFFER);
    if (rc != ERR_OK) {
        return rc;
    }

    for (int32_t i = 0; i < t->got_dirty_count; i++) {
        int64_t id = st_got_dirty_id(t, i);
        int64_t spos = st_got_dirty_pos(t, i);
        struct node *gotDirtyNode;
        rc = canonical_node(st, id, spos, &gotDirtyNode, e);
        if (rc != ERR_OK) {
            return rc;
        }
        if (gotDirtyNode == NULL) {
            struct node *inTable = nt_get_node(env->nt, id);
            return err_set(e, ERR_FORMAT, "StreamFormatException", "startup error, node %"
                    PRId64 ":%" PRId64 " not found, got dirty in trans tt=%" PRId64 ", tpos=%"
                    PRId64 "; startup pos %" PRId64 ", time %" PRId64 "; in node table: %s",
                    id, spos, t->tt, t->tpos, st->startup_pos, st->startup_time,
                    inTable == NULL ? "no" : "a snapshot");
        }
        node_set_dirty(gotDirtyNode, true);
        /* tinfo.addGotDirtyNode: the list holds the node (012-09's rule) */
        rc = ts_info_add_node(tinfo, env->mem, gotDirtyNode, gotDirtyNode->id,
                node_is_top_node(gotDirtyNode) ? NODE_TOP : NODE_KEY, e);
        if (rc != ERR_OK) {
            return rc;
        }
        obj_retain(&gotDirtyNode->o);
    }

    tinfo->tt = t->tt;
    tinfo->tpos = t->tpos;
    tinfo->startupPos = t->startup_pos;
    tinfo->lastPos = t->last_pos;
    tinfo->ownBytes = ts_own_bytes(valueBytes);     /* the take's pace (005-49) */
    return ERR_OK;
}

/* rerunTransactions: every transaction but the first. */
static enum err_code rerun_transactions(struct starter *st, struct err *e) {
    struct sr_env *env = st->env;
    for (int32_t i = 1; i < st->nrecs; i++) {
        struct ts_info *tinfo = ts_info_new(env->mem);
        if (tinfo == NULL) {
            return nomem(e, "a TransInfo");
        }
        enum err_code rc = rerun_transaction(st, &st->recs[i].st, tinfo, e);
        if (rc == ERR_OK) {
            rc = ts_add(env->ts, tinfo, e);
        }
        if (rc != ERR_OK) {
            /* tinfo's nodes are held: release them with it */
            for (int32_t j = 0; j < tinfo->ndirty; j++) {
                obj_release(env->cx, &((struct node *) tinfo->gotDirtyNodes[j].node)->o);
            }
            ts_info_free(tinfo, env->mem);
            return rc;
        }
        obj_collect(env->cx);
    }
    return ERR_OK;
}

/* linkD: rule 4 by position (005-57), on the canonical object of each node
 * of D. */
static enum err_code link_d(struct starter *st, struct err *e) {
    struct sr_env *env = st->env;
    struct lmap byPos;
    lmap_init(&byPos, env->mem);
    enum err_code rc = ERR_OK;
    for (int64_t i = 0; i < nt_slots(env->nt) && rc == ERR_OK; i++) {
        struct handle *h = nt_slot(env->nt, i);
        if (h == NULL) {
            continue;
        }
        struct node *o = h->obj;
        if (o != NULL && node_is_canonical(o)) {
            if (!lmap_put(&byPos, o->spos, (int64_t) (intptr_t) h)) {
                rc = nomem(e, "linkD's byPos");
            }
        }
    }
    for (struct ts_info *t = env->ts->first; t != NULL && rc == ERR_OK; t = t->next) {
        for (int32_t i = 0; i < t->ndirty && rc == ERR_OK; i++) {
            rc = nc_link_to_canonical(env->nc, t->gotDirtyNodes[i].node, &st->pos_to_id, &byPos,
                    e);
        }
    }
    lmap_free(&byPos);
    return rc;
}

/* postStartupCheck: checkThatValueNodesHaveSpos, and Db.checkNodes (each key
 * node in memory checked); over the node table's objects. */
static enum err_code post_startup_check(struct starter *st, struct err *e) {
    struct sr_env *env = st->env;
    for (int64_t i = 0; i < nt_slots(env->nt); i++) {
        struct handle *h = nt_slot(env->nt, i);
        if (h == NULL || h->obj == NULL || node_type(h->obj) != NODE_TYPE_KEY_NODE) {
            continue;
        }
        const struct knode *k = (const struct knode *) h->obj;
        const char *msg = kn_check(k);
        if (msg != NULL) {
            return err_set(e, ERR_FORMAT, "AssertionError", "%s", msg);
        }
        for (int32_t j = 0; j < k->size; j++) {
            struct obj *p = k->pointers[j];
            if (p != NULL && p->kind == OBJ_VALUE && !(((struct node *) p)->spos >= 0)) {
                return err_set(e, ERR_FORMAT, "AssertionError", "value node got no spos "
                        "during startup");
            }
        }
    }
    return ERR_OK;
}

/* doOrdinaryStartup */
static enum err_code do_ordinary_startup(struct starter *st, struct err *e) {
    enum err_code rc = create_maps(st, e);
    if (rc != ERR_OK) {
        return rc;
    }
    update_stream_pointers(st);
    change_key_nodes_to_state_at_startup_time(st);
    rc = check_stream_pointers(st, e);
    if (rc == ERR_OK) {
        rc = create_memory_pointers(st, e);
    }
    if (rc == ERR_OK) {
        rc = register_section_nodes(st, e);
    }
    if (rc == ERR_OK) {
        rc = find_super_node_at_startup_time(st, e);
    }
    if (rc != ERR_OK) {
        return rc;
    }
    rc = prepare_db(st, e);
    if (rc == ERR_OK) {
        rc = rerun_transactions(st, e);
    }
    if (rc == ERR_OK) {
        rc = link_d(st, e);
    }
    if (rc == ERR_OK) {
        rc = post_startup_check(st, e);
    }
    nc_end_reconstruction(st->env->nc);
    return rc;
}

enum err_code sr_start(struct sr_env *env, struct sr_result *out, struct err *e) {
    struct starter st;
    memset(&st, 0, sizeof st);
    memset(out, 0, sizeof *out);
    st.env = env;
    st.out = out;
    lmap_init(&st.pos_map, env->mem);
    lmap_init(&st.new_by_id, env->mem);
    lmap_init(&st.pos_to_id, env->mem);
    err_clear(&st.lerr);

    /* handleStartParams */
    struct meta *meta = &env->rs->meta;
    enum err_code rc = meta_check_format(meta, e);
    int64_t startupPos = 0;
    if (rc == ERR_OK) {
        rc = startup_pos_from_last_transaction(&st, meta_last_trans(meta), &startupPos, e);
    }
    if (rc == ERR_OK) {
        out->startup_distance = meta_startup_distance(meta);
        out->startup_pos = startupPos;
        /* readTransactions */
        rc = read_transactions(&st, startupPos, e);
    }
    if (rc == ERR_OK && st.nrecs == 0) {
        /* setLastTransTimeOfDbClock */
        rc = err_set(e, ERR_FORMAT, "StreamFormatException",
                "No transactions in startup transaction set.");
    }
    if (rc == ERR_OK) {
        out->last_trans_time = st.recs[st.nrecs - 1].st.tt;
        out->start_pos = startupPos;
        out->start_time = st.recs[0].st.tt;
        out->trans_count = st.nrecs;
        out->last_pos = st.recs[st.nrecs - 1].st.last_pos;

        /* DbStarter.start */
        st.startup_pos = st.recs[0].st.tpos;
        st.startup_time = st.recs[0].st.tt;
        rc = validate_transactions(&st, e);
    }
    if (rc == ERR_OK) {
        rc = is_primordial_transaction(&st) ? do_primordial_startup(&st, e)
                : do_ordinary_startup(&st, e);
    }
    free_starter(&st);
    obj_collect(env->cx);
    return rc;
}
