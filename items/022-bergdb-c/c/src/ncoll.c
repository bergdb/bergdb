/* ncoll: Java's NodeCollection; see ncoll.h. Java's names in the comments. */
#include "ncoll.h"
#include <assert.h>
#include <inttypes.h>
#include <string.h>
#include "handle.h"
#include "klong.h"
#include "knode.h"
#include "spos.h"
#include "tnode.h"
#include "vnode.h"

/* The size of idOf's cache (Java's removeEldestEntry: size() > 100 * 1000). */
#define ID_BY_POS_MAX 100000

static struct handle *to_handle(int64_t v) {
    return (struct handle *) (intptr_t) v;
}

void nc_init(struct ncoll *nc, struct obj_ctx *cx, struct mem *m, struct stream *s,
        struct ntable *nt) {
    memset(nc, 0, sizeof *nc);
    nc->cx = cx;
    nc->mem = m;
    nc->s = s;
    nc->nt = nt;
    lmap_init(&nc->new_by_id, m);
    lmap_init(&nc->id_by_pos, m);
    err_clear(&nc->err);
}

void nc_free(struct ncoll *nc) {
    lmap_free(&nc->new_by_id);
    lmap_free(&nc->id_by_pos);
    ns_buf_free(&nc->buf, nc->mem);
}

struct node *nc_node_from_sn(struct obj_ctx *cx, const struct sn_node *sn) {
    switch (sn->type) {
    case NODE_TOP: {
        struct tnode *t = tn_new_stored(cx, sn->ordinal, sn->root, sn->root_time, sn->spos,
                sn->id, sn->h, sn->bytes + 40);
        return t == NULL ? NULL : &t->n;
    }
    case NODE_KEY: {
        struct knode *k = kn_new_stored(cx, sn->leaf, sn->spos, sn->id, sn->n, sn->bytes + 32,
                sn->bytes + 32 + 8 * (size_t) sn->n);
        return k == NULL ? NULL : &k->n;
    }
    default: {
        assert(sn->type == NODE_VALUE || sn->type == NODE_DELETE);
        struct vnode *v = vn_new_stored(cx, sn->value, sn->value_len, sn->spos, sn->id,
                sn->tpos);
        return v == NULL ? NULL : &v->n;
    }
    }
}

/* NodeStream.readNode, the object made. */
static enum err_code read_node(struct ncoll *nc, int64_t pos, struct node **out,
        struct err *e) {
    if (nc->source.read_node != NULL) {
        return nc->source.read_node(nc->source.ctx, pos, out, e);
    }
    struct sn_node sn;
    enum err_code rc = ns_read_node(nc->s, nc->mem, pos, &nc->buf, &sn, e);
    if (rc != ERR_OK) {
        return rc;
    }
    struct node *n = nc_node_from_sn(nc->cx, &sn);
    if (n == NULL) {
        return err_set(e, ERR_NOMEM, "OutOfMemoryError", "a node read at %" PRId64, pos);
    }
    *out = n;
    return ERR_OK;
}

enum err_code nc_read_node(struct ncoll *nc, int64_t pos, struct node **out, struct err *e) {
    enum err_code rc = read_node(nc, pos, out, e);
    if (rc == ERR_OK) {
        nc->reads++;
    }
    return rc;
}

enum err_code nc_read_node_header(struct ncoll *nc, int64_t pos, int32_t *type, int64_t *id,
        struct err *e) {
    nc->header_reads++;
    if (nc->source.read_header != NULL) {
        return nc->source.read_header(nc->source.ctx, pos, type, id, e);
    }
    return ns_read_node_header(nc->s, pos, type, id, e);
}

/* idOf: the id of the node version at pos, or the vpos itself. */
static enum err_code id_of(struct ncoll *nc, int64_t pos, int64_t *id, struct err *e) {
    if (spos_is_vpos(pos)) {
        *id = pos;
        return ERR_OK;
    }
    if (lmap_get(&nc->id_by_pos, pos, id)) {
        return ERR_OK;
    }
    int32_t type;
    enum err_code rc = nc_read_node_header(nc, pos, &type, id, e);
    if (rc != ERR_OK) {
        return rc;
    }
    if (nc->id_by_pos.size >= ID_BY_POS_MAX) {
        lmap_clear(&nc->id_by_pos);
    }
    if (!lmap_put(&nc->id_by_pos, pos, *id)) {
        return err_set(e, ERR_NOMEM, "OutOfMemoryError", "idOf's cache");
    }
    return ERR_OK;
}

bool nc_points_to_index_node(const struct node *node, int32_t i) {
    switch (node_type(node)) {
    case NODE_TYPE_TOP_NODE:
        return true;
    case NODE_TYPE_KEY_NODE: {
        /* In a segment leaf, a key klong of length 7 points to the root of the
         * next key segment, and shorter ones point to value nodes. */
        const struct knode *k = (const struct knode *) node;
        int64_t klong = k->klongs[i];
        return kl_is_key(klong) && (!kn_is_segment_leaf(k) || kl_get_length(klong) == KL_MAX_SIZE);
    }
    default:
        return false;
    }
}

enum err_code nc_check_pointee_type(const struct node *node, int32_t i,
        const struct node *pointee, int64_t pos, struct err *e) {
    int32_t type = node_type(node) == NODE_TYPE_TOP_NODE
            ? (i == 0 ? NODE_TYPE_KEY_NODE : NODE_TYPE_TOP_NODE)
            : nc_points_to_index_node(node, i) ? NODE_TYPE_KEY_NODE : NODE_TYPE_VALUE;
    if (node_type(pointee) != type) {
        return err_set(e, ERR_FORMAT, "StreamFormatException", "Pointer %d of node %" PRId64
                " names a node of type %d at %" PRId64 ", not %d.", (int) i, node->id,
                (int) node_type(pointee), pos, (int) type);
    }
    return ERR_OK;
}

int64_t nc_newer_pos(int64_t ref, int64_t w) {
    if (!spos_is_valid(w) || spos_is_vpos(w)) {
        return ref;
    }
    return spos_is_vpos(ref) || spos_is_null(ref) || w > ref ? w : ref;
}

void nc_set_startup_section(struct ncoll *nc, struct lmap *newById, int64_t sectionStartPos,
        int64_t startupTime) {
    lmap_free(&nc->new_by_id);
    nc->new_by_id = *newById;
    lmap_init(newById, nc->mem);
    nc->have_section = true;
    nc->section_start_pos = sectionStartPos;
    nc->section_startup_time = startupTime;
    nc->reconstructing = true;
}

void nc_end_reconstruction(struct ncoll *nc) {
    nc->reconstructing = false;
}

bool nc_newest_in_section(const struct ncoll *nc, int64_t id, int64_t *pos) {
    return nc->have_section && lmap_get(&nc->new_by_id, id, pos);
}

/* memoryObject: what the pointee gives a pointer with reference ref without
 * a load: a value; or the handle's object if it may serve the pointer. */
static struct node *memory_object(struct obj *pointee, int64_t ref) {
    if (pointee == NULL) {
        return NULL;
    }
    if (pointee->kind == OBJ_VALUE) {
        return (struct node *) pointee;
    }
    struct handle *h = (struct handle *) pointee;
    struct node *o = h->obj;
    return o != NULL && hd_usable(o, ref) ? o : NULL;
}

/* touch: the CLOCK bit of a handle. */
static void touch(struct obj *pointee) {
    if (pointee != NULL && pointee->kind == OBJ_HANDLE) {
        pointee->flags |= OBJ_REF;
    }
}

/* readVersion: version pos of node id; during the reconstruction a key node
 * version of the section is cut back to the startup time (M22). */
static enum err_code read_version(struct ncoll *nc, int64_t id, int64_t pos,
        int32_t pointerIndex, struct node *predecessor, struct node **out, struct err *e) {
    if (spos_is_vpos(pos)) {
        return err_set(e, ERR_FORMAT, "StreamFormatException", "Pointer to node %" PRId64
                ", which is not in the stream and not in memory, index %d of node %" PRId64 ".",
                id, (int) pointerIndex, predecessor->id);
    }
    struct node *node;
    enum err_code rc = read_node(nc, pos, &node, e);
    if (rc == ERR_OK) {
        /* before an install (bergdb 019-32, as Java's since release 2026.3) */
        rc = nc_check_pointee_type(predecessor, pointerIndex, node, pos, e);
    }
    if (rc != ERR_OK) {
        return rc;
    }
    if (node->id != id) {
        /* Java's assert: "ids differ" */
        return err_set(e, ERR_FORMAT, "AssertionError", "ids differ, %" PRId64 " != %" PRId64,
                node->id, id);
    }
    nc->loads++;
    if (nc->reconstructing && nc->have_section && pos >= nc->section_start_pos
            && node_type(node) == NODE_TYPE_KEY_NODE) {
        kn_to_previous_state(nc->cx, (struct knode *) node, nc->section_startup_time);
    }
    *out = node;
    return ERR_OK;
}

/* cutBack: a version just read at pos was cut back by readVersion. */
static bool cut_back(const struct ncoll *nc, const struct node *node, int64_t pos) {
    return nc->reconstructing && nc->have_section && pos >= nc->section_start_pos
            && node_type(node) == NODE_TYPE_KEY_NODE;
}

/* followValuePointer: the value read at the pointer's position, put into the
 * pointer unless the cache policy says no (large values). */
static struct node *follow_value_pointer(struct ncoll *nc, struct node *predecessor,
        int32_t pointerIndex, int64_t pointerPos, struct opdata *op, bool isMaintenance) {
    /* Checks, not an assert (bergdb 019-32, as Java's since release 2026.3): the
     * pointer is stream data, and the node it names is a value. */
    if (pointerPos < 0 || spos_is_vpos(pointerPos)) {
        err_set(&nc->err, ERR_FORMAT, "StreamFormatException", "Bad value pointer %" PRId64
                ", index %d of node %" PRId64 ".", pointerPos, (int) pointerIndex,
                predecessor->id);
        return NULL;
    }
    struct node *node;
    enum err_code rc = read_node(nc, pointerPos, &node, &nc->err);
    if (rc == ERR_OK) {
        rc = nc_check_pointee_type(predecessor, pointerIndex, node, pointerPos, &nc->err);
    }
    if (rc != ERR_OK) {
        return NULL;
    }
    nc->loads++;
    if (!isMaintenance && op->cache_policy.should_cache(op->cache_policy.ctx, node)) {
        if (node_pointee(predecessor, pointerIndex) == NULL) {
            node_set_pointee(nc->cx, predecessor, pointerIndex, &node->o);
        }
    }
    if (!op->pointer_listener.pointer_followed(op->pointer_listener.ctx, predecessor,
            pointerIndex, node, PTR_TYPE_STREAM)) {
        err_set(&nc->err, ERR_NOMEM, "OutOfMemoryError", "a pointer listener");
        return NULL;
    }
    return node;
}

/* followStreamPointer: the slow path (009-02, 4.4). A maintenance read
 * (isMaintenance, reclaim's, 012-11) raises no reference, makes no handle,
 * installs nothing and does not swizzle, as Java's. */
static struct node *follow_stream_pointer(struct ncoll *nc, struct node *predecessor,
        int32_t pointerIndex, int64_t pointerPos, struct handle *handle, struct opdata *op,
        bool isWriter, bool isMaintenance) {
    if (!nc_points_to_index_node(predecessor, pointerIndex)) {
        return follow_value_pointer(nc, predecessor, pointerIndex, pointerPos, op,
                isMaintenance);
    }

    /* 1. The id of the node. A vpos is the id of a node that had not been
     *    written when the pointer was written. */
    int64_t id;
    if (handle != NULL) {
        id = handle->id;
    } else if (spos_is_vpos(pointerPos)) {
        id = pointerPos;
    } else {
        /* A check, not an assert (bergdb 019-32, as Java's since release 2026.3). */
        if (pointerPos < 0) {
            err_set(&nc->err, ERR_FORMAT, "StreamFormatException", "Bad pointer %" PRId64
                    ", index %d of node %" PRId64 ".", pointerPos, (int) pointerIndex,
                    predecessor->id);
            return NULL;
        }
        int32_t type;
        enum err_code rc = nc_read_node_header(nc, pointerPos, &type, &id, &nc->err);
        if (rc != ERR_OK) {
            return NULL;
        }
    }

    /* 2. The version the pointer names, after Rule R. A dead handle names the
     *    position this process last wrote the node at. */
    int64_t ref = pointerPos;
    int64_t newPos;
    if (nc->have_section && lmap_get(&nc->new_by_id, id, &newPos) && spos_newer(newPos, ref)) {
        ref = newPos;
    }
    if (handle != NULL) {
        ref = nc_newer_pos(ref, handle->written_pos);
    }
    if (ref != pointerPos && !isMaintenance) {
        node_raise_ref(predecessor, pointerIndex, ref);     /* never lowered (step 3d) */
    }

    /* 3. The node's live handle. A maintenance read makes none. */
    struct handle *live = handle != NULL && !hd_is_dead(handle) ? handle
            : isMaintenance ? nt_live_handle(nc->nt, id) : nt_live_or_new_handle(nc->nt, id);
    if (live == NULL && !isMaintenance) {
        err_set(&nc->err, ERR_NOMEM, "OutOfMemoryError", "a handle");
        return NULL;
    }

    /* 4. The handle's object, or a version read and installed. */
    struct node *result = NULL;
    bool cutBack = false;
    struct node *o = live == NULL ? NULL : live->obj;
    if (live == NULL) {
        /* A maintenance read of a node with no live handle: read, keep nothing. */
        struct node *node;
        enum err_code rc = read_version(nc, id, ref, pointerIndex, predecessor, &node, &nc->err);
        if (rc != ERR_OK) {
            return NULL;
        }
        cutBack = cut_back(nc, node, ref);
        result = node;
    } else if (o != NULL && hd_usable(o, ref)) {
        result = o;
    } else {
        struct node *node;
        enum err_code rc = read_version(nc, id, ref, pointerIndex, predecessor, &node, &nc->err);
        if (rc != ERR_OK) {
            /* The handle of step 3 stays in the table, empty, as Java's after
             * the exception. */
            return NULL;
        }
        cutBack = cut_back(nc, node, ref);
        /* A version cut back to the startup time is not the version at its
         * position: only the writer's rerun, which makes it canonical, keeps it
         * in the handle (M22). */
        if (!isMaintenance && op->cache_policy.should_cache(op->cache_policy.ctx, node)
                && (!cutBack || isWriter)) {
            if (nt_install(nc->nt, live, node, &result, &nc->err) != ERR_OK) {
                return NULL;
            }
            if (!hd_usable(result, ref)) {
                result = node;
            }
        } else {
            result = node;
        }
    }

    /* Also an object of the handle (bergdb 019-32, as Java's since release
     * 2026.3): a damaged node's id names another. */
    if (nc_check_pointee_type(predecessor, pointerIndex, result, ref, &nc->err) != ERR_OK) {
        return NULL;
    }

    /* A read that kept nothing in a new handle leaves no empty handle. */
    if (live != NULL && live->obj == NULL && !isMaintenance) {
        nt_drop_if_empty(nc->nt, live);
    }

    /* 5. Swizzle: the live handle into the pointer. */
    if (!isMaintenance && live != NULL && op->cache_policy.should_cache(op->cache_policy.ctx,
            result) && (!cutBack || isWriter) && node_pointee(predecessor, pointerIndex)
            != &live->o) {
        if (isWriter) {
            node_set_pointee(nc->cx, predecessor, pointerIndex, &live->o);
        } else {
            node_swizzle(nc->cx, predecessor, pointerIndex, handle == NULL ? NULL : &handle->o,
                    &live->o);
        }
    }

    /* 6. The canonical object, for the writer. */
    if (isWriter && !node_is_canonical(result)) {
        result = nt_make_canonical(nc->nt, live, result);
    }

    if (live != NULL) {
        touch(&live->o);
    }
    if (!op->pointer_listener.pointer_followed(op->pointer_listener.ctx, predecessor,
            pointerIndex, result, PTR_TYPE_STREAM)) {
        err_set(&nc->err, ERR_NOMEM, "OutOfMemoryError", "a pointer listener");
        return NULL;
    }
    return result;
}

/* followPointer, the readers' follower */
struct node *nc_follow_reader(void *ctx, struct node *predecessor, int32_t pointerIndex,
        struct opdata *op) {
    struct ncoll *nc = ctx;
    assert(pointerIndex >= 0 && "pointerIndex");
    assert(predecessor != NULL && "predecessor is null");
    struct obj *pointee = node_pointee(predecessor, pointerIndex);
    int64_t pointerPos = node_pointer_pos(predecessor, pointerIndex);
    struct node *mem = memory_object(pointee, pointerPos);
    if (mem != NULL) {
        touch(pointee);
        if (!op->pointer_listener.pointer_followed(op->pointer_listener.ctx, predecessor,
                pointerIndex, mem, PTR_TYPE_MEMORY)) {
            err_set(&nc->err, ERR_NOMEM, "OutOfMemoryError", "a pointer listener");
            return NULL;
        }
        return mem;
    }
    assert((pointee != NULL || pointerPos != SPOS_NULL) && "Pointer is null");
    return follow_stream_pointer(nc, predecessor, pointerIndex, pointerPos,
            pointee != NULL && pointee->kind == OBJ_HANDLE ? (struct handle *) pointee : NULL,
            op, false, false);
}

/* MaintenanceFollower.followPointer (reclaim's scan and reads, 012-11): an
 * object in memory as the readers' follower takes it, without the touch;
 * else the version read, kept by nothing (Java's map of the versions it
 * read, by position, saves reads only, and is left out). */
struct node *nc_follow_maintenance(void *ctx, struct node *predecessor, int32_t pointerIndex,
        struct opdata *op) {
    struct ncoll *nc = ctx;
    assert(pointerIndex >= 0 && "pointerIndex");
    assert(predecessor != NULL && "predecessor is null");
    struct obj *pointee = node_pointee(predecessor, pointerIndex);
    int64_t pointerPos = node_pointer_pos(predecessor, pointerIndex);
    assert((pointee != NULL || pointerPos != SPOS_NULL) && "Pointer is null");
    struct node *mem = memory_object(pointee, pointerPos);
    if (mem != NULL) {
        if (!op->pointer_listener.pointer_followed(op->pointer_listener.ctx, predecessor,
                pointerIndex, mem, PTR_TYPE_MEMORY)) {
            err_set(&nc->err, ERR_NOMEM, "OutOfMemoryError", "a pointer listener");
            return NULL;
        }
        return mem;
    }
    return follow_stream_pointer(nc, predecessor, pointerIndex, pointerPos,
            pointee != NULL && pointee->kind == OBJ_HANDLE ? (struct handle *) pointee : NULL,
            op, false, true);
}

/* WriterFollower.followPointer */
struct node *nc_follow_writer(void *ctx, struct node *predecessor, int32_t pointerIndex,
        struct opdata *op) {
    struct ncoll *nc = ctx;
    assert(pointerIndex >= 0 && "pointerIndex");
    assert(predecessor != NULL && "predecessor is null");
    struct obj *pointee = node_pointee(predecessor, pointerIndex);
    int64_t pointerPos = node_pointer_pos(predecessor, pointerIndex);
    assert((pointee != NULL || pointerPos != SPOS_NULL) && "Pointer is null");
    struct node *mem = memory_object(pointee, pointerPos);
    if (mem != NULL) {
        struct node *result = mem;
        if (!node_is_canonical(result)) {
            result = nt_make_canonical(nc->nt, (struct handle *) pointee, result);
        }
        touch(pointee);
        if (!op->pointer_listener.pointer_followed(op->pointer_listener.ctx, predecessor,
                pointerIndex, result, PTR_TYPE_MEMORY)) {
            err_set(&nc->err, ERR_NOMEM, "OutOfMemoryError", "a pointer listener");
            return NULL;
        }
        return result;
    }
    return follow_stream_pointer(nc, predecessor, pointerIndex, pointerPos,
            pointee != NULL && pointee->kind == OBJ_HANDLE ? (struct handle *) pointee : NULL,
            op, true, false);
}

enum err_code nc_resolve_pointers(struct ncoll *nc, struct node *node, struct err *e) {
    const int32_t count = node_size(node);
    for (int32_t i = 0; i < count; i++) {
        if (!nc_points_to_index_node(node, i)) {
            continue;       /* Value nodes have one version and are never dirty. */
        }
        struct obj *pointee = node_pointee(node, i);
        int64_t pos = node_pointer_pos(node, i);
        struct handle *h = (struct handle *) pointee;
        if (h == NULL && spos_is_null(pos)) {
            continue;
        }
        struct node *o = h == NULL ? NULL : h->obj;
        if (o != NULL && node_is_canonical(o)) {
            continue;
        }
        /* A stream pointer below the first position of the stream names a
         * version that reclaim cut away; it is left as it is. */
        if (h == NULL && !spos_is_vpos(pos) && pos < stream_first_pos(nc->s)) {
            continue;
        }
        int64_t id;
        if (h != NULL) {
            id = h->id;
        } else {
            enum err_code rc = id_of(nc, pos, &id, e);
            if (rc != ERR_OK) {
                return rc;
            }
        }

        /* 1. A pinned pointee, by node id: its live handle. */
        struct handle *live = nt_live_handle(nc->nt, id);
        struct node *pinned = live == NULL ? NULL : live->obj;
        if (pinned != NULL && node_is_canonical(pinned) && node_is_dirty(pinned)) {
            if (h != live) {
                node_set_pointee(nc->cx, node, i, &live->o);
            }
            continue;
        }

        /* 2. Any other: the pointer's reference after Rule R. */
        int64_t ref = pos;
        int64_t newPos;
        if (nc_newest_in_section(nc, id, &newPos) && spos_newer(newPos, ref)) {
            ref = newPos;
        }
        if (ref != pos) {
            node_set_ref(node, i, ref);
        }
    }
    return ERR_OK;
}

/* checkLinkById: the handle that rule 4 by position gave pointer i, at pos,
 * is the one that rule 4 by node id gives, with a read of the header. */
static enum err_code check_link_by_id(struct ncoll *nc, struct node *node, int32_t i,
        int64_t pos, struct handle *linked, struct err *e) {
    int64_t id;
    enum err_code rc = id_of(nc, pos, &id, e);
    if (rc != ERR_OK) {
        return rc;
    }
    struct handle *byId = nt_live_handle(nc->nt, id);
    struct node *o = byId == NULL ? NULL : byId->obj;
    struct handle *expected = o != NULL && node_is_canonical(o) ? byId : NULL;
    if (linked != expected) {
        return err_set(e, ERR_FORMAT, "AssertionError", "rule 4 by position is not rule 4 by "
                "node id (bergdb 005-57): pointer %d of node %" PRId64 " names %" PRId64
                "; by position %s %" PRId64 ", by node id %s %" PRId64, (int) i, node->id, pos,
                linked == NULL ? "no canonical object" : "node", linked == NULL ? -1 : linked->id,
                expected == NULL ? "no canonical object" : "node",
                expected == NULL ? -1 : expected->id);
    }
    return ERR_OK;
}

enum err_code nc_link_to_canonical(struct ncoll *nc, struct node *node, const struct lmap *ids,
        const struct lmap *byPos, struct err *e) {
    const int32_t count = node_size(node);
    const bool top = node_type(node) == NODE_TYPE_TOP_NODE;
    for (int32_t i = 0; i < count; i++) {
        if (!nc_points_to_index_node(node, i)) {
            continue;
        }
        struct obj *pointee = node_pointee(node, i);
        int64_t pos = node_pointer_pos(node, i);
        if (pointee != NULL || spos_is_null(pos)) {
            continue;
        }
        if (!spos_is_vpos(pos) && pos < stream_first_pos(nc->s)) {
            continue;
        }
        int64_t id = pos;
        bool haveId = spos_is_vpos(pos) || lmap_get(ids, pos, &id);
        struct handle *live = NULL;
        int64_t hv;
        if (haveId) {
            live = nt_live_handle(nc->nt, id);
        } else if (lmap_get(byPos, pos, &hv)) {
            live = to_handle(hv);
        }
        if (live == NULL && !haveId && top) {
            int64_t tid;
            enum err_code rc = id_of(nc, pos, &tid, e);
            if (rc != ERR_OK) {
                return rc;
            }
            live = nt_live_handle(nc->nt, tid);
        }
        struct node *canonical = live == NULL ? NULL : live->obj;
        if (canonical == NULL || !node_is_canonical(canonical)) {
            live = NULL;
        }
        if (nc->check_link) {
            enum err_code rc = check_link_by_id(nc, node, i, pos, live, e);
            if (rc != ERR_OK) {
                return rc;
            }
        }
        if (live != NULL) {
            node_set_pointee(nc->cx, node, i, &live->o);
        }
    }
    return ERR_OK;
}
