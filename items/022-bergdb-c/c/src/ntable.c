/* ntable: the node table, Java's Cache3 in part; see ntable.h. */
#include "ntable.h"
#include <assert.h>
#include <inttypes.h>
#include <stddef.h>
#include "knode.h"
#include "tnode.h"

static int64_t to_long(struct handle *h) {
    return (int64_t) (intptr_t) h;
}

static struct handle *to_handle(int64_t v) {
    return (struct handle *) (intptr_t) v;
}

void nt_init(struct ntable *t, struct obj_ctx *cx, struct mem *m) {
    t->cx = cx;
    lmap_init(&t->map, m);
}

void nt_free(struct ntable *t, bool release) {
    if (release) {
        for (int64_t i = 0; i < t->map.cap; i++) {
            if (t->map.used[i]) {
                obj_release(t->cx, &to_handle(t->map.vals[i])->o);
            }
        }
    }
    lmap_free(&t->map);
}

/* internalGet */
struct handle *nt_live_handle(const struct ntable *t, int64_t id) {
    int64_t v;
    return lmap_get(&t->map, id, &v) ? to_handle(v) : NULL;
}

/* internalPut: the table holds h. */
static bool put(struct ntable *t, int64_t id, struct handle *h) {
    if (!lmap_put(&t->map, id, to_long(h))) {
        return false;
    }
    obj_retain(&h->o);
    return true;
}

/* internalRemove */
static void remove_handle(struct ntable *t, struct handle *h) {
    if (lmap_remove(&t->map, h->id)) {
        obj_release(t->cx, &h->o);
    }
}

struct handle *nt_live_or_new_handle(struct ntable *t, int64_t id) {
    struct handle *h = nt_live_handle(t, id);
    if (h == NULL) {
        h = hd_new(t->cx, id);
        if (h == NULL || !put(t, id, h)) {
            return NULL;        /* h, if made, is pending */
        }
    }
    return h;
}

struct node *nt_get_node(const struct ntable *t, int64_t id) {
    struct handle *h = nt_live_handle(t, id);
    return h == NULL ? NULL : h->obj;
}

/* Cache3.handleOf: the handle the object is in (its back reference). */
static struct handle *handle_of(struct node *node) {
    if (node->o.kind == OBJ_KEY) {
        return ((struct knode *) node)->handle;
    }
    if (node->o.kind == OBJ_TOP) {
        return ((struct tnode *) node)->handle;
    }
    return NULL;
}

/* Cache3.isBetter: never over a canonical object; else a canonical object or a
 * newer version. */
static bool is_better(const struct node *node, const struct node *old) {
    if (node_is_canonical(old)) {
        assert(!node_is_canonical(node) && "two canonical objects for one node");
        return false;
    }
    return node_is_canonical(node) || node->spos > old->spos;
}

/* Cache3.checkType: one node, one type (bergdb 019-32, as Java's since
 * release 2026.3). A node from a damaged stream whose id was changed to that
 * of a node of another type (its checksum right) went into that node's
 * handle, and a pointer to the other node got it: in Java a
 * ClassCastException, in C a read of the node as the wrong type. */
static enum err_code check_type(const struct node *old, const struct node *node,
        struct err *e) {
    if (old != NULL && node_type(old) != node_type(node)) {
        return err_set(e, ERR_FORMAT, "StreamFormatException", "Two nodes with the id %" PRId64
                ": of type %d at %" PRId64 ", and of type %d at %" PRId64 ".", node->id,
                (int) node_type(old), old->spos, (int) node_type(node), node->spos);
    }
    return ERR_OK;
}

enum err_code nt_register(struct ntable *t, struct node *node, struct node **out,
        struct err *e) {
    if (!node_is_index_node(node)) {
        *out = node;    /* Values have no handles and are not in the table (009-02, 4.8). */
        return ERR_OK;
    }
    int64_t id = node->id;
    struct handle *h = nt_live_handle(t, id);
    if (h == NULL) {
        h = handle_of(node);
        if (h == NULL || h->id != id || hd_is_dead(h)) {
            h = hd_new(t->cx, id);
            if (h == NULL) {
                return err_set(e, ERR_NOMEM, "OutOfMemoryError", "the node table");
            }
        }
        if (!put(t, id, h)) {
            return err_set(e, ERR_NOMEM, "OutOfMemoryError", "the node table");
        }
    }
    struct node *old = h->obj;
    enum err_code rc = check_type(old, node, e);
    if (rc != ERR_OK) {
        return rc;
    }
    if (old == NULL || (old != node && is_better(node, old))) {
        hd_set_obj(t->cx, h, node);
        *out = node;
        return ERR_OK;
    }
    *out = old;
    return ERR_OK;
}

enum err_code nt_install(struct ntable *t, struct handle *h, struct node *node,
        struct node **out, struct err *e) {
    struct node *old = h->obj;
    enum err_code rc = check_type(old, node, e);
    if (rc != ERR_OK) {
        return rc;
    }
    if (old == NULL || (old != node && is_better(node, old))) {
        hd_set_obj(t->cx, h, node);
        *out = node;
        return ERR_OK;
    }
    *out = old;
    return ERR_OK;
}

struct node *nt_make_canonical(struct ntable *t, struct handle *h, struct node *node) {
    struct node *other = h->obj;
    struct node *result = node;
    if (other != NULL && other != node) {
        if (node_is_canonical(other) || other->spos > node->spos) {
            result = other;
        }
    }
    node_set_canonical(result, true);
    if (other != result) {
        hd_set_obj(t->cx, h, result);
    }
    return result;
}

void nt_drop_if_empty(struct ntable *t, struct handle *h) {
    if (h->obj == NULL && nt_live_handle(t, h->id) == h && !hd_is_dead(h)) {
        hd_kill(t->cx, h);
        remove_handle(t, h);
    }
}

int64_t nt_size(const struct ntable *t) {
    return t->map.size;
}

int64_t nt_slots(const struct ntable *t) {
    return t->map.cap;
}

struct handle *nt_slot(const struct ntable *t, int64_t i) {
    return t->map.used[i] ? to_handle(t->map.vals[i]) : NULL;
}

bool nt_evict(struct ntable *t, struct handle *h) {
    if (hd_is_dead(h)) {
        return false;
    }
    hd_kill(t->cx, h);
    if (nt_live_handle(t, h->id) == h) {
        remove_handle(t, h);
    }
    return true;
}

int64_t nt_bytes(const struct ntable *t) {
    return t->map.cap * (int64_t) (2 * sizeof(int64_t) + 1);
}

/* The smallest table that nt_shrink makes, in slots. */
#define NT_MIN_SHRINK 1024

void nt_shrink(struct ntable *t) {
    if (t->map.cap <= NT_MIN_SHRINK || t->map.size >= t->map.cap / 8) {
        return;
    }
    struct lmap n;
    lmap_init(&n, t->map.mem);
    for (int64_t i = 0; i < t->map.cap; i++) {
        if (t->map.used[i] && !lmap_put(&n, t->map.keys[i], t->map.vals[i])) {
            lmap_free(&n);
            return;
        }
    }
    lmap_free(&t->map);
    t->map = n;
}
