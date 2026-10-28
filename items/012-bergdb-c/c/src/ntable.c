/* ntable: the node table, Java's Cache3 in part; see ntable.h. */
#include "ntable.h"
#include <assert.h>
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

bool nt_register(struct ntable *t, struct node *node, struct node **out) {
    if (!node_is_index_node(node)) {
        *out = node;    /* Values have no handles and are not in the table (009-02, 4.8). */
        return true;
    }
    int64_t id = node->id;
    struct handle *h = nt_live_handle(t, id);
    if (h == NULL) {
        h = handle_of(node);
        if (h == NULL || h->id != id || hd_is_dead(h)) {
            h = hd_new(t->cx, id);
            if (h == NULL) {
                return false;
            }
        }
        if (!put(t, id, h)) {
            return false;
        }
    }
    struct node *old = h->obj;
    if (old == NULL || (old != node && is_better(node, old))) {
        hd_set_obj(t->cx, h, node);
        *out = node;
        return true;
    }
    *out = old;
    return true;
}

struct node *nt_install(struct ntable *t, struct handle *h, struct node *node) {
    struct node *old = h->obj;
    if (old == NULL || (old != node && is_better(node, old))) {
        hd_set_obj(t->cx, h, node);
        return node;
    }
    return old;
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
