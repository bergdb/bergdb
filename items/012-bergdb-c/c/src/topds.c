/* topds: ported from Java's bergdb.dag.TopDs; see topds.h. */
#include "topds.h"
#include <assert.h>
#include "handle.h"
#include "spos.h"

/* TopDs(superRoot) */
void tds_init(struct topds *ds, struct tnode *superRoot) {
    assert(superRoot != NULL && "superRoot == null not allowed");
    obj_retain(&superRoot->n.o);
    ds->super_root = superRoot;
    ds->second_ordinal = 1;
}

void tds_free(struct obj_ctx *cx, struct topds *ds) {
    struct tnode *t = ds->super_root;
    ds->super_root = NULL;
    obj_release(cx, t == NULL ? NULL : &t->n.o);
}

/* TopDs.createSuperRootFromFirstKeyNode */
struct tnode *tds_create_super_root_from_first_key_node(struct obj_ctx *cx, int64_t firstTime,
        struct knode *firstRoot, int64_t accessData,
        const struct op_pointer_created_listener *pointerCreationListener) {
    struct tnode *first = tn_new(cx, 0, firstRoot, accessData, firstTime, SPOS_NULL);
    if (first == NULL || !op_pointer_created(pointerCreationListener, &first->n, 0,
            firstRoot == NULL ? NULL : &firstRoot->n)) {
        return NULL;
    }
    return first;
}

/* TopDs.createFromFirstRoot */
bool tds_create_from_first_root(struct obj_ctx *cx, struct topds *ds, int64_t firstTime,
        struct knode *firstRoot, int64_t accessData,
        const struct op_pointer_created_listener *pointerCreationListener) {
    struct tnode *first = tds_create_super_root_from_first_key_node(cx, firstTime, firstRoot,
            accessData, pointerCreationListener);
    if (first == NULL) {
        return false;
    }
    tds_init(ds, first);
    return true;
}

/* TopDs.setSecondOrdinal */
bool tds_set_second_ordinal(struct topds *ds, int64_t ordinal) {
    if (ordinal < 1 || ordinal > TN_MAX_TOP_NODE_ID_VALUE) {
        return false;           /* IllegalArgumentException, "Bad ordinal" */
    }
    ds->second_ordinal = ordinal;
    return true;
}

/* TopDs.newSuperRoot */
bool tds_new_super_root(struct obj_ctx *cx, struct topds *ds, int64_t time, struct knode *newRoot,
        int64_t accessData, const struct op_pointer_created_listener *pointerCreationListener,
        const struct op_node_change_listener *nodeChangeListener) {
    struct tnode *superRoot = ds->super_root;

    if (time == superRoot->root_time) {
        /* A second new space root in the same transaction, for example a
         * time split of the root followed by a space split. The super root
         * was created by this transaction: update it instead of creating a
         * new top node. */
        struct handle *h = hd_of(cx, &newRoot->n);
        if (h == NULL) {
            return false;
        }
        tn_set_pointer(cx, superRoot, 0, &h->o, newRoot->n.spos);
        return op_pointer_created(pointerCreationListener, &superRoot->n, 0, &newRoot->n);
    }

    assert(time > superRoot->root_time);

    /* The ordinal: one more than the super root's (005-02). */
    const int64_t id = superRoot->top_node_id == 0 ? ds->second_ordinal
            : superRoot->top_node_id + 1;
    struct tnode *newSuperRoot = tn_new(cx, id, newRoot, accessData, time, SPOS_NULL);
    if (newSuperRoot == NULL) {
        return false;
    }
    const int32_t h = newSuperRoot->pointers_length;

    if (!op_top_node_created(nodeChangeListener, newSuperRoot)
            || !op_top_node_replaced(nodeChangeListener, superRoot)  /* existed before */
            || !op_pointer_created(pointerCreationListener, &newSuperRoot->n, 0, &newRoot->n)) {
        return false;
    }

    for (int32_t i = 0; i < h; i++) {
        if ((id & tn_power2(i)) != 0) {
            struct obj *inherited = NULL;
            int64_t inheritedRef = SPOS_NULL;

            if (i < superRoot->pointers_length) {
                inherited = tn_get_pointee(superRoot, i + 1);
                inheritedRef = tn_get_pointer_pos(superRoot, i + 1);
            }

            if (inherited != NULL || inheritedRef != SPOS_NULL) {
                /* Inherited as it is, its handle and its reference (bergdb item
                 * 009, step 3a). The time is the target's root time, cached. */
                tn_set_pointee(cx, newSuperRoot, i + 1, inherited);
                newSuperRoot->skip[i].pos = inheritedRef;
                newSuperRoot->skip[i].time = superRoot->skip[i].time;
                continue;
            }

            /* The super root lacks the skip pointer: the new one names the
             * super root. */
            struct handle *sh = hd_of(cx, &superRoot->n);
            if (sh == NULL) {
                return false;
            }
            tn_set_pointee(cx, newSuperRoot, i + 1, &sh->o);
            newSuperRoot->skip[i].time = superRoot->root_time;
            newSuperRoot->skip[i].pos = superRoot->n.spos;
            if (!op_pointer_created(pointerCreationListener, &newSuperRoot->n, i + 1,
                    &superRoot->n)) {
                return false;
            }
        }
    }

    /* this.superRoot = newSuperRoot: the field holds the new one. */
    obj_retain(&newSuperRoot->n.o);
    ds->super_root = newSuperRoot;
    obj_release(cx, &superRoot->n.o);
    return true;
}

/* TopDs.getSuperRoot */
struct tnode *tds_get_super_root(const struct topds *ds) {
    return ds->super_root;
}

/* TopDs.findRoot */
bool tds_find_root(struct topds *ds, int64_t time, struct opdata *op, struct knode **out) {
    struct tnode *n;
    *out = NULL;
    if (!tds_find_super_root_at_time(ds, time, op, &n)) {
        return false;
    }
    if (n == NULL) {
        return true;
    }
    struct node *r = op_follow_pointer(op, &n->n, 0);
    if (r == NULL) {
        return false;
    }
    assert(r->o.kind == OBJ_KEY);       /* Java's cast (KeyNode) */
    *out = (struct knode *) r;
    return true;
}

/* TopDs.rightMostGte: p, the right-most skip pointer whose time is at or
 * after t. */
static void right_most_gte(struct tnode *n, int64_t t, struct pointer *p) {
    ptr_reset(p);

    for (int32_t i = n->pointers_length - 1; i >= 0; i--) {
        struct node *top = tn_get_pointer_node(n, i + 1);
        if (ptr_is_null2(top, n->skip[i].pos)) {
            continue;
        }

        if (n->skip[i].time >= t) {
            p->node = top;
            p->pos = n->skip[i].pos;
            p->index = i + 1;   /* +1 because root pointer has index 0. */
            break;
        }
    }
}

/* TopDs.leftMost */
static void left_most(struct tnode *n, int64_t t, struct pointer *p) {
    ptr_reset(p);
    const int32_t pointersLength = n->pointers_length;

    for (int32_t i = 0; i < pointersLength; i++) {
        struct node *top = tn_get_pointer_node(n, i + 1);

        if (ptr_is_null2(top, n->skip[i].pos)) {
            continue;
        }

        if (t >= n->skip[i].time) {
            p->node = top;
            p->pos = n->skip[i].pos;
            p->index = i + 1;   /* +1 since root pointer has index 0. */
        }

        break;
    }
}

/* TopDs.findSuperRootAtTime */
bool tds_find_super_root_at_time(struct topds *ds, int64_t time, struct opdata *op,
        struct tnode **out) {
    struct tnode *mySuperRoot = ds->super_root;
    *out = NULL;

    if (!op_super_root_accessed(&op->pointer_listener, mySuperRoot)) {
        return false;
    }

    if (time >= mySuperRoot->root_time) {
        *out = mySuperRoot;
        return true;
    }

    struct tnode *n = mySuperRoot;

    /* Finds right-most pointer with time >= 'time'. */

    struct pointer *pt = &op->temp_pointer;

    while (true) {
        right_most_gte(n, time, pt);
        if (ptr_is_null(pt)) {
            break;
        }

        struct node *next = op_follow_pointer(op, &n->n, pt->index);
        if (next == NULL) {
            return false;
        }
        assert(next->o.kind == OBJ_TOP);
        n = (struct tnode *) next;
    }

    if (n->root_time == time) {
        *out = n;
        return true;
    }

    /* Find left-most pointer */

    ptr_reset(pt);
    left_most(n, time, pt);

    if (ptr_is_null(pt)) {
        return true;            /* No old-enough node exists */
    }

    struct node *n2 = op_follow_pointer(op, &n->n, pt->index);
    if (n2 == NULL) {
        return false;
    }
    assert(n2->o.kind == OBJ_TOP);
    *out = (struct tnode *) n2;
    return true;
}
