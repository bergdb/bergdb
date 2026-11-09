/* evict: eviction to a memory budget, Java's Eviction (BUDGET) and Cache3's
 * evict and clockStep, for one caller; see evict.h. */
#include "evict.h"
#include <assert.h>
#include <stddef.h>
#include "handle.h"
#include "jsem.h"
#include "knode.h"
#include "spos.h"
#include "vnode.h"

void ev_init(struct ev *ev, struct obj_ctx *cx, struct mem *m, int64_t budget) {
    *ev = (struct ev) {0};
    ev->mem = m;
    ev->cx = cx;
    ev_set_budget(ev, budget);
}

void ev_free(struct ev *ev) {
    for (int32_t i = 0; i < ev->nlarge; i++) {
        obj_release(ev->cx, &ev->large[i].holder->n.o);
        obj_release(ev->cx, &ev->large[i].value->n.o);
    }
    mem_free(ev->mem, ev->large, (size_t) ev->cap_large * sizeof *ev->large, MEM_STATE);
    ev->large = NULL;
    ev->nlarge = ev->cap_large = 0;
}

int64_t ev_low_of(int64_t budget) {
    return budget == INT64_MAX ? INT64_MAX : budget / 4 * 3 + budget % 4 * 3 / 4;
}

/* Eviction.setBudget: high the budget, low lowOf(budget), the trigger the
 * budget. */
void ev_set_budget(struct ev *ev, int64_t budget) {
    assert(budget >= 1);
    ev->high = budget;
    ev->low = ev_low_of(budget);
    ev->trigger = budget;
}

int64_t ev_resident_bytes(const struct mem *m, const struct ntable *nt) {
    return m->live[MEM_INDEX] + m->live[MEM_VALUE] + m->live[MEM_HANDLE] + nt_bytes(nt);
}

/* Eviction.detachable */
bool ev_detachable(const struct node *o, const struct tnode *superRoot,
        const struct tnode *newestWrittenTop) {
    if (node_is_in_trans_nodes(o)) {
        return false;
    }
    if (node_is_index_node(o)) {
        if (o == &superRoot->n || (newestWrittenTop != NULL && o == &newestWrittenTop->n)) {
            return false;
        }
        /* Residents.isPinned: canonical and dirty (D) or in the record. */
        if (node_is_canonical(o) && node_is_dirty(o)) {
            return false;
        }
    }
    const int64_t spos = o->spos;
    return spos_is_valid(spos) && !spos_is_vpos(spos);
}

/* A written value that may leave memory: not in the record, at a stream
 * position (Eviction.unswizzleValues' test). */
static bool written_value(const struct vnode *v) {
    const int64_t spos = v->n.spos;
    return !node_is_in_trans_nodes(&v->n) && spos_is_valid(spos) && !spos_is_vpos(spos);
}

/* Eviction.unswizzleValue: pointer i of x, which holds value v, becomes a
 * stream pointer naming v's position. */
static void unswizzle_value(struct ev *ev, struct knode *x, int32_t i, struct vnode *v) {
    kn_set_pointer(ev->cx, x, i, NULL, v->n.spos);
    ev->unswizzled++;
}

/* Eviction.unswizzleValues: the written values that pinned key node x holds
 * become stream pointers. */
static void unswizzle_values(struct ev *ev, struct knode *x) {
    const int32_t size = x->size;
    for (int32_t i = 0; i < size; i++) {
        struct obj *p = kn_get_pointee(x, i);
        if (p == NULL || p->kind != OBJ_VALUE) {
            continue;
        }
        struct vnode *v = (struct vnode *) p;
        if (written_value(v)) {
            unswizzle_value(ev, x, i, v);
        }
    }
}

/* One sweep (Eviction.sweep with Cache3.clockStep, 009-02, 4.7): the CLOCK
 * hand over the node table's slots until the resident bytes are at most the
 * low watermark, or two rounds. A removal from the table moves later
 * entries back (lmap.h's backward shift), so after one the hand looks at its
 * slot again. Each evicted object is freed at once (a safe point). Returns
 * the bytes freed. */
static int64_t sweep(struct ev *ev, const struct ev_env *env, bool in_call) {
    struct ntable *nt = env->nt;
    const int64_t before = ev_resident_bytes(ev->mem, nt);
    const int64_t cap = nt_slots(nt);
    ev->sweeps++;
    if (before > ev->max_before) {
        ev->max_before = before;
    }
    bool complete = true;
    /* Two rounds: the hand moves 2 * cap times; an eviction does not move it
     * (its slot is looked at again), and each takes an entry. */
    int64_t moves = 0;
    while (moves < 2 * cap) {
        if (ev_resident_bytes(ev->mem, nt) <= ev->low) {
            complete = false;
            break;
        }
        if (ev->hand >= cap) {
            ev->hand = 0;
        }
        ev->examined++;
        struct handle *h = nt_slot(nt, ev->hand);
        if (h == NULL) {
            ev->hand++;
            moves++;
            continue;
        }
        struct node *o = h->obj;
        if (o == NULL) {
            /* A live handle with no object (a read that kept nothing) leaves
             * the table too. */
            nt_evict(nt, h);
            obj_collect(ev->cx);
            ev->dropped++;
            continue;
        }
        if (!ev_detachable(o, env->super_root, env->newest_written_top)) {
            if (o->o.kind == OBJ_KEY) {
                unswizzle_values(ev, (struct knode *) o);
                obj_collect(ev->cx);
            }
            ev->hand++;
            moves++;
            continue;
        }
        if ((h->o.flags & OBJ_REF) != 0) {
            h->o.flags &= (uint16_t) ~OBJ_REF;     /* a second chance */
            ev->hand++;
            moves++;
            continue;
        }
        nt_evict(nt, h);
        obj_collect(ev->cx);
        ev->evicted++;
    }
    /* The node table's arrays shrink first (nt_shrink), as they count in
     * the resident bytes: a floor measured before would keep the arrays of
     * the table's largest size in the trigger, and after a take that wrote
     * most of D the trigger would stay far above what is resident while
     * reclaim's loads grow unevicted (14-robustness.md, 6.8). */
    nt_shrink(nt);
    if (ev->hand >= nt_slots(nt)) {
        ev->hand = 0;
    }
    const int64_t after = ev_resident_bytes(ev->mem, nt);
    /* The trigger (Eviction.sweep's last step): after two rounds what is left
     * could not go; the controller runs again once the resident bytes have
     * grown over it by the gap between the watermarks, or by the node table's
     * own bytes if that is more (the margin, bergdb 022-06, U1-4: a sweep
     * looks at the table's slots, two rounds, so the next sweep that cannot
     * reach the budget waits for the calls to load at least as many bytes as
     * the table has; evict.h). */
    const int64_t gap = ev->high - ev->low;
    const int64_t table = nt_bytes(nt);
    const int64_t margin = table > gap ? table : gap;
    if (in_call) {
        /* Inside a call, what the call holds (a getMany's chain, its values)
         * cannot go either, but only until the call ends: the floor so found
         * lasts for the call (call_trigger). */
        if (complete) {
            ev->call_trigger = after > ev->high - gap ? after + margin : ev->high;
        }
    } else if (complete) {
        ev->complete_sweeps++;
        ev->floor = after;
        ev->floor_dirty = env->d->dirtyCount;
        ev->trigger = ev->floor > ev->high - gap ? ev->floor + margin : ev->high;
    } else {
        ev->trigger = ev->high;
    }
    return before - after;
}

void ev_run(struct ev *ev, const struct ev_env *env, bool in_call) {
    obj_collect(ev->cx);
    if (ev->trigger > ev->high && env->d->dirtyCount < ev->floor_dirty) {
        ev->trigger = ev->high;     /* the floor is old: D has shrunk */
    }
    if (!in_call) {
        ev->call_trigger = 0;       /* the call's floor ends with the call */
    }
    bool swept = false;
    while (ev_resident_bytes(ev->mem, env->nt)
            > (ev->call_trigger > ev->trigger ? ev->call_trigger : ev->trigger)) {
        swept = true;
        if (sweep(ev, env, in_call) <= 0) {
            break;
        }
    }
#ifdef BERGDB_TEST
    if (swept) {
        assert(ev_check_pins(env) == 0 && "a pinned object left the node table");
    }
#else
    (void) swept;
#endif
}

bool ev_large_value_created(struct ev *ev, struct knode *holder, int32_t index,
        struct vnode *v) {
    if (ev->nlarge == ev->cap_large) {
        const int32_t ncap = ev->cap_large == 0 ? 4 : 2 * ev->cap_large;
        struct ev_large *n = mem_realloc(ev->mem, ev->large,
                (size_t) ev->cap_large * sizeof *n, (size_t) ncap * sizeof *n, MEM_STATE);
        if (n == NULL) {
            return false;
        }
        ev->large = n;
        ev->cap_large = ncap;
    }
    obj_retain(&holder->n.o);
    obj_retain(&v->n.o);
    ev->large[ev->nlarge++] = (struct ev_large) {holder, index, v};
    return true;
}

static bool is_large(const struct vnode *v) {
    return v->len > EV_LARGE_VALUE;
}

/* Eviction.recordWritten's first part: the large values the transaction
 * made, through their pointers as the writer made them; a value is written
 * with its transaction's record. The list is emptied. */
static void admit_listed(struct ev *ev) {
    for (int32_t k = 0; k < ev->nlarge; k++) {
        struct knode *x = ev->large[k].holder;
        int32_t i = ev->large[k].index;
        struct vnode *v = ev->large[k].value;
        if (spos_is_valid(v->n.spos) && !spos_is_vpos(v->n.spos)) {
            const int32_t size = x->size;
            if (i >= size || kn_get_pointee(x, i) != &v->n.o) {
                i = -1;
                for (int32_t j = 0; j < size; j++) {
                    if (kn_get_pointee(x, j) == &v->n.o) {
                        i = j;
                    }
                }
            }
            if (i >= 0) {
                unswizzle_value(ev, x, i, v);
            }
        }
        obj_release(ev->cx, &x->n.o);
        obj_release(ev->cx, &v->n.o);
    }
    ev->nlarge = 0;
}

/* Eviction.recordWritten's second part, for one written key node x: its
 * pointers to written large values become stream pointers. */
static void admit_written(struct ev *ev, struct knode *x) {
    const int32_t size = x->size;
    for (int32_t i = 0; i < size; i++) {
        struct obj *p = kn_get_pointee(x, i);
        if (p == NULL || p->kind != OBJ_VALUE) {
            continue;
        }
        struct vnode *v = (struct vnode *) p;
        if (is_large(v) && spos_is_valid(v->n.spos) && !spos_is_vpos(v->n.spos)) {
            unswizzle_value(ev, x, i, v);
        }
    }
}

void ev_record_written(struct ev *ev, const struct transnodes *tn) {
    admit_listed(ev);
    /* The record's key nodes. */
    for (int32_t k = 0; k < tn->key_count; k++) {
        admit_written(ev, tn->key_nodes[k]);
    }
}

void ev_record_written_start(struct ev *ev, const struct ntable *nt) {
    admit_listed(ev);
    /* The resident key nodes as the written nodes, Java's cache.nodes(): the
     * object of each live handle of the node table (bergdb 019-47). The
     * walk changes no slot: an unswizzle changes a pointer of its key node
     * and lets the value go, to be freed at the next safe point. */
    for (int64_t s = 0; s < nt_slots(nt); s++) {
        const struct handle *h = nt_slot(nt, s);
        if (h != NULL && h->obj != NULL && h->obj->o.kind == OBJ_KEY) {
            admit_written(ev, (struct knode *) h->obj);
        }
    }
}

/* The bytes of object o as allocated (knode.c's, tnode.c's, vnode.c's and
 * handle.c's sizes). */
static int64_t obj_bytes(const struct obj *o) {
    switch (o->kind) {
    case OBJ_KEY: {
        const struct knode *k = (const struct knode *) o;
        return (int64_t) (sizeof(struct knode) + (size_t) k->cap * (2 * sizeof(int64_t)
                + sizeof(struct obj *)));
    }
    case OBJ_TOP:
        return (int64_t) (sizeof(struct tnode) + (size_t) ((const struct tnode *) o)->pointers_length
                * sizeof(struct tskip));
    case OBJ_VALUE: {
        const int32_t len = ((const struct vnode *) o)->len;
        return (int64_t) (sizeof(struct vnode) + (len < 0 ? 0 : (size_t) len));
    }
    default:
        return (int64_t) sizeof(struct handle);
    }
}

/* A pinned object's bytes with its handle and what it holds; 0 if seen. */
static int64_t pinned_of(const struct node *n) {
    if (n == NULL || (n->o.flags & OBJ_MARK) != 0) {
        return 0;
    }
    int64_t b = obj_bytes(&n->o) + (int64_t) sizeof(struct handle);
    const int32_t count = obj_held_count(&n->o);
    for (int32_t i = 0; i < count; i++) {
        const struct obj *p = obj_held(&n->o, i);
        if (p != NULL) {
            b += obj_bytes(p);
        }
    }
    return b;
}

int64_t ev_pinned_bytes(const struct ev_env *env) {
    int64_t b = nt_bytes(env->nt);
    struct node *roots[2] = { env->super_root == NULL ? NULL : &env->super_root->n,
            env->newest_written_top == NULL ? NULL : &env->newest_written_top->n };
    /* Each object once: marked (OBJ_MARK, which only the recount's and the
     * close's walks use, never across a call) and then unmarked. */
    for (int pass = 0; pass < 2; pass++) {
        for (int r = 0; r < 2; r++) {
            if (roots[r] != NULL) {
                if (pass == 0) {
                    b += pinned_of(roots[r]);
                    roots[r]->o.flags |= OBJ_MARK;
                } else {
                    roots[r]->o.flags &= (uint16_t) ~OBJ_MARK;
                }
            }
        }
        for (const struct ts_info *x = env->d->first; x != NULL; x = x->next) {
            for (int32_t i = 0; i < x->ndirty; i++) {
                struct node *n = x->gotDirtyNodes[i].node;
                if (pass == 0) {
                    b += pinned_of(n);
                    n->o.flags |= OBJ_MARK;
                } else {
                    n->o.flags &= (uint16_t) ~OBJ_MARK;
                }
            }
        }
    }
    return b;
}

/* One pinned object: the object of its node's live handle. */
static int64_t check_pin(const struct ntable *nt, const struct node *o) {
    if (o == NULL) {
        return 0;
    }
    const struct handle *h = nt_live_handle(nt, o->id);
    return h != NULL && h->obj == o ? 0 : 1;
}

int64_t ev_check_pins(const struct ev_env *env) {
    int64_t bad = check_pin(env->nt, env->super_root == NULL ? NULL : &env->super_root->n);
    bad += check_pin(env->nt, env->newest_written_top == NULL ? NULL
            : &env->newest_written_top->n);
    for (const struct ts_info *x = env->d->first; x != NULL; x = x->next) {
        for (int32_t i = 0; i < x->ndirty; i++) {
            const struct node *n = x->gotDirtyNodes[i].node;
            bad += check_pin(env->nt, n);
            if (!node_is_canonical(n) || !node_is_dirty(n)) {
                bad++;
            }
        }
    }
    return bad;
}
