/* Unit tests of obj and handle (bergdb 012-07, sections 6.3 and 6.4): the
 * counts, the pending list and safe points, the recount, close's walk, the
 * handle's states and the record rule, and allocation failures in turn. */
#include "handle.h"
#include "klong.h"
#include "knode.h"
#include "nfix.h"
#include "obj.h"
#include "spos.h"
#include "test.h"
#include "tnode.h"
#include "topds.h"
#include "opdata.h"
#include "vnode.h"

static int64_t live_objects(const struct nfix *f) {
    return f->cx.live[OBJ_KEY] + f->cx.live[OBJ_TOP] + f->cx.live[OBJ_VALUE]
            + f->cx.live[OBJ_HANDLE];
}

/* An object made without a holder is pending, and a safe point frees it. */
TEST(obj_made_pending_and_collected) {
    struct nfix f;
    nfix_init(&f);
    struct knode *k = kn_new(&f.cx, true);
    REQUIRE(k != NULL);
    CHECK((k->n.o.flags & OBJ_PENDING) != 0);
    CHECK_EQ(k->n.o.refs, 0);
    CHECK_EQ(live_objects(&f), 1);
    obj_collect(&f.cx);
    CHECK_EQ(live_objects(&f), 0);
    CHECK_MEM_ZERO(&f.m);
}

/* A held object survives a safe point, with what it holds; when its holder
 * lets go, the next safe point frees it and what only it held. */
TEST(obj_held_survives) {
    struct nfix f;
    nfix_init(&f);
    struct knode *k = kn_new(&f.cx, true);
    struct vnode *v = vn_new(&f.cx, (const uint8_t *) "abc", 3, 40);
    CHECK(kn_add_klong(&f.cx, k, 10, nfix_key("a"), &v->n, ACCESS_DATA_DEFAULT));
    CHECK_EQ(v->n.o.refs, 1);
    struct obj *root = &k->n.o;
    obj_retain(root);           /* a test's field holds k */
    NFIX_RECOUNT(&f, &root, 1);
    obj_collect(&f.cx);
    CHECK_EQ(live_objects(&f), 2);
    CHECK((k->n.o.flags & OBJ_PENDING) == 0);
    CHECK((v->n.o.flags & OBJ_PENDING) == 0);
    NFIX_RECOUNT(&f, &root, 1);

    obj_release(&f.cx, root);   /* the field lets go */
    CHECK((k->n.o.flags & OBJ_PENDING) != 0);
    CHECK_EQ(live_objects(&f), 2);  /* nothing freed before a safe point */
    obj_collect(&f.cx);
    CHECK_EQ(live_objects(&f), 0);
    CHECK_MEM_ZERO(&f.m);
}

/* A value shared by two nodes (as a replacement shares it with the node it
 * replaces) stays until both let go. */
TEST(obj_shared_value) {
    struct nfix f;
    nfix_init(&f);
    struct knode *a = kn_new(&f.cx, true);
    struct vnode *v = vn_new(&f.cx, (const uint8_t *) "x", 1, 40);
    CHECK(kn_add_klong(&f.cx, a, 10, nfix_key("a"), &v->n, ACCESS_DATA_DEFAULT));
    struct knode *last = kn_last_version(&f.cx, a, 20);
    REQUIRE(last != NULL);
    CHECK_EQ(v->n.o.refs, 2);
    struct obj *roots[1] = {&last->n.o};
    obj_retain(roots[0]);
    NFIX_RECOUNT(&f, roots, 1);
    obj_collect(&f.cx);         /* a goes, v stays with last */
    CHECK_EQ(f.cx.live[OBJ_KEY], 1);
    CHECK_EQ(v->n.o.refs, 1);
    NFIX_RECOUNT(&f, roots, 1);
    obj_release(&f.cx, roots[0]);
    NFIX_END(&f);
}

/* The recount finds a count that is wrong, and leaves the counts and the
 * pending list as they were. */
TEST(obj_recount_finds_wrong_count) {
    struct nfix f;
    nfix_init(&f);
    struct knode *k = kn_new(&f.cx, true);
    struct vnode *v = vn_new(&f.cx, NULL, 0, 40);
    CHECK(kn_add_klong(&f.cx, k, 10, nfix_key("a"), &v->n, ACCESS_DATA_DEFAULT));
    int64_t reached = 0;
    CHECK_EQ(obj_recount(&f.cx, NULL, 0, &reached), 0);
    CHECK_EQ(reached, 2);
    v->n.o.refs++;              /* a count too high */
    CHECK_EQ(obj_recount(&f.cx, NULL, 0, NULL), 1);
    CHECK_EQ(v->n.o.refs, 2);   /* as it was */
    v->n.o.refs -= 2;           /* a count too low */
    CHECK_EQ(obj_recount(&f.cx, NULL, 0, NULL), 1);
    v->n.o.refs = 1;
    CHECK_EQ(obj_recount(&f.cx, NULL, 0, NULL), 0);
    CHECK((k->n.o.flags & OBJ_PENDING) != 0);
    CHECK((v->n.o.flags & OBJ_PENDING) != 0);
    NFIX_END(&f);
}

/* Close's walk frees everything reachable from the roots and the pending
 * list, also when the counts are wrong. */
TEST(obj_free_all) {
    struct nfix f;
    nfix_init(&f);
    struct knode *k = kn_new(&f.cx, true);
    struct knode *child = kn_new(&f.cx, true);
    struct vnode *v = vn_new(&f.cx, NULL, 3 - 3, 40);
    CHECK(kn_add_klong(&f.cx, k, 10, nfix_key("a"), &child->n, ACCESS_DATA_DEFAULT));
    CHECK(kn_add_klong(&f.cx, child, 10, nfix_key("b"), &v->n, ACCESS_DATA_DEFAULT));
    struct obj *root = &k->n.o;
    obj_retain(root);
    obj_collect(&f.cx);         /* nothing pending now */
    CHECK_EQ(live_objects(&f), 4);     /* k, child, child's handle, v */
    v->n.o.refs += 5;           /* wrong counts do not matter */
    CHECK_EQ(obj_free_all(&f.cx, &root, 1), 4);
    CHECK_EQ(live_objects(&f), 0);
    CHECK_MEM_ZERO(&f.m);
}

/* Handle.of makes a handle that holds the object, once; the record rule
 * gives the canonical object's position, a written position of a dead
 * handle, or the reference. */
TEST(obj_handle_of_and_record_rule) {
    struct nfix f;
    nfix_init(&f);
    struct knode *child = kn_new(&f.cx, true);
    child->n.id = 9;
    child->n.spos = 9;          /* a vpos: not written */
    struct handle *h = hd_of(&f.cx, &child->n);
    REQUIRE(h != NULL);
    CHECK(hd_of(&f.cx, &child->n) == h);
    CHECK(child->handle == h);
    CHECK(h->obj == &child->n);
    CHECK_EQ(h->id, 9);
    CHECK_EQ(child->n.o.refs, 1);

    /* Not canonical: the reference, unless the written position is newer. */
    CHECK_EQ(hd_serialized_ref(&h->o, 9), 9);
    node_set_canonical(&child->n, true);
    child->n.spos = 1000;
    CHECK_EQ(hd_serialized_ref(&h->o, 9), 1000);     /* the canonical object's position */

    /* Killed: the written position kept, the object let go. */
    obj_retain(&h->o);          /* a pointer holds the handle */
    hd_kill(&f.cx, h);
    CHECK(hd_is_dead(h));
    CHECK(h->obj == NULL);
    CHECK_EQ(h->written_pos, 1000);
    CHECK(child->handle == NULL);
    CHECK((child->n.o.flags & OBJ_LEFT) != 0);
    CHECK(!node_is_canonical(&child->n));
    CHECK_EQ(hd_serialized_ref(&h->o, 9), 1000);     /* a vpos reference: the written position */
    CHECK_EQ(hd_serialized_ref(&h->o, 800), 1000);   /* an older position */
    CHECK_EQ(hd_serialized_ref(&h->o, 1200), 1200);  /* a newer one */
    CHECK_EQ(hd_serialized_ref(NULL, 77), 77);

    obj_collect(&f.cx);         /* the child goes, the dead handle stays (held) */
    CHECK_EQ(f.cx.live[OBJ_KEY], 0);
    CHECK_EQ(f.cx.live[OBJ_HANDLE], 1);
    obj_release(&f.cx, &h->o);
    NFIX_END(&f);
}

/* Handle.usable: a canonical object serves every reference; a version a
 * position at or before its own; never a vpos. */
TEST(obj_handle_usable) {
    struct nfix f;
    nfix_init(&f);
    struct knode *k = kn_new(&f.cx, true);
    k->n.spos = 500;
    CHECK(hd_usable(&k->n, 400));
    CHECK(hd_usable(&k->n, 500));
    CHECK(!hd_usable(&k->n, 600));
    CHECK(!hd_usable(&k->n, 401));      /* a vpos */
    node_set_canonical(&k->n, true);
    CHECK(hd_usable(&k->n, 600));
    CHECK(hd_usable(&k->n, 401));
    NFIX_END(&f);
}

/* hd_set_obj: a handle's object replaced (Cache3's install or
 * makeCanonical): the old one let go, its back reference cleared. */
TEST(obj_handle_set_obj) {
    struct nfix f;
    nfix_init(&f);
    struct handle *h = hd_new(&f.cx, 5);
    struct knode *v1 = kn_new(&f.cx, true);
    struct knode *v2 = kn_new(&f.cx, true);
    v1->n.id = v2->n.id = 5;
    v1->n.spos = 100;
    v2->n.spos = 200;
    struct obj *root = &h->o;
    obj_retain(root);           /* the node table holds h */
    hd_set_obj(&f.cx, h, &v1->n);
    CHECK(v1->handle == h);
    CHECK_EQ(v1->n.o.refs, 1);
    hd_set_obj(&f.cx, h, &v2->n);
    CHECK(v1->handle == NULL);
    CHECK((v1->n.o.flags & OBJ_LEFT) != 0);
    CHECK(v2->handle == h);
    CHECK_EQ(v1->n.o.refs, 0);
    NFIX_RECOUNT(&f, &root, 1);
    obj_collect(&f.cx);
    CHECK_EQ(f.cx.live[OBJ_KEY], 1);    /* v1 freed, v2 in h */
    obj_release(&f.cx, root);
    NFIX_END(&f);
}

/* A pointer to a node replaced by a dead handle's live successor
 * (setPointee), and swizzle's test of what the pointer held. */
TEST(obj_set_pointee_and_swizzle) {
    struct nfix f;
    nfix_init(&f);
    struct knode *parent = kn_new(&f.cx, true);
    struct knode *child = kn_new(&f.cx, true);
    child->n.id = 7;
    child->n.spos = 7;
    CHECK(kn_add_klong(&f.cx, parent, 10, nfix_key("a"), &child->n, ACCESS_DATA_DEFAULT));
    struct handle *dead = child->handle;
    hd_kill(&f.cx, dead);
    struct handle *live = hd_new(&f.cx, 7);
    hd_set_obj(&f.cx, live, &child->n);
    CHECK(!kn_swizzle(&f.cx, parent, 1, &live->o, &live->o));   /* holds dead, not live */
    CHECK(kn_swizzle(&f.cx, parent, 1, &dead->o, &live->o));
    CHECK(kn_get_pointee(parent, 1) == &live->o);
    CHECK_EQ(dead->o.refs, 0);
    CHECK_EQ(live->o.refs, 1);
    NFIX_RECOUNT(&f, NULL, 0);
    NFIX_END(&f);
}

/* toPreviousState releases what the dropped slots held (012-07, 6.5). */
TEST(obj_to_previous_state_releases) {
    struct nfix f;
    nfix_init(&f);
    struct knode *k = kn_new(&f.cx, true);
    struct vnode *a = nfix_value(&f);
    struct vnode *b = nfix_value(&f);
    CHECK(kn_add_klong(&f.cx, k, 10, nfix_key("a"), &a->n, ACCESS_DATA_DEFAULT));
    CHECK(kn_add_klong(&f.cx, k, 20, nfix_key("b"), &b->n, ACCESS_DATA_DEFAULT));
    CHECK_EQ(b->n.o.refs, 1);
    kn_to_previous_state(&f.cx, k, 15);
    CHECK_EQ(k->size, 2);
    CHECK_EQ(b->n.o.refs, 0);
    CHECK(k->pointers[3] == NULL);
    CHECK_EQ(k->last_time_index, -1);
    NFIX_RECOUNT(&f, NULL, 0);
    NFIX_END(&f);
}

/* setContentFrom: the node's pointers become the other's; the old ones
 * released. */
TEST(obj_set_content_from) {
    struct nfix f;
    nfix_init(&f);
    struct knode *k = kn_new(&f.cx, true);
    struct vnode *a = nfix_value(&f);
    struct vnode *b = nfix_value(&f);
    CHECK(kn_add_klong(&f.cx, k, 10, nfix_key("a"), &a->n, ACCESS_DATA_DEFAULT));
    struct knode *other = kn_new_with_time(&f.cx, 30);
    CHECK(kn_add_klong(&f.cx, other, 30, nfix_key("b"), &b->n, ACCESS_DATA_DEFAULT));
    CHECK(kn_set_content_from(&f.cx, k, other));
    CHECK_EQ(k->size, 2);
    CHECK_EQ(k->klongs[1], nfix_key("b"));
    CHECK_EQ(a->n.o.refs, 0);
    CHECK_EQ(b->n.o.refs, 2);
    CHECK_EQ(k->last_time_index, 0);
    NFIX_RECOUNT(&f, NULL, 0);
    NFIX_END(&f);
}

/* A small workload of the node functions that allocate, as the
 * allocation-failure runs make each allocation fail in turn: every run
 * either completes or gets a failure (false or NULL) from one of them, and
 * a safe point then frees everything (012-01, 4.5, point 7). */
static bool workload(struct obj_ctx *cx) {
    struct knode *k = kn_new(cx, true);
    if (k == NULL) {
        return false;
    }
    for (int i = 0; i < 20; i++) {
        uint8_t key[2] = {(uint8_t) ('a' + i % 13), (uint8_t) ('0' + i)};
        struct vnode *v = vn_new(cx, key, 2, SPOS_NULL);
        if (v == NULL || !kn_add_klong(cx, k, 10 + i / 3, kl_create_key(key, 2), &v->n,
                ACCESS_DATA_DEFAULT)) {
            return false;
        }
    }
    struct knode *child = kn_new(cx, false);
    if (child == NULL || !kn_add_klong(cx, k, 20, nfix_key("z"), &child->n, ACCESS_DATA_DEFAULT)) {
        return false;
    }
    int64_t del = kn_get_delete_bitmap(k, nfix_cv("c2"));
    if (!kn_add_delete_klong(cx, k, 21, del)) {
        return false;
    }
    struct knode *last = kn_last_version(cx, k, 30);
    struct knode *half1 = kn_new(cx, true);
    struct knode *second = kn_new(cx, true);
    if (last == NULL || half1 == NULL || second == NULL) {
        return false;
    }
    struct kwp insert[1];
    kwp_init(&insert[0]);
    insert[0].klong = nfix_key("zz");
    insert[0].node = &child->n;
    int64_t secondKlong;
    if (!kn_first_and_second(cx, k, 30, last, insert, 1, half1, second, &secondKlong)) {
        return false;
    }
    if (!kn_set_content_from(cx, k, half1)) {
        return false;
    }
    struct tnode *t = tn_new(cx, 5, k, 0, 30, SPOS_NULL);
    if (t == NULL) {
        return false;
    }
    /* A chain of top nodes, with the same-time case and a skip pointer to
     * the super root; the field that holds the super root released at the
     * end, as the test holds it only in the call. */
    struct topds ds;
    struct knode *first = kn_new_with_time(cx, 40);
    if (first == NULL || !tds_create_from_first_root(cx, &ds, 40, first, 0,
            &OP_DO_NOTHING_POINTER_CREATED_LISTENER)) {
        return false;
    }
    bool ok = true;
    for (int i = 0; ok && i < 6; i++) {
        struct knode *root = kn_new(cx, false);
        ok = root != NULL && tds_new_super_root(cx, &ds, 41 + i / 2, root, 0,
                &OP_DO_NOTHING_POINTER_CREATED_LISTENER, &OP_DO_NOTHING_NODE_CHANGE_LISTENER);
    }
    tds_free(cx, &ds);
    return ok;
}

TEST(obj_allocation_failures) {
    struct nfix f;
    nfix_init(&f);
    int64_t runs = 0;
    for (int64_t n = 1; ; n++) {
        nfix_init(&f);
        f.m.fail_at = n;
        bool ok = workload(&f.cx);
        int64_t allocs = f.m.allocs;
        NFIX_RECOUNT(&f, NULL, 0);
        obj_collect(&f.cx);
        CHECK_EQ(live_objects(&f), 0);
        CHECK_MEM_ZERO(&f.m);
        runs++;
        if (allocs < n) {
            CHECK(ok);          /* no allocation failed: the workload completed */
            break;
        }
        CHECK(!ok);
    }
    CHECK(runs > 20);
}

const struct test obj_tests[] = {
    TEST_ENTRY(obj_made_pending_and_collected),
    TEST_ENTRY(obj_held_survives),
    TEST_ENTRY(obj_shared_value),
    TEST_ENTRY(obj_recount_finds_wrong_count),
    TEST_ENTRY(obj_free_all),
    TEST_ENTRY(obj_handle_of_and_record_rule),
    TEST_ENTRY(obj_handle_usable),
    TEST_ENTRY(obj_handle_set_obj),
    TEST_ENTRY(obj_set_pointee_and_swizzle),
    TEST_ENTRY(obj_to_previous_state_releases),
    TEST_ENTRY(obj_set_content_from),
    TEST_ENTRY(obj_allocation_failures),
    TEST_END
};
