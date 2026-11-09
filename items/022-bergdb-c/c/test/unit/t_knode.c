/* Unit tests of knode: Java's KeyNodeTester, ported test by test (bergdb
 * 012-07), with the counts checked at each test's end (nfix.h). */
#include "bytes.h"
#include "knode.h"
#include "klong.h"
#include "nfix.h"
#include "spos.h"
#include "test.h"
#include "vnode.h"

/* KeyNodeTester.createT2: keys ap, apa, d, g, kr, kram, mage, md at time
 * 1, each with a pointer to a key node of its own (t2Pointers). */
struct t2 {
    struct knode *node;
    struct knode *pointers[8];
};

static void create_t2(struct nfix *f, struct t2 *t) {
    static const char *const keys[] = {"ap", "apa", "d", "g", "kr", "kram", "mage", "md"};
    for (int i = 0; i < 8; i++) {
        t->pointers[i] = kn_new(&f->cx, true);
    }
    t->node = kn_new(&f->cx, true);
    for (int i = 0; i < 8; i++) {
        bool ok = kn_add_klong(&f->cx, t->node, 1, nfix_key(keys[i]), &t->pointers[i]->n,
                ACCESS_DATA_DEFAULT);
        CHECK(ok);
    }
}

/* KeyNodeTester.addKlong: a key with a new empty value. */
static void add_klong(struct nfix *f, struct knode *node, int64_t time, const char *s) {
    struct vnode *value = nfix_value(f);
    CHECK(kn_add_klong(&f->cx, node, time, nfix_key(s), &value->n, ACCESS_DATA_DEFAULT));
}

static bool exists(const struct knode *node, const char *s) {
    struct kwp kwi;
    kwp_init(&kwi);
    kn_search_eq(node, 999, nfix_cv(s), &kwi);
    return kwi.klong != KL_NULL;
}

static struct node *as_node(struct knode *k) {
    return &k->n;
}

TEST(knode_sanity1) {
    struct nfix f;
    nfix_init(&f);
    struct t2 t;
    create_t2(&f, &t);
    NFIX_END(&f);
}

TEST(knode_sanity2) {
    struct nfix f;
    nfix_init(&f);
    struct t2 t;
    create_t2(&f, &t);
    struct kwp kwi;
    kwp_init(&kwi);
    kn_search_eq(t.node, 2000, nfix_cv("ap"), &kwi);
    CHECK(kn_get_pointer_node(t.node, kwi.pointer_index) != NULL);
    CHECK(kn_get_pointer_node(t.node, kwi.pointer_index) == as_node(t.pointers[0]));
    NFIX_END(&f);
}

TEST(knode_eq) {
    struct nfix f;
    nfix_init(&f);
    struct t2 t;
    create_t2(&f, &t);
    struct kwp kwi;
    kwp_init(&kwi);

    kn_search_eq(t.node, 2000, nfix_cv("ap"), &kwi);
    CHECK(kn_get_pointer_node(t.node, kwi.pointer_index) == as_node(t.pointers[0]));
    kn_search_eq(t.node, 2000, nfix_cv("apa"), &kwi);
    CHECK(kn_get_pointer_node(t.node, kwi.pointer_index) != NULL);
    CHECK(kn_get_pointer_node(t.node, kwi.pointer_index) == as_node(t.pointers[1]));
    kn_search_eq(t.node, 2000, nfix_cv("g"), &kwi);
    CHECK(kn_get_pointer_node(t.node, kwi.pointer_index) == as_node(t.pointers[3]));
    kn_search_eq(t.node, 2000, nfix_cv("mage"), &kwi);
    CHECK(kn_get_pointer_node(t.node, kwi.pointer_index) == as_node(t.pointers[6]));
    kn_search_eq(t.node, 2000, nfix_cv("md"), &kwi);
    CHECK(kn_get_pointer_node(t.node, kwi.pointer_index) == as_node(t.pointers[7]));
    NFIX_END(&f);
}

TEST(knode_eq_with_versions) {
    struct nfix f;
    nfix_init(&f);
    struct t2 t;
    create_t2(&f, &t);
    struct kwp kwi;
    kwp_init(&kwi);

    CHECK(kn_add_klong(&f.cx, t.node, 1020, nfix_key("a"), as_node(t.pointers[7]),
            ACCESS_DATA_DEFAULT));
    kn_search_eq(t.node, 2000, nfix_cv("a"), &kwi);
    CHECK(kwi.node == as_node(t.pointers[7]));
    kn_search_eq(t.node, 2000, nfix_cv("mage"), &kwi);
    CHECK(kwi.node == as_node(t.pointers[6]));
    NFIX_END(&f);
}

TEST(knode_eq_with_versions_and_delete) {
    struct nfix f;
    nfix_init(&f);
    struct t2 t;
    create_t2(&f, &t);
    struct kwp kwi;
    kwp_init(&kwi);
    struct knode *node = t.node;

    int64_t klong = kn_get_delete_bitmap(node, nfix_cv("apa"));
    CHECK(kn_add_klong(&f.cx, node, 1020, klong, NULL, ACCESS_DATA_DEFAULT));

    kn_search_eq(node, 2000, nfix_cv("apa"), &kwi);
    CHECK_EQ(kwi.klong, KL_NULL);

    kn_search_eq(node, 1010, nfix_cv("apa"), &kwi);
    CHECK(kwi.node == as_node(t.pointers[1]));

    CHECK(kn_add_klong(&f.cx, node, 1030, nfix_key("apa"), as_node(t.pointers[5]),
            ACCESS_DATA_DEFAULT));
    kn_search_eq(node, 2000, nfix_cv("apa"), &kwi);
    CHECK(kwi.node == as_node(t.pointers[5]));
    NFIX_END(&f);
}

TEST(knode_eq_before_first_version) {
    struct nfix f;
    nfix_init(&f);
    struct knode *n = kn_new(&f.cx, true);
    CHECK(kn_add_klong(&f.cx, n, 10, nfix_key("first"), &nfix_value(&f)->n, ACCESS_DATA_DEFAULT));
    CHECK(kn_check(n, NULL) == NULL);
    struct kwp kwi;
    kwp_init(&kwi);
    kn_search_eq(n, 20, nfix_cv("first"), &kwi);
    CHECK(kwi.klong != KL_NULL);
    kn_search_eq(n, 5, nfix_cv("first"), &kwi);
    CHECK(kwi.klong == KL_NULL);
    NFIX_END(&f);
}

/* k10 at 10 and k20 at 20, with values; with a delete of k10 at 30 if
 * del. */
static struct knode *k10_k20(struct nfix *f, bool del) {
    struct knode *n = kn_new(&f->cx, true);
    CHECK(kn_add_klong(&f->cx, n, 10, nfix_key("k10"), &nfix_value(f)->n, ACCESS_DATA_DEFAULT));
    CHECK(kn_add_klong(&f->cx, n, 20, nfix_key("k20"), &nfix_value(f)->n, ACCESS_DATA_DEFAULT));
    if (del) {
        int64_t klongToAdd = kn_get_delete_bitmap(n, nfix_cv("k10"));
        CHECK(kn_add_klong(&f->cx, n, 30, klongToAdd, NULL, ACCESS_DATA_DEFAULT));
    }
    return n;
}

TEST(knode_lte1) {
    struct nfix f;
    nfix_init(&f);
    struct knode *n = kn_new(&f.cx, true);
    CHECK(kn_add_klong(&f.cx, n, 10, nfix_key("first"), &nfix_value(&f)->n, ACCESS_DATA_DEFAULT));
    CHECK(kn_check(n, NULL) == NULL);
    struct kwp kwi;
    kn_search_lte(n, 20, nfix_cv("first"), &kwi);
    CHECK(kwi.klong != KL_NULL);
    kn_search_lte(n, 5, nfix_cv("first"), &kwi);
    CHECK(kwi.klong == KL_NULL);
    kn_search_lte(n, 20, nfix_cv("fir"), &kwi);
    CHECK(kwi.klong == KL_NULL);
    kn_search_lte(n, 20, nfix_cv("g"), &kwi);
    CHECK(kwi.klong != KL_NULL);
    NFIX_END(&f);
}

TEST(knode_lte2) {
    struct nfix f;
    nfix_init(&f);
    struct knode *n = k10_k20(&f, false);
    struct kwp kwi;

    kn_search_lte(n, INT64_MAX, nfix_cv("k20"), &kwi);
    CHECK_EQ(kwi.klong, nfix_key("k20"));
    kn_search_lte(n, INT64_MAX, nfix_cv("k21"), &kwi);
    CHECK_EQ(kwi.klong, nfix_key("k20"));
    kn_search_lte(n, INT64_MAX, nfix_cv("k19"), &kwi);
    CHECK_EQ(kwi.klong, nfix_key("k10"));
    kn_search_lte(n, INT64_MAX, nfix_cv("k09"), &kwi);
    CHECK_EQ(kwi.klong, KL_NULL);

    kn_search_lte(n, 15, nfix_cv("k99"), &kwi);
    CHECK_EQ(kwi.klong, nfix_key("k10"));
    kn_search_lte(n, 15, nfix_cv("k10"), &kwi);
    CHECK_EQ(kwi.klong, nfix_key("k10"));
    kn_search_lte(n, 15, nfix_cv("k09"), &kwi);
    CHECK_EQ(kwi.klong, KL_NULL);
    NFIX_END(&f);
}

TEST(knode_lte3) {
    struct nfix f;
    nfix_init(&f);
    struct knode *n = k10_k20(&f, true);
    struct kwp kwi;

    kn_search_lte(n, INT64_MAX, nfix_cv("k20"), &kwi);
    CHECK_EQ(kwi.klong, nfix_key("k20"));
    kn_search_lte(n, INT64_MAX, nfix_cv("k21"), &kwi);
    CHECK_EQ(kwi.klong, nfix_key("k20"));
    kn_search_lte(n, INT64_MAX, nfix_cv("k19"), &kwi);
    CHECK_EQ(kwi.klong, KL_NULL);
    kn_search_lte(n, INT64_MAX, nfix_cv("k09"), &kwi);
    CHECK_EQ(kwi.klong, KL_NULL);
    NFIX_END(&f);
}

TEST(knode_lt1) {
    struct nfix f;
    nfix_init(&f);
    struct knode *n = kn_new(&f.cx, true);
    CHECK(kn_add_klong(&f.cx, n, 10, nfix_key("first"), &nfix_value(&f)->n, ACCESS_DATA_DEFAULT));
    CHECK(kn_check(n, NULL) == NULL);
    struct kwp kwi;
    kn_search_lt(n, 20, nfix_cv("first"), &kwi);
    CHECK(kwi.klong == KL_NULL);
    kn_search_lt(n, 5, nfix_cv("first"), &kwi);
    CHECK(kwi.klong == KL_NULL);
    kn_search_lt(n, 20, nfix_cv("fir"), &kwi);
    CHECK(kwi.klong == KL_NULL);
    kn_search_lt(n, 20, nfix_cv("g"), &kwi);
    CHECK(kwi.klong != KL_NULL);
    NFIX_END(&f);
}

TEST(knode_lt2) {
    struct nfix f;
    nfix_init(&f);
    struct knode *n = k10_k20(&f, false);
    struct kwp kwi;

    kn_search_lt(n, INT64_MAX, nfix_cv("k20"), &kwi);
    CHECK_EQ(kwi.klong, nfix_key("k10"));
    kn_search_lt(n, INT64_MAX, nfix_cv("k21"), &kwi);
    CHECK_EQ(kwi.klong, nfix_key("k20"));
    kn_search_lt(n, INT64_MAX, nfix_cv("k19"), &kwi);
    CHECK_EQ(kwi.klong, nfix_key("k10"));
    kn_search_lt(n, INT64_MAX, nfix_cv("k09"), &kwi);
    CHECK_EQ(kwi.klong, KL_NULL);

    kn_search_lt(n, 15, nfix_cv("k99"), &kwi);
    CHECK_EQ(kwi.klong, nfix_key("k10"));
    kn_search_lt(n, 15, nfix_cv("k10"), &kwi);
    CHECK_EQ(kwi.klong, KL_NULL);
    kn_search_lt(n, 15, nfix_cv("k09"), &kwi);
    CHECK_EQ(kwi.klong, KL_NULL);
    NFIX_END(&f);
}

TEST(knode_lt3) {
    struct nfix f;
    nfix_init(&f);
    struct knode *n = k10_k20(&f, true);
    struct kwp kwi;

    kn_search_lt(n, INT64_MAX, nfix_cv("k20"), &kwi);
    CHECK_EQ(kwi.klong, KL_NULL);
    kn_search_lt(n, INT64_MAX, nfix_cv("k21"), &kwi);
    CHECK_EQ(kwi.klong, nfix_key("k20"));
    kn_search_lt(n, INT64_MAX, nfix_cv("k19"), &kwi);
    CHECK_EQ(kwi.klong, KL_NULL);
    NFIX_END(&f);
}

TEST(knode_gt1) {
    struct nfix f;
    nfix_init(&f);
    struct knode *n = kn_new(&f.cx, true);
    CHECK(kn_add_klong(&f.cx, n, 10, nfix_key("key"), &nfix_value(&f)->n, ACCESS_DATA_DEFAULT));
    CHECK(kn_check(n, NULL) == NULL);
    struct kwp kwi;
    kn_search_gt(n, 20, nfix_cv("a"), &kwi);
    CHECK(kwi.klong != KL_NULL);
    kn_search_gt(n, 5, nfix_cv("a"), &kwi);
    CHECK(kwi.klong == KL_NULL);
    kn_search_gt(n, 20, nfix_cv("key"), &kwi);
    CHECK(kwi.klong == KL_NULL);
    NFIX_END(&f);
}

TEST(knode_gt2) {
    struct nfix f;
    nfix_init(&f);
    struct knode *n = k10_k20(&f, false);
    struct kwp kwi;

    kn_search_gt(n, INT64_MAX, nfix_cv("k19"), &kwi);
    CHECK_EQ(kwi.klong, nfix_key("k20"));
    kn_search_gt(n, INT64_MAX, nfix_cv("k10"), &kwi);
    CHECK_EQ(kwi.klong, nfix_key("k20"));
    kn_search_gt(n, INT64_MAX, nfix_cv("k20"), &kwi);
    CHECK_EQ(kwi.klong, KL_NULL);
    kn_search_gt(n, INT64_MAX, nfix_cv("k00"), &kwi);
    CHECK_EQ(kwi.klong, nfix_key("k10"));

    kn_search_gt(n, 15, nfix_cv("k15"), &kwi);
    CHECK_EQ(kwi.klong, KL_NULL);
    kn_search_gt(n, 15, nfix_cv("k10"), &kwi);
    CHECK_EQ(kwi.klong, KL_NULL);
    kn_search_gt(n, 15, nfix_cv("k09"), &kwi);
    CHECK_EQ(kwi.klong, nfix_key("k10"));
    NFIX_END(&f);
}

TEST(knode_gte) {
    struct nfix f;
    nfix_init(&f);
    struct knode *n = k10_k20(&f, false);
    struct kwp kwi;

    kn_search_gte(n, INT64_MAX, nfix_cv("k19"), &kwi);
    CHECK_EQ(kwi.klong, nfix_key("k20"));
    kn_search_gte(n, INT64_MAX, nfix_cv("k10"), &kwi);
    CHECK_EQ(kwi.klong, nfix_key("k10"));
    kn_search_gte(n, INT64_MAX, nfix_cv("k20"), &kwi);
    CHECK_EQ(kwi.klong, nfix_key("k20"));
    kn_search_gte(n, INT64_MAX, nfix_cv("k00"), &kwi);
    CHECK_EQ(kwi.klong, nfix_key("k10"));

    kn_search_gte(n, 15, nfix_cv("k15"), &kwi);
    CHECK_EQ(kwi.klong, KL_NULL);
    kn_search_gte(n, 15, nfix_cv("k10"), &kwi);
    CHECK_EQ(kwi.klong, nfix_key("k10"));
    kn_search_gte(n, 15, nfix_cv("k09"), &kwi);
    CHECK_EQ(kwi.klong, nfix_key("k10"));
    NFIX_END(&f);
}

TEST(knode_first1) {
    struct nfix f;
    nfix_init(&f);
    struct t2 t;
    create_t2(&f, &t);
    struct kwp kwi;
    kn_search_first(t.node, 2000, &kwi);
    CHECK(kwi.klong != KL_NULL);
    CHECK(kwi.node == as_node(t.pointers[0]));
    CHECK_EQ(kwi.klong, nfix_key("ap"));
    NFIX_END(&f);
}

TEST(knode_check_empty_node) {
    struct nfix f;
    nfix_init(&f);
    CHECK(kn_check(kn_new(&f.cx, true), NULL) == NULL);
    NFIX_END(&f);
}

TEST(knode_check1) {
    struct nfix f;
    nfix_init(&f);
    struct t2 t;
    create_t2(&f, &t);
    CHECK(kn_check(t.node, NULL) == NULL);
    NFIX_END(&f);
}

TEST(knode_check2) {
    struct nfix f;
    nfix_init(&f);
    struct t2 t;
    create_t2(&f, &t);
    struct knode *node = t.node;
    CHECK(kn_check(node, NULL) == NULL);
    int64_t klong = kn_get_delete_bitmap(node, nfix_cv("apa"));
    CHECK(kn_add_klong(&f.cx, node, 1020, klong, NULL, ACCESS_DATA_DEFAULT));
    CHECK(kn_check(node, NULL) == NULL);
    CHECK(kn_add_klong(&f.cx, node, 1030, nfix_key("apa"), as_node(t.pointers[5]),
            ACCESS_DATA_DEFAULT));
    CHECK(kn_check(node, NULL) == NULL);
    NFIX_END(&f);
}

TEST(knode_get_pointers) {
    struct nfix f;
    nfix_init(&f);
    struct t2 t;
    create_t2(&f, &t);
    int32_t pointerCount = kn_get_size(t.node);
    struct pointer p;
    ptr_reset(&p);
    CHECK_EQ(pointerCount, 9);
    for (int32_t j = 0; j < pointerCount; j++) {
        kn_get_pointer(t.node, j, &p);
        if (ptr_is_null(&p)) {
            continue;
        }
        CHECK(p.node == as_node(t.pointers[j - 1]));
    }
    NFIX_END(&f);
}

/* Java's KeyNode.getInfo, the fields the tests read. */
struct info {
    int32_t klong_count;
    int32_t time_count;
    int64_t last_time;
};

static void get_info(const struct knode *k, struct info *info) {
    info->klong_count = 0;
    info->time_count = 0;
    info->last_time = -1;
    for (int32_t i = 0; i < k->size; i++) {
        info->klong_count++;
        if (kl_get_int_type(k->klongs[i]) == KL_INT_TYPE_TIME) {
            info->time_count++;
            info->last_time = kl_get_time(k->klongs[i]);
        }
    }
}

TEST(knode_last_version1) {
    struct nfix f;
    nfix_init(&f);
    struct knode *n = kn_new(&f.cx, true);
    add_klong(&f, n, 10, "a");
    add_klong(&f, n, 20, "b");
    add_klong(&f, n, 30, "c");

    struct knode *last = kn_last_version(&f.cx, n, 100);
    REQUIRE(last != NULL);
    struct info info;
    get_info(last, &info);
    CHECK_EQ(info.last_time, 100);
    CHECK_EQ(info.klong_count, 4);
    CHECK_EQ(info.time_count, 1);
    NFIX_END(&f);
}

TEST(knode_last_version3) {
    struct nfix f;
    nfix_init(&f);
    struct knode *n = kn_new(&f.cx, true);
    struct vnode *value = nfix_value(&f);

    CHECK(kn_add_klong(&f.cx, n, 10, nfix_key("a"), &value->n, ACCESS_DATA_DEFAULT));
    CHECK(kn_add_klong(&f.cx, n, 20, nfix_key("b"), &value->n, ACCESS_DATA_DEFAULT));
    CHECK(kn_add_klong(&f.cx, n, 25, nfix_key("c"), &value->n, ACCESS_DATA_DEFAULT));
    CHECK(kn_add_klong(&f.cx, n, 30, kn_get_delete_bitmap(n, nfix_cv("b")), NULL,
            ACCESS_DATA_DEFAULT));
    CHECK(kn_add_klong(&f.cx, n, 40, kn_get_delete_bitmap(n, nfix_cv("a")), NULL,
            ACCESS_DATA_DEFAULT));
    CHECK(kn_add_klong(&f.cx, n, 50, nfix_key("b"), &value->n, ACCESS_DATA_DEFAULT));

    struct knode *last = kn_last_version(&f.cx, n, 100);
    REQUIRE(last != NULL);
    struct info info;
    get_info(last, &info);
    CHECK_EQ(info.last_time, 100);
    CHECK_EQ(info.klong_count, 3);
    CHECK_EQ(info.time_count, 1);
    CHECK_EQ(last->klongs[0], kl_create_time(100));
    CHECK_EQ(last->klongs[1], nfix_key("b"));
    CHECK_EQ(last->klongs[2], nfix_key("c"));
    NFIX_RECOUNT(&f, NULL, 0);
    NFIX_END(&f);
}

TEST(knode_last_version4) {
    struct nfix f;
    nfix_init(&f);
    struct knode *n = kn_new(&f.cx, true);
    struct vnode *value = nfix_value(&f);
    CHECK(kn_add_klong(&f.cx, n, 10, nfix_key("a"), &value->n, ACCESS_DATA_DEFAULT));
    CHECK(kn_add_klong(&f.cx, n, 10, nfix_key("b"), &value->n, ACCESS_DATA_DEFAULT));
    CHECK(kn_add_klong(&f.cx, n, 20, nfix_key("c"), &value->n, ACCESS_DATA_DEFAULT));
    CHECK(kn_add_klong(&f.cx, n, 30, kn_get_delete_bitmap(n, nfix_cv("b")), NULL,
            ACCESS_DATA_DEFAULT));
    CHECK(kn_add_klong(&f.cx, n, 40, nfix_key("d"), &value->n, ACCESS_DATA_DEFAULT));
    CHECK(kn_add_klong(&f.cx, n, 50, KL_DELETE_ALL_BITMAP, NULL, ACCESS_DATA_DEFAULT));

    struct knode *last = kn_last_version(&f.cx, n, 100);
    REQUIRE(last != NULL);
    CHECK(last->size <= 1);
    NFIX_END(&f);
}

/* The node of testFirstAndSecond2 to 6: keys at the times given, each with
 * the value v1 ("v1"). */
static struct knode *fas_node(struct nfix *f, struct vnode **v1, const int64_t *times,
        const char *const *keys, int n) {
    struct knode *node = kn_new(&f->cx, true);
    *v1 = vn_new(&f->cx, (const uint8_t *) "v1", 2, SPOS_NULL);
    for (int i = 0; i < n; i++) {
        CHECK(kn_add_klong(&f->cx, node, times[i], nfix_key(keys[i]), &(*v1)->n,
                ACCESS_DATA_DEFAULT));
    }
    return node;
}

/* Splits node at 100 with the inserts (keys, each with v1) into first and
 * second, and checks their klongs. */
static void fas_check(struct nfix *f, struct knode *node, struct vnode *v1,
        const char *const *inserts, int ninserts, const char *const *firstKeys, int nfirst,
        const char *const *secondKeys, int nsecond) {
    struct knode *first = kn_new(&f->cx, true);
    struct knode *second = kn_new(&f->cx, true);
    struct kwp insert[4];
    for (int i = 0; i < ninserts; i++) {
        kwp_init(&insert[i]);
        insert[i].klong = nfix_key(inserts[i]);
        insert[i].node = &v1->n;
    }
    struct knode *last = kn_last_version(&f->cx, node, 100);
    REQUIRE(last != NULL);
    int64_t secondKlong = 0;
    CHECK(kn_first_and_second(&f->cx, node, 100, last, insert, ninserts, first, second,
            &secondKlong));
    CHECK_EQ(secondKlong, nfix_key(secondKeys[0]));

    CHECK_EQ(first->size, nfirst + 1);
    CHECK_EQ(first->klongs[0], kl_create_time(100));
    for (int i = 0; i < nfirst && i + 1 < first->size; i++) {
        CHECK_EQ(first->klongs[i + 1], nfix_key(firstKeys[i]));
    }
    CHECK_EQ(second->size, nsecond + 1);
    CHECK_EQ(second->klongs[0], kl_create_time(100));
    for (int i = 0; i < nsecond && i + 1 < second->size; i++) {
        CHECK_EQ(second->klongs[i + 1], nfix_key(secondKeys[i]));
    }
    NFIX_RECOUNT(f, NULL, 0);
}

TEST(knode_first_and_second2) {
    struct nfix f;
    nfix_init(&f);
    static const int64_t times[] = {10, 20, 30, 40};
    static const char *const keys[] = {"10", "20", "30", "40"};
    struct vnode *v1;
    struct knode *n = fas_node(&f, &v1, times, keys, 4);
    static const char *const ins[] = {"22"};
    static const char *const fk[] = {"10", "20", "22"};
    static const char *const sk[] = {"30", "40"};
    fas_check(&f, n, v1, ins, 1, fk, 3, sk, 2);
    NFIX_END(&f);
}

TEST(knode_first_and_second3) {
    struct nfix f;
    nfix_init(&f);
    static const int64_t times[] = {10, 20, 30, 40};
    static const char *const keys[] = {"10", "20", "30", "40"};
    struct vnode *v1;
    struct knode *n = fas_node(&f, &v1, times, keys, 4);
    static const char *const ins[] = {"01", "22"};
    static const char *const fk[] = {"10", "20", "01", "22"};
    static const char *const sk[] = {"30", "40"};
    fas_check(&f, n, v1, ins, 2, fk, 4, sk, 2);
    NFIX_END(&f);
}

TEST(knode_first_and_second4) {
    struct nfix f;
    nfix_init(&f);
    static const int64_t times[] = {10, 30, 40};
    static const char *const keys[] = {"10", "30", "40"};
    struct vnode *v1;
    struct knode *n = fas_node(&f, &v1, times, keys, 3);
    static const char *const ins[] = {"21", "22", "23"};
    static const char *const fk[] = {"10", "21", "22", "23"};
    static const char *const sk[] = {"30", "40"};
    fas_check(&f, n, v1, ins, 3, fk, 4, sk, 2);
    NFIX_END(&f);
}

TEST(knode_first_and_second5) {
    struct nfix f;
    nfix_init(&f);
    static const int64_t times[] = {10, 10, 30, 40};
    static const char *const keys[] = {"10", "20", "30", "40"};
    struct vnode *v1;
    struct knode *n = fas_node(&f, &v1, times, keys, 4);
    static const char *const ins[] = {"01", "02"};
    static const char *const fk[] = {"10", "20", "01", "02"};
    static const char *const sk[] = {"30", "40"};
    fas_check(&f, n, v1, ins, 2, fk, 4, sk, 2);
    NFIX_END(&f);
}

TEST(knode_first_and_second6) {
    struct nfix f;
    nfix_init(&f);
    static const int64_t times[] = {10, 10, 30, 40};
    static const char *const keys[] = {"10", "20", "30", "40"};
    struct vnode *v1;
    struct knode *n = fas_node(&f, &v1, times, keys, 4);
    static const char *const ins[] = {"41", "42"};
    static const char *const fk[] = {"10", "20"};
    static const char *const sk[] = {"30", "40", "41", "42"};
    fas_check(&f, n, v1, ins, 2, fk, 2, sk, 4);
    NFIX_END(&f);
}

TEST(knode_delete_bitmap1) {
    struct nfix f;
    nfix_init(&f);
    struct knode *node = kn_new(&f.cx, true);
    struct vnode *value = nfix_value(&f);
    CHECK(kn_add_klong(&f.cx, node, 10, nfix_key("a"), &value->n, ACCESS_DATA_DEFAULT));
    CHECK(kn_add_klong(&f.cx, node, 20, nfix_key("c"), &value->n, ACCESS_DATA_DEFAULT));

    CHECK(kn_get_delete_bitmap(node, nfix_cv("a")) != 0);
    CHECK(kn_get_delete_bitmap(node, nfix_cv("b")) == 0);
    CHECK(kn_get_delete_bitmap(node, nfix_cv("c")) != 0);
    CHECK(kn_get_delete_bitmap(node, nfix_cv("d")) == 0);

    CHECK_EQ(kn_get_delete_bitmap(node, nfix_cv("a")), kl_delete(kl_create_delete(), 1));
    CHECK_EQ(kn_get_delete_bitmap(node, nfix_cv("c")), kl_delete(kl_create_delete(), 3));
    NFIX_END(&f);
}

TEST(knode_to_previous_state1) {
    struct nfix f;
    nfix_init(&f);
    struct knode *node = kn_new(&f.cx, true);
    add_klong(&f, node, 10, "a");
    add_klong(&f, node, 20, "b");
    kn_to_previous_state(&f.cx, node, 15);
    CHECK(exists(node, "a"));
    CHECK(!exists(node, "b"));
    NFIX_END(&f);
}

TEST(knode_to_previous_state2) {
    struct nfix f;
    nfix_init(&f);
    struct knode *node = kn_new(&f.cx, true);
    add_klong(&f, node, 10, "a");
    add_klong(&f, node, 20, "b");
    kn_to_previous_state(&f.cx, node, 5);
    CHECK(!exists(node, "a"));
    CHECK(!exists(node, "b"));
    NFIX_END(&f);
}

TEST(knode_to_previous_state3) {
    struct nfix f;
    nfix_init(&f);
    struct knode *node = kn_new(&f.cx, true);
    add_klong(&f, node, 10, "a");
    add_klong(&f, node, 20, "b");
    kn_to_previous_state(&f.cx, node, 40);
    CHECK(exists(node, "a"));
    CHECK(exists(node, "b"));
    NFIX_END(&f);
}

TEST(knode_to_previous_state4) {
    struct nfix f;
    nfix_init(&f);
    struct knode *node = kn_new(&f.cx, true);
    add_klong(&f, node, 10, "a");
    add_klong(&f, node, 20, "b");
    kn_to_previous_state(&f.cx, node, 15);
    add_klong(&f, node, 30, "c");
    CHECK(exists(node, "a"));
    CHECK(!exists(node, "b"));
    CHECK(exists(node, "c"));
    NFIX_END(&f);
}

TEST(knode_new_key_node_with_time) {
    struct nfix f;
    nfix_init(&f);
    struct knode *node = kn_new_with_time(&f.cx, 123);
    REQUIRE(node != NULL);
    CHECK_EQ(node->size, 1);
    CHECK_EQ(kn_get_size(node), 1);
    struct pointer p;
    kn_get_pointer(node, 0, &p);
    CHECK(ptr_is_null(&p));
    int64_t klong = kn_get_klong(node, 0);
    CHECK_EQ(kl_get_type(klong), KL_TYPE_TIME);
    CHECK_EQ(kl_get_time(klong), 123);
    NFIX_END(&f);
}

TEST(knode_get_first_time1) {
    struct nfix f;
    nfix_init(&f);
    CHECK_EQ(kn_get_first_time(kn_new_with_time(&f.cx, 123)), 123);
    NFIX_END(&f);
}

TEST(knode_get_first_time2) {
    struct nfix f;
    nfix_init(&f);
    CHECK_EQ(kn_get_first_time(kn_new(&f.cx, true)), -1);
    NFIX_END(&f);
}

TEST(knode_get_first_time3) {
    struct nfix f;
    nfix_init(&f);
    struct knode *node = kn_new(&f.cx, true);
    add_klong(&f, node, 10, "a");
    add_klong(&f, node, 20, "b");
    CHECK_EQ(kn_get_first_time(node), 10);
    NFIX_END(&f);
}

TEST(knode_get_pointer_count0) {
    struct nfix f;
    nfix_init(&f);
    struct knode *node = kn_new(&f.cx, true);
    add_klong(&f, node, 10, "a");
    CHECK_EQ(kn_get_size(node), 2);
    NFIX_END(&f);
}

TEST(knode_get_pointer_count1) {
    struct nfix f;
    nfix_init(&f);
    struct knode *node = kn_new(&f.cx, true);
    add_klong(&f, node, 10, "a");
    add_klong(&f, node, 10, "b");
    CHECK_EQ(kn_get_size(node), 3);
    NFIX_END(&f);
}

TEST(knode_get_pointer_count2) {
    struct nfix f;
    nfix_init(&f);
    struct knode *node = kn_new(&f.cx, true);
    add_klong(&f, node, 10, "a");
    add_klong(&f, node, 20, "b");
    CHECK_EQ(kn_get_size(node), 4);
    NFIX_END(&f);
}

TEST(knode_get_pointer_count3) {
    struct nfix f;
    nfix_init(&f);
    struct knode *node = kn_new(&f.cx, true);
    add_klong(&f, node, 10, "a");
    add_klong(&f, node, 20, "b");
    CHECK_EQ(kn_get_size_at_time(node, 9), 0);
    CHECK_EQ(kn_get_size_at_time(node, 10), 2);
    CHECK_EQ(kn_get_size_at_time(node, 11), 2);
    CHECK_EQ(kn_get_size_at_time(node, 19), 2);
    CHECK_EQ(kn_get_size_at_time(node, 20), 4);
    CHECK_EQ(kn_get_size_at_time(node, INT64_MAX), 4);
    NFIX_END(&f);
}

TEST(knode_max_valid_time0) {
    struct nfix f;
    nfix_init(&f);
    struct knode *node = kn_new(&f.cx, true);
    add_klong(&f, node, 10, "a");
    CHECK_EQ(kn_get_max_valid_time(node, 1), INT64_MAX);
    NFIX_END(&f);
}

TEST(knode_max_valid_time1) {
    struct nfix f;
    nfix_init(&f);
    struct knode *node = kn_new(&f.cx, true);
    add_klong(&f, node, 10, "a");       /* index 1 */
    add_klong(&f, node, 20, "a");       /* index 3 */
    CHECK_EQ(kn_get_max_valid_time(node, 1), 19);
    CHECK_EQ(kn_get_max_valid_time(node, 3), INT64_MAX);
    NFIX_END(&f);
}

TEST(knode_max_valid_time_with_delete) {
    struct nfix f;
    nfix_init(&f);
    struct knode *node = kn_new(&f.cx, true);
    add_klong(&f, node, 10, "a");       /* index 1 */
    add_klong(&f, node, 20, "b");       /* index 3 */
    int64_t deleteKlong = kn_get_delete_bitmap(node, nfix_cv("a"));
    CHECK(kn_add_klong(&f.cx, node, 30, deleteKlong, NULL, ACCESS_DATA_DEFAULT));
    CHECK_EQ(kn_get_max_valid_time(node, 1), 29);
    CHECK_EQ(kn_get_max_valid_time(node, 3), INT64_MAX);
    NFIX_END(&f);
}

TEST(knode_add_delete_klong) {
    struct nfix f;
    nfix_init(&f);
    struct knode *node = kn_new(&f.cx, true);
    add_klong(&f, node, 10, "a");                               /* index 1 */
    CHECK(kn_add_delete_klong(&f.cx, node, 40, kl_create_delete()));    /* index 3 */
    struct pointer p;
    kn_get_pointer(node, 0, &p);
    CHECK(ptr_is_null(&p));
    kn_get_pointer(node, 1, &p);
    CHECK(!ptr_is_null(&p));
    kn_get_pointer(node, 2, &p);
    CHECK(ptr_is_null(&p));
    kn_get_pointer(node, 3, &p);
    CHECK(ptr_is_null(&p));
    NFIX_END(&f);
}

/* testPrint: Java prints createT2's node; C has no print (knode.h). */

/* searchFirst takes the first of the klongs of the smallest key, not the
 * latest (its test is a strict <, the other searches' <= and >=); no
 * production code calls it: GetMany takes the first key with searchGt(-1),
 * which gives the latest (012-07, section 5). */
TEST(knode_search_first_takes_first) {
    struct nfix f;
    nfix_init(&f);
    struct knode *node = kn_new(&f.cx, true);
    struct vnode *v1 = nfix_value(&f);
    struct vnode *v2 = nfix_value(&f);
    CHECK(kn_add_klong(&f.cx, node, 10, nfix_key("a"), &v1->n, ACCESS_DATA_DEFAULT));
    CHECK(kn_add_klong(&f.cx, node, 20, nfix_key("a"), &v2->n, ACCESS_DATA_DEFAULT));
    struct kwp kwi;
    kn_search_first(node, 30, &kwi);
    CHECK(kwi.node == &v1->n);
    CHECK_EQ(kwi.pointer_index, 1);
    kn_search_gt(node, 30, -1, &kwi);
    CHECK(kwi.node == &v2->n);
    kn_search_eq(node, 30, nfix_cv("a"), &kwi);
    CHECK(kwi.node == &v2->n);
    NFIX_END(&f);
}

/* Pointer.test1 */
TEST(knode_pointer_test1) {
    struct pointer p;
    ptr_reset(&p);
    CHECK(ptr_is_null(&p));
    p.pos = 80;
    p.node = NULL;
    p.index = -1;
    CHECK(!ptr_is_mem(&p));
    CHECK(!ptr_is_null(&p));
    CHECK(p.node == NULL);
    CHECK_EQ(ptr_spos_for_stream(&p), 80);
}

/* A key node made from a stored one (StoredKeyNode.parse): stream
 * pointers, its id and position, the last time index. */
TEST(knode_new_stored) {
    struct nfix f;
    nfix_init(&f);
    uint8_t klongs[24], refs[24];
    bytes_put_long_le(kl_create_time(7), klongs);
    bytes_put_long_le(nfix_key("a"), klongs + 8);
    bytes_put_long_le(nfix_key("b"), klongs + 16);
    bytes_put_long_le(-1, refs);
    bytes_put_long_le(1000, refs + 8);
    bytes_put_long_le(1003, refs + 16);
    struct knode *k = kn_new_stored(&f.cx, false, 2048, 1001, 3, klongs, refs);
    REQUIRE(k != NULL);
    CHECK(!kn_is_segment_leaf(k));
    CHECK_EQ(k->n.id, 1001);
    CHECK_EQ(k->n.spos, 2048);
    CHECK_EQ(k->size, 3);
    CHECK_EQ(k->last_time_index, 0);
    CHECK(kn_get_pointee(k, 1) == NULL);
    CHECK_EQ(kn_get_pointer_pos(k, 2), 1003);
    CHECK_EQ(kn_get_serialized_ref(k, 2), 1003);
    char buf[KN_TEXT];
    CHECK(kn_validate_stream_node(k, 7, buf) == NULL);
    NFIX_END(&f);
}

/* KeyNode.validateStreamNode's text for times that do not increase, Java's
 * with the times and the index (022-01, step 4: the corrupt-stream set
 * found C's "Time not increasing" alone, a node of a record's start whose
 * time klong was changed, its checksum made right); KeyNode.check's too,
 * with a buffer (bergdb 021-15: the start's check and the put's
 * assertOk), and the short one without (the asserts). */
TEST(knode_validate_time_text) {
    struct nfix f;
    nfix_init(&f);
    uint8_t klongs[32], refs[32];
    bytes_put_long_le(kl_create_time(500), klongs);
    bytes_put_long_le(nfix_key("a"), klongs + 8);
    bytes_put_long_le(kl_create_time(500), klongs + 16);
    bytes_put_long_le(nfix_key("b"), klongs + 24);
    bytes_put_long_le(-1, refs);
    bytes_put_long_le(1000, refs + 8);
    bytes_put_long_le(-1, refs + 16);
    bytes_put_long_le(1003, refs + 24);
    struct knode *k = kn_new_stored(&f.cx, false, 2048, 1001, 4, klongs, refs);
    REQUIRE(k != NULL);
    char buf[KN_TEXT];
    const char *m = kn_validate_stream_node(k, 7, buf);
    REQUIRE(m != NULL);
    CHECK(strcmp(m, "Time not increasing, 500, 500, index=2") == 0);
    char buf2[KN_TEXT];
    m = kn_check(k, buf2);
    REQUIRE(m != NULL);
    CHECK(strcmp(m, "Time not increasing, 500, 500, index=2") == 0);
    m = kn_check_max(k, 62, buf2);
    REQUIRE(m != NULL);
    CHECK(strcmp(m, "Time not increasing, 500, 500, index=2") == 0);
    m = kn_check(k, NULL);
    REQUIRE(m != NULL);
    CHECK(strcmp(m, "Time not increasing") == 0);
    NFIX_END(&f);
}

/* A key node as a start reads it (KeyNodeTester.streamNode): id 22807, at
 * 36536, its pointers stream pointers, or pointee's where pointee[i]. */
static struct knode *stream_node(struct nfix *f, const int64_t *klongs, const int64_t *pos,
        struct obj *const *pointee, int32_t n) {
    struct knode *k = kn_new(&f->cx, false);
    if (k == NULL) {
        return NULL;
    }
    k->n.id = 22807;
    k->n.spos = 36536;
    for (int32_t i = 0; i < n; i++) {
        if (!kn_add_to_end(&f->cx, k, klongs[i], pointee != NULL ? pointee[i] : NULL, pos[i])) {
            return NULL;
        }
    }
    return k;
}

static bool same_text(const char *m, const char *expected) {
    if (m != NULL && strcmp(m, expected) == 0) {
        return true;
    }
    printf("    expected \"%s\", got \"%s\"\n", expected, m != NULL ? m : "(NULL)");
    return false;
}

/* KeyNodeTester.testNodeTextsSameInEveryRun (bergdb 021-15, as Java's since
 * release 2026.4): the texts of validateStreamNode, which a start refuses a
 * stream with, and of check() name the node by its id and position
 * (Node.name), the same in every run. Java's held KeyNode.toString, with
 * Object.toString's identity hash, or printed the whole node, and C's were
 * its own ("Key node with size 0", "Bad spos of pointer", "Bad spos of
 * pointer, at or before the startup time"). And check()'s two other texts
 * that name the node, a pointer's bad reference and an overfull node
 * (check(maxNodeSize)), and Node.name's kind. */
TEST(knode_node_texts_same_in_every_run) {
    struct nfix f;
    nfix_init(&f);
    char buf[KN_TEXT];
    const int64_t key = nfix_key("a");
    struct knode *k = stream_node(&f, NULL, NULL, NULL, 0);
    REQUIRE(k != NULL);
    CHECK(same_text(kn_validate_stream_node(k, 470, buf), "Key node 22807 at 36536 with size "
            "0."));
    /* A key klong before every time klong is of the time 0, at or before the startup time. */
    k = stream_node(&f, (const int64_t[]) { key }, (const int64_t[]) { SPOS_NULL }, NULL, 1);
    REQUIRE(k != NULL);
    CHECK(same_text(kn_validate_stream_node(k, 470, buf), "Bad spos of pointer 0 of key node "
            "22807 at 36536: -1, at or before the startup time 470."));
    k = stream_node(&f, (const int64_t[]) { kl_create_time(480), key },
            (const int64_t[]) { SPOS_NULL, -5 }, NULL, 2);
    REQUIRE(k != NULL);
    CHECK(same_text(kn_validate_stream_node(k, 470, buf), "Bad spos of pointer 1 of key node "
            "22807 at 36536: -5."));
    struct knode *bad = stream_node(&f, (const int64_t[]) { kl_create_time(400), key },
            (const int64_t[]) { SPOS_NULL, SPOS_NULL }, NULL, 2);
    REQUIRE(bad != NULL);
    CHECK(same_text(kn_check(bad, buf), "Bad spos of pointer 1 of key node 22807 at 36536: "
            "-1."));
    CHECK(same_text(kn_check(bad, NULL), "Bad spos"));
    CHECK(same_text(node_kind(node_type(&bad->n)), "key node"));
    /* A pointer that holds a value has a reference too: -5 is none. */
    struct vnode *v = nfix_value(&f);
    REQUIRE(v != NULL);
    k = stream_node(&f, (const int64_t[]) { kl_create_time(400), key },
            (const int64_t[]) { SPOS_NULL, -5 }, (struct obj *const[]) { NULL, &v->n.o }, 2);
    REQUIRE(k != NULL);
    CHECK(same_text(kn_check(k, buf), "Bad reference of pointer 1 of key node 22807 at 36536: "
            "-5."));
    CHECK(same_text(kn_check(k, NULL), "Bad reference"));
    /* check(maxNodeSize): at most maxNodeSize + 1 klongs. */
    k = stream_node(&f, (const int64_t[]) { kl_create_time(400), key, nfix_key("b") },
            (const int64_t[]) { SPOS_NULL, 1000, 1008 }, NULL, 3);
    REQUIRE(k != NULL);
    CHECK(kn_check_max(k, 2, buf) == NULL);
    CHECK(same_text(kn_check_max(k, 1, buf), "Overfull node, size=3, maxNodeSize=1, key node "
            "22807 at 36536."));
    CHECK(same_text(kn_check_max(k, 1, NULL), "Overfull node"));
    NFIX_END(&f);
}

const struct test knode_tests[] = {
    TEST_ENTRY(knode_sanity1),
    TEST_ENTRY(knode_sanity2),
    TEST_ENTRY(knode_eq),
    TEST_ENTRY(knode_eq_with_versions),
    TEST_ENTRY(knode_eq_with_versions_and_delete),
    TEST_ENTRY(knode_eq_before_first_version),
    TEST_ENTRY(knode_lte1),
    TEST_ENTRY(knode_lte2),
    TEST_ENTRY(knode_lte3),
    TEST_ENTRY(knode_lt1),
    TEST_ENTRY(knode_lt2),
    TEST_ENTRY(knode_lt3),
    TEST_ENTRY(knode_gt1),
    TEST_ENTRY(knode_gt2),
    TEST_ENTRY(knode_gte),
    TEST_ENTRY(knode_first1),
    TEST_ENTRY(knode_check_empty_node),
    TEST_ENTRY(knode_check1),
    TEST_ENTRY(knode_check2),
    TEST_ENTRY(knode_validate_time_text),
    TEST_ENTRY(knode_node_texts_same_in_every_run),
    TEST_ENTRY(knode_get_pointers),
    TEST_ENTRY(knode_last_version1),
    TEST_ENTRY(knode_last_version3),
    TEST_ENTRY(knode_last_version4),
    TEST_ENTRY(knode_first_and_second2),
    TEST_ENTRY(knode_first_and_second3),
    TEST_ENTRY(knode_first_and_second4),
    TEST_ENTRY(knode_first_and_second5),
    TEST_ENTRY(knode_first_and_second6),
    TEST_ENTRY(knode_delete_bitmap1),
    TEST_ENTRY(knode_to_previous_state1),
    TEST_ENTRY(knode_to_previous_state2),
    TEST_ENTRY(knode_to_previous_state3),
    TEST_ENTRY(knode_to_previous_state4),
    TEST_ENTRY(knode_new_key_node_with_time),
    TEST_ENTRY(knode_get_first_time1),
    TEST_ENTRY(knode_get_first_time2),
    TEST_ENTRY(knode_get_first_time3),
    TEST_ENTRY(knode_get_pointer_count0),
    TEST_ENTRY(knode_get_pointer_count1),
    TEST_ENTRY(knode_get_pointer_count2),
    TEST_ENTRY(knode_get_pointer_count3),
    TEST_ENTRY(knode_max_valid_time0),
    TEST_ENTRY(knode_max_valid_time1),
    TEST_ENTRY(knode_max_valid_time_with_delete),
    TEST_ENTRY(knode_add_delete_klong),
    TEST_ENTRY(knode_search_first_takes_first),
    TEST_ENTRY(knode_pointer_test1),
    TEST_ENTRY(knode_new_stored),
    TEST_END
};
