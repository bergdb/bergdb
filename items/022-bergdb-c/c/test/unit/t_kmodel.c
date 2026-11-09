/* A random test of a key node against a simple model (bergdb 012-07,
 * section 4): puts and deletes of a few keys at increasing times, as the Dag
 * makes them (a delete only of a key that exists, a TIME klong when the
 * time moves); then the searches at random times against the model's state
 * at that time; the last version, a split of it into first and second, and
 * toPreviousState, each checked the same way; the counts recounted, and
 * nothing left after the last safe point. */
#include <string.h>
#include "klong.h"
#include "knode.h"
#include "nfix.h"
#include "spos.h"
#include "test.h"
#include "vnode.h"

#define NKEYS 10
#define MAXOPS 64

struct op {
    int64_t time;
    int32_t key;
    struct vnode *value;        /* NULL: a delete */
};

struct model {
    int64_t cv[NKEYS];          /* the keys' compare values, increasing */
    struct op ops[MAXOPS];
    int32_t nops;
};

/* The value of each key at time t (NULL: absent). */
static void state_at(const struct model *m, int64_t t, struct vnode **out) {
    for (int i = 0; i < NKEYS; i++) {
        out[i] = NULL;
    }
    for (int32_t i = 0; i < m->nops; i++) {
        if (m->ops[i].time <= t) {
            out[m->ops[i].key] = m->ops[i].value;
        }
    }
}

static int key_of(const struct model *m, int64_t cv) {
    for (int i = 0; i < NKEYS; i++) {
        if (m->cv[i] == cv) {
            return i;
        }
    }
    return -1;
}

/* Every search of node at time t against the state st, for each key and
 * for the compare values between them. */
static void check_searches(const struct knode *node, const struct model *m, int64_t t,
        struct vnode *const *st) {
    struct kwp kwi;
    for (int i = 0; i < NKEYS; i++) {
        kn_search_eq(node, t, m->cv[i], &kwi);
        if (st[i] == NULL) {
            CHECK_EQ(kwi.klong, KL_NULL);
        } else {
            CHECK_EQ(kl_get_compare_value(kwi.klong), m->cv[i]);
            CHECK(kwi.node == &st[i]->n);
        }
    }
    /* Probes: each key, one above and one below it. */
    for (int i = 0; i < NKEYS; i++) {
        for (int d = -1; d <= 1; d++) {
            int64_t probe = m->cv[i] + d * 8;
            int lte = -1, lt = -1, gt = -1, gte = -1;
            for (int j = 0; j < NKEYS; j++) {
                if (st[j] == NULL) {
                    continue;
                }
                if (m->cv[j] <= probe) lte = j;
                if (m->cv[j] < probe) lt = j;
                if (m->cv[j] > probe && gt == -1) gt = j;
                if (m->cv[j] >= probe && gte == -1) gte = j;
            }
            kn_search_lte(node, t, probe, &kwi);
            CHECK_EQ(kwi.klong == KL_NULL ? -1 : key_of(m, kl_get_compare_value(kwi.klong)), lte);
            if (lte >= 0) CHECK(kwi.node == &st[lte]->n);
            kn_search_lt(node, t, probe, &kwi);
            CHECK_EQ(kwi.klong == KL_NULL ? -1 : key_of(m, kl_get_compare_value(kwi.klong)), lt);
            if (lt >= 0) CHECK(kwi.node == &st[lt]->n);
            kn_search_gt(node, t, probe, &kwi);
            CHECK_EQ(kwi.klong == KL_NULL ? -1 : key_of(m, kl_get_compare_value(kwi.klong)), gt);
            if (gt >= 0) CHECK(kwi.node == &st[gt]->n);
            kn_search_gte(node, t, probe, &kwi);
            CHECK_EQ(kwi.klong == KL_NULL ? -1 : key_of(m, kl_get_compare_value(kwi.klong)), gte);
            if (gte >= 0) CHECK(kwi.node == &st[gte]->n);
        }
    }
    /* searchFirst: the smallest key; its pointer is the first of the key's
     * klongs, not the latest (012-07, section 5), so only the key is
     * checked. searchGt(-1), which getMany uses, gives the latest. */
    int first = -1;
    for (int j = 0; j < NKEYS && first == -1; j++) {
        if (st[j] != NULL) first = j;
    }
    kn_search_first(node, t, &kwi);
    CHECK_EQ(kwi.klong == KL_NULL ? -1 : key_of(m, kl_get_compare_value(kwi.klong)), first);
    kn_search_gt(node, t, -1, &kwi);
    CHECK_EQ(kwi.klong == KL_NULL ? -1 : key_of(m, kl_get_compare_value(kwi.klong)), first);
    if (first >= 0) CHECK(kwi.node == &st[first]->n);
}

static void make_keys(struct model *m, uint64_t *rnd) {
    int n = 0;
    while (n < NKEYS) {
        uint8_t b[3];
        int32_t len = test_random_below(rnd, 4);
        for (int32_t i = 0; i < len; i++) {
            b[i] = (uint8_t) (0x61 + test_random_below(rnd, 4));
        }
        int64_t cv = kl_create_compare_value(b, len);
        bool dup = false;
        for (int i = 0; i < n; i++) {
            dup = dup || m->cv[i] == cv;
        }
        if (!dup) {
            m->cv[n++] = cv;
        }
    }
    for (int i = 1; i < NKEYS; i++) {       /* sorted */
        for (int j = i; j > 0 && m->cv[j - 1] > m->cv[j]; j--) {
            int64_t x = m->cv[j];
            m->cv[j] = m->cv[j - 1];
            m->cv[j - 1] = x;
        }
    }
}

static void one_run(uint64_t seed) {
    struct nfix f;
    nfix_init(&f);
    uint64_t rnd = seed;
    struct model m;
    memset(&m, 0, sizeof m);
    make_keys(&m, &rnd);

    struct knode *node = kn_new(&f.cx, true);
    REQUIRE(node != NULL);
    int64_t t = 1 + test_random_below(&rnd, 5);
    bool usedAtT[NKEYS] = {false};
    struct vnode *st[NKEYS];

    while (m.nops < MAXOPS && node->size + 2 <= 60) {
        int k = test_random_below(&rnd, NKEYS);
        if (usedAtT[k] || test_random_below(&rnd, 3) == 0) {
            t += 1 + test_random_below(&rnd, 3);
            memset(usedAtT, 0, sizeof usedAtT);
        }
        usedAtT[k] = true;
        state_at(&m, t, st);
        if (st[k] != NULL && test_random_below(&rnd, 4) == 0) {
            int64_t del = kn_get_delete_bitmap(node, m.cv[k]);
            CHECK(del != 0);
            CHECK(kn_add_delete_klong(&f.cx, node, t, del));
            m.ops[m.nops].time = t;
            m.ops[m.nops].key = k;
            m.ops[m.nops].value = NULL;
            m.nops++;
        } else {
            uint8_t b[1] = {(uint8_t) m.nops};
            struct vnode *v = vn_new(&f.cx, b, 1, 1000 + 8 * m.nops);
            REQUIRE(v != NULL);
            CHECK(kn_add_klong(&f.cx, node, t, kl_compare_value_to_key_klong(m.cv[k]), &v->n,
                    ACCESS_DATA_DEFAULT));
            m.ops[m.nops].time = t;
            m.ops[m.nops].key = k;
            m.ops[m.nops].value = v;
            m.nops++;
        }
        CHECK(kn_check_max(node, 62) == NULL);
        NFIX_RECOUNT(&f, NULL, 0);      /* after each change (012-01, 4.5) */
    }

    /* The searches at every time up to past the last. */
    for (int64_t at = 0; at <= t + 2; at++) {
        state_at(&m, at, st);
        check_searches(node, &m, at, st);
    }

    /* The last version at t + 1: the latest state, in increasing compare
     * values; nothing before t + 1. */
    struct knode *last = kn_last_version(&f.cx, node, t + 1);
    REQUIRE(last != NULL);
    state_at(&m, t, st);
    check_searches(last, &m, t + 1, st);
    check_searches(last, &m, INT64_MAX, st);
    for (int32_t i = 2; i < last->size; i++) {
        CHECK(kl_get_compare_value(last->klongs[i - 1]) < kl_get_compare_value(last->klongs[i]));
    }
    struct vnode *none[NKEYS] = {NULL};
    check_searches(last, &m, t, none);

    /* A split of the last version: each key in first or second. */
    if (last->size >= 2) {
        struct knode *first = kn_new(&f.cx, true);
        struct knode *second = kn_new(&f.cx, true);
        int64_t secondKlong = 0;
        CHECK(kn_first_and_second(&f.cx, node, t + 1, last, NULL, 0, first, second,
                &secondKlong));
        CHECK_EQ(first->size + second->size, last->size + 1);
        struct vnode *in1[NKEYS], *in2[NKEYS];
        for (int i = 0; i < NKEYS; i++) {
            bool high = m.cv[i] >= kl_get_compare_value(secondKlong);
            in1[i] = high ? NULL : st[i];
            in2[i] = high ? st[i] : NULL;
        }
        check_searches(first, &m, t + 1, in1);
        check_searches(second, &m, t + 1, in2);
    }
    NFIX_RECOUNT(&f, NULL, 0);

    /* toPreviousState at a random time: the state of that time ever after. */
    int64_t t0 = test_random_below(&rnd, (int32_t) t + 1);
    kn_to_previous_state(&f.cx, node, t0);
    CHECK(kn_check(node) == NULL);
    for (int64_t at = 0; at <= t + 2; at++) {
        state_at(&m, at <= t0 ? at : t0, st);
        check_searches(node, &m, at, st);
    }
    NFIX_END(&f);
}

TEST(kmodel_random) {
    for (uint64_t seed = 1; seed <= 300; seed++) {
        long failed = test_failed_checks_;
        one_run(seed);
        if (test_failed_checks_ != failed) {
            printf("kmodel_random: seed %llu failed\n", (unsigned long long) seed);
            break;
        }
    }
}

const struct test kmodel_tests[] = {
    TEST_ENTRY(kmodel_random),
    TEST_END
};
