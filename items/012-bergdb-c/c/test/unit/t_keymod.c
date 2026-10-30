/* Unit tests of keymod (bergdb 012-09, part 1): Java's @Nano tests of
 * KeyModSet, ported, the startup boundary (005-70), the bins' turnover,
 * and the allocation-failure runs. */
#include "test.h"
#include "keymod.h"

static struct mem km;
static struct err ke;

static struct kms *new_set(struct kms *s, int32_t size) {
    mem_init(&km);
    if (kms_init_size(s, &km, size, &ke) != ERR_OK) {
        return NULL;
    }
    return s;
}

/* KeyModSet.test1: any request with time < 1 should return true. */
TEST(keymod_test1) {
    struct kms s;
    REQUIRE(new_set(&s, KMS_DEFAULT_SIZE) != NULL);
    CHECK_EQ(kms_add(&s, 1, 1234, &ke), ERR_OK);
    CHECK(kms_modified_after(&s, 0, 1234));
    CHECK(!kms_modified_after(&s, 1, 1234));
    CHECK(!kms_modified_after(&s, 9999, 1234));
    CHECK(kms_modified_after(&s, 0, 9234));
    CHECK(!kms_modified_after(&s, 9999, 9234));
    kms_free(&s);
    CHECK_MEM_ZERO(&km);
}

/* KeyModSet.test2. */
TEST(keymod_test2) {
    struct kms s;
    REQUIRE(new_set(&s, KMS_DEFAULT_SIZE) != NULL);
    CHECK_EQ(kms_add(&s, 1001, 3, &ke), ERR_OK);
    CHECK(kms_modified_after(&s, 100, 3));
    CHECK(!kms_modified_after(&s, 2000, 3));
    kms_free(&s);
    CHECK_MEM_ZERO(&km);
}

/* KeyModSet.test3. */
TEST(keymod_test3) {
    struct kms s;
    REQUIRE(new_set(&s, KMS_DEFAULT_SIZE) != NULL);
    CHECK_EQ(kms_add(&s, 1, 3, &ke), ERR_OK);
    CHECK_EQ(kms_add(&s, 1001, 3, &ke), ERR_OK);
    CHECK(kms_modified_after(&s, 100, 3));
    CHECK(kms_modified_after(&s, 1000, 3));
    CHECK(!kms_modified_after(&s, 1001, 3));
    CHECK(!kms_modified_after(&s, 99999, 3));
    kms_free(&s);
    CHECK_MEM_ZERO(&km);
}

/* KeyModSet.testFutureTime. */
TEST(keymod_future_time) {
    struct kms s;
    REQUIRE(new_set(&s, KMS_DEFAULT_SIZE) != NULL);
    CHECK_EQ(kms_add(&s, 1001, 3, &ke), ERR_OK);
    CHECK(!kms_modified_after(&s, 99999, 3));
    CHECK(!kms_modified_after(&s, 99999, 4));
    kms_free(&s);
    CHECK_MEM_ZERO(&km);
}

/* KeyModSet.testResize: a sub-bin's array grows. */
TEST(keymod_resize) {
    struct kms s;
    REQUIRE(new_set(&s, KMS_DEFAULT_SIZE) != NULL);
    for (int i = 0; i < KMS_INITIAL_SIZE_OF_LONG_ARRAY * 3; i++) {
        CHECK_EQ(kms_add(&s, i, 0, &ke), ERR_OK);
    }
    CHECK(!kms_modified_after(&s, KMS_INITIAL_SIZE_OF_LONG_ARRAY * 3, 0));
    CHECK(!kms_modified_after(&s, KMS_INITIAL_SIZE_OF_LONG_ARRAY * 3 - 1, 0));
    CHECK(kms_modified_after(&s, KMS_INITIAL_SIZE_OF_LONG_ARRAY * 3 - 2, 0));
    kms_free(&s);
    CHECK_MEM_ZERO(&km);
}

/* A sub-bin that holds several hashes: one array with several pairs,
 * grown, each hash's last time kept. A set of 32 has bins of 8 pairs and
 * 2 sub-bins each. */
TEST(keymod_collisions) {
    struct kms s;
    REQUIRE(new_set(&s, 32) != NULL);
    REQUIRE(s.bins[0]->subSize == 2);
    /* Hashes 0, 2, 4 and 6 share sub-bin 0; 1 and 3 sub-bin 1. */
    CHECK_EQ(kms_add(&s, 10, 0, &ke), ERR_OK);
    CHECK_EQ(kms_add(&s, 11, 2, &ke), ERR_OK);
    CHECK_EQ(kms_add(&s, 12, 4, &ke), ERR_OK);
    CHECK_EQ(kms_add(&s, 13, 0, &ke), ERR_OK);       /* replaces hash 0's pair */
    CHECK_EQ(kms_add(&s, 14, 1, &ke), ERR_OK);
    CHECK_EQ(s.bins[0]->subBins[0].len, 8);         /* grown once: 3 pairs */
    CHECK_EQ(s.bins[0]->subBins[1].len, 4);
    CHECK(kms_modified_after(&s, 12, 0));
    CHECK(!kms_modified_after(&s, 13, 0));
    CHECK(kms_modified_after(&s, 10, 2));
    CHECK(!kms_modified_after(&s, 11, 2));
    CHECK(!kms_modified_after(&s, 10, 6));          /* in no bin */
    CHECK(kms_modified_after(&s, 9, 6));            /* too old: before every bin */
    CHECK_EQ(kms_first_time(&s), 10);
    kms_free(&s);
    CHECK_MEM_ZERO(&km);
}

/* KeyModSet.testBins1. */
TEST(keymod_bins1) {
    struct kms s;
    REQUIRE(new_set(&s, 8) != NULL);
    CHECK_EQ(kms_add(&s, 10, 0, &ke), ERR_OK);
    CHECK_EQ(kms_add(&s, 20, 0, &ke), ERR_OK);
    CHECK_EQ(kms_add(&s, 30, 0, &ke), ERR_OK);
    CHECK_EQ(kms_add(&s, 30, 1, &ke), ERR_OK);

    CHECK(kms_modified_after(&s, 0, 0));
    CHECK(kms_modified_after(&s, 29, 0));
    CHECK(!kms_modified_after(&s, 99, 0));
    CHECK(kms_modified_after(&s, 29, 1));
    CHECK(!kms_modified_after(&s, 30, 1));
    kms_free(&s);
    CHECK_MEM_ZERO(&km);
}

/* KeyModSet.testBins2: more than 4 bins are made; the oldest go. */
TEST(keymod_bins2) {
    struct kms s;
    REQUIRE(new_set(&s, 8) != NULL);
    CHECK_EQ(kms_add(&s, 3, 222, &ke), ERR_OK);
    for (int i = 0; i < 16; i++) {
        CHECK_EQ(kms_add(&s, 5 + i * 10, 333, &ke), ERR_OK);
    }
    CHECK_EQ(kms_add(&s, 200, 444, &ke), ERR_OK);

    CHECK(kms_modified_after(&s, 150, 333));
    CHECK(!kms_modified_after(&s, 161, 333));
    CHECK(!kms_modified_after(&s, 99, 0));
    CHECK(kms_modified_after(&s, 1, 111));      /* true because of lack of info */
    CHECK(!kms_modified_after(&s, 120, 111));

    CHECK(kms_first_time(&s) > 50);
    CHECK(kms_first_time(&s) < 150);
    /* Exactly: 18 adds in bins of 2 (a bin counts its adds, also those
     * that replace a hash's pair); the 4 kept hold adds 11 to 18, the
     * oldest at 5 + 9 * 10. */
    CHECK_EQ(kms_first_time(&s), 95);
    kms_free(&s);
    CHECK_MEM_ZERO(&km);
}

/* KeyModSet(int) refuses a size that is not a multiple of 4. */
TEST(keymod_bad_size) {
    struct kms s;
    mem_init(&km);
    CHECK_EQ(kms_init_size(&s, &km, 6, &ke), ERR_ARG);
    CHECK(strcmp(ke.java, "IllegalArgumentException") == 0);
    CHECK(strstr(ke.text, "size was 6, must be dividable by 4.") != NULL);
    kms_free(&s);
    CHECK_MEM_ZERO(&km);
}

/* KeyModSet.testStartupBoundary: the last recovered commit, preserved on
 * the first add and eventually dropped by normal bin turnover (005-70). */
TEST(keymod_startup_boundary) {
    struct kms s;
    REQUIRE(new_set(&s, 8) != NULL);
    kms_set_first_time(&s, 100);
    CHECK(kms_modified_after(&s, 99, 5));
    CHECK(!kms_modified_after(&s, 100, 5));
    CHECK(!kms_modified_after(&s, 101, 5));
    CHECK_EQ(kms_add(&s, 110, 7, &ke), ERR_OK);
    CHECK_EQ(kms_first_time(&s), 100);
    CHECK(!kms_modified_after(&s, 100, 5));
    CHECK(kms_modified_after(&s, 100, 7));
    CHECK(!kms_modified_after(&s, 110, 7));
    for (int i = 1; i <= 8; i++) {
        CHECK_EQ(kms_add(&s, 110 + i, 7, &ke), ERR_OK);
    }
    CHECK_EQ(kms_first_time(&s), 112);
    CHECK(kms_modified_after(&s, 100, 5));
    CHECK(!kms_modified_after(&s, 112, 5));
    kms_free(&s);
    CHECK_MEM_ZERO(&km);
}

/* The default set: bins of 32,000 pairs, 8,000 sub-bins; the fifth bin
 * drops the first. */
TEST(keymod_default_turnover) {
    struct kms s;
    REQUIRE(new_set(&s, KMS_DEFAULT_SIZE) != NULL);
    REQUIRE(s.bins[0]->maxSize == 32000 && s.bins[0]->subSize == 8000);
    int failures = 0;
    for (int64_t i = 0; i < 4 * 32000; i++) {
        failures += kms_add(&s, 100 + i, i * 7919, &ke) != ERR_OK;
    }
    CHECK_EQ(failures, 0);
    CHECK(s.bins[3] != NULL);
    CHECK_EQ(kms_first_time(&s), 100);
    CHECK(!kms_modified_after(&s, 100, 0));
    CHECK(kms_modified_after(&s, 99, 0));      /* too old */
    REQUIRE(kms_add(&s, 100 + 4 * 32000, 1, &ke) == ERR_OK);
    CHECK_EQ(kms_first_time(&s), 100 + 32000);
    CHECK(kms_modified_after(&s, 100 + 32000 - 1, 0));     /* now too old */
    CHECK(!kms_modified_after(&s, 100 + 32000, 32000 * INT64_C(7919)));
    CHECK(kms_modified_after(&s, 100 + 32000, 32001 * INT64_C(7919)));
    kms_free(&s);
    CHECK_MEM_ZERO(&km);
}

/* Each allocation made to fail in turn (012-01, 4.5): NOMEM, and the set
 * as it was, which still answers as before. */
TEST(keymod_failure_runs) {
    int64_t n = 1;
    for (;; n++) {
        struct kms s;
        mem_init(&km);
        km.fail_at = n;
        enum err_code rc = kms_init_size(&s, &km, 8, &ke);
        if (rc != ERR_OK) {
            CHECK_EQ(rc, ERR_NOMEM);
            kms_free(&s);
            CHECK_MEM_ZERO(&km);
            continue;
        }
        bool failed = false;
        for (int i = 0; i < 12; i++) {
            int64_t first = kms_first_time(&s);
            bool before = kms_modified_after(&s, 5, i % 3);
            rc = kms_add(&s, 10 + i, i % 3, &ke);
            if (rc != ERR_OK) {
                CHECK_EQ(rc, ERR_NOMEM);
                CHECK_EQ(kms_first_time(&s), first);
                CHECK(kms_modified_after(&s, 5, i % 3) == before);
                failed = true;
                break;
            }
        }
        kms_free(&s);
        CHECK_MEM_ZERO(&km);
        if (!failed && km.allocs < n) {
            break;
        }
    }
    CHECK(n > 5);
}

const struct test keymod_tests[] = {
    TEST_ENTRY(keymod_test1),
    TEST_ENTRY(keymod_test2),
    TEST_ENTRY(keymod_test3),
    TEST_ENTRY(keymod_future_time),
    TEST_ENTRY(keymod_resize),
    TEST_ENTRY(keymod_collisions),
    TEST_ENTRY(keymod_bins1),
    TEST_ENTRY(keymod_bins2),
    TEST_ENTRY(keymod_bad_size),
    TEST_ENTRY(keymod_startup_boundary),
    TEST_ENTRY(keymod_default_turnover),
    TEST_ENTRY(keymod_failure_runs),
    TEST_END
};
