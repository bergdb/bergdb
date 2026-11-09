/* Unit tests of spos (bergdb 012-04): Java's @Nano tests of Spos, ported,
 * and spos_newer. */
#include "test.h"
#include "spos.h"

/* Spos.testAlign1. */
TEST(spos_align1) {
    CHECK_EQ(spos_add_to_align(0, 4), 0);
    CHECK_EQ(spos_add_to_align(1, 4), 3);
    CHECK_EQ(spos_add_to_align(2, 4), 2);
    CHECK_EQ(spos_add_to_align(3, 4), 1);
    CHECK_EQ(spos_add_to_align(4, 4), 0);
    CHECK_EQ(spos_add_to_align(5, 4), 3);
}

/* Spos.testAlign2. */
TEST(spos_align2) {
    CHECK_EQ(spos_add_to_align(0, 3), 0);
    CHECK_EQ(spos_add_to_align(1, 3), 2);
    CHECK_EQ(spos_add_to_align(2, 3), 1);
    CHECK_EQ(spos_add_to_align(3, 3), 0);
    CHECK_EQ(spos_add_to_align(4, 3), 2);
    CHECK_EQ(spos_add_to_align(5, 3), 1);
}

/* Spos.testIsNull, testIsValid, testIsValidOrNull. */
TEST(spos_null_and_valid) {
    CHECK(spos_is_null(SPOS_NULL));
    CHECK(!spos_is_null(12345));
    CHECK(spos_is_valid(1200));
    CHECK(spos_is_valid(0));
    CHECK(!spos_is_valid(-1234));
    CHECK(!spos_is_valid(SPOS_NULL));
    CHECK(spos_is_valid_or_null(1200));
    CHECK(spos_is_valid_or_null(0));
    CHECK(!spos_is_valid_or_null(-1234));
    CHECK(spos_is_valid_or_null(SPOS_NULL));
}

/* Spos.testNextVpos1. */
TEST(spos_next_vpos1) {
    CHECK_EQ(spos_next_vpos(0), 1);
    CHECK_EQ(spos_next_vpos(3), 5);
    CHECK_EQ(spos_next_vpos(9), 11);
}

/* Spos.testNextVpos2: never a multiple of 8, always odd and greater. */
TEST(spos_next_vpos2) {
    int64_t vpos = 123456;
    for (int i = 0; i < 40; i++) {
        int64_t next = spos_next_vpos(vpos);
        CHECK(next % 8 != 0);
        CHECK(spos_is_vpos(next) && next > vpos);
        vpos++;
    }
}

/* isVpos is Java's spos % 2 == 1: false for negative odd numbers, whose
 * remainder is -1 in both languages. */
TEST(spos_is_vpos) {
    CHECK(spos_is_vpos(1));
    CHECK(spos_is_vpos(INT64_MAX));
    CHECK(!spos_is_vpos(0));
    CHECK(!spos_is_vpos(8));
    CHECK(!spos_is_vpos(SPOS_NULL));
    CHECK(!spos_is_vpos(-3));
    CHECK(!spos_is_vpos(INT64_MIN));
}

/* newer (bergdb 009): a position is newer than a vpos whatever their
 * numbers; else by number; a vpos is never newer than a vpos, nor a
 * negative pos than a vpos. */
TEST(spos_newer) {
    CHECK(spos_newer(8, 9));                /* a position, a vpos above it */
    CHECK(spos_newer(0, 1001));
    CHECK(!spos_newer(11, 9));              /* a vpos is not newer than a vpos */
    CHECK(!spos_newer(7, 9));
    CHECK(!spos_newer(SPOS_NULL, 9));
    CHECK(spos_newer(16, 8));               /* by number */
    CHECK(!spos_newer(8, 8));
    CHECK(!spos_newer(8, 16));
    CHECK(spos_newer(9, 8));                /* a vpos against a position: by number */
    CHECK(!spos_newer(7, 8));
    CHECK(spos_newer(0, SPOS_NULL));
}

const struct test spos_tests[] = {
    TEST_ENTRY(spos_align1),
    TEST_ENTRY(spos_align2),
    TEST_ENTRY(spos_null_and_valid),
    TEST_ENTRY(spos_next_vpos1),
    TEST_ENTRY(spos_next_vpos2),
    TEST_ENTRY(spos_is_vpos),
    TEST_ENTRY(spos_newer),
    TEST_END
};
