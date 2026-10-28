/*
 * test.h: the C clone's test framework, one header (bergdb 012-04).
 *
 * A test is a function, TEST(name) { ... }, registered in its file's table:
 *
 *     TEST(klong_time) { CHECK_EQ(kl_get_time(kl_create_time(5)), 5); }
 *     const struct test klong_tests[] = { TEST_ENTRY(klong_time), TEST_END };
 *
 * (an unregistered test is an unused static function: an error with
 * -Werror). One file of each test program defines TEST_MAIN before it
 * includes this header, lists the tables and calls test_main:
 *
 *     #define TEST_MAIN
 *     #include "test.h"
 *     extern const struct test klong_tests[];
 *     int main(int argc, char **argv) {
 *         const struct test *const tables[] = { klong_tests, NULL };
 *         return test_main(argc, argv, "UNIT", tables);
 *     }
 *
 * The program runs every test, or those whose names start with one of its
 * arguments; -l lists the names. Each failed check prints its file, line and
 * values, and the test goes on (CHECK) or returns (REQUIRE). At the end a
 * summary line: "UNIT OK: ..." or "UNIT FAILED: ...", and the exit status
 * is 1 if a check failed or no test matched.
 */
#ifndef BERGDB_TEST_H
#define BERGDB_TEST_H

#include <inttypes.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>
#include "mem.h"

struct test {
    const char *name;
    void (*fn)(void);
};

/* The function is test_NAME, so that a test may have its module's names. */
#define TEST(name) static void test_##name(void)
#define TEST_ENTRY(name) { #name, test_##name }
#define TEST_END { NULL, NULL }

/* The failed and the made checks of the running program. */
extern long test_failed_checks_;
extern long test_checks_;

void test_fail_(const char *file, int line, const char *expr);
void test_fail_i64_(const char *file, int line, const char *expr, int64_t a, int64_t b);
void test_fail_mem_(const char *file, int line, const char *expr, const struct mem *m);

#define CHECK(c) do { \
        test_checks_++; \
        if (!(c)) test_fail_(__FILE__, __LINE__, "CHECK(" #c ")"); \
    } while (0)

/* Fails the check, and returns from the test. */
#define REQUIRE(c) do { \
        test_checks_++; \
        if (!(c)) { test_fail_(__FILE__, __LINE__, "REQUIRE(" #c ")"); return; } \
    } while (0)

/* Two integers, compared as int64_t; both printed on a failure. */
#define CHECK_EQ(a, b) do { \
        int64_t test_a_ = (a), test_b_ = (b); \
        test_checks_++; \
        if (test_a_ != test_b_) \
            test_fail_i64_(__FILE__, __LINE__, "CHECK_EQ(" #a ", " #b ")", test_a_, test_b_); \
    } while (0)

/* n bytes at a and b. */
#define CHECK_BYTES(a, b, n) do { \
        test_checks_++; \
        if (memcmp((a), (b), (n)) != 0) \
            test_fail_(__FILE__, __LINE__, "CHECK_BYTES(" #a ", " #b ", " #n ")"); \
    } while (0)

/* The allocator's counts are 0: nothing live (after a close, after the
 * last free); else the live bytes by kind are printed. */
#define CHECK_MEM_ZERO(m) do { \
        test_checks_++; \
        if ((m)->live_total != 0 || (m)->live_blocks != 0) \
            test_fail_mem_(__FILE__, __LINE__, "CHECK_MEM_ZERO(" #m ")", (m)); \
    } while (0)

/* A deterministic random long (SplitMix64), for tests where Java's use
 * java.util.Random for values whose choice does not matter (round trips,
 * two ways that must agree). Where Java's exact values matter, the vectors
 * have them. */
static inline int64_t test_random(uint64_t *state) {
    uint64_t z = (*state += UINT64_C(0x9E3779B97F4A7C15));
    z = (z ^ (z >> 30)) * UINT64_C(0xBF58476D1CE4E5B9);
    z = (z ^ (z >> 27)) * UINT64_C(0x94D049BB133111EB);
    return (int64_t) (z ^ (z >> 31));
}

/* A random int in 0 to n - 1, n > 0. */
static inline int32_t test_random_below(uint64_t *state, int32_t n) {
    return (int32_t) ((uint64_t) test_random(state) % (uint64_t) n);
}

int test_main(int argc, char **argv, const char *suite, const struct test *const *tables);

#ifdef TEST_MAIN

long test_failed_checks_;
long test_checks_;
static const char *test_current_;

void test_fail_(const char *file, int line, const char *expr) {
    test_failed_checks_++;
    printf("%s:%d: %s failed, in %s\n", file, line, expr, test_current_);
}

void test_fail_i64_(const char *file, int line, const char *expr, int64_t a, int64_t b) {
    test_failed_checks_++;
    printf("%s:%d: %s failed, in %s: %" PRId64 " != %" PRId64
            " (0x%016" PRIx64 " != 0x%016" PRIx64 ")\n", file, line, expr, test_current_,
            a, b, (uint64_t) a, (uint64_t) b);
}

void test_fail_mem_(const char *file, int line, const char *expr, const struct mem *m) {
    test_failed_checks_++;
    printf("%s:%d: %s failed, in %s: %" PRId64 " bytes in %" PRId64 " blocks live:",
            file, line, expr, test_current_, m->live_total, m->live_blocks);
    for (int k = 0; k < MEM_KINDS; k++) {
        if (m->live[k] != 0) {
            printf(" %s %" PRId64, mem_kind_name((enum mem_kind) k), m->live[k]);
        }
    }
    printf("\n");
}

static int test_selected_(const char *name, int argc, char **argv) {
    int any = 0;
    for (int i = 1; i < argc; i++) {
        if (argv[i][0] == '-') {
            continue;
        }
        any = 1;
        if (strncmp(name, argv[i], strlen(argv[i])) == 0) {
            return 1;
        }
    }
    return !any;
}

int test_main(int argc, char **argv, const char *suite, const struct test *const *tables) {
    int list = argc > 1 && strcmp(argv[1], "-l") == 0;
    int run = 0;
    int failed = 0;

    for (int t = 0; tables[t] != NULL; t++) {
        for (const struct test *x = tables[t]; x->name != NULL; x++) {
            if (!test_selected_(x->name, argc, argv)) {
                continue;
            }
            if (list) {
                printf("%s\n", x->name);
                continue;
            }
            long before = test_failed_checks_;
            test_current_ = x->name;
            x->fn();
            fflush(stdout);
            run++;
            if (test_failed_checks_ != before) {
                failed++;
                printf("FAILED %s\n", x->name);
            }
        }
    }
    if (list) {
        return 0;
    }
    if (failed != 0 || run == 0) {
        printf("%s FAILED: %d of %d tests failed, %ld of %ld checks\n", suite, failed, run,
                test_failed_checks_, test_checks_);
        return 1;
    }
    printf("%s OK: %d tests, %ld checks\n", suite, run, test_checks_);
    return 0;
}

#endif /* TEST_MAIN */

#endif
