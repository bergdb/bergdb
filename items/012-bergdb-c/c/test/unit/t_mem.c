/* Unit tests of mem, the allocator (bergdb 012-01, 4.5, point 1; 012-04):
 * the counts by kind, NOMEM, the Nth allocation made to fail, and the
 * check that nothing is live after a close (CHECK_MEM_ZERO). */
#include <signal.h>
#include <stdio.h>
#include <stdlib.h>
#include <sys/wait.h>
#include <unistd.h>
#include "test.h"
#include "mem.h"

/* The live bytes and blocks of each kind, and their sums. */
TEST(mem_counts_by_kind) {
    struct mem m;
    mem_init(&m);
    CHECK_MEM_ZERO(&m);
    void *a = mem_alloc(&m, 100, MEM_INDEX);
    void *b = mem_alloc(&m, 30, MEM_VALUE);
    void *c = mem_alloc(&m, 7, MEM_INDEX);
    void *d = mem_alloc(&m, 4096, MEM_BUFFER);
    REQUIRE(a != NULL && b != NULL && c != NULL && d != NULL);
    CHECK_EQ(m.live[MEM_INDEX], 107);
    CHECK_EQ(m.live[MEM_VALUE], 30);
    CHECK_EQ(m.live[MEM_BUFFER], 4096);
    CHECK_EQ(m.live[MEM_HANDLE] + m.live[MEM_TABLE] + m.live[MEM_CALLER] + m.live[MEM_STATE], 0);
    CHECK_EQ(m.live_total, 107 + 30 + 4096);
    CHECK_EQ(m.live_blocks, 4);
    CHECK_EQ(m.allocs, 4);
    memset(a, 1, 100);                      /* the blocks are usable to their size */
    memset(d, 2, 4096);
    mem_free(&m, d, 4096, MEM_BUFFER);
    CHECK_EQ(m.live_total, 137);
    CHECK_EQ(m.peak_total, 107 + 30 + 4096);
    mem_free(&m, a, 100, MEM_INDEX);
    mem_free(&m, c, 7, MEM_INDEX);
    CHECK_EQ(m.live[MEM_INDEX], 0);
    mem_free(&m, b, 30, MEM_VALUE);
    CHECK_MEM_ZERO(&m);
    CHECK_EQ(m.failed, 0);
}

/* Each struct mem counts its own: one per database, no global state. */
TEST(mem_per_database) {
    struct mem m1, m2;
    mem_init(&m1);
    mem_init(&m2);
    void *a = mem_alloc(&m1, 10, MEM_STATE);
    void *b = mem_alloc(&m2, 20, MEM_STATE);
    CHECK_EQ(m1.live_total, 10);
    CHECK_EQ(m2.live_total, 20);
    mem_free(&m1, a, 10, MEM_STATE);
    CHECK_MEM_ZERO(&m1);
    CHECK_EQ(m2.live_total, 20);
    mem_free(&m2, b, 20, MEM_STATE);
    CHECK_MEM_ZERO(&m2);
}

/* zalloc zeroes; a block of 0 bytes is a block, not a failure; free of
 * NULL does nothing. */
TEST(mem_zalloc_and_zero) {
    struct mem m;
    mem_init(&m);
    uint8_t *z = mem_zalloc(&m, 64, MEM_TABLE);
    REQUIRE(z != NULL);
    for (int i = 0; i < 64; i++) {
        CHECK(z[i] == 0);
    }
    void *e = mem_alloc(&m, 0, MEM_CALLER);
    CHECK(e != NULL);
    CHECK_EQ(m.live_blocks, 2);
    CHECK_EQ(m.live_total, 64);
    mem_free(&m, e, 0, MEM_CALLER);
    mem_free(&m, z, 64, MEM_TABLE);
    mem_free(&m, NULL, 123, MEM_TABLE);
    CHECK_MEM_ZERO(&m);
}

/* realloc counts the difference, keeps the bytes, and from NULL allocates. */
TEST(mem_realloc) {
    struct mem m;
    mem_init(&m);
    uint8_t *p = mem_realloc(&m, NULL, 0, 16, MEM_BUFFER);
    REQUIRE(p != NULL);
    CHECK_EQ(m.live_blocks, 1);
    for (int i = 0; i < 16; i++) {
        p[i] = (uint8_t) i;
    }
    p = mem_realloc(&m, p, 16, 100000, MEM_BUFFER);
    REQUIRE(p != NULL);
    CHECK_EQ(m.live[MEM_BUFFER], 100000);
    CHECK_EQ(m.live_blocks, 1);
    for (int i = 0; i < 16; i++) {
        CHECK(p[i] == i);
    }
    p[99999] = 7;
    p = mem_realloc(&m, p, 100000, 8, MEM_BUFFER);
    REQUIRE(p != NULL);
    CHECK_EQ(m.live_total, 8);
    CHECK_EQ(m.peak_total, 100000);
    CHECK(p[7] == 7);
    p = mem_realloc(&m, p, 8, 0, MEM_BUFFER);
    REQUIRE(p != NULL);
    CHECK_EQ(m.live_total, 0);
    CHECK_EQ(m.live_blocks, 1);
    mem_free(&m, p, 0, MEM_BUFFER);
    CHECK_MEM_ZERO(&m);
    CHECK_EQ(m.allocs, 4);
}

/* fail_at: that allocation, and only it, gives NULL, and counts nothing
 * live; a failed realloc leaves the block as it was. */
TEST(mem_fail_at) {
    struct mem m;
    mem_init(&m);
    m.fail_at = 3;
    void *a = mem_alloc(&m, 10, MEM_INDEX);
    void *b = mem_zalloc(&m, 10, MEM_INDEX);
    void *c = mem_alloc(&m, 10, MEM_INDEX);
    void *d = mem_alloc(&m, 10, MEM_INDEX);
    CHECK(a != NULL && b != NULL && d != NULL);
    CHECK(c == NULL);
    CHECK_EQ(m.failed, 1);
    CHECK_EQ(m.live_total, 30);
    CHECK_EQ(m.live_blocks, 3);
    CHECK_EQ(m.allocs, 4);

    uint8_t *p = a;
    memset(p, 0x5a, 10);
    m.fail_at = m.allocs + 1;               /* the next: a realloc */
    CHECK(mem_realloc(&m, p, 10, 1000, MEM_INDEX) == NULL);
    CHECK_EQ(m.failed, 2);
    CHECK_EQ(m.live_total, 30);
    CHECK(p[0] == 0x5a && p[9] == 0x5a);    /* still there, still 10 bytes */
    mem_free(&m, a, 10, MEM_INDEX);
    mem_free(&m, b, 10, MEM_INDEX);
    mem_free(&m, d, 10, MEM_INDEX);
    CHECK_MEM_ZERO(&m);
}

/* An allocation too large for malloc fails, counted as failed, not live.
 * The results go through a volatile pointer: where the optimizer sees the
 * whole allocation (the release build's -flto, 012-17, inlines mem_alloc
 * here), it may remove a malloc whose block is never used and take it as
 * succeeded, as C allows; the block must escape for malloc to run. */
TEST(mem_too_large) {
    struct mem m;
    void *volatile p;
    mem_init(&m);
    p = mem_alloc(&m, SIZE_MAX, MEM_VALUE);
    CHECK(p == NULL);
    p = mem_alloc(&m, SIZE_MAX - 8, MEM_VALUE);
    CHECK(p == NULL);
    CHECK_EQ(m.failed, 2);
    CHECK_MEM_ZERO(&m);
}

/* A small workload as the library's code will be: a list of n nodes, each
 * with a value; NOMEM (here -1) frees what was built and returns. */
struct node {
    struct node *next;
    uint8_t *value;
};

/* Frees a list of n nodes, the head the last built. */
static void free_list(struct mem *m, struct node *head, int n) {
    for (int i = n - 1; head != NULL; i--) {
        struct node *next = head->next;
        mem_free(m, head->value, (size_t) (i + 1), MEM_VALUE);
        mem_free(m, head, sizeof *head, MEM_INDEX);
        head = next;
    }
}

static int build_list(struct mem *m, int n, struct node **out) {
    struct node *head = NULL;
    for (int i = 0; i < n; i++) {
        struct node *x = mem_alloc(m, sizeof *x, MEM_INDEX);
        if (x == NULL) {
            free_list(m, head, i);
            return -1;
        }
        x->value = mem_alloc(m, (size_t) (i + 1), MEM_VALUE);
        if (x->value == NULL) {
            mem_free(m, x, sizeof *x, MEM_INDEX);
            free_list(m, head, i);
            return -1;
        }
        memset(x->value, i, (size_t) (i + 1));
        x->next = head;
        head = x;
    }
    *out = head;
    return 0;
}

/* The allocation-failure runs (012-01, 4.5): each allocation made to fail
 * in turn, one run each; every run gives NOMEM and leaves nothing live,
 * and the run with fail_at past the last allocation succeeds. */
TEST(mem_failure_runs) {
    const int n = 5;
    int runs = 0;
    for (int64_t k = 1;; k++) {
        struct mem m;
        struct node *list = NULL;
        mem_init(&m);
        m.fail_at = k;
        int rc = build_list(&m, n, &list);
        runs++;
        if (m.allocs < k) {                 /* nothing failed: the end */
            REQUIRE(rc == 0);
            CHECK_EQ(m.failed, 0);
            free_list(&m, list, n);
            CHECK_MEM_ZERO(&m);
            break;
        }
        CHECK_EQ(rc, -1);
        CHECK_EQ(m.failed, 1);
        CHECK_MEM_ZERO(&m);
        REQUIRE(k < 1000);
    }
    CHECK_EQ(runs, 2 * n + 1);
}

#ifdef BERGDB_TEST
/* The test build checks a free's size and kind against the allocation's
 * and aborts on a mismatch: run in a child process. */
static int child_aborts(size_t free_size, enum mem_kind free_kind) {
    fflush(stdout);
    pid_t pid = fork();
    if (pid == 0) {
        struct mem m;
        mem_init(&m);
        if (freopen("/dev/null", "w", stderr) == NULL) {
            _exit(3);
        }
        void *p = mem_alloc(&m, 16, MEM_VALUE);
        mem_free(&m, p, free_size, free_kind);
        _exit(0);
    }
    int status = 0;
    if (pid < 0 || waitpid(pid, &status, 0) != pid) {
        return -1;
    }
    return WIFSIGNALED(status) && WTERMSIG(status) == SIGABRT;
}

TEST(mem_bad_free_aborts) {
    CHECK_EQ(child_aborts(16, MEM_VALUE), 0);   /* the right size and kind */
    CHECK_EQ(child_aborts(17, MEM_VALUE), 1);
    CHECK_EQ(child_aborts(16, MEM_INDEX), 1);
}
#endif

const struct test mem_tests[] = {
    TEST_ENTRY(mem_counts_by_kind),
    TEST_ENTRY(mem_per_database),
    TEST_ENTRY(mem_zalloc_and_zero),
    TEST_ENTRY(mem_realloc),
    TEST_ENTRY(mem_fail_at),
    TEST_ENTRY(mem_too_large),
    TEST_ENTRY(mem_failure_runs),
#ifdef BERGDB_TEST
    TEST_ENTRY(mem_bad_free_aborts),
#endif
    TEST_END
};
