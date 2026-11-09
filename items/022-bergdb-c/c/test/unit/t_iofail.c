/*
 * Failures in storage (bergdb 022-05): Java's StorageFaultTester (harness 6.2 of 018-01,
 * 018-03) in C, its fault of the IO layer, an IOException at the Nth file call, for C's
 * file calls: the test build's I/O seam (plat.h, struct plat_io: the opens of the stream's
 * files, the writes, the forces of files and of the directory, the deletes) makes call N
 * fail, for N = 1, 2, ... until the workload makes fewer calls, on a new database and on
 * one that the first half of the workload made. The workload, through bergdb.h: an open, a
 * retain duration of one second (reclaim's cuts delete the front files), puts of 3,000
 * bytes at 0.1 s apart, a sync every fifth, a get every third, then the close. The checks
 * of 018-03, section 1, that hold in C: after a call that gave BERGDB_FAILED, every later
 * transaction, read and sync gives it too (P7); an open that meets the fault gives
 * BERGDB_IO and leaves nothing open; the close gives BERGDB_IO once the storage has failed,
 * whether a call reported it or not (bergdb.h, bergdb_close; c/readme.md, section 9, point
 * 8), and frees everything; a new open of the directory works, and holds every transaction
 * that a sync confirmed, and a prefix of those executed. The seam's forces do not reach
 * the disk (what a force makes durable is power.sh's part), so that the runs are fast.
 * Java's other faults (an unchecked exception, an Error, interrupts, a stop()) and its
 * stream layer have no counterpart in C (one caller, no thread; a failed allocation is
 * allocfail's, section 10).
 */
#define _DARWIN_C_SOURCE        /* mkdtemp */
#include <dirent.h>
#include <stdlib.h>
#include <unistd.h>
#include "test.h"
#include "bergdb.h"
#include "plat.h"

#ifdef BERGDB_TEST
#define IOF_TRANS 120
#define IOF_VALUE 3000
#define IOF_KEYS 13

/* The seam: call number at (1 is the first) fails, and every call is counted. */
static int64_t iof_calls, iof_at, iof_fired, iof_unlinks;
static char iof_what[32];
/* The kind of each call of a run without a fault (its first letter: o, w, f, d for the
 * directory's force, x for a delete), for the sample. */
#define IOF_MAX_CALLS 400
static char iof_kinds[IOF_MAX_CALLS + 1];

static bool iof_fail(const char *what) {
    if (iof_calls < IOF_MAX_CALLS) {
        iof_kinds[iof_calls] = strcmp(what, "force_dir") == 0 ? 'd'
                : strcmp(what, "delete") == 0 ? 'x' : what[0];
    }
    iof_calls++;
    if (iof_calls == iof_at) {
        iof_fired = iof_calls;
        snprintf(iof_what, sizeof iof_what, "%s", what);
        return true;
    }
    return false;
}

static enum err_code iof_open_rw(const char *path, int *fd, struct err *e) {
    if (iof_fail("open")) {
        return err_set(e, ERR_IO, "IOException", "injected open failure");
    }
    return plat_io_real()->open_rw(path, fd, e);
}

static enum err_code iof_pwrite(int fd, int64_t off, const uint8_t *buf, int64_t n,
        struct err *e) {
    if (iof_fail("write")) {
        return err_set(e, ERR_IO, "IOException", "injected write failure");
    }
    return plat_io_real()->pwrite(fd, off, buf, n, e);
}

static enum err_code iof_force(int fd, enum plat_force_why why, struct err *e) {
    (void) fd;
    (void) why;
    if (iof_fail("force")) {
        return err_set(e, ERR_IO, "IOException", "injected force failure");
    }
    return ERR_OK;          /* not to the disk: the runs' speed */
}

static enum err_code iof_force_dir(const char *dir, struct err *e) {
    (void) dir;
    if (iof_fail("force_dir")) {
        return err_set(e, ERR_IO, "IOException", "injected directory force failure");
    }
    return ERR_OK;
}

static enum err_code iof_unlink(const char *path, struct err *e) {
    if (iof_fail("delete")) {
        return err_set(e, ERR_IO, "IOException", "injected delete failure");
    }
    iof_unlinks++;
    return plat_io_real()->unlink(path, e);
}

static void iof_close(int fd) {
    plat_io_real()->close(fd);
}

static const struct plat_io IOF = {
    iof_open_rw, iof_pwrite, iof_force, iof_force_dir, iof_unlink, iof_close
};

static void iof_options(struct bergdb_options *o, struct bergdb_test_clock *c,
        struct bergdb_mem *m) {
    bergdb_options_init(o);
    o->max_node_size = 8;
    o->startup_distance = 2000;
    o->clock = bergdb_test_clock_time;
    o->clock_ctx = c;
    o->mem = m;
    memcpy(o->id, bergdb_test_id, sizeof o->id);
}

static void iof_value(int i, uint8_t *v) {
    for (int j = 0; j < IOF_VALUE; j++) {
        v[j] = (uint8_t) (i * 7 + j);
    }
    v[0] = (uint8_t) i;
    v[1] = (uint8_t) (i >> 8);
}

static size_t iof_key(int k, uint8_t *b) {
    char ikey[16];
    snprintf(ikey, sizeof ikey, "/k/%d", k);
    size_t n = strlen(ikey);
    bergdb_ikey_to_bkey((const uint8_t *) ikey, n, b);
    return n;
}

/* What a run saw. */
struct iof_run {
    int last_ok;        /* the last transaction that returned BERGDB_OK, -1 for none */
    int synced;         /* the last transaction that a sync confirmed, -1 for none */
    bool failed;        /* a call gave BERGDB_FAILED */
    bool open_failed;   /* the open gave an error */
    int close_rc;
};

/* Transactions from to to - 1 on dir, from an open to the close, with the seam's fault
 * at call 'at' (0: none). */
static void iof_part(const char *dir, struct bergdb_test_clock *c, struct bergdb_mem *m,
        int from, int to, struct iof_run *r) {
    struct bergdb_options o;
    bergdb_db *db;
    char errbuf[BERGDB_ERRBUF_SIZE];
    static uint8_t v[IOF_VALUE];
    iof_options(&o, c, m);
    int rc = bergdb_open(dir, &o, &db, NULL, errbuf);
    if (rc != BERGDB_OK) {
        CHECK(iof_fired > 0);
        CHECK_EQ(rc, BERGDB_IO);
        CHECK(db == NULL);
        CHECK_EQ(m->live_total, 0);
        r->open_failed = true;
        return;
    }
    if (from == 0) {
        rc = bergdb_set_retain_duration(db, BERGDB_UNITS_PER_SEC);
        CHECK(rc == BERGDB_OK || (rc == BERGDB_FAILED && iof_fired > 0));
        r->failed |= rc == BERGDB_FAILED;
    }
    bergdb_read *rd = NULL;
    rc = bergdb_read_new(db, &rd);
    CHECK_EQ(rc, BERGDB_OK);
    for (int i = from; i < to && rd != NULL; i++) {
        uint8_t key[16];
        size_t kl = iof_key(i % IOF_KEYS, key);
        iof_value(i, v);
        bergdb_test_clock_set(c, BERGDB_UNITS_PER_SEC * 10
                + (int64_t) i * BERGDB_UNITS_PER_SEC / 10);
        bergdb_trans *t;
        rc = bergdb_trans_new(db, &t);
        CHECK_EQ(rc, BERGDB_OK);
        if (rc == BERGDB_OK) {
            CHECK_EQ(bergdb_trans_put(t, key, kl, v, IOF_VALUE), BERGDB_OK);
            rc = bergdb_execute(db, t, NULL);
            bergdb_trans_free(t);
        }
        if (r->failed) {
            CHECK_EQ(rc, BERGDB_FAILED);        /* P7 */
        } else if (rc == BERGDB_OK) {
            r->last_ok = i;
        } else {
            CHECK_EQ(rc, BERGDB_FAILED);
            CHECK(iof_fired > 0);
            r->failed = true;
        }
        if (i % 5 == 4) {
            rc = bergdb_sync(db, 0, BERGDB_SYNC_ORDINARY);
            if (r->failed) {
                CHECK_EQ(rc, BERGDB_FAILED);
            } else if (rc == BERGDB_OK) {
                r->synced = r->last_ok;
            } else {
                CHECK_EQ(rc, BERGDB_FAILED);
                CHECK(iof_fired > 0);
                r->failed = true;
            }
        }
        if (i % 3 == 2) {
            struct bergdb_one one;
            rc = bergdb_get_one(db, rd, BERGDB_LATEST, key, kl, &one);
            if (r->failed) {
                CHECK_EQ(rc, BERGDB_FAILED);
            } else {
                CHECK_EQ(rc, BERGDB_OK);
                CHECK(rc != BERGDB_OK || (one.value != NULL && one.value_len == IOF_VALUE
                        && memcmp(one.value, v, IOF_VALUE) == 0));
            }
        }
    }
    bergdb_read_free(rd);
    r->close_rc = bergdb_close(db);
    CHECK_EQ(m->live_total, 0);
}

/* A new open of dir with no fault: it opens, and holds the state after a prefix of the
 * transactions, of at least synced + 1 and at most last + 2 of them (the transaction that
 * failed after its go point may be in, c/readme.md, section 9, point 8). Then a
 * transaction more is taken. */
static void iof_check(const char *dir, struct bergdb_test_clock *c, int synced, int last,
        int64_t at) {
    struct bergdb_mem m = {0};
    struct bergdb_options o;
    bergdb_db *db;
    char errbuf[BERGDB_ERRBUF_SIZE];
    static uint8_t v[IOF_VALUE];
    iof_options(&o, c, &m);
    int rc = bergdb_open(dir, &o, &db, NULL, errbuf);
    CHECK_EQ(rc, BERGDB_OK);
    if (rc != BERGDB_OK) {
        printf("    fault at call %lld (%s): the open after it: %s\n", (long long) at, iof_what,
                errbuf);
        return;
    }
    bergdb_read *rd;
    REQUIRE(bergdb_read_new(db, &rd) == BERGDB_OK);
    int found[IOF_KEYS];
    int n = -1;         /* the last transaction found */
    for (int k = 0; k < IOF_KEYS; k++) {
        uint8_t key[16];
        size_t kl = iof_key(k, key);
        struct bergdb_one one;
        CHECK_EQ(bergdb_get_one(db, rd, BERGDB_LATEST, key, kl, &one), BERGDB_OK);
        found[k] = -1;
        if (one.value != NULL) {
            CHECK_EQ((int64_t) one.value_len, IOF_VALUE);
            found[k] = one.value[0] | one.value[1] << 8;
            iof_value(found[k], v);
            CHECK(memcmp(one.value, v, IOF_VALUE) == 0);
            CHECK_EQ(found[k] % IOF_KEYS, k);
            n = found[k] > n ? found[k] : n;
        }
    }
    /* A prefix: each key holds its last value of transactions 0 to n. */
    bool prefix = true;
    for (int k = 0; k < IOF_KEYS; k++) {
        int want = n - (n - k + IOF_KEYS * 1000) % IOF_KEYS;
        prefix = prefix && found[k] == (want >= 0 ? want : -1);
    }
    CHECK(prefix);
    CHECK(n >= synced);
    CHECK(n <= last + 1);
    if (!prefix || n < synced || n > last + 1) {
        printf("    fault at call %lld (%s): found up to %d, synced %d, last %d\n",
                (long long) at, iof_what, n, synced, last);
    }
    bergdb_read_free(rd);
    bergdb_trans *t;
    REQUIRE(bergdb_trans_new(db, &t) == BERGDB_OK);
    uint8_t key[16];
    size_t kl = iof_key(0, key);
    bergdb_test_clock_set(c, c->time + BERGDB_UNITS_PER_SEC);
    CHECK_EQ(bergdb_trans_put(t, key, kl, v, 10), BERGDB_OK);
    CHECK_EQ(bergdb_execute(db, t, NULL), BERGDB_OK);
    bergdb_trans_free(t);
    CHECK_EQ(bergdb_close(db), BERGDB_OK);
    CHECK_EQ(m.live_total, 0);
}

/* Removes dir and its files (it has no subdirectory). */
static void iof_remove_dir(const char *dir) {
    DIR *d = opendir(dir);
    struct dirent *x;
    char path[700];
    while (d != NULL && (x = readdir(d)) != NULL) {
        if (strcmp(x->d_name, ".") != 0 && strcmp(x->d_name, "..") != 0) {
            snprintf(path, sizeof path, "%s/%s", dir, x->d_name);
            unlink(path);
        }
    }
    if (d != NULL) {
        closedir(d);
    }
    CHECK(rmdir(dir) == 0);
}

/* One run: the fault at call 'at' (0: none) of the workload's second half on a reopened
 * database, or of the whole on a new one. Returns the calls that the faulted part made. */
static int64_t iof_one(int64_t at, bool reopened, int64_t *unlinks) {
    char dir[512];
    const char *tmp = getenv("TMPDIR");
    struct bergdb_test_clock c = {0};
    struct bergdb_mem m = {0};
    struct iof_run r = { -1, -1, false, false, BERGDB_OK };
    snprintf(dir, sizeof dir, "%s/bergdb-t_iofail-XXXXXX", tmp != NULL ? tmp : "/tmp");
    if (mkdtemp(dir) == NULL) {
        CHECK(false);
        return 0;
    }
    iof_calls = iof_at = iof_fired = iof_unlinks = 0;
    iof_what[0] = '\0';
    plat_io_set(&IOF);
    int from = 0;
    if (reopened) {
        iof_part(dir, &c, &m, 0, IOF_TRANS / 2, &r);
        CHECK_EQ(r.close_rc, BERGDB_OK);
        CHECK(!r.failed);
        r.synced = r.last_ok;           /* the close syncs */
        from = IOF_TRANS / 2;
    }
    iof_calls = 0;
    iof_at = at;
    iof_part(dir, &c, &m, from, IOF_TRANS, &r);
    const int64_t calls = iof_calls;
    if (!r.open_failed) {
        if (iof_fired > 0) {
            CHECK_EQ(r.close_rc, BERGDB_IO);
            if (r.close_rc != BERGDB_IO) {
                printf("    fault at call %lld (%s)%s: the close gave %s\n", (long long) at,
                        iof_what, reopened ? ", reopened" : "", bergdb_errname(r.close_rc));
            }
        } else {
            CHECK_EQ(r.close_rc, BERGDB_OK);
            CHECK(!r.failed);
            r.synced = r.last_ok;
        }
    }
    *unlinks = iof_unlinks;
    iof_at = 0;             /* the seam stays, with no fault: the check's forces are no-ops */
    iof_check(dir, &c, r.synced, r.last_ok, at);
    plat_io_set(NULL);
    iof_remove_dir(dir);
    return calls;
}

/* True if call 'at' (1 is the first) of the reference run is in the sample: the first and
 * the last call of each kind, and every tenth; every call with BERGDB_IOFAIL_ALL set. */
static bool iof_sampled(int64_t at, int64_t calls, const char *kinds) {
    if (getenv("BERGDB_IOFAIL_ALL") != NULL || at % 10 == 0 || at > IOF_MAX_CALLS) {
        return true;
    }
    const char k = kinds[at - 1];
    bool first = true, last = true;
    for (int64_t i = 1; i < at; i++) {
        first = first && kinds[i - 1] != k;
    }
    for (int64_t i = at + 1; i <= calls && i <= IOF_MAX_CALLS; i++) {
        last = last && kinds[i - 1] != k;
    }
    return first || last;
}
#endif

/* StorageFaultTester.testSample, its IO layer: a fault at file calls in turn, of a new
 * database and of a reopened one (the calls of the second half): a sample, the first and
 * the last call of each kind and every tenth (every call with BERGDB_IOFAIL_ALL set in the
 * environment: about 120 runs, 12 s under load). The workload's reclaim deletes a front
 * file, so that a delete and the directory's force after it fail too. Before the fix of
 * stream_flush (bergdb 022-05), a force that failed in a sync left the database's later
 * syncs and its close to force the files again: they gave BERGDB_OK, not BERGDB_FAILED and
 * BERGDB_IO; and so after a failed cut (a delete, or the directory's force after it). */
TEST(iofail_each_call) {
#ifdef BERGDB_TEST
    static char kinds[IOF_MAX_CALLS + 1];
    for (int reopened = 0; reopened < 2; reopened++) {
        int64_t unlinks;
        memset(iof_kinds, 0, sizeof iof_kinds);
        const int64_t calls = iof_one(0, reopened, &unlinks);
        memcpy(kinds, iof_kinds, sizeof kinds);
        CHECK(calls > 10);
        CHECK(unlinks > 0);
        CHECK(strchr(kinds, 'o') != NULL && strchr(kinds, 'w') != NULL
                && strchr(kinds, 'f') != NULL && strchr(kinds, 'd') != NULL
                && strchr(kinds, 'x') != NULL);
        int runs = 0;
        for (int64_t at = 1; at <= calls; at++) {
            if (iof_sampled(at, calls, kinds)) {
                int64_t u;
                iof_one(at, reopened, &u);
                runs++;
            }
        }
        printf("  iofail_each_call: %s database: %lld file calls (%s), %d made to fail\n",
                reopened ? "a reopened" : "a new", (long long) calls, kinds, runs);
    }
#endif
}

const struct test iofail_tests[] = {
    TEST_ENTRY(iofail_each_call),
    TEST_END
};
