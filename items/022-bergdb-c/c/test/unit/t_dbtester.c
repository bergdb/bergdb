/* Java's tests of Db through bergdb.h (bergdb 022-05, db-tester): DbTester's
 * tests of results (puts, deletes and reads at times, keys long and short,
 * splits, the STM, crashes at chosen positions, getTrans, and, through
 * db.h, the record limit lowered), DbTesterJavadoc's of what Db's Javadoc
 * promises, and DbTesterFailure's of reads that fail on the storage, each
 * ported where C has what it tests; 022-05's db-tester part lists every
 * test of those classes and what C has for it. A database is Java's
 * DbBuilder.testSetup(): the test clock, no eviction, the test id, in
 * memory; in a directory where a test restarts it or changes its files.
 * Where Java draws with java.util.Random, test_random draws the same kind
 * of input. */
#define _DARWIN_C_SOURCE        /* mkdtemp */
#include <dirent.h>
#include <stdarg.h>
#include <stdlib.h>
#include <sys/stat.h>
#include <unistd.h>
#include "test.h"
#include "bergdb.h"
#include "checksum.h"
#include "db.h"
#include "keys.h"
#include "rstream.h"
#include "sdb.h"
#include "stream.h"
#include "trans.h"

#define KMAX 256
#define D_META 200000           /* RecoverableStream.META_BLOCK_DISTANCE */
#define CREATION_LENGTH 264     /* Db.CREATION_LENGTH */

/* ======== A database ======== */

struct tdb {
    bergdb_db *db;
    bergdb_read *rd;
    struct bergdb_test_clock clock;
    struct bergdb_mem m;
    struct bergdb_options o;
    char dir[512];          /* "" for a database in memory */
};

/* DbBuilder.testSetup(): node size and startup distance as given, 0 for
 * the defaults (30 and 50,000,000). */
static void tdb_init(struct tdb *x, int32_t node, int32_t sd) {
    memset(x, 0, sizeof *x);
    bergdb_options_init(&x->o);
    x->o.clock = bergdb_test_clock_time;
    x->o.clock_ctx = &x->clock;
    memcpy(x->o.id, bergdb_test_id, BERGDB_ID_SIZE);
    x->o.cache_size_indicator = BERGDB_NO_EVICT;
    if (node != 0) {
        x->o.max_node_size = node;
    }
    if (sd != 0) {
        x->o.startup_distance = sd;
    }
    x->o.mem = &x->m;
}

/* start(): opens the database, and a read context. */
static int tdb_start(struct tdb *x) {
    char errbuf[BERGDB_ERRBUF_SIZE];
    int rc = bergdb_open(x->dir[0] != '\0' ? x->dir : NULL, &x->o, &x->db, NULL, errbuf);
    if (rc == BERGDB_OK) {
        rc = bergdb_read_new(x->db, &x->rd);
    }
    return rc;
}

/* close(): nothing of the database's memory is left. */
static int tdb_close(struct tdb *x) {
    bergdb_read_free(x->rd);
    x->rd = NULL;
    int rc = bergdb_close(x->db);
    x->db = NULL;
    CHECK_EQ(x->m.live_total, 0);
    return rc;
}

/* A new database in memory (dir false) or in a new directory. */
static bool tdb_new(struct tdb *x, int32_t node, int32_t sd, bool dir) {
    tdb_init(x, node, sd);
    if (dir) {
        const char *tmp = getenv("TMPDIR");
        snprintf(x->dir, sizeof x->dir, "%s/bergdb-t_dbtester-XXXXXX",
                tmp != NULL ? tmp : "/tmp");
        if (mkdtemp(x->dir) == NULL) {
            return false;
        }
    }
    return tdb_start(x) == BERGDB_OK;
}

static void remove_dir(const char *dir) {
    DIR *d = opendir(dir);
    if (d == NULL) {
        return;
    }
    struct dirent *e;
    char path[1024];
    while ((e = readdir(d)) != NULL) {
        if (e->d_name[0] != '.') {
            snprintf(path, sizeof path, "%s/%s", dir, e->d_name);
            unlink(path);
        }
    }
    closedir(d);
    rmdir(dir);
}

/* A new empty directory, for copies of a stream. */
static bool new_dir(char *out, size_t cap) {
    const char *tmp = getenv("TMPDIR");
    snprintf(out, cap, "%s/bergdb-t_dbtester-XXXXXX", tmp != NULL ? tmp : "/tmp");
    return mkdtemp(out) != NULL;
}

/* An ikey's bkey (Keys.toBytes(String)); its length. */
static size_t bk(const char *ikey, uint8_t *out) {
    size_t n = strlen(ikey);
    if (bergdb_ikey_to_bkey((const uint8_t *) ikey, n, out) != BERGDB_OK) {
        return 0;
    }
    return n;
}

/*
 * A transaction at the clock's time: ("p", ikey, value) puts, ("d", ikey)
 * deletes, ended by NULL (Trans.Builder's put(String, String) and
 * delete(String)). Its result in *ex if ex is not NULL.
 */
static int tx(struct tdb *x, struct bergdb_executed *ex, ...) {
    bergdb_trans *t;
    int rc = bergdb_trans_new(x->db, &t);
    if (rc != BERGDB_OK) {
        return rc;
    }
    va_list ap;
    va_start(ap, ex);
    const char *op;
    while (rc == BERGDB_OK && (op = va_arg(ap, const char *)) != NULL) {
        uint8_t b[KMAX];
        size_t n = bk(va_arg(ap, const char *), b);
        if (op[0] == 'p') {
            const char *v = va_arg(ap, const char *);
            rc = bergdb_trans_put(t, b, n, (const uint8_t *) v, strlen(v));
        } else {
            rc = bergdb_trans_delete(t, b, n);
        }
    }
    va_end(ap);
    if (rc == BERGDB_OK) {
        rc = bergdb_execute(x->db, t, ex);
    }
    bergdb_trans_free(t);
    return rc;
}

/* A transaction of one put of bytes, by bkey. */
static int put_b(struct tdb *x, const uint8_t *key, size_t kn, const uint8_t *v, size_t vn,
        struct bergdb_executed *ex) {
    bergdb_trans *t;
    int rc = bergdb_trans_new(x->db, &t);
    if (rc == BERGDB_OK) {
        rc = bergdb_trans_put(t, key, kn, v, vn);
    }
    if (rc == BERGDB_OK) {
        rc = bergdb_execute(x->db, t, ex);
    }
    bergdb_trans_free(t);
    return rc;
}

/* Sets the test clock, as CoreTestClock.setTime. */
static void at(struct tdb *x, int64_t time) {
    CHECK_EQ(bergdb_test_clock_set(&x->clock, time), BERGDB_OK);
}

/* DbUtil.get(db, time, ikey) equals want, as a string; want NULL: no value. */
static bool get_is(struct tdb *x, int64_t time, const char *ikey, const char *want) {
    uint8_t b[KMAX];
    size_t n = bk(ikey, b);
    struct bergdb_one one;
    if (n == 0 || bergdb_get_one(x->db, x->rd, time, b, n, &one) != BERGDB_OK) {
        return false;
    }
    if (want == NULL) {
        return one.value == NULL;
    }
    return one.value != NULL && one.value_len == strlen(want)
            && memcmp(one.value, want, one.value_len) == 0;
}

static int64_t db_length(struct tdb *x) {
    struct bergdb_stats s;
    if (bergdb_stats(x->db, &s) != BERGDB_OK) {
        return -1;
    }
    return s.stream_length;
}

/* ======== The stream's files ======== */

#define MAXF 64

/* A directory's stream: its .bergdb files, in the order of their names. */
struct files {
    int n;
    char name[MAXF][32];
    uint8_t *bytes[MAXF];
    int64_t len[MAXF];
};

static int name_cmp(const void *a, const void *b) {
    return strcmp((const char *) a, (const char *) b);
}

static bool files_read(const char *dir, struct files *f) {
    f->n = 0;
    DIR *d = opendir(dir);
    if (d == NULL) {
        return false;
    }
    struct dirent *e;
    while ((e = readdir(d)) != NULL && f->n < MAXF) {
        size_t l = strlen(e->d_name);
        if (l > 7 && l < 32 && strcmp(e->d_name + l - 7, ".bergdb") == 0) {
            strcpy(f->name[f->n++], e->d_name);
        }
    }
    closedir(d);
    qsort(f->name, (size_t) f->n, sizeof f->name[0], name_cmp);
    for (int i = 0; i < f->n; i++) {
        char path[1024];
        snprintf(path, sizeof path, "%s/%s", dir, f->name[i]);
        FILE *fp = fopen(path, "rb");
        f->bytes[i] = NULL;
        f->len[i] = 0;
        if (fp == NULL) {
            return false;
        }
        fseek(fp, 0, SEEK_END);
        long size = ftell(fp);
        fseek(fp, 0, SEEK_SET);
        f->bytes[i] = malloc(size > 0 ? (size_t) size : 1);
        f->len[i] = (int64_t) fread(f->bytes[i], 1, (size_t) size, fp);
        fclose(fp);
    }
    return f->n > 0;
}

static void files_free(struct files *f) {
    for (int i = 0; i < f->n; i++) {
        free(f->bytes[i]);
    }
    f->n = 0;
}

/* The byte at a stream position, or NULL. */
static uint8_t *files_at(struct files *f, int64_t pos) {
    for (int i = 0; i < f->n; i++) {
        if (pos < f->len[i]) {
            return f->bytes[i] + pos;
        }
        pos -= f->len[i];
    }
    return NULL;
}

/* Writes the stream into dir cut at 'cut' bytes, as a crash leaves it: the
 * files before the cut, the one it ends in cut short, none after it. */
static bool files_write(const char *dir, const struct files *f, int64_t cut) {
    int64_t start = 0;
    for (int i = 0; i < f->n; i++) {
        char path[1024];
        snprintf(path, sizeof path, "%s/%s", dir, f->name[i]);
        if (start >= cut && i > 0) {
            unlink(path);
            continue;
        }
        int64_t n = f->len[i] < cut - start ? f->len[i] : cut - start;
        FILE *fp = fopen(path, "wb");
        if (fp == NULL) {
            return false;
        }
        if (n > 0 && fwrite(f->bytes[i], 1, (size_t) n, fp) != (size_t) n) {
            fclose(fp);
            return false;
        }
        fclose(fp);
        start += f->len[i];
    }
    return true;
}

/* ======== DbTester: results ======== */

/* DbTester.test1: no value for a key never put. */
TEST(dbt_test1) {
    struct tdb x;
    REQUIRE(tdb_new(&x, 0, 0, false));
    CHECK(get_is(&x, 99, "admin1", NULL));
    tdb_close(&x);
}

/* DbTester.test2 and test3: one put, two puts in one transaction. */
TEST(dbt_test2_and_test3) {
    struct tdb x;
    REQUIRE(tdb_new(&x, 0, 0, false));
    CHECK_EQ(tx(&x, NULL, "p", "admin1", "F", NULL), BERGDB_OK);
    CHECK(get_is(&x, 99, "admin1", "F"));
    tdb_close(&x);
    REQUIRE(tdb_new(&x, 0, 0, false));
    CHECK_EQ(tx(&x, NULL, "p", "admin1", "F1", "p", "admin2", "F2", NULL), BERGDB_OK);
    CHECK(get_is(&x, 99, "admin1", "F1"));
    CHECK(get_is(&x, 99, "admin2", "F2"));
    tdb_close(&x);
}

/* DbTester.test4: two transactions at 100 and 200. */
TEST(dbt_test4) {
    struct tdb x;
    REQUIRE(tdb_new(&x, 0, 0, false));
    at(&x, 100);
    CHECK_EQ(tx(&x, NULL, "p", "admin1", "F1", NULL), BERGDB_OK);
    at(&x, 200);
    CHECK_EQ(tx(&x, NULL, "p", "admin2", "F2", NULL), BERGDB_OK);
    CHECK(get_is(&x, BERGDB_LATEST, "admin1", "F1"));
    CHECK(get_is(&x, BERGDB_LATEST, "admin2", "F2"));
    tdb_close(&x);
}

/* DbTester.createT2DB: eight keys, some the prefix of another. */
static bool t2_db(struct tdb *x) {
    if (!tdb_new(x, 0, 0, false)) {
        return false;
    }
    return tx(x, NULL, "p", "ap", "P0", "p", "apa", "P1", "p", "d", "P2", "p", "g", "P3",
            "p", "kr", "P4", "p", "kram", "P5", "p", "mage", "P6", "p", "md", "P7", NULL)
            == BERGDB_OK;
}

/* DbTester.testT2, testVersions and testVersionsReplaceValue. */
TEST(dbt_t2_and_versions) {
    struct tdb x;
    REQUIRE(t2_db(&x));
    CHECK(get_is(&x, 999, "apa", "P1"));
    CHECK(get_is(&x, 999, "ap", "P0"));
    CHECK(get_is(&x, 999, "md", "P7"));
    at(&x, 20);
    struct bergdb_executed ex;
    CHECK_EQ(tx(&x, &ex, "p", "e", "e-value", NULL), BERGDB_OK);
    CHECK(ex.tt >= 20);
    CHECK(get_is(&x, 999, "e", "e-value"));
    CHECK(get_is(&x, 10, "e", NULL));
    tdb_close(&x);
    REQUIRE(t2_db(&x));
    at(&x, 20);
    CHECK_EQ(tx(&x, NULL, "p", "apa", "A", NULL), BERGDB_OK);
    CHECK(get_is(&x, 30, "apa", "A"));
    CHECK(get_is(&x, 999, "apa", "A"));
    CHECK(get_is(&x, 19, "apa", "P1"));
    tdb_close(&x);
}

#define LONGER "anotherKeyThatIsLongerThanThePreviousAndIndeedVeryLong"

/* DbTester.testLongKey, testLongerKey, testMultipleLongKeys,
 * testLongAndShortKeys, testMultipleKeysWithSamePrefix, testGet2,
 * testGetWithLongerKey and testGetWithLongAndShortKeys: keys of one to
 * eight segments, absent keys beside them. */
TEST(dbt_long_keys) {
    struct tdb x;
    REQUIRE(tdb_new(&x, 0, 0, false));
    CHECK_EQ(tx(&x, NULL, "p", "myLongerKey", "v1", NULL), BERGDB_OK);
    CHECK(get_is(&x, 99, "rKey", NULL));
    CHECK(get_is(&x, 99, "myLongerKey", "v1"));
    CHECK_EQ(tx(&x, NULL, "p", LONGER, "v2", NULL), BERGDB_OK);
    CHECK(get_is(&x, 99, LONGER, "v2"));
    CHECK(get_is(&x, 99, "myLongerX", NULL));
    tdb_close(&x);

    REQUIRE(tdb_new(&x, 0, 0, false));
    at(&x, 10);
    CHECK_EQ(tx(&x, NULL, "p", "myLongerKey", "v1", "p", "nash", "v2", NULL), BERGDB_OK);
    const char *absent[] = { "myLongerX", "anotherX", "nas", "nasher" };
    for (int i = 0; i < 4; i++) {
        CHECK(get_is(&x, 20, absent[i], NULL));
    }
    CHECK(get_is(&x, 20, "myLongerKey", "v1"));
    CHECK(get_is(&x, 20, "nash", "v2"));
    tdb_close(&x);

    REQUIRE(tdb_new(&x, 0, 0, false));
    CHECK_EQ(tx(&x, NULL, "p", "myLongerKey1", "v1", "p", "myLongerKey2", "v2", NULL),
            BERGDB_OK);
    CHECK(get_is(&x, 30, "myLongerKey1", "v1"));
    CHECK(get_is(&x, 30, "myLongerKey2", "v2"));
    CHECK(get_is(&x, 30, "myLongerX", NULL));
    CHECK(get_is(&x, 30, "myLongerKey1b", NULL));
    CHECK_EQ(tx(&x, NULL, "p", "longerKey", "v", NULL), BERGDB_OK);
    CHECK(get_is(&x, BERGDB_LATEST, "longerKey", "v"));
    tdb_close(&x);
}

/* DbTester.testDelete0 and testDelete1: a value deleted and put again,
 * read at every time between. */
TEST(dbt_delete) {
    struct tdb x;
    REQUIRE(tdb_new(&x, 0, 0, false));
    at(&x, 10);
    CHECK_EQ(tx(&x, NULL, "p", "a", "a-value", "p", "b", "b-value", NULL), BERGDB_OK);
    at(&x, 20);
    CHECK_EQ(tx(&x, NULL, "d", "a", NULL), BERGDB_OK);
    CHECK(get_is(&x, 30, "a", NULL));
    CHECK(get_is(&x, 30, "b", "b-value"));
    CHECK(get_is(&x, 15, "a", "a-value"));
    at(&x, 30);
    CHECK_EQ(tx(&x, NULL, "p", "a", "a-value-2", NULL), BERGDB_OK);
    at(&x, 40);
    CHECK_EQ(tx(&x, NULL, "d", "a", NULL), BERGDB_OK);
    at(&x, 50);
    CHECK_EQ(tx(&x, NULL, "p", "a", "a-value-3", NULL), BERGDB_OK);
    CHECK(get_is(&x, BERGDB_LATEST, "a", "a-value-3"));
    CHECK(get_is(&x, 5, "a", NULL));
    CHECK(get_is(&x, 15, "a", "a-value"));
    CHECK(get_is(&x, 25, "a", NULL));
    CHECK(get_is(&x, 35, "a", "a-value-2"));
    CHECK(get_is(&x, 45, "a", NULL));
    CHECK(get_is(&x, 55, "a", "a-value-3"));
    tdb_close(&x);
}

/* DbTester.testDeleteOfNonExistingData0 and 1: deletes of keys without a
 * value change nothing; a delete repeated. */
TEST(dbt_delete_of_non_existing_data) {
    struct tdb x;
    REQUIRE(tdb_new(&x, 0, 0, false));
    at(&x, 10);
    CHECK_EQ(tx(&x, NULL, "d", "a", NULL), BERGDB_OK);
    CHECK(get_is(&x, BERGDB_LATEST, "a", NULL));
    at(&x, 11);
    CHECK_EQ(tx(&x, NULL, "p", "a", "a-value", "p", "b", "b-value", NULL), BERGDB_OK);
    at(&x, 20);
    CHECK_EQ(tx(&x, NULL, "d", "c", NULL), BERGDB_OK);
    CHECK_EQ(tx(&x, NULL, "d", "anton", NULL), BERGDB_OK);
    CHECK_EQ(tx(&x, NULL, "d", "anton-and-all-his-friends", NULL), BERGDB_OK);
    CHECK(get_is(&x, BERGDB_LATEST, "a", "a-value"));
    CHECK(get_is(&x, BERGDB_LATEST, "b", "b-value"));
    for (int i = 0; i < 3; i++) {
        CHECK_EQ(tx(&x, NULL, "d", "a", NULL), BERGDB_OK);
    }
    CHECK(get_is(&x, BERGDB_LATEST, "a", NULL));
    CHECK(get_is(&x, BERGDB_LATEST, "b", "b-value"));
    tdb_close(&x);
}

/* A transfer of DbTester.testRerun: puts with a read set at a lookup time. */
static int transfer(struct tdb *x, int64_t lookup, const char *v1, const char *v2) {
    bergdb_trans *t;
    uint8_t b[KMAX];
    size_t n;
    int rc = bergdb_trans_new(x->db, &t);
    if (rc != BERGDB_OK) {
        return rc;
    }
    rc = bergdb_trans_lookup_time(t, lookup);
    n = bk("acc1", b);
    if (rc == BERGDB_OK) rc = bergdb_trans_key_read(t, b, n);
    if (rc == BERGDB_OK) rc = bergdb_trans_put(t, b, n, (const uint8_t *) v1, strlen(v1));
    n = bk("acc2", b);
    if (rc == BERGDB_OK) rc = bergdb_trans_key_read(t, b, n);
    if (rc == BERGDB_OK) rc = bergdb_trans_put(t, b, n, (const uint8_t *) v2, strlen(v2));
    if (rc == BERGDB_OK) rc = bergdb_execute(x->db, t, NULL);
    bergdb_trans_free(t);
    return rc;
}

/* DbTester.testRerun: a read set written after its lookup time is refused
 * (RerunException), and nothing changes; a later lookup time runs. */
TEST(dbt_rerun) {
    struct tdb x;
    REQUIRE(tdb_new(&x, 0, 0, false));
    at(&x, 10);
    CHECK_EQ(tx(&x, NULL, "p", "acc1", "200", "p", "acc2", "100", NULL), BERGDB_OK);
    at(&x, 20);
    CHECK_EQ(tx(&x, NULL, "p", "acc1", "50", NULL), BERGDB_OK);
    at(&x, 30);
    CHECK(get_is(&x, 11, "acc1", "200"));
    CHECK(get_is(&x, 11, "acc2", "100"));
    int64_t len = db_length(&x);
    CHECK_EQ(transfer(&x, 11, "100", "200"), BERGDB_RERUN);
    CHECK(strncmp(bergdb_errmsg(x.db), "RerunException", 14) == 0);
    CHECK_EQ(db_length(&x), len);
    CHECK(get_is(&x, BERGDB_LATEST, "acc1", "50"));
    CHECK_EQ(transfer(&x, 21, "199", "101"), BERGDB_OK);
    CHECK(get_is(&x, BERGDB_LATEST, "acc1", "199"));
    CHECK(get_is(&x, BERGDB_LATEST, "acc2", "101"));
    tdb_close(&x);
}

/* DbTester.testSame7BytesPrefix, testGetSmallerKey, testGet1,
 * testManyKeysInOneTransaction and testGetBeforeFirstSet. */
TEST(dbt_small_cases) {
    struct tdb x;
    REQUIRE(tdb_new(&x, 0, 0, false));
    CHECK_EQ(tx(&x, NULL, "p", "account1", "1", "p", "account2", "2", NULL), BERGDB_OK);
    CHECK(get_is(&x, BERGDB_LATEST, "account1", "1"));
    CHECK(get_is(&x, BERGDB_LATEST, "account2", "2"));
    CHECK(get_is(&x, 20, "account0", NULL));
    CHECK_EQ(tx(&x, NULL, "p", "k", "v", NULL), BERGDB_OK);
    CHECK(get_is(&x, 999, "k", "v"));
    tdb_close(&x);

    REQUIRE(tdb_new(&x, 0, 0, false));
    bergdb_trans *t;
    REQUIRE(bergdb_trans_new(x.db, &t) == BERGDB_OK);
    for (int i = 0; i < 15; i++) {
        char k[32], v[16];
        uint8_t b[KMAX];
        snprintf(k, sizeof k, "admin-account-%d", i);
        snprintf(v, sizeof v, "v%d", i);
        size_t n = bk(k, b);
        CHECK_EQ(bergdb_trans_put(t, b, n, (const uint8_t *) v, strlen(v)), BERGDB_OK);
    }
    CHECK_EQ(bergdb_execute(x.db, t, NULL), BERGDB_OK);
    bergdb_trans_free(t);
    CHECK(get_is(&x, BERGDB_LATEST, "admin-account-5", "v5"));
    CHECK(get_is(&x, BERGDB_LATEST, "admin-account-14", "v14"));
    CHECK(get_is(&x, BERGDB_LATEST, "admin-account-0", "v0"));
    tdb_close(&x);

    REQUIRE(tdb_new(&x, 0, 0, false));
    at(&x, 10);
    CHECK_EQ(tx(&x, NULL, "p", "first", "f", NULL), BERGDB_OK);
    CHECK(get_is(&x, 99, "first", "f"));
    CHECK(get_is(&x, 5, "first", NULL));
    tdb_close(&x);
}

/* DbTester's getKey: "01" to "09", then "10" and up. */
static void key2(int i, char *out, size_t cap, const char *prefix) {
    snprintf(out, cap, "%s%s%d", prefix, i < 10 ? "0" : "", i);
}

/* Puts prefix + key2(i) = "v" + i for i in from..to (step -1 or 1) in one
 * transaction at the clock's time. */
static int put_range(struct tdb *x, const char *prefix, int from, int to) {
    bergdb_trans *t;
    int rc = bergdb_trans_new(x->db, &t);
    int step = from <= to ? 1 : -1;
    for (int i = from; rc == BERGDB_OK; i += step) {
        char k[64], v[16];
        uint8_t b[KMAX];
        key2(i, k, sizeof k, prefix);
        snprintf(v, sizeof v, "v%d", i);
        size_t n = bk(k, b);
        rc = bergdb_trans_put(t, b, n, (const uint8_t *) v, strlen(v));
        if (i == to) {
            break;
        }
    }
    if (rc == BERGDB_OK) {
        rc = bergdb_execute(x->db, t, NULL);
    }
    bergdb_trans_free(t);
    return rc;
}

static bool range_is(struct tdb *x, int64_t time, const char *prefix, int from, int to) {
    bool ok = true;
    for (int i = from; i <= to; i++) {
        char k[64], v[16];
        key2(i, k, sizeof k, prefix);
        snprintf(v, sizeof v, "v%d", i);
        ok = ok && get_is(x, time, k, v);
    }
    return ok;
}

/* DbTester's splits: testSplit0 (time splits, node size 14), testSplit1,
 * testSpaceSplit1 (node size 8), testSplitInSingleTransaction,
 * testSplitTwoSplitsInOneTransaction, testSpaceSplitAddBackwards,
 * testSpaceSplitOfRoot and testTimeSplitOfRoot (whose check of the super
 * root's rootTime is the index's, not the API's). */
TEST(dbt_splits) {
    struct tdb x;
    char k[64], v[16];
    REQUIRE(tdb_new(&x, 14, 0, false));                     /* testSplit0 */
    for (int i = 0; i < 10; i++) {
        snprintf(k, sizeof k, "account-id-%d", i);
        snprintf(v, sizeof v, "v%d", i);
        at(&x, 1 + i);
        CHECK_EQ(tx(&x, NULL, "p", k, v, NULL), BERGDB_OK);
    }
    for (int i = 0; i < 10; i++) {
        snprintf(k, sizeof k, "account-id-%d", i);
        snprintf(v, sizeof v, "v%d", i);
        CHECK(get_is(&x, 999, k, v));
    }
    CHECK_EQ(bergdb_debug_check(x.db), BERGDB_OK);
    tdb_close(&x);

    REQUIRE(tdb_new(&x, 14, 0, false));                     /* testSplit1 */
    for (int time = 100; time < 200; time += 10) {
        snprintf(k, sizeof k, "k%d", time);
        snprintf(v, sizeof v, "v%d", time);
        at(&x, time);
        CHECK_EQ(tx(&x, NULL, "p", k, v, NULL), BERGDB_OK);
    }
    for (int time = 100; time < 200; time += 10) {
        snprintf(k, sizeof k, "k%d", time);
        snprintf(v, sizeof v, "v%d", time);
        CHECK(get_is(&x, 999, k, v));
    }
    tdb_close(&x);

    REQUIRE(tdb_new(&x, 8, 0, false));                      /* testSpaceSplit1 */
    for (int i = 100; i < 105; i++) {
        snprintf(k, sizeof k, "admin-accounts-%d", i);
        snprintf(v, sizeof v, "v%d", i);
        at(&x, i);
        CHECK_EQ(tx(&x, NULL, "p", k, v, NULL), BERGDB_OK);
    }
    CHECK(get_is(&x, 101, "admin-accounts-100", "v100"));
    CHECK(get_is(&x, 103, "admin-accounts-100", "v100"));
    CHECK(get_is(&x, 104, "admin-accounts-100", "v100"));
    for (int i = 100; i < 105; i++) {
        snprintf(k, sizeof k, "admin-accounts-%d", i);
        snprintf(v, sizeof v, "v%d", i);
        CHECK(get_is(&x, 199, k, v));
    }
    CHECK_EQ(bergdb_debug_check(x.db), BERGDB_OK);
    tdb_close(&x);

    /* In one transaction: 10 and 15 keys at node size 14, 11 backwards at
     * node size 8, the root split. */
    const struct { int node, from, to; const char *prefix; } one[] = {
        { 14, 0, 9, "admin-accounts-" }, { 14, 0, 14, "admin-accounts-" },
        { 8, 10, 0, "admin-accounts-" }, { 8, 10, 0, "k-" } };
    for (int c = 0; c < 4; c++) {
        REQUIRE(tdb_new(&x, one[c].node, 0, false));
        at(&x, 10);
        CHECK_EQ(put_range(&x, one[c].prefix, one[c].from, one[c].to), BERGDB_OK);
        int lo = one[c].from < one[c].to ? one[c].from : one[c].to;
        int hi = one[c].from < one[c].to ? one[c].to : one[c].from;
        CHECK(range_is(&x, 20, one[c].prefix, lo, hi));
        CHECK(range_is(&x, BERGDB_LATEST, one[c].prefix, lo, hi));
        CHECK_EQ(bergdb_debug_check(x.db), BERGDB_OK);
        tdb_close(&x);
    }

    REQUIRE(tdb_new(&x, 0, 0, false));                      /* testTimeSplitOfRoot */
    for (int i = 1; i <= 20; i++) {
        key2(i, k, sizeof k, "");
        snprintf(v, sizeof v, "v%s", k);
        at(&x, i * 10);
        CHECK_EQ(tx(&x, NULL, "p", k, v, NULL), BERGDB_OK);
        CHECK(get_is(&x, 9999, k, v));
    }
    for (int i = 1; i <= 20; i++) {
        key2(i, k, sizeof k, "");
        snprintf(v, sizeof v, "v%s", k);
        CHECK(get_is(&x, 210, k, v));
    }
    tdb_close(&x);
}

/* DbTester.createRandomDB: n puts of random int keys, each read back at once
 * (testWithRandomData, n 25; testWithMoreRandomData, an f-test in Java, n
 * 1,000), then every key read again. */
static void random_db(int n) {
    struct tdb x;
    REQUIRE(tdb_new(&x, 0, 0, false));
    uint64_t rs = 1;
    for (int i = 0; i < n; i++) {
        char k[32], v[40];
        snprintf(k, sizeof k, "%d", (int32_t) test_random(&rs));
        snprintf(v, sizeof v, "v%s", k);
        at(&x, i * 10 + 10);
        CHECK_EQ(tx(&x, NULL, "p", k, v, NULL), BERGDB_OK);
        CHECK(get_is(&x, BERGDB_LATEST, k, v));
    }
    rs = 1;
    for (int i = 0; i < n; i++) {
        char k[32], v[40];
        snprintf(k, sizeof k, "%d", (int32_t) test_random(&rs));
        snprintf(v, sizeof v, "v%s", k);
        CHECK(get_is(&x, BERGDB_LATEST, k, v));
    }
    CHECK_EQ(bergdb_debug_check(x.db), BERGDB_OK);
    tdb_close(&x);
}

TEST(dbt_with_random_data) {
    random_db(25);
    random_db(1000);
}

/* DbTester.testSplit3: a split in a transaction of 13 keys at node size 14,
 * then keys whose seven-byte segments share their start; the index
 * checked (checkNodes). */
TEST(dbt_split3) {
    struct tdb x;
    char k[64], v[64];
    REQUIRE(tdb_new(&x, 14, 0, false));
    at(&x, 100);
    bergdb_trans *t;
    REQUIRE(bergdb_trans_new(x.db, &t) == BERGDB_OK);
    for (int i = 100; i < 113; i++) {
        uint8_t b[KMAX];
        snprintf(k, sizeof k, "four%dend", i);
        snprintf(v, sizeof v, "%d", i);
        size_t n = bk(k, b);
        CHECK_EQ(bergdb_trans_put(t, b, n, (const uint8_t *) v, strlen(v)), BERGDB_OK);
    }
    CHECK_EQ(bergdb_execute(x.db, t, NULL), BERGDB_OK);
    bergdb_trans_free(t);
    CHECK_EQ(bergdb_debug_check(x.db), BERGDB_OK);
    at(&x, 110);
    REQUIRE(bergdb_trans_new(x.db, &t) == BERGDB_OK);
    for (int i = 100; i < 111; i++) {
        uint8_t b[KMAX];
        snprintf(k, sizeof k, "four110-%d", i);
        snprintf(v, sizeof v, "v-four110-%d", i);
        size_t n = bk(k, b);
        CHECK_EQ(bergdb_trans_put(t, b, n, (const uint8_t *) v, strlen(v)), BERGDB_OK);
    }
    CHECK_EQ(bergdb_execute(x.db, t, NULL), BERGDB_OK);
    bergdb_trans_free(t);
    at(&x, 120);
    CHECK_EQ(tx(&x, NULL, "p", "four110-111", "v-four110-111", NULL), BERGDB_OK);
    for (int i = 100; i < 113; i++) {
        snprintf(k, sizeof k, "four%dend", i);
        snprintf(v, sizeof v, "%d", i);
        CHECK(get_is(&x, BERGDB_LATEST, k, v));
    }
    for (int i = 100; i < 112; i++) {
        snprintf(k, sizeof k, "four110-%d", i);
        snprintf(v, sizeof v, "v-four110-%d", i);
        CHECK(get_is(&x, BERGDB_LATEST, k, v));
    }
    CHECK_EQ(bergdb_debug_check(x.db), BERGDB_OK);
    tdb_close(&x);
}

/* DbTester.testSpecialCase, testPrintGraph1 and testPrintGraph2 (Java's
 * prints are commented out; here the index is printed and checked). */
TEST(dbt_special_case) {
    struct tdb x;
    REQUIRE(tdb_new(&x, 0, 0, false));
    at(&x, 10);
    CHECK_EQ(tx(&x, NULL, "p", "r/directory1", "v1", "p", "r/direc", "v2", "p", "2/directory2",
            "v3", "p", "r/direct", "v4", NULL), BERGDB_OK);
    CHECK(get_is(&x, 999, "r/directory1", "v1"));
    CHECK(get_is(&x, 999, "r/direc", "v2"));
    CHECK(get_is(&x, 999, "2/direc", NULL));
    CHECK(get_is(&x, 999, "r/direct", "v4"));
    CHECK(get_is(&x, 999, "2/directory2", "v3"));
    for (int i = 0; i < 9; i++) {
        char k[8], v[8];
        snprintf(k, sizeof k, "k%d", i);
        snprintf(v, sizeof v, "v%d", i);
        CHECK_EQ(tx(&x, NULL, "p", k, v, NULL), BERGDB_OK);
    }
    FILE *null = fopen("/dev/null", "w");
    REQUIRE(null != NULL);
    CHECK_EQ(bergdb_debug_print(x.db, null), BERGDB_OK);
    fclose(null);
    CHECK_EQ(bergdb_debug_check(x.db), BERGDB_OK);
    tdb_close(&x);
}

/* DbTester.testTwoBinaryKeysInOneTransaction: the keys
 * KeyFactory.binaryIntKeyLE(j), 4-byte values, at the clock's time 0. */
TEST(dbt_two_binary_keys) {
    struct tdb x;
    REQUIRE(tdb_new(&x, 0, 0, false));
    bergdb_trans *t;
    REQUIRE(bergdb_trans_new(x.db, &t) == BERGDB_OK);
    for (uint8_t j = 0; j < 2; j++) {
        const uint8_t key[4] = { j, 0, 0, 0 }, value[4] = { j, 0, 0, 0 };
        CHECK_EQ(bergdb_trans_put(t, key, 4, value, 4), BERGDB_OK);
    }
    CHECK_EQ(bergdb_execute(x.db, t, NULL), BERGDB_OK);
    bergdb_trans_free(t);
    for (uint8_t j = 0; j < 2; j++) {
        const uint8_t key[4] = { j, 0, 0, 0 };
        struct bergdb_one one;
        CHECK_EQ(bergdb_get_one(x.db, x.rd, BERGDB_LATEST, key, 4, &one), BERGDB_OK);
        CHECK(one.value != NULL && one.value_len == 4 && one.value[0] == j);
    }
    tdb_close(&x);
}

/* DbTester.testManyOverwrites and testSettingValueManyTimes: one key
 * written again and again, read at every time. */
TEST(dbt_overwrites) {
    struct tdb x;
    char v[32];
    REQUIRE(tdb_new(&x, 0, 0, false));
    for (int i = 0; i < 40; i++) {
        snprintf(v, sizeof v, "version %d", i);
        CHECK_EQ(tx(&x, NULL, "p", "key", v, NULL), BERGDB_OK);
    }
    CHECK(get_is(&x, BERGDB_LATEST, "key", "version 39"));
    tdb_close(&x);
    REQUIRE(tdb_new(&x, 0, 0, false));
    for (int i = 0; i < 20; i++) {
        snprintf(v, sizeof v, "v-%d", i);
        at(&x, i * 10 + 1);
        CHECK_EQ(tx(&x, NULL, "p", "directory/myFile", v, NULL), BERGDB_OK);
    }
    for (int i = 0; i < 20; i++) {
        snprintf(v, sizeof v, "v-%d", i);
        CHECK(get_is(&x, i * 10 + 5, "directory/myFile", v));
    }
    tdb_close(&x);
}

/* KeyFactory.crazyKey's kinds: 'B' binary (an int, then 'B'), 'I' (the
 * index and 'I', as bytes), 'L' (20 to 1,019 bytes, or up to 10,019, a
 * number at its start and the index before its last byte 'L'), 'P' (a long
 * path shared by many keys) and 'C' (one of five paths); drawn by
 * test_random from the index. Its length. */
static size_t crazy_key(int index, uint8_t *key) {
    static const char *const prefixes[] = { "r/customers/", "r/internal/admins/",
            "home/frasse/.eclipse/settings/", "home/frasse/notes/",
            "media/usb/music/mp3/bach/" };
    uint64_t r = (uint64_t) index * 7919 + 1;
    int type = test_random_below(&r, 10);
    char s[200];
    if (type <= 2) {
        key[0] = (uint8_t) index;
        key[1] = (uint8_t) (index >> 8);
        key[2] = 0;
        key[3] = 0;
        key[4] = 'B';
        return 5;
    }
    if (type <= 5) {
        snprintf(s, sizeof s, "%dI", index);
        memcpy(key, s, strlen(s));
        return strlen(s);
    }
    if (type == 6) {
        size_t size = (size_t) test_random_below(&r, 1000) + 20;
        if (test_random_below(&r, 50) == 0) {
            size = (size_t) test_random_below(&r, 10000) + 20;
        }
        memset(key, 0, size);
        snprintf(s, sizeof s, "%d", 10000 + test_random_below(&r, 1000000));
        memcpy(key, s, strlen(s));
        key[size - 5] = 0;
        key[size - 4] = 0;
        key[size - 3] = (uint8_t) (index >> 8);
        key[size - 2] = (uint8_t) index;
        key[size - 1] = 'L';
        return size;
    }
    if (type == 7) {
        snprintf(s, sizeof s, "r/examples/A long directory name/followed by another one/%d-P",
                index);
    } else {
        snprintf(s, sizeof s, "%s%d-C", prefixes[test_random_below(&r, 5)], index);
    }
    return bk(s, key);
}

/* DbTester.testCrazyKeys: 50 keys of every kind, every tenth deleted, read
 * before and after the deletes. */
TEST(dbt_crazy_keys) {
    struct tdb x;
    enum { N = 50 };
    static uint8_t key[11000];
    REQUIRE(tdb_new(&x, 0, 0, false));
    char v[16];
    struct bergdb_one one;
    for (int i = 0; i < N; i++) {
        size_t n = crazy_key(i, key);
        snprintf(v, sizeof v, "v%d", i);
        at(&x, 1000000 + i * 10);
        CHECK_EQ(put_b(&x, key, n, (const uint8_t *) v, strlen(v), NULL), BERGDB_OK);
    }
    for (int i = 0; i < N; i++) {
        size_t n = crazy_key(i, key);
        snprintf(v, sizeof v, "v%d", i);
        CHECK_EQ(bergdb_get_one(x.db, x.rd, BERGDB_LATEST, key, n, &one), BERGDB_OK);
        CHECK(one.value != NULL && one.value_len == strlen(v)
                && memcmp(one.value, v, strlen(v)) == 0);
    }
    for (int i = 0; i < N; i += 10) {
        size_t n = crazy_key(i, key);
        bergdb_trans *t;
        at(&x, 2000000 + i * 10);
        REQUIRE(bergdb_trans_new(x.db, &t) == BERGDB_OK);
        CHECK_EQ(bergdb_trans_delete(t, key, n), BERGDB_OK);
        CHECK_EQ(bergdb_execute(x.db, t, NULL), BERGDB_OK);
        bergdb_trans_free(t);
    }
    for (int i = 0; i < N; i++) {
        size_t n = crazy_key(i, key);
        snprintf(v, sizeof v, "v%d", i);
        CHECK_EQ(bergdb_get_one(x.db, x.rd, BERGDB_LATEST, key, n, &one), BERGDB_OK);
        if (i % 10 == 0) {
            CHECK(one.value == NULL);
        } else {
            CHECK(one.value != NULL && one.value_len == strlen(v));
        }
        CHECK_EQ(bergdb_get_one(x.db, x.rd, 2000000 - 1, key, n, &one), BERGDB_OK);
        CHECK(one.value != NULL && one.value_len == strlen(v)
                && memcmp(one.value, v, strlen(v)) == 0);
    }
    CHECK_EQ(bergdb_debug_check(x.db), BERGDB_OK);
    tdb_close(&x);
}

/* DbUtil.getFirstKey: the first key at a time (GetMany.GetOne); its
 * length, 0 for none. */
static size_t first_key(struct tdb *x, int64_t time, uint8_t *out) {
    struct bergdb_range r;
    struct bergdb_many many;
    bergdb_range_init(&r);
    r.lookup_time = time;
    r.max_count = 1;
    if (bergdb_get_many(x->db, x->rd, &r, &many) != BERGDB_OK || many.count == 0) {
        return 0;
    }
    memcpy(out, many.kvts[0].key, many.kvts[0].key_len);
    return many.kvts[0].key_len;
}

static bool first_is(struct tdb *x, int64_t time, const char *ikey) {
    uint8_t got[KMAX], want[KMAX];
    size_t n = first_key(x, time, got);
    if (ikey == NULL) {
        return n == 0;
    }
    size_t w = bk(ikey, want);
    return n == w && memcmp(got, want, n) == 0;
}

/* DbTester.tGetFirst1 and tGetFirst2: the first key at each time. */
TEST(dbt_get_first) {
    struct tdb x;
    REQUIRE(tdb_new(&x, 0, 0, false));
    at(&x, 10);
    CHECK_EQ(tx(&x, NULL, "p", "bert", "v1", NULL), BERGDB_OK);
    at(&x, 20);
    CHECK_EQ(tx(&x, NULL, "p", "anna", "v2", NULL), BERGDB_OK);
    CHECK(first_is(&x, 5, NULL));
    CHECK(first_is(&x, 15, "bert"));
    CHECK(first_is(&x, 25, "anna"));
    tdb_close(&x);
    REQUIRE(tdb_new(&x, 0, 0, false));
    at(&x, 10);
    CHECK_EQ(tx(&x, NULL, "p", "employees/bertilsson", "v1", NULL), BERGDB_OK);
    at(&x, 20);
    CHECK_EQ(tx(&x, NULL, "p", "employees/annasson", "v2", NULL), BERGDB_OK);
    at(&x, 30);
    CHECK_EQ(tx(&x, NULL, "p", "a", "v3", NULL), BERGDB_OK);
    CHECK(first_is(&x, 5, NULL));
    CHECK(first_is(&x, 15, "employees/bertilsson"));
    CHECK(first_is(&x, 25, "employees/annasson"));
    CHECK(first_is(&x, 35, "a"));
    tdb_close(&x);
}

/* DbTester.bug130403: node size 62, 100 empty values. */
TEST(dbt_bug130403) {
    struct tdb x;
    REQUIRE(tdb_new(&x, 62, 0, false));
    for (int i = 0; i < 100; i++) {
        char k[8];
        snprintf(k, sizeof k, "%d", i);
        CHECK_EQ(tx(&x, NULL, "p", k, "", NULL), BERGDB_OK);
    }
    CHECK(get_is(&x, BERGDB_LATEST, "0", ""));
    CHECK(get_is(&x, BERGDB_LATEST, "99", ""));
    CHECK_EQ(bergdb_debug_check(x.db), BERGDB_OK);
    tdb_close(&x);
}

/* ======== DbTester: getTrans ======== */

/* checkGetTrans: every value's tpos from a get, and getTrans of it. */
static void check_get_trans(struct tdb *x, const struct bergdb_executed *ts, int n) {
    for (int i = 0; i < n; i++) {
        for (int j = 0; j < 20; j++) {
            char k[32];
            uint8_t b[KMAX];
            struct bergdb_one one;
            snprintf(k, sizeof k, "/k%d/%d", i, j);
            size_t kn = bk(k, b);
            CHECK_EQ(bergdb_get_one(x->db, x->rd, BERGDB_LATEST, b, kn, &one), BERGDB_OK);
            CHECK_EQ(one.tpos, ts[i].tpos);
        }
        struct bergdb_stored st;
        CHECK_EQ(bergdb_get_trans(x->db, x->rd, ts[i].tpos, &st), BERGDB_OK);
        CHECK_EQ(st.tt, ts[i].tt);
        CHECK_EQ(st.last_pos, ts[i].last_pos);
    }
}

/* DbTester.testGetTransOfEveryValue (005-34): the position of the
 * transaction that wrote each value, also after a meta block in its record,
 * and getTrans of it; again after a restart, at Java's default startup
 * distance (every transaction rerun) and at 20,000 bytes (values read from
 * the stream). */
TEST(dbt_get_trans_of_every_value) {
    static struct bergdb_executed ts[200];
    const int32_t sds[] = { 50 * 1000 * 1000, 20000 };
    for (int c = 0; c < 2; c++) {
        struct tdb x;
        REQUIRE(tdb_new(&x, 0, sds[c], true));
        uint64_t rs = 34;
        int n = 0, crossing = 0;
        while (crossing < 3 && n < 200) {
            bergdb_trans *t;
            REQUIRE(bergdb_trans_new(x.db, &t) == BERGDB_OK);
            for (int j = 0; j < 20; j++) {
                char k[32];
                uint8_t b[KMAX], v[500];
                for (int q = 0; q < 500; q++) {
                    v[q] = (uint8_t) test_random(&rs);
                }
                snprintf(k, sizeof k, "/k%d/%d", n, j);
                size_t kn = bk(k, b);
                CHECK_EQ(bergdb_trans_put(t, b, kn, v, 500), BERGDB_OK);
            }
            CHECK_EQ(bergdb_execute(x.db, t, &ts[n]), BERGDB_OK);
            bergdb_trans_free(t);
            if (ts[n].tpos / D_META != ts[n].last_pos / D_META) {
                crossing++;
            }
            n++;
        }
        CHECK_EQ(crossing, 3);
        check_get_trans(&x, ts, n);
        CHECK_EQ(bergdb_sync(x.db, 0, BERGDB_SYNC_ORDINARY), BERGDB_OK);
        CHECK_EQ(tdb_close(&x), BERGDB_OK);
        REQUIRE(tdb_start(&x) == BERGDB_OK);
        check_get_trans(&x, ts, n);
        CHECK_EQ(tdb_close(&x), BERGDB_OK);
        remove_dir(x.dir);
    }
}

/* DbTester.testGetTransRefusesBadPositions (005-34, 005-43): positions
 * where no transaction can start, refused before anything is read, and the
 * database goes on. */
TEST(dbt_get_trans_refuses_bad_positions) {
    struct tdb x;
    REQUIRE(tdb_new(&x, 0, 0, false));
    struct bergdb_executed ex;
    CHECK_EQ(tx(&x, &ex, "p", "/a", "a0", NULL), BERGDB_OK);
    const int64_t end = db_length(&x);
    CHECK_EQ(ex.last_pos + 1, end);
    const int64_t bad[] = { -1, INT64_MIN, ex.tpos + 4, ex.tpos + 1, 0, 64, D_META,
            D_META + 120, end, end + 8, D_META + 128 };
    struct bergdb_stored st;
    for (size_t i = 0; i < sizeof bad / sizeof bad[0]; i++) {
        CHECK_EQ(bergdb_get_trans(x.db, x.rd, bad[i], &st), BERGDB_ARG);
        CHECK(strncmp(bergdb_errmsg(x.db), "IllegalArgumentException", 24) == 0);
    }
    CHECK_EQ(bergdb_get_trans(x.db, x.rd, ex.tpos, &st), BERGDB_OK);
    CHECK_EQ(st.tt, ex.tt);
    CHECK_EQ(tx(&x, NULL, "p", "/b", "b0", NULL), BERGDB_OK);
    CHECK(get_is(&x, BERGDB_LATEST, "/b", "b0"));
    tdb_close(&x);
}

/* ======== DbTester: crashes ======== */

/* DbTester.testCrash6TornSizeBelowMin: a crash after the first byte of a
 * record's size, that byte 8: recovery completes a size that a record
 * cannot have; the start must take the stream as before the record, and
 * the database goes on. */
TEST(dbt_crash6_torn_size_below_min) {
    struct tdb x;
    REQUIRE(tdb_new(&x, 0, 0, true));
    CHECK_EQ(tx(&x, NULL, "p", "key1", "value1", NULL), BERGDB_OK);
    int64_t size1 = db_length(&x);
    CHECK_EQ(tx(&x, NULL, "p", "key2", "value2", NULL), BERGDB_OK);
    CHECK_EQ(tdb_close(&x), BERGDB_OK);
    struct files f;
    REQUIRE(files_read(x.dir, &f));
    *files_at(&f, size1) = 8;
    REQUIRE(files_write(x.dir, &f, size1 + 1));
    files_free(&f);
    REQUIRE(tdb_start(&x) == BERGDB_OK);
    CHECK(get_is(&x, BERGDB_LATEST, "key1", "value1"));
    CHECK(get_is(&x, BERGDB_LATEST, "key2", NULL));
    CHECK_EQ(tx(&x, NULL, "p", "key3", "value3", NULL), BERGDB_OK);
    CHECK_EQ(tdb_close(&x), BERGDB_OK);
    REQUIRE(tdb_start(&x) == BERGDB_OK);
    CHECK(get_is(&x, BERGDB_LATEST, "key1", "value1"));
    CHECK(get_is(&x, BERGDB_LATEST, "key2", NULL));
    CHECK(get_is(&x, BERGDB_LATEST, "key3", "value3"));
    CHECK_EQ(tdb_close(&x), BERGDB_OK);
    remove_dir(x.dir);
}

/* DbTester.testCrash7AtMetaBlockPosition (005-27): a crash that ends the
 * stream exactly at a meta block's position, after a record that ends
 * there; a cut just after that block; and a record that crosses the next
 * position, cut there. Each starts, has the records before the cut, takes a
 * transaction and starts again. */
TEST(dbt_crash7_at_meta_block_position) {
    struct tdb x;
    REQUIRE(tdb_new(&x, 0, 0, true));
    struct bergdb_executed ex;
    uint8_t key2[8], key3[8];
    size_t k2 = bk("key2", key2), k3 = bk("key3", key3);
    CHECK_EQ(tx(&x, NULL, "p", "key1", "value1", NULL), BERGDB_OK);
    uint8_t *v = calloc(D_META, 1);
    REQUIRE(v != NULL);
    CHECK_EQ(put_b(&x, key2, k2, v, 1000, &ex), BERGDB_OK);
    /* The next put of key2 has the same overhead; its value is sized for its
     * record to end at the second meta block's position. */
    int64_t overhead = ex.next_pos - ex.tpos - 1000;
    size_t v2n = (size_t) (D_META - ex.next_pos - overhead);
    v[0] = 2;
    CHECK_EQ(put_b(&x, key2, k2, v, v2n, &ex), BERGDB_OK);
    CHECK_EQ(ex.last_pos + 1, D_META);
    v[0] = 0;
    CHECK_EQ(put_b(&x, key3, k3, v, D_META, &ex), BERGDB_OK);
    CHECK(ex.tpos < 2 * D_META && ex.last_pos > 2 * D_META);
    CHECK_EQ(tdb_close(&x), BERGDB_OK);
    struct files f;
    REQUIRE(files_read(x.dir, &f));
    const int64_t cuts[] = { D_META, D_META + 128, 2 * D_META };
    for (int c = 0; c < 3; c++) {
        struct tdb y;
        tdb_init(&y, 0, 0);
        REQUIRE(new_dir(y.dir, sizeof y.dir));
        REQUIRE(files_write(y.dir, &f, cuts[c]));
        for (int start = 0; start < 2; start++) {
            REQUIRE(tdb_start(&y) == BERGDB_OK);
            struct bergdb_one one;
            CHECK(get_is(&y, BERGDB_LATEST, "key1", "value1"));
            CHECK_EQ(bergdb_get_one(y.db, y.rd, BERGDB_LATEST, key2, k2, &one), BERGDB_OK);
            CHECK(one.value != NULL && one.value_len == v2n && one.value[0] == 2);
            CHECK(get_is(&y, BERGDB_LATEST, "key3", NULL));
            if (start == 0) {
                CHECK_EQ(tx(&y, NULL, "p", "key4", "value4", NULL), BERGDB_OK);
            } else {
                CHECK(get_is(&y, BERGDB_LATEST, "key4", "value4"));
            }
            CHECK_EQ(tdb_close(&y), BERGDB_OK);
        }
        remove_dir(y.dir);
    }
    files_free(&f);
    free(v);
    remove_dir(x.dir);
}

/* DbTester.testCrash8InCreation (005-33; an f-test in Java): a crash while
 * the database is created, at every length of its stream from 1 byte to
 * the whole creation less one, and the whole creation with its transaction
 * failed (its last byte 0): the start is refused (DatabaseNotCreatedException)
 * and leaves the stream as it was. Every cut through the start on a stream
 * in memory (sdb_open, Db.start's checks and recovery); some through
 * bergdb_open in a directory, whose open forces the directory's parent, as
 * Java's createDirIfNeeded, about 10 ms each on F53. The whole creation
 * opens. */
TEST(dbt_crash8_in_creation) {
    struct tdb x;
    REQUIRE(tdb_new(&x, 0, 0, true));
    CHECK_EQ(tdb_close(&x), BERGDB_OK);
    struct files f;
    REQUIRE(files_read(x.dir, &f));
    REQUIRE(f.n == 1);
    CHECK_EQ(f.len[0], CREATION_LENGTH);
    uint8_t created[CREATION_LENGTH];
    memcpy(created, f.bytes[0], CREATION_LENGTH);
    int refused = 0, same = 0, cuts = 0;
    for (int cut = 1; cut <= CREATION_LENGTH; cut++) {
        uint8_t expected[CREATION_LENGTH];
        memcpy(expected, created, CREATION_LENGTH);
        if (cut == CREATION_LENGTH) {
            expected[CREATION_LENGTH - 1] = 0;
        }
        struct mem m;
        struct stream st;
        struct sdb b;
        struct err e;
        mem_init(&m);
        stream_open_memory(&st, &m);
        CHECK_EQ(stream_append_memory(&st, expected, cut, &e), ERR_OK);
        enum err_code rc = sdb_open(&b, &st, &m, 30, true, &e);
        if (rc == ERR_OK) {
            printf("  cut at %d: started\n", cut);
            sdb_close(&b);
        } else if (strcmp(e.java, "DatabaseNotCreatedException") == 0) {
            refused++;
        } else {
            printf("  cut at %d: %s: %s\n", cut, e.java, e.text);
        }
        if (stream_length(&st) == cut && memcmp(st.bytes, expected, (size_t) cut) == 0) {
            same++;
        }
        stream_close(&st);
        CHECK_MEM_ZERO(&m);
        if (cut != 1 && cut != 60 && cut != 127 && cut != 128 && cut != 129 && cut != 200
                && cut < CREATION_LENGTH - 1) {
            continue;
        }
        cuts++;
        memcpy(f.bytes[0], expected, CREATION_LENGTH);
        REQUIRE(files_write(x.dir, &f, cut));
        char errbuf[BERGDB_ERRBUF_SIZE];
        bergdb_db *db = NULL;
        int arc = bergdb_open(x.dir, &x.o, &db, NULL, errbuf);
        CHECK_EQ(arc, BERGDB_NOT_CREATED);
        CHECK(strncmp(errbuf, "DatabaseNotCreatedException", 27) == 0);
        if (arc == BERGDB_OK) {
            bergdb_close(db);
        }
        struct files after;
        CHECK(files_read(x.dir, &after) && after.n == 1 && after.len[0] == cut
                && memcmp(after.bytes[0], expected, (size_t) cut) == 0);
        files_free(&after);
    }
    CHECK_EQ(refused, CREATION_LENGTH);
    CHECK_EQ(same, CREATION_LENGTH);
    CHECK_EQ(cuts, 8);
    CHECK_EQ(x.m.live_total, 0);
    memcpy(f.bytes[0], created, CREATION_LENGTH);
    REQUIRE(files_write(x.dir, &f, CREATION_LENGTH));
    files_free(&f);
    REQUIRE(tdb_start(&x) == BERGDB_OK);
    CHECK_EQ(tx(&x, NULL, "p", "key1", "value1", NULL), BERGDB_OK);
    CHECK(get_is(&x, BERGDB_LATEST, "key1", "value1"));
    CHECK_EQ(tdb_close(&x), BERGDB_OK);
    remove_dir(x.dir);
}

/* ======== DbTester: the record limit lowered (db.h) ======== */

/* A put of an ikey into a builder, the value n bytes of v or the string s. */
static void tr_put_ikey(struct tr_builder *b, const char *ikey, const char *s, uint8_t v,
        int32_t n) {
    struct err e;
    uint8_t bkey[KMAX];
    int32_t kl = (int32_t) bk(ikey, bkey);
    if (s != NULL) {
        CHECK_EQ(tr_put(b, bkey, kl, (const uint8_t *) s, (int32_t) strlen(s), NULL, &e),
                ERR_OK);
        return;
    }
    uint8_t *value = malloc((size_t) n + 1);
    memset(value, v, (size_t) n);
    CHECK_EQ(tr_put(b, bkey, kl, value, n, NULL, &e), ERR_OK);
    free(value);
}

/* Builds and executes; t's outputs set on ERR_OK. */
static enum err_code exec_built(struct db *db, struct tr_builder *b, struct trans *t,
        struct err *e) {
    enum err_code rc = tr_build(b, t, e);
    if (rc == ERR_OK) {
        rc = db_execute(db, t, e);
    }
    return rc;
}

/* DbTester's config: node size, startup distance, the record limit; no
 * eviction; the test clock, set to 1,000,000; the test id. */
static void limit_config(struct db_config *cfg, struct bergdb_test_clock *clock, int32_t node,
        int32_t sd, int64_t limit) {
    memset(cfg, 0, sizeof *cfg);
    cfg->max_node_size = node;
    cfg->startup_distance = sd;
    cfg->cache_size_indicator = INT64_MAX;
    cfg->clock = bergdb_test_clock_time;
    cfg->clock_ctx = clock;
    memcpy(cfg->id, bergdb_test_id, 16);
    cfg->record_limit = limit;
    bergdb_test_clock_set(clock, 1000 * 1000);
}

/* DbTester.dirtyKey. */
static void dirty_key(int k, char *out, size_t cap) {
    snprintf(out, cap, "/k/%06d", k);
}

/*
 * DbTester.testTooManyDirtyNodes (005-31; an f-test in Java): with the
 * record limit lowered to 200 kB and a startup distance of 10 kB, an update
 * of every 10th of 10,000 keys, whose index nodes would not fit in a record,
 * is refused before it changes anything ("005-31"), nothing appended; a
 * smaller update and 1,000 new keys are taken, and the startup pos moves:
 * after 500 more transactions the startup section is under 3 times the
 * startup distance. Before 005-31 the startup pos stayed before such a
 * transaction for good. Read back through bergdb.h after a restart.
 */
TEST(dbt_too_many_dirty_nodes) {
    struct mem m;
    struct err e;
    struct db db;
    struct db_config cfg;
    struct db_start_info info;
    struct bergdb_test_clock clock = {0};
    int64_t time = 1000 * 1000;
    const int32_t sd = 10 * 1000;
    char dir[512], k[32], v[16];
    REQUIRE(new_dir(dir, sizeof dir));
    mem_init(&m);
    limit_config(&cfg, &clock, 30, sd, 200 * 1000);
    REQUIRE(db_open(&db, dir, &cfg, &m, &info, &e) == ERR_OK);
    static int order[10000];
    for (int i = 0; i < 10000; i++) {
        order[i] = i;
    }
    uint64_t rs = 7;
    for (int i = 9999; i > 0; i--) {
        int j = test_random_below(&rs, i + 1), t = order[i];
        order[i] = order[j];
        order[j] = t;
    }
    struct tr_builder b;
    struct trans t;
    for (int i = 0; i < 100; i++) {
        bergdb_test_clock_set(&clock, time += 1000);
        tr_builder_init(&b, &m);
        tr_init(&t, &m);
        for (int j = 0; j < 100; j++) {
            dirty_key(order[i * 100 + j], k, sizeof k);
            tr_put_ikey(&b, k, "v", 0, 0);
        }
        CHECK_EQ(exec_built(&db, &b, &t, &e), ERR_OK);
        tr_free(&t);
        tr_builder_free(&b);
    }
    for (int i = 0; i < 500; i++) {
        bergdb_test_clock_set(&clock, time += 1000);
        tr_builder_init(&b, &m);
        tr_init(&t, &m);
        snprintf(v, sizeof v, "a%d", i);
        tr_put_ikey(&b, "/x", v, 0, 0);
        CHECK_EQ(exec_built(&db, &b, &t, &e), ERR_OK);
        tr_free(&t);
        tr_builder_free(&b);
    }
    /* Every 10th key: index nodes over the record limit. */
    bergdb_test_clock_set(&clock, time += 1000);
    tr_builder_init(&b, &m);
    tr_init(&t, &m);
    for (int i = 0; i < 10000; i += 10) {
        dirty_key(i, k, sizeof k);
        tr_put_ikey(&b, k, "w", 0, 0);
    }
    int64_t length = db_stream_length(&db);
    CHECK_EQ(exec_built(&db, &b, &t, &e), ERR_LIMIT);
    CHECK(strcmp(e.java, "DbException") == 0 && strstr(e.text, "005-31") != NULL);
    CHECK_EQ(db_stream_length(&db), length);
    tr_free(&t);
    tr_builder_free(&b);
    bergdb_test_clock_set(&clock, time += 1000);
    tr_builder_init(&b, &m);
    tr_init(&t, &m);
    for (int i = 0; i < 10000; i += 1000) {
        dirty_key(i, k, sizeof k);
        tr_put_ikey(&b, k, "w", 0, 0);
    }
    CHECK_EQ(exec_built(&db, &b, &t, &e), ERR_OK);
    tr_free(&t);
    tr_builder_free(&b);
    bergdb_test_clock_set(&clock, time += 1000);
    tr_builder_init(&b, &m);
    tr_init(&t, &m);
    for (int i = 0; i < 1000; i++) {
        snprintf(k, sizeof k, "/new/%06d", i);
        tr_put_ikey(&b, k, "n", 0, 0);
    }
    CHECK_EQ(exec_built(&db, &b, &t, &e), ERR_OK);
    tr_free(&t);
    tr_builder_free(&b);
    for (int i = 0; i < 500; i++) {
        bergdb_test_clock_set(&clock, time += 1000);
        tr_builder_init(&b, &m);
        tr_init(&t, &m);
        snprintf(v, sizeof v, "b%d", i);
        tr_put_ikey(&b, "/y", v, 0, 0);
        CHECK_EQ(exec_built(&db, &b, &t, &e), ERR_OK);
        tr_free(&t);
        tr_builder_free(&b);
    }
    int64_t section = db_stream_length(&db) - db.startup_pos.startupPos;
    CHECK(section < 3 * sd);
    if (section >= 3 * sd) {
        printf("  the startup section: %lld bytes\n", (long long) section);
    }
    CHECK_EQ(db_close(&db, &e), ERR_OK);
    CHECK_MEM_ZERO(&m);
    struct tdb x;
    tdb_init(&x, 30, sd);
    snprintf(x.dir, sizeof x.dir, "%s", dir);
    REQUIRE(tdb_start(&x) == BERGDB_OK);
    CHECK(get_is(&x, BERGDB_LATEST, "/k/000000", "w"));
    CHECK(get_is(&x, BERGDB_LATEST, "/k/000010", "v"));
    CHECK(get_is(&x, BERGDB_LATEST, "/k/009000", "w"));
    CHECK(get_is(&x, BERGDB_LATEST, "/k/009990", "v"));
    CHECK(get_is(&x, BERGDB_LATEST, "/new/000999", "n"));
    CHECK(get_is(&x, BERGDB_LATEST, "/y", "b499"));
    CHECK_EQ(tdb_close(&x), BERGDB_OK);
    remove_dir(dir);
}

/*
 * DbTester.testRecordsWithinLimit (005-17; an f-test in Java): records near
 * the record limit, lowered to 200 kB, stay within it, as the writer takes
 * fewer dirty index nodes (TransSeq.take's budget): node size 8, a startup
 * distance of 150 kB, transactions of a value of 170 kB and 50 small puts of
 * 3,000 keys; each record at most the limit and two meta blocks. A restart
 * has the state, every key read against the run's own record of it. Java
 * runs 300 transactions; 60 here, about 10 MB.
 */
TEST(dbt_records_within_limit) {
    enum { N = 60, NK = 3000 };
    const int64_t limit = 200 * 1000;
    struct mem m;
    struct err e;
    struct db db;
    struct db_config cfg;
    struct db_start_info info;
    struct bergdb_test_clock clock = {0};
    int64_t time = 1000 * 1000;
    char dir[512], k[32], v[16];
    static int last[NK];
    REQUIRE(new_dir(dir, sizeof dir));
    mem_init(&m);
    limit_config(&cfg, &clock, 8, 150 * 1000, limit);
    REQUIRE(db_open(&db, dir, &cfg, &m, &info, &e) == ERR_OK);
    for (int i = 0; i < NK; i++) {
        last[i] = -1;
    }
    uint64_t rs = 17;
    int64_t largest = 0;
    for (int i = 0; i < N; i++) {
        struct tr_builder b;
        struct trans t;
        bergdb_test_clock_set(&clock, time += 1000);
        tr_builder_init(&b, &m);
        tr_init(&t, &m);
        snprintf(k, sizeof k, "/big/%d", i % 7);
        tr_put_ikey(&b, k, NULL, (uint8_t) i, 170 * 1000);
        for (int j = 0; j < 50; j++) {
            int n = test_random_below(&rs, NK);
            snprintf(k, sizeof k, "/k/%d", n);
            snprintf(v, sizeof v, "v%d", i);
            tr_put_ikey(&b, k, v, 0, 0);
            last[n] = i;
        }
        CHECK_EQ(exec_built(&db, &b, &t, &e), ERR_OK);
        int64_t record = t.next_pos - t.tpos;
        largest = record > largest ? record : largest;
        CHECK(record <= limit + 2 * 128);
        tr_free(&t);
        tr_builder_free(&b);
    }
    CHECK(largest > 170 * 1000);
    CHECK_EQ(db_close(&db, &e), ERR_OK);
    CHECK_MEM_ZERO(&m);
    struct tdb x;
    tdb_init(&x, 8, 150 * 1000);
    snprintf(x.dir, sizeof x.dir, "%s", dir);
    REQUIRE(tdb_start(&x) == BERGDB_OK);
    for (int n = 0; n < NK; n++) {
        snprintf(k, sizeof k, "/k/%d", n);
        snprintf(v, sizeof v, "v%d", last[n]);
        CHECK(get_is(&x, BERGDB_LATEST, k, last[n] < 0 ? NULL : v));
    }
    for (int j = 0; j < 7; j++) {
        uint8_t key[16];
        struct bergdb_one one;
        snprintf(k, sizeof k, "/big/%d", j);
        size_t kn = bk(k, key);
        CHECK_EQ(bergdb_get_one(x.db, x.rd, BERGDB_LATEST, key, kn, &one), BERGDB_OK);
        CHECK(one.value != NULL && one.value_len == 170 * 1000
                && one.value[0] == (uint8_t) (N - 1 - (N - 1 - j) % 7));
    }
    CHECK_EQ(tdb_close(&x), BERGDB_OK);
    remove_dir(dir);
}

/* ======== DbTesterJavadoc ======== */

/* DbTesterJavadoc.testGetOneAndTheTransaction: no value for an absent key
 * or before the transaction; the value's tpos is its transaction's, which
 * getTrans reads (tt, tpos, lastPos); nextPos is the stream's length. */
TEST(dbt_get_one_and_the_transaction) {
    struct tdb x;
    REQUIRE(tdb_new(&x, 0, 0, false));
    const uint8_t value[] = { 1, 2, 3 };
    uint8_t a[4], b[4];
    size_t an = bk("a", a), bn = bk("b", b);
    struct bergdb_executed ex;
    CHECK_EQ(put_b(&x, a, an, value, 3, &ex), BERGDB_OK);
    CHECK_EQ(ex.next_pos, ex.last_pos + 1);
    CHECK_EQ(db_length(&x), ex.next_pos);
    struct bergdb_one one;
    CHECK_EQ(bergdb_get_one(x.db, x.rd, BERGDB_LATEST, b, bn, &one), BERGDB_OK);
    CHECK(one.value == NULL);
    CHECK_EQ(bergdb_get_one(x.db, x.rd, ex.tt - 1, a, an, &one), BERGDB_OK);
    CHECK(one.value == NULL);
    CHECK_EQ(bergdb_get_one(x.db, x.rd, BERGDB_LATEST, a, an, &one), BERGDB_OK);
    CHECK(one.value != NULL && one.value_len == 3 && memcmp(one.value, value, 3) == 0);
    CHECK_EQ(one.tpos, ex.tpos);
    struct bergdb_stored st;
    CHECK_EQ(bergdb_get_trans(x.db, x.rd, one.tpos, &st), BERGDB_OK);
    CHECK_EQ(st.tt, ex.tt);
    CHECK_EQ(st.tpos, ex.tpos);
    CHECK_EQ(st.last_pos, ex.last_pos);
    tdb_close(&x);
}

/* A stop function with an answer that is none of the four. */
static int bad_answer(void *ctx, const struct bergdb_kvt *kvt) {
    (void) ctx;
    (void) kvt;
    return 7;
}

/*
 * DbTesterJavadoc.testDbNullArguments, testTransBuilderNullArguments,
 * testGetManyNullArguments and testRangeArguments (020-27, Q2, on main
 * after the pin of 17:18), as bergdb.h has them: a NULL where a pointer is
 * needed (also for a key or a value of length 0), a negative count and a
 * stop function's bad answer are refused with BERGDB_ARG; nothing is
 * written and the database goes on. The arguments that Java's Core takes
 * and C's API has not (a key of no segments, a GetMany used twice, read
 * hashes, the stream and the builder's settings) are not here.
 */
TEST(dbt_null_and_range_arguments) {
    struct tdb x;
    REQUIRE(tdb_new(&x, 0, 0, false));
    CHECK_EQ(tx(&x, NULL, "p", "k", "v", NULL), BERGDB_OK);
    const int64_t length = db_length(&x);
    uint8_t key[4];
    size_t kn = bk("k", key);
    const uint8_t v = 1;
    bergdb_trans *t;
    REQUIRE(bergdb_trans_new(x.db, &t) == BERGDB_OK);
    struct bergdb_one one;
    struct bergdb_many many;
    struct bergdb_stored st;
    struct bergdb_range r;
    struct bergdb_executed ex;
    bergdb_read *rd = NULL;
    bergdb_range_init(&r);
    const int rcs[] = {
        bergdb_trans_new(NULL, &t),
        bergdb_trans_put(NULL, key, kn, &v, 1),
        bergdb_trans_put(t, NULL, 1, &v, 1),
        bergdb_trans_put(t, NULL, 0, &v, 1),
        bergdb_trans_put(t, key, kn, NULL, 1),
        bergdb_trans_put(t, key, kn, NULL, 0),
        bergdb_trans_put_transformed(t, NULL, 1, &v, 1, NULL),
        bergdb_trans_put_transformed(t, key, kn, NULL, 1, NULL),
        bergdb_trans_delete(NULL, key, kn),
        bergdb_trans_delete(t, NULL, 1),
        bergdb_trans_key_read(NULL, key, kn),
        bergdb_trans_key_read(t, NULL, 1),
        bergdb_trans_lookup_time(NULL, 1),
        bergdb_execute(NULL, t, &ex),
        bergdb_execute(x.db, NULL, &ex),
        bergdb_read_new(NULL, &rd),
        bergdb_read_new(x.db, NULL),
        bergdb_get_one(NULL, x.rd, BERGDB_LATEST, key, kn, &one),
        bergdb_get_one(x.db, NULL, BERGDB_LATEST, key, kn, &one),
        bergdb_get_one(x.db, x.rd, BERGDB_LATEST, NULL, 1, &one),
        bergdb_get_one(x.db, x.rd, BERGDB_LATEST, NULL, 0, &one),
        bergdb_get_one(x.db, x.rd, BERGDB_LATEST, key, kn, NULL),
        bergdb_get_many(NULL, x.rd, &r, &many),
        bergdb_get_many(x.db, NULL, &r, &many),
        bergdb_get_many(x.db, x.rd, NULL, &many),
        bergdb_get_many(x.db, x.rd, &r, NULL),
        bergdb_get_trans(NULL, x.rd, CREATION_LENGTH, &st),
        bergdb_get_trans(x.db, NULL, CREATION_LENGTH, &st),
        bergdb_get_trans(x.db, x.rd, CREATION_LENGTH, NULL),
        bergdb_sync(NULL, 0, BERGDB_SYNC_ORDINARY),
        bergdb_debug_print(NULL, stdout),
        bergdb_debug_print(x.db, NULL) };
    for (size_t i = 0; i < sizeof rcs / sizeof rcs[0]; i++) {
        CHECK_EQ(rcs[i], BERGDB_ARG);
        if (rcs[i] != BERGDB_ARG) {
            printf("  call %zu: %s\n", i, bergdb_errname(rcs[i]));
        }
    }
    CHECK(rd == NULL);
    /* The range: a negative count (GetN's), a stop function's bad answer. */
    r.max_count = -1;
    CHECK_EQ(bergdb_get_many(x.db, x.rd, &r, &many), BERGDB_ARG);
    bergdb_range_init(&r);
    r.stop = bad_answer;
    CHECK_EQ(bergdb_get_many(x.db, x.rd, &r, &many), BERGDB_ARG);
    /* Nothing added to the transaction, nothing written; the database goes on. */
    uint8_t k2[4];
    size_t k2n = bk("k2", k2);
    CHECK_EQ(bergdb_trans_put(t, k2, k2n, (const uint8_t *) "v2", 2), BERGDB_OK);
    CHECK_EQ(db_length(&x), length);
    CHECK_EQ(bergdb_execute(x.db, t, &ex), BERGDB_OK);
    bergdb_trans_free(t);
    CHECK(db_length(&x) > length);
    CHECK(get_is(&x, BERGDB_LATEST, "k", "v"));
    CHECK(get_is(&x, BERGDB_LATEST, "k2", "v2"));
    bergdb_range_init(&r);
    CHECK_EQ(bergdb_get_many(x.db, x.rd, &r, &many), BERGDB_OK);
    CHECK_EQ((int64_t) many.count, 2);
    tdb_close(&x);
}

/* ======== DbTesterFailure: reads that fail on the storage ======== */

/* DbTesterFailure.key: "/k" + (10000 + i). */
static void fkey(int i, char *out, size_t cap) {
    snprintf(out, cap, "/k%d", 10000 + i);
}

#define KEYS 2000

/* DbTesterFailure.startEvicting and fill, in a directory: node size 8, a
 * startup distance of 1,000 bytes, a budget of 1 byte (every evictable
 * object out at the end of each call, as Java's Eviction.Schedule.EVERY);
 * KEYS keys, ten a transaction; synced and closed. Its files. */
static bool evicting_base(struct files *f) {
    struct tdb x;
    if (!tdb_new(&x, 8, 1000, true)) {
        return false;
    }
    for (int i = 0; i < KEYS; i += 10) {
        bergdb_trans *t;
        if (bergdb_trans_new(x.db, &t) != BERGDB_OK) {
            return false;
        }
        for (int j = i; j < i + 10; j++) {
            char k[16], v[16];
            uint8_t b[KMAX];
            fkey(j, k, sizeof k);
            snprintf(v, sizeof v, "v%d", j);
            size_t n = bk(k, b);
            bergdb_trans_put(t, b, n, (const uint8_t *) v, strlen(v));
        }
        int rc = bergdb_execute(x.db, t, NULL);
        bergdb_trans_free(t);
        if (rc != BERGDB_OK) {
            return false;
        }
    }
    bool ok = tdb_close(&x) == BERGDB_OK && files_read(x.dir, f);
    remove_dir(x.dir);
    return ok;
}

/* Opens a copy of the base's files with a budget of 1 byte. */
static bool evicting_start(struct tdb *x, const struct files *f) {
    tdb_init(x, 8, 1000);
    x->o.cache_size_indicator = 1;
    return new_dir(x->dir, sizeof x->dir) && files_write(x->dir, f, INT64_MAX)
            && tdb_start(x) == BERGDB_OK;
}

/* The bytes of a record at tpos, from its byte 'off' on, n of them, through
 * the meta blocks between (RecoverableStream.getSpos). */
static void record_bytes(struct files *f, int64_t tpos, int32_t off, uint8_t *buf, int32_t n,
        bool write) {
    for (int32_t i = 0; i < n; i++) {
        uint8_t *p = files_at(f, rs_get_spos(tpos, off + i));
        if (p != NULL && write) {
            *p = buf[i];
        } else if (p != NULL) {
            buf[i] = *p;
        }
    }
}

/* DbTesterFailure's KeyCountStream, in the files: every key node of every
 * record after the creation with its key count, bytes 17 and 18, set to
 * 0x7fff and its checksum made right; Java damages the reads of such nodes.
 * Written into dir under the open database. */
static int64_t key_node_tpos;       /* the first record with a damaged key node */

static void damage_key_counts(const char *dir, const struct files *base) {
    struct files f = *base;
    int64_t total = 0;
    for (int i = 0; i < f.n; i++) {
        f.bytes[i] = malloc((size_t) base->len[i]);
        memcpy(f.bytes[i], base->bytes[i], (size_t) base->len[i]);
        total += f.len[i];
    }
    int damaged = 0;
    key_node_tpos = -1;
    static uint8_t node[64 * 1024];
    for (int64_t tpos = CREATION_LENGTH; tpos < total; ) {
        uint8_t h[4];
        record_bytes(&f, tpos, 0, h, 4, false);
        int32_t size = (int32_t) ((uint32_t) h[0] | (uint32_t) h[1] << 8
                | (uint32_t) h[2] << 16 | (uint32_t) h[3] << 24);
        if (size < 41) {
            break;
        }
        for (int32_t off = 32; off + 8 <= size; ) {
            record_bytes(&f, tpos, off, h, 4, false);
            int32_t n = (int32_t) ((uint32_t) h[0] | (uint32_t) h[1] << 8
                    | (uint32_t) h[2] << 16 | (uint32_t) h[3] << 24);
            if (n <= 0 || n > (int32_t) sizeof node || off + n > size) {
                break;
            }
            record_bytes(&f, tpos, off, node, n, false);
            if (node[4] == 20 && n >= 32) {         /* Node.TYPE_KEY_NODE */
                node[17] = 0xff;
                node[18] = 0x7f;
                int32_t sum = cks_sum_with_zero_replace(node, 0, n, 6);
                node[6] = (uint8_t) sum;
                node[7] = (uint8_t) (sum >> 8);
                record_bytes(&f, tpos, off, node, n, true);
                damaged++;
                if (key_node_tpos < 0) {
                    key_node_tpos = tpos;
                }
            }
            off += n;
        }
        tpos = rs_get_spos(tpos, size);
    }
    CHECK(damaged > 100);
    CHECK(files_write(dir, &f, INT64_MAX));
    files_free(&f);
}

/* The damage under an open database, in its files: 0, the bytes from the
 * creation's end on cut off (the reads there fail: an EOFException, the
 * storage's I/O error); 1, the last byte of every 8-byte word from there on
 * flipped (a node's checksum, at its bytes 6 and 7, is then wrong:
 * StreamChecksumException), its size field and type left; 2, every key
 * node's key count wrong, its checksum right (damage_key_counts:
 * StreamFormatException, "Bad key count", 015-07). The start has read what
 * it reads; the index nodes that eviction has released are
 * loaded from the damaged bytes. */
static void damage(const char *dir, const struct files *f, int how) {
    if (how == 2) {
        damage_key_counts(dir, f);
        return;
    }
    int64_t start = 0;
    for (int i = 0; i < f->n; i++) {
        char path[1024];
        snprintf(path, sizeof path, "%s/%s", dir, f->name[i]);
        int64_t from = start < CREATION_LENGTH ? CREATION_LENGTH - start : 0;
        if (from < f->len[i]) {
            if (how == 0) {
                CHECK_EQ(truncate(path, (off_t) from), 0);
            } else {
                uint8_t *b = malloc((size_t) f->len[i]);
                memcpy(b, f->bytes[i], (size_t) f->len[i]);
                for (int64_t q = from; q < f->len[i]; q++) {
                    if ((start + q) % 8 == 7) {
                        b[q] ^= 0x55;
                    }
                }
                FILE *fp = fopen(path, "r+b");
                if (fp != NULL) {
                    fseek(fp, (long) from, SEEK_SET);
                    CHECK_EQ((int64_t) fwrite(b + from, 1, (size_t) (f->len[i] - from), fp),
                            f->len[i] - from);
                    fclose(fp);
                }
                free(b);
            }
        }
        start += f->len[i];
    }
}

/* Every later call is refused with the failure as its cause: a transaction,
 * a read, getTrans; the status works (DbTesterFailure.assertRefused). */
static void check_refused(struct tdb *x, const char *cause) {
    struct bergdb_stats s;
    CHECK_EQ(bergdb_stats(x->db, &s), BERGDB_OK);
    int64_t len = s.stream_length;
    CHECK_EQ(tx(x, NULL, "p", "/later", "x", NULL), BERGDB_FAILED);
    CHECK(strncmp(bergdb_errmsg(x->db), "DbFailedException", 17) == 0);
    CHECK(strstr(bergdb_errmsg(x->db), cause) != NULL);
    CHECK(!get_is(x, BERGDB_LATEST, "/k10005", "v5"));
    struct bergdb_stored st;
    CHECK_EQ(bergdb_get_trans(x->db, x->rd, 128, &st), BERGDB_FAILED);
    CHECK_EQ(bergdb_stats(x->db, &s), BERGDB_OK);
    CHECK_EQ(s.stream_length, len);
}

/* A restart on the base's files, undamaged: every key. */
static void check_restart(const struct files *f) {
    struct tdb x;
    REQUIRE(evicting_start(&x, f));
    for (int j = 0; j < KEYS; j += 7) {
        char k[16], v[16];
        fkey(j, k, sizeof k);
        snprintf(v, sizeof v, "v%d", j);
        CHECK(get_is(&x, BERGDB_LATEST, k, v));
    }
    CHECK_EQ(tx(&x, NULL, "p", "/k11000", "w", NULL), BERGDB_OK);
    CHECK(get_is(&x, BERGDB_LATEST, "/k11000", "w"));
    CHECK_EQ(tdb_close(&x), BERGDB_OK);
    remove_dir(x.dir);
}

/* A key transformation of DbTesterFailure.failInPut: the key becomes
 * key(KEYS / 2), whose path the warm-up did not read, and the storage is
 * damaged first, after the go point. */
struct fail_in_put {
    const char *dir;
    const struct files *f;
    int how;
    uint8_t key[16];
};

static void fail_in_put_key(void *ctx, int64_t tt, const uint8_t **key, size_t *key_len) {
    struct fail_in_put *c = ctx;
    (void) tt;
    damage(c->dir, c->f, c->how);
    *key_len = bk("/k11000", c->key);
    *key = c->key;
}

/*
 * DbTesterFailure's failInRead, failInPut and testReadErrorInWarmup (005-01,
 * 005-30): a get (testReadErrorInGetOne, testCorruptNodeInGetOne), a scan
 * (testReadErrorInGetMany, testCorruptNodeInGetMany), a transaction's
 * warm-up (testReadErrorInWarmup) and a put after its go point
 * (testReadErrorInPut, testCorruptNodeInPut) that load an evicted index
 * node from damaged storage, and getTrans of a damaged record
 * (testGetTrans): an I/O error (an EOFException, which the
 * stream gives as a StreamIoException) or a checksum error
 * (StreamChecksumException). The call fails the database, with the
 * failure as its cause; every later call is refused with it; nothing is
 * appended; a restart on the undamaged files has every key, and neither
 * the failed put's keys.
 */
TEST(dbt_reads_that_fail_on_the_storage) {
    struct files f;
    REQUIRE(evicting_base(&f));
    const char *const causes[] = { "StreamIoException", "StreamChecksumException",
            "StreamFormatException: Bad key count" };
    for (int how = 0; how < 3; how++) {
        for (int call = 0; call < 5; call++) {
            struct tdb x;
            REQUIRE(evicting_start(&x, &f));
            int64_t len = db_length(&x);
            int rc;
            struct bergdb_many many;
            if (call == 3) {
                struct fail_in_put c = { x.dir, &f, how, { 0 } };
                struct bergdb_transform tf = { fail_in_put_key, NULL, &c };
                bergdb_trans *t;
                uint8_t a[4], z[4];
                size_t an = bk("/a", a), zn = bk("/z", z);
                REQUIRE(bergdb_trans_new(x.db, &t) == BERGDB_OK);
                CHECK_EQ(bergdb_trans_put(t, a, an, (const uint8_t *) "a1", 2), BERGDB_OK);
                CHECK_EQ(bergdb_trans_put_transformed(t, z, zn, (const uint8_t *) "x", 1, &tf),
                        BERGDB_OK);
                rc = bergdb_execute(x.db, t, NULL);
                bergdb_trans_free(t);
            } else {
                damage(x.dir, &f, how);
                if (call == 0) {
                    uint8_t b[KMAX];
                    size_t n = bk("/k11000", b);
                    struct bergdb_one one;
                    rc = bergdb_get_one(x.db, x.rd, BERGDB_LATEST, b, n, &one);
                } else if (call == 1) {
                    struct bergdb_range r;
                    bergdb_range_init(&r);
                    rc = bergdb_get_many(x.db, x.rd, &r, &many);
                } else if (call == 2) {
                    rc = tx(&x, NULL, "p", "/k11000", "w", NULL);
                } else {
                    struct bergdb_stored st;
                    rc = bergdb_get_trans(x.db, x.rd, how == 2 ? key_node_tpos : CREATION_LENGTH,
                            &st);
                }
            }
            /* getTrans of a damaged record: its last byte, the commit byte, is
             * wrong, as in Java's FaultStream, whose corrupt reads flip the last
             * byte of each read (a StreamFormatException there too). */
            const char *cause = call == 4 && how == 1 ? "StreamFormatException: Bad lastByte"
                    : causes[how];
            CHECK_EQ(rc, BERGDB_FAILED);
            if (rc != BERGDB_FAILED) {
                printf("  damage %d, call %d: %s\n", how, call, bergdb_errname(rc));
            }
            CHECK(strncmp(bergdb_errmsg(x.db), "DbFailedException", 17) == 0);
            CHECK(strstr(bergdb_errmsg(x.db), cause) != NULL);
            if (strstr(bergdb_errmsg(x.db), cause) == NULL) {
                printf("  damage %d, call %d: %s\n", how, call, bergdb_errmsg(x.db));
            }
            check_refused(&x, cause);
            CHECK_EQ(db_length(&x), len);
            int crc = tdb_close(&x);
            CHECK(crc == BERGDB_OK || crc == BERGDB_IO);
            remove_dir(x.dir);
        }
    }
    check_restart(&f);
    files_free(&f);
}

/* ======== DbTesterDelete, and DbTester.testTransformedKeysSorted ========
 *
 * Deletes through the database: the upward unlink, the take-back and root
 * collapse at the delete (bergdb 023-07, sections 5.1 to 5.3; Java's since
 * release 2026.4; 022-07), with restarts that rerun the records, and the
 * sort of a transaction's keys after their transformations, one operation a
 * key (023-08, section 7). Java's MemoryStream.copy() is a database in a
 * directory, closed and started again. */

/* A key transformation's state: what it changes, and the new key's bytes,
 * valid until it is called again. */
struct ktf {
    int how;            /* 0 DOLLAR_TO_Z, 1 TO_C, 2 toName, 3 bySlot */
    uint8_t buf[KMAX];
    int calls;          /* of the value transformation (Bang) */
    uint8_t vbuf[64];
    int slot;           /* bySlot: 0 or 1 */
    const bool *first;
    const bool *collide;
};

static void ktf_key(void *ctx, int64_t tt, const uint8_t **key, size_t *key_len) {
    (void) tt;
    struct ktf *f = ctx;
    char in[KMAX], out[KMAX];
    size_t n = *key_len;
    if (n >= KMAX || bergdb_bkey_to_ikey(*key, n, (uint8_t *) in) != BERGDB_OK) {
        return;
    }
    in[n] = '\0';
    switch (f->how) {
    case 0:
        /* "/prefix/$..." into "/prefix/z...", which sorts after "/prefix/b...". */
        snprintf(out, sizeof out, "%s", in);
        if (strncmp(out, "/prefix/$", 9) == 0) {
            out[8] = 'z';
        }
        break;
    case 1:
        /* "/c/$x" or "/c/~x" into "/c/x": "$" sorts before letters, "~" after. */
        snprintf(out, sizeof out, "/c/%s", in + 4);
        break;
    case 2: {
        /* "/t/$NN=kXXX" into "/t/kXXX". */
        const char *eq = strchr(in, '=');
        snprintf(out, sizeof out, "/t/%s", eq != NULL ? eq + 1 : in);
        break;
    }
    default:
        if (!*f->first) {
            snprintf(out, sizeof out, "/later/%s", f->slot == 0 ? "a" : "b");
        } else if (*f->collide) {
            snprintf(out, sizeof out, "/shared");
        } else {
            snprintf(out, sizeof out, "%s", f->slot == 0 ? "/x2" : "/x1");
        }
        break;
    }
    *key_len = bk(out, f->buf);
    *key = f->buf;
}

/* Bang: appends "!" to the value it is given, and counts its calls. */
static void ktf_bang(void *ctx, int64_t tt, const uint8_t *previous, size_t previous_len,
        const uint8_t **value, size_t *value_len) {
    (void) tt, (void) previous, (void) previous_len;
    struct ktf *f = ctx;
    f->calls++;
    memcpy(f->vbuf, *value, *value_len);
    f->vbuf[*value_len] = '!';
    *value = f->vbuf;
    *value_len += 1;
}

/* tb.put(key, keyTransformation, value, valueTransformation), by ikey. */
static int put_tf(bergdb_trans *t, const char *ikey, const char *value, struct ktf *f,
        bool keyTf, bool valueTf) {
    uint8_t b[KMAX];
    size_t n = bk(ikey, b);
    struct bergdb_transform tf = { keyTf ? ktf_key : NULL, valueTf ? ktf_bang : NULL, f };
    return bergdb_trans_put_transformed(t, b, n, (const uint8_t *) value, strlen(value), &tf);
}

static int put_s(bergdb_trans *t, const char *ikey, const char *value) {
    uint8_t b[KMAX];
    size_t n = bk(ikey, b);
    return bergdb_trans_put(t, b, n, (const uint8_t *) value, strlen(value));
}

static int del_s(bergdb_trans *t, const char *ikey) {
    uint8_t b[KMAX];
    size_t n = bk(ikey, b);
    return bergdb_trans_delete(t, b, n);
}

/* Closes the database and starts it again on its directory. */
static bool tdb_restart(struct tdb *x) {
    if (tdb_close(x) != BERGDB_OK) {
        return false;
    }
    return tdb_start(x) == BERGDB_OK;
}

static void tdb_end(struct tdb *x) {
    tdb_close(x);
    remove_dir(x->dir);
}

/* The two directories' streams are the same, byte for byte. */
static bool same_streams(const char *dir0, const char *dir1) {
    struct files *f0 = malloc(sizeof *f0), *f1 = malloc(sizeof *f1);
    bool same = files_read(dir0, f0) && files_read(dir1, f1) && f0->n == f1->n;
    for (int i = 0; same && i < f0->n; i++) {
        same = f0->len[i] == f1->len[i]
                && memcmp(f0->bytes[i], f1->bytes[i], (size_t) f0->len[i]) == 0;
    }
    files_free(f0);
    files_free(f1);
    free(f0);
    free(f1);
    return same;
}

/* Startup distances: 10 bytes, so a start reruns little; 10 MB, so it reruns all. */
static const int32_t DISTANCES[] = { 10, 10 * 1000 * 1000 };

/* DbTesterDelete.testTransformedPutsAndDeletesWithRestarts: a history of b
 * keys, then one transaction that puts z keys through a key transformation
 * and deletes every b key, then a restart and more transactions, and
 * another restart; the values at each step, at a startup distance of 10
 * bytes, which writes each record at once. */
TEST(dbt_transformed_puts_and_deletes_with_restarts) {
    uint64_t rs = 1;
    for (int iter = 0; iter < 16; iter++) {
        const int nb = 1 + test_random_below(&rs, 60);
        const int hist = 1 + test_random_below(&rs, 4);
        const int nz = 1 + test_random_below(&rs, 120);
        struct tdb x;
        REQUIRE(tdb_new(&x, 8, 10, true));
        char key[40], value[40];
        bergdb_trans *t;
        for (int h = 0; h < hist; h++) {
            REQUIRE(bergdb_trans_new(x.db, &t) == BERGDB_OK);
            for (int i = 0; i < nb; i++) {
                if (h == 0 || test_random_below(&rs, 3) == 0) {
                    snprintf(key, sizeof key, "/prefix/b%04d", i);
                    snprintf(value, sizeof value, "v%d-%d", h, i);
                    CHECK_EQ(put_s(t, key, value), BERGDB_OK);
                }
            }
            CHECK_EQ(bergdb_execute(x.db, t, NULL), BERGDB_OK);
            bergdb_trans_free(t);
        }
        struct ktf *fs = calloc((size_t) nz, sizeof *fs);
        REQUIRE(bergdb_trans_new(x.db, &t) == BERGDB_OK);
        for (int i = 0; i < nz; i++) {
            snprintf(key, sizeof key, "/prefix/$%04d", i);
            snprintf(value, sizeof value, "z%d", i);
            CHECK_EQ(put_tf(t, key, value, &fs[i], true, false), BERGDB_OK);
        }
        for (int i = 0; i < nb; i++) {
            snprintf(key, sizeof key, "/prefix/b%04d", i);
            CHECK_EQ(del_s(t, key), BERGDB_OK);
        }
        CHECK_EQ(bergdb_execute(x.db, t, NULL), BERGDB_OK);
        bergdb_trans_free(t);
        free(fs);
        struct bergdb_executed ex;
        CHECK_EQ(tx(&x, &ex, "p", "/other/key00001", "x", NULL), BERGDB_OK);
        CHECK_EQ(bergdb_sync(x.db, ex.last_pos, BERGDB_SYNC_ORDINARY), BERGDB_OK);
        for (int i = 0; i < nz; i++) {
            snprintf(key, sizeof key, "/prefix/z%04d", i);
            snprintf(value, sizeof value, "z%d", i);
            CHECK(get_is(&x, BERGDB_LATEST, key, value));
        }

        REQUIRE(tdb_restart(&x));
        for (int i = 0; i < nz; i++) {
            snprintf(key, sizeof key, "/prefix/z%04d", i);
            snprintf(value, sizeof value, "z%d", i);
            CHECK(get_is(&x, BERGDB_LATEST, key, value));
        }
        for (int i = 0; i < nb; i++) {
            snprintf(key, sizeof key, "/prefix/b%04d", i);
            CHECK(get_is(&x, BERGDB_LATEST, key, NULL));
        }
        CHECK_EQ(tx(&x, NULL, "p", "/other/key00002", "y", NULL), BERGDB_OK);
        CHECK_EQ(tx(&x, NULL, "p", "/other/key00003", "y", NULL), BERGDB_OK);
        for (int q = 0; q < 30; q++) {
            char other[40];
            snprintf(other, sizeof other, "/other/q%d", q);
            snprintf(key, sizeof key, "/prefix/z%04d", q % nz);
            CHECK_EQ(tx(&x, NULL, "p", other, "y", "d", key, NULL), BERGDB_OK);
        }

        REQUIRE(tdb_restart(&x));
        for (int i = 30; i < nz; i++) {
            snprintf(key, sizeof key, "/prefix/z%04d", i);
            snprintf(value, sizeof value, "z%d", i);
            CHECK(get_is(&x, BERGDB_LATEST, key, value));
        }
        tdb_end(&x);
    }
}

/* DbTesterDelete.testDeleteEveryKey: the climbs reach the space root, which
 * root collapse lowers as it loses its children, down to a segment leaf
 * that stays, empty. In one transaction after the fill, and over several
 * transactions, then puts again, at startup distances that rerun little and
 * all; gets after each step and after restarts. */
TEST(dbt_delete_every_key) {
    const int counts[] = { 1, 7, 100, 2000 };
    for (int di = 0; di < 2; di++) {
        for (int ni = 0; ni < 4; ni++) {
            const int n = counts[ni];
            for (int pi = 0; pi < 2; pi++) {
                const int per = pi == 0 ? n : 13;
                struct tdb x;
                REQUIRE(tdb_new(&x, 8, DISTANCES[di], true));
                char key[40], value[40];
                bergdb_trans *t;
                for (int i = 0; i < n; i += 50) {
                    REQUIRE(bergdb_trans_new(x.db, &t) == BERGDB_OK);
                    for (int j = i; j < (n < i + 50 ? n : i + 50); j++) {
                        snprintf(key, sizeof key, "/k/%d", j);
                        snprintf(value, sizeof value, "v%d", j);
                        CHECK_EQ(put_s(t, key, value), BERGDB_OK);
                    }
                    CHECK_EQ(bergdb_execute(x.db, t, NULL), BERGDB_OK);
                    bergdb_trans_free(t);
                }
                for (int i = 0; i < n; i += per) {
                    REQUIRE(bergdb_trans_new(x.db, &t) == BERGDB_OK);
                    for (int j = i; j < (n < i + per ? n : i + per); j++) {
                        snprintf(key, sizeof key, "/k/%d", j);
                        CHECK_EQ(del_s(t, key), BERGDB_OK);
                    }
                    CHECK_EQ(bergdb_execute(x.db, t, NULL), BERGDB_OK);
                    bergdb_trans_free(t);
                }
                for (int i = 0; i < n; i++) {
                    snprintf(key, sizeof key, "/k/%d", i);
                    CHECK(get_is(&x, BERGDB_LATEST, key, NULL));
                }

                REQUIRE(tdb_restart(&x));
                for (int i = 0; i < n; i++) {
                    snprintf(key, sizeof key, "/k/%d", i);
                    CHECK(get_is(&x, BERGDB_LATEST, key, NULL));
                }
                REQUIRE(bergdb_trans_new(x.db, &t) == BERGDB_OK);
                for (int i = 0; i < n; i += 3) {
                    snprintf(key, sizeof key, "/k/%d", i);
                    snprintf(value, sizeof value, "w%d", i);
                    CHECK_EQ(put_s(t, key, value), BERGDB_OK);
                }
                CHECK_EQ(bergdb_execute(x.db, t, NULL), BERGDB_OK);
                bergdb_trans_free(t);

                REQUIRE(tdb_restart(&x));
                for (int i = 0; i < n; i++) {
                    snprintf(key, sizeof key, "/k/%d", i);
                    snprintf(value, sizeof value, "w%d", i);
                    CHECK(get_is(&x, BERGDB_LATEST, key, i % 3 == 0 ? value : NULL));
                }
                tdb_end(&x);
            }
        }
    }
}

/* DbTesterDelete.testOneOperationAKeyAfterTransformations: KVs that key
 * transformations make one key reach the index as one operation: of them
 * the last put in the order of the keys as written is kept, or a delete if
 * there is no put; a delete never replaces a put. One transaction has, on
 * keys that existed: a transformed put and a plain put (the plain one,
 * later, is kept); a transformed put and a later delete (the put); a delete
 * and a later transformed put (the put); two transformed puts (the later);
 * and a transformed put with a value transformation before a plain put
 * with one (only the kept one's runs). Its database writes the same stream,
 * byte for byte, as one given the kept operations alone, and gives their
 * values at the latest time and after a restart. */
TEST(dbt_one_operation_a_key_after_transformations) {
    for (int di = 0; di < 2; di++) {
        struct tdb x[2];
        for (int d = 0; d < 2; d++) {
            REQUIRE(tdb_new(&x[d], 8, DISTANCES[di], true));
            CHECK_EQ(tx(&x[d], NULL, "p", "/c/a", "old", "p", "/c/b", "old", "p", "/c/c", "old",
                    "p", "/c/d", "old", "p", "/c/e", "old", NULL), BERGDB_OK);
            struct ktf f[6];
            memset(f, 0, sizeof f);
            for (int i = 0; i < 6; i++) {
                f[i].how = 1;
            }
            struct ktf *dropped = &f[4], *kept = &f[5];
            bergdb_trans *t;
            REQUIRE(bergdb_trans_new(x[d].db, &t) == BERGDB_OK);
            if (d == 0) {
                CHECK_EQ(put_tf(t, "/c/$a", "a1", &f[0], true, false), BERGDB_OK);
                CHECK_EQ(put_s(t, "/c/a", "a2"), BERGDB_OK);
                CHECK_EQ(put_tf(t, "/c/$b", "b1", &f[1], true, false), BERGDB_OK);
                CHECK_EQ(del_s(t, "/c/b"), BERGDB_OK);
                CHECK_EQ(del_s(t, "/c/c"), BERGDB_OK);
                CHECK_EQ(put_tf(t, "/c/~c", "c1", &f[2], true, false), BERGDB_OK);
                CHECK_EQ(put_tf(t, "/c/$d", "d1", &f[3], true, false), BERGDB_OK);
                CHECK_EQ(put_tf(t, "/c/~d", "d2", &f[0], true, false), BERGDB_OK);
                CHECK_EQ(put_tf(t, "/c/$e", "e1", dropped, true, true), BERGDB_OK);
                CHECK_EQ(put_tf(t, "/c/e", "e2", kept, false, true), BERGDB_OK);
            } else {
                CHECK_EQ(put_s(t, "/c/a", "a2"), BERGDB_OK);
                CHECK_EQ(put_s(t, "/c/b", "b1"), BERGDB_OK);
                CHECK_EQ(put_s(t, "/c/c", "c1"), BERGDB_OK);
                CHECK_EQ(put_s(t, "/c/d", "d2"), BERGDB_OK);
                CHECK_EQ(put_tf(t, "/c/e", "e2", kept, false, true), BERGDB_OK);
            }
            CHECK_EQ(bergdb_execute(x[d].db, t, NULL), BERGDB_OK);
            bergdb_trans_free(t);
            CHECK_EQ(dropped->calls, 0);    /* the dropped KV's value transformation */
            CHECK_EQ(kept->calls, 1);       /* the kept KV's */
            for (int round = 0; round < 2; round++) {
                CHECK(get_is(&x[d], BERGDB_LATEST, "/c/a", "a2"));
                CHECK(get_is(&x[d], BERGDB_LATEST, "/c/b", "b1"));
                CHECK(get_is(&x[d], BERGDB_LATEST, "/c/c", "c1"));
                CHECK(get_is(&x[d], BERGDB_LATEST, "/c/d", "d2"));
                CHECK(get_is(&x[d], BERGDB_LATEST, "/c/e", "e2!"));
                REQUIRE(tdb_restart(&x[d]));
            }
            tdb_close(&x[d]);
        }
        CHECK(same_streams(x[0].dir, x[1].dir));    /* the same stream */
        remove_dir(x[0].dir);
        remove_dir(x[1].dir);
    }
}

/* DbTesterDelete.testReusedTransKeepsItsKvs (bergdb 023-11, review A, F1),
 * as far as C's API has the case: the sort after the key transformations
 * and its one operation a key are made in a copy for each run, and leave
 * the transaction's pairs as they are. Two puts built at "/template/a" and
 * "/template/b", whose transformation gives each its key by its own state
 * and a switch: in the first run "/x2" and "/x1" (the sort turns them
 * round), in the second "/later/a" and "/later/b"; after the second run,
 * and after a restart, each "/later" key holds its own put's value.
 *
 * With both first keys "/shared" (one put kept, b's), C departs from Java:
 * a C transaction is its builder, which keeps a transformed key in place of
 * the put's key (bergdb.h, struct bergdb_transform) and is built again at
 * each execute, with one put a key (bergdb_trans_put): the second run has
 * b's put only, so "/later/b" is 2 and "/later/a" has no value, where
 * Java's Trans, built once, keeps both KVs and gives "/later/a" 1. */
TEST(dbt_reused_trans_keeps_its_kvs) {
    for (int ci = 0; ci < 2; ci++) {
        bool first = true, collide = ci == 0;
        struct ktf f[2];
        memset(f, 0, sizeof f);
        for (int i = 0; i < 2; i++) {
            f[i].how = 3;
            f[i].slot = i;
            f[i].first = &first;
            f[i].collide = &collide;
        }
        struct tdb x;
        REQUIRE(tdb_new(&x, 8, DISTANCES[1], true));
        bergdb_trans *t;
        REQUIRE(bergdb_trans_new(x.db, &t) == BERGDB_OK);
        CHECK_EQ(put_tf(t, "/template/a", "1", &f[0], true, false), BERGDB_OK);
        CHECK_EQ(put_tf(t, "/template/b", "2", &f[1], true, false), BERGDB_OK);
        CHECK_EQ(bergdb_execute(x.db, t, NULL), BERGDB_OK);
        if (collide) {
            CHECK(get_is(&x, BERGDB_LATEST, "/shared", "2"));
        } else {
            CHECK(get_is(&x, BERGDB_LATEST, "/x2", "1"));
            CHECK(get_is(&x, BERGDB_LATEST, "/x1", "2"));
        }
        first = false;
        CHECK_EQ(bergdb_execute(x.db, t, NULL), BERGDB_OK);
        bergdb_trans_free(t);
        for (int round = 0; round < 2; round++) {
            CHECK(get_is(&x, BERGDB_LATEST, "/later/a", collide ? NULL : "1"));
            CHECK(get_is(&x, BERGDB_LATEST, "/later/b", "2"));
            REQUIRE(tdb_restart(&x));
        }
        tdb_end(&x);
    }
}

#ifndef VECTORS_DIR
#define VECTORS_DIR "test/unit/vectors"
#endif

/* Java's stream NAME of sorted.txt ("sortstream NAME HEX"; Vectors.sorted);
 * its length, -1 if it is not there. The caller frees *out. */
static int64_t java_sorted_stream(const char *name, uint8_t **out) {
    char path[1024];
    const char *dir = getenv("BERGDB_VECTORS");
    snprintf(path, sizeof path, "%s/sorted.txt", dir != NULL ? dir : VECTORS_DIR);
    FILE *f = fopen(path, "r");
    *out = NULL;
    if (f == NULL) {
        return -1;
    }
    char *line = NULL;
    size_t cap = 0;
    ssize_t len;
    int64_t n = -1;
    const size_t nl = strlen(name);
    while (n < 0 && (len = getline(&line, &cap, f)) >= 0) {
        if (strncmp(line, "sortstream ", 11) != 0 || strncmp(line + 11, name, nl) != 0
                || line[11 + nl] != ' ') {
            continue;
        }
        const char *hex = line + 12 + nl;
        size_t hl = strlen(hex);
        while (hl > 0 && (hex[hl - 1] == '\n' || hex[hl - 1] == '\r')) {
            hl--;
        }
        uint8_t *b = malloc(hl / 2 + 1);
        for (size_t i = 0; i < hl / 2; i++) {
            unsigned v = 0;
            sscanf(hex + 2 * i, "%2x", &v);
            b[i] = (uint8_t) v;
        }
        *out = b;
        n = (int64_t) (hl / 2);
    }
    free(line);
    fclose(f);
    return n;
}

/* The transactions with key transformations against Java's bytes (bergdb
 * 022-07; 023-08, section 7): the two runs of Vectors.sorted,
 * DbTester.testTransformedKeysSorted's operations (the transformed puts
 * given in the order (i * 37 + 11) % 60 of their names) and
 * DbTesterDelete.testOneOperationAKeyAfterTransformations's, through C's
 * API, write the streams that release 2026.4's Java wrote, byte for byte.
 * The cross workloads have no transformations, so this is where the sort
 * after the transformations and its one operation a key meet Java's
 * bytes. */
TEST(dbt_transformed_streams_are_javas) {
    for (int run = 0; run < 2; run++) {
        struct tdb x;
        tdb_init(&x, 8, 1000);
        const char *tmp = getenv("TMPDIR");
        snprintf(x.dir, sizeof x.dir, "%s/bergdb-t_dbtester-XXXXXX", tmp != NULL ? tmp : "/tmp");
        REQUIRE(mkdtemp(x.dir) != NULL);
        at(&x, 1000);
        REQUIRE(tdb_start(&x) == BERGDB_OK);
        char key[40], value[40];
        bergdb_trans *t;
        struct ktf *fs = calloc(64, sizeof *fs);
        at(&x, 2000);
        REQUIRE(bergdb_trans_new(x.db, &t) == BERGDB_OK);
        if (run == 0) {
            for (int i = 0; i < 120; i += 2) {
                snprintf(key, sizeof key, "/t/k%03d", i);
                snprintf(value, sizeof value, "old%d", i);
                CHECK_EQ(put_s(t, key, value), BERGDB_OK);
            }
        } else {
            const char *const ks[] = { "/c/a", "/c/b", "/c/c", "/c/d", "/c/e" };
            for (int i = 0; i < 5; i++) {
                CHECK_EQ(put_s(t, ks[i], "old"), BERGDB_OK);
            }
        }
        CHECK_EQ(bergdb_execute(x.db, t, NULL), BERGDB_OK);
        bergdb_trans_free(t);
        at(&x, 2010);
        REQUIRE(bergdb_trans_new(x.db, &t) == BERGDB_OK);
        if (run == 0) {
            for (int i = 0; i < 60; i++) {
                fs[i].how = 2;
                const int name = 2 * ((i * 37 + 11) % 60) + 1;
                snprintf(key, sizeof key, "/t/$%02d=k%03d", i, name);
                snprintf(value, sizeof value, "newk%03d", name);
                CHECK_EQ(put_tf(t, key, value, &fs[i], true, false), BERGDB_OK);
            }
            for (int i = 0; i < 120; i += 6) {
                snprintf(key, sizeof key, "/t/k%03d", i);
                CHECK_EQ(del_s(t, key), BERGDB_OK);
            }
            CHECK_EQ(put_s(t, "/t/k031", "plain"), BERGDB_OK);
        } else {
            for (int i = 0; i < 8; i++) {
                fs[i].how = 1;
            }
            CHECK_EQ(put_tf(t, "/c/$a", "a1", &fs[0], true, false), BERGDB_OK);
            CHECK_EQ(put_s(t, "/c/a", "a2"), BERGDB_OK);
            CHECK_EQ(put_tf(t, "/c/$b", "b1", &fs[1], true, false), BERGDB_OK);
            CHECK_EQ(del_s(t, "/c/b"), BERGDB_OK);
            CHECK_EQ(del_s(t, "/c/c"), BERGDB_OK);
            CHECK_EQ(put_tf(t, "/c/~c", "c1", &fs[2], true, false), BERGDB_OK);
            CHECK_EQ(put_tf(t, "/c/$d", "d1", &fs[3], true, false), BERGDB_OK);
            CHECK_EQ(put_tf(t, "/c/~d", "d2", &fs[4], true, false), BERGDB_OK);
            CHECK_EQ(put_tf(t, "/c/$e", "e1", &fs[5], true, true), BERGDB_OK);
            CHECK_EQ(put_tf(t, "/c/e", "e2", &fs[6], false, true), BERGDB_OK);
        }
        CHECK_EQ(bergdb_execute(x.db, t, NULL), BERGDB_OK);
        bergdb_trans_free(t);
        free(fs);
        tdb_close(&x);

        uint8_t *java = NULL;
        const int64_t jn = java_sorted_stream(run == 0 ? "keys-sorted" : "one-operation", &java);
        struct files *f = malloc(sizeof *f);
        REQUIRE(files_read(x.dir, f));
        CHECK(jn > 0);          /* Java's stream is in sorted.txt */
        CHECK_EQ(f->n, 1);
        CHECK_EQ(f->len[0], jn);
        int64_t first = -1;
        for (int64_t i = 0; first < 0 && i < jn && i < f->len[0]; i++) {
            if (java[i] != f->bytes[0][i]) {
                first = i;
            }
        }
        CHECK_EQ(first, -1);    /* the first byte that differs */
        files_free(f);
        free(f);
        free(java);
        remove_dir(x.dir);
    }
}

/* DbTester.testTransformedKeysSorted: a transaction's KVs reach the index
 * in the order of their keys after the key transformations (bergdb 023-08,
 * section 7, Q4): two databases, each given the same operations, puts
 * through a key transformation in another order and plain deletes, write
 * the same stream, byte for byte, and give the same values, also after a
 * restart. One transformed key is also put by a plain KV: one of the two is
 * kept, the later put in the builder's order, in both databases. */
TEST(dbt_transformed_keys_sorted) {
    enum { N = 60 };
    struct tdb x[2];
    for (int d = 0; d < 2; d++) {
        int names[N];
        for (int i = 0; i < N; i++) {
            names[i] = i;
        }
        uint64_t rs = (uint64_t) (10 + d);
        for (int i = N - 1; i > 0; i--) {       /* Collections.shuffle */
            int j = test_random_below(&rs, i + 1);
            int tmp = names[i];
            names[i] = names[j];
            names[j] = tmp;
        }
        REQUIRE(tdb_new(&x[d], 8, 0, true));
        char key[40], value[40];
        bergdb_trans *t;
        REQUIRE(bergdb_trans_new(x[d].db, &t) == BERGDB_OK);
        for (int i = 0; i < 2 * N; i += 2) {
            snprintf(key, sizeof key, "/t/k%03d", i);
            snprintf(value, sizeof value, "old%d", i);
            CHECK_EQ(put_s(t, key, value), BERGDB_OK);
        }
        CHECK_EQ(bergdb_execute(x[d].db, t, NULL), BERGDB_OK);
        bergdb_trans_free(t);
        struct ktf *fs = calloc(N, sizeof *fs);
        REQUIRE(bergdb_trans_new(x[d].db, &t) == BERGDB_OK);
        for (int i = 0; i < N; i++) {
            /* "/t/$NN=kXXX": the builder's order is NN's, the key after it kXXX. */
            fs[i].how = 2;
            snprintf(key, sizeof key, "/t/$%02d=k%03d", i, 2 * names[i] + 1);
            snprintf(value, sizeof value, "newk%03d", 2 * names[i] + 1);
            CHECK_EQ(put_tf(t, key, value, &fs[i], true, false), BERGDB_OK);
        }
        for (int i = 0; i < 2 * N; i += 6) {
            snprintf(key, sizeof key, "/t/k%03d", i);
            CHECK_EQ(del_s(t, key), BERGDB_OK);
        }
        CHECK_EQ(put_s(t, "/t/k031", "plain"), BERGDB_OK);
        CHECK_EQ(bergdb_execute(x[d].db, t, NULL), BERGDB_OK);
        bergdb_trans_free(t);
        free(fs);

        REQUIRE(tdb_restart(&x[d]));
        for (int i = 0; i < 2 * N; i++) {
            snprintf(key, sizeof key, "/t/k%03d", i);
            snprintf(value, sizeof value, i % 2 == 0 ? "old%d" : "newk%03d", i);
            CHECK(get_is(&x[d], BERGDB_LATEST, key,
                    i % 6 == 0 ? NULL : i == 31 ? "plain" : value));
        }
        tdb_close(&x[d]);
    }
    CHECK(same_streams(x[0].dir, x[1].dir));    /* the same stream */
    remove_dir(x[0].dir);
    remove_dir(x[1].dir);
}

const struct test dbtester_tests[] = {
    TEST_ENTRY(dbt_test1),
    TEST_ENTRY(dbt_test2_and_test3),
    TEST_ENTRY(dbt_test4),
    TEST_ENTRY(dbt_t2_and_versions),
    TEST_ENTRY(dbt_long_keys),
    TEST_ENTRY(dbt_delete),
    TEST_ENTRY(dbt_delete_of_non_existing_data),
    TEST_ENTRY(dbt_rerun),
    TEST_ENTRY(dbt_small_cases),
    TEST_ENTRY(dbt_splits),
    TEST_ENTRY(dbt_with_random_data),
    TEST_ENTRY(dbt_split3),
    TEST_ENTRY(dbt_special_case),
    TEST_ENTRY(dbt_two_binary_keys),
    TEST_ENTRY(dbt_overwrites),
    TEST_ENTRY(dbt_crazy_keys),
    TEST_ENTRY(dbt_get_first),
    TEST_ENTRY(dbt_bug130403),
    TEST_ENTRY(dbt_get_trans_of_every_value),
    TEST_ENTRY(dbt_get_trans_refuses_bad_positions),
    TEST_ENTRY(dbt_crash6_torn_size_below_min),
    TEST_ENTRY(dbt_crash7_at_meta_block_position),
    TEST_ENTRY(dbt_crash8_in_creation),
    TEST_ENTRY(dbt_too_many_dirty_nodes),
    TEST_ENTRY(dbt_records_within_limit),
    TEST_ENTRY(dbt_get_one_and_the_transaction),
    TEST_ENTRY(dbt_null_and_range_arguments),
    TEST_ENTRY(dbt_reads_that_fail_on_the_storage),
    TEST_ENTRY(dbt_transformed_puts_and_deletes_with_restarts),
    TEST_ENTRY(dbt_delete_every_key),
    TEST_ENTRY(dbt_one_operation_a_key_after_transformations),
    TEST_ENTRY(dbt_reused_trans_keeps_its_kvs),
    TEST_ENTRY(dbt_transformed_keys_sorted),
    TEST_ENTRY(dbt_transformed_streams_are_javas),
    TEST_END
};
