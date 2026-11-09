/*
 * Java's DbTesterRestart (bergdb 022-05): restarts of a database in a
 * directory, through db.h, as Java's tests restart a Db on a copy of its
 * MemoryStream: a value, deletes and the history kept; deletes of missing
 * long keys; transactions that change nothing; the meta block's last
 * transaction; the startup distance kept; the top node ordinals across
 * 2^30, 2^31, 2^32 and 2^47, at their end and with reclaim; a record's
 * time, another node size and a meta block without one refused at the
 * start, with Java's texts; Level 2's runs (puts, deletes, short and long
 * keys) whose every key is right at many times after each restart, and
 * whose stream is the one without restarts, byte for byte; one object per
 * node; the STM's boundary kept; getMany after a restart
 * (DbTesterGetMany.test4); random ids (DatabaseId). f_restart.c has the
 * slower ones through the API, and t_sdb.c, t_reclaim.c, t_db.c and
 * f_api.c DbTesterRestart's others (022-05, restart-getmany-trans.md).
 * Each test ends with the allocator's count 0.
 */
#define _DARWIN_C_SOURCE        /* mkdtemp */
#include <dirent.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include "test.h"
#include "bergdb.h"
#include "bytes.h"
#include "clock.h"
#include "db.h"
#include "keys.h"
#include "klong.h"
#include "meta.h"
#include "ntable.h"
#include "topds.h"
#include "trans.h"
#include "transseq.h"

#define RT_FIRST_FILE "00000000000000.bergdb"

/* A database in a directory, restarted as Java's tests restart theirs. */
struct rt {
    struct mem m;
    struct db db;
    struct bergdb_test_clock clock;
    struct db_config cfg;
    char dir[1024];
    bool open;
};

static void rt_init(struct rt *r, int32_t node, int32_t sd) {
    mem_init(&r->m);
    memset(&r->clock, 0, sizeof r->clock);
    memset(&r->cfg, 0, sizeof r->cfg);
    r->cfg.max_node_size = node;
    r->cfg.startup_distance = sd;
    r->cfg.cache_size_indicator = INT64_MAX;
    r->cfg.clock = bergdb_test_clock_time;
    r->cfg.clock_ctx = &r->clock;
    memcpy(r->cfg.id, bergdb_test_id, sizeof r->cfg.id);    /* testSetup's DatabaseId.TEST_ID */
    const char *t = getenv("TMPDIR");
    snprintf(r->dir, sizeof r->dir, "%s/bergdb-t_restart-XXXXXX", t != NULL ? t : "/tmp");
    if (mkdtemp(r->dir) == NULL) {
        r->dir[0] = '\0';
    }
    r->open = false;
}

/* The start (a creation, the first time). */
static enum err_code rt_open(struct rt *r, struct err *e) {
    struct db_start_info info;
    err_clear(e);
    enum err_code rc = db_open(&r->db, r->dir, &r->cfg, &r->m, &info, e);
    r->open = rc == ERR_OK;
    return rc;
}

static void rt_close(struct rt *r) {
    struct err e;
    if (r->open) {
        CHECK_EQ(db_recount(&r->db), 0);
        CHECK(db_close(&r->db, &e) == ERR_OK);
        r->open = false;
    }
}

/* close() and a start on the directory: sync, stop and a copy in Java. */
static bool rt_restart(struct rt *r) {
    struct err e;
    rt_close(r);
    enum err_code rc = rt_open(r, &e);
    if (rc != ERR_OK) {
        printf("    restart: %s: %s\n", e.java, e.text);
    }
    return rc == ERR_OK;
}

static void rt_end(struct rt *r) {
    rt_close(r);
    CHECK_MEM_ZERO(&r->m);
    if (r->dir[0] != '\0') {
        char cmd[1200];
        snprintf(cmd, sizeof cmd, "rm -rf '%s'", r->dir);
        if (system(cmd) != 0) {
            printf("could not remove %s\n", r->dir);
        }
    }
}

/* A transaction under construction: puts and deletes of ikeys. */
struct rtb {
    struct rt *r;
    struct tr_builder b;
    enum err_code rc;
    struct err e;
};

static void rtb_begin(struct rtb *x, struct rt *r) {
    x->r = r;
    x->rc = ERR_OK;
    tr_builder_init(&x->b, &r->m);
}

/* A put of len bytes of v, or a delete (len -1). */
static void rtb_put(struct rtb *x, const char *ikey, const uint8_t *v, int32_t len) {
    uint8_t bkey[128];
    const int32_t kl = (int32_t) strlen(ikey);
    REQUIRE(kl < 100 && keys_ikey_to_bkey((const uint8_t *) ikey, kl, bkey));
    if (x->rc != ERR_OK) {
        return;
    }
    if (len < 0) {
        x->rc = tr_delete(&x->b, bkey, kl, &x->e);
    } else {
        x->rc = tr_put(&x->b, bkey, kl, v != NULL ? v : (const uint8_t *) "", len, NULL, &x->e);
    }
}

static void rtb_puts(struct rtb *x, const char *ikey, const char *value) {
    rtb_put(x, ikey, (const uint8_t *) value, (int32_t) strlen(value));
}

/* Executes the transaction at clock time tt (if later than the clock's);
 * *tpos its record's position (if not NULL). e the refusal's. */
static enum err_code rtb_commit(struct rtb *x, int64_t tt, bool internal, int64_t *tpos,
        struct err *e) {
    struct rt *r = x->r;
    struct trans t;
    tr_init(&t, &r->m);
    if (tt > r->clock.time) {
        bergdb_test_clock_set(&r->clock, tt);
    }
    enum err_code rc = x->rc;
    if (rc != ERR_OK) {
        *e = x->e;
    } else {
        rc = tr_build(&x->b, &t, e);
    }
    if (rc == ERR_OK) {
        t.is_internal = internal;
        rc = db_execute(&r->db, &t, e);
    }
    if (rc == ERR_OK && tpos != NULL) {
        *tpos = t.tpos;
    }
    tr_free(&t);
    tr_builder_free(&x->b);
    return rc;
}

/* A transaction of one put of a string at clock time tt. */
static enum err_code rt_put(struct rt *r, int64_t tt, const char *ikey, const char *value,
        int64_t *tpos) {
    struct rtb x;
    struct err e;
    rtb_begin(&x, r);
    rtb_puts(&x, ikey, value);
    enum err_code rc = rtb_commit(&x, tt, false, tpos, &e);
    if (rc != ERR_OK) {
        printf("    put %s: %s: %s\n", ikey, e.java, e.text);
    }
    return rc;
}

/* getOne at lookup time lt: the value's length, its bytes in out (up to cap); -1 for
 * none, -2 for an error. */
static int32_t rt_get(struct rt *r, int64_t lt, const char *ikey, uint8_t *out, int32_t cap) {
    uint8_t bkey[128];
    int64_t seg[32];
    struct err e;
    const int32_t kl = (int32_t) strlen(ikey);
    if (kl >= 100 || !keys_ikey_to_bkey((const uint8_t *) ikey, kl, bkey)) {
        return -2;
    }
    keys_to_segments(bkey, kl, seg);
    struct getdata gd;
    struct vnode *v = NULL;
    db_new_get_data(&r->db, &gd);
    if (db_get_one(&r->db, lt, seg, keys_segment_count(kl), &gd, &v, &e) != ERR_OK) {
        printf("    get %s at %lld: %s: %s\n", ikey, (long long) lt, e.java, e.text);
        return -2;
    }
    if (v == NULL || v->len < 0) {
        return -1;
    }
    if (out != NULL) {
        memcpy(out, v->value, (size_t) (v->len < cap ? v->len : cap));
    }
    return v->len;
}

/* True if ikey's value at lt is the string 'want' (NULL: none). */
static bool rt_is(struct rt *r, int64_t lt, const char *ikey, const char *want) {
    uint8_t v[256];
    int32_t n = rt_get(r, lt, ikey, v, (int32_t) sizeof v);
    if (want == NULL) {
        return n == -1;
    }
    return n == (int32_t) strlen(want) && memcmp(v, want, (size_t) n) == 0;
}

/* DbUtil.checksum: a digest of every pair at lookup time lt (FNV-1a over the keys'
 * segments and the values), and their count. */
struct rt_digest {
    uint64_t h;
    int64_t n;
};

static bool rt_digest_add(void *ctx, const struct kvt *k) {
    struct rt_digest *d = ctx;
    for (int32_t i = 0; i < k->key_n; i++) {
        d->h = (d->h ^ (uint64_t) k->key[i]) * UINT64_C(1099511628211);
    }
    d->h = (d->h ^ 0xff) * UINT64_C(1099511628211);
    for (int32_t i = 0; k->value != NULL && i < k->value->len; i++) {
        d->h = (d->h ^ k->value->value[i]) * UINT64_C(1099511628211);
    }
    d->h = (d->h ^ 0xfe) * UINT64_C(1099511628211);
    d->n++;
    return true;
}

static uint64_t rt_checksum(struct rt *r, int64_t *count) {
    struct getmany g;
    struct err e;
    struct rt_digest d = { UINT64_C(1469598103934665603), 0 };
    db_new_get_many(&r->db, &g);
    g.lookup_time = INT64_MAX;
    g.result.add = rt_digest_add;
    g.result.ctx = &d;
    CHECK(db_get_many(&r->db, &g, &e) == ERR_OK);
    *count = d.n;
    return d.h;
}

static int64_t rt_super_root(struct rt *r) {
    return tds_get_super_root(&r->db.dag.top_ds)->top_node_id;
}

/* The first file's bytes, into a new buffer (the tests' streams have one file). */
static uint8_t *rt_read_file(const struct rt *r, int64_t *len) {
    char path[1200];
    snprintf(path, sizeof path, "%s/%s", r->dir, RT_FIRST_FILE);
    FILE *f = fopen(path, "rb");
    *len = -1;
    if (f == NULL) {
        return NULL;
    }
    fseek(f, 0, SEEK_END);
    long n = ftell(f);
    fseek(f, 0, SEEK_SET);
    uint8_t *b = malloc(n > 0 ? (size_t) n : 1);
    *len = (int64_t) fread(b, 1, (size_t) n, f);
    fclose(f);
    return b;
}

static void rt_write_file(const struct rt *r, const uint8_t *b, int64_t len) {
    char path[1200];
    snprintf(path, sizeof path, "%s/%s", r->dir, RT_FIRST_FILE);
    FILE *f = fopen(path, "wb");
    REQUIRE(f != NULL);
    if (len > 0) {
        CHECK_EQ((int64_t) fwrite(b, 1, (size_t) len, f), len);
    }
    fclose(f);
}

static int rt_name_cmp(const void *a, const void *b) {
    return strcmp(*(const char *const *) a, *(const char *const *) b);
}

/* The stream's bytes: every NAME.bergdb file of the directory, in the order of
 * their names (the positions where they begin), into a new buffer. */
static uint8_t *rt_read_stream(const struct rt *r, int64_t *len) {
    char *names[64];
    int n = 0;
    DIR *d = opendir(r->dir);
    *len = -1;
    if (d == NULL) {
        return NULL;
    }
    struct dirent *de;
    while ((de = readdir(d)) != NULL && n < 64) {
        size_t k = strlen(de->d_name);
        if (k > 7 && strcmp(de->d_name + k - 7, ".bergdb") == 0) {
            names[n++] = strdup(de->d_name);
        }
    }
    closedir(d);
    qsort(names, (size_t) n, sizeof names[0], rt_name_cmp);
    uint8_t *all = NULL;
    int64_t total = 0;
    for (int i = 0; i < n; i++) {
        char path[1200];
        snprintf(path, sizeof path, "%s/%s", r->dir, names[i]);
        FILE *f = fopen(path, "rb");
        if (f != NULL) {
            fseek(f, 0, SEEK_END);
            long m = ftell(f);
            fseek(f, 0, SEEK_SET);
            all = realloc(all, (size_t) (total + m + 1));
            total += (int64_t) fread(all + total, 1, (size_t) m, f);
            fclose(f);
        }
        free(names[i]);
    }
    *len = total;
    return all;
}

/* True if the first file holds exactly b's len bytes. */
static bool rt_file_is(const struct rt *r, const uint8_t *b, int64_t len) {
    int64_t n;
    uint8_t *now = rt_read_file(r, &n);
    bool same = now != NULL && n == len && memcmp(now, b, (size_t) len) == 0;
    free(now);
    return same;
}

/* ======== Restarts with values and deletes ======== */

/* DbTesterRestart.test0 and DbTesterStream.testDbOnFileMultipleTransactions: a
 * restart has the values and their history. */
TEST(restart_values) {
    struct rt r;
    struct err e;
    int64_t tpos;
    rt_init(&r, 30, 1000000);
    REQUIRE(rt_open(&r, &e) == ERR_OK);
    CHECK(rt_put(&r, 10, "admin1", "Sanna", &tpos) == ERR_OK);
    REQUIRE(rt_restart(&r));
    CHECK(rt_is(&r, INT64_MAX, "admin1", "Sanna"));
    CHECK(rt_is(&r, 9, "admin1", NULL));
    CHECK(rt_is(&r, 10, "admin1", "Sanna"));
    CHECK(rt_put(&r, 20, "admin2", "Sanna2", &tpos) == ERR_OK);
    REQUIRE(rt_restart(&r));
    CHECK(rt_is(&r, 99, "admin1", "Sanna"));
    CHECK(rt_is(&r, 5, "admin1", NULL));
    CHECK(rt_is(&r, 99, "admin2", "Sanna2"));
    CHECK(rt_is(&r, 15, "admin2", NULL));
    rt_end(&r);
}

/* getMany's pairs: the values (up to 8 bytes) and the times. */
struct rt_pairs {
    char v[8][9];
    int64_t time[8];
    int64_t key0[8];
    int32_t n;
};

static bool rt_pairs_add(void *ctx, const struct kvt *k) {
    struct rt_pairs *p = ctx;
    if (p->n < 8 && k->value != NULL && k->value->len <= 8) {
        memcpy(p->v[p->n], k->value->value, (size_t) k->value->len);
        p->v[p->n][k->value->len] = '\0';
        p->time[p->n] = k->time;
        p->key0[p->n] = k->key[0];
        p->n++;
    }
    return true;
}

/* DbTesterGetMany.test4: a getMany after a restart, its nodes read from the stream:
 * the values in the keys' order, the last key's time that of its transaction. */
TEST(restart_get_many) {
    struct rt r;
    struct err e;
    rt_init(&r, 30, 1000000);
    REQUIRE(rt_open(&r, &e) == ERR_OK);
    CHECK(rt_put(&r, 10, "c", "3", NULL) == ERR_OK);
    CHECK(rt_put(&r, 20, "b", "2", NULL) == ERR_OK);
    CHECK(rt_put(&r, 30, "a", "1", NULL) == ERR_OK);
    REQUIRE(rt_restart(&r));
    struct getmany g;
    struct rt_pairs p;
    p.n = 0;
    db_new_get_many(&r.db, &g);
    g.lookup_time = 100;
    g.result.add = rt_pairs_add;
    g.result.ctx = &p;
    CHECK(db_get_many(&r.db, &g, &e) == ERR_OK);
    REQUIRE(p.n == 3);
    CHECK(strcmp(p.v[0], "1") == 0 && strcmp(p.v[1], "2") == 0 && strcmp(p.v[2], "3") == 0);
    uint8_t bkey[8];
    int64_t c;
    CHECK(keys_ikey_to_bkey((const uint8_t *) "c", 1, bkey));
    keys_to_segments(bkey, 1, &c);
    CHECK_EQ(p.key0[2], c);
    CHECK(p.time[2] >= 10 && p.time[2] < 35);
    rt_end(&r);
}

/* DatabaseId.twoRandomIdsShouldNotBeEqual, and testThatNullBytesCannotBeCreated as C
 * has it: two databases created with a random id (bergdb_options.id all zeros, C's
 * DatabaseId.createRandom) have different ids in their meta blocks, neither all zeros,
 * and a restart keeps the id. */
TEST(restart_random_ids) {
    struct rt a, b;
    struct err e;
    static const uint8_t zeros[16];
    rt_init(&a, 30, 1000000);
    rt_init(&b, 30, 1000000);
    memset(a.cfg.id, 0, sizeof a.cfg.id);
    memset(b.cfg.id, 0, sizeof b.cfg.id);
    a.cfg.random_id = true;
    b.cfg.random_id = true;
    REQUIRE(rt_open(&a, &e) == ERR_OK);
    REQUIRE(rt_open(&b, &e) == ERR_OK);
    uint8_t id[16];
    memcpy(id, meta_id(&a.db.rs.meta), 16);
    CHECK(memcmp(id, meta_id(&b.db.rs.meta), 16) != 0);
    CHECK(memcmp(id, zeros, 16) != 0);
    CHECK(memcmp(meta_id(&b.db.rs.meta), zeros, 16) != 0);
    CHECK(rt_put(&a, 10, "/k", "v", NULL) == ERR_OK);
    REQUIRE(rt_restart(&a));
    CHECK(memcmp(meta_id(&a.db.rs.meta), id, 16) == 0);
    rt_end(&a);
    rt_end(&b);
}

/* testRestartOfEmptyDatabase, and dbShouldRememberStartupDistance1 and 2: a
 * database restarted as created, and after one transaction, has what it had, and
 * the startup distance it was created with, whatever the start's setting. */
TEST(restart_empty_and_startup_distance) {
    for (int k = 0; k < 2; k++) {
        struct rt r;
        struct err e;
        rt_init(&r, 30, 400 * 1000);
        REQUIRE(rt_open(&r, &e) == ERR_OK);
        bergdb_test_clock_set(&r.clock, 10);
        if (k == 1) {
            CHECK(rt_put(&r, 10, "key", "value", NULL) == ERR_OK);
        }
        CHECK_EQ(r.db.startup_distance, 400 * 1000);
        int64_t n1, n2;
        const uint64_t c1 = rt_checksum(&r, &n1);
        CHECK_EQ(n1, k);
        r.cfg.startup_distance = 10 * 1000 * 1000;      /* the builder's default, unused */
        REQUIRE(rt_restart(&r));
        CHECK_EQ(r.db.startup_distance, 400 * 1000);
        const uint64_t c2 = rt_checksum(&r, &n2);
        CHECK_EQ(n2, n1);
        CHECK(c1 == c2);
        rt_end(&r);
    }
}

/* longerThanStartup: one key updated 20 times, the stream longer than the startup
 * distance; after a restart every version at its time, the same checksum. */
TEST(restart_longer_than_startup) {
    struct rt r;
    struct err e;
    rt_init(&r, 30, 10 * 1000);
    bergdb_test_clock_set(&r.clock, 2);
    REQUIRE(rt_open(&r, &e) == ERR_OK);
    uint8_t bytes[1000] = {0};
    for (int i = 0; i < 20; i++) {
        struct rtb x;
        bytes[0] = (uint8_t) i;
        rtb_begin(&x, &r);
        rtb_put(&x, "k", bytes, (int32_t) sizeof bytes);
        CHECK(rtb_commit(&x, 100 + i * 10, false, NULL, &e) == ERR_OK);
    }
    CHECK(db_stream_length(&r.db) > 10 * 1000);
    int64_t n1, n2;
    const uint64_t sum1 = rt_checksum(&r, &n1);
    REQUIRE(rt_restart(&r));
    CHECK_EQ(rt_get(&r, 5, "k", NULL, 0), -1);
    for (int i = 0; i < 20; i++) {
        uint8_t v[1000];
        CHECK_EQ(rt_get(&r, 100 + i * 10 + 5, "k", v, (int32_t) sizeof v), 1000);
        CHECK_EQ(v[0], i);
    }
    const uint64_t sum2 = rt_checksum(&r, &n2);
    CHECK(sum1 == sum2 && n1 == n2);
    rt_end(&r);
}

/* testDelete1 and testDelete2: a delete and its history over a restart; deletes of
 * existing and missing keys with a put in one transaction, the same checksum after. */
TEST(restart_deletes) {
    struct rt r;
    struct err e;
    struct rtb x;
    rt_init(&r, 30, 1000000);
    REQUIRE(rt_open(&r, &e) == ERR_OK);
    CHECK(rt_put(&r, 10, "k1", "k1-value", NULL) == ERR_OK);
    rtb_begin(&x, &r);
    rtb_put(&x, "k1", NULL, -1);
    CHECK(rtb_commit(&x, 20, false, NULL, &e) == ERR_OK);
    REQUIRE(rt_restart(&r));
    CHECK(rt_is(&r, 15, "k1", "k1-value"));
    CHECK(rt_is(&r, 25, "k1", NULL));
    rt_end(&r);

    rt_init(&r, 30, 1000000);
    REQUIRE(rt_open(&r, &e) == ERR_OK);
    rtb_begin(&x, &r);
    rtb_puts(&x, "k1", "k1-value");
    rtb_puts(&x, "k2", "k2-value");
    CHECK(rtb_commit(&x, 10, false, NULL, &e) == ERR_OK);
    rtb_begin(&x, &r);
    rtb_put(&x, "k1", NULL, -1);
    rtb_put(&x, "k2", NULL, -1);
    rtb_put(&x, "kk", NULL, -1);
    rtb_puts(&x, "k3", "k3-value");
    CHECK(rtb_commit(&x, 20, false, NULL, &e) == ERR_OK);
    int64_t n1, n2;
    const uint64_t sum1 = rt_checksum(&r, &n1);
    CHECK_EQ(n1, 1);
    REQUIRE(rt_restart(&r));
    const uint64_t sum2 = rt_checksum(&r, &n2);
    CHECK(sum1 == sum2 && n1 == n2);
    CHECK(rt_is(&r, 15, "k2", "k2-value"));
    rt_end(&r);
}

/* testDeleteMissingLongKey: deletes of missing keys of more than one segment, then
 * two restarts. Java's bug of 2026-10-12: the delete made a key node for a missing
 * segment, the rerun at the start did not, so the node ids differed after the first
 * restart, and the second failed. */
TEST(restart_delete_missing_long_key) {
    struct rt r;
    struct err e;
    struct rtb x;
    rt_init(&r, 30, 1000000);
    REQUIRE(rt_open(&r, &e) == ERR_OK);
    rtb_begin(&x, &r);
    rtb_puts(&x, "/a", "a-value");
    rtb_puts(&x, "/abcdefXX", "x-value");
    CHECK(rtb_commit(&x, 10, false, NULL, &e) == ERR_OK);
    rtb_begin(&x, &r);
    rtb_put(&x, "/k/1000", NULL, -1);           /* two segments, both missing */
    CHECK(rtb_commit(&x, 20, false, NULL, &e) == ERR_OK);
    rtb_begin(&x, &r);
    rtb_put(&x, "/abcdefgh12345", NULL, -1);    /* three segments, the first exists */
    CHECK(rtb_commit(&x, 30, false, NULL, &e) == ERR_OK);
    CHECK(rt_put(&r, 40, "/b", "b-value", NULL) == ERR_OK);
    int64_t n, n2;
    const uint64_t sum1 = rt_checksum(&r, &n);
    REQUIRE(rt_restart(&r));
    CHECK(rt_checksum(&r, &n2) == sum1 && n2 == n);
    CHECK(rt_put(&r, 50, "/c", "c-value", NULL) == ERR_OK);
    const uint64_t sum2 = rt_checksum(&r, &n);
    REQUIRE(rt_restart(&r));
    CHECK(rt_checksum(&r, &n2) == sum2 && n2 == n);
    CHECK(rt_is(&r, INT64_MAX, "/a", "a-value"));
    CHECK(rt_is(&r, INT64_MAX, "/abcdefXX", "x-value"));
    CHECK(rt_is(&r, INT64_MAX, "/c", "c-value"));
    CHECK(rt_is(&r, INT64_MAX, "/k/1000", NULL));
    rt_end(&r);
}

/* testRestartAfterTransactionsThatChangeNothing: transactions without pairs (mode
 * 0) or with deletes of missing keys (1) do not mark the super root; enough of them
 * move the startup position past every top node version, and a start finds the
 * super root by the last transaction's topPos. Java's M18 of 011-11: "Could not
 * find super node in startup section". */
TEST(restart_after_changing_nothing) {
    for (int mode = 0; mode < 2; mode++) {
        struct rt r;
        struct err e;
        rt_init(&r, 8, 100);
        REQUIRE(rt_open(&r, &e) == ERR_OK);
        int64_t time = 10;
        char key[32], value[32];
        for (int i = 0; i < 50; i++) {
            snprintf(key, sizeof key, "/k/%d", i);
            snprintf(value, sizeof value, "v%d", i);
            CHECK(rt_put(&r, time++, key, value, NULL) == ERR_OK);
        }
        for (int round = 0; round < 3; round++) {
            for (int i = 0; i < 40; i++) {
                struct rtb x;
                rtb_begin(&x, &r);
                if (mode == 1) {
                    snprintf(key, sizeof key, "/missing/%d/%d", round, i);
                    rtb_put(&x, key, NULL, -1);
                }
                CHECK(rtb_commit(&x, time++, false, NULL, &e) == ERR_OK);
            }
            REQUIRE(rt_restart(&r));
            for (int i = 0; i < 50; i++) {
                snprintf(key, sizeof key, "/k/%d", i);
                snprintf(value, sizeof value, "v%d", i);
                CHECK(rt_is(&r, INT64_MAX, key, value));
            }
            snprintf(key, sizeof key, "/k/%d", round);
            snprintf(value, sizeof value, "v%d", round);
            CHECK(rt_put(&r, time++, key, value, NULL) == ERR_OK);
        }
        rt_end(&r);
    }
}

/* testLastTransPosAfterRestart: after a restart the meta block in memory names the
 * last transaction, as without the restart, so that the next meta block written is
 * the same. Java's bug of 2026-10-12: it kept the position of the last meta block
 * on disk. */
TEST(restart_last_trans_pos) {
    struct rt r;
    struct err e;
    rt_init(&r, 30, 1000000);
    REQUIRE(rt_open(&r, &e) == ERR_OK);
    int64_t lastTpos = -1;
    for (int i = 0; i < 10; i++) {
        char key[32];
        snprintf(key, sizeof key, "/k/%d", i);
        CHECK(rt_put(&r, 10 + 10 * i, key, "value", &lastTpos) == ERR_OK);
    }
    CHECK_EQ(meta_last_trans(&r.db.rs.meta), lastTpos);
    REQUIRE(rt_restart(&r));
    CHECK_EQ(meta_last_trans(&r.db.rs.meta), lastTpos);
    rt_end(&r);
}

/* The actual lookup time of a getOne of ikey at the latest time. */
static int64_t rt_read_time(struct rt *r, const char *ikey) {
    uint8_t bkey[128];
    int64_t seg[32];
    struct err e;
    const int32_t kl = (int32_t) strlen(ikey);
    CHECK(keys_ikey_to_bkey((const uint8_t *) ikey, kl, bkey));
    keys_to_segments(bkey, kl, seg);
    struct getdata gd;
    struct vnode *v = NULL;
    db_new_get_data(&r->db, &gd);
    CHECK(db_get_one(&r->db, INT64_MAX, seg, keys_segment_count(kl), &gd, &v, &e) == ERR_OK);
    return gd.actual_lookup_time;
}

/* A transaction with lookup time lt, a key read of "/k" (if read) and a put of "/j". */
static enum err_code stm_put(struct rt *r, int64_t lt, bool read, const char *value,
        struct err *e) {
    struct rtb x;
    uint8_t bkey[8];
    rtb_begin(&x, r);
    CHECK(keys_ikey_to_bkey((const uint8_t *) "/k", 2, bkey));
    if (read) {
        x.rc = tr_key_read(&x.b, bkey, 2, &x.e);
    }
    if (x.rc == ERR_OK) {
        x.rc = tr_lookup_time(&x.b, lt, &x.e);
    }
    rtb_puts(&x, "/j", value);
    return rtb_commit(&x, r->clock.time + 10, false, NULL, e);
}

/* assertStmRefused: a read of "/k" at readTime is stale; refused (RerunException),
 * nothing written, "/j" as it was. */
static void stm_refused(struct rt *r, int64_t readTime) {
    struct err e;
    uint8_t before[64];
    const int64_t length = db_stream_length(&r->db);
    const int32_t n = rt_get(r, INT64_MAX, "/j", before, (int32_t) sizeof before);
    CHECK_EQ(stm_put(r, readTime, true, "stale", &e), ERR_RERUN);
    CHECK_EQ(db_stream_length(&r->db), length);
    uint8_t after[64];
    CHECK_EQ(rt_get(r, INT64_MAX, "/j", after, (int32_t) sizeof after), n);
    CHECK(n < 0 || memcmp(before, after, (size_t) n) == 0);
}

/* testStmAfterRestart (005-70, option A): real read results carried to a restarted
 * database: the boundary is the last commit, one without writes included; after the
 * restart a stale read is refused, also after an empty commit; a read at the boundary
 * commits, and the first unrelated write keeps the coverage; new writes conflict as
 * before; a transaction without reads commits at any lookup time. Startup distances of
 * 100 and 1,000,000 bytes. f_api.c's api_stm_after_restart has a part, through the
 * API. */
TEST(restart_stm) {
    const int32_t sds[2] = { 100, 1000000 };
    for (int k = 0; k < 2; k++) {
        struct rt r;
        struct err e;
        rt_init(&r, 30, sds[k]);
        REQUIRE(rt_open(&r, &e) == ERR_OK);
        CHECK(rt_put(&r, 10, "/k", "1", NULL) == ERR_OK);
        CHECK(rt_is(&r, INT64_MAX, "/k", "1"));
        const int64_t oldReadTime = rt_read_time(&r, "/k");
        CHECK(rt_put(&r, 20, "/k", "2", NULL) == ERR_OK);
        struct rtb x;
        rtb_begin(&x, &r);
        CHECK(rtb_commit(&x, 30, false, NULL, &e) == ERR_OK);      /* no writes */
        const int64_t boundary = rt_read_time(&r, "/k");
        CHECK(boundary > oldReadTime);
        stm_refused(&r, oldReadTime);
        REQUIRE(rt_restart(&r));
        stm_refused(&r, oldReadTime);
        rtb_begin(&x, &r);
        CHECK(rtb_commit(&x, r.clock.time + 10, false, NULL, &e) == ERR_OK);
        stm_refused(&r, oldReadTime);
        CHECK(stm_put(&r, boundary, true, "1", &e) == ERR_OK);      /* equality is safe */
        CHECK(stm_put(&r, boundary, true, "2", &e) == ERR_OK);
        CHECK(rt_is(&r, INT64_MAX, "/j", "2"));
        CHECK(rt_put(&r, r.clock.time + 10, "/k", "3", NULL) == ERR_OK);
        stm_refused(&r, boundary);
        CHECK(stm_put(&r, rt_read_time(&r, "/k"), true, "3", &e) == ERR_OK);
        CHECK(stm_put(&r, oldReadTime, false, "4", &e) == ERR_OK);
        CHECK(rt_is(&r, INT64_MAX, "/j", "4"));
        rt_end(&r);
    }
}

/* ======== The top node ordinals (005-02) ======== */

/* startOrdinalTest: node size 8, the second top node's ordinal 'second'; setup 0 a
 * startup distance of 1,000 bytes, 1 of 100,000, 2 of 1,000 with every evictable
 * object evicted at the end of every call (Java's Eviction.Schedule.EVERY; C's
 * budget of one byte). */
static void ordinal_init(struct rt *r, int setup, int64_t second) {
    rt_init(r, 8, setup == 1 ? 100000 : 1000);
    r->cfg.second_top_ordinal = second;
    if (setup == 2) {
        r->cfg.cache_size_indicator = 1;
    }
}

/* checkHotHistory: "/hot" at the time of each of the n transactions, 10 (k + 1),
 * is "v" + k. */
static void check_hot_history(struct rt *r, int n, const char *what, int64_t boundary,
        int setup) {
    int bad = 0;
    for (int k = 0; k < n; k++) {
        char v[32];
        snprintf(v, sizeof v, "v%d", k);
        if (!rt_is(r, 10 * (int64_t) (k + 1), "/hot", v)) {
            bad++;
        }
    }
    CHECK_EQ(bad, 0);
    if (bad != 0) {
        printf("    boundary %lld, setup %d, %s: %d values wrong\n", (long long) boundary, setup,
                what, bad);
    }
}

static enum err_code put_hot(struct rt *r, int n) {
    char v[32];
    snprintf(v, sizeof v, "v%d", n);
    return rt_put(r, 10 * (int64_t) (n + 1), "/hot", v, NULL);
}

/* testOrdinalsAcrossBoundaries: databases cross the top node ordinals 2^30, 2^31,
 * 2^32 and 2^47 and restart with their history; the next top node continues the
 * ordinals. The second top node starts 20 below the boundary; one key updated in
 * every transaction makes a new top node about every four. With a startup distance
 * of 1,000 bytes a restart reads top nodes above the boundary from the stream, with
 * 100,000 it makes them all again, and with everything evicted after every call the
 * reads load top nodes. */
TEST(restart_ordinals_across_boundaries) {
    const int64_t boundaries[4] = { INT64_C(1) << 30, INT64_C(1) << 31, INT64_C(1) << 32,
            INT64_C(1) << 47 };
    for (int b = 0; b < 4; b++) {
        for (int setup = 0; setup < 3; setup++) {
            const int64_t boundary = boundaries[b];
            struct rt r;
            struct err e;
            ordinal_init(&r, setup, boundary - 20);
            REQUIRE(rt_open(&r, &e) == ERR_OK);
            int n = 0;
            while (rt_super_root(&r) < boundary + 20) {
                REQUIRE(n < 1000);
                REQUIRE(put_hot(&r, n) == ERR_OK);
                n++;
            }
            if (setup != 1) {
                CHECK(r.db.newest_written_top != NULL
                        && r.db.newest_written_top->top_node_id >= boundary);
            }
            check_hot_history(&r, n, "before the restart", boundary, setup);
            const int64_t superRoot = rt_super_root(&r);
            REQUIRE(rt_restart(&r));
            CHECK_EQ(rt_super_root(&r), superRoot);
            check_hot_history(&r, n, "after the restart", boundary, setup);
            while (rt_super_root(&r) == superRoot) {
                REQUIRE(n < 2000);
                REQUIRE(put_hot(&r, n) == ERR_OK);
                n++;
            }
            CHECK_EQ(rt_super_root(&r), superRoot + 1);
            check_hot_history(&r, n, "at the end", boundary, setup);
            rt_end(&r);
        }
    }
}

/* assertRefused: refused with Java's DbException text, nothing written. */
static void check_end_refused(struct rt *r, bool two) {
    struct rtb x;
    struct err e;
    const int64_t length = db_stream_length(&r->db);
    rtb_begin(&x, r);
    if (two) {
        rtb_puts(&x, "/other", "x");
    }
    rtb_puts(&x, "/hot", "x");
    CHECK_EQ(rtb_commit(&x, r->clock.time + 10, false, NULL, &e), ERR_LIMIT);
    CHECK(strcmp(e.java, "DbException") == 0);
    CHECK(strncmp(e.text, "The database has used its top node ordinals", 43) == 0);
    CHECK_EQ(db_stream_length(&r->db), length);
}

/* testEndOfOrdinals: once the super root's ordinal is LAST_TOP_ORDINAL, 1,024 below
 * the bound, a user transaction is refused before it changes anything: the keys keep
 * their values, no node is left in the writer's list, the history is right, and the
 * database restarts and refuses again. An internal transaction is not refused
 * (reclaim's run in the margin below the bound). */
TEST(restart_end_of_ordinals) {
    struct rt r;
    struct err e;
    ordinal_init(&r, 0, DB_LAST_TOP_ORDINAL - 10);
    REQUIRE(rt_open(&r, &e) == ERR_OK);
    int n = 0;
    while (rt_super_root(&r) < DB_LAST_TOP_ORDINAL) {
        REQUIRE(n < 1000);
        REQUIRE(put_hot(&r, n) == ERR_OK);
        n++;
    }
    for (int round = 0; round < 2; round++) {
        check_end_refused(&r, false);
        check_end_refused(&r, true);
        CHECK_EQ(rt_super_root(&r), DB_LAST_TOP_ORDINAL);
        CHECK_EQ(tns_size(&r.db.trans_nodes), 0);
        CHECK(rt_is(&r, INT64_MAX, "/other", NULL));
        char v[32];
        snprintf(v, sizeof v, "v%d", n - 1);
        CHECK(rt_is(&r, INT64_MAX, "/hot", v));
        check_hot_history(&r, n, round == 0 ? "before the restart" : "after the restart",
                DB_LAST_TOP_ORDINAL, 0);
        REQUIRE(rt_restart(&r));
    }
    struct rtb x;
    rtb_begin(&x, &r);
    rtb_puts(&x, "/internal", "i");
    CHECK(rtb_commit(&x, 10 * (int64_t) (n + 1), true, NULL, &e) == ERR_OK);
    CHECK(rt_is(&r, INT64_MAX, "/internal", "i"));
    check_end_refused(&r, false);
    rt_end(&r);
}

/* testOrdinalsWithReclaim's run (005-02): the top node ordinals across 2^32, or to the
 * end, with reclaim. "/hot" updated in every transaction, "/cold" written in the first
 * only, which reclaim rewrites; node size 8, a startup distance of 2,000 bytes, the second
 * top node's ordinal 'second', a retention of one second set at every start (written
 * once), 20 transactions a second. A restart every 150 transactions, after each every key
 * checked at every transaction's time from the first available time on. Runs until the
 * super root's ordinal is 'until' or a transaction is refused. */
struct ow_model {
    int64_t times[5000];
    int32_t n;
    int64_t cold_time;
};

static enum err_code ow_open(struct rt *r, struct err *e) {
    enum err_code rc = rt_open(r, e);
    if (rc == ERR_OK) {
        rc = db_set_retain_duration(&r->db, CLK_UNITS_PER_SEC, e);
    }
    return rc;
}

/* checkModel: "/hot" at transaction k's time is "v" + k, "/cold" "v0" (the first's). */
static void ow_check(struct rt *r, const struct ow_model *mo, const char *what) {
    const int64_t first = db_first_available_time(&r->db);
    int bad = 0;
    for (int32_t k = 0; k < mo->n; k++) {
        if (mo->times[k] < first) {
            continue;
        }
        char v[32];
        snprintf(v, sizeof v, "v%d", (int) k);
        if (!rt_is(r, mo->times[k], "/hot", v) || !rt_is(r, mo->times[k], "/cold", "v0")) {
            bad++;
        }
    }
    CHECK_EQ(bad, 0);
    if (bad != 0) {
        printf("    %s: %d times wrong\n", what, bad);
    }
}

static void run_ordinals_with_reclaim(int64_t second, int64_t until) {
    static struct ow_model mo;
    struct rt r;
    struct err e;
    rt_init(&r, 8, 2000);
    r.cfg.second_top_ordinal = second;
    int64_t time = CLK_UNITS_PER_SEC;
    bergdb_test_clock_set(&r.clock, time);
    REQUIRE(ow_open(&r, &e) == ERR_OK);
    mo.n = 0;
    int64_t secondTime = -1;
    bool refused = false;
    for (int i = 0; !refused && rt_super_root(&r) < until; i++) {
        REQUIRE(i < 5000);
        time += CLK_UNITS_PER_SEC / 20;
        char v[32];
        snprintf(v, sizeof v, "v%d", i);
        struct rtb x;
        rtb_begin(&x, &r);
        rtb_puts(&x, "/hot", v);
        if (i == 0) {
            rtb_puts(&x, "/cold", v);
        }
        enum err_code rc = rtb_commit(&x, time, false, NULL, &e);
        if (rc != ERR_OK) {
            CHECK(rc == ERR_LIMIT && until == INT64_MAX
                    && rt_super_root(&r) >= DB_LAST_TOP_ORDINAL);
            refused = true;
            continue;
        }
        mo.times[mo.n++] = time;
        if (secondTime == -1 && rt_super_root(&r) >= second) {
            secondTime = time;
        }
        if (i % 150 == 149) {
            rt_close(&r);
            REQUIRE(ow_open(&r, &e) == ERR_OK);
            ow_check(&r, &mo, "after a restart");
        }
    }
    CHECK(db_first_available_pos(&r.db) > 0);
    CHECK(secondTime != -1 && db_first_available_time(&r.db) > secondTime);
    const int64_t superRoot = rt_super_root(&r);
    if (until == INT64_MAX) {
        CHECK(refused);
        CHECK(superRoot >= DB_LAST_TOP_ORDINAL && superRoot <= DB_LAST_TOP_ORDINAL + 5);
        check_end_refused(&r, false);
    }
    ow_check(&r, &mo, "at the end");
    rt_close(&r);
    REQUIRE(ow_open(&r, &e) == ERR_OK);
    CHECK_EQ(rt_super_root(&r), superRoot);
    ow_check(&r, &mo, "after the last restart");
    if (until == INT64_MAX) {
        check_end_refused(&r, false);
    }
    rt_end(&r);
}

/* testOrdinalsWithReclaim: the ordinals across 2^32 and to the end with reclaim, which
 * cuts the front of the stream, from about transaction 900 on, with the first top node
 * and the second, whose skip pointers name the first; restarts every 150. Near the end,
 * reclaim's internal transactions are not refused, and their top nodes stay within
 * Db.TOP_ORDINAL_MARGIN, at most five above LAST_TOP_ORDINAL. */
TEST(restart_ordinals_with_reclaim) {
    run_ordinals_with_reclaim((INT64_C(1) << 32) - 400, (INT64_C(1) << 32) + 300);
    run_ordinals_with_reclaim(DB_LAST_TOP_ORDINAL - 400, INT64_MAX);
}

/* ======== Refusals at a start ======== */

/* testCorruptRecordTimesRefused: a record's time, in its header (no checksum), set
 * to one not after the record before or out of the 56-bit range is refused at the
 * start, before the replay, with Java's StreamFormatException; the creation's
 * record too. Nothing written. */
TEST(restart_record_times_refused) {
    struct rt r;
    struct err e;
    int64_t lastPos = -1;
    rt_init(&r, 30, 1000000);
    REQUIRE(rt_open(&r, &e) == ERR_OK);
    CHECK(rt_put(&r, 10, "/k1", "1", NULL) == ERR_OK);
    CHECK(rt_put(&r, 20, "/k2", "2", NULL) == ERR_OK);
    CHECK(rt_put(&r, 30, "/k3", "3", &lastPos) == ERR_OK);
    rt_close(&r);
    int64_t len;
    uint8_t *file = rt_read_file(&r, &len);
    REQUIRE(file != NULL && lastPos > 0 && lastPos + 16 < len);
    const int64_t bad[8][2] = {
        { lastPos, 20 }, { lastPos, 10 }, { lastPos, 0 }, { lastPos, -1 },
        { lastPos, KL_MAX_TIME + 1 }, { lastPos, INT64_MAX },
        { META_BLOCK_SIZE, -1 }, { META_BLOCK_SIZE, KL_MAX_TIME + 1 },
    };
    uint8_t *copy = malloc((size_t) len);
    for (int i = 0; i < 8; i++) {
        memcpy(copy, file, (size_t) len);
        bytes_put_long_le(bad[i][1], copy + bad[i][0] + 8);
        rt_write_file(&r, copy, len);
        CHECK_EQ(rt_open(&r, &e), ERR_FORMAT);
        const char *message = bad[i][1] < 0 || bad[i][1] > KL_MAX_TIME
                ? "Transaction time out of range" : "non-increasing tt";
        CHECK(strcmp(e.java, "StreamFormatException") == 0 && strstr(e.text, message) != NULL);
        if (strstr(e.text, message) == NULL) {
            printf("    record time %lld at %lld: %s: %s\n", (long long) bad[i][1],
                    (long long) bad[i][0], e.java, e.text);
        }
        rt_close(&r);
        CHECK(rt_file_is(&r, copy, len));
    }
    rt_write_file(&r, file, len);
    REQUIRE(rt_open(&r, &e) == ERR_OK);
    CHECK(rt_is(&r, INT64_MAX, "/k3", "3"));
    free(copy);
    free(file);
    rt_end(&r);
}

/* testOtherNodeSizeRefused (005-50): a start with another maximum node size than the
 * database was created with is refused with Java's StreamFormatException, naming
 * both, and writes nothing; then a start with the database's size starts. Every pair
 * of 8, 14, 30 and 62, on a database as created and on one of 300 transactions whose
 * last record a crash has torn (3 bytes cut), which recovery fills out. */
TEST(restart_other_node_size_refused) {
    const int32_t sizes[4] = { 8, 14, 30, 62 };
    for (int ia = 0; ia < 4; ia++) {
        const int32_t a = sizes[ia];
        for (int torn = 0; torn < 2; torn++) {
            struct rt r;
            struct err e;
            rt_init(&r, a, 1000000);
            REQUIRE(rt_open(&r, &e) == ERR_OK);
            for (int i = 0; torn && i < 300; i++) {
                char key[32], value[32];
                snprintf(key, sizeof key, "key%d", i);
                snprintf(value, sizeof value, "value%d", i);
                CHECK(rt_put(&r, 10 + i, key, value, NULL) == ERR_OK);
            }
            rt_close(&r);
            int64_t len;
            uint8_t *file = rt_read_file(&r, &len);
            REQUIRE(file != NULL);
            if (torn) {
                len -= 3;
                rt_write_file(&r, file, len);
            }
            for (int ib = 0; ib < 4; ib++) {
                const int32_t b = sizes[ib];
                if (b == a) {
                    continue;
                }
                r.cfg.max_node_size = b;
                CHECK_EQ(rt_open(&r, &e), ERR_FORMAT);
                rt_close(&r);
                char want[100];
                snprintf(want, sizeof want, "maximum node size is %d, and this start uses %d.",
                        (int) a, (int) b);
                CHECK(strcmp(e.java, "StreamFormatException") == 0
                        && strstr(e.text, want) != NULL);
                CHECK(rt_file_is(&r, file, len));
            }
            r.cfg.max_node_size = a;
            REQUIRE(rt_open(&r, &e) == ERR_OK);
            if (torn) {
                CHECK(rt_is(&r, INT64_MAX, "key298", "value298"));
                CHECK(rt_is(&r, INT64_MAX, "key299", NULL));       /* torn */
            }
            free(file);
            rt_end(&r);
        }
    }
}

/* testNoNodeSizeRefused (005-50): a meta block without a maximum node size (bytes 44
 * and 45 zero), as one written before 2026-10-27, is refused with Java's
 * VersioningStreamException, whatever size the start uses; nothing written. */
TEST(restart_no_node_size_refused) {
    struct rt r;
    struct err e;
    rt_init(&r, 30, 1000000);
    REQUIRE(rt_open(&r, &e) == ERR_OK);
    CHECK(rt_put(&r, 10, "key1", "value1", NULL) == ERR_OK);
    rt_close(&r);
    int64_t len;
    uint8_t *file = rt_read_file(&r, &len);
    REQUIRE(file != NULL && len < 200000);
    file[44] = 0;
    file[45] = 0;
    rt_write_file(&r, file, len);
    const int32_t sizes[2] = { 8, 30 };
    for (int i = 0; i < 2; i++) {
        r.cfg.max_node_size = sizes[i];
        CHECK(rt_open(&r, &e) != ERR_OK);
        rt_close(&r);
        CHECK(strcmp(e.java, "VersioningStreamException") == 0
                && strstr(e.text, "meta block has no maximum node size") != NULL);
        CHECK(rt_file_is(&r, file, len));
    }
    free(file);
    rt_end(&r);
}

/* ======== One object per node ======== */

/* identityViolations: every node in D is the node table's object for its id and is
 * dirty; every dirty top or key node reachable by memory pointers from the super root
 * is in D; and no id has two dirty objects. The count of problems. */
struct ident {
    const void *in_d[4096];
    int32_t nd;
    int problems;
    struct ntable *table;
};

static void ident_visit(void *ctx, const struct ts_node *tn, int64_t tpos, int64_t lastTpos) {
    struct ident *x = ctx;
    (void) tpos;
    (void) lastTpos;
    const struct node *node = tn->node;
    if (x->nd < 4096) {
        x->in_d[x->nd++] = node;
    }
    if (nt_get_node(x->table, tn->id) != node) {
        x->problems++;
        printf("    node %lld in D is not in the node table\n", (long long) tn->id);
    }
    if (!node_is_dirty(node)) {
        x->problems++;
        printf("    node %lld in D is not dirty\n", (long long) tn->id);
    }
}

static int identity_violations(struct db *db) {
    static struct ident x;
    x.nd = 0;
    x.problems = 0;
    x.table = &db->node_table;
    ts_visit_got_dirty_nodes(&db->trans_seq, INT64_MAX, ident_visit, &x);
    static const struct node *seen[8192];
    static const struct node *stack[8192];
    int32_t nseen = 0, top = 0;
    stack[top++] = &tds_get_super_root(&db->dag.top_ds)->n;
    while (top > 0) {
        const struct node *n = stack[--top];
        bool was = false;
        for (int32_t i = 0; i < nseen && !was; i++) {
            was = seen[i] == n;
        }
        if (was || n->o.kind == OBJ_VALUE) {
            continue;
        }
        if (nseen == 8192) {
            CHECK(false);
            return x.problems + 1;
        }
        seen[nseen++] = n;
        if (node_is_dirty(n)) {
            bool inD = false;
            for (int32_t i = 0; i < x.nd && !inD; i++) {
                inD = x.in_d[i] == n;
            }
            if (!inD) {
                x.problems++;
                printf("    dirty node %lld is not in D\n", (long long) n->id);
            }
            for (int32_t i = 0; i + 1 < nseen; i++) {
                if (seen[i]->id == n->id && node_is_dirty(seen[i])) {
                    x.problems++;
                    printf("    two dirty objects for node %lld\n", (long long) n->id);
                }
            }
        }
        const int32_t size = node_size(n);
        for (int32_t i = 0; i < size; i++) {
            struct node *c = node_pointer_node(n, i);
            if (c != NULL && top < 8192) {
                stack[top++] = c;
            }
            CHECK(top < 8192);
        }
    }
    return x.problems;
}

/* testOneObjectPerNodeAfterRestarts: one object per node after restarts with the
 * bounded startup (Level 2), checked after each of the first 20 transactions after
 * each restart. Java's bugs of 2026-10-12: after a restart, D could hold a copy of a
 * node read from the stream while the Dag held another object with the same id; and
 * Db and NodeCollection had a node table each. */
TEST(restart_one_object_per_node) {
    struct rt r;
    struct err e;
    uint64_t rnd = 1;
    rt_init(&r, 30, 10 * 1000);
    REQUIRE(rt_open(&r, &e) == ERR_OK);
    int64_t time = 10;
    int restarts = 0;
    int problems = 0;
    for (int i = 0; i < 1000 && problems == 0; i++) {
        time += 10;
        struct rtb x;
        rtb_begin(&x, &r);
        int32_t keys[3];
        int32_t nk = 0;
        const int32_t ops = 1 + test_random_below(&rnd, 3);
        while (nk < ops) {
            const int32_t k = test_random_below(&rnd, 500);
            bool seen = false;
            for (int32_t j = 0; j < nk; j++) {
                seen = seen || keys[j] == k;
            }
            if (!seen) {
                keys[nk++] = k;
            }
        }
        for (int32_t j = 0; j < nk; j++) {
            char key[32];
            uint8_t v[40];
            const int32_t len = 1 + test_random_below(&rnd, 40);
            for (int32_t q = 0; q < len; q++) {
                v[q] = (uint8_t) test_random(&rnd);
            }
            snprintf(key, sizeof key, "/k/%d", (int) keys[j]);
            rtb_put(&x, key, v, len);
        }
        REQUIRE(rtb_commit(&x, time, false, NULL, &e) == ERR_OK);
        if (i % 250 == 249) {
            REQUIRE(rt_restart(&r));
            restarts++;
        }
        if (restarts > 0 && i % 250 < 20) {
            problems += identity_violations(&r.db);
            if (problems != 0) {
                printf("    after transaction %d\n", i);
            }
        }
    }
    CHECK_EQ(problems, 0);
    CHECK(r.db.startup_pos.startupPos > META_BLOCK_SIZE);
    rt_end(&r);
}

/* ======== Level 2 ======== */

/* Level2Run: transactions of one to three keys (one in ten of one to twenty), of
 * "/k/N" and "/long/N" for N below 300, each a put of 1 to 60 random bytes or (one in
 * five) a delete, at times 20, 30, ...; a restart every restartEvery, and after it
 * every key checked at the latest time and at ten earlier times (a transaction's,
 * or one less) against the model. C's generator, not java.util.Random. */
#define L2_KEYS 600
#define L2_EVENTS 64

struct l2_event {
    int64_t time;
    int32_t len;            /* -1: a delete */
    uint8_t v[60];
};

struct l2 {
    struct rt r;
    uint64_t rnd;
    uint64_t lookup_rnd;
    int32_t restart_every;
    int32_t nev[L2_KEYS];
    struct l2_event (*ev)[L2_EVENTS];
    int64_t times[2000];
    int32_t ntimes;
    int problems;
};

static void l2_key(int32_t k, char *out, size_t cap) {
    if (k < 300) {
        snprintf(out, cap, "/k/%d", (int) k);
    } else {
        snprintf(out, cap, "/long/%d", (int) (k - 300));
    }
}

static void l2_check(struct l2 *x, int i) {
    int64_t lts[11];
    lts[0] = INT64_MAX;
    for (int j = 1; j < 11; j++) {
        lts[j] = x->times[test_random_below(&x->lookup_rnd, x->ntimes)]
                + test_random_below(&x->lookup_rnd, 2) - 1;
    }
    for (int32_t k = 0; k < L2_KEYS; k++) {
        if (x->nev[k] == 0) {
            continue;
        }
        char key[32];
        l2_key(k, key, sizeof key);
        for (int j = 0; j < 11; j++) {
            const struct l2_event *want = NULL;
            for (int32_t q = 0; q < x->nev[k] && x->ev[k][q].time <= lts[j]; q++) {
                want = &x->ev[k][q];
            }
            uint8_t v[64];
            int32_t n = rt_get(&x->r, lts[j], key, v, (int32_t) sizeof v);
            bool same = want == NULL || want->len < 0 ? n == -1
                    : n == want->len && memcmp(v, want->v, (size_t) n) == 0;
            if (!same) {
                if (x->problems++ < 3) {
                    printf("    after transaction %d: %s at %lld: %d bytes, not %d\n", i, key,
                            (long long) lts[j], (int) n,
                            (int) (want == NULL ? -1 : want->len));
                }
            }
        }
    }
}

/* Runs n transactions; the stream's length in *length. */
static void l2_run(struct l2 *x, uint64_t seed, int32_t node, int32_t restart_every, int n,
        int64_t *length) {
    struct err e;
    memset(x->nev, 0, sizeof x->nev);
    x->ev = calloc(L2_KEYS, sizeof *x->ev);
    x->rnd = seed;
    x->lookup_rnd = seed + 1000;
    x->restart_every = restart_every;
    x->ntimes = 0;
    x->problems = 0;
    rt_init(&x->r, node, 2000);
    REQUIRE(x->ev != NULL && rt_open(&x->r, &e) == ERR_OK);
    int64_t time = 10;
    for (int i = 0; i < n && x->problems == 0; i++) {
        time += 10;
        x->times[x->ntimes++] = time;
        const int32_t ops = test_random_below(&x->rnd, 10) == 0
                ? 1 + test_random_below(&x->rnd, 20) : 1 + test_random_below(&x->rnd, 3);
        int32_t keys[20];
        int32_t nk = 0;
        while (nk < ops) {
            const int32_t k = test_random_below(&x->rnd, 2) == 0
                    ? test_random_below(&x->rnd, 300) : 300 + test_random_below(&x->rnd, 300);
            bool seen = false;
            for (int32_t j = 0; j < nk; j++) {
                seen = seen || keys[j] == k;
            }
            if (!seen) {
                keys[nk++] = k;
            }
        }
        struct rtb b;
        rtb_begin(&b, &x->r);
        for (int32_t j = 0; j < nk; j++) {
            const int32_t k = keys[j];
            REQUIRE(x->nev[k] < L2_EVENTS);
            struct l2_event *ev = &x->ev[k][x->nev[k]++];
            ev->time = time;
            if (test_random_below(&x->rnd, 5) == 0) {
                ev->len = -1;
            } else {
                ev->len = 1 + test_random_below(&x->rnd, 60);
                for (int32_t q = 0; q < ev->len; q++) {
                    ev->v[q] = (uint8_t) test_random(&x->rnd);
                }
            }
            char key[32];
            l2_key(k, key, sizeof key);
            rtb_put(&b, key, ev->v, ev->len);
        }
        REQUIRE(rtb_commit(&b, time, false, NULL, &e) == ERR_OK);
        if (restart_every > 0 && i % restart_every == restart_every - 1) {
            if (!rt_restart(&x->r)) {
                x->problems++;
                printf("    restart after transaction %d\n", i);
                break;
            }
            l2_check(x, i);
        }
    }
    *length = db_stream_length(&x->r.db);
    rt_close(&x->r);
    free(x->ev);
}

/* testLevel2RestartsKeepAllValues: Level 2, restarts with bounded startup; after
 * each, every key right at the latest time and at earlier times. In Java, fails
 * without DbStarter.canonicalNode()'s use of the stored position (a delete of a key
 * that does not exist). */
TEST(restart_level2_keep_all_values) {
    static struct l2 x;
    int64_t length;
    l2_run(&x, 1, 30, 50, 200, &length);
    CHECK_EQ(x.problems, 0);
    rt_end(&x.r);
    l2_run(&x, 2, 8, 25, 200, &length);
    CHECK_EQ(x.problems, 0);
    rt_end(&x.r);
}

/* testLevel2SameStreamWithRestarts: the stream with restarts is the one without,
 * byte for byte (T2 of docs/sis-model.md). In Java, fails without
 * NodeCollection.resolvePointers(). */
TEST(restart_level2_same_stream) {
    static struct l2 a, b;
    int64_t la, lb, fa_len, fb_len;
    l2_run(&a, 2, 30, 0, 200, &la);
    l2_run(&b, 2, 30, 20, 200, &lb);
    CHECK_EQ(b.problems, 0);
    CHECK_EQ(la, lb);
    uint8_t *fa = rt_read_stream(&a.r, &fa_len);
    uint8_t *fb = rt_read_stream(&b.r, &fb_len);
    CHECK_EQ(fa_len, la);
    CHECK(fa != NULL && fb != NULL && fa_len == fb_len
            && memcmp(fa, fb, (size_t) fa_len) == 0);
    free(fa);
    free(fb);
    rt_end(&a.r);
    rt_end(&b.r);
}

const struct test restart_tests[] = {
    TEST_ENTRY(restart_values),
    TEST_ENTRY(restart_get_many),
    TEST_ENTRY(restart_random_ids),
    TEST_ENTRY(restart_empty_and_startup_distance),
    TEST_ENTRY(restart_longer_than_startup),
    TEST_ENTRY(restart_deletes),
    TEST_ENTRY(restart_delete_missing_long_key),
    TEST_ENTRY(restart_stm),
    TEST_ENTRY(restart_after_changing_nothing),
    TEST_ENTRY(restart_last_trans_pos),
    TEST_ENTRY(restart_ordinals_across_boundaries),
    TEST_ENTRY(restart_end_of_ordinals),
    TEST_ENTRY(restart_ordinals_with_reclaim),
    TEST_ENTRY(restart_record_times_refused),
    TEST_ENTRY(restart_other_node_size_refused),
    TEST_ENTRY(restart_no_node_size_refused),
    TEST_ENTRY(restart_one_object_per_node),
    TEST_ENTRY(restart_level2_keep_all_values),
    TEST_ENTRY(restart_level2_same_stream),
    TEST_END
};
