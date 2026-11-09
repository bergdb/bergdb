/* The write path (bergdb 012-09): Db's creation and execute against Java's
 * bytes (records.txt's stream, which Java's Db wrote: its transactions,
 * read back from its records, executed again by C give the same stream, byte
 * for byte); Trans.Builder's order; the refusals before the go point, each
 * leaving the database as it was; a failure after it (P7); and the
 * allocation failures in turn (012-01, 4.5), each run NOMEM before the go
 * point (the database as it was, the transaction then executed again) or a
 * failed database after it, and everything freed at the close; a
 * transformed value past the record limit (015-51). */
#define _DARWIN_C_SOURCE        /* mkdtemp */
#include <dirent.h>
#include <errno.h>
#include <stdlib.h>
#include <unistd.h>
#include "test.h"
#include "bergdb.h"
#include "db.h"
#include "keys.h"
#include "meta.h"
#include "nstream.h"
#include "snode.h"
#include "strans.h"
#include "topds.h"
#include "trans.h"

#ifndef VECTORS_DIR
#define VECTORS_DIR "test/unit/vectors"
#endif

#define V_MAX (1 << 16)

/* Java's stream (records.txt) and the transactions read back from it. */
struct vtrans {
    int64_t tt;
    int32_t npairs;
    int64_t keys[8][8];
    int32_t key_n[8];
    uint8_t values[8][64];
    int32_t len[8];             /* -1: a delete */
};

static struct {
    uint8_t stream[V_MAX];
    int32_t stream_len;
    int64_t creation_time;
    int32_t node_size;
    int32_t sd;
    struct vtrans trans[64];
    int32_t ntrans;
} jv;

static int hexd(char c) {
    if (c >= '0' && c <= '9') return c - '0';
    if (c >= 'a' && c <= 'f') return c - 'a' + 10;
    return -1;
}

/* Reads records.txt's stream and, through C's reader, its transactions. */
static bool load_java_stream(void) {
    char path[1024];
    const char *dir = getenv("BERGDB_VECTORS");
    snprintf(path, sizeof path, "%s/records.txt", dir != NULL ? dir : VECTORS_DIR);
    FILE *f = fopen(path, "r");
    if (f == NULL) {
        printf("cannot open %s: %s\n", path, strerror(errno));
        return false;
    }
    static char line[1 << 18];
    jv.stream_len = 0;
    while (fgets(line, sizeof line, f) != NULL) {
        if (strncmp(line, "stream ", 7) == 0) {
            const char *s = line + 7;
            int32_t n = 0;
            while (hexd(s[0]) >= 0 && hexd(s[1]) >= 0 && n < V_MAX) {
                jv.stream[n++] = (uint8_t) (hexd(s[0]) * 16 + hexd(s[1]));
                s += 2;
            }
            jv.stream_len = n;
        }
    }
    fclose(f);
    if (jv.stream_len == 0) {
        return false;
    }
    struct mem m;
    struct err e;
    struct stream st;
    mem_init(&m);
    stream_open_memory(&st, &m);
    stream_append_memory(&st, jv.stream, jv.stream_len, &e);
    struct meta mb;
    meta_from_bytes(&mb, jv.stream, 0);
    jv.creation_time = meta_time(&mb);
    jv.node_size = meta_max_node_size(&mb);
    jv.sd = meta_startup_distance(&mb);
    struct ns_iter it;
    struct st_record r;
    ns_iter_init(&it, &st, &m, META_BLOCK_SIZE, true);
    st_init(&r);
    jv.ntrans = 0;
    bool first = true;
    bool ok = true;
    for (;;) {
        bool has;
        if (ns_iter_next(&it, &has, &e) != ERR_OK) {
            ok = false;
            break;
        }
        if (!has) {
            break;
        }
        if (st_parse(&r, it.tpos, it.buf.p, it.size, &m, &e) != ERR_OK) {
            ok = false;
            break;
        }
        if (first) {
            first = false;      /* the creation */
            continue;
        }
        struct vtrans *t = &jv.trans[jv.ntrans++];
        t->tt = r.tt;
        t->npairs = 0;
        for (int32_t i = 0; i < r.nnodes; i++) {
            const struct sn_node *x = &r.nodes[i];
            if (x->type != NODE_VALUE && x->type != NODE_DELETE) {
                continue;
            }
            int32_t p = t->npairs++;
            t->key_n[p] = x->key_n;
            for (int32_t k = 0; k < x->key_n; k++) {
                t->keys[p][k] = sn_seg(x, k);
            }
            t->len[p] = x->value_len;
            if (x->value_len > 0) {
                memcpy(t->values[p], x->value, (size_t) x->value_len);
            }
        }
    }
    st_free(&r, &m);
    ns_iter_free(&it);
    stream_close(&st);
    return ok && jv.ntrans > 0;
}

static void config_of_java(struct db_config *cfg, struct bergdb_test_clock *clock) {
    memset(cfg, 0, sizeof *cfg);
    cfg->max_node_size = jv.node_size;
    cfg->startup_distance = jv.sd;
    cfg->cache_size_indicator = INT64_MAX;
    cfg->clock = bergdb_test_clock_time;
    cfg->clock_ctx = clock;
    cfg->random_id = false;
    memcpy(cfg->id, bergdb_test_id, 16);
}

/* Transaction k of Java's stream, built into t from builder b. */
static enum err_code build_java_trans(int32_t k, struct tr_builder *b, struct trans *t,
        struct err *e) {
    const struct vtrans *v = &jv.trans[k];
    for (int32_t p = 0; p < v->npairs; p++) {
        enum err_code rc = tr_put_segments(b, v->keys[p], v->key_n[p],
                v->len[p] < 0 ? NULL : v->values[p], v->len[p] < 0 ? 0 : v->len[p], e);
        if (rc != ERR_OK) {
            return rc;
        }
    }
    return tr_build(b, t, e);
}

/* The bytes of a memory stream equal Java's up to its length. */
static bool same_prefix(const struct db *db) {
    int64_t n = db_stream_length(db);
    return n <= jv.stream_len && memcmp(db->stream.bytes, jv.stream, (size_t) n) == 0;
}

TEST(db_java_stream) {
    REQUIRE(load_java_stream());
    struct mem m;
    struct err e;
    struct db db;
    struct db_config cfg;
    struct db_start_info info;
    struct bergdb_test_clock clock = {0};
    mem_init(&m);
    config_of_java(&cfg, &clock);
    bergdb_test_clock_set(&clock, jv.creation_time);
    REQUIRE(db_open(&db, NULL, &cfg, &m, &info, &e) == ERR_OK);
    CHECK(info.created);
    CHECK_EQ(info.last_pos, DB_CREATION_LENGTH - 1);
    CHECK_EQ(db_stream_length(&db), DB_CREATION_LENGTH);
    CHECK(same_prefix(&db));
    for (int32_t k = 0; k < jv.ntrans; k++) {
        struct tr_builder b;
        struct trans t;
        tr_builder_init(&b, &m);
        tr_init(&t, &m);
        bergdb_test_clock_set(&clock, jv.trans[k].tt);
        CHECK(build_java_trans(k, &b, &t, &e) == ERR_OK);
        CHECK(db_execute(&db, &t, &e) == ERR_OK);
        CHECK_EQ(t.tt, jv.trans[k].tt);
        CHECK(same_prefix(&db));
        CHECK_EQ(db_recount(&db), 0);
        tr_free(&t);
        tr_builder_free(&b);
    }
    CHECK_EQ(db_stream_length(&db), jv.stream_len);
    CHECK(same_prefix(&db));
    CHECK(db_close(&db, &e) == ERR_OK);
    CHECK_MEM_ZERO(&m);
}

/* Trans.Builder.build: key order (unsigned bytes, a prefix first), the last
 * put of a key, a later delete replaces a delete, never a put. */
TEST(db_trans_build) {
    struct mem m;
    struct err e;
    struct tr_builder b;
    struct trans t;
    mem_init(&m);
    tr_builder_init(&b, &m);
    tr_init(&t, &m);
    const uint8_t kb[] = {1, 0x64}, ka[] = {1, 0x63}, kab[] = {1, 0x63, 0x64}, kz[] = {0xf0};
    const uint8_t v1[] = "1", v2[] = "2", v3[] = "3";
    CHECK(tr_put(&b, kb, 2, v1, 1, NULL, &e) == ERR_OK);
    CHECK(tr_delete(&b, kb, 2, &e) == ERR_OK);          /* a delete after a put: the put */
    CHECK(tr_delete(&b, ka, 2, &e) == ERR_OK);
    CHECK(tr_put(&b, ka, 2, v2, 1, NULL, &e) == ERR_OK);    /* a put after a delete: the put */
    CHECK(tr_put(&b, kz, 1, v1, 1, NULL, &e) == ERR_OK);
    CHECK(tr_put(&b, kz, 1, v3, 1, NULL, &e) == ERR_OK);    /* the later put */
    CHECK(tr_delete(&b, kab, 3, &e) == ERR_OK);
    CHECK(tr_delete(&b, kab, 3, &e) == ERR_OK);
    REQUIRE(tr_build(&b, &t, &e) == ERR_OK);
    REQUIRE(t.nkvs == 4);
    /* ka, kab (ka is its prefix), kb, kz */
    CHECK_EQ(t.kvs[0]->len, 1);
    CHECK_EQ(t.kvs[0]->value[0], '2');
    CHECK_EQ(t.kvs[1]->len, -1);
    CHECK_EQ(t.kvs[2]->value[0], '1');
    CHECK_EQ(t.kvs[3]->value[0], '3');
    CHECK_EQ(t.write_key_hashes[3], keys_hash(t.kvs[3]->key, t.kvs[3]->key_n));
    CHECK_EQ(t.read_time, INT64_MAX);
    CHECK(tr_lookup_time(&b, -1, &e) == ERR_ARG);
    tr_free(&t);
    tr_builder_free(&b);
    CHECK_MEM_ZERO(&m);
}

/* A put of key "/k/N" (ikey) with a value of len bytes of v. */
static void put_ikey(struct tr_builder *b, int n, int32_t len, uint8_t v) {
    struct err e;
    char ikey[32];
    uint8_t bkey[32];
    snprintf(ikey, sizeof ikey, "/k/%d", n);
    int32_t kl = (int32_t) strlen(ikey);
    keys_ikey_to_bkey((const uint8_t *) ikey, kl, bkey);
    uint8_t *value = calloc((size_t) len + 1, 1);
    memset(value, v, (size_t) len);
    tr_put(b, bkey, kl, value, len, NULL, &e);
    free(value);
}

/* Executes a transaction of puts of keys from..to-1 at clock time tt. */
static enum err_code exec_puts(struct db *db, struct mem *m, struct bergdb_test_clock *clock,
        int64_t tt, int from, int to, int32_t len, struct err *e) {
    struct tr_builder b;
    struct trans t;
    tr_builder_init(&b, m);
    tr_init(&t, m);
    if (tt > clock->time) {
        bergdb_test_clock_set(clock, tt);
    }
    for (int k = from; k < to; k++) {
        put_ikey(&b, k, len, (uint8_t) k);
    }
    enum err_code rc = tr_build(&b, &t, e);
    if (rc == ERR_OK) {
        rc = db_execute(db, &t, e);
    }
    tr_free(&t);
    tr_builder_free(&b);
    return rc;
}

static void small_config(struct db_config *cfg, struct bergdb_test_clock *clock) {
    memset(cfg, 0, sizeof *cfg);
    cfg->max_node_size = 8;
    cfg->startup_distance = 100;
    cfg->cache_size_indicator = INT64_MAX;
    cfg->clock = bergdb_test_clock_time;
    cfg->clock_ctx = clock;
    memcpy(cfg->id, bergdb_test_id, 16);
}

/* The refusals before the go point (005-17, 005-31, 005-18, the STM): each
 * refuses, leaves the stream and the state as they were, and the database
 * goes on with the bytes of a run without the refused transaction. */
TEST(db_refusals) {
    struct mem m, m2;
    struct err e;
    struct db db, ref;
    struct db_config cfg;
    struct db_start_info info;
    struct bergdb_test_clock clock = {0}, clock2 = {0};
    mem_init(&m);
    mem_init(&m2);
    small_config(&cfg, &clock);
    cfg.record_limit = 4000;        /* StoredTrans.recordLimit, lowered as Java's tests do */
    bergdb_test_clock_set(&clock, 1000);
    REQUIRE(db_open(&db, NULL, &cfg, &m, &info, &e) == ERR_OK);
    struct db_config cfg2 = cfg;
    cfg2.clock_ctx = &clock2;
    bergdb_test_clock_set(&clock2, 1000);
    REQUIRE(db_open(&ref, NULL, &cfg2, &m2, &info, &e) == ERR_OK);

    CHECK(exec_puts(&db, &m, &clock, 2000, 0, 5, 10, &e) == ERR_OK);
    CHECK(exec_puts(&ref, &m2, &clock2, 2000, 0, 5, 10, &e) == ERR_OK);
    int64_t len = db_stream_length(&db);

    /* checkSize: the value nodes over 7/8 of the limit. */
    CHECK(exec_puts(&db, &m, &clock, 3000, 10, 11, 3600, &e) == ERR_LIMIT);
    CHECK(strcmp(e.java, "DbException") == 0);
    CHECK_EQ(db_stream_length(&db), len);
    /* checkDirtyNodes: many keys over the lowered limit's bound. */
    CHECK(exec_puts(&db, &m, &clock, 3001, 100, 160, 1, &e) == ERR_LIMIT);
    CHECK(strstr(e.text, "005-31") != NULL);
    CHECK_EQ(db_stream_length(&db), len);
    /* The STM: a read set whose key was written after its lookup time. */
    {
        struct tr_builder b;
        struct trans t;
        tr_builder_init(&b, &m);
        tr_init(&t, &m);
        uint8_t bkey[8];
        keys_ikey_to_bkey((const uint8_t *) "/k/1", 4, bkey);
        tr_key_read(&b, bkey, 4, &e);
        tr_lookup_time(&b, 1500, &e);
        put_ikey(&b, 7, 3, 7);
        tr_build(&b, &t, &e);
        CHECK(db_execute(&db, &t, &e) == ERR_RERUN);
        CHECK(strcmp(e.java, "RerunException") == 0);
        tr_free(&t);
        tr_builder_free(&b);
    }
    CHECK_EQ(db_stream_length(&db), len);
    /* The clock out of range (005-18). */
    bergdb_test_clock_set(&clock, INT64_C(1) << 57);
    CHECK(exec_puts(&db, &m, &clock, 0, 20, 21, 5, &e) == ERR_LIMIT);
    CHECK_EQ(db_stream_length(&db), len);
    CHECK(db.state == DB_ACTIVE);

    /* The same bytes as the run without the refused transactions: the clock
     * set back by hand (the test clock moves forward only), and DbClock's
     * last time is still the last committed transaction's. */
    clock.time = 2999;
    CHECK(exec_puts(&ref, &m2, &clock2, 4000, 0, 3, 20, &e) == ERR_OK);
    CHECK(exec_puts(&db, &m, &clock, 4000, 0, 3, 20, &e) == ERR_OK);
    CHECK_EQ(db_stream_length(&db), db_stream_length(&ref));
    CHECK(memcmp(db.stream.bytes, ref.stream.bytes, (size_t) db_stream_length(&db)) == 0);
    CHECK_EQ(db_recount(&db), 0);
    CHECK(db_close(&db, &e) == ERR_OK);
    CHECK(db_close(&ref, &e) == ERR_OK);
    CHECK_MEM_ZERO(&m);
    CHECK_MEM_ZERO(&m2);
}

/* setStartupDistance (005-53): the value in force writes nothing, another
 * one the dummy transaction, whose meta block holds it; a refused dummy puts
 * the setting and the meta block's value back. */
TEST(db_set_startup_distance) {
    struct mem m;
    struct err e;
    struct db db;
    struct db_config cfg;
    struct db_start_info info;
    struct bergdb_test_clock clock = {0};
    mem_init(&m);
    small_config(&cfg, &clock);
    bergdb_test_clock_set(&clock, 1000);
    REQUIRE(db_open(&db, NULL, &cfg, &m, &info, &e) == ERR_OK);
    CHECK(exec_puts(&db, &m, &clock, 2000, 0, 5, 10, &e) == ERR_OK);
    int64_t len = db_stream_length(&db);
    CHECK(db_set_startup_distance(&db, -1, &e) == ERR_ARG);
    CHECK(db_set_startup_distance(&db, 100, &e) == ERR_OK);     /* clamped to 400,000 */
    CHECK(db_stream_length(&db) >= len + 200000);
    CHECK_EQ(db.startup_distance, 400000);
    CHECK_EQ(meta_startup_distance(&db.rs.meta), 400000);
    len = db_stream_length(&db);
    CHECK(db_set_startup_distance(&db, 300000, &e) == ERR_OK);  /* in force: nothing */
    CHECK_EQ(db_stream_length(&db), len);
    bergdb_test_clock_set(&clock, INT64_C(1) << 57);            /* the dummy refused */
    CHECK(db_set_startup_distance(&db, 500000, &e) == ERR_LIMIT);
    CHECK_EQ(db.startup_distance, 400000);
    CHECK_EQ(meta_startup_distance(&db.rs.meta), 400000);
    CHECK_EQ(db_stream_length(&db), len);
    CHECK(db.state == DB_ACTIVE);
    CHECK_EQ(db_recount(&db), 0);
    CHECK(db_close(&db, &e) == ERR_OK);
    CHECK(db_set_startup_distance(&db, 500000, &e) == ERR_STATE);  /* stopping */
    CHECK_MEM_ZERO(&m);
}

/* The end of the top node ordinals (005-02): with the second top node's
 * ordinal near the bound (DbBuilder.secondTopOrdinal, a test setting), a
 * user transaction is refused once the super root's ordinal reaches
 * LAST_TOP_ORDINAL, before it changes anything; reads go on. */
TEST(db_top_ordinals) {
    struct mem m;
    struct err e;
    struct db db;
    struct db_config cfg;
    struct db_start_info info;
    struct bergdb_test_clock clock = {0};
    mem_init(&m);
    small_config(&cfg, &clock);
    cfg.second_top_ordinal = DB_LAST_TOP_ORDINAL - 1;
    bergdb_test_clock_set(&clock, 1000);
    REQUIRE(db_open(&db, NULL, &cfg, &m, &info, &e) == ERR_OK);
    enum err_code rc = ERR_OK;
    int k;
    for (k = 0; k < 400 && rc == ERR_OK; k++) {
        rc = exec_puts(&db, &m, &clock, 2000 + 10 * k, 10 * k, 10 * k + 10, 4, &e);
    }
    CHECK_EQ(rc, ERR_LIMIT);
    CHECK(strstr(e.text, "top node ordinals") != NULL);
    CHECK_EQ(tds_get_super_root(&db.dag.top_ds)->top_node_id, DB_LAST_TOP_ORDINAL);
    int64_t len = db_stream_length(&db);
    CHECK(exec_puts(&db, &m, &clock, 100000, 0, 1, 4, &e) == ERR_LIMIT);
    CHECK_EQ(db_stream_length(&db), len);
    /* DbTesterRestart.testReclaimSettingAtEndOfOrdinals (015-87): a setter
     * that would write is refused as a user transaction is, and changes
     * nothing; one with the value in force writes nothing and is not
     * refused. */
    CHECK(db_set_retain_duration(&db, 5 * CLK_UNITS_PER_SEC, &e) == ERR_LIMIT);
    CHECK(strncmp(e.text, "The database has used its top node ordinals", 43) == 0);
    CHECK(db_set_reclaim_internal_fraction(&db, 0.5, &e) == ERR_LIMIT);
    CHECK(strncmp(e.text, "The database has used its top node ordinals", 43) == 0);
    CHECK_EQ(db.reclaim.retainDuration, INT64_MAX);
    CHECK_EQ(db.reclaim.internalFraction, RC_DEFAULT_INTERNAL_FRACTION);
    CHECK(db_set_retain_duration(&db, INT64_MAX, &e) == ERR_OK);       /* in force */
    CHECK(db_set_reclaim_internal_fraction(&db, 0.25, &e) == ERR_OK);
    CHECK_EQ(db_stream_length(&db), len);
    CHECK_EQ(tds_get_super_root(&db.dag.top_ds)->top_node_id, DB_LAST_TOP_ORDINAL);
    struct getdata gd;
    struct vnode *v = NULL;
    db_new_get_data(&db, &gd);
    int64_t key[4];
    uint8_t bkey[8];
    keys_ikey_to_bkey((const uint8_t *) "/k/5", 4, bkey);
    keys_to_segments(bkey, 4, key);
    CHECK(db_get_one(&db, INT64_MAX, key, 1, &gd, &v, &e) == ERR_OK);
    CHECK(v != NULL && v->len == 4);
    CHECK_EQ(db_recount(&db), 0);
    CHECK(db_close(&db, &e) == ERR_OK);
    CHECK_MEM_ZERO(&m);
}

/* A value transformation's result: 120,000 bytes, whatever the input. */
static void value_of_120k(void *ctx, int64_t tt, const uint8_t *previous, size_t previous_len,
        const uint8_t **value, size_t *value_len) {
    (void) tt;
    (void) previous;
    (void) previous_len;
    *value = ctx;
    *value_len = 120000;
}

/* The value of ikey at the latest time: its length, -1 if none. */
static int32_t latest_len(struct db *db, const char *ikey, struct err *e) {
    uint8_t bkey[32];
    int64_t key[8];
    const int32_t kl = (int32_t) strlen(ikey);
    keys_ikey_to_bkey((const uint8_t *) ikey, kl, bkey);
    keys_to_segments(bkey, kl, key);
    struct getdata gd;
    struct vnode *v = NULL;
    db_new_get_data(db, &gd);
    if (db_get_one(db, INT64_MAX, key, keys_segment_count(kl), &gd, &v, e) != ERR_OK) {
        return -2;
    }
    return v == NULL ? -1 : v->len;
}

/* A put of ikey with value (len bytes; tf NULL for none), alone in a
 * transaction at clock time tt. */
static enum err_code exec_put1(struct db *db, struct mem *m, struct bergdb_test_clock *clock,
        int64_t tt, const char *ikey, const uint8_t *value, int32_t len,
        const struct tr_transform *tf, struct err *e) {
    struct tr_builder b;
    struct trans t;
    uint8_t bkey[32];
    const int32_t kl = (int32_t) strlen(ikey);
    keys_ikey_to_bkey((const uint8_t *) ikey, kl, bkey);
    tr_builder_init(&b, m);
    tr_init(&t, m);
    bergdb_test_clock_set(clock, tt);
    enum err_code rc = tr_put(&b, bkey, kl, value, len, tf, e);
    if (rc == ERR_OK) {
        rc = tr_build(&b, &t, e);
    }
    if (rc == ERR_OK) {
        rc = db_execute(db, &t, e);
    }
    tr_free(&t);
    tr_builder_free(&b);
    return rc;
}

/* DbTester.testTransformedValueBeyondRecordLimit (bergdb 015-51, as Java's
 * since release 2026.3; bergdb.h, struct bergdb_transform): a value
 * transformation runs after the go point, so checkSize counts its input,
 * not its result. A result that takes the transaction past the value limit
 * is the caller's fault: one whose record does not fit the record limit,
 * lowered to 100 kB, fails the database when the record is made, which
 * appends nothing, and a restart has the state before the transaction. The
 * test pins the contract that bergdb.h states; the code was not changed. */
TEST(db_transformed_value_beyond_record_limit) {
    const char *t = getenv("TMPDIR");
    char dir[256];
    snprintf(dir, sizeof dir, "%s/bergdb-t_db-XXXXXX", t != NULL ? t : "/tmp");
    REQUIRE(mkdtemp(dir) != NULL);
    struct mem m;
    struct err e;
    struct db db;
    struct db_config cfg;
    struct db_start_info info;
    struct bergdb_test_clock clock = {0};
    mem_init(&m);
    memset(&cfg, 0, sizeof cfg);            /* testSetup */
    cfg.max_node_size = 30;
    cfg.startup_distance = 50000000;
    cfg.cache_size_indicator = INT64_MAX;
    cfg.clock = bergdb_test_clock_time;
    cfg.clock_ctx = &clock;
    memcpy(cfg.id, bergdb_test_id, 16);
    cfg.record_limit = 100 * 1000;          /* StoredTrans.recordLimit, lowered */
    bergdb_test_clock_set(&clock, 1000);
    REQUIRE(db_open(&db, dir, &cfg, &m, &info, &e) == ERR_OK);
    CHECK(exec_put1(&db, &m, &clock, 2000, "/a", (const uint8_t *) "a", 1, NULL, &e) == ERR_OK);
    const int64_t len = db_stream_length(&db);
    uint8_t *big = calloc(120000, 1);
    REQUIRE(big != NULL);
    const struct tr_transform tf = { NULL, value_of_120k, big };
    CHECK(exec_put1(&db, &m, &clock, 3000, "/t", big, 0, &tf, &e) == ERR_FAILED);
    CHECK(strcmp(e.java, "DbFailedException") == 0);
    CHECK(strcmp(db.failure.java, "DbException") == 0);         /* the cause */
    CHECK(strstr(db.failure.text, "more than the limit") != NULL);
    CHECK_EQ(db_stream_length(&db), len);       /* nothing appended */
    CHECK(exec_put1(&db, &m, &clock, 4000, "/x", (const uint8_t *) "x", 1, NULL, &e)
            == ERR_FAILED);                     /* a failed database takes none */
    db_close(&db, &e);
    CHECK_MEM_ZERO(&m);
    free(big);

    cfg.record_limit = 0;
    REQUIRE(db_open(&db, dir, &cfg, &m, &info, &e) == ERR_OK);
    CHECK_EQ(latest_len(&db, "/a", &e), 1);
    CHECK_EQ(latest_len(&db, "/t", &e), -1);
    CHECK(exec_put1(&db, &m, &clock, 5000, "/x", (const uint8_t *) "x", 1, NULL, &e) == ERR_OK);
    CHECK_EQ(latest_len(&db, "/x", &e), 1);
    CHECK_EQ(db_recount(&db), 0);
    CHECK(db_close(&db, &e) == ERR_OK);
    CHECK_MEM_ZERO(&m);
    DIR *d = opendir(dir);
    if (d != NULL) {
        struct dirent *x;
        char path[512];
        while ((x = readdir(d)) != NULL) {
            if (x->d_name[0] != '.') {
                snprintf(path, sizeof path, "%s/%s", dir, x->d_name);
                unlink(path);
            }
        }
        closedir(d);
    }
    rmdir(dir);
}

/* The allocation failures in turn over Java's transactions: each run's
 * failure refuses (NOMEM, before the go point: the database as it was, and
 * the transaction executed again gives Java's bytes) or fails the database
 * (FAILED, after it: every later execute FAILED); the close frees all. */
TEST(db_alloc_failures) {
    REQUIRE(load_java_stream());
    int64_t runs = 0, refused = 0, failed = 0, opens = 0;
    for (int64_t at = 1; at < 100000; at++) {
        struct mem m;
        struct err e;
        struct db db;
        struct db_config cfg;
        struct db_start_info info;
        struct bergdb_test_clock clock = {0};
        mem_init(&m);
        m.fail_at = at;
        config_of_java(&cfg, &clock);
        bergdb_test_clock_set(&clock, jv.creation_time);
        enum err_code rc = db_open(&db, NULL, &cfg, &m, &info, &e);
        if (rc != ERR_OK) {
            CHECK_EQ(rc, ERR_NOMEM);
            CHECK_MEM_ZERO(&m);
            opens++;
            runs++;
            continue;
        }
        bool hit = false, dead = false;
        for (int32_t k = 0; k < jv.ntrans && !dead; k++) {
            bergdb_test_clock_set(&clock, jv.trans[k].tt);
            for (int attempt = 0; attempt < 2; attempt++) {
                struct tr_builder b;
                struct trans t;
                tr_builder_init(&b, &m);
                tr_init(&t, &m);
                rc = build_java_trans(k, &b, &t, &e);
                if (rc == ERR_OK) {
                    rc = db_execute(&db, &t, &e);
                }
                tr_free(&t);
                tr_builder_free(&b);
                if (rc == ERR_OK) {
                    break;
                }
                hit = true;
                m.fail_at = 0;
                if (rc == ERR_NOMEM) {
                    refused++;
                    CHECK(db.state == DB_ACTIVE);
                    CHECK(same_prefix(&db));
                    CHECK_EQ(db_recount(&db), 0);
                    continue;       /* the same transaction again, without failures */
                }
                CHECK_EQ(rc, ERR_FAILED);
                CHECK(db.state == DB_FAILED);
                failed++;
                dead = true;
                struct tr_builder b2;
                struct trans t2;
                tr_builder_init(&b2, &m);
                tr_init(&t2, &m);
                CHECK(build_java_trans(k, &b2, &t2, &e) == ERR_OK);
                CHECK(db_execute(&db, &t2, &e) == ERR_FAILED);  /* every later call */
                tr_free(&t2);
                tr_builder_free(&b2);
                break;
            }
        }
        if (!dead) {
            CHECK_EQ(db_stream_length(&db), jv.stream_len);
            CHECK(same_prefix(&db));
        }
        db_close(&db, &e);
        CHECK_MEM_ZERO(&m);
        runs++;
        if (!hit && m.allocs < at) {
            break;      /* a run with no failure: all allocations covered */
        }
    }
    CHECK(refused > 0);
    CHECK(failed > 0);
    CHECK(opens > 0);
    printf("  db_alloc_failures: %lld runs: %lld opens refused, %lld transactions refused "
            "(NOMEM), %lld failed databases\n", (long long) runs, (long long) opens,
            (long long) refused, (long long) failed);
}

const struct test db_tests[] = {
    TEST_ENTRY(db_java_stream),
    TEST_ENTRY(db_trans_build),
    TEST_ENTRY(db_refusals),
    TEST_ENTRY(db_set_startup_distance),
    TEST_ENTRY(db_top_ordinals),
    TEST_ENTRY(db_transformed_value_beyond_record_limit),
    TEST_ENTRY(db_alloc_failures),
    TEST_END
};
