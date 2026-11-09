/* The tests of the full replay and getTrans (bergdb 012-08), on Java's
 * stream of records.txt (Db, a memory stream, node size 8, startup
 * distance 100, 14 transactions): its reads at each record's time against a
 * map made from its value and delete nodes alone; getTrans of each record
 * against StoredTrans.parse's fields as Java gave them, and Java's
 * refusals; the stream cut at every position, as a crash leaves it, read as
 * Java's start reads it after its recovery; and the allocation failures in
 * turn. Nothing is left at the end. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "getmany.h"
#include "keys.h"
#include "mdb.h"
#include "mem.h"
#include "nstream.h"
#include "replay.h"
#include "snode.h"
#include "spos.h"
#include "strans.h"
#include "stream.h"
#include "test.h"

#ifndef VECTORS_DIR
#define VECTORS_DIR "test/unit/vectors"
#endif

/* records.txt: the stream's bytes, and Java's "trans" lines of the records
 * parsed at their own positions. */
struct jtrans {
    int64_t tpos, tt, startup_pos, top_pos, last_pos;
    int32_t nnodes;
};

struct vec {
    uint8_t *stream;
    int64_t len;
    struct jtrans t[64];
    int32_t nt;
};

static int hexval(int c) {
    return c <= '9' ? c - '0' : (c | 0x20) - 'a' + 10;
}

static bool read_vec(struct vec *v) {
    char path[600];
    const char *dir = getenv("BERGDB_VECTORS");
    snprintf(path, sizeof path, "%s/records.txt", dir != NULL ? dir : VECTORS_DIR);
    FILE *f = fopen(path, "r");
    if (f == NULL) {
        return false;
    }
    memset(v, 0, sizeof *v);
    char *line = NULL;
    size_t cap = 0;
    while (getline(&line, &cap, f) >= 0) {
        if (strncmp(line, "stream ", 7) == 0) {
            const char *h = line + 7;
            size_t n = strcspn(h, " \n") / 2;
            v->stream = malloc(n);
            for (size_t i = 0; i < n; i++) {
                v->stream[i] = (uint8_t) (hexval(h[2 * i]) * 16 + hexval(h[2 * i + 1]));
            }
            v->len = (int64_t) n;
        } else if (strncmp(line, "trans ", 6) == 0 && v->nt < 64) {
            long long tpos, at, tt, sp, top, last;
            int nn;
            if (sscanf(line, "trans %lld %lld %lld %lld %lld %lld %d", &tpos, &at, &tt, &sp,
                    &top, &last, &nn) == 7 && tpos == at) {
                struct jtrans *t = &v->t[v->nt++];
                t->tpos = tpos;
                t->tt = tt;
                t->startup_pos = sp;
                t->top_pos = top;
                t->last_pos = last;
                t->nnodes = nn;
            }
        }
    }
    free(line);
    fclose(f);
    return v->stream != NULL && v->nt > 0;
}

/* A memory stream of the first len bytes of v's stream. */
static void open_stream(struct stream *s, struct mem *m, const struct vec *v, int64_t len) {
    struct err e;
    stream_open_memory(s, m);
    CHECK_EQ(stream_append_memory(s, v->stream, len, &e), ERR_OK);
}

/* ======== A map made from the records' value nodes alone ======== */

#define MAXK 64

struct mkey {
    int64_t s[8];
    int32_t n;
    const uint8_t *value;       /* NULL: deleted */
    int32_t len;
    int64_t spos;               /* the value node's */
    int64_t tpos;
};

struct map {
    struct mkey k[MAXK];
    int32_t n;
};

/* The state after the committed records whose time is at most t, of the
 * stream's first len bytes. The values point into v->stream. */
static void map_at(struct map *mp, const struct vec *v, int64_t len, int64_t t) {
    struct mem m;
    mem_init(&m);
    struct stream s;
    open_stream(&s, &m, v, len);
    struct ns_iter it;
    struct st_record rec;
    struct err e;
    ns_iter_init(&it, &s, &m, 128, true);
    st_init(&rec);
    mp->n = 0;
    while (true) {
        bool has;
        if (ns_iter_next(&it, &has, &e) != ERR_OK || !has) {
            break;
        }
        if (st_parse(&rec, it.tpos, it.buf.p, it.size, &m, &e) != ERR_OK || rec.tt > t) {
            break;
        }
        for (int32_t i = 0; i < rec.nnodes; i++) {
            const struct sn_node *n = &rec.nodes[i];
            if (n->type != NODE_VALUE && n->type != NODE_DELETE) {
                continue;
            }
            REQUIRE(n->key_n <= 8);
            int64_t ks[8];
            for (int32_t q = 0; q < n->key_n; q++) {
                ks[q] = sn_seg(n, q);
            }
            int32_t j = 0;
            while (j < mp->n && !(mp->k[j].n == n->key_n
                    && memcmp(mp->k[j].s, ks, (size_t) n->key_n * sizeof ks[0]) == 0)) {
                j++;
            }
            if (j == mp->n) {
                REQUIRE(mp->n < MAXK);
                mp->k[j].n = n->key_n;
                memcpy(mp->k[j].s, ks, (size_t) n->key_n * sizeof ks[0]);
                mp->n++;
            }
            /* the value's offset in the record's bytes, which are a copy: map
             * it to the vector's stream (the record lies whole before a meta
             * block in this small stream) */
            mp->k[j].value = n->type == NODE_DELETE ? NULL
                    : v->stream + rec.tpos + (n->value - it.buf.p);
            mp->k[j].len = n->value_len;
            mp->k[j].spos = n->spos;
            mp->k[j].tpos = n->tpos;
        }
    }
    st_free(&rec, &m);
    ns_iter_free(&it);
    stream_close(&s);
    CHECK_MEM_ZERO(&m);
}

/* The replay's reads at time t against the map. */
static void check_reads(struct replay *r, const struct map *mp, int64_t t) {
    struct getdata gd;
    mdb_new_get_data(&r->db, &gd);
    int32_t live = 0;
    for (int32_t j = 0; j < mp->n; j++) {
        struct vnode *vn;
        CHECK(mdb_get_one(&r->db, t, mp->k[j].s, mp->k[j].n, &gd, &vn));
        if (mp->k[j].value == NULL) {
            CHECK(vn == NULL);
            continue;
        }
        live++;
        REQUIRE(vn != NULL);
        CHECK_EQ(vn->len, mp->k[j].len);
        CHECK(memcmp(vn->value, mp->k[j].value, (size_t) mp->k[j].len) == 0);
        CHECK_EQ(gd.tpos, mp->k[j].tpos);
        CHECK_EQ(vn->n.spos, mp->k[j].spos);
    }
    struct getmany g;
    mdb_new_get_many(&r->db, &g);
    g.lookup_time = t;
    CHECK(mdb_get_many(&r->db, &g));
    CHECK_EQ(g.get_op_count, live);
}

/* ======== The tests ======== */

TEST(replay_java_stream) {
    struct vec v;
    REQUIRE(read_vec(&v));
    struct mem m;
    mem_init(&m);
    struct stream s;
    open_stream(&s, &m, &v, v.len);
    struct replay r;
    struct err e;
    REQUIRE(replay_open(&r, &s, &m, 8, &e) == ERR_OK);

    CHECK_EQ(r.length, v.len);
    CHECK_EQ(r.startup_distance, 100);
    CHECK_EQ(r.records, v.nt);
    CHECK_EQ(r.first_available_pos, 0);
    CHECK_EQ(r.first_available_time, 0);
    /* StartInfo: the last record's startup position, and the records from it. */
    const struct jtrans *last = &v.t[v.nt - 1];
    CHECK_EQ(r.start_pos, last->startup_pos);
    CHECK_EQ(r.last_pos, last->last_pos);
    int32_t count = 0;
    for (int32_t i = 0; i < v.nt; i++) {
        if (v.t[i].tpos >= (r.start_pos == 0 ? 128 : r.start_pos)) {
            if (count == 0) {
                CHECK_EQ(r.start_time, v.t[i].tt);
            }
            count++;
        }
    }
    CHECK_EQ(r.trans_count, count);

    /* Reads at every record's time, and just before. */
    struct map mp;
    for (int32_t i = 0; i < v.nt; i++) {
        map_at(&mp, &v, v.len, v.t[i].tt - 1);
        check_reads(&r, &mp, v.t[i].tt - 1);
        map_at(&mp, &v, v.len, v.t[i].tt);
        check_reads(&r, &mp, v.t[i].tt);
    }
    check_reads(&r, &mp, INT64_MAX);

    /* getTrans of every record, as StoredTrans.parse gave it in Java. */
    for (int32_t i = 0; i < v.nt; i++) {
        const struct st_record *st;
        REQUIRE(replay_get_trans(&r, v.t[i].tpos, &st, &e) == ERR_OK);
        CHECK_EQ(st->tpos, v.t[i].tpos);
        CHECK_EQ(st->tt, v.t[i].tt);
        CHECK_EQ(st->startup_pos, v.t[i].startup_pos);
        CHECK_EQ(st->top_pos, v.t[i].top_pos);
        CHECK_EQ(st->last_pos, v.t[i].last_pos);
        CHECK_EQ(st->nnodes, v.t[i].nnodes);
    }
    /* Java's refusals of positions (005-34, 005-43): nothing is read. */
    const struct st_record *st;
    const int64_t bad[] = { -8, -1, 3, 132, 200000, 200064, 200127, v.len, v.len + 8 };
    for (size_t i = 0; i < sizeof bad / sizeof bad[0]; i++) {
        CHECK_EQ(replay_get_trans(&r, bad[i], &st, &e), ERR_ARG);
        CHECK(strcmp(e.java, "IllegalArgumentException") == 0);
    }
    CHECK(!r.failed);
    /* The middle of a record read as one: corrupt data, which fails the
     * database (005-30), and every later read. */
    CHECK(replay_get_trans(&r, 136, &st, &e) != ERR_OK);
    CHECK(strcmp(e.java, "DbFailedException") == 0);
    CHECK(r.failed);
    CHECK(replay_get_trans(&r, 128, &st, &e) != ERR_OK);
    CHECK(strcmp(e.java, "DbFailedException") == 0);

    replay_close(&r);
    stream_close(&s);
    CHECK_MEM_ZERO(&m);
    free(v.stream);
}

/* The stream cut at every position after the creation, as a crash leaves
 * it: the start's view after recovery (its length, the last record), and
 * the reads, the state of the records that are whole. */
TEST(replay_cut_stream) {
    struct vec v;
    REQUIRE(read_vec(&v));
    for (int64_t cut = 264; cut <= v.len; cut++) {
        struct mem m;
        mem_init(&m);
        struct stream s;
        open_stream(&s, &m, &v, cut);
        struct replay r;
        struct err e;
        enum err_code rc = replay_open(&r, &s, &m, 8, &e);
        REQUIRE(rc == ERR_OK);
        /* the whole records: those that end at or before the cut */
        int32_t whole = 0;
        for (int32_t i = 0; i < v.nt; i++) {
            if (v.t[i].last_pos < cut) {
                whole = i + 1;
            }
        }
        CHECK_EQ(r.records, whole);
        CHECK_EQ(r.last_pos, v.t[whole - 1].last_pos);
        CHECK(r.length >= cut);
        /* a cut inside a record: the fill to its end */
        if (whole < v.nt && cut > v.t[whole].tpos) {
            int64_t have = cut - v.t[whole].tpos;
            int64_t size = v.t[whole].last_pos + 1 - v.t[whole].tpos;
            if (have < 4) {
                /* A torn size field, completed as Java's transHeaderFixBytes
                 * does: the missing bytes 0, but the first 1 when the size
                 * so far is below 17 (012-02, 4.4). */
                int64_t sofar = 0;
                for (int64_t i = 0; i < have; i++) {
                    sofar |= (int64_t) v.stream[v.t[whole].tpos + i] << (8 * i);
                }
                size = sofar < 17 ? sofar | (INT64_C(1) << (8 * have)) : sofar;
            }
            CHECK_EQ(r.length, v.t[whole].tpos + size);
        } else {
            CHECK_EQ(r.length, cut);
        }
        struct map mp;
        map_at(&mp, &v, cut, INT64_MAX);
        check_reads(&r, &mp, INT64_MAX);
        replay_close(&r);
        stream_close(&s);
        CHECK_MEM_ZERO(&m);
    }
    free(v.stream);
}

/* Java's refusals at a start, and what C's replay cannot read. */
TEST(replay_refusals) {
    struct vec v;
    REQUIRE(read_vec(&v));
    struct mem m;
    mem_init(&m);
    struct stream s;
    struct replay r;
    struct err e;

    /* Another node size (005-50). */
    open_stream(&s, &m, &v, v.len);
    CHECK_EQ(replay_open(&r, &s, &m, 14, &e), ERR_FORMAT);
    CHECK(strcmp(e.java, "StreamFormatException") == 0);
    stream_close(&s);

    /* An empty stream: Java creates the database (012-09). */
    stream_open_memory(&s, &m);
    CHECK_EQ(replay_open(&r, &s, &m, 8, &e), ERR_ARG);
    CHECK(strcmp(e.java, "UnsupportedOperationException") == 0);
    stream_close(&s);

    /* A creation cut short (005-33). */
    open_stream(&s, &m, &v, 200);
    CHECK_EQ(replay_open(&r, &s, &m, 8, &e), ERR_FORMAT);
    CHECK(strcmp(e.java, "DatabaseNotCreatedException") == 0);
    stream_close(&s);

    /* Bad magic bytes: Db.startInner's StreamFormatException, the
     * BadMagicBytes its cause (bergdb 020-28, as Java's since release 2026.4:
     * BadCryptoKey before). */
    uint8_t *copy = malloc((size_t) v.len);
    memcpy(copy, v.stream, (size_t) v.len);
    copy[0] ^= 1;
    stream_open_memory(&s, &m);
    CHECK_EQ(stream_append_memory(&s, copy, v.len, &e), ERR_OK);
    CHECK_EQ(replay_open(&r, &s, &m, 8, &e), ERR_FORMAT);
    CHECK(strcmp(e.java, "StreamFormatException") == 0);
    CHECK(strcmp(e.cause, "BadMagicBytes") == 0);
    CHECK(strncmp(e.text, "Invalid magic bytes in stream: the stream is not a BergDB", 57) == 0);
    stream_close(&s);
    free(copy);

    CHECK_MEM_ZERO(&m);
    free(v.stream);
}

TEST(replay_allocation_failures) {
    struct vec v;
    REQUIRE(read_vec(&v));
    int64_t runs = 0;
    for (int64_t failAt = 1; failAt < 100000; failAt++) {
        struct mem m;
        mem_init(&m);
        struct stream s;
        open_stream(&s, &m, &v, v.len);
        m.fail_at = m.allocs + failAt;
        struct replay r;
        struct err e;
        enum err_code rc = replay_open(&r, &s, &m, 8, &e);
        const struct st_record *st;
        if (rc == ERR_OK) {
            rc = replay_get_trans(&r, 312, &st, &e);
            replay_close(&r);
        }
        bool failed = m.failed > 0;
        m.fail_at = 0;
        stream_close(&s);
        CHECK_MEM_ZERO(&m);
        runs++;
        if (!failed) {
            CHECK_EQ(rc, ERR_OK);
            break;
        }
        CHECK(rc != ERR_OK);
    }
    CHECK(runs > 50);       /* 100 on 2026-10-28 */
    free(v.stream);
}

const struct test replay_tests[] = {
    TEST_ENTRY(replay_java_stream),
    TEST_ENTRY(replay_cut_stream),
    TEST_ENTRY(replay_refusals),
    TEST_ENTRY(replay_allocation_failures),
    TEST_END
};
