/* The tests of the bounded startup (bergdb 012-10, part 1: recover.h,
 * starter.h, ncoll.h, ntable.h through sdb.h), on Java's stream of
 * records.txt (Db, a memory stream, node size 8, startup distance 100, 14
 * transactions, so a startup section of a few records): its reads at each
 * record's time against a map made from its value and delete nodes alone,
 * and against the full replay; the stream cut at every position, as a crash
 * leaves it, recovered with its fill (the length and the bytes that Java's
 * recovery appends) and read; Java's refusals at a start; the recount after
 * the start and the reads; the allocation failures in turn. Nothing is left
 * at the end. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "bytes.h"
#include "getmany.h"
#include "keys.h"
#include "klong.h"
#include "mdb.h"
#include "mem.h"
#include "meta.h"
#include "nstream.h"
#include "recover.h"
#include "replay.h"
#include "rstream.h"
#include "sdb.h"
#include "snode.h"
#include "spos.h"
#include "strans.h"
#include "stream.h"
#include "test.h"

#ifndef VECTORS_DIR
#define VECTORS_DIR "test/unit/vectors"
#endif

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

static void open_stream(struct stream *s, struct mem *m, const uint8_t *bytes, int64_t len) {
    struct err e;
    stream_open_memory(s, m);
    CHECK_EQ(stream_append_memory(s, bytes, len, &e), ERR_OK);
}

/* Every getOne of every key the replay knows, at time t, and the getMany at
 * t both ways, by the bounded startup against the full replay of the same
 * stream: the same values, kvTime, tpos and value positions. */
static void compare_reads(struct sdb *b, struct replay *r, int64_t t) {
    /* the keys: those of the replay's latest state, and of t */
    int64_t keys[64][8];
    int32_t keyn[64];
    int32_t nk = 0;
    struct err e;
    /* The keys of the records' value and delete nodes. */
    struct ns_iter it;
    struct st_record rec;
    ns_iter_init(&it, r->s, r->mem, 128, true);
    st_init(&rec);
    while (nk < 64) {
        bool has;
        if (ns_iter_next(&it, &has, &e) != ERR_OK || !has) {
            break;
        }
        if (st_parse(&rec, it.tpos, it.buf.p, it.size, r->mem, &e) != ERR_OK) {
            break;
        }
        for (int32_t i = 0; i < rec.nnodes && nk < 64; i++) {
            const struct sn_node *n = &rec.nodes[i];
            if ((n->type != NODE_VALUE && n->type != NODE_DELETE) || n->key_n > 8) {
                continue;
            }
            int64_t s[8];
            for (int32_t q = 0; q < n->key_n; q++) {
                s[q] = sn_seg(n, q);
            }
            bool seen = false;
            for (int32_t j = 0; j < nk && !seen; j++) {
                seen = keyn[j] == n->key_n
                        && memcmp(keys[j], s, (size_t) n->key_n * sizeof s[0]) == 0;
            }
            if (!seen) {
                memcpy(keys[nk], s, sizeof s);
                keyn[nk] = n->key_n;
                nk++;
            }
        }
    }
    st_free(&rec, r->mem);
    ns_iter_free(&it);

    struct getdata gr, gb;
    mdb_new_get_data(&r->db, &gr);
    sdb_new_get_data(b, &gb);
    for (int32_t j = 0; j < nk; j++) {
        struct vnode *vr, *vb;
        CHECK(mdb_get_one(&r->db, t, keys[j], keyn[j], &gr, &vr));
        CHECK_EQ(sdb_get_one(b, t, keys[j], keyn[j], &gb, &vb, &e), ERR_OK);
        CHECK((vr == NULL) == (vb == NULL));
        if (vr != NULL && vb != NULL) {
            CHECK_EQ(vb->len, vr->len);
            CHECK(vb->len < 0 || memcmp(vb->value, vr->value, (size_t) vr->len) == 0);
            CHECK_EQ(gb.kv_time, gr.kv_time);
            CHECK_EQ(gb.tpos, gr.tpos);
            CHECK_EQ(vb->n.spos, vr->n.spos);
        }
    }
    for (int fwd = 1; fwd >= 0; fwd--) {
        struct getmany gm1, gm2;
        mdb_new_get_many(&r->db, &gm1);
        sdb_new_get_many(b, &gm2);
        gm1.lookup_time = gm2.lookup_time = t;
        gm1.forward = gm2.forward = fwd == 1;
        CHECK(mdb_get_many(&r->db, &gm1));
        CHECK_EQ(sdb_get_many(b, &gm2, &e), ERR_OK);
        CHECK_EQ(gm2.get_op_count, gm1.get_op_count);
        CHECK_EQ(gm2.actual_lookup_time, gm1.actual_lookup_time);
    }
}

/* The stream after Java's recovery of the first cut bytes of v's stream, as
 * the plan of 012-06 (rs_plan_recovery) says it: the cut bytes, a meta
 * block's fill, the torn record's header fix and zeros, the meta blocks it
 * reaches. Checked: the recovery's stream has the plan's length, the cut
 * bytes, and a failed torn record. */
static void check_recovered(const struct vec *v, int64_t cut, struct stream *s,
        const struct rs_recovery *got) {
    struct mem m;
    mem_init(&m);
    struct stream p;
    struct rs_recovery plan;
    struct err e;
    open_stream(&p, &m, v->stream, cut);
    REQUIRE(rs_plan_recovery(&p, &plan, &e) == ERR_OK);
    CHECK_EQ(stream_length(s), plan.length_after);
    CHECK_EQ(got->length_after, plan.length_after);
    CHECK_EQ(got->torn, plan.torn);
    CHECK_EQ(got->torn_size, plan.torn_size);
    CHECK_EQ(got->zero_fill, plan.zero_fill);
    CHECK_EQ(got->meta_fill, plan.meta_fill);
    CHECK_EQ(got->header_fix_len, plan.header_fix_len);
    CHECK_EQ(got->last_whole, plan.last_whole);
    /* the cut bytes are kept */
    uint8_t *b = malloc((size_t) stream_length(s) + 1);
    REQUIRE(stream_read(s, 0, b, (int32_t) stream_length(s), &e) == ERR_OK);
    CHECK(memcmp(b, v->stream, (size_t) cut) == 0);
    /* the torn record ends in 0 */
    if (plan.torn != SPOS_NULL) {
        int64_t lastByte = rs_get_spos(plan.torn, plan.torn_size - 1);
        CHECK_EQ(b[lastByte], 0);
    }
    free(b);
    stream_close(&p);
    CHECK_MEM_ZERO(&m);
}

TEST(sdb_java_stream) {
    struct vec v;
    REQUIRE(read_vec(&v));
    struct mem m;
    mem_init(&m);
    struct stream s, s2;
    open_stream(&s, &m, v.stream, v.len);
    open_stream(&s2, &m, v.stream, v.len);
    struct sdb b;
    struct replay r;
    struct err e;
    REQUIRE(sdb_open(&b, &s, &m, 8, true, &e) == ERR_OK);
    REQUIRE(replay_open(&r, &s2, &m, 8, &e) == ERR_OK);
    CHECK_EQ(sdb_recount(&b), 0);

    /* StartInfo and the status, as the replay's (Java's, 012-08) */
    CHECK_EQ(stream_length(&s), v.len);
    CHECK_EQ(b.start.startup_distance, 100);
    CHECK_EQ(b.start.start_pos, r.start_pos);
    CHECK_EQ(b.start.start_time, r.start_time);
    CHECK_EQ(b.start.trans_count, r.trans_count);
    CHECK_EQ(b.start.last_pos, r.last_pos);
    CHECK_EQ(b.last_trans_time, v.t[v.nt - 1].tt);
    /* the section: from the last record's startup position */
    const struct jtrans *last = &v.t[v.nt - 1];
    CHECK_EQ(b.start.start_pos, last->startup_pos);
    CHECK(b.start.trans_count < v.nt);       /* bounded: not every record */
    CHECK_EQ(b.start.rerun_pairs > 0, true);
    CHECK(b.newest_written_top != NULL);

    for (int32_t i = 0; i < v.nt; i++) {
        compare_reads(&b, &r, v.t[i].tt - 1);
        compare_reads(&b, &r, v.t[i].tt);
    }
    compare_reads(&b, &r, INT64_MAX);
    CHECK_EQ(sdb_recount(&b), 0);

    /* getTrans of every record */
    for (int32_t i = 0; i < v.nt; i++) {
        const struct st_record *st;
        REQUIRE(sdb_get_trans(&b, v.t[i].tpos, &st, &e) == ERR_OK);
        CHECK_EQ(st->tt, v.t[i].tt);
        CHECK_EQ(st->last_pos, v.t[i].last_pos);
    }
    sdb_close(&b);
    replay_close(&r);
    stream_close(&s);
    stream_close(&s2);
    CHECK_MEM_ZERO(&m);
    free(v.stream);
}

/* The stream cut at every position after the creation: recovered (the fill
 * as the plan says), started, and read as the replay of the same cut reads
 * it; then the recovered stream started again: nothing more written. */
TEST(sdb_cut_stream) {
    struct vec v;
    REQUIRE(read_vec(&v));
    for (int64_t cut = 264; cut <= v.len; cut++) {
        struct mem m;
        mem_init(&m);
        struct stream s, s2;
        open_stream(&s, &m, v.stream, cut);
        open_stream(&s2, &m, v.stream, cut);
        struct sdb b;
        struct replay r;
        struct err e;
        REQUIRE(sdb_open(&b, &s, &m, 8, true, &e) == ERR_OK);
        REQUIRE(replay_open(&r, &s2, &m, 8, &e) == ERR_OK);
        check_recovered(&v, cut, &s, &b.plan);
        CHECK_EQ(stream_length(&s), r.length);
        CHECK_EQ(b.start.start_pos, r.start_pos);
        CHECK_EQ(b.start.trans_count, r.trans_count);
        CHECK_EQ(b.start.last_pos, r.last_pos);
        compare_reads(&b, &r, INT64_MAX);
        CHECK_EQ(sdb_recount(&b), 0);
        sdb_close(&b);

        /* A second start of the recovered stream writes nothing. */
        int64_t len = stream_length(&s);
        REQUIRE(sdb_open(&b, &s, &m, 8, true, &e) == ERR_OK);
        CHECK_EQ(stream_length(&s), len);
        CHECK_EQ(b.plan.torn, SPOS_NULL);
        compare_reads(&b, &r, INT64_MAX);
        sdb_close(&b);

        replay_close(&r);
        stream_close(&s);
        stream_close(&s2);
        CHECK_MEM_ZERO(&m);
    }
    free(v.stream);
}

/* Java's refusals at a start, before anything is written. */
TEST(sdb_refusals) {
    struct vec v;
    REQUIRE(read_vec(&v));
    struct mem m;
    mem_init(&m);
    struct stream s;
    struct sdb b;
    struct err e;

    /* Another node size (005-50): nothing written. */
    open_stream(&s, &m, v.stream, v.len - 5);
    CHECK_EQ(sdb_open(&b, &s, &m, 14, false, &e), ERR_FORMAT);
    CHECK(strcmp(e.java, "StreamFormatException") == 0);
    CHECK_EQ(stream_length(&s), v.len - 5);
    stream_close(&s);

    /* An empty stream: Java creates the database (012-09). */
    stream_open_memory(&s, &m);
    CHECK_EQ(sdb_open(&b, &s, &m, 8, false, &e), ERR_ARG);
    CHECK(strcmp(e.java, "UnsupportedOperationException") == 0);
    stream_close(&s);

    /* A creation cut short (005-33): nothing written. */
    const int64_t cuts[] = { 1, 60, 127, 128, 130, 148, 200, 263 };
    for (size_t i = 0; i < sizeof cuts / sizeof cuts[0]; i++) {
        open_stream(&s, &m, v.stream, cuts[i]);
        CHECK(sdb_open(&b, &s, &m, 8, false, &e) != ERR_OK);
        CHECK(strcmp(e.java, "DatabaseNotCreatedException") == 0);
        CHECK_EQ(stream_length(&s), cuts[i]);
        stream_close(&s);
    }

    /* Bad magic bytes: BadCryptoKey, nothing written. */
    uint8_t *copy = malloc((size_t) v.len);
    memcpy(copy, v.stream, (size_t) v.len);
    copy[0] ^= 1;
    open_stream(&s, &m, copy, v.len - 3);
    CHECK(sdb_open(&b, &s, &m, 8, false, &e) != ERR_OK);
    CHECK(strcmp(e.java, "BadCryptoKey") == 0);
    CHECK_EQ(stream_length(&s), v.len - 3);
    stream_close(&s);

    /* Another version in the meta block: VersioningStreamException. */
    memcpy(copy, v.stream, (size_t) v.len);
    copy[4] = 1;
    open_stream(&s, &m, copy, v.len);
    CHECK(sdb_open(&b, &s, &m, 8, false, &e) != ERR_OK);
    CHECK(strcmp(e.java, "VersioningStreamException") == 0);
    stream_close(&s);

    /* No node size in the block (a database before 005-50). */
    memcpy(copy, v.stream, (size_t) v.len);
    copy[44] = 0;
    copy[45] = 0;
    open_stream(&s, &m, copy, v.len);
    CHECK(sdb_open(&b, &s, &m, 8, false, &e) != ERR_OK);
    CHECK(strcmp(e.java, "VersioningStreamException") == 0);
    stream_close(&s);

    /* The last record's topPos names a key node: refused, as Java's since release 2026.3
     * (before, C's AssertionError of an assert was taken too). */
    memcpy(copy, v.stream, (size_t) v.len);
    const struct jtrans *last = &v.t[v.nt - 1];
    /* its first node (a top node or a key node) is at tpos + 32 */
    int64_t keyPos = -1;
    for (int64_t p = last->tpos + 32; p < last->last_pos; ) {
        int32_t size = (int32_t) (copy[p] | copy[p + 1] << 8 | copy[p + 2] << 16);
        if (size == 0) {
            break;
        }
        if (copy[p + 4] == NODE_KEY) {
            keyPos = p;
            break;
        }
        p += size;
    }
    if (keyPos > 0) {
        for (int k = 0; k < 8; k++) {
            copy[last->tpos + 24 + k] = (uint8_t) (keyPos >> (8 * k));
        }
        open_stream(&s, &m, copy, v.len);
        CHECK(sdb_open(&b, &s, &m, 8, false, &e) != ERR_OK);
        CHECK(strcmp(e.java, "StreamFormatException") == 0);
        char want[120];
        snprintf(want, sizeof want, "topPos %lld of the last transaction names a KeyNode, not "
                "a top node.", (long long) keyPos);
        CHECK(strcmp(e.text, want) == 0);
        stream_close(&s);
    }

    /* The records' times, checked before replay (bergdb 005-75, as Java's
     * since release 2026.2; before, C aborted on such a time, 012-14): the
     * last record's time beyond the 56 bits, and equal to the time of the
     * record before it, when both are in the startup section. The record's
     * header has no checksum. */
    const struct jtrans *before = &v.t[v.nt - 2];
    memcpy(copy, v.stream, (size_t) v.len);
    for (int k = 0; k < 8; k++) {
        copy[last->tpos + 8 + k] = (uint8_t) ((KL_MAX_TIME + 1) >> (8 * k));
    }
    open_stream(&s, &m, copy, v.len);
    CHECK_EQ(sdb_open(&b, &s, &m, 8, false, &e), ERR_FORMAT);
    CHECK(strcmp(e.java, "StreamFormatException") == 0);
    CHECK(strncmp(e.text, "Transaction time out of range", 29) == 0);
    stream_close(&s);
    REQUIRE(before->tpos >= last->startup_pos && before->tt < last->tt);
    memcpy(copy, v.stream, (size_t) v.len);
    for (int k = 0; k < 8; k++) {
        copy[last->tpos + 8 + k] = (uint8_t) (before->tt >> (8 * k));
    }
    open_stream(&s, &m, copy, v.len);
    CHECK_EQ(sdb_open(&b, &s, &m, 8, false, &e), ERR_FORMAT);
    CHECK(strcmp(e.java, "StreamFormatException") == 0);
    CHECK(strncmp(e.text, "non-increasing tt", 17) == 0);
    stream_close(&s);
    free(copy);
    CHECK_MEM_ZERO(&m);
    free(v.stream);
}

/* A copy of the vectors' stream with n bytes written at 'at', started: refused with a
 * StreamFormatException (or 'java') whose text is 'text', or contains it if 'contains';
 * nothing written. */
static void refused(const struct vec *v, int64_t at, const uint8_t *bytes, int32_t n,
        const char *java, const char *text, bool contains) {
    struct mem m;
    struct stream s;
    struct sdb b;
    struct err e;
    mem_init(&m);
    uint8_t *copy = malloc((size_t) v->len);
    memcpy(copy, v->stream, (size_t) v->len);
    memcpy(copy + at, bytes, (size_t) n);
    open_stream(&s, &m, copy, v->len);
    err_clear(&e);
    enum err_code rc = sdb_open(&b, &s, &m, 8, true, &e);
    if (rc == ERR_OK) {
        sdb_close(&b);
    }
    CHECK_EQ(rc, ERR_FORMAT);
    bool same = strcmp(e.java, java) == 0
            && (contains ? strstr(e.text, text) != NULL : strcmp(e.text, text) == 0);
    CHECK(same);
    if (!same) {
        printf("    at %lld: %s: %s\n", (long long) at, e.java, e.text);
    }
    CHECK_EQ(stream_length(&s), v->len);
    CHECK(memcmp(s.bytes, copy, (size_t) v->len) == 0);
    stream_close(&s);
    free(copy);
    CHECK_MEM_ZERO(&m);
}

static void le64(int64_t x, uint8_t out[8]) {
    for (int k = 0; k < 8; k++) {
        out[k] = (uint8_t) ((uint64_t) x >> (8 * k));
    }
}

/* DbTesterRestart's refusals of release 2026.3, ported onto the vectors' stream (node size
 * 8, startup distance 100: its last record, at 3960, starts at 3824, so the startup section
 * is the records at 3824 and 3960). Each failed before its fix: C took the stream, or
 * refused it with another exception or text (an AssertionError where Java had an assert).
 * And the stream as it is starts. */
TEST(sdb_refusals_2026_3) {
    struct vec v;
    REQUIRE(read_vec(&v));
    REQUIRE(v.nt >= 4);
    const struct jtrans *last = &v.t[v.nt - 1];
    uint8_t b[8];
    char want[300];

    /* testEnlargedRecordSizeRefused (015-72): a record's size set to its own and the next
     * one's together, so that it ends on the next one's last byte; for each record in
     * turn. Before, C took it, and the walk skipped the record it covered. */
    for (int32_t k = 1; k + 1 < v.nt; k++) {
        const int64_t a = v.t[k].tpos;
        const int64_t c = k + 2 < v.nt ? v.t[k + 2].tpos : v.len;
        int32_t size = (int32_t) (c - a);
        for (int i = 0; i < 4; i++) {
            b[i] = (uint8_t) (size >> (8 * i));
        }
        snprintf(want, sizeof want, "The record at %lld ends at offset %lld by its content, "
                "and its size says %d.", (long long) a, (long long) (v.t[k + 1].tpos - a),
                (int) size);
        refused(&v, a, b, 4, "StreamFormatException", want, false);
    }

    /* testCorruptStartupPosRefused (015-75): the last record's startupPos negative, not a
     * multiple of 8, in the first meta block, or after the record. Before, C refused -8
     * with an AssertionError, and walked from the others. */
    const int64_t c = last->tpos;
    const int64_t sps[8] = { -8, INT64_MIN, 4, 8, 120, c + 4, c + 8, c | (INT64_C(1) << 40) };
    const char *problems[8] = { "negative", "negative", "not a multiple of 8",
            "in the first meta block", "in the first meta block", "not a multiple of 8",
            "after the record", "after the record" };
    for (int i = 0; i < 8; i++) {
        le64(sps[i], b);
        snprintf(want, sizeof want, "The record at %lld has startupPos %lld, %s.",
                (long long) c, (long long) sps[i], problems[i]);
        refused(&v, c + 16, b, 8, "StreamFormatException", want, false);
    }

    /* testCorruptGotDirtyIdRefused (015-75): the id of a got-dirty entry of the last record
     * (rerun: the section's second) whose position is a node's, 123456789. Before, C
     * refused it with an AssertionError ("ids differ"), as Java's assert. */
    {
        struct mem m;
        struct err e;
        struct st_record r;
        mem_init(&m);
        st_init(&r);
        const int32_t size = (int32_t) (v.len - last->tpos);
        REQUIRE(st_parse(&r, last->tpos, v.stream + last->tpos, size, &m, &e) == ERR_OK);
        int32_t entry = -1;
        for (int32_t i = 0; i < r.got_dirty_count && entry < 0; i++) {
            int64_t pos = st_got_dirty_pos(&r, i);
            if (spos_is_valid(pos) && !spos_is_vpos(pos)) {
                entry = i;
            }
        }
        REQUIRE(entry >= 0);
        const int64_t at = last->tpos + (r.got_dirty - (v.stream + last->tpos)) + 16 * entry;
        const int64_t id = st_got_dirty_id(&r, entry), pos = st_got_dirty_pos(&r, entry);
        st_free(&r, &m);
        CHECK_MEM_ZERO(&m);
        le64(123456789, b);
        snprintf(want, sizeof want, "The got-dirty entry of node 123456789 names position "
                "%lld, where node %lld is.", (long long) pos, (long long) id);
        refused(&v, at, b, 8, "StreamFormatException", want, false);
    }

    /* testOlderTopPosRefused (015-75): the last record's topPos an older version of its top
     * node (2601, at 3992; older at 2776 and 3424). Before, C refused it with an
     * AssertionError, as Java's assert. */
    {
        int64_t id = -1, older = -1;
        for (int32_t k = 0; k < v.nt; k++) {
            if (v.t[k].top_pos == last->top_pos) {
                continue;
            }
            if (v.t[k].top_pos > older && v.t[k].top_pos < last->top_pos
                    && bytes_get_long_le(v.stream + v.t[k].top_pos + 16)
                    == bytes_get_long_le(v.stream + last->top_pos + 16)) {
                older = v.t[k].top_pos;
                id = bytes_get_long_le(v.stream + last->top_pos + 16);
            }
        }
        REQUIRE(older > 0);
        le64(older, b);
        snprintf(want, sizeof want, "The last transaction's topPos %lld is not the newest "
                "version %lld of top node %lld.", (long long) older, (long long) last->top_pos,
                (long long) id);
        refused(&v, last->tpos + 24, b, 8, "StreamFormatException", want, false);
    }

    /* testMetaBlockLastTransPosRefused (019-34): the first meta block's byte 23 (its last
     * transaction, Spos.NULL as the creation wrote it) xor 0x80 and 0xff. Before, C refused
     * it in the recovery's walk with an IllegalArgumentException ("spos >= streamSize"). */
    for (int i = 0; i < 2; i++) {
        uint8_t x = (uint8_t) (v.stream[23] ^ (i == 0 ? 0x80 : 0xff));
        int64_t named = bytes_get_long_le(v.stream + 16);
        named = (int64_t) (((uint64_t) named & UINT64_C(0x00ffffffffffffff))
                | ((uint64_t) x << 56));
        snprintf(want, sizeof want, "The meta block at 0 names the last transaction at %lld, "
                "which cannot be one in a stream from 0: not before the block.",
                (long long) named);
        refused(&v, 23, &x, 1, "StreamFormatException", want, false);
    }

    /* testVersionHighBytesRefused (019-01): byte 6 or 7 of the meta block set to 1: the
     * version, an int, is not 154. Before, C read 2 bytes, and started. */
    const uint8_t one = 1;
    refused(&v, 6, &one, 1, "VersioningStreamException", "Cannot read meta block with version "
            "65690. Version supported: 154", false);
    refused(&v, 7, &one, 1, "VersioningStreamException", "Cannot read meta block with version "
            "16777370. Version supported: 154", false);

    /* The stream as it is: started. */
    {
        struct mem m;
        struct stream s;
        struct sdb d;
        struct err e;
        mem_init(&m);
        open_stream(&s, &m, v.stream, v.len);
        CHECK_EQ(sdb_open(&d, &s, &m, 8, true, &e), ERR_OK);
        sdb_close(&d);
        stream_close(&s);
        CHECK_MEM_ZERO(&m);
    }
    free(v.stream);
}

TEST(sdb_allocation_failures) {
    struct vec v;
    REQUIRE(read_vec(&v));
    int64_t runs = 0;
    /* a cut inside the last record, so that the fill is written too */
    const int64_t cut = v.t[v.nt - 1].tpos + 40;
    for (int64_t failAt = 1; failAt < 100000; failAt++) {
        struct mem m;
        mem_init(&m);
        struct stream s;
        open_stream(&s, &m, v.stream, cut);
        m.fail_at = m.allocs + failAt;
        struct sdb b;
        struct err e;
        enum err_code rc = sdb_open(&b, &s, &m, 8, true, &e);
        bool inClose = false;
        if (rc == ERR_OK) {
            struct getmany g;
            sdb_new_get_many(&b, &g);
            rc = sdb_get_many(&b, &g, &e);
            const struct st_record *st;
            if (rc == ERR_OK) {
                rc = sdb_get_trans(&b, 312, &st, &e);
            }
            bool before = m.failed > 0;
            sdb_close(&b);      /* without the roots' list, the counts free all */
            inClose = !before && m.failed > 0;
        }
        bool failed = m.failed > 0 && !inClose;
        m.fail_at = 0;
        stream_close(&s);
        CHECK_MEM_ZERO(&m);
        runs++;
        if (inClose) {
            CHECK_EQ(rc, ERR_OK);
            continue;
        }
        if (!failed) {
            CHECK_EQ(rc, ERR_OK);
            break;
        }
        CHECK(rc != ERR_OK);
    }
    CHECK(runs > 50);
    free(v.stream);
}

const struct test sdb_tests[] = {
    TEST_ENTRY(sdb_java_stream),
    TEST_ENTRY(sdb_cut_stream),
    TEST_ENTRY(sdb_refusals),
    TEST_ENTRY(sdb_refusals_2026_3),
    TEST_ENTRY(sdb_allocation_failures),
    TEST_END
};
