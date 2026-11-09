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
#include <time.h>
#include "bytes.h"
#include "checksum.h"
#include "getmany.h"
#include "keys.h"
#include "klong.h"
#include "lmap.h"
#include "mdb.h"
#include "mem.h"
#include "meta.h"
#include "nfix.h"
#include "nstream.h"
#include "recover.h"
#include "replay.h"
#include "rstream.h"
#include "sdb.h"
#include "snode.h"
#include "spos.h"
#include "starter.h"
#include "strans.h"
#include "stream.h"
#include "test.h"
#include "tnode.h"

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

/* True if 'text' is Java's text of a record refused by the start for its
 * time: the reason, then StoredTrans.toString of the record with time tt
 * (Java's other fields of it, from the vectors), and nothing more, or the
 * line of its got-dirty pairs. */
static bool records_text(const char *text, const char *reason, int64_t tt,
        const struct jtrans *t) {
    char want[300];
    int n = snprintf(want, sizeof want, "%s, tt:%lld, tpos:%lld, lastPos:%lld, startupPos:%lld, "
            "topPos:%lld, nodeCount:%d", reason, (long long) tt, (long long) t->tpos,
            (long long) t->last_pos, (long long) t->startup_pos, (long long) t->top_pos,
            (int) t->nnodes);
    return strncmp(text, want, (size_t) n) == 0
            && (text[n] == '\0' || strncmp(text + n, "\ngot dirty: ", 12) == 0);
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

    /* Bad magic bytes: a StreamFormatException with Java's text, cut at 239
     * bytes, and the BadMagicBytes its cause, nothing written (bergdb 020-28,
     * as Java's since release 2026.4: BadCryptoKey before). */
    static const char magic[] = "Invalid magic bytes in stream: the stream is not a BergDB stream, or it is "
            "damaged; or an earlier release of BergDB, 2026.3 or before, encrypted it, and "
            "this release cannot read it: it has no encryption (bergdb 020-28). The start "
            "has written nothing.";
    uint8_t *copy = malloc((size_t) v.len);
    memcpy(copy, v.stream, (size_t) v.len);
    copy[0] ^= 1;
    open_stream(&s, &m, copy, v.len - 3);
    CHECK(sdb_open(&b, &s, &m, 8, false, &e) != ERR_OK);
    CHECK(strcmp(e.java, "StreamFormatException") == 0);
    CHECK(strcmp(e.cause, "BadMagicBytes") == 0);
    CHECK(strlen(e.text) == ERR_TEXT - 1 && strncmp(e.text, magic, ERR_TEXT - 1) == 0);
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
     * header has no checksum. The texts are Java's, StoredTrans.toString
     * after the reason, from Java's fields of the record (022-01, step 4:
     * the corrupt-stream set found C's, which named tpos and tt only). */
    const struct jtrans *before = &v.t[v.nt - 2];
    memcpy(copy, v.stream, (size_t) v.len);
    for (int k = 0; k < 8; k++) {
        copy[last->tpos + 8 + k] = (uint8_t) ((KL_MAX_TIME + 1) >> (8 * k));
    }
    open_stream(&s, &m, copy, v.len);
    CHECK_EQ(sdb_open(&b, &s, &m, 8, false, &e), ERR_FORMAT);
    CHECK(strcmp(e.java, "StreamFormatException") == 0);
    CHECK(records_text(e.text, "Transaction time out of range", KL_MAX_TIME + 1, last));
    stream_close(&s);
    REQUIRE(before->tpos >= last->startup_pos && before->tt < last->tt);
    memcpy(copy, v.stream, (size_t) v.len);
    for (int k = 0; k < 8; k++) {
        copy[last->tpos + 8 + k] = (uint8_t) (before->tt >> (8 * k));
    }
    open_stream(&s, &m, copy, v.len);
    CHECK_EQ(sdb_open(&b, &s, &m, 8, false, &e), ERR_FORMAT);
    CHECK(strcmp(e.java, "StreamFormatException") == 0);
    CHECK(records_text(e.text, "non-increasing tt", before->tt, last));
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

/* A copy of the vectors' stream with the 8 bytes at byte 'at' of the node at nodePos set to
 * 'value', the node's checksum made right (CorruptStreamTester.nodeCopy). Freed by the
 * caller. */
static uint8_t *node_copy(const struct vec *v, int64_t nodePos, int32_t at, int64_t value) {
    uint8_t *copy = malloc((size_t) v->len);
    memcpy(copy, v->stream, (size_t) v->len);
    le64(value, copy + nodePos + at);
    const int32_t size = bytes_get_int_le(copy + nodePos);
    const int32_t sum = cks_sum_with_zero_replace(copy, (int32_t) nodePos, size,
            (int32_t) nodePos + 6);
    copy[nodePos + 6] = (uint8_t) sum;
    copy[nodePos + 7] = (uint8_t) (sum >> 8);
    return copy;
}

/* copy started with the check by node id or without: refused at the start with Java's
 * StreamFormatException and 'text' if 'text', else started, and a read at time t (getMany
 * forward) refused with 'readText' (sdb.c's DbFailedException). */
static void found_start(const struct vec *v, const uint8_t *copy, bool check,
        const char *text, int64_t t, const char *readText) {
    struct mem m;
    struct stream s;
    struct sdb d;
    struct err e;
    mem_init(&m);
    open_stream(&s, &m, copy, v->len);
    err_clear(&e);
    enum err_code rc = sdb_open(&d, &s, &m, 8, check, &e);
    if (text != NULL) {
        CHECK_EQ(rc, ERR_FORMAT);
        bool same = strcmp(e.java, "StreamFormatException") == 0 && strcmp(e.text, text) == 0;
        CHECK(same);
        if (!same) {
            printf("    check %d: %s: %s\n", (int) check, e.java, e.text);
        }
        CHECK(memcmp(s.bytes, copy, (size_t) v->len) == 0);    /* nothing written */
    } else {
        CHECK_EQ(rc, ERR_OK);
    }
    if (rc == ERR_OK) {
        struct getmany g;
        sdb_new_get_many(&d, &g);
        g.lookup_time = t;
        g.forward = true;
        err_clear(&e);
        rc = sdb_get_many(&d, &g, &e);
        if (text == NULL) {
            CHECK(rc != ERR_OK && strcmp(e.text, readText) == 0);
            if (rc == ERR_OK || strcmp(e.text, readText) != 0) {
                printf("    check %d, the read: %s: %s\n", (int) check, e.java, e.text);
            }
        }
        sdb_close(&d);
    }
    stream_close(&s);
    CHECK_MEM_ZERO(&m);
}

/* CorruptStreamTester.testFound021_11 (bergdb 021-11, as Java's since release 2026.4), on the
 * vectors' stream: a pointer that the start links by node id (NodeCollection.linkToCanonical,
 * rule 4) set to a version of a node of another type, its node's checksum made right, is
 * refused at the start with Java's text. The startup section is the records at 3824 and 3960
 * (sdb_refusals_2026_3); the last record's nodes are of D. (a) Its top node 2601 at 3992,
 * skip pointer 1 (pointer 2, its byte 56) set to 3496, a version of key node 1359 from before
 * the section, linked by the header's node id: refused, with the check by node id and
 * without. Before, the start took it, and a read at time 2030, which takes the skip pointer,
 * refused it where it cast the node (the JVM's ClassCastException). (b) Its key node 2599 at
 * 4064, pointer 4 set to 2776, an older version of top node 2601, in neither of the start's
 * maps: with the check by node id (Java's -ea), refused; before, the check's AssertionError
 * (005-57). Without the check, as Java without -ea, nothing is linked: started, and a read
 * refuses the pointer, which Rule R makes name the newest version, 3992. Its other pointers
 * set so are refused by the rerun's follows (019-32), and a key node's pointer that rule 4
 * links by posToId to a top node is t_ncoll.c's ncoll_link_to_canonical_another_type. On
 * Java's streams of LONG: the corrupt set's found-long-1 (CorruptSet.java). */
TEST(sdb_found_021_11) {
    struct vec v;
    REQUIRE(read_vec(&v));
    const int64_t top = 3992, key = 4064, keyOld = 3496, topOld = 2776;
    REQUIRE(v.t[v.nt - 1].tpos == 3960 && v.t[v.nt - 1].top_pos == top);
    REQUIRE(v.stream[top + 4] == NODE_TOP && bytes_get_long_le(v.stream + top + 16) == 2601);
    REQUIRE(bytes_get_long_le(v.stream + top + 56) == 2192);           /* skip pointer 1 */
    REQUIRE(v.stream[key + 4] == NODE_KEY && bytes_get_long_le(v.stream + key + 24) == 2599);
    const int32_t n = bytes_get_short_le(v.stream + key + 17);
    REQUIRE(n == 7 && bytes_get_long_le(v.stream + key + 32 + 8 * n + 8 * 4) == 4208);
    REQUIRE(v.stream[keyOld + 4] == NODE_KEY && v.stream[topOld + 4] == NODE_TOP);
    REQUIRE(bytes_get_long_le(v.stream + topOld + 16) == 2601);

    uint8_t *copy = node_copy(&v, top, 56, keyOld);
    for (int check = 1; check >= 0; check--) {
        found_start(&v, copy, check == 1,
                "Pointer 2 of node 2601 names a node of type 20 at 3496, not 10.", 0, NULL);
    }
    free(copy);

    copy = node_copy(&v, key, 32 + 8 * n + 8 * 4, topOld);
    found_start(&v, copy, true, "Pointer 4 of node 2599 names a node of type 10 at 2776, not 20.",
            0, NULL);
    found_start(&v, copy, false, NULL, 2130,
            "A read failed: Pointer 4 of node 2599 names a node of type 10 at 3992, not 20.");
    free(copy);
    free(v.stream);
}

/* A copy started (with the check by node id or without): refused at the start with Java's
 * StreamFormatException and 'text', nothing written, or, if 'text' is NULL, started. */
static void start_copy(const struct vec *v, const uint8_t *copy, bool check, const char *text) {
    if (text != NULL) {
        found_start(v, copy, check, text, 0, NULL);
        return;
    }
    struct mem m;
    struct stream s;
    struct sdb d;
    struct err e;
    mem_init(&m);
    open_stream(&s, &m, copy, v->len);
    err_clear(&e);
    enum err_code rc = sdb_open(&d, &s, &m, 8, check, &e);
    CHECK_EQ(rc, ERR_OK);
    if (rc == ERR_OK) {
        sdb_close(&d);
    } else {
        printf("    check %d: %s: %s\n", (int) check, e.java, e.text);
    }
    stream_close(&s);
    CHECK_MEM_ZERO(&m);
}

/* CorruptStreamTester.testFound021_12 (bergdb 021-12, as Java's since release 2026.4), on the
 * vectors' stream: a key node version that the start reads from before its startup section
 * (the records at 3824 and 3960, the startup time 2120), damaged so that it breaks KeyNode's
 * invariants, its checksum right, is refused at the start with Java's StreamFormatException
 * and text, as the section's own nodes are (validateNode): the start validates it before
 * the cut back (nc_validate_key_node, Java's DbStarter.validateKeyNode) where it reads it,
 * by a follow during the reconstruction (read_version, NodeCollection.readVersion) and as the
 * canonical object of a got-dirty node (canonical_node, DbStarter.canonicalNode). Before, C
 * took such a version: (a) a time klong's byte xor 0xff, the times not increasing, gave the
 * AssertionError of the start's check of its nodes (post_startup_check, Java's KeyNode.check
 * from DbStarter.postStartupCheck), or (b) failed an assert of the rerun's put, an abort
 * (dag.c's append_delete_klong and append_klongs, knode.c's kn_add_klong: Java's
 * KeyNode.addKlong); a time after the startup time that kept the times increasing was
 * started; (c) the first klong, a time klong, made a key klong, whose pointer is Spos.NULL
 * (the int 0x7ffffff8 at the node's byte 36), gave the start's check's AssertionError. The
 * text of (c) names the node by its id and position (bergdb 021-15, as Java's since release
 * 2026.4; Java's printed the node, KeyNode.print, with Object.toString's identity hash, and
 * C's was its own, "Bad spos of pointer, at or before the startup time"). On Java's streams
 * of keys of three segments: the corrupt set's found-long-3971358, testFound021_12's own
 * copies (CorruptSet.java), whose texts Java's test checks exactly since 021-15. */
TEST(sdb_found_021_12) {
    struct vec v;
    REQUIRE(read_vec(&v));
    const struct jtrans *last = &v.t[v.nt - 1];
    REQUIRE(last->tpos == 3960 && last->startup_pos == 3824);
    REQUIRE(v.t[v.nt - 2].tpos == 3824 && v.t[v.nt - 2].tt == 2120);
    /* The node's position and id, the klong's byte in the node, and xor 0xff of its low
     * byte, or (mask 0) its high int set to 0x7ffffff8; the text, NULL: started. The
     * versions of key nodes 1357, 2595 and 1359 that the rerun's puts reach, by its follows
     * (read_version). And, after the entry's change below, of 733 and 735, which the rerun
     * does not reach, read as the canonical objects of D (canonical_node). */
    const struct {
        int64_t pos, id;
        int32_t at, mask;
        const char *text;
    } rows[] = {
        /* (a): 2595's time 2090 made 2261 */
        { 2848, 2595, 32, 0xff, "Time not increasing, 2100, 2261, index=4" },
        /* (b): 1357's time 2050 made 2301; before, an abort in append_delete_klong */
        { 1760, 1357, 32, 0xff, "Time not increasing, 2060, 2301, index=3" },
        /* (b): 2595's last time, 2100, made 2251; before, an abort in kn_add_klong */
        { 2848, 2595, 64, 0xff, "Key node 2595 at 2848, before the startup section, has the "
                "time 2251, after the startup time 2120." },
        /* (b): 1359's time 2050 made 2301; before, an abort in append_klongs */
        { 3496, 1359, 32, 0xff, "Time not increasing, 2100, 2301, index=4" },
        /* 1359's last time, 2110, made 2241; before, started */
        { 3496, 1359, 80, 0xff, "Key node 1359 at 3496, before the startup section, has the "
                "time 2241, after the startup time 2120." },
        /* (c) */
        { 2848, 2595, 32, 0, "Bad spos of pointer 0 of key node 2595 at 2848: -1, at or before "
                "the startup time 2120." },
        /* canonical_node, (a): 733's time 2040 made 1799 */
        { 1008, 733, 56, 0xff, "Time not increasing, 1799, 2030, index=3" },
        /* canonical_node: 735's last time, 2080, made 2271; before, started */
        { 2376, 735, 80, 0xff, "Key node 735 at 2376, before the startup section, has the "
                "time 2271, after the startup time 2120." },
        /* canonical_node: unchanged; started */
        { 1008, 733, 32, -1, NULL },
        { 2376, 735, 32, -1, NULL },
    };
    /* The last record's got-dirty entry of 2595 at 2848, set to the canonical rows' node and
     * version: a version that the rerun does not reach, as the entry of a node that a touch
     * made dirty names one (a reclaim step's, which is not rerun). */
    int64_t entry;
    {
        struct mem m;
        struct err e;
        struct st_record r;
        mem_init(&m);
        st_init(&r);
        REQUIRE(st_parse(&r, last->tpos, v.stream + last->tpos, (int32_t) (v.len - last->tpos),
                &m, &e) == ERR_OK);
        REQUIRE(r.got_dirty_count == 5 && st_got_dirty_id(&r, 2) == 2595
                && st_got_dirty_pos(&r, 2) == 2848);
        entry = last->tpos + (r.got_dirty - (v.stream + last->tpos)) + 16 * 2;
        st_free(&r, &m);
        CHECK_MEM_ZERO(&m);
    }
    for (size_t r = 0; r < sizeof rows / sizeof rows[0]; r++) {
        const int64_t p = rows[r].pos;
        REQUIRE(v.stream[p + 4] == NODE_KEY && bytes_get_long_le(v.stream + p + 24) == rows[r].id);
        REQUIRE(p < 3824 && rows[r].at < 32 + 8 * bytes_get_short_le(v.stream + p + 17));
        const int64_t klong = bytes_get_long_le(v.stream + p + rows[r].at);
        REQUIRE(kl_get_type(klong) == KL_TYPE_TIME);
        const int64_t value = rows[r].mask > 0 ? klong ^ rows[r].mask
                : rows[r].mask < 0 ? klong
                : (int64_t) (((uint64_t) klong & UINT64_C(0xffffffff))
                | ((uint64_t) 0x7ffffff8 << 32));
        uint8_t *copy = node_copy(&v, p, rows[r].at, value);
        if (p == 1008 || p == 2376) {
            le64(rows[r].id, copy + entry);
            le64(p, copy + entry + 8);
        }
        for (int check = 1; check >= 0; check--) {
            start_copy(&v, copy, check == 1, rows[r].text);
        }
        free(copy);
    }
    free(v.stream);
}

static bool same_error(const struct err *e, const char *java, const char *text) {
    if (strcmp(e->java, java) == 0 && strcmp(e->text, text) == 0) {
        return true;
    }
    printf("    expected %s: \"%s\", got %s: \"%s\"\n", java, text, e->java, e->text);
    return false;
}

/* DbStarter's texts that name a node (bergdb 021-15, as Java's since release 2026.4): by
 * Node.name, "KIND ID at SPOS", the same in every run, where Java's printed the node
 * (Object.toString's identity hash) and C's named it by its id or its type alone.
 * DbStarter.testCheckStreamPointersOfKeyNode (a key node that points to a vpos refused, one
 * that points to a position taken; C's key klong "a"'s), and a top node's; validateNode's
 * position of a node (no stream gives a negative one); checkPrimordialTransaction's nodes;
 * checkThatValueNodesHaveSpos (an AssertionError). */
TEST(sdb_starter_node_texts) {
    struct nfix f;
    struct err e;
    nfix_init(&f);
    struct knode *good = kn_new_with_time(&f.cx, 10);
    REQUIRE(good != NULL && kn_add_to_end(&f.cx, good, nfix_key("a"), NULL, 2000));
    good->n.spos = 1000;
    CHECK_EQ(sr_check_stream_pointers(&good->n, &e), ERR_OK);
    struct knode *bad = kn_new_with_time(&f.cx, 10);
    REQUIRE(bad != NULL && kn_add_to_end(&f.cx, bad, nfix_key("a"), NULL, 2001));
    bad->n.id = 999;
    bad->n.spos = 1000;
    CHECK_EQ(sr_check_stream_pointers(&bad->n, &e), ERR_FORMAT);
    CHECK(same_error(&e, "StreamFormatException", "Unexpected stream pointer 2001, index 1 of "
            "key node 999 at 1000."));
    struct tnode *top = tn_new(&f.cx, 1, NULL, 2001, 10, 1000);
    REQUIRE(top != NULL);
    top->n.id = 77;
    CHECK_EQ(sr_check_stream_pointers(&top->n, &e), ERR_FORMAT);
    CHECK(same_error(&e, "StreamFormatException", "Unexpected stream pointer 2001, index 0 of "
            "top node 77 at 1000."));

    struct sn_node nodes[2];
    memset(nodes, 0, sizeof nodes);
    nodes[0].type = NODE_KEY;
    nodes[0].id = 7;
    nodes[0].spos = -1;
    CHECK_EQ(sr_validate_node(&f.cx, &nodes[0], 470, &e), ERR_FORMAT);
    CHECK(same_error(&e, "StreamFormatException", "Bad spos of key node 7 at -1."));
    nodes[0].type = NODE_DELETE;
    nodes[0].spos = -8;
    CHECK_EQ(sr_validate_node(&f.cx, &nodes[0], 470, &e), ERR_FORMAT);
    CHECK(same_error(&e, "StreamFormatException", "Bad spos of value node 7 at -8."));

    struct st_record r;
    st_init(&r);
    r.nodes = nodes;
    r.nnodes = 2;
    nodes[0] = (struct sn_node) { .type = NODE_KEY, .spos = 136, .id = 2 };
    nodes[1] = (struct sn_node) { .type = NODE_TOP, .spos = 200, .id = 1 };
    CHECK_EQ(sr_check_primordial_transaction(&r, &e), ERR_FORMAT);
    CHECK(same_error(&e, "StreamFormatException", "Expected TopNode, got key node 2 at 136."));
    nodes[0] = (struct sn_node) { .type = NODE_TOP, .spos = 136, .id = 1 };
    CHECK_EQ(sr_check_primordial_transaction(&r, &e), ERR_FORMAT);
    CHECK(same_error(&e, "StreamFormatException", "Expected KeyNode, got top node 1 at 200."));
    nodes[1] = (struct sn_node) { .type = NODE_VALUE, .spos = 200, .id = 2 };
    CHECK_EQ(sr_check_primordial_transaction(&r, &e), ERR_FORMAT);
    CHECK(same_error(&e, "StreamFormatException", "Expected KeyNode, got value node 2 at 200."));
    nodes[1] = (struct sn_node) { .type = NODE_KEY, .spos = 200, .id = 2 };
    CHECK_EQ(sr_check_primordial_transaction(&r, &e), ERR_OK);

    struct vnode *v = nfix_value(&f);
    REQUIRE(v != NULL);
    v->n.id = 5;
    REQUIRE(kn_add_to_end(&f.cx, good, nfix_key("b"), &v->n.o, SPOS_NULL));
    CHECK_EQ(sr_check_value_nodes_have_spos(good, &e), ERR_FORMAT);
    CHECK(same_error(&e, "AssertionError", "value node got no spos during startup, value node 5 "
            "at -1."));
    v->n.spos = 3000;
    CHECK_EQ(sr_check_value_nodes_have_spos(good, &e), ERR_OK);
    NFIX_END(&f);
}

/* A key node of the startup section whose key klong points to a vpos, its checksum right:
 * refused at the start by checkStreamPointers, after the cut back, with Java's text, which
 * names the node by its id and position (bergdb 021-15; C named it by its id alone). On the
 * vectors' stream (the section's records at 3824 and 3960, the startup time 2120), the first
 * key node of the section with a key klong at or before the startup time, which the cut back
 * keeps, that has a position: the position set to 2001. */
TEST(sdb_section_pointer_to_a_vpos) {
    struct vec v;
    REQUIRE(read_vec(&v));
    const struct jtrans *last = &v.t[v.nt - 1];
    REQUIRE(last->tpos == 3960 && last->startup_pos == 3824 && v.t[v.nt - 2].tt == 2120);
    struct mem m;
    struct err e;
    mem_init(&m);
    int64_t pos = -1, id = -1;
    int32_t at = -1, index = -1;
    for (int32_t t = v.nt - 2; t < v.nt && at < 0; t++) {
        struct st_record r;
        st_init(&r);
        REQUIRE(st_parse(&r, v.t[t].tpos, v.stream + v.t[t].tpos,
                (int32_t) (v.len - v.t[t].tpos), &m, &e) == ERR_OK);
        for (int32_t j = 0; j < r.nnodes && at < 0; j++) {
            const struct sn_node *sn = &r.nodes[j];
            int64_t time = 0;
            for (int32_t i = 0; sn->type == NODE_KEY && i < sn->n && at < 0; i++) {
                const int64_t klong = sn_klong(sn, i);
                if (kl_get_type(klong) == KL_TYPE_TIME) {
                    time = kl_get_time(klong);
                } else if (kl_get_type(klong) == KL_TYPE_KEY && time <= 2120
                        && sn_ref(sn, i) >= 0) {
                    pos = sn->spos;
                    id = sn->id;
                    index = i;
                    at = 32 + 8 * sn->n + 8 * i;
                }
            }
        }
        st_free(&r, &m);
    }
    CHECK_MEM_ZERO(&m);
    REQUIRE(at > 0);
    char text[200];
    snprintf(text, sizeof text, "Unexpected stream pointer 2001, index %d of key node %lld at "
            "%lld.", (int) index, (long long) id, (long long) pos);
    uint8_t *copy = node_copy(&v, pos, at, 2001);
    for (int check = 1; check >= 0; check--) {
        start_copy(&v, copy, check == 1, text);
    }
    free(copy);
    free(v.stream);
}

/* StoredTrans.testFindNode (bergdb 021-16, Q2): sr_find_node gives the node
 * of an id, the first of two nodes with one id, NULL for an id that no node
 * has, and the nodes of another record once the map is made again; in time
 * linear in the count of nodes, as the start's rerun calls it for each node
 * it makes. It scanned the nodes at each call: 200,000 lookups among
 * 100,001 nodes took seconds. And a scan, up to SR_FIND_NODE_SCAN_LIMIT
 * nodes, and the map above it give the same answers. */
TEST(sdb_find_node) {
    const int32_t n = 100 * 1000;
    struct mem m;
    mem_init(&m);
    struct lmap ids;
    lmap_init(&ids, &m);
    struct err e;
    struct sn_node *nodes = calloc((size_t) n + 1, sizeof *nodes);
    REQUIRE(nodes != NULL);
    for (int32_t i = 0; i < n; i++) {
        nodes[i].type = NODE_VALUE;
        nodes[i].id = 1000 + 2 * (int64_t) i;
    }
    nodes[n].type = NODE_VALUE;
    nodes[n].id = 1000;                     /* the twin */
    struct st_record t;
    st_init(&t);
    t.nodes = nodes;
    t.nnodes = n + 1;
    bool indexed = false;
    const struct sn_node *got;
    struct timespec t0, t1;
    clock_gettime(CLOCK_MONOTONIC, &t0);
    int32_t wrong = 0;
    for (int32_t i = 0; i < n; i++) {
        REQUIRE(sr_find_node(&t, &ids, &indexed, 1000 + 2 * (int64_t) i, &got, &e));
        wrong += got != &nodes[i];
        REQUIRE(sr_find_node(&t, &ids, &indexed, 1001 + 2 * (int64_t) i, &got, &e));
        wrong += got != NULL;
    }
    clock_gettime(CLOCK_MONOTONIC, &t1);
    const int64_t ms = (int64_t) (t1.tv_sec - t0.tv_sec) * 1000
            + (t1.tv_nsec - t0.tv_nsec) / 1000000;
    CHECK_EQ(wrong, 0);
    CHECK(indexed);
    CHECK(ms < 2000);
    if (ms >= 2000) {
        printf("  sdb_find_node: 200,000 lookups took %lld ms\n", (long long) ms);
    }

    /* Another record: its map made again. */
    t.nodes = &nodes[n];
    t.nnodes = 1;
    indexed = false;
    REQUIRE(sr_find_node(&t, &ids, &indexed, 1000, &got, &e));
    CHECK(got == &nodes[n]);
    REQUIRE(sr_find_node(&t, &ids, &indexed, 1002, &got, &e));
    CHECK(got == NULL);

    /* A scan, up to SR_FIND_NODE_SCAN_LIMIT nodes, and a map above it: the
     * same answers. */
    const int32_t sizes[] = { 2, SR_FIND_NODE_SCAN_LIMIT, SR_FIND_NODE_SCAN_LIMIT + 1 };
    struct sn_node few[SR_FIND_NODE_SCAN_LIMIT + 1];
    for (int k = 0; k < 3; k++) {
        const int32_t size = sizes[k];
        memset(few, 0, sizeof few);
        for (int32_t i = 0; i < size - 1; i++) {
            few[i] = nodes[i];
        }
        few[size - 1] = nodes[n];
        t.nodes = few;
        t.nnodes = size;
        indexed = false;
        REQUIRE(sr_find_node(&t, &ids, &indexed, 1000, &got, &e));
        CHECK(got == &few[0]);
        REQUIRE(sr_find_node(&t, &ids, &indexed, 1000 + 2 * (int64_t) (size - 2), &got, &e));
        CHECK(got == &few[size - 2]);
        REQUIRE(sr_find_node(&t, &ids, &indexed, 999, &got, &e));
        CHECK(got == NULL);
        CHECK(indexed == (size > SR_FIND_NODE_SCAN_LIMIT));
    }
    lmap_free(&ids);
    free(nodes);
    CHECK_MEM_ZERO(&m);
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
    TEST_ENTRY(sdb_found_021_11),
    TEST_ENTRY(sdb_found_021_12),
    TEST_ENTRY(sdb_starter_node_texts),
    TEST_ENTRY(sdb_section_pointer_to_a_vpos),
    TEST_ENTRY(sdb_find_node),
    TEST_ENTRY(sdb_allocation_failures),
    TEST_END
};
