/*
 * Java's records (bergdb 012-06): test/unit/vectors/records.txt, written by
 * Vectors.java from a small stream that Db wrote (node size 8, startup
 * distance 100): the stream, its committed records, what StoredTrans.parse
 * gives for each (at its own position, and at a position 40 bytes before a
 * meta block, so that its nodes and value offsets cross the block), and
 * records with one change that Java's parser refuses, with the exception.
 * C's parsers (strans, snode), C's walk (nstream), the node reads and the
 * recovery plan must agree. The lines are long (the stream), so this file
 * has a reader of its own; the directory is that of t_vectors.c.
 */
#include <errno.h>
#include <stdbool.h>
#include <stdlib.h>
#include "test.h"
#include "bytes.h"
#include "checksum.h"
#include "nstream.h"
#include "rstream.h"
#include "snode.h"
#include "spos.h"
#include "stream.h"
#include "strans.h"

#ifndef VECTORS_DIR
#define VECTORS_DIR "test/unit/vectors"
#endif

#define R_LINE (1 << 17)
#define R_TOK 16
#define R_RECORDS 64
#define R_POOL (1 << 17)

/* The file's records, in a static pool (one test at a time). */
static struct {
    char line[R_LINE];
    char *tok[R_TOK];
    int ntok;
    uint8_t stream[R_POOL / 2];
    int32_t stream_len;
    uint8_t pool[R_POOL];
    int32_t pool_used;
    int64_t tpos[R_RECORDS];
    uint8_t *bytes[R_RECORDS];
    int32_t len[R_RECORDS];
    int nrecords;
    uint8_t work[R_POOL / 4];
} rv;

static int hex_digit(char c) {
    if (c >= '0' && c <= '9') return c - '0';
    if (c >= 'a' && c <= 'f') return c - 'a' + 10;
    return -1;
}

/* Hex into out; "-" is none. The number of bytes, or -1. */
static int32_t unhex(const char *s, uint8_t *out, int32_t max) {
    if (strcmp(s, "-") == 0) {
        return 0;
    }
    int32_t n = (int32_t) strlen(s);
    if (n % 2 != 0 || n / 2 > max) {
        return -1;
    }
    for (int32_t i = 0; i < n / 2; i++) {
        int a = hex_digit(s[2 * i]), b = hex_digit(s[2 * i + 1]);
        if (a < 0 || b < 0) return -1;
        out[i] = (uint8_t) (a * 16 + b);
    }
    return n / 2;
}

/* A list of longs, hex (16 digits each) or decimal, comma-separated; "-" is none. */
static int32_t longs(const char *s, bool hex, int64_t *out, int32_t max) {
    int32_t n = 0;
    if (strcmp(s, "-") == 0) {
        return 0;
    }
    while (*s != '\0' && n < max) {
        char *end;
        out[n++] = hex ? (int64_t) strtoull(s, &end, 16) : (int64_t) strtoll(s, &end, 10);
        s = *end == ',' ? end + 1 : end;
    }
    return n;
}

static int64_t num(const char *s) {
    return (int64_t) strtoll(s, NULL, 10);
}

static int find(int64_t tpos) {
    for (int i = 0; i < rv.nrecords; i++) {
        if (rv.tpos[i] == tpos) return i;
    }
    return -1;
}

/* Reads the file's lines into rv: the stream and the records. */
static bool load(FILE *f) {
    rv.nrecords = 0;
    rv.pool_used = 0;
    rv.stream_len = 0;
    while (fgets(rv.line, sizeof rv.line, f) != NULL) {
        char *nl = strchr(rv.line, '\n');
        if (nl != NULL) *nl = '\0';
        if (strncmp(rv.line, "stream ", 7) == 0) {
            rv.stream_len = unhex(rv.line + 7, rv.stream, (int32_t) sizeof rv.stream);
            if (rv.stream_len < 0) return false;
        } else if (strncmp(rv.line, "record ", 7) == 0) {
            char *sp = strchr(rv.line + 7, ' ');
            if (sp == NULL || rv.nrecords == R_RECORDS) return false;
            *sp = '\0';
            rv.tpos[rv.nrecords] = num(rv.line + 7);
            rv.bytes[rv.nrecords] = rv.pool + rv.pool_used;
            int32_t n = unhex(sp + 1, rv.pool + rv.pool_used, R_POOL - rv.pool_used);
            if (n < 0) return false;
            rv.len[rv.nrecords++] = n;
            rv.pool_used += n;
        }
    }
    return rv.stream_len > 0 && rv.nrecords > 0;
}

static FILE *open_vectors(void) {
    char path[1024];
    const char *dir = getenv("BERGDB_VECTORS");
    snprintf(path, sizeof path, "%s/records.txt", dir != NULL ? dir : VECTORS_DIR);
    FILE *f = fopen(path, "r");
    if (f == NULL) {
        printf("cannot open %s: %s\n", path, strerror(errno));
    }
    return f;
}

static void split(void) {
    rv.ntok = 0;
    for (char *t = strtok(rv.line, " "); t != NULL && rv.ntok < R_TOK; t = strtok(NULL, " ")) {
        rv.tok[rv.ntok++] = t;
    }
}

/* Every line: the records parsed at both positions, their nodes, and the refusals. */
TEST(records_parse) {
    struct mem m;
    struct err e;
    struct st_record r;
    int64_t ls[64], ls2[64];
    long counts[4] = { 0, 0, 0, 0 };
    mem_init(&m);
    err_clear(&e);
    st_init(&r);
    FILE *f = open_vectors();
    REQUIRE(f != NULL);
    REQUIRE(load(f));
    rewind(f);
    int64_t cur_tpos = -1, cur_at = -1;
    bool cur_ok = false;
    while (fgets(rv.line, sizeof rv.line, f) != NULL) {
        char *nl = strchr(rv.line, '\n');
        if (nl != NULL) *nl = '\0';
        if (rv.line[0] == '#' || strncmp(rv.line, "stream ", 7) == 0
                || strncmp(rv.line, "record ", 7) == 0) {
            continue;
        }
        char copy[400];
        snprintf(copy, sizeof copy, "%s", rv.line);
        long before = test_failed_checks_;
        split();
        const char *kind = rv.tok[0];
        if (strcmp(kind, "trans") == 0 && rv.ntok == 9) {
            int k = find(num(rv.tok[1]));
            REQUIRE(k >= 0);
            cur_tpos = num(rv.tok[1]);
            cur_at = num(rv.tok[2]);
            cur_ok = st_parse(&r, cur_at, rv.bytes[k], rv.len[k], &m, &e) == ERR_OK;
            CHECK(cur_ok);
            if (cur_ok) {
                CHECK_EQ(r.tt, num(rv.tok[3]));
                CHECK_EQ(r.startup_pos, num(rv.tok[4]));
                CHECK_EQ(r.top_pos, num(rv.tok[5]));
                CHECK_EQ(r.last_pos, num(rv.tok[6]));
                CHECK_EQ(r.nnodes, num(rv.tok[7]));
                int32_t nd = longs(rv.tok[8], true, ls, 64);
                CHECK_EQ(nd, 2 * r.got_dirty_count);
                for (int32_t i = 0; i < nd / 2 && i < r.got_dirty_count; i++) {
                    CHECK_EQ(st_got_dirty_id(&r, i), ls[2 * i]);
                    CHECK_EQ(st_got_dirty_pos(&r, i), ls[2 * i + 1]);
                }
            }
            counts[0]++;
        } else if (strcmp(kind, "node") == 0 && rv.ntok >= 9) {
            REQUIRE(cur_ok && cur_tpos == num(rv.tok[1]) && cur_at == num(rv.tok[2]));
            int32_t i = (int32_t) num(rv.tok[3]);
            REQUIRE(i >= 0 && i < r.nnodes);
            const struct sn_node *n = &r.nodes[i];
            int32_t type = (int32_t) num(rv.tok[4]);
            CHECK_EQ(n->type, type);
            CHECK_EQ(n->spos, num(rv.tok[5]));
            CHECK_EQ(n->id, num(rv.tok[6]));
            if (type == NODE_TOP && rv.ntok == 12) {
                CHECK_EQ(n->ordinal, num(rv.tok[7]));
                CHECK_EQ(n->root_time, num(rv.tok[8]));
                CHECK_EQ(n->root, num(rv.tok[9]));
                int32_t np = longs(rv.tok[10], false, ls, 64);
                int32_t nt = longs(rv.tok[11], false, ls2, 64);
                CHECK_EQ(np, n->h);
                CHECK_EQ(nt, n->h);
                for (int32_t j = 0; j < n->h && j < np && j < nt; j++) {
                    CHECK_EQ(sn_skip_pos(n, j), ls[j]);
                    CHECK_EQ(sn_skip_time(n, j), ls2[j]);
                }
            } else if (type == NODE_KEY && rv.ntok == 12) {
                CHECK_EQ(n->prev_pos, num(rv.tok[7]));
                CHECK_EQ(n->leaf ? 1 : 0, num(rv.tok[8]));
                CHECK_EQ(n->n, num(rv.tok[9]));
                int32_t nk = longs(rv.tok[10], true, ls, 64);
                int32_t nr = longs(rv.tok[11], false, ls2, 64);
                CHECK_EQ(nk, n->n);
                CHECK_EQ(nr, n->n);
                for (int32_t j = 0; j < n->n && j < nk && j < nr; j++) {
                    CHECK_EQ(sn_klong(n, j), ls[j]);
                    CHECK_EQ(sn_ref(n, j), ls2[j]);
                }
            } else if ((type == NODE_VALUE || type == NODE_DELETE) && rv.ntok == 11) {
                uint8_t value[256];
                CHECK_EQ(n->tpos, num(rv.tok[7]));
                CHECK_EQ(n->offset_from_trans, num(rv.tok[8]));
                if (strcmp(rv.tok[9], "-") == 0 && type == NODE_DELETE) {
                    CHECK(n->value == NULL);
                    CHECK_EQ(n->value_len, -1);
                } else {
                    int32_t vl = unhex(rv.tok[9], value, (int32_t) sizeof value);
                    CHECK_EQ(n->value_len, vl);
                    if (vl == n->value_len && vl > 0) {
                        CHECK_BYTES(n->value, value, (size_t) vl);
                    }
                }
                int32_t nk = longs(rv.tok[10], true, ls, 64);
                CHECK_EQ(n->key_n, nk);
                for (int32_t j = 0; j < nk && j < n->key_n; j++) {
                    CHECK_EQ(sn_seg(n, j), ls[j]);
                }
            } else {
                CHECK(false);
            }
            counts[1]++;
        } else if (strcmp(kind, "refuse") == 0 && rv.ntok == 6) {
            int k = find(num(rv.tok[1]));
            REQUIRE(k >= 0);
            int32_t off = (int32_t) num(rv.tok[2]);
            int32_t fix = (int32_t) num(rv.tok[4]);
            uint8_t change[16];
            int32_t nc = unhex(rv.tok[3], change, 16);
            REQUIRE(nc > 0 && off + nc <= rv.len[k]);
            memcpy(rv.work, rv.bytes[k], (size_t) rv.len[k]);
            memcpy(rv.work + off, change, (size_t) nc);
            if (fix >= 0) {
                int32_t size = bytes_get_int_le(rv.work + fix);
                if (fix + size <= rv.len[k]) {
                    int32_t sum = cks_sum_with_zero_replace(rv.work, fix, size, fix + 6);
                    rv.work[fix + 6] = (uint8_t) sum;
                    rv.work[fix + 7] = (uint8_t) (sum >> 8);
                }
            }
            err_clear(&e);
            enum err_code rc = st_parse(&r, rv.tpos[k], rv.work, rv.len[k], &m, &e);
            cur_ok = false;
            if (strcmp(rv.tok[5], "taken") == 0) {
                CHECK_EQ(rc, ERR_OK);
            } else {
                CHECK(rc != ERR_OK);
                CHECK(strcmp(e.java, rv.tok[5]) == 0);
            }
            counts[2]++;
        } else {
            CHECK(false);
        }
        if (test_failed_checks_ != before) {
            printf("    records.txt: %s\n", copy);
            if (strcmp(kind, "refuse") == 0) {
                printf("    C: %s %s: %s\n", err_code_name(e.code), e.java, e.text);
            }
        }
    }
    fclose(f);
    CHECK(counts[0] > 0 && counts[1] > 0 && counts[2] > 0);
    st_free(&r, &m);
    CHECK_MEM_ZERO(&m);
}

/* Builds the vector stream in a memory stream. */
static void stream_of_vectors(struct stream *s, struct mem *m) {
    struct err e;
    stream_open_memory(s, m);
    stream_append_memory(s, rv.stream, rv.stream_len, &e);
}

/* The walk finds the committed records, in order, with their bytes; each node of each
 * record reads by its position as it parses in its record; the plan of recovery fills
 * nothing. */
TEST(records_walk_and_reads) {
    struct mem m;
    struct err e;
    struct stream s;
    struct ns_iter it;
    struct ns_buf nb = { NULL, 0 };
    struct st_record r;
    bool has;
    mem_init(&m);
    st_init(&r);
    FILE *f = open_vectors();
    REQUIRE(f != NULL);
    REQUIRE(load(f));
    fclose(f);
    stream_of_vectors(&s, &m);

    ns_iter_init(&it, &s, &m, 0, false);
    int k = 0;
    while (ns_iter_next(&it, &has, &e) == ERR_OK && has) {
        REQUIRE(k < rv.nrecords);
        CHECK_EQ(it.tpos, rv.tpos[k]);
        CHECK_EQ(it.size, rv.len[k]);
        CHECK(it.size == rv.len[k] && memcmp(it.buf.p, rv.bytes[k], (size_t) it.size) == 0);
        CHECK_EQ(it.trans_count, k + 1);
        k++;
    }
    CHECK(e.code == ERR_OK || !has);
    CHECK_EQ(k, rv.nrecords);
    ns_iter_free(&it);

    /* From an exact position: the second record. */
    ns_iter_init(&it, &s, &m, rv.tpos[1], true);
    CHECK(ns_iter_next(&it, &has, &e) == ERR_OK && has);
    CHECK_EQ(it.tpos, rv.tpos[1]);
    ns_iter_free(&it);

    for (int i = 0; i < rv.nrecords; i++) {
        REQUIRE(st_parse(&r, rv.tpos[i], rv.bytes[i], rv.len[i], &m, &e) == ERR_OK);
        for (int32_t j = 0; j < r.nnodes; j++) {
            struct sn_node n;
            int32_t type;
            int64_t id;
            const struct sn_node *x = &r.nodes[j];
            REQUIRE(ns_read_node(&s, &m, x->spos, &nb, &n, &e) == ERR_OK);
            CHECK_EQ(n.type, x->type);
            CHECK_EQ(n.spos, x->spos);
            CHECK_EQ(n.id, x->id);
            CHECK_EQ(n.size, x->size);
            CHECK(memcmp(n.bytes, x->bytes, (size_t) x->size) == 0);
            CHECK(ns_read_node_header(&s, x->spos, &type, &id, &e) == ERR_OK);
            CHECK_EQ(type, x->type);
            CHECK_EQ(id, x->id);
        }
        int32_t size;
        CHECK(ns_read_trans_bytes(&s, &m, rv.tpos[i], &nb, &size, &e) == ERR_OK);
        CHECK_EQ(size, rv.len[i]);
    }

    /* The last valid meta block names the creation's record (the stream is below
     * 200,000), and recovery has nothing to fill. */
    struct rs_recovery plan;
    REQUIRE(rs_plan_recovery(&s, &plan, &e) == ERR_OK);
    CHECK_EQ(plan.last_valid.pos, 0);
    CHECK_EQ(plan.meta_fill, 0);
    CHECK_EQ(plan.torn, SPOS_NULL);
    CHECK_EQ(plan.zero_fill, 0);
    CHECK_EQ(plan.last_whole, rv.tpos[rv.nrecords - 1]);
    CHECK_EQ(plan.length_after, s.length);
    int64_t p;
    CHECK(rs_pos_of_trans_completed_before(&s, s.length, &p, &e) == ERR_OK);
    CHECK_EQ(p, 128);
    bool incomplete;
    CHECK(rs_is_incomplete_creation(&s, 264, &incomplete, &e) == ERR_OK && !incomplete);

    /* Cut in the middle of each record: recovery fills the rest of it. */
    for (int i = 1; i < rv.nrecords; i++) {
        int64_t cut = rv.tpos[i] + rv.len[i] / 2;
        stream_truncate_memory(&s, cut, &e);
        REQUIRE(rs_plan_recovery(&s, &plan, &e) == ERR_OK);
        CHECK_EQ(plan.torn, rv.tpos[i]);
        CHECK_EQ(plan.torn_have, rv.len[i] / 2);
        CHECK_EQ(plan.torn_size, rv.len[i]);
        CHECK_EQ(plan.zero_fill, rv.len[i] - rv.len[i] / 2);
        CHECK_EQ(plan.last_whole, rv.tpos[i - 1]);
        CHECK_EQ(plan.length_after, rv.tpos[i] + rv.len[i]);
        stream_close(&s);
        stream_of_vectors(&s, &m);
    }

    ns_buf_free(&nb, &m);
    st_free(&r, &m);
    stream_close(&s);
    CHECK_MEM_ZERO(&m);
}

/* NodeStream.readNode: a position in the first meta block is refused with a
 * StreamFormatException (bergdb 019-32, as Java's since release 2026.3: a pointer of a
 * damaged node reaches it); before, Java's assert, which C returned as an AssertionError. */
TEST(records_bad_node_position) {
    struct mem m;
    struct err e;
    struct stream s;
    struct ns_buf nb = { NULL, 0 };
    struct sn_node n;
    mem_init(&m);
    FILE *f = open_vectors();
    REQUIRE(f != NULL);
    REQUIRE(load(f));
    fclose(f);
    stream_of_vectors(&s, &m);
    const int64_t bad[3] = { 0, 8, 127 };
    for (int i = 0; i < 3; i++) {
        CHECK_EQ(ns_read_node(&s, &m, bad[i], &nb, &n, &e), ERR_FORMAT);
        CHECK(strcmp(e.java, "StreamFormatException") == 0);
        char want[60];
        snprintf(want, sizeof want, "Bad node position, %lld.", (long long) bad[i]);
        CHECK(strcmp(e.text, want) == 0);
    }
    CHECK_EQ(ns_read_node(&s, &m, 160, &nb, &n, &e), ERR_OK);     /* the creation's top node */
    CHECK_EQ(n.type, NODE_TOP);
    ns_buf_free(&nb, &m);
    stream_close(&s);
    CHECK_MEM_ZERO(&m);
}

/* 012-06's finding F2: a node size below 0, which Java's parser took until 005-74 (its
 * offset went back, and this record made it loop until it ran out of memory), is refused,
 * as Java's parser refuses it since release 2026.2. The record of the finding's probe. */
TEST(records_negative_node_size) {
    struct mem m;
    struct err e;
    struct st_record r;
    uint8_t b[112];
    mem_init(&m);
    st_init(&r);
    memset(b, 0, sizeof b);
    bytes_put_int_le(112, b);
    b[4] = 5;
    bytes_put_long_le(1, b + 8);
    bytes_put_int_le(32, b + 32);
    b[36] = 40;
    b[37] = 4;
    bytes_put_long_le(129, b + 40);
    bytes_put_int_le(32, b + 48);
    bytes_put_int_le(8, b + 52);
    bytes_put_long_le(INT64_C(0x0058c00000000010), b + 56);
    int32_t sum = cks_sum_with_zero_replace(b, 32, 32, 38);
    b[38] = (uint8_t) sum;
    b[39] = (uint8_t) (sum >> 8);
    bytes_put_int_le(-32, b + 64);
    b[68] = 40;
    b[69] = 4;
    bytes_put_long_le(131, b + 72);
    bytes_put_int_le(64, b + 80);
    bytes_put_int_le(8, b + 84);
    bytes_put_long_le(INT64_C(0x0058c00000000010), b + 88);
    b[111] = 10;
    CHECK_EQ(st_parse(&r, 128, b, 112, &m, &e), ERR_FORMAT);
    CHECK(strcmp(e.java, "StreamFormatException") == 0);    /* as Java's since 005-74 */
    CHECK(strncmp(e.text, "Bad node size, -32,", 19) == 0);
    bytes_put_int_le(0, b + 64);            /* the end of the nodes there, and no got-dirty */
    bytes_put_int_le(0, b + 68);            /* pairs: taken, at the size of its content */
    CHECK_EQ(st_parse(&r, 128, b, 112, &m, &e), ERR_FORMAT);       /* 015-72: 80, not 112 */
    bytes_put_int_le(80, b);
    b[79] = 10;
    CHECK_EQ(st_parse(&r, 128, b, 112, &m, &e), ERR_OK);
    CHECK_EQ(r.nnodes, 1);
    CHECK_EQ(r.last_pos, 128 + 32 + 32 + 4 + 4 + 8 * 0 + 1 + 7 - 1);
    st_free(&r, &m);
    CHECK_MEM_ZERO(&m);
}

/* A record whose size field is larger than its content is refused (bergdb 015-72, as
 * Java's since release 2026.3; DbTesterRestart.testEnlargedRecordSizeRefused at the parser):
 * each record of the vectors followed by the next, its size made theirs together, so that
 * it ends on the next one's last byte. Before, it was taken, and the walk skipped the
 * record it covered. A size of 8 bytes more than the content is refused too. */
TEST(records_enlarged_size) {
    struct mem m;
    struct err e;
    struct st_record r;
    mem_init(&m);
    st_init(&r);
    FILE *f = open_vectors();
    REQUIRE(f != NULL);
    REQUIRE(load(f));
    fclose(f);
    int tried = 0;
    for (int k = 0; k + 1 < rv.nrecords; k++) {
        if (rv.tpos[k] + rv.len[k] != rv.tpos[k + 1]) {
            continue;
        }
        const int32_t a = rv.len[k], n = rv.len[k] + rv.len[k + 1];
        REQUIRE(n <= (int32_t) sizeof rv.work);
        memcpy(rv.work, rv.bytes[k], (size_t) a);
        memcpy(rv.work + a, rv.bytes[k + 1], (size_t) rv.len[k + 1]);
        CHECK_EQ(st_parse(&r, rv.tpos[k], rv.work, n, &m, &e), ERR_OK);
        bytes_put_int_le(n, rv.work);
        err_clear(&e);
        CHECK_EQ(st_parse(&r, rv.tpos[k], rv.work, n, &m, &e), ERR_FORMAT);
        CHECK(strcmp(e.java, "StreamFormatException") == 0);
        char want[200];
        snprintf(want, sizeof want, "The record at %lld ends at offset %d by its content, and "
                "its size says %d.", (long long) rv.tpos[k], (int) a, (int) n);
        CHECK(strcmp(e.text, want) == 0);
        bytes_put_int_le(a + 8, rv.work);
        err_clear(&e);
        CHECK_EQ(st_parse(&r, rv.tpos[k], rv.work, n, &m, &e), ERR_FORMAT);
        CHECK(strncmp(e.text, "The record at ", 14) == 0);
        tried++;
    }
    CHECK(tried > 5);
    st_free(&r, &m);
    CHECK_MEM_ZERO(&m);
}

const struct test records_tests[] = {
    TEST_ENTRY(records_parse),
    TEST_ENTRY(records_walk_and_reads),
    TEST_ENTRY(records_negative_node_size),
    TEST_ENTRY(records_enlarged_size),
    TEST_ENTRY(records_bad_node_position),
    TEST_END
};
