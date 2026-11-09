/* The round trip of every node (bergdb 012-07, done item 5): each node of
 * Java's records, parsed by 012-06's parsers (strans, snode), made into an
 * object as Java's parse makes it (kn_new_stored, tn_new_stored,
 * vn_new_stored) and written again by the writers (nwrite), gives its bytes.
 * The records: those of test/unit/vectors/records.txt (012-06's, from a
 * stream that Db wrote); and, when the environment's BERGDB_STREAMS names
 * a file, every committed record of each database directory listed in it,
 * one a line (012-05's streams: the cross sets' databases). */
#include <errno.h>
#include <stdlib.h>
#include <string.h>
#include "bytes.h"
#include "err.h"
#include "knode.h"
#include "nfix.h"
#include "nstream.h"
#include "nwrite.h"
#include "snode.h"
#include "spos.h"
#include "stream.h"
#include "strans.h"
#include "test.h"
#include "tnode.h"
#include "vnode.h"

#ifndef VECTORS_DIR
#define VECTORS_DIR "test/unit/vectors"
#endif

struct rt_counts {
    int64_t records;
    int64_t top, key, value, del;
    int64_t failed;
    int64_t cut_ends;           /* walks that ended at a cut stream's end */
};

/* One node at offset off of its record's bytes rec: made and written
 * again; true if the bytes are the node's. scratch: at least as long as
 * the record. */
static bool round_trip(struct obj_ctx *cx, const uint8_t *rec, const struct sn_node *sn,
        uint8_t *scratch, struct rt_counts *c) {
    int32_t off = (int32_t) (sn->bytes - rec);
    int32_t n = 0;
    switch (sn->type) {
    case NODE_TOP: {
        struct tnode *t = tn_new_stored(cx, sn->ordinal, sn->root, sn->root_time, sn->spos,
                sn->id, sn->h, sn->bytes + 40);
        if (t == NULL) {
            return false;
        }
        int64_t longs[(40 + 16 * 48) / 8];
        int32_t count = nw_top_to_longs(t, longs, 0);
        bytes_longs_to_le(longs, count, scratch + off);
        n = 8 * count;
        c->top++;
        break;
    }
    case NODE_KEY: {
        struct knode *k = kn_new_stored(cx, sn->leaf, sn->spos, sn->id, sn->n, sn->bytes + 32,
                sn->bytes + 32 + 8 * (size_t) sn->n);
        if (k == NULL) {
            return false;
        }
        size_t bytes = (size_t) nw_key_byte_size(k);
        int64_t *longs = mem_alloc(cx->mem, bytes, MEM_BUFFER);
        if (longs == NULL) {
            return false;
        }
        int32_t count = nw_key_to_longs(k, longs, 0, sn->prev_pos);
        bytes_longs_to_le(longs, count, scratch + off);
        mem_free(cx->mem, longs, bytes, MEM_BUFFER);
        n = 8 * count;
        c->key++;
        break;
    }
    case NODE_VALUE:
    case NODE_DELETE: {
        struct vnode *v = vn_new_stored(cx, sn->value, sn->value_len, sn->spos, sn->id, sn->tpos);
        if (v == NULL) {
            return false;
        }
        int64_t key[64];
        if (sn->key_n > 64) {
            return false;
        }
        for (int32_t i = 0; i < sn->key_n; i++) {
            key[i] = sn_seg(sn, i);
        }
        n = nw_value_to_bytes(v, key, sn->key_n, scratch, off);
        if (sn->type == NODE_VALUE) c->value++; else c->del++;
        break;
    }
    default:
        return false;
    }
    obj_collect(cx);
    return n == sn->size && memcmp(scratch + off, sn->bytes, (size_t) n) == 0;
}

/* Every node of the record at tpos, rec[0] to rec[len - 1]. */
static void round_trip_record(struct obj_ctx *cx, struct st_record *r, int64_t tpos,
        const uint8_t *rec, int32_t len, uint8_t *scratch, struct rt_counts *c,
        const char *where) {
    struct err e;
    if (st_parse(r, tpos, rec, len, cx->mem, &e) != ERR_OK) {
        printf("    %s: record at %lld not parsed: %s\n", where, (long long) tpos, e.text);
        c->failed++;
        return;
    }
    c->records++;
    for (int32_t i = 0; i < r->nnodes; i++) {
        if (!round_trip(cx, rec, &r->nodes[i], scratch, c)) {
            if (c->failed < 5) {
                printf("    %s: the node at %lld (type %d) of the record at %lld is not its bytes"
                        " again\n", where, (long long) r->nodes[i].spos, r->nodes[i].type,
                        (long long) tpos);
            }
            c->failed++;
        }
    }
}

static int hexd(char ch) {
    return ch >= 'a' ? ch - 'a' + 10 : ch - '0';
}

TEST(roundtrip_java_records) {
    char path[1024];
    const char *dir = getenv("BERGDB_VECTORS");
    snprintf(path, sizeof path, "%s/records.txt", dir != NULL ? dir : VECTORS_DIR);
    FILE *in = fopen(path, "r");
    REQUIRE(in != NULL);
    static char line[1 << 17];
    static uint8_t rec[1 << 16], scratch[1 << 16];
    struct nfix f;
    nfix_init(&f);
    struct st_record r;
    st_init(&r);
    struct rt_counts c;
    memset(&c, 0, sizeof c);
    while (fgets(line, sizeof line, in) != NULL) {
        if (strncmp(line, "record ", 7) != 0) {
            continue;
        }
        char *p = line + 7;
        int64_t tpos = strtoll(p, &p, 10);
        p++;
        int32_t len = 0;
        while (p[0] != '\n' && p[0] != '\0' && len < (int32_t) sizeof rec) {
            rec[len++] = (uint8_t) (hexd(p[0]) * 16 + hexd(p[1]));
            p += 2;
        }
        round_trip_record(&f.cx, &r, tpos, rec, len, scratch, &c, "records.txt");
    }
    fclose(in);
    st_free(&r, &f.m);
    CHECK_EQ(c.failed, 0);
    CHECK(c.records >= 10);
    CHECK(c.top > 0 && c.key > 0 && c.value > 0);
    NFIX_END(&f);
}

/* The streams of BERGDB_STREAMS, a file of database directories. */
TEST(roundtrip_streams) {
    const char *list = getenv("BERGDB_STREAMS");
    if (list == NULL) {
        return;                 /* only when asked: the gate's quick set has no list */
    }
    FILE *in = fopen(list, "r");
    REQUIRE(in != NULL);
    char dirname[2048];
    struct rt_counts c;
    memset(&c, 0, sizeof c);
    int64_t dirs = 0;
    while (fgets(dirname, sizeof dirname, in) != NULL) {
        dirname[strcspn(dirname, "\n")] = '\0';
        if (dirname[0] == '\0') {
            continue;
        }
        struct nfix f;
        nfix_init(&f);
        struct stream s;
        struct err e;
        if (stream_open_dir(&s, dirname, &f.m, &e) != ERR_OK) {
            printf("    %s: not opened: %s\n", dirname, e.text);
            c.failed++;
            continue;
        }
        dirs++;
        struct ns_iter it;
        ns_iter_init(&it, &s, &f.m, stream_first_pos(&s), false);
        struct st_record r;
        st_init(&r);
        struct ns_buf scratch = {NULL, 0};
        bool has = true;
        while (has) {
            enum err_code code = ns_iter_next(&it, &has, &e);
            if (code == ERR_IO) {
                /* A crash variant's cut stream, not recovered: its walk ends at
                 * the cut with a read past the end, as Java's iterator does. */
                c.cut_ends++;
                break;
            }
            if (code != ERR_OK) {
                printf("    %s: the walk stopped: %s\n", dirname, e.text);
                c.failed++;
                break;
            }
            if (!has) {
                break;
            }
            if (scratch.cap < it.size) {
                mem_free(&f.m, scratch.p, (size_t) scratch.cap, MEM_BUFFER);
                scratch.p = mem_alloc(&f.m, (size_t) it.size, MEM_BUFFER);
                scratch.cap = it.size;
                REQUIRE(scratch.p != NULL);
            }
            round_trip_record(&f.cx, &r, it.tpos, it.buf.p, it.size, scratch.p, &c, dirname);
        }
        mem_free(&f.m, scratch.p, (size_t) scratch.cap, MEM_BUFFER);
        st_free(&r, &f.m);
        ns_iter_free(&it);
        stream_close(&s);
        NFIX_END(&f);
    }
    fclose(in);
    printf("    roundtrip_streams: %lld directories (%lld of them cut, their walks ended at the"
            " cut), %lld records, %lld top, %lld key, %lld value and %lld delete nodes, each its"
            " bytes again; %lld failed\n", (long long) dirs, (long long) c.cut_ends,
            (long long) c.records, (long long) c.top, (long long) c.key, (long long) c.value,
            (long long) c.del, (long long) c.failed);
    CHECK_EQ(c.failed, 0);
    CHECK(dirs > 0);
}

const struct test roundtrip_tests[] = {
    TEST_ENTRY(roundtrip_java_records),
    TEST_ENTRY(roundtrip_streams),
    TEST_END
};
