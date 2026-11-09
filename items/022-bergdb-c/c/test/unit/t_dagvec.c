/* The Dag against Java's (bergdb 012-08): dag.txt, written by Vectors.java
 * from Java's Dag (Dag.createEmpty, its pointers memory pointers), 12 runs
 * of 80 transactions of random keys that share prefixes and segments:
 * before each transaction Java's dirtyNodeBound, after it PutData's split
 * counts and a hash of the latest state's getMany (each pair's segments,
 * Kvt.time and value length). C makes the same transactions and must give
 * the same numbers. From VECTORS_DIR or the environment's BERGDB_VECTORS. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "dag.h"
#include "getmany.h"
#include "keys.h"
#include "nfix.h"
#include "test.h"
#include "topds.h"

#ifndef VECTORS_DIR
#define VECTORS_DIR "test/unit/vectors"
#endif

static struct node *follow(void *ctx, struct node *predecessor, int32_t index,
        struct opdata *op) {
    (void) ctx;
    struct node *n = node_pointer_node(predecessor, index);
    if (n == NULL) {
        return NULL;
    }
    if (!op->pointer_listener.pointer_followed(op->pointer_listener.ctx, predecessor, index, n,
            PTR_TYPE_MEMORY)) {
        return NULL;
    }
    return n;
}

static uint64_t fnv(uint64_t h, int64_t x) {
    for (int i = 0; i < 8; i++) {
        h ^= (uint64_t) ((x >> (8 * i)) & 0xff);
        h *= UINT64_C(0x100000001b3);
    }
    return h;
}

static bool hash_add(void *ctx, const struct kvt *kvt) {
    uint64_t *h = ctx;
    for (int32_t i = 0; i < kvt->key_n; i++) {
        *h = fnv(*h, kvt->key[i]);
    }
    *h = fnv(*h, kvt->time);
    *h = fnv(*h, kvt->value->len);
    return true;
}

static int hexval(int c) {
    return c <= '9' ? c - '0' : (c | 0x20) - 'a' + 10;
}

struct run {
    struct nfix f;
    struct dag dag;
    struct putdata pd;
    struct getdata gd;
    int64_t t;
    bool open;
};

static void run_end(struct run *r) {
    if (!r->open) {
        return;
    }
    struct obj *roots[1] = { &tds_get_super_root(&r->dag.top_ds)->n.o };
    NFIX_RECOUNT(&r->f, roots, 1);
    dag_free(&r->dag);
    pd_free(&r->pd);
    NFIX_END(&r->f);
    r->open = false;
}

TEST(dagvec_java) {
    char path[600];
    const char *dir = getenv("BERGDB_VECTORS");
    snprintf(path, sizeof path, "%s/dag.txt", dir != NULL ? dir : VECTORS_DIR);
    FILE *fp = fopen(path, "r");
    REQUIRE(fp != NULL);
    struct run r;
    memset(&r, 0, sizeof r);
    char *line = NULL;
    size_t cap = 0;
    int64_t trans = 0;
    int64_t *segs = malloc(4096 * sizeof *segs);
    const int64_t **keys = malloc(64 * sizeof *keys);
    int32_t *kn = malloc(64 * sizeof *kn);
    bool *dels = malloc(64 * sizeof *dels);
    while (getline(&line, &cap, fp) >= 0) {
        if (line[0] == '#') {
            continue;
        }
        if (strncmp(line, "dag ", 4) == 0) {
            run_end(&r);
            int seed, maxNode;
            long long t0;
            REQUIRE(sscanf(line, "dag %d %d %lld", &seed, &maxNode, &t0) == 3);
            nfix_init(&r.f);
            REQUIRE(dag_create_empty(&r.dag, &r.f.cx, t0, maxNode,
                    &OP_DO_NOTHING_POINTER_CREATED_LISTENER));
            dag_new_put_data(&r.dag, &r.pd, &r.f.m);
            r.pd.op.pointer_follower.follow = follow;
            dag_new_get_data(&r.dag, &r.gd);
            r.gd.op.pointer_follower.follow = follow;
            r.t = t0;
            r.open = true;
            continue;
        }
        REQUIRE(strncmp(line, "t ", 2) == 0 && r.open);
        long long tt, bound, ts, ss;
        unsigned long long hash;
        int off;
        REQUIRE(sscanf(line, "t %lld %lld %lld %lld %llx%n", &tt, &bound, &ts, &ss, &hash, &off)
                == 5);
        /* the pairs: BKEYHEX:D */
        int32_t n = 0, used = 0;
        const char *p = line + off;
        while (*p == ' ') {
            p++;
            const char *colon = strchr(p, ':');
            REQUIRE(colon != NULL && n < 64);
            int32_t blen = (int32_t) (colon - p) / 2;
            uint8_t b[256];
            REQUIRE(blen <= 250);
            for (int32_t i = 0; i < blen; i++) {
                b[i] = (uint8_t) (hexval(p[2 * i]) * 16 + hexval(p[2 * i + 1]));
            }
            int32_t ns = keys_segment_count(blen);
            REQUIRE(used + ns <= 4096);
            keys_to_segments(b, blen, segs + used);
            keys[n] = segs + used;
            kn[n] = ns;
            dels[n] = colon[1] == '1';
            used += ns;
            n++;
            p = colon + 2;
        }
        int64_t got;
        CHECK(dag_dirty_node_bound(&r.dag, r.t, keys, kn, dels, n, &r.gd, &r.f.m, &got));
        CHECK_EQ(got, bound);
        r.t = tt;
        r.pd.tt = tt;
        for (int32_t k = 0; k < n; k++) {
            uint8_t v[3] = { (uint8_t) tt, (uint8_t) (tt >> 8), 7 };
            CHECK(dag_put_kv(&r.dag, keys[k], kn[k], dels[k] ? NULL : v, 3, &r.pd));
            pd_clear_fast(&r.pd);
        }
        pd_clear(&r.pd);
        obj_collect(&r.f.cx);
        CHECK_EQ(r.pd.time_split_count, ts);
        CHECK_EQ(r.pd.space_split_count, ss);
        struct getmany g;
        gm_init(&g, &r.dag, &r.f.m);
        g.gd.op.pointer_follower.follow = follow;
        g.actual_lookup_time = tt;
        uint64_t h = UINT64_C(0xcbf29ce484222325);
        g.result.add = hash_add;
        g.result.ctx = &h;
        CHECK(dag_get_many(&r.dag, &g));
        CHECK_EQ((int64_t) h, (int64_t) hash);
        trans++;
    }
    run_end(&r);
    free(line);
    free(segs);
    free(keys);
    free(kn);
    free(dels);
    fclose(fp);
    CHECK_EQ(trans, 12 * 80);
}

const struct test dagvec_tests[] = {
    TEST_ENTRY(dagvec_java),
    TEST_END
};
