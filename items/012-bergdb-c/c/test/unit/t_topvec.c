/* Java's TopDs against C's (bergdb 012-07): test/unit/vectors/top.txt,
 * written by Vectors.java, has chains of top nodes made by
 * TopDs.newSuperRoot as the Dag makes them (a second new root at the same
 * time changes the super root's root pointer; the second ordinal set), the
 * ids given by the node change listener as Db gives them, the super root
 * written now and then; after each new root the super root's ordinal and
 * the size and FNV-1a hash of its stored bytes, and findRoot at times. C
 * replays them and compares. */
#include <assert.h>
#include <inttypes.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "bytes.h"
#include "knode.h"
#include "nfix.h"
#include "nwrite.h"
#include "opdata.h"
#include "test.h"
#include "tnode.h"
#include "topds.h"

#ifndef VECTORS_DIR
#define VECTORS_DIR "test/unit/vectors"
#endif

/* The listener of the chain: each new top node gets the next id, as Db's
 * setIdOfNode and registerNewNode (canonical). */
static bool next_id(void *ctx, struct tnode *node) {
    int64_t *nextId = ctx;
    node->n.id = *nextId;
    node->n.spos = *nextId;
    node_set_canonical(&node->n, true);
    *nextId += 2;
    return true;
}

static struct node *follow(void *ctx, struct node *predecessor, int32_t index,
        struct opdata *op) {
    (void) ctx, (void) op;
    struct node *n = node_pointer_node(predecessor, index);
    assert(n != NULL && "not in memory");
    return n;
}

static uint64_t top_hash(const struct tnode *t, int32_t *size) {
    int64_t longs[(40 + 16 * 48) / 8];
    uint8_t b[40 + 16 * 48];
    int32_t n = nw_top_to_longs(t, longs, 0);
    bytes_longs_to_le(longs, n, b);
    *size = 8 * n;
    uint64_t h = UINT64_C(0xcbf29ce484222325);
    for (int32_t i = 0; i < 8 * n; i++) {
        h ^= b[i];
        h *= UINT64_C(0x100000001b3);
    }
    return h;
}

static struct knode *root_at(struct nfix *f, int64_t pos) {
    struct knode *root = kn_new(&f->cx, true);
    if (root != NULL) {
        root->n.spos = pos;
        root->n.id = pos + 1;
        node_set_canonical(&root->n, true);
    }
    return root;
}

TEST(topvec_java) {
    char path[1024];
    const char *dir = getenv("BERGDB_VECTORS");
    snprintf(path, sizeof path, "%s/top.txt", dir != NULL ? dir : VECTORS_DIR);
    FILE *in = fopen(path, "r");
    REQUIRE(in != NULL);

    static char line[4096];
    struct nfix f;
    struct topds ds;
    bool running = false;
    int64_t nextId = 1;
    struct op_node_change_listener ids = OP_DO_NOTHING_NODE_CHANGE_LISTENER;
    ids.top_node_created = next_id;
    ids.ctx = &nextId;
    int64_t chains = 0, news = 0, finds = 0;

    while (fgets(line, sizeof line, in) != NULL) {
        char *p = line;
        if (line[0] == '#' || line[0] == '\n') {
            continue;
        }
        if (strncmp(line, "chain ", 6) == 0) {
            if (running) {
                tds_free(&f.cx, &ds);
                NFIX_END(&f);
            }
            nfix_init(&f);
            running = true;
            chains++;
            p += 6;
            strtoll(p, &p, 10);
            int64_t t0 = strtoll(p, &p, 10);
            int64_t r0 = strtoll(p, &p, 10);
            int64_t second = strtoll(p, &p, 10);
            REQUIRE(tds_create_from_first_root(&f.cx, &ds, t0, root_at(&f, r0), 0,
                    &OP_DO_NOTHING_POINTER_CREATED_LISTENER));
            nextId = 1;
            ds.super_root->n.id = nextId;
            ds.super_root->n.spos = nextId;
            node_set_canonical(&ds.super_root->n, true);
            nextId += 2;
            CHECK(tds_set_second_ordinal(&ds, second));
            continue;
        }
        REQUIRE(running);
        char op = line[0];
        p += 2;
        int64_t a = strtoll(p, &p, 10);
        if (op == 'n') {
            int64_t r = strtoll(p, &p, 10);
            CHECK(tds_new_super_root(&f.cx, &ds, a, root_at(&f, r), 0,
                    &OP_DO_NOTHING_POINTER_CREATED_LISTENER, &ids));
            while (*p == ' ' || *p == '=') p++;
            int64_t ord = strtoll(p, &p, 10);
            int64_t size = strtoll(p, &p, 10);
            uint64_t hash = strtoull(p, &p, 16);
            int32_t csize;
            uint64_t chash = top_hash(ds.super_root, &csize);
            CHECK_EQ(ds.super_root->top_node_id, ord);
            CHECK_EQ(csize, size);
            if (chash != hash) {
                printf("    top.txt: %s    C: %016" PRIx64 "\n", line, chash);
                CHECK(false);
            }
            news++;
        } else if (op == 'w') {
            ds.super_root->n.spos = a;
        } else if (op == 'f') {
            while (*p == ' ' || *p == '=') p++;
            int64_t expected = strtoll(p, &p, 10);
            struct opdata gd;
            op_init(&gd);
            gd.pointer_follower.follow = follow;
            gd.pointer_listener = OP_DO_NOTHING_POINTER_LISTENER;
            struct knode *found = NULL;
            CHECK(tds_find_root(&ds, a, &gd, &found));
            CHECK_EQ(found == NULL ? -1 : found->n.spos, expected);
            finds++;
        } else {
            printf("    top.txt: an unknown line: %s", line);
            CHECK(false);
        }
        obj_collect(&f.cx);     /* a safe point: what the super root holds stays */
    }
    fclose(in);
    if (running) {
        struct obj *root = &ds.super_root->n.o;
        NFIX_RECOUNT(&f, &root, 1);
        tds_free(&f.cx, &ds);
        NFIX_END(&f);
    }
    CHECK_EQ(chains, 8);
    CHECK(news > 100);
    CHECK(finds > 30);
}

const struct test topvec_tests[] = {
    TEST_ENTRY(topvec_java),
    TEST_END
};
