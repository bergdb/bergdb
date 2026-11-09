/* Java's KeyNode against C's, operation by operation (bergdb 012-07):
 * test/unit/vectors/knode.txt, written by Vectors.java, has runs of
 * KeyNode's operations as the Dag makes them (addKlong of values and key
 * nodes, deletes, replaceKlong, lastVersion, setContentFrom, toPreviousState,
 * firstAndSecond with inserts), each with the size and the FNV-1a hash of
 * the node's stored bytes after it in Java. C replays them and compares
 * after every operation; so the klongs, their order, the TIME klongs, the
 * split points and the references are Java's. The directory is VECTORS_DIR,
 * or the environment's BERGDB_VECTORS. */
#include <inttypes.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "bytes.h"
#include "klong.h"
#include "knode.h"
#include "nfix.h"
#include "nwrite.h"
#include "spos.h"
#include "test.h"
#include "vnode.h"

#ifndef VECTORS_DIR
#define VECTORS_DIR "test/unit/vectors"
#endif

/* The node's stored bytes (StoredKeyNode.toLongs with prevPos 0) into
 * out, at most 32 + 16 * 126 bytes; returns their number. */
static int32_t stored(const struct knode *node, uint8_t *out) {
    int64_t longs[(32 + 16 * 126) / 8];
    int32_t n = nw_key_to_longs(node, longs, 0, 0);
    bytes_longs_to_le(longs, n, out);
    return n * 8;
}

static uint64_t fnv(const uint8_t *b, int32_t n) {
    uint64_t h = UINT64_C(0xcbf29ce484222325);
    for (int32_t i = 0; i < n; i++) {
        h ^= b[i];
        h *= UINT64_C(0x100000001b3);
    }
    return h;
}

/* Checks "SIZE HASH" at *p against node; advances *p. */
static bool check_state(const struct knode *node, char **p, const char *line) {
    char *end;
    long size = strtol(*p, &end, 10);
    uint64_t hash = strtoull(end, &end, 16);
    *p = end;
    uint8_t b[32 + 16 * 126];
    int32_t n = stored(node, b);
    if (size != node->size || hash != fnv(b, n)) {
        printf("    knode.txt: %s    C: size %d hash %016" PRIx64 "\n", line, node->size,
                fnv(b, n));
        return false;
    }
    return true;
}

static int64_t num(char **p) {
    return strtoll(*p, p, 10);
}

static int64_t hex(char **p) {
    return (int64_t) strtoull(*p, p, 16);
}

static struct vnode *value_at(struct nfix *f, int64_t s) {
    struct vnode *v = vn_new(&f->cx, NULL, 0, s);
    if (v != NULL) {
        v->n.id = s;
    }
    return v;
}

TEST(knodevec_java) {
    char path[1024];
    const char *dir = getenv("BERGDB_VECTORS");
    snprintf(path, sizeof path, "%s/knode.txt", dir != NULL ? dir : VECTORS_DIR);
    FILE *in = fopen(path, "r");
    REQUIRE(in != NULL);

    static char line[16384];
    struct nfix f;
    bool running = false;
    bool leaf = true;
    struct knode *node = NULL;
    int64_t ops = 0, runs = 0, ends = 0;
    bool failed = false;

    while (!failed && fgets(line, sizeof line, in) != NULL) {
        char *p = line;
        if (line[0] == '#' || line[0] == '\n') {
            continue;
        }
        if (strncmp(line, "run ", 4) == 0) {
            if (running) {
                NFIX_END(&f);
            }
            nfix_init(&f);
            running = true;
            runs++;
            p += 4;
            num(&p);
            leaf = num(&p) == 1;
            node = kn_new(&f.cx, leaf);
            REQUIRE(node != NULL);
            node->n.id = 0;
            node->n.spos = 0;
            continue;
        }
        REQUIRE(running);
        if (strncmp(line, "end ", 4) == 0) {
            uint8_t b[32 + 16 * 126];
            int32_t n = stored(node, b);
            char hexs[2 * sizeof b + 1];
            for (int32_t i = 0; i < n; i++) {
                snprintf(hexs + 2 * i, 3, "%02x", b[i]);
            }
            size_t len = strcspn(line + 4, "\n");
            CHECK(len == (size_t) (2 * n) && memcmp(line + 4, hexs, len) == 0);
            ends++;
            continue;
        }
        char op = line[0];
        p += 2;
        int64_t t = num(&p);
        ops++;
        bool ok = true;
        switch (op) {
        case 'a': {             /* addKlong(T, K, a value node at S) */
            int64_t k = hex(&p);
            int64_t s = num(&p);
            struct vnode *v = value_at(&f, s);
            ok = v != NULL && kn_add_klong(&f.cx, node, t, k, &v->n, ACCESS_DATA_DEFAULT);
            break;
        }
        case 'c': {             /* addKlong(T, K, a key node at S) */
            int64_t k = hex(&p);
            int64_t s = num(&p);
            struct knode *c = kn_new(&f.cx, true);
            ok = c != NULL;
            if (ok) {
                c->n.id = s + 1;
                c->n.spos = s;
                ok = kn_add_klong(&f.cx, node, t, k, &c->n, ACCESS_DATA_DEFAULT);
            }
            break;
        }
        case 'd': {             /* getDeleteBitmap(CV), addDeleteKlong */
            int64_t cv = hex(&p);
            int64_t expected = hex(&p);
            int64_t del = kn_get_delete_bitmap(node, cv);
            CHECK_EQ(del, expected);
            if (del != 0) {
                ok = kn_add_delete_klong(&f.cx, node, t, del);
            }
            break;
        }
        case 'r': {             /* replaceKlong */
            int64_t k = hex(&p);
            int64_t s = num(&p);
            int64_t expected = num(&p);
            struct vnode *v = value_at(&f, s);
            bool replaced = false;
            ok = v != NULL && kn_replace_klong(&f.cx, node, t, k, &v->n, ACCESS_DATA_DEFAULT,
                    &replaced);
            CHECK_EQ(replaced ? 1 : 0, expected);
            break;
        }
        case 'l': {             /* the node becomes lastVersion(T) */
            struct knode *last = kn_last_version(&f.cx, node, t);
            ok = last != NULL;
            if (ok) {
                node = last;
                node->n.id = 0;
                node->n.spos = 0;
            }
            break;
        }
        case 'x': {             /* setContentFrom(lastVersion(T)) */
            struct knode *last = kn_last_version(&f.cx, node, t);
            ok = last != NULL && kn_set_content_from(&f.cx, node, last);
            break;
        }
        case 'p':               /* toPreviousState(T) */
            kn_to_previous_state(&f.cx, node, t);
            break;
        case 's': {             /* firstAndSecond */
            int64_t which = num(&p);
            int32_t n = (int32_t) num(&p);
            struct kwp insert[4];
            REQUIRE(n <= 4);
            for (int32_t i = 0; i < n; i++) {
                kwp_init(&insert[i]);
                insert[i].klong = hex(&p);
                struct vnode *v = value_at(&f, num(&p));
                REQUIRE(v != NULL);
                insert[i].node = &v->n;
            }
            struct knode *last = kn_last_version(&f.cx, node, t);
            struct knode *first = kn_new(&f.cx, leaf);
            struct knode *second = kn_new(&f.cx, leaf);
            REQUIRE(last != NULL && first != NULL && second != NULL);
            int64_t secondKlong = 0;
            ok = kn_first_and_second(&f.cx, node, t, last, insert, n, first, second,
                    &secondKlong);
            struct knode *other = which == 0 ? second : first;
            node = which == 0 ? first : second;
            node->n.id = other->n.id = 0;
            node->n.spos = other->n.spos = 0;
            while (*p == ' ') p++;
            if (*p == '=') p++;
            if (!check_state(node, &p, line)) {
                failed = true;
            }
            CHECK_EQ(hex(&p), secondKlong);
            if (!check_state(other, &p, line)) {
                failed = true;
            }
            CHECK(ok);
            continue;
        }
        default:
            printf("    knode.txt: an unknown line: %s", line);
            CHECK(false);
            failed = true;
            continue;
        }
        CHECK(ok);
        CHECK(kn_check(node, NULL) == NULL);
        NFIX_RECOUNT(&f, NULL, 0);      /* after each change (012-01, 4.5) */
        while (*p == ' ') p++;
        if (*p == '=') p++;
        if (!check_state(node, &p, line)) {
            failed = true;
        }
    }
    fclose(in);
    if (running) {
        NFIX_END(&f);
    }
    CHECK(!failed);
    CHECK(runs >= 10);
    CHECK(ops >= 400);
    CHECK_EQ(ends, 4);
}

const struct test knodevec_tests[] = {
    TEST_ENTRY(knodevec_java),
    TEST_END
};
