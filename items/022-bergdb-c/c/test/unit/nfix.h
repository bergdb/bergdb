/*
 * nfix.h: a fixture for the tests of the index objects (bergdb 012-07): an
 * allocator and an object context; and the checks at a test's end: the
 * recount agrees with the counts, the safe point frees everything that has
 * no holder, and then nothing is live.
 */
#ifndef BERGDB_NFIX_H
#define BERGDB_NFIX_H

#include <string.h>
#include "klong.h"
#include "knode.h"
#include "mem.h"
#include "obj.h"
#include "test.h"
#include "vnode.h"

struct nfix {
    struct mem m;
    struct obj_ctx cx;
};

static inline void nfix_init(struct nfix *f) {
    mem_init(&f->m);
    obj_ctx_init(&f->cx, &f->m);
}

/* The recount from the pending list and the roots given. */
#define NFIX_RECOUNT(f, roots, n) do { \
        int64_t nfix_wrong_ = obj_recount(&(f)->cx, (roots), (n), NULL); \
        CHECK_EQ(nfix_wrong_, 0); \
    } while (0)

/* The end of a test: a recount with no roots, a safe point, and nothing
 * live after it. */
#define NFIX_END(f) do { \
        NFIX_RECOUNT((f), NULL, 0); \
        obj_collect(&(f)->cx); \
        CHECK_EQ((f)->cx.live[OBJ_KEY] + (f)->cx.live[OBJ_TOP] + (f)->cx.live[OBJ_VALUE] \
                + (f)->cx.live[OBJ_HANDLE], 0); \
        CHECK_MEM_ZERO(&(f)->m); \
    } while (0)

/* Java's StringUtil.toBytes(s) as a key klong and as a compare value. */
static inline int64_t nfix_key(const char *s) {
    return kl_create_key((const uint8_t *) s, (int32_t) strlen(s));
}

static inline int64_t nfix_cv(const char *s) {
    return kl_create_compare_value((const uint8_t *) s, (int32_t) strlen(s));
}

/* new ValueNode(new byte[0]) */
static inline struct vnode *nfix_value(struct nfix *f) {
    struct vnode *v = vn_new(&f->cx, NULL, 0, -1);
    return v;
}

#endif
