/*
 * lmap: a map from a long to a long, Java's HashMap<Long, Long> where its
 * iteration order does not matter (bergdb 012-10): DbStarter's newById and
 * posToId, NodeCollection's section, and the node table (ntable.h), whose
 * values are handles. Open addressing with linear probing, removal by
 * backward shift, at most half full. Prefix lmap_.
 *
 * No iteration order of Java's is reproduced: the startup iterates
 * HashMaps only where each entry is handled alone (012-01, 3.2, point 3;
 * 012-02, 10.2), and C iterates its own maps in slot order. Memory through
 * the allocator (MEM_TABLE). One caller at a time.
 */
#ifndef BERGDB_LMAP_H
#define BERGDB_LMAP_H

#include <stdbool.h>
#include <stdint.h>
#include "mem.h"

struct lmap {
    struct mem *mem;
    int64_t *keys;
    int64_t *vals;
    uint8_t *used;
    int64_t cap;            /* 0 or a power of 2 */
    int64_t size;
};

/* An empty map; nothing allocated until the first put. */
void lmap_init(struct lmap *m, struct mem *mem);

/* Frees the arrays; the map is empty again. */
void lmap_free(struct lmap *m);

/* put(key, val): the key's value becomes val. false: NOMEM, the map as it
 * was. */
bool lmap_put(struct lmap *m, int64_t key, int64_t val);

/* get(key): true and *val if the key is in the map. */
bool lmap_get(const struct lmap *m, int64_t key, int64_t *val);

/* remove(key): true if it was in the map. */
bool lmap_remove(struct lmap *m, int64_t key);

/* Clears every entry; the arrays stay. */
void lmap_clear(struct lmap *m);

/* The slots, for iteration: for (i = 0; i < m->cap; i++) if (m->used[i])
 * m->keys[i], m->vals[i]. A put or a remove during an iteration may move
 * entries. */

#endif
