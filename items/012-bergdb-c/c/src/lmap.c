/* lmap: a map from a long to a long; see lmap.h. */
#include "lmap.h"
#include <assert.h>
#include <string.h>

/* SplitMix64's finalizer: the slot of a key. */
static uint64_t mix(int64_t key) {
    uint64_t z = (uint64_t) key;
    z = (z ^ (z >> 30)) * UINT64_C(0xbf58476d1ce4e5b9);
    z = (z ^ (z >> 27)) * UINT64_C(0x94d049bb133111eb);
    return z ^ (z >> 31);
}

void lmap_init(struct lmap *m, struct mem *mem) {
    memset(m, 0, sizeof *m);
    m->mem = mem;
}

static void free_arrays(struct mem *mem, int64_t *keys, int64_t *vals, uint8_t *used,
        int64_t cap) {
    mem_free(mem, keys, (size_t) cap * sizeof *keys, MEM_TABLE);
    mem_free(mem, vals, (size_t) cap * sizeof *vals, MEM_TABLE);
    mem_free(mem, used, (size_t) cap, MEM_TABLE);
}

void lmap_free(struct lmap *m) {
    if (m->cap > 0) {
        free_arrays(m->mem, m->keys, m->vals, m->used, m->cap);
    }
    m->keys = NULL;
    m->vals = NULL;
    m->used = NULL;
    m->cap = 0;
    m->size = 0;
}

static int64_t slot_of(const struct lmap *m, int64_t key) {
    return (int64_t) (mix(key) & (uint64_t) (m->cap - 1));
}

static bool grow(struct lmap *m) {
    int64_t ncap = m->cap == 0 ? 16 : 2 * m->cap;
    int64_t *keys = mem_alloc(m->mem, (size_t) ncap * sizeof *keys, MEM_TABLE);
    int64_t *vals = mem_alloc(m->mem, (size_t) ncap * sizeof *vals, MEM_TABLE);
    uint8_t *used = mem_zalloc(m->mem, (size_t) ncap, MEM_TABLE);
    if (keys == NULL || vals == NULL || used == NULL) {
        mem_free(m->mem, keys, keys == NULL ? 0 : (size_t) ncap * sizeof *keys, MEM_TABLE);
        mem_free(m->mem, vals, vals == NULL ? 0 : (size_t) ncap * sizeof *vals, MEM_TABLE);
        mem_free(m->mem, used, used == NULL ? 0 : (size_t) ncap, MEM_TABLE);
        return false;
    }
    struct lmap old = *m;
    m->keys = keys;
    m->vals = vals;
    m->used = used;
    m->cap = ncap;
    m->size = 0;
    for (int64_t i = 0; i < old.cap; i++) {
        if (old.used[i]) {
            int64_t j = slot_of(m, old.keys[i]);
            while (m->used[j]) {
                j = (j + 1) & (m->cap - 1);
            }
            m->used[j] = 1;
            m->keys[j] = old.keys[i];
            m->vals[j] = old.vals[i];
            m->size++;
        }
    }
    if (old.cap > 0) {
        free_arrays(m->mem, old.keys, old.vals, old.used, old.cap);
    }
    return true;
}

bool lmap_put(struct lmap *m, int64_t key, int64_t val) {
    if (m->cap > 0) {
        int64_t j = slot_of(m, key);
        while (m->used[j]) {
            if (m->keys[j] == key) {
                m->vals[j] = val;
                return true;
            }
            j = (j + 1) & (m->cap - 1);
        }
    }
    if (2 * (m->size + 1) > m->cap && !grow(m)) {
        return false;
    }
    int64_t j = slot_of(m, key);
    while (m->used[j]) {
        j = (j + 1) & (m->cap - 1);
    }
    m->used[j] = 1;
    m->keys[j] = key;
    m->vals[j] = val;
    m->size++;
    return true;
}

bool lmap_get(const struct lmap *m, int64_t key, int64_t *val) {
    if (m->cap == 0) {
        return false;
    }
    int64_t j = slot_of(m, key);
    while (m->used[j]) {
        if (m->keys[j] == key) {
            *val = m->vals[j];
            return true;
        }
        j = (j + 1) & (m->cap - 1);
    }
    return false;
}

bool lmap_remove(struct lmap *m, int64_t key) {
    if (m->cap == 0) {
        return false;
    }
    int64_t mask = m->cap - 1;
    int64_t j = slot_of(m, key);
    while (m->used[j]) {
        if (m->keys[j] == key) {
            break;
        }
        j = (j + 1) & mask;
    }
    if (!m->used[j]) {
        return false;
    }
    /* Backward shift: the entries after the hole that may move into it. */
    int64_t hole = j;
    int64_t k = (j + 1) & mask;
    while (m->used[k]) {
        int64_t home = slot_of(m, m->keys[k]);
        /* k's entry may fill the hole if its home is not in (hole, k], cyclically. */
        bool between = hole <= k ? (home > hole && home <= k) : (home > hole || home <= k);
        if (!between) {
            m->keys[hole] = m->keys[k];
            m->vals[hole] = m->vals[k];
            hole = k;
        }
        k = (k + 1) & mask;
    }
    m->used[hole] = 0;
    m->size--;
    return true;
}

void lmap_clear(struct lmap *m) {
    if (m->cap > 0) {
        memset(m->used, 0, (size_t) m->cap);
    }
    m->size = 0;
}
