/* trans: a transaction and its builder; see trans.h. */
#include "trans.h"
#include <assert.h>
#include <string.h>
#include "keys.h"
#include "spos.h"

void tr_builder_init(struct tr_builder *b, struct mem *m) {
    memset(b, 0, sizeof *b);
    b->mem = m;
    b->lookup_time = INT64_MAX;
}

static void kv_free(struct tr_kv *kv, struct mem *m) {
    mem_free(m, kv->key, (size_t) kv->key_n * sizeof *kv->key, MEM_CALLER);
    if (kv->value != NULL) {
        mem_free(m, kv->value, (size_t) kv->len, MEM_CALLER);
    }
    kv->key = NULL;
    kv->value = NULL;
}

void tr_builder_free(struct tr_builder *b) {
    for (int32_t i = 0; i < b->nkvs; i++) {
        kv_free(&b->kvs[i], b->mem);
    }
    mem_free(b->mem, b->kvs, (size_t) b->cap * sizeof *b->kvs, MEM_CALLER);
    mem_free(b->mem, b->read_hashes, (size_t) b->read_cap * sizeof *b->read_hashes,
            MEM_CALLER);
    b->kvs = NULL;
    b->read_hashes = NULL;
    b->nkvs = b->cap = b->nread = b->read_cap = 0;
}

static enum err_code nomem(struct err *e) {
    return err_set(e, ERR_NOMEM, "OutOfMemoryError", "out of memory");
}

/* Room for one more pair. */
static bool kvs_room(struct tr_builder *b) {
    if (b->nkvs < b->cap) {
        return true;
    }
    int32_t ncap = b->cap == 0 ? 8 : b->cap * 2;
    struct tr_kv *n = mem_realloc(b->mem, b->kvs, (size_t) b->cap * sizeof *b->kvs,
            (size_t) ncap * sizeof *b->kvs, MEM_CALLER);
    if (n == NULL) {
        return false;
    }
    b->kvs = n;
    b->cap = ncap;
    return true;
}

/* Copies of the key's segments and the value into kv; false on NOMEM
 * (nothing left allocated). */
static bool kv_make(struct tr_kv *kv, struct mem *m, const int64_t *seg, int32_t n,
        const uint8_t *value, int32_t len) {
    memset(kv, 0, sizeof *kv);
    kv->key = mem_alloc(m, (size_t) n * sizeof *kv->key, MEM_CALLER);
    if (kv->key == NULL) {
        return false;
    }
    memcpy(kv->key, seg, (size_t) n * sizeof *seg);
    kv->key_n = n;
    kv->len = value == NULL ? -1 : len;
    if (value != NULL && len > 0) {
        kv->value = mem_alloc(m, (size_t) len, MEM_CALLER);
        if (kv->value == NULL) {
            mem_free(m, kv->key, (size_t) n * sizeof *kv->key, MEM_CALLER);
            kv->key = NULL;
            return false;
        }
        memcpy(kv->value, value, (size_t) len);
    }
    return true;
}

/* The key's segments (Keys.toSegments) into a block of the allocator's;
 * NULL on NOMEM. */
static int64_t *segments_of(struct mem *m, const uint8_t *key, int32_t key_len, int32_t *n) {
    *n = keys_segment_count(key_len);
    int64_t *seg = mem_alloc(m, (size_t) *n * sizeof *seg, MEM_CALLER);
    if (seg != NULL) {
        keys_to_segments(key, key_len, seg);
    }
    return seg;
}

static enum err_code add(struct tr_builder *b, const uint8_t *key, int32_t key_len,
        const uint8_t *value, int32_t value_len, const struct tr_transform *tf, struct err *e) {
    int32_t n;
    if (!kvs_room(b)) {
        return nomem(e);
    }
    int64_t *seg = segments_of(b->mem, key, key_len, &n);
    if (seg == NULL) {
        return nomem(e);
    }
    struct tr_kv *kv = &b->kvs[b->nkvs];
    bool ok = kv_make(kv, b->mem, seg, n, value, value_len);
    mem_free(b->mem, seg, (size_t) n * sizeof *seg, MEM_CALLER);
    if (!ok) {
        return nomem(e);
    }
    if (tf != NULL) {
        kv->has_tf = true;
        kv->tf = *tf;
    }
    b->nkvs++;
    return ERR_OK;
}

enum err_code tr_put(struct tr_builder *b, const uint8_t *key, int32_t key_len,
        const uint8_t *value, int32_t value_len, const struct tr_transform *tf, struct err *e) {
    assert(value != NULL);
    return add(b, key, key_len, value, value_len, tf, e);
}

enum err_code tr_delete(struct tr_builder *b, const uint8_t *key, int32_t key_len,
        struct err *e) {
    return add(b, key, key_len, NULL, -1, NULL, e);
}

enum err_code tr_put_segments(struct tr_builder *b, const int64_t *key, int32_t key_n,
        const uint8_t *value, int32_t value_len, struct err *e) {
    if (!kvs_room(b)) {
        return nomem(e);
    }
    if (!kv_make(&b->kvs[b->nkvs], b->mem, key, key_n, value, value_len)) {
        return nomem(e);
    }
    b->nkvs++;
    return ERR_OK;
}

enum err_code tr_key_read(struct tr_builder *b, const uint8_t *key, int32_t key_len,
        struct err *e) {
    if (b->nread == b->read_cap) {
        int32_t ncap = b->read_cap == 0 ? 8 : b->read_cap * 2;
        int64_t *n = mem_realloc(b->mem, b->read_hashes,
                (size_t) b->read_cap * sizeof *b->read_hashes,
                (size_t) ncap * sizeof *b->read_hashes, MEM_CALLER);
        if (n == NULL) {
            return nomem(e);
        }
        b->read_hashes = n;
        b->read_cap = ncap;
    }
    int32_t n;
    int64_t *seg = segments_of(b->mem, key, key_len, &n);
    if (seg == NULL) {
        return nomem(e);
    }
    b->read_hashes[b->nread++] = keys_hash(seg, n);     /* Builder.keyRead */
    mem_free(b->mem, seg, (size_t) n * sizeof *seg, MEM_CALLER);
    return ERR_OK;
}

enum err_code tr_lookup_time(struct tr_builder *b, int64_t lookupTime, struct err *e) {
    if (lookupTime < 0) {
        return err_set(e, ERR_ARG, "IllegalArgumentException", "lookupTime = %lld",
                (long long) lookupTime);
    }
    b->lookup_time = lookupTime;
    return ERR_OK;
}

void tr_init(struct trans *t, struct mem *m) {
    memset(t, 0, sizeof *t);
    t->mem = m;
    t->startup_pos = SPOS_NULL;
    t->read_time = INT64_MAX;
}

void tr_free(struct trans *t) {
    mem_free(t->mem, t->kvs, (size_t) t->cap * sizeof *t->kvs, MEM_CALLER);
    mem_free(t->mem, t->write_key_hashes, (size_t) t->cap * sizeof *t->write_key_hashes,
            MEM_CALLER);
    t->kvs = NULL;
    t->write_key_hashes = NULL;
    t->cap = 0;
    t->nkvs = 0;
}

static int32_t cmp_kv(const struct tr_kv *a, const struct tr_kv *b) {
    return keys_compare_arrays(a->key, a->key_n, b->key, b->key_n);
}

enum err_code tr_build(struct tr_builder *b, struct trans *t, struct err *e) {
    struct mem *m = b->mem;
    tr_free(t);
    tr_init(t, m);
    t->read_time = b->lookup_time;
    t->read_key_hashes = b->read_hashes;
    t->nread = b->nread;
    const int32_t n = b->nkvs;
    if (n == 0) {
        return ERR_OK;
    }

    /* The TreeMap's order: a stable merge sort of the pairs by key, bottom
     * up (no recursion), so that the pairs of one key stay in the order
     * given; then each key's last pair, but a delete never replaces a put. */
    struct tr_kv **a = mem_alloc(m, (size_t) n * sizeof *a, MEM_CALLER);
    struct tr_kv **tmp = mem_alloc(m, (size_t) n * sizeof *tmp, MEM_CALLER);
    int64_t *hashes = mem_alloc(m, (size_t) n * sizeof *hashes, MEM_CALLER);
    if (a == NULL || tmp == NULL || hashes == NULL) {
        mem_free(m, a, (size_t) n * sizeof *a, MEM_CALLER);
        mem_free(m, tmp, (size_t) n * sizeof *tmp, MEM_CALLER);
        mem_free(m, hashes, (size_t) n * sizeof *hashes, MEM_CALLER);
        return nomem(e);
    }
    for (int32_t i = 0; i < n; i++) {
        a[i] = &b->kvs[i];
    }
    for (int32_t width = 1; width < n; width *= 2) {
        for (int32_t lo = 0; lo < n; lo += 2 * width) {
            int32_t mid = lo + width < n ? lo + width : n;
            int32_t hi = lo + 2 * width < n ? lo + 2 * width : n;
            int32_t i = lo, j = mid, k = lo;
            while (i < mid && j < hi) {
                tmp[k++] = cmp_kv(a[j], a[i]) < 0 ? a[j++] : a[i++];
            }
            while (i < mid) {
                tmp[k++] = a[i++];
            }
            while (j < hi) {
                tmp[k++] = a[j++];
            }
        }
        struct tr_kv **swap = a;
        a = tmp;
        tmp = swap;
    }
    int32_t count = 0;
    for (int32_t i = 0; i < n; ) {
        struct tr_kv *cur = NULL;
        int32_t j = i;
        for (; j < n && cmp_kv(a[i], a[j]) == 0; j++) {
            /* Kv prev = map.put(kv.getKey(), kv); "Non-deletes take precedence over
             * deletes": a delete after a put puts the put back. */
            struct tr_kv *prev = cur;
            cur = a[j];
            if (cur->len < 0 && prev != NULL && prev->len >= 0) {
                cur = prev;
            }
        }
        tmp[count++] = cur;
        i = j;
    }
    mem_free(m, a, (size_t) n * sizeof *a, MEM_CALLER);
    t->kvs = tmp;           /* n slots, count used */
    t->nkvs = count;
    t->cap = n;
    /* computeWriteHashes: Keys.hash of each pair's key. */
    for (int32_t i = 0; i < count; i++) {
        hashes[i] = keys_hash(t->kvs[i]->key, t->kvs[i]->key_n);
    }
    t->write_key_hashes = hashes;
    return ERR_OK;
}

enum err_code tr_kv_set_key(struct tr_kv *kv, struct mem *m, const uint8_t *key, int32_t len,
        struct err *e) {
    int32_t n;
    int64_t *seg = segments_of(m, key, len, &n);
    if (seg == NULL) {
        return nomem(e);
    }
    mem_free(m, kv->key, (size_t) kv->key_n * sizeof *kv->key, MEM_CALLER);
    kv->key = seg;
    kv->key_n = n;
    return ERR_OK;
}

enum err_code tr_kv_set_value(struct tr_kv *kv, struct mem *m, const uint8_t *value,
        int32_t len, struct err *e) {
    uint8_t *v = NULL;
    if (value != NULL && len > 0) {
        v = mem_alloc(m, (size_t) len, MEM_CALLER);
        if (v == NULL) {
            return nomem(e);
        }
        memcpy(v, value, (size_t) len);
    }
    if (kv->value != NULL) {
        mem_free(m, kv->value, (size_t) kv->len, MEM_CALLER);
    }
    kv->value = v;
    kv->len = value == NULL ? -1 : len;
    return ERR_OK;
}
