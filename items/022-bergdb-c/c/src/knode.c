/* knode: ported from Java's bergdb.dag.KeyNode, method by method; see
 * knode.h. Java's names are kept, and each function names its method. */
#include "knode.h"
#include <assert.h>
#include <inttypes.h>
#include <stdio.h>
#include <string.h>
#include "bytes.h"
#include "handle.h"
#include "klong.h"
#include "spos.h"

/* KeyNode.ARRAY_SIZES: the possible lengths of the arrays. */
static const int32_t ARRAY_SIZES[] = {2, 8-2, 16-2, 32-2, 64-2, 128-2};
#define ARRAY_SIZES_LENGTH ((int32_t) (sizeof ARRAY_SIZES / sizeof ARRAY_SIZES[0]))

/* The bytes of a block of cap slots: a klong, a reference and a pointee. */
static size_t block_bytes(int32_t cap) {
    return (size_t) cap * (2 * sizeof(int64_t) + sizeof(struct obj *));
}

/* Points klongs, pos and pointers into block (cap slots). */
static void set_arrays(struct knode *k, int64_t *block, int32_t cap) {
    k->cap = cap;
    k->klongs = block;
    k->pos = block == NULL ? NULL : block + cap;
    k->pointers = block == NULL ? NULL : (struct obj **) (void *) (block + 2 * (size_t) cap);
}

/* A zeroed block of cap slots; NULL: NOMEM (cap > 0). */
static int64_t *new_block(struct obj_ctx *cx, int32_t cap) {
    return mem_zalloc(cx->mem, block_bytes(cap), MEM_INDEX);
}

static void free_block(struct obj_ctx *cx, struct knode *k) {
    if (k->klongs != NULL) {
        mem_free(cx->mem, k->klongs, block_bytes(k->cap), MEM_INDEX);
    }
    set_arrays(k, NULL, 0);
}

/* KeyNode(isSegmentLeaf) */
struct knode *kn_new(struct obj_ctx *cx, bool is_segment_leaf) {
    struct knode *k = obj_alloc(cx, sizeof(struct knode), OBJ_KEY);
    if (k == NULL) {
        return NULL;
    }
    if (is_segment_leaf) {
        k->n.o.flags |= OBJ_LEAF;
    }
    set_arrays(k, NULL, 0);     /* EMPTY_LONG_ARRAY, EMPTY_INODE_ARRAY */
    k->n.spos = SPOS_NULL;
    k->n.id = SPOS_NULL;
    k->size = 0;
    k->last_time_index = -1;
    k->handle = NULL;
    return k;
}

/* KeyNode.nodeWithTime */
struct knode *kn_new_with_time(struct obj_ctx *cx, int64_t time) {
    struct knode *node = kn_new(cx, true);
    if (node == NULL || !kn_add_to_end(cx, node, kl_create_time(time), NULL, SPOS_NULL)) {
        return NULL;            /* pending: freed at the next safe point */
    }
    node->last_time_index = 0;
    assert(node->size == 1);
    return node;
}

/* StoredKeyNode.parse, from "new KeyNode(isSegmentLeaf)" on. */
struct knode *kn_new_stored(struct obj_ctx *cx, bool is_segment_leaf, int64_t spos, int64_t id,
        int32_t n, const uint8_t *klongs_le, const uint8_t *refs_le) {
    struct knode *keyNode = kn_new(cx, is_segment_leaf);
    if (keyNode == NULL) {
        return NULL;
    }
    keyNode->n.spos = spos;
    keyNode->n.id = id;
    for (int32_t i = 0; i < n; i++) {
        if (!kn_add_to_end(cx, keyNode, bytes_get_long_le(klongs_le + 8 * (size_t) i), NULL,
                bytes_get_long_le(refs_le + 8 * (size_t) i))) {
            return NULL;
        }
    }
    return keyNode;
}

bool kn_is_segment_leaf(const struct knode *k) {
    return (k->n.o.flags & OBJ_LEAF) != 0;
}

/* KeyNode.getKlong */
int64_t kn_get_klong(const struct knode *k, int32_t index) {
    assert(index >= 0 && index < k->cap);
    return k->klongs[index];
}

/* KeyNode.getSize */
int32_t kn_get_size(const struct knode *k) {
    return k->size;
}

/* KeyNode.getSizeAtTime */
int32_t kn_get_size_at_time(const struct knode *k, int64_t lookupTime) {
    const int32_t sz = k->size;
    const int64_t *klongs = k->klongs;
    int64_t klong;
    int32_t result = sz;

    for (int32_t index = 0; index < sz; index++) {
        klong = klongs[index];
        if (kl_is_time(klong)) {
            int64_t klongTime = kl_get_time(klong);
            if (klongTime > lookupTime) {
                result = index;
                break;
            }
        }
    }

    return result;
}

/* KeyNode.getPointer */
void kn_get_pointer(const struct knode *k, int32_t index, struct pointer *pointer) {
    pointer->node = kn_get_pointer_node(k, index);
    pointer->pos = k->pos[index];
    pointer->index = index;
}

/* KeyNode.getPointerNode: the value, or the handle's object if it may
 * serve. */
struct node *kn_get_pointer_node(const struct knode *k, int32_t index) {
    assert(index >= 0 && index < k->cap);
    struct obj *p = k->pointers[index];
    if (p == NULL) {
        return NULL;
    }
    if (p->kind == OBJ_VALUE) {
        return (struct node *) p;
    }
    struct node *o = ((struct handle *) p)->obj;
    return o != NULL && hd_usable(o, k->pos[index]) ? o : NULL;
}

/* KeyNode.getPointerPos */
int64_t kn_get_pointer_pos(const struct knode *k, int32_t index) {
    return k->pos[index];
}

/* KeyNode.getPointee, getPointeeAcquire */
struct obj *kn_get_pointee(const struct knode *k, int32_t index) {
    return k->pointers[index];
}

/* Pointer index holds pointee, counted: the new retained, then the old
 * released. Only below size (asserted), where a slot is counted. */
static void hold(struct obj_ctx *cx, struct knode *k, int32_t index, struct obj *pointee) {
    obj_set(cx, &k->pointers[index], pointee);
}

/* KeyNode.setPointee */
void kn_set_pointee(struct obj_ctx *cx, struct knode *k, int32_t index, struct obj *pointee) {
    assert(index >= 0 && index < k->size);
    hold(cx, k, index, pointee);
}

/* KeyNode.setRef */
void kn_set_ref(struct knode *k, int32_t index, int64_t ref) {
    k->pos[index] = ref;
}

/* KeyNode.raiseRef */
void kn_raise_ref(struct knode *k, int32_t index, int64_t ref) {
    if (spos_newer(ref, k->pos[index])) {
        k->pos[index] = ref;
    }
}

/* KeyNode.swizzle */
bool kn_swizzle(struct obj_ctx *cx, struct knode *k, int32_t index, struct obj *expected,
        struct obj *pointee) {
    if (k->pointers[index] != expected) {
        return false;
    }
    kn_set_pointee(cx, k, index, pointee);
    return true;
}

/* KeyNode.setPointer */
void kn_set_pointer(struct obj_ctx *cx, struct knode *k, int32_t index, struct obj *pointee,
        int64_t ref) {
    k->pos[index] = ref;
    kn_set_pointee(cx, k, index, pointee);
}

/* KeyNode.getSerializedRef */
int64_t kn_get_serialized_ref(const struct knode *k, int32_t index) {
    return hd_serialized_ref(k->pointers[index], k->pos[index]);
}

/* Klong.DELETE_BITS[index], as Java's searches inline it. */
static int64_t delete_bits(int32_t index) {
    return kl_delete_bit(index);
}

/* KeyNode.searchEq */
void kn_search_eq(const struct knode *k, int64_t time, int64_t compareValue, struct kwp *kwi) {
    int32_t sz;
    const int64_t *klongs;
    int32_t index = 0;
    int64_t klong;
    int64_t arrayTime = -1;
    int32_t klongType;
    int64_t deleteBitmap = KL_DELETE_NONE_BITMAP;

    sz = k->size;
    klongs = k->klongs;
    kwi->klong = KL_NULL;

    for (index = 0; index < sz; index++) {
        if ((deleteBitmap & delete_bits(index)) != 0) {
            continue;
        }

        klong = klongs[index];
        klongType = j_l2i(j_ushr64(klong & J64(0xc000000000000000), 62));

        if (klongType == KL_INT_TYPE_TIME) {
            arrayTime = klong & INT64_C(0x00ffffffffffffff);
            if (arrayTime > time) {
                break;          /* At time 'time', the rest of the array did not exist. */
            }
        } else if (klongType == KL_INT_TYPE_KEY) {
            if (compareValue == (klong & INT64_C(0x3ffffffffffffff8))) {
                kwi->klong = klong;
                kwi->pointer_index = index;
                kwi->klong_time = arrayTime;
                kwi->node = kn_get_pointer_node(k, index);
                kwi->pos = k->pos[index];
            }
        } else if (klongType == KL_INT_TYPE_DELETE_BITMAP) {
            deleteBitmap = klong;
            if (kwi->klong != KL_NULL && (deleteBitmap & delete_bits(kwi->pointer_index)) != 0) {
                kwi->klong = KL_NULL;
            }
        } else {
            assert(0 && "Bad klong type");
        }
    }
}

/* The search of searchLte, searchLt, searchGt, searchGte and searchFirst
 * (Java has five copies of one loop, which differ in the test of a key
 * klong's compare value only; the test is the argument). */
enum search_kind { LTE, LT, GT, GTE, FIRST };

static void search(const struct knode *k, int64_t time, int64_t compareValue, struct kwp *kwi,
        enum search_kind kind) {
    int32_t sz;
    const int64_t *klongs;
    int64_t klong;
    int64_t arrayTime = -1;
    int32_t klongType;
    int64_t bestCompareValue = -1;      /* Best compare value in the matching process so far. */
    int64_t bestKlongTime = -1;
    int32_t bestPointerIndex = -1;
    int64_t arrayCompareValue;
    int64_t del = KL_DELETE_NONE_BITMAP;

    sz = k->size;
    klongs = k->klongs;
    kwi->klong = KL_NULL;

    del = kn_get_delete_bitmap_at_time(k, time, sz);

    for (int32_t i = 0; i < sz; i++) {
        if ((del & delete_bits(i)) != 0) {
            continue;
        }

        klong = klongs[i];
        klongType = j_l2i(j_ushr64(klong & J64(0xc000000000000000), 62));

        if (klongType == KL_INT_TYPE_TIME) {
            arrayTime = klong & INT64_C(0x00ffffffffffffff);
            if (arrayTime > time) {
                break;
            }
        } else if (klongType == KL_INT_TYPE_KEY) {
            arrayCompareValue = klong & INT64_C(0x3ffffffffffffff8);
            bool better = false;
            switch (kind) {
            case LTE:
                better = arrayCompareValue >= bestCompareValue && arrayCompareValue <= compareValue;
                break;
            case LT:
                better = arrayCompareValue >= bestCompareValue && arrayCompareValue < compareValue;
                break;
            case GT:
                better = (arrayCompareValue <= bestCompareValue || bestCompareValue == -1)
                        && arrayCompareValue > compareValue;
                break;
            case GTE:
                better = (arrayCompareValue <= bestCompareValue || bestCompareValue == -1)
                        && arrayCompareValue >= compareValue;
                break;
            case FIRST:
                better = arrayCompareValue < bestCompareValue || bestCompareValue == -1;
                break;
            }
            if (better) {
                bestCompareValue = arrayCompareValue;
                bestPointerIndex = i;
                bestKlongTime = arrayTime;
            }
        } else if (klongType == KL_INT_TYPE_DELETE_BITMAP) {
            /* Empty */
        } else {
            assert(0 && "Bad klong type");
        }
    }

    if (bestCompareValue != -1) {
        kwi->klong = klongs[bestPointerIndex];
        kwi->pointer_index = bestPointerIndex;
        kwi->klong_time = bestKlongTime;
        kwi->pos = k->pos[bestPointerIndex];
        kwi->node = kn_get_pointer_node(k, bestPointerIndex);
    }
}

/* KeyNode.searchLte */
void kn_search_lte(const struct knode *k, int64_t time, int64_t compareValue, struct kwp *kwi) {
    search(k, time, compareValue, kwi, LTE);
}

/* KeyNode.searchLt */
void kn_search_lt(const struct knode *k, int64_t time, int64_t compareValue, struct kwp *kwi) {
    search(k, time, compareValue, kwi, LT);
}

/* KeyNode.searchGt */
void kn_search_gt(const struct knode *k, int64_t time, int64_t compareValue, struct kwp *kwi) {
    search(k, time, compareValue, kwi, GT);
}

/* KeyNode.searchGte */
void kn_search_gte(const struct knode *k, int64_t time, int64_t compareValue, struct kwp *kwi) {
    search(k, time, compareValue, kwi, GTE);
}

/* KeyNode.searchFirst */
void kn_search_first(const struct knode *k, int64_t time, struct kwp *kwi) {
    search(k, time, -1, kwi, FIRST);
}

/* KeyNode.ensureCapacity and growCapacity: the arrays at least neededSize
 * long, at the next of ARRAY_SIZES, else neededSize + 10. */
static bool ensure_capacity(struct obj_ctx *cx, struct knode *k, int32_t neededSize) {
    if (neededSize <= k->cap) {
        return true;
    }
    int32_t sz = k->size;
    assert(sz <= k->cap);

    int32_t newSize = -1;
    for (int32_t i = 0; i < ARRAY_SIZES_LENGTH; i++) {
        int32_t arraySize = ARRAY_SIZES[i];
        if (arraySize >= neededSize) {
            newSize = arraySize;
            break;
        }
    }
    if (newSize == -1) {
        newSize = neededSize + 10;
    }

    int64_t *block = new_block(cx, newSize);
    if (block == NULL) {
        return false;
    }
    int64_t *klongs = block;
    int64_t *pos = block + newSize;
    struct obj **pointers = (struct obj **) (void *) (block + 2 * (size_t) newSize);
    if (sz > 0) {
        memcpy(klongs, k->klongs, (size_t) sz * sizeof *klongs);
        memcpy(pointers, k->pointers, (size_t) sz * sizeof *pointers);   /* moved: counts kept */
        memcpy(pos, k->pos, (size_t) sz * sizeof *pos);
    }
    free_block(cx, k);
    set_arrays(k, block, newSize);
    return true;
}

/* KeyNode.addDeleteKlong */
bool kn_add_delete_klong(struct obj_ctx *cx, struct knode *k, int64_t time, int64_t klong) {
    assert(kl_get_type(klong) == KL_TYPE_DELETE_BITMAP);
    return kn_add_klong(cx, k, time, klong, NULL, SPOS_NULL);
}

/* KeyNode.addKlong */
bool kn_add_klong(struct obj_ctx *cx, struct knode *k, int64_t time, int64_t klong,
        struct node *pointerNode, int64_t accessDataOrSpos) {
    /* A pointer to a node holds its handle, or the value; its reference is
     * the node's position, its vpos if not written (bergdb item 009, step
     * 3a). Without a node, a stream pointer: accessDataOrSpos is its
     * position. */
    struct obj *pointer;
    if (!hd_pointee_of(cx, pointerNode, &pointer)) {
        return false;
    }
    const int64_t ref = pointerNode != NULL ? pointerNode->spos : accessDataOrSpos;
    int16_t sz = k->size;

    assert(k->last_time_index == -1 || time >= k->klongs[k->last_time_index]);
    assert(kl_get_type(klong) != KL_TYPE_TIME && "Time klongs not supported.");

    int32_t addCount = 1;
    if (k->last_time_index == -1 || time > kl_get_time(k->klongs[k->last_time_index])) {
        addCount = 2;
    }

    if (!ensure_capacity(cx, k, sz + addCount)) {
        return false;
    }
    assert(k->cap >= sz + addCount);

    int16_t newSize = sz;

    if (addCount == 2) {
        /* Adds a time klong. */
        k->klongs[newSize] = kl_create_time(time);
        assert(k->pointers[newSize] == NULL);
        k->pos[newSize] = SPOS_NULL;        /* Important that pos == NULL here, no pointer. */
        k->last_time_index = newSize;
        newSize++;
    }

    assert(k->cap > newSize);

    k->klongs[newSize] = klong;
    assert(k->pointers[newSize] == NULL);
    obj_retain(pointer);
    k->pointers[newSize] = pointer;
    k->pos[newSize] = ref;
    newSize++;

    k->size = newSize;
    return true;
}

/* KeyNode.replaceKlong */
bool kn_replace_klong(struct obj_ctx *cx, struct knode *k, int64_t time, int64_t klong1,
        struct node *pointerNode, int64_t accessData, bool *replaced) {
    struct obj *pointer;
    if (!hd_pointee_of(cx, pointerNode, &pointer)) {
        return false;
    }
    const int64_t ref = pointerNode != NULL ? pointerNode->spos : accessData;
    const int32_t sz = k->size;
    const int64_t *klongs = k->klongs;
    int64_t arrayTime = -1;
    bool result = false;

    for (int32_t index = 0; index < sz; index++) {
        int64_t klong = klongs[index];
        int32_t klongType = kl_get_int_type(klong);

        if (klongType == KL_INT_TYPE_TIME) {
            arrayTime = kl_get_time(klong);
        } else if (klongType == KL_INT_TYPE_KEY) {
            if (klong1 == klong && time == arrayTime) {
                k->klongs[index] = klong1;
                hold(cx, k, index, pointer);
                k->pos[index] = ref;
                result = true;
                break;
            }
        } else {
            /* Java: IllegalStateException, "This method is cannot be used for
             * KeyNode with delete klongs." or "unexpected klong type". */
            assert(0 && "replaceKlong: a delete klong");
        }
    }
    *replaced = result;
    return true;
}

/* KeyNode.addToEnd */
bool kn_add_to_end(struct obj_ctx *cx, struct knode *k, int64_t klongToAdd, struct obj *pointerToAdd,
        int64_t posToAdd) {
    int32_t sz = k->size;
    if (k->cap + 1 > sz) {      /* Java's test, always true; ensureCapacity decides */
        if (!ensure_capacity(cx, k, sz + 1)) {
            return false;
        }
    }

    if (kl_get_type(klongToAdd) == KL_TYPE_TIME) {
        k->last_time_index = (int16_t) sz;
    }

    k->klongs[sz] = klongToAdd;
    assert(k->pointers[sz] == NULL);
    obj_retain(pointerToAdd);
    k->pointers[sz] = pointerToAdd;
    k->pos[sz] = posToAdd;

    k->size = (int16_t) (sz + 1);
    return true;
}

/* Lowers the size to newSize, releasing the pointees of the slots that go
 * (012-07, 6.5: Java leaves them in place). */
static void lower_size(struct obj_ctx *cx, struct knode *k, int16_t newSize) {
    for (int32_t i = newSize; i < k->size; i++) {
        struct obj *p = k->pointers[i];
        k->pointers[i] = NULL;
        obj_release(cx, p);
    }
    k->size = newSize;
}

/* KeyNode.toPreviousState */
void kn_to_previous_state(struct obj_ctx *cx, struct knode *k, int64_t time) {
    int16_t sz = k->size;

    for (int32_t i = 0; i < sz; i++) {
        int64_t klong = k->klongs[i];

        if (kl_get_int_type(klong) == KL_INT_TYPE_TIME) {
            int64_t klongTime = kl_get_time(klong);
            if (klongTime > time) {
                if (i == 0) {
                    lower_size(cx, k, 0);
                } else {
                    lower_size(cx, k, (int16_t) i);
                }
                break;
            }
        }
    }

    k->last_time_index = -1;
}

/* KeyNode.setContentFrom */
bool kn_set_content_from(struct obj_ctx *cx, struct knode *k, const struct knode *other) {
    assert(other->size > 0 && kl_get_type(other->klongs[0]) == KL_TYPE_TIME);
    int32_t sz = other->size;
    int32_t len = sz > other->cap ? sz : other->cap;       /* Math.max(sz, other.klongs.length) */
    int64_t *block = new_block(cx, len);
    if (block == NULL) {
        return false;
    }
    int64_t *kk = block;
    int64_t *ps = block + len;
    struct obj **p = (struct obj **) (void *) (block + 2 * (size_t) len);
    memcpy(kk, other->klongs, (size_t) sz * sizeof *kk);
    memcpy(ps, other->pos, (size_t) sz * sizeof *ps);
    for (int32_t i = 0; i < sz; i++) {
        p[i] = other->pointers[i];
        obj_retain(p[i]);
    }

    lower_size(cx, k, 0);       /* the node's pointers before go */
    free_block(cx, k);
    set_arrays(k, block, len);
    k->last_time_index = other->last_time_index;
    k->size = (int16_t) sz;
    return true;
}

/* KeyNode.lastVersion */
struct knode *kn_last_version(struct obj_ctx *cx, const struct knode *k, int64_t time) {
    int16_t sz = k->size;
    int64_t deleteBitmap = kn_get_last_delete_bitmap(k, sz);
    return kn_last_version_given_del(cx, k, sz, time, deleteBitmap);
}

/* KeyNode.timeKlongCount */
static int32_t time_klong_count(const struct knode *k, int32_t sz) {
    int32_t timeCount = 0;
    for (int32_t i = 0; i < sz; i++) {
        if (kl_get_type(k->klongs[i]) == KL_TYPE_TIME) {
            timeCount++;
        }
    }
    return timeCount;
}

/* KeyNode.addToSorted: into a node sorted by strictly increasing compare
 * value, with at most one TIME klong, first, and no delete klong. */
static bool add_to_sorted(struct obj_ctx *cx, struct knode *k, int64_t klongToAdd,
        struct obj *pointerToAdd, int64_t posToAdd) {
    assert(kl_get_type(klongToAdd) == KL_TYPE_KEY);

    int64_t compareValue = kl_get_compare_value(klongToAdd);
    int16_t sz = k->size;
    if (!ensure_capacity(cx, k, sz + 1)) {
        return false;
    }
    int32_t startIndex = 0;
    if (sz > 0 && kl_get_type(k->klongs[0]) == KL_TYPE_TIME) {
        startIndex = 1;
    }

    bool added = false;

    for (int32_t i = startIndex; i < sz; i++) {
        int64_t arrayCompareValue = kl_get_compare_value(k->klongs[i]);
        if (arrayCompareValue == compareValue) {
            /* If same compare value, overwrite (will this ever happen?) */
            k->klongs[i] = klongToAdd;
            hold(cx, k, i, pointerToAdd);
            k->pos[i] = posToAdd;
            added = true;
            break;
        } else if (arrayCompareValue > compareValue) {
            /* Move existing values in the arrays to the right one step. Then insert. */
            memmove(k->klongs + i + 1, k->klongs + i, (size_t) (sz - i) * sizeof *k->klongs);
            memmove(k->pointers + i + 1, k->pointers + i, (size_t) (sz - i) * sizeof *k->pointers);
            memmove(k->pos + i + 1, k->pos + i, (size_t) (sz - i) * sizeof *k->pos);
            k->klongs[i] = klongToAdd;
            obj_retain(pointerToAdd);
            k->pointers[i] = pointerToAdd;
            k->pos[i] = posToAdd;
            k->size = (int16_t) (sz + 1);
            added = true;
            break;
        }
    }

    if (!added) {
        /* Adds to end if not already added. klongToAdd > all-existing-klongs-in-array. */
        k->klongs[sz] = klongToAdd;
        assert(k->pointers[sz] == NULL);
        obj_retain(pointerToAdd);
        k->pointers[sz] = pointerToAdd;
        k->pos[sz] = posToAdd;
        k->size = (int16_t) (sz + 1);
        added = true;
    }
    return true;
}

/* KeyNode.lastVersionGivenDel */
struct knode *kn_last_version_given_del(struct obj_ctx *cx, const struct knode *k, int16_t sz,
        int64_t time, int64_t del) {
    /* A simple brute-force method that scales with n^2, n = this.size. */
    struct knode *result;

    assert(sz >= 0 && sz <= 62);

    result = kn_new(cx, kn_is_segment_leaf(k));
    if (result == NULL || !ensure_capacity(cx, result, 1 + sz - time_klong_count(k, sz))) {
        return NULL;
    }

    /* Note, actual result size may be smaller because of deletes or setting a
     * key klong several times. */

    if (!kn_add_to_end(cx, result, kl_create_time(time), NULL, SPOS_NULL)) {
        return NULL;
    }
    assert(result->last_time_index == 0);

    for (int32_t i = 0; i < sz; i++) {
        if (kl_is_deleted(del, i)) {
            continue;
        }

        int64_t klong1 = k->klongs[i];
        int64_t type = kl_get_type(klong1);
        if (type == KL_TYPE_DELETE_BITMAP) {
            continue;           /* Just continue, we know delete bitmap already */
        }

        int64_t klongToAdd = KL_NULL;
        struct obj *pointerToAdd = NULL;
        int64_t posToAdd = SPOS_NULL;

        if (type == KL_TYPE_TIME) {
            if (kl_get_time(klong1) > time) {
                break;          /* Rest of klongs have a too high time, break for loop. */
            } else {
                continue;       /* Skips the time klong. */
            }
        }

        assert(type == KL_TYPE_KEY);

        int64_t compareValue1 = kl_get_compare_value(klong1);

        /* If such a compareValue is already in result, do nothing with this
         * klong; it has been handled already. */
        bool handled = false;
        for (int32_t j = 0; j < result->size; j++) {
            int64_t k1 = result->klongs[j];
            if (kl_get_type(k1) == KL_TYPE_KEY && kl_get_compare_value(k1) == compareValue1) {
                handled = true;
                break;
            }
        }
        if (handled) {
            continue;
        }

        klongToAdd = k->klongs[i];
        pointerToAdd = k->pointers[i];      /* Reference is copied, no deep copy. */
        posToAdd = k->pos[i];

        /* We have a klong with a compareValue that does not exist in result,
         * lets see if it is modified (set again) in the rest of the array
         * (within the time boundary). */

        for (int32_t j = i + 1; j < sz; j++) {
            if (kl_is_deleted(del, j)) {
                continue;
            }

            int64_t klong2 = k->klongs[j];
            int32_t intType2 = kl_get_int_type(klong2);

            if (intType2 == KL_INT_TYPE_TIME || intType2 == KL_INT_TYPE_DELETE_BITMAP) {
                continue;
            } else if (intType2 == KL_INT_TYPE_KEY) {
                int64_t cValue = kl_get_compare_value(klong2);
                if (cValue == compareValue1) {
                    klongToAdd = klong2;
                    pointerToAdd = k->pointers[j];
                    posToAdd = k->pos[j];
                }
            } else {
                assert(0 && "Bad klong type");
            }
        }

        if (klongToAdd != KL_NULL) {
            if (!add_to_sorted(cx, result, klongToAdd, pointerToAdd, posToAdd)) {
                return NULL;
            }
        }
    }

    return result;
}

/* KeyNode.firstAndSecond */
bool kn_first_and_second(struct obj_ctx *cx, const struct knode *k, int64_t tTime,
        const struct knode *last, const struct kwp *insert, int32_t insertLength,
        struct knode *first, struct knode *second, int64_t *secondKlongOut) {
    (void) k;                   /* Java's this, in an assert's message only */
    assert(insert != NULL || insertLength == 0);
    assert(insertLength >= 0 && insertLength < 10);

    int32_t lastSize = last->size;
    int32_t sizeOfFirst = (lastSize - 1) / 2 + 1;
    assert(kl_get_type(last->klongs[0]) == KL_TYPE_TIME);
    assert(lastSize > 1);
    assert(kn_check(last, NULL) == NULL);

    int64_t timeKlong = kl_create_time(tTime);
    if (!kn_add_to_end(cx, first, timeKlong, NULL, SPOS_NULL)        /* time klong, spos NULL */
            || !kn_add_to_end(cx, second, timeKlong, NULL, SPOS_NULL)) {
        return false;
    }
    int64_t secondKlong = KL_NULL;

    for (int32_t i = 1; i < lastSize; i++) {
        assert(kl_get_type(last->klongs[i]) != KL_TYPE_TIME);
        if (first->size < sizeOfFirst) {
            if (!kn_add_to_end(cx, first, last->klongs[i], last->pointers[i], last->pos[i])) {
                return false;
            }
        } else {
            if (!kn_add_to_end(cx, second, last->klongs[i], last->pointers[i], last->pos[i])) {
                return false;
            }
            if (secondKlong == KL_NULL) {
                secondKlong = last->klongs[i];
            }
        }
    }

    assert(secondKlong != KL_NULL);
    assert(first->size > 0);
    assert(second->size > 0);

    struct knode *insertTo = first;
    if (insertLength > 0
            && kl_get_compare_value(insert[0].klong) >= kl_get_compare_value(secondKlong)) {
        insertTo = second;
    }

    for (int32_t i = 0; i < insertLength; i++) {
        const struct kwp *kwi = &insert[i];
        struct obj *pointee;
        if (!hd_pointee_of(cx, kwi->node, &pointee)
                || !kn_add_to_end(cx, insertTo, kwi->klong, pointee,
                        kwi->node != NULL ? kwi->node->spos : kwi->pos)) {
            return false;
        }
    }

    *secondKlongOut = secondKlong;
    return true;
}

/* KeyNode.getMemSize: 80 + klongs.length * 24 (Java's estimate). */
int32_t kn_get_mem_size(const struct knode *k) {
    return 80 + k->cap * 24;
}

/* KeyNode.getMemoryPointerCount */
int32_t kn_get_memory_pointer_count(const struct knode *k) {
    int32_t count = 0;
    int32_t size = k->size;
    for (int32_t i = 0; i < size; i++) {
        if (kn_get_pointer_node(k, i) != NULL) {
            count++;
        }
    }
    return count;
}

/* KeyNode.checkSizes */
static const char *check_sizes(const struct knode *k) {
    if (k->cap < k->size) {
        return "klongs.length too small";
    }
    return NULL;
}

/* KeyNode.checkLastTimeIndex */
static const char *check_last_time_index(const struct knode *k) {
    int32_t index = k->last_time_index;
    if (index != -1) {
        int64_t klong = k->klongs[index];
        if (kl_get_type(klong) != KL_TYPE_TIME) {
            return "lastTimeIndex: not a TIME klong";      /* Assert.assertEquals */
        }
        int64_t time = kl_get_time(klong);
        if (time < 0) {
            return "Bad time";
        }
    }
    return NULL;
}

/* KeyNode.checkIncreasingTime: the TIME klongs' times increase strictly.
 * Since bergdb 005-75 (release 2026.2) 'time' follows the loop; before, it
 * was never updated, and no node failed (012-07, section 5). With 'buf'
 * (KN_TEXT bytes), Java's text, "Time not increasing, T, PREVIOUS,
 * index=I", is written there and returned (022-01, step 4). */
static const char *check_increasing_time(const struct knode *k, char *buf) {
    int64_t time = INT64_MIN;
    int16_t sz = k->size;

    for (int32_t i = 0; i < sz; i++) {
        int64_t klong = k->klongs[i];
        if (kl_get_type(klong) == KL_TYPE_TIME) {
            int64_t klongTime = kl_get_time(klong);
            if (klongTime <= time) {
                if (buf == NULL) {
                    return "Time not increasing";
                }
                snprintf(buf, KN_TEXT, "Time not increasing, %" PRId64 ", %" PRId64
                        ", index=%d", klongTime, time, (int) i);
                return buf;
            }
            time = klongTime;
        }
    }
    return NULL;
}

/* The text of a pointer's check, "WHAT of pointer I of key node ID at SPOS:
 * S." and 'more' (Node.name; bergdb 021-15), written into buf, or 'what'
 * alone without buf. */
static const char *pointer_text(const struct knode *k, char *buf, const char *what, int32_t i,
        int64_t pos, const char *more) {
    if (buf == NULL) {
        return what;
    }
    snprintf(buf, KN_TEXT, "%s of pointer %d of key node %" PRId64 " at %" PRId64 ": %" PRId64
            "%s.", what, (int) i, k->n.id, k->n.spos, pos, more);
    return buf;
}

/* KeyNode.checkMemoryPointers */
static const char *check_memory_pointers(const struct knode *k, int16_t sz, char *buf) {
    for (int32_t i = 0; i < sz; i++) {
        if (kl_get_type(k->klongs[i]) == KL_TYPE_KEY) {
            if (k->pointers[i] != NULL && !spos_is_valid_or_null(k->pos[i])) {
                return pointer_text(k, buf, "Bad reference", i, k->pos[i], "");
            }
        }
    }
    return NULL;
}

/* KeyNode.checkStreamPointers */
static const char *check_stream_pointers(const struct knode *k, int16_t sz, char *buf) {
    for (int32_t i = 0; i < sz; i++) {
        if (kl_get_type(k->klongs[i]) == KL_TYPE_KEY) {
            if (k->pointers[i] == NULL && !spos_is_valid(k->pos[i])) {
                return pointer_text(k, buf, "Bad spos", i, k->pos[i], "");
            }
        }
    }
    return NULL;
}

/* KeyNode.check(maxNodeSize) */
const char *kn_check_max(const struct knode *k, int32_t maxNodeSize, char *buf) {
    if (k->size > maxNodeSize + 1) {
        if (buf == NULL) {
            return "Overfull node";
        }
        snprintf(buf, KN_TEXT, "Overfull node, size=%d, maxNodeSize=%d, key node %" PRId64
                " at %" PRId64 ".", (int) k->size, (int) maxNodeSize, k->n.id, k->n.spos);
        return buf;
    }
    return kn_check(k, buf);
}

/* KeyNode.check */
const char *kn_check(const struct knode *k, char *buf) {
    int16_t sz = k->size;
    const char *m;
    if ((m = check_sizes(k)) != NULL || (m = check_last_time_index(k)) != NULL
            || (m = check_increasing_time(k, buf)) != NULL
            || (m = check_memory_pointers(k, sz, buf)) != NULL
            || (m = check_stream_pointers(k, sz, buf)) != NULL) {
        return m;
    }
    return NULL;
}

/* KeyNode.validateStreamNode */
const char *kn_validate_stream_node(const struct knode *k, int64_t startupTime, char *buf) {
    int16_t sz = k->size;
    const char *m;

    if (sz < 1) {
        snprintf(buf, KN_TEXT, "Key node %" PRId64 " at %" PRId64 " with size %d.", k->n.id,
                k->n.spos, (int) sz);
        return buf;
    }
    if ((m = check_sizes(k)) != NULL || (m = check_last_time_index(k)) != NULL
            || (m = check_increasing_time(k, buf)) != NULL) {
        return m;
    }

    int64_t klongTime = 0;

    for (int32_t i = 0; i < sz; i++) {
        int64_t klong = k->klongs[i];
        int64_t type = kl_get_type(klong);

        if (type == KL_TYPE_TIME) {
            klongTime = kl_get_time(klong);
        } else if (type == KL_TYPE_KEY) {
            if (k->pointers[i] == NULL) {
                int64_t spos = k->pos[i];
                if (klongTime > startupTime) {
                    if (!spos_is_valid_or_null(spos)) {
                        return pointer_text(k, buf, "Bad spos", i, spos, "");
                    }
                } else {
                    if (!spos_is_valid(spos)) {
                        char more[60];
                        snprintf(more, sizeof more, ", at or before the startup time %" PRId64,
                                startupTime);
                        return pointer_text(k, buf, "Bad spos", i, spos, more);
                    }
                }
            }
        }
    }
    return NULL;
}

/* KeyNode.getDeleteBitmap */
int64_t kn_get_delete_bitmap(const struct knode *k, int64_t compareValue) {
    int16_t sz;
    const int64_t *klongs;
    int64_t klong;
    int32_t klongType;
    int64_t deleteBitmap;
    int64_t newDeleteBitmap = 0;

    sz = k->size;
    klongs = k->klongs;
    deleteBitmap = kn_get_last_delete_bitmap(k, sz);

    for (int32_t index = 0; index < sz; index++) {
        if (kl_is_deleted(deleteBitmap, index)) {
            continue;
        }

        klong = klongs[index];
        klongType = kl_get_int_type(klong);

        if (klongType == KL_INT_TYPE_KEY) {
            if (compareValue == kl_get_compare_value(klong)) {
                if (newDeleteBitmap == 0) {
                    newDeleteBitmap = kl_delete(deleteBitmap, index);
                } else {
                    newDeleteBitmap = kl_delete(newDeleteBitmap, index);
                }
            }
        }
    }

    return newDeleteBitmap;
}

/* KeyNode.getLastDeleteBitmap: Java reads this.size, not sz. */
int64_t kn_get_last_delete_bitmap(const struct knode *k, int16_t sz) {
    (void) sz;
    int64_t del = kl_create_delete();
    int32_t s = k->size;

    for (int32_t index = 0; index < s; index++) {
        int64_t klong = k->klongs[index];
        if (kl_get_int_type(klong) == KL_INT_TYPE_DELETE_BITMAP) {
            del = klong;
        }
    }

    return del;
}

/* KeyNode.getDeleteBitmapAtTime */
int64_t kn_get_delete_bitmap_at_time(const struct knode *k, int64_t time, int32_t sz) {
    int64_t del = KL_DELETE_NONE_BITMAP;
    const int64_t *klongs = k->klongs;

    for (int32_t index = 0; index < sz; index++) {
        int64_t klong = klongs[index];
        int32_t type = j_l2i(j_ushr64(klong & J64(0xc000000000000000), 62));
        if (type == KL_INT_TYPE_TIME) {
            if ((klong & INT64_C(0x00ffffffffffffff)) > time) {
                break;
            }
        } else if (type == KL_INT_TYPE_DELETE_BITMAP) {
            del = klong;
        } else if (type != KL_INT_TYPE_KEY) {
            assert(0 && "Bad klong type");
        }
    }

    return del;
}

/* KeyNode.getFirstTime */
int64_t kn_get_first_time(const struct knode *k) {
    int64_t time = -1;
    int16_t sz = k->size;

    for (int32_t i = 0; i < sz; i++) {
        int64_t klong = k->klongs[i];
        if (kl_get_type(klong) == KL_TYPE_TIME) {
            time = kl_get_time(klong);
            break;
        }
    }

    return time;
}

/* KeyNode.getMaxValidTime */
int64_t kn_get_max_valid_time(const struct knode *k, int32_t pointerIndex) {
    int64_t klongAtIndex = k->klongs[pointerIndex];
    assert(kl_is_key(klongAtIndex));
    int64_t time = 0;
    int64_t maxValidTime = INT64_MAX;

    int32_t sz = k->size;
    for (int32_t i = pointerIndex; i < sz; i++) {
        int64_t klong = k->klongs[i];
        int32_t type = kl_get_int_type(klong);

        if (type == KL_INT_TYPE_TIME) {
            time = kl_get_time(klong);
        } else if (type == KL_INT_TYPE_KEY) {
            if (klong == klongAtIndex && time != 0) {
                maxValidTime = time - 1;
                break;
            }
        } else if (type == KL_INT_TYPE_DELETE_BITMAP) {
            if (kl_is_deleted(klong, pointerIndex) && time != 0) {
                maxValidTime = time - 1;
                break;
            }
        }
    }

    return maxValidTime;
}

void kn_destroy(struct obj_ctx *cx, struct knode *k, bool release) {
    if (release) {
        /* The rule of handle.h: a back reference names the handle that holds
         * k, which counts k; so k, freed, has none. */
        assert(k->handle == NULL);
        lower_size(cx, k, 0);
    }
    free_block(cx, k);
    obj_dealloc(cx, &k->n.o, sizeof(struct knode));
}
