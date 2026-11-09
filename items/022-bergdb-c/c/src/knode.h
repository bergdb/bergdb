/*
 * knode: Java's bergdb.dag.KeyNode, method by method (bergdb 012-07), and
 * the making of a key node object from a parsed one (StoredKeyNode.parse's
 * second half). Prefix kn_.
 *
 * A key node has an array of klongs (klong.h), appended in time order, each
 * with a pointer: what it holds (NULL, a child's handle or a value; counted)
 * and its reference (a position, a vpos or -1). A TIME klong begins the
 * entries of its time, a KEY klong maps a compare value to its pointer, a
 * delete bitmap removes the klongs whose bits it sets (012-02, 6.3.1).
 *
 * The three arrays are one block of cap * 24 bytes: klongs, then pos, then
 * pointers, at Java's lengths (ARRAY_SIZES). A slot holds a pointee exactly
 * when it is below size (Java's toPreviousState leaves the slots past the
 * new size as they were; C releases and clears them: 012-07, 6.5).
 *
 * Java's monitors and volatiles serve concurrent readers, which C does not
 * have; they are left out. A function that can allocate returns false (or
 * NULL) on NOMEM, with the counts kept (obj.h); Java's checks that throw
 * AssertionError return a message here, NULL when the node is right.
 * Left out: print, toString, getInfo, createKlongIter (debug text), accept.
 */
#ifndef BERGDB_KNODE_H
#define BERGDB_KNODE_H

#include <stdbool.h>
#include <stdint.h>
#include "handle.h"
#include "node.h"
#include "obj.h"

struct knode {
    struct node n;
    int16_t size;               /* KeyNode.size: the klongs used */
    int16_t last_time_index;    /* KeyNode.lastTimeIndex: -1 or the last TIME klong's index */
    int32_t cap;                /* klongs.length = pointers.length = pos.length */
    int64_t *klongs;            /* the block (MEM_INDEX), NULL when cap is 0 */
    int64_t *pos;               /* klongs + cap: each pointer's reference */
    struct obj **pointers;      /* after pos: what each pointer holds */
    struct handle *handle;      /* KeyNode.handle, the back reference: not counted */
};

/* new KeyNode(isSegmentLeaf): no klongs, id and spos -1; pending (obj.h).
 * NULL: NOMEM. */
struct knode *kn_new(struct obj_ctx *cx, bool is_segment_leaf);

/* KeyNode.nodeWithTime: a segment leaf with one TIME klong. */
struct knode *kn_new_with_time(struct obj_ctx *cx, int64_t time);

/* StoredKeyNode.parse's object: a key node of n klongs at spos with the
 * id, its klongs and references little-endian at klongs_le and refs_le (8
 * bytes each, as the stored node has them), every pointer a stream pointer
 * (addToEnd(klong, null, pos)). NULL: NOMEM. */
struct knode *kn_new_stored(struct obj_ctx *cx, bool is_segment_leaf, int64_t spos, int64_t id,
        int32_t n, const uint8_t *klongs_le, const uint8_t *refs_le);

bool kn_is_segment_leaf(const struct knode *k);
int64_t kn_get_klong(const struct knode *k, int32_t index);
int32_t kn_get_size(const struct knode *k);
int32_t kn_get_size_at_time(const struct knode *k, int64_t lookup_time);

/* getPointer, getPointerNode, getPointerPos, getPointee */
void kn_get_pointer(const struct knode *k, int32_t index, struct pointer *p);
struct node *kn_get_pointer_node(const struct knode *k, int32_t index);
int64_t kn_get_pointer_pos(const struct knode *k, int32_t index);
struct obj *kn_get_pointee(const struct knode *k, int32_t index);
/* setPointee, setRef, raiseRef, swizzle, setPointer; the pointee counted. */
void kn_set_pointee(struct obj_ctx *cx, struct knode *k, int32_t index, struct obj *pointee);
void kn_set_ref(struct knode *k, int32_t index, int64_t ref);
void kn_raise_ref(struct knode *k, int32_t index, int64_t ref);
bool kn_swizzle(struct obj_ctx *cx, struct knode *k, int32_t index, struct obj *expected,
        struct obj *pointee);
void kn_set_pointer(struct obj_ctx *cx, struct knode *k, int32_t index, struct obj *pointee,
        int64_t ref);
/* getSerializedRef: the record rule (hd_serialized_ref). */
int64_t kn_get_serialized_ref(const struct knode *k, int32_t index);

/* The searches at a time, into *kwi (its state on entry does not matter;
 * kwi->klong is KL_NULL if nothing is found). searchEq: the latest key
 * klong whose compare value is compare_value; searchLte, searchLt,
 * searchGt, searchGte: the largest key klong <= or < it, the smallest > or
 * >= it (-1 for the smallest); searchFirst: the smallest. */
void kn_search_eq(const struct knode *k, int64_t time, int64_t compare_value, struct kwp *kwi);
void kn_search_lte(const struct knode *k, int64_t time, int64_t compare_value, struct kwp *kwi);
void kn_search_lt(const struct knode *k, int64_t time, int64_t compare_value, struct kwp *kwi);
void kn_search_gt(const struct knode *k, int64_t time, int64_t compare_value, struct kwp *kwi);
void kn_search_gte(const struct knode *k, int64_t time, int64_t compare_value, struct kwp *kwi);
void kn_search_first(const struct knode *k, int64_t time, struct kwp *kwi);

/* addDeleteKlong: a delete bitmap klong at time. */
bool kn_add_delete_klong(struct obj_ctx *cx, struct knode *k, int64_t time, int64_t klong);

/* addKlong: klong (not a TIME klong) at the end, with a pointer to
 * pointer_node (its handle, or the value; reference its spos), or without
 * a node a stream pointer to access_data_or_spos; a TIME klong first if
 * time is later than the node's last time. */
bool kn_add_klong(struct obj_ctx *cx, struct knode *k, int64_t time, int64_t klong,
        struct node *pointer_node, int64_t access_data_or_spos);

/* replaceKlong: replaces the pointer of the key klong equal to klong1 at
 * time; *replaced is true if there was one. A delete bitmap in the node is
 * a bug (asserted; Java throws IllegalStateException). */
bool kn_replace_klong(struct obj_ctx *cx, struct knode *k, int64_t time, int64_t klong1,
        struct node *pointer_node, int64_t access_data, bool *replaced);

/* addToEnd: the klong and its pointer (pointee retained, reference pos)
 * at the end; a TIME klong becomes the last time. */
bool kn_add_to_end(struct obj_ctx *cx, struct knode *k, int64_t klong, struct obj *pointee,
        int64_t pos);

/* toPreviousState: the state at time: the klongs after the first TIME
 * klong later than time go (their pointers released), lastTimeIndex -1. */
void kn_to_previous_state(struct obj_ctx *cx, struct knode *k, int64_t time);

/* setContentFrom: k's klongs and pointers become other's (copied, the
 * pointees retained; k's released); other's first klong a TIME klong. */
bool kn_set_content_from(struct obj_ctx *cx, struct knode *k, const struct knode *other);

/* lastVersion, lastVersionGivenDel: a new key node (pending), the last
 * version of k at time: a TIME klong, then k's live key klongs in strictly
 * increasing compare value order, each with its latest pointer (shared:
 * the pointees retained). NULL: NOMEM. sz 0 to 62. */
struct knode *kn_last_version(struct obj_ctx *cx, const struct knode *k, int64_t time);
struct knode *kn_last_version_given_del(struct obj_ctx *cx, const struct knode *k, int16_t sz,
        int64_t time, int64_t del);

/* firstAndSecond: splits last (k's last version) into first and second, at
 * (last.size - 1) / 2 + 1, each with a TIME klong of t_time first; the
 * n_insert klongs of insert[] go to first, or to second if the first of
 * them is at or after second's first key; *second_klong is second's first
 * key klong. first and second are empty on entry. */
bool kn_first_and_second(struct obj_ctx *cx, const struct knode *k, int64_t t_time,
        const struct knode *last, const struct kwp *insert, int32_t n_insert,
        struct knode *first, struct knode *second, int64_t *second_klong);

/* getMemSize, getMemoryPointerCount */
int32_t kn_get_mem_size(const struct knode *k);
int32_t kn_get_memory_pointer_count(const struct knode *k);

/* The size of the buffer of the checks' texts: the longest, 158 bytes with
 * its end, fits. */
#define KN_TEXT 200

/* The checks: NULL if right, else a message. check(maxNodeSize): the size
 * at most maxNodeSize + 1, then check(); check(): the sizes, the last time
 * index, increasing times (as Java's, see 012-07's notes), the pointers.
 * With buf (KN_TEXT bytes), Java's AssertionError's text is written there
 * and returned, the node named by Node.name, "key node ID at SPOS" (bergdb
 * 021-15, as Java's since release 2026.4: "Bad spos of pointer I of key
 * node ID at SPOS: S."); with NULL, a short text without numbers (the
 * asserts). */
const char *kn_check_max(const struct knode *k, int32_t max_node_size, char *buf);
const char *kn_check(const struct knode *k, char *buf);

/* validateStreamNode: Java's KeyNode.Invalid as a message, written into
 * buf, KN_TEXT bytes: Java's texts, the node named by Node.name (bergdb
 * 021-15, as Java's since release 2026.4: "Key node ID at SPOS with size
 * 0.", "Bad spos of pointer I of key node ID at SPOS: S." and, for a
 * pointer at or before the startup time, "..., at or before the startup
 * time T."; before, Java's held KeyNode.toString, with Object.toString's
 * identity hash, and C's were its own). */
const char *kn_validate_stream_node(const struct knode *k, int64_t startup_time, char *buf);

/* getDeleteBitmap: the delete bitmap that deletes compare_value's klongs,
 * 0 if none (a delete of a key that does not exist). */
int64_t kn_get_delete_bitmap(const struct knode *k, int64_t compare_value);
/* getLastDeleteBitmap; Java ignores sz and reads size, as C does. */
int64_t kn_get_last_delete_bitmap(const struct knode *k, int16_t sz);
/* getDeleteBitmapAtTime: the last delete bitmap at or before time among
 * the first sz klongs. */
int64_t kn_get_delete_bitmap_at_time(const struct knode *k, int64_t time, int32_t sz);
/* getFirstTime: the first TIME klong's time, -1 if none. */
int64_t kn_get_first_time(const struct knode *k);
/* getMaxValidTime: the last lookup time at which pointer index is valid. */
int64_t kn_get_max_valid_time(const struct knode *k, int32_t pointer_index);

/* The free of a key node (obj.c): releases its pointees (if release) and
 * frees its block and the node. */
void kn_destroy(struct obj_ctx *cx, struct knode *k, bool release);

#endif
