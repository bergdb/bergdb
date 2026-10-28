/*
 * trans: a transaction and its builder, ported from Java's bergdb.core.Trans
 * and Trans.Builder (bergdb 012-09; 012-02, 8.5), with Java's Kv. Prefix
 * tr_.
 *
 * The builder collects the puts and deletes in the caller's order, the
 * read set's key hashes and the lookup time. tr_build makes the
 * transaction as Trans.Builder.build does: its pairs in key order
 * (Keys.compareArrays, the TreeMap's comparator), one per key: a later put
 * replaces an earlier one, a later delete an earlier delete, and a delete
 * never replaces a put ("Non-deletes take precedence over deletes"); the
 * read set's hashes in the order given; the write hashes, Keys.hash of each
 * pair's key, in the pairs' order. Java's virtual write hashes and
 * addReadHash are the Pub API's and are left out.
 *
 * A pair holds copies of its key (segments, Keys.toSegments) and value,
 * owned by the builder (MEM_CALLER). A built transaction points to the
 * builder's pairs: it is used while the builder is not changed, within one
 * execute. A pair's key and value transformations (Java's KeyTransformation
 * and ValueTransformation, the API's struct bergdb_transform) replace its
 * key and value when they run, as Java's Kv keeps what they set.
 */
#ifndef BERGDB_TRANS_H
#define BERGDB_TRANS_H

#include <stdbool.h>
#include <stdint.h>
#include "err.h"
#include "mem.h"

/* A key or value transformation: the API's struct bergdb_transform. */
struct tr_transform {
    void (*key)(void *ctx, int64_t tt, const uint8_t **key, size_t *key_len);
    void (*value)(void *ctx, int64_t tt, const uint8_t *previous, size_t previous_len,
            const uint8_t **value, size_t *value_len);
    void *ctx;
};

/* Kv: a pair of the transaction. */
struct tr_kv {
    int64_t *key;           /* the key's segments, key_n of them (owned) */
    int32_t key_n;
    uint8_t *value;         /* the value's bytes (owned; NULL for an empty value too) */
    int32_t len;            /* the value's length; -1: a delete (Java's null) */
    bool has_tf;            /* tf holds transformations (Kv.keyTransformation and
                               valueTransformation, either may be NULL) */
    struct tr_transform tf;
};

/* Trans.Builder. */
struct tr_builder {
    struct mem *mem;
    struct tr_kv *kvs;      /* in the order given */
    int32_t nkvs;
    int32_t cap;
    int64_t *read_hashes;   /* Keys.hash of each key read */
    int32_t nread;
    int32_t read_cap;
    int64_t lookup_time;    /* builderLookupTime: Long.MAX_VALUE */
};

/* Trans: what build makes, and execute's input and output fields. */
struct trans {
    struct tr_kv **kvs;     /* the builder's pairs, in key order, one per key */
    int32_t nkvs;
    int64_t *write_key_hashes;  /* writeKeyHashes, one per pair */
    int64_t read_time;      /* readTime */
    const int64_t *read_key_hashes;     /* readKeyHashes: the builder's */
    int32_t nread;
    int64_t tt;             /* the transaction's time */
    int64_t tpos;           /* the position of its first byte (after execute) */
    int64_t last_pos;       /* of its last byte */
    int64_t next_pos;       /* of the next transaction's first byte */
    int32_t node_count;     /* the nodes of its record */
    bool is_internal;       /* Trans.isInternal: the creation; reclaim's (012-11) */
    int64_t startup_pos;    /* Spos.NULL until store() */
    int32_t cap;            /* the arrays' capacity */
    struct mem *mem;
};

/* new Trans.Builder(): empty, lookup time Long.MAX_VALUE. */
void tr_builder_init(struct tr_builder *b, struct mem *m);

/* Frees the builder's pairs and arrays. */
void tr_builder_free(struct tr_builder *b);

/* Builder.put(byte[] key, byte[] value): copies of the key (as segments)
 * and the value; tf NULL for none, else Builder.put(long[], KeyTransformation,
 * byte[], ValueTransformation). ERR_NOMEM, and the builder as before. */
enum err_code tr_put(struct tr_builder *b, const uint8_t *key, int32_t key_len,
        const uint8_t *value, int32_t value_len, const struct tr_transform *tf, struct err *e);

/* Builder.delete(byte[] key). ERR_NOMEM, and the builder as before. */
enum err_code tr_delete(struct tr_builder *b, const uint8_t *key, int32_t key_len,
        struct err *e);

/* Builder.put(long[] key, byte[] value) and delete(long[]): the key as
 * segments (copied); value NULL for a delete. For the database's own
 * transactions (setStartupDistance's dummy). */
enum err_code tr_put_segments(struct tr_builder *b, const int64_t *key, int32_t key_n,
        const uint8_t *value, int32_t value_len, struct err *e);

/* Builder.keyRead(byte[] key): Keys.hash of its segments. ERR_NOMEM. */
enum err_code tr_key_read(struct tr_builder *b, const uint8_t *key, int32_t key_len,
        struct err *e);

/* Builder.lookupTime: not negative (else ERR_ARG, Java's
 * IllegalArgumentException; the builder unchanged). */
enum err_code tr_lookup_time(struct tr_builder *b, int64_t lookup_time, struct err *e);

/* Builder.build into t (made or remade here; tr_free frees it). ERR_NOMEM,
 * and t empty. */
enum err_code tr_build(struct tr_builder *b, struct trans *t, struct err *e);

/* An empty transaction, nothing allocated. */
void tr_init(struct trans *t, struct mem *m);

/* Frees what tr_build allocated in t. */
void tr_free(struct trans *t);

/* Replaces pair kv's key with a copy of key (len bytes, as segments), or
 * its value with a copy of value (len bytes; value NULL: a delete): what a
 * transformation set. ERR_NOMEM, and the pair as before. */
enum err_code tr_kv_set_key(struct tr_kv *kv, struct mem *m, const uint8_t *key, int32_t len,
        struct err *e);
enum err_code tr_kv_set_value(struct tr_kv *kv, struct mem *m, const uint8_t *value,
        int32_t len, struct err *e);

#endif
