/*
 * nwrite: the writers of the stored nodes (bergdb 012-07; 012-02, section
 * 6), ported from Java's StoredKeyNode.toLongs, StoredTopNode.toLongs and
 * StoredValueNode.toBytes, with their getByteSize. The parsers are
 * 012-06's (snode). Prefix nw_.
 *
 * As in Java, a top or a key node is written as longs into a long buffer
 * (each long is 8 little-endian bytes of the record: bytes_longs_to_le),
 * and a value node as bytes. The checksum (Fletcher-16, checksum.h) is
 * computed with its two bytes 0 and put at bytes 6 and 7.
 */
#ifndef BERGDB_NWRITE_H
#define BERGDB_NWRITE_H

#include <stdint.h>
#include "knode.h"
#include "tnode.h"
#include "vnode.h"

/* StoredKeyNode.getByteSize: 32 + 16 size. */
int32_t nw_key_byte_size(const struct knode *node);

/* StoredKeyNode.toLongs: node with prev_pos into buffer[first_offset] on;
 * returns the longs written, nw_key_byte_size / 8. Each reference is the
 * record rule's (kn_get_serialized_ref). */
int32_t nw_key_to_longs(const struct knode *node, int64_t *buffer, int32_t first_offset,
        int64_t prev_pos);

/* StoredTopNode.getByteSize: 40 + 16 h. */
int32_t nw_top_byte_size(const struct tnode *node);

/* StoredTopNode.toLongs: returns the longs written. */
int32_t nw_top_to_longs(const struct tnode *node, int64_t *buffer, int32_t first_offset);

/* StoredValueNode.getByteSize: 8 + 8 + 4 + 4 + L + 4 + 8 k for a value
 * (no 4 + L for a delete), rounded up to a multiple of 4; in an int, as
 * Java. */
int32_t nw_value_byte_size(const struct vnode *node, int32_t key_n);

/* StoredValueNode.getByteSizeLong: the same for a value of len bytes (-1:
 * a delete), in a long (005-17). */
int64_t nw_value_byte_size_long(int64_t len, int32_t key_n);

/* StoredValueNode.toBytes: node with its key (key_n segments) into
 * buffer[buffer_offset] on, where buffer_offset is also the node's offset in
 * its record's bytes, as it is stored; returns the bytes written,
 * nw_value_byte_size. */
int32_t nw_value_to_bytes(const struct vnode *node, const int64_t *key, int32_t key_n,
        uint8_t *buffer, int32_t buffer_offset);

#endif
