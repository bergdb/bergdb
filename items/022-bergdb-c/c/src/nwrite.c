/* nwrite: ported from Java's StoredKeyNode.toLongs, StoredTopNode.toLongs
 * and StoredValueNode.toBytes; see nwrite.h. */
#include "nwrite.h"
#include <assert.h>
#include <string.h>
#include "bytes.h"
#include "checksum.h"
#include "jsem.h"
#include "spos.h"

/* StoredKeyNode.getByteSize */
int32_t nw_key_byte_size(const struct knode *node) {
    return 32 + node->size * 16;
}

/* StoredKeyNode.toLongs */
int32_t nw_key_to_longs(const struct knode *node, int64_t *buffer, int32_t firstOffset,
        int64_t prevPos) {
    int32_t sz = node->size;
    int32_t byteSize = nw_key_byte_size(node);
    int32_t offset = firstOffset;
    const int64_t FORMAT_VERSION = 2;   /* serial format version (one byte) */

    buffer[offset++] =
              ((int64_t) byteSize)
            | (((int64_t) NODE_TYPE_KEY_NODE) << (4 * 8))
            | (FORMAT_VERSION << (5 * 8));

    /* 2 bytes available for checksum */

    buffer[offset++] = prevPos;
    buffer[offset++] = ((int64_t) (kn_is_segment_leaf(node) ? 1 : 0)) | j_shl32(sz, 1 * 8);
    /* 6 zero bytes available... */
    buffer[offset++] = node->n.id;

    if (sz > 0) {
        memcpy(buffer + offset, node->klongs, (size_t) sz * sizeof *buffer);
    }
    offset += sz;

    for (int32_t i = 0; i < sz; i++) {
        buffer[offset++] = kn_get_serialized_ref(node, i);
    }

    int64_t checksum = cks_sum_longs(buffer, firstOffset, offset - firstOffset);
    buffer[firstOffset] = buffer[firstOffset] | (checksum << (6 * 8));

    assert((offset - firstOffset) * 8 == byteSize);
    assert(byteSize % 8 == 0);
    return byteSize / 8;
}

/* StoredTopNode.getByteSize */
int32_t nw_top_byte_size(const struct tnode *node) {
    return 40 + 16 * node->pointers_length;
}

/* StoredTopNode.toLongs */
int32_t nw_top_to_longs(const struct tnode *node, int64_t *buffer, int32_t firstOffset) {
    int32_t byteSize = nw_top_byte_size(node);
    int32_t offset = firstOffset;
    int64_t l;
    const int64_t FORMAT_VERSION = 2;   /* serial format version (one byte) */

    assert(byteSize % 8 == 0);

    l = ((int64_t) byteSize)
            | (((int64_t) NODE_TYPE_TOP_NODE) << (4 * 8))
            | (FORMAT_VERSION << (5 * 8));

    /* Room for 2 checksum bytes. */

    buffer[offset++] = l;

    /* The ordinal is widened before it is shifted (2026-10-16, WP A3; a long
     * below 2^48 in bytes 10 to 15 since 005-02; byte 9 stays zero). */
    l = ((int64_t) node->pointers_length) | j_shl64(node->top_node_id, 2 * 8);
    buffer[offset++] = l;

    buffer[offset++] = node->n.id;

    buffer[offset++] = node->root_time;

    /* spos value for the pointers */

    int64_t spos = tn_get_serialized_ref(node, 0);

    buffer[offset++] = spos;

    for (int32_t i = 0; i < node->pointers_length; i++) {
        spos = tn_get_serialized_ref(node, i + 1);
        buffer[offset++] = spos;

        int64_t time = spos == SPOS_NULL ? -1 : node->skip[i].time;
        buffer[offset++] = time;
    }

    int64_t checksum = cks_sum_longs(buffer, firstOffset, offset - firstOffset);
    buffer[firstOffset] = buffer[firstOffset] | (checksum << (6 * 8));

    assert((offset - firstOffset) * 8 == byteSize);
    return byteSize / 8;
}

/* StoredValueNode.getByteSize */
int32_t nw_value_byte_size(const struct vnode *node, int32_t keyLength) {
    int32_t size = node->len < 0
            ? 8 + 8 + 4 +                   4 + 8 * keyLength
            : 8 + 8 + 4 + 4 + node->len + 4 + 8 * keyLength;
    return size + spos_add_to_align(size, 4);
}

/* StoredValueNode.getByteSizeLong */
int64_t nw_value_byte_size_long(int64_t len, int32_t keyLength) {
    int64_t size = len < 0
            ? 8 + 8 + 4 +                 4 + INT64_C(8) * keyLength
            : 8 + 8 + 4 + 4 + len + 4 + INT64_C(8) * keyLength;
    return size + (4 - size % 4) % 4;
}

/* StoredValueNode.toBytes */
int32_t nw_value_to_bytes(const struct vnode *node, const int64_t *key, int32_t keyLength,
        uint8_t *buffer, int32_t bufferOffset) {
    int32_t offset = bufferOffset;
    int32_t byteSize = nw_value_byte_size(node, keyLength);
    int64_t myLong;
    const int64_t FORMAT_VERSION = 4;   /* serial format version (one byte) */
    int64_t nodeType = node->len < 0 ? NODE_TYPE_DELETE : NODE_TYPE_VALUE;

    myLong = ((int64_t) byteSize)
            | (nodeType << (4 * 8))
            | (FORMAT_VERSION << (5 * 8));

    bytes_put_long_le(myLong, buffer + offset);
    offset += 8;
    /* Room for 2 checksum bytes. */

    bytes_put_long_le(node->n.id, buffer + offset);
    offset += 8;

    int32_t offsetFromTrans = bufferOffset;
    bytes_put_int_le(offsetFromTrans, buffer + offset);
    offset += 4;

    if (nodeType == NODE_TYPE_VALUE) {
        /* only TYPE_VALUE (not TYPE_DELETE) have value */
        bytes_put_int_le(node->len, buffer + offset);
        offset += 4;
        if (node->len > 0) {
            memcpy(buffer + offset, node->value, (size_t) node->len);
        }
        offset += node->len;
    }

    bytes_put_int_le(keyLength * 8, buffer + offset);
    offset += 4;
    bytes_longs_to_le(key, keyLength, buffer + offset);
    offset += 8 * keyLength;

    /* Zeros the alignment padding: the buffer may hold earlier bytes, and the
     * padding is part of the checksum. */
    for (int32_t i = offset; i < bufferOffset + byteSize; i++) {
        buffer[i] = 0;
    }

    int32_t checksum = cks_sum(buffer, bufferOffset, byteSize);
    bool ok = bytes_put_ushort_le(checksum, buffer + bufferOffset + 6);
    assert(ok);
    (void) ok;

    int32_t sizeHere = offset - bufferOffset;
    assert(sizeHere + spos_add_to_align(sizeHere, 4) == byteSize);
    (void) sizeHere;

    return byteSize;
}
