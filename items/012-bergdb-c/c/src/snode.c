/* snode: the stored nodes' parsers, ported from Java's NodeStream.bytesToNode,
 * StoredTopNode.parse, StoredKeyNode.parse and StoredValueNode.parse; see
 * snode.h. */
#include "snode.h"
#include <string.h>
#include "bytes.h"
#include "checksum.h"
#include "jsem.h"
#include "rstream.h"
#include "spos.h"

#define KLONG_MIN_TIME INT64_C(0)
#define KLONG_MAX_TIME ((INT64_C(1) << 56) - 1)
#define AIOOBE "ArrayIndexOutOfBoundsException"

/* Whether n bytes at off are within a buffer of len bytes. */
static bool in(int32_t len, int64_t off, int64_t n) {
    return off >= 0 && n >= 0 && off <= (int64_t) len - n;
}

static enum err_code oob(struct err *e, int64_t off, int32_t len) {
    return err_set(e, ERR_FORMAT, AIOOBE, "Index %lld out of bounds for length %d",
            (long long) off, (int) len);
}

/* Reads, as Java's Bytes do, once the bounds are checked. */
#define NEED(off, n) do { if (!in(len, (off), (n))) return oob(e, (off), len); } while (0)

/* TopNode.height: the bit length of the ordinal. */
static int32_t height(int64_t id) {
    int32_t i;
    for (i = 0; i < 48; i++) {
        if (id < (INT64_C(1) << i)) {
            break;
        }
    }
    return i;
}

enum err_code sn_bytes_to_node(int64_t spos, const uint8_t *buf, int32_t len, int32_t offset,
        int32_t size, struct sn_node *out, struct err *e) {
    /* assert buffer.length > offset + 5, a check with -ea */
    if (!(len > offset + 5) || offset < 0) {
        return err_set(e, ERR_FORMAT, "AssertionError", "offset=%d, buffer.length=%d",
                (int) offset, (int) len);
    }
    int8_t nodeType = j_l2b(buf[offset + 4]);

    /* checkChecksum: NodeChecksum.sumWithZeroReplace runs from offset to offset + size,
     * an int that may wrap, and reads each byte. */
    int32_t end = offset + size;
    int32_t computedSum = 0;
    if (end > offset) {
        if (end > len) {
            return oob(e, len, len);
        }
        computedSum = cks_sum_with_zero_replace(buf, offset, size, offset + 6);
    }
    NEED(offset + 6, 2);
    int32_t storedSum = bytes_get_ushort_le(buf + offset + 6);
    if (computedSum != storedSum) {
        return err_set(e, ERR_FORMAT, "StreamChecksumException",
                "spos: %lld, storedSum: %d, computedSum: %d, nodeType: %d", (long long) spos,
                (int) storedSum, (int) computedSum, (int) nodeType);
    }

    enum err_code rc;
    switch (nodeType) {
    case NODE_KEY:
        rc = sn_parse_key(buf, len, offset, spos, out, e);
        break;
    case NODE_TOP:
        rc = sn_parse_top(buf, len, offset, spos, out, e);
        break;
    case NODE_VALUE:
    case NODE_DELETE:
        rc = sn_parse_value(buf, len, offset, spos, out, e);
        break;
    default:
        return err_set(e, ERR_FORMAT, "StreamFormatException", "Bad node type in stream, %d, "
                "for stream item at spos = %lld. , buffer.length=%d.", (int) nodeType,
                (long long) spos, (int) len);
    }
    if (rc == ERR_OK) {
        out->size = size;
    }
    return rc;
}

static void init_node(struct sn_node *out, int32_t type, int64_t spos, const uint8_t *bytes) {
    memset(out, 0, sizeof *out);
    out->type = type;
    out->spos = spos;
    out->bytes = bytes;
    out->value_len = -1;
}

enum err_code sn_parse_top(const uint8_t *buf, int32_t len, const int32_t firstOffset,
        int64_t spos, struct sn_node *out, struct err *e) {
    int32_t offset = firstOffset;
    offset += 4;    /* Skip size bytes */
    NEED(offset, 1);
    int8_t type = j_l2b(buf[offset]);
    offset += 1;
    if (type != NODE_TOP) {
        return err_set(e, ERR_FORMAT, "Bug", "Bad node type byte, %d, should have been checked"
                " already.", (int) type);
    }
    NEED(offset, 1);
    int8_t version = j_l2b(buf[offset]);
    offset += 1;
    if (version != 2) {
        return err_set(e, ERR_FORMAT, "VersioningStreamException",
                "Cannot parse top node of format version %d.", (int) version);
    }
    offset += 2;    /* checksum bytes, checked later */

    NEED(offset, 1);
    int32_t pointerCount = j_l2b(buf[offset]);
    offset += 1;
    if (pointerCount < 0) {         /* 005-21, before the arrays */
        return err_set(e, ERR_FORMAT, "StreamFormatException",
                "TopNode at %lld with %d skip pointers.", (long long) spos, (int) pointerCount);
    }
    offset += 1;    /* rest of header (reserved) */

    NEED(firstOffset + 8, 8);
    int64_t topNodeId = j_ushr64(bytes_get_long_le(buf + firstOffset + 8), 16);
    offset += 6;
    if (topNodeId > SN_MAX_ORDINAL) {
        return err_set(e, ERR_FORMAT, "StreamFormatException",
                "TopNode ID too large in stream, %lld", (long long) topNodeId);
    }
    NEED(offset, 8);
    int64_t id = bytes_get_long_le(buf + offset);
    offset += 8;
    NEED(offset, 8);
    int64_t rootTime = bytes_get_long_le(buf + offset);
    offset += 8;
    if (rootTime < KLONG_MIN_TIME) {
        return err_set(e, ERR_FORMAT, "StreamFormatException", "Time too small, %lld.",
                (long long) rootTime);
    }
    if (rootTime > KLONG_MAX_TIME) {
        return err_set(e, ERR_FORMAT, "StreamFormatException", "Time too large, %lld.",
                (long long) rootTime);
    }
    NEED(offset, 8);
    int64_t rootPointerPos = bytes_get_long_le(buf + offset);
    offset += 8;
    if (rootPointerPos < 0) {
        return err_set(e, ERR_FORMAT, "StreamFormatException", "Invalid root pointer pos, %lld.",
                (long long) rootPointerPos);
    }
    const int32_t pointersOffset = offset;
    NEED(offset, (int64_t) 16 * pointerCount);
    offset += 16 * pointerCount;

    /* assert Bytes.bytesToIntLE(buffer, firstOffset) == offset - firstOffset, a check
     * with -ea */
    NEED(firstOffset, 4);
    if (bytes_get_int_le(buf + firstOffset) != offset - firstOffset) {
        return err_set(e, ERR_FORMAT, "AssertionError", "top node at %lld: size %d, parsed %d",
                (long long) spos, (int) bytes_get_int_le(buf + firstOffset),
                (int) (offset - firstOffset));
    }

    /* The skip pointers must fit the ordinal (2026-10-16, WP A3). */
    int32_t pointersLength = height(topNodeId);
    if (pointerCount != pointersLength) {
        return err_set(e, ERR_FORMAT, "StreamFormatException", "TopNode at %lld with ordinal "
                "%lld has %d skip pointers, not %d.", (long long) spos, (long long) topNodeId,
                (int) pointerCount, (int) pointersLength);
    }
    for (int32_t i = 0; i < pointerCount; i++) {
        bool set = bytes_get_long_le(buf + pointersOffset + 16 * i) != SPOS_NULL;
        if (set != ((topNodeId & (INT64_C(1) << i)) != 0)) {
            return err_set(e, ERR_FORMAT, "StreamFormatException", "TopNode at %lld with "
                    "ordinal %lld: skip pointer %d %s, which does not fit the ordinal.",
                    (long long) spos, (long long) topNodeId, (int) i,
                    set ? "is set" : "is not set");
        }
    }

    init_node(out, NODE_TOP, spos, buf + firstOffset);
    out->id = id;
    out->ordinal = topNodeId;
    out->root_time = rootTime;
    out->root = rootPointerPos;
    out->h = pointerCount;
    return ERR_OK;
}

enum err_code sn_parse_key(const uint8_t *buf, int32_t len, int32_t offset, int64_t spos,
        struct sn_node *out, struct err *e) {
    const int32_t firstOffset = offset;
    offset += 4;    /* Skip size. */
    NEED(offset, 1);
    int8_t type = j_l2b(buf[offset]);
    offset += 1;
    if (type != NODE_KEY) {
        return err_set(e, ERR_FORMAT, "Bug", "Bad node type byte, %d, should have been checked"
                " already.", (int) type);
    }
    NEED(offset, 1);
    int8_t version = j_l2b(buf[offset]);
    if (version != 2) {
        return err_set(e, ERR_FORMAT, "VersioningStreamException",
                "Cannot parse key node of format version %d.", (int) version);
    }
    offset += 1;
    offset += 2;    /* checksum bytes */

    NEED(offset, 8);
    int64_t prevPos = bytes_get_long_le(buf + offset);
    if (!spos_is_valid_or_null(prevPos)) {
        return err_set(e, ERR_FORMAT, "StreamFormatException",
                "Bad KeyNode, prevPos is illegal: %lld.", (long long) prevPos);
    }
    offset += 8;
    NEED(offset, 1);
    if (!(buf[offset] == 0 || buf[offset] == 1)) {
        return err_set(e, ERR_FORMAT, "StreamFormatException",
                "Bad second byte, expected 0 or 1, was %d.", (int) j_l2b(buf[offset]));
    }
    bool isSegmentLeaf = buf[offset] == 1;
    offset += 1;
    NEED(offset, 2);
    int32_t size = bytes_get_short_le(buf + offset);
    offset += 2;
    offset += 5;    /* 5 zero bytes */
    NEED(offset, 8);
    int64_t id = bytes_get_long_le(buf + offset);
    offset += 8;
    if (size < 0) {
        return err_set(e, ERR_FORMAT, "StreamFormatException", "Bad Node size, %d.", (int) size);
    }
    NEED(offset, (int64_t) 16 * size);

    init_node(out, NODE_KEY, spos, buf + firstOffset);
    out->id = id;
    out->prev_pos = prevPos;
    out->leaf = isSegmentLeaf;
    out->n = size;
    return ERR_OK;
}

enum err_code sn_parse_value(const uint8_t *buf, int32_t len, int32_t offset, int64_t spos,
        struct sn_node *out, struct err *e) {
    const int32_t firstOffset = offset;
    offset += 4;    /* Skips byte size. */
    NEED(offset, 1);
    int8_t type = j_l2b(buf[offset]);
    offset += 1;
    if (type != NODE_VALUE && type != NODE_DELETE) {
        return err_set(e, ERR_FORMAT, "Bug", "Bad node type byte, %d, should have been checked"
                " already.", (int) type);
    }
    NEED(offset, 1);
    int8_t version = j_l2b(buf[offset]);
    offset += 1;
    if (version != 4) {
        return err_set(e, ERR_FORMAT, "VersioningStreamException",
                "Cannot parse value node of format version %d.", (int) version);
    }
    offset += 2;    /* the checksum, checked before */

    NEED(offset, 8);
    int64_t id = bytes_get_long_le(buf + offset);
    offset += 8;
    NEED(offset, 4);
    int32_t offsetFromTrans = bytes_get_int_le(buf + offset);
    offset += 4;

    const uint8_t *value = NULL;
    int32_t valueSize = -1;
    if (type == NODE_VALUE) {
        NEED(offset, 4);
        valueSize = bytes_get_int_le(buf + offset);
        offset += 4;
        if (valueSize < 0) {
            return err_set(e, ERR_FORMAT, "NegativeArraySizeException", "%d", (int) valueSize);
        }
        NEED(offset, valueSize);
        value = buf + offset;
        offset += valueSize;
    }

    NEED(offset, 4);
    int32_t keySize = bytes_get_int_le(buf + offset);
    offset += 4;
    if (keySize % 8 != 0 || keySize <= 0) {
        return err_set(e, ERR_FORMAT, "StreamFormatException", "Bad key size when reading value"
                " node at spos %lld, keySize: %d.", (long long) spos, (int) keySize);
    }
    NEED(offset, keySize);
    const uint8_t *key = buf + offset;
    offset += keySize;

    /* The stored offset is in the record's bytes (005-34). */
    int64_t tpos;
    if (rs_get_start_spos(spos, offsetFromTrans, &tpos, e) != ERR_OK) {
        return err_set(e, ERR_FORMAT, "StreamFormatException", "Bad offset from transaction, "
                "%d, of value node at spos %lld.", (int) offsetFromTrans, (long long) spos);
    }

    init_node(out, type, spos, buf + firstOffset);
    out->id = id;
    out->stored_offset = offsetFromTrans;
    out->tpos = tpos;
    out->offset_from_trans = j_l2i(spos - tpos);
    out->value = value;
    out->value_len = valueSize;
    out->key_n = keySize / 8;
    out->key = key;
    return ERR_OK;
}

int64_t sn_skip_pos(const struct sn_node *n, int32_t i) {
    return bytes_get_long_le(n->bytes + 40 + 16 * i);
}

int64_t sn_skip_time(const struct sn_node *n, int32_t i) {
    return sn_skip_pos(n, i) == SPOS_NULL ? -1 : bytes_get_long_le(n->bytes + 48 + 16 * i);
}

int64_t sn_klong(const struct sn_node *n, int32_t i) {
    return bytes_get_long_le(n->bytes + 32 + 8 * i);
}

int64_t sn_ref(const struct sn_node *n, int32_t i) {
    return bytes_get_long_le(n->bytes + 32 + 8 * n->n + 8 * i);
}

int64_t sn_seg(const struct sn_node *n, int32_t i) {
    return bytes_get_long_le(n->key + 8 * i);
}
