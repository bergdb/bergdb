/*
 * snode: the stored nodes, parsed as Java parses them (bergdb 012-06;
 * 012-02, section 6): NodeStream.bytesToNode, which checks the checksum
 * and the type, and StoredTopNode.parse, StoredKeyNode.parse and
 * StoredValueNode.parse, with their checks in their order. Prefix sn_.
 *
 * A parsed node is a plain struct, a view into the bytes it was parsed
 * from: its fixed fields decoded, its arrays (skip pointers, klongs and
 * refs, a value, a key's segments) read from the bytes by the accessors
 * below. It owns nothing and is valid while the bytes are. 012-07 makes
 * its in-memory nodes from it (decided in 012-06, section 5 of its file).
 *
 * The parsers read within the buffer they are given, as Java reads within
 * its array: a record's bytes in StoredTrans's parser, so that a field
 * past a node's size field but within the record is read as Java reads it.
 * A read past the buffer is refused (ERR_FORMAT,
 * "ArrayIndexOutOfBoundsException"), where Java throws it.
 */
#ifndef BERGDB_SNODE_H
#define BERGDB_SNODE_H

#include <stdbool.h>
#include <stdint.h>
#include "err.h"

#define NODE_TOP 10             /* Node.TYPE_TOP_NODE */
#define NODE_KEY 20             /* Node.TYPE_KEY_NODE */
#define NODE_VALUE 30           /* Node.TYPE_VALUE */
#define NODE_DELETE 40          /* Node.TYPE_DELETE */

#define SN_TOP_ID_OFFSET 16     /* StoredTopNode.ID_OFFSET */
#define SN_KEY_ID_OFFSET 24     /* StoredKeyNode.ID_OFFSET */
#define SN_VALUE_ID_OFFSET 8    /* StoredValueNode.ID_OFFSET */
#define SN_VALUE_MIN_SIZE 24    /* StoredValueNode.MIN_SIZE: the header, the id, the offset
                                   from the transaction, a size (015-07) */

/* TopNode.MAX_TOP_NODE_ID_VALUE, 2^48 - 1 */
#define SN_MAX_ORDINAL ((INT64_C(1) << 48) - 1)

struct sn_node {
    int32_t type;               /* NODE_TOP, NODE_KEY, NODE_VALUE or NODE_DELETE */
    int64_t spos;               /* the node's position */
    int64_t id;
    const uint8_t *bytes;       /* the node's first byte (its size field) */
    int32_t size;               /* its size field, which the parsers do not check */

    /* A top node (StoredTopNode.parse; TopNode). */
    int64_t ordinal;            /* TopNode.topNodeId, bytes 10 to 15 */
    int64_t root_time;
    int64_t root;               /* the root pointer's reference */
    int32_t h;                  /* the skip pointers: sn_skip_pos, sn_skip_time */

    /* A key node (StoredKeyNode.parse; KeyNode). */
    int64_t prev_pos;
    bool leaf;                  /* KeyNode.isSegmentLeaf */
    int32_t n;                  /* the klongs and refs: sn_klong, sn_ref */

    /* A value or delete node (StoredValueNode.parse; ValueNode). */
    int32_t stored_offset;      /* the offset in its record's bytes, as stored */
    int64_t tpos;               /* its record's position, from that offset */
    int32_t offset_from_trans;  /* ValueNode.offsetFromTrans: spos - tpos */
    const uint8_t *value;       /* the value's bytes; NULL for a delete */
    int32_t value_len;          /* -1 for a delete */
    int32_t key_n;              /* the key's segments: sn_seg */
    const uint8_t *key;
};

/* NodeStream.bytesToNode: the node at buf[offset] with the size field
 * 'size', at stream position spos, in a buffer of len bytes. The checksum
 * first (Fletcher-16 over the node's size bytes, its bytes 6 and 7 as 0:
 * ERR_FORMAT, "StreamChecksumException"), then the type (10, 20, 30 or 40,
 * else "StreamFormatException", "Bad node type"), then the node's parser. */
enum err_code sn_bytes_to_node(int64_t spos, const uint8_t *buf, int32_t len, int32_t offset,
        int32_t size, struct sn_node *out, struct err *e);

/* StoredTopNode.parse: the format 2 (else "VersioningStreamException");
 * h, a signed byte, not negative; the size field 40 + 16 h and within the
 * buffer, before the arrays ("StreamFormatException", bergdb 015-07, release
 * 2026.2); the ordinal at most 2^48 - 1; the root time 0 to 2^56 - 1; the
 * root pointer not negative; the size field again after the arrays (Java's
 * assert, a check with -ea: "AssertionError"); h the ordinal's bit length;
 * a skip pointer set exactly at the ordinal's set bits. */
enum err_code sn_parse_top(const uint8_t *buf, int32_t len, int32_t offset, int64_t spos,
        struct sn_node *out, struct err *e);

/* StoredKeyNode.parse: the size field at least 32 and within the buffer
 * (015-07); the format 2; prevPos a position or -1; the leaf byte 0 or 1;
 * n, a signed short, not negative and within the size field ("Bad key
 * count", 015-07), checked after the id is read, as Java does. */
enum err_code sn_parse_key(const uint8_t *buf, int32_t len, int32_t offset, int64_t spos,
        struct sn_node *out, struct err *e);

/* StoredValueNode.parse, for a value and a delete node: the size field at
 * least SN_VALUE_MIN_SIZE and within the buffer; the format 4; a value's
 * length not negative and within the size field, with room for the key's
 * size ("Bad value size"); the key size a positive multiple of 8 within the
 * size field; the stored offset one that getStartSpos takes ("Bad offset
 * from transaction"). Each a "StreamFormatException"; the sizes against the
 * node's since bergdb 015-07 (release 2026.2; before, a negative value
 * length was a "NegativeArraySizeException" and the others were checked
 * against the buffer only). */
enum err_code sn_parse_value(const uint8_t *buf, int32_t len, int32_t offset, int64_t spos,
        struct sn_node *out, struct err *e);

/* A top node's skip pointer i (0 to h - 1), as TopNode holds it: its
 * reference, or -1 if unset; its time, -1 if unset. */
int64_t sn_skip_pos(const struct sn_node *n, int32_t i);
int64_t sn_skip_time(const struct sn_node *n, int32_t i);

/* A key node's klong i and its reference (0 to n - 1). */
int64_t sn_klong(const struct sn_node *n, int32_t i);
int64_t sn_ref(const struct sn_node *n, int32_t i);

/* A value or delete node's key segment i (0 to key_n - 1). */
int64_t sn_seg(const struct sn_node *n, int32_t i);

#endif
