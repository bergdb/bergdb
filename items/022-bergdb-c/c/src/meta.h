/*
 * meta: the meta block, ported from Java's bergdb.storage.MetaBlock
 * (bergdb 012-06; 012-02, section 3). 128 bytes at every multiple of
 * 200,000, little-endian:
 *
 *   0   4  magic, "berg"
 *   4   4  version, 154, an int (read as an unsigned short until 019-01)
 *   8   8  time, the creation's
 *  16   8  lastTrans: the last record appended before the block, or -1
 *  24  16  the database id
 *  40   4  the startup distance
 *  44   2  the maximum node size, unsigned (005-50; 0 before it)
 *  46  81  reserved, zero
 * 127   1  the last byte: 10 for a valid block
 *
 * The block's bytes are kept whole, as Java keeps them, so that a copy
 * passes the reserved bytes on (MetaBlock.setFromOtherMetaBlock).
 * Prefix meta_.
 */
#ifndef BERGDB_META_H
#define BERGDB_META_H

#include <stdbool.h>
#include <stdint.h>
#include "err.h"

#define META_BLOCK_SIZE 128            /* RecoverableStream.META_BLOCK_SIZE */
#define META_BLOCK_DISTANCE 200000     /* RecoverableStream.META_BLOCK_DISTANCE */
#define META_VERSION_154 154           /* MetaBlock.VERSION_154, CURRENT_VERSION */
#define META_LAST_BYTE 10              /* MetaBlock.META_BLOCK_LAST_BYTE */

struct meta {
    uint8_t block[META_BLOCK_SIZE];
    int64_t pos;            /* the block's position, or -1 if not applicable */
};

/* MetaBlock(): the magic bytes, the version, the last byte 10, lastTrans
 * -1, the rest zero; pos -1. */
void meta_init(struct meta *mb);

/* MetaBlock(byte[] block, long pos): a copy of the 128 bytes at b. */
void meta_from_bytes(struct meta *mb, const uint8_t *b, int64_t pos);

/* MetaBlock.isValid: the last byte is 10. */
bool meta_is_valid(const struct meta *mb);

/* MetaBlock.checkFormat: for a valid block, the magic bytes ("Illegal first
 * bytes of block"), lastTrans -1 or not negative, the time not negative;
 * an invalid block is not checked. ERR_FORMAT, "StreamFormatException". */
enum err_code meta_check_format(const struct meta *mb, struct err *e);

int32_t meta_version(const struct meta *mb);           /* an int at 4 (019-01) */
int64_t meta_time(const struct meta *mb);
int64_t meta_last_trans(const struct meta *mb);
const uint8_t *meta_id(const struct meta *mb);         /* 16 bytes */
int32_t meta_startup_distance(const struct meta *mb);
int32_t meta_max_node_size(const struct meta *mb);     /* unsigned short at 44 */

void meta_set_time(struct meta *mb, int64_t time);
void meta_set_last_trans(struct meta *mb, int64_t spos);
void meta_set_id(struct meta *mb, const uint8_t id[16]);
void meta_set_startup_distance(struct meta *mb, int32_t startup_distance);
/* Refuses (false, nothing written) a size outside 0 to 65535, where Java's
 * Bytes.ushortToBytesLE throws IllegalArgumentException. */
bool meta_set_max_node_size(struct meta *mb, int32_t max_node_size);

/* MetaBlock.beginsAsBlock: the first min(n, 8) bytes are the fill-out
 * template's, "berg" and 154 as an int (005-33; 6 bytes, the version an
 * unsigned short, until bergdb 019-01, release 2026.3). */
bool meta_begins_as_block(const uint8_t *bytes, int32_t n);

/* Byte i (0 to 127) of MetaBlock.FILL_OUT_TEMPLATE, the bytes that complete
 * a meta block cut by a crash (4.4): "berg", 154 as an int (the same bytes
 * as the unsigned short of before 019-01), zeros, the last byte 0. */
uint8_t meta_fill_out_template(int32_t i);

#endif
