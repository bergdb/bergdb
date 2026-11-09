/*
 * rstream: the framing, ported from Java's bergdb.storage.RecoverableStream,
 * its reading side (bergdb 012-06; 012-02, sections 2.3 and 4): positions
 * that skip the meta blocks, record bytes read across them, the meta
 * blocks read and searched, the record to walk from, an incomplete
 * creation, and recovery's plan, which says what Java's recover() would
 * append without appending it (the fill is written in 012-10). The appends
 * (012-09): struct rs, the stream with its in-memory meta block, and
 * rs_append, which frames a record around the meta blocks and writes each
 * block as soon as the record's bytes reach it. Prefix rs_.
 *
 * A record's bytes are its own, without the meta blocks between them; a
 * record's size and every offset in it count record bytes. The functions
 * that read return the stream's error as it is (Java wraps an IOException
 * in a StreamIoException: the same code here).
 */
#ifndef BERGDB_RSTREAM_H
#define BERGDB_RSTREAM_H

#include <stdbool.h>
#include <stdint.h>
#include "err.h"
#include "meta.h"
#include "stream.h"

#define RS_MIN_TRANS_SIZE 17            /* RecoverableStream.MIN_TRANS_SIZE, 16 + 1 */
#define RS_TRANS_ALIGNMENT 8            /* RecoverableStream.TRANS_ALIGNMENT */
#define RS_LAST_BYTE 10                 /* RecoverableStream.LAST_BYTE */
#define RS_TORN_HEADER_FILLER 4         /* RecoverableStream.TORN_HEADER_FILLER */
#define RS_MAX_TRANS_SIZE INT32_MAX     /* RecoverableStream.MAX_TRANS_SIZE */

/* getSpos: the position of record byte 'size' of a record at 'start'; a
 * byte that would fall at a multiple of 200,000 falls after the meta block
 * there. getSpos(start, size) is the next record's position. */
int64_t rs_get_spos(int64_t start, int64_t size);

/* getStartSpos, the inverse (005-34): the start of the record whose byte
 * 'size' is at 'spos'. ERR_ARG ("IllegalArgumentException") if spos is
 * negative or in a meta block, or the record would start before the
 * stream's first record byte, or size is negative. */
enum err_code rs_get_start_spos(int64_t spos, int64_t size, int64_t *out, struct err *e);

/* getTransPos: the record bytes before position spos. */
int64_t rs_trans_pos(int64_t spos);

/* getRemainingTransBytes: the record bytes from spos to the end of a stream
 * of length 'stream_size'. ERR_ARG if spos is past it. */
enum err_code rs_remaining_trans_bytes(int64_t spos, int64_t stream_size, int64_t *out,
        struct err *e);

/* getNextSpos: where the next record of a stream of this length begins:
 * after the meta block, if the length is in one. */
int64_t rs_next_spos(int64_t length);

/* read: 'size' record bytes from position pos into buf, the meta blocks
 * skipped; a pos in a meta block reads from the block's end. */
enum err_code rs_read(struct stream *s, int64_t pos, uint8_t *buf, int32_t size,
        struct err *e);

/* readMetaBlock: the block at block_pos, valid or not. Its magic bytes must
 * be "berg" (ERR_FORMAT, "BadMagicBytes") and its version, an int at bytes
 * 4 to 7, 154 (ERR_FORMAT, "VersioningStreamException"; bytes 4 and 5 only
 * until bergdb 019-01, release 2026.3), checked before the rest is read. */
enum err_code rs_read_meta_block(struct stream *s, int64_t block_pos, struct meta *out,
        struct err *e);

/* readAValidMetaBlock: the last valid block at or before spos, and not
 * before the stream's first position; its format checked
 * (meta_check_format). *found is false if there is none. */
enum err_code rs_read_a_valid_meta_block(struct stream *s, int64_t spos, struct meta *out,
        bool *found, struct err *e);

/* readLastValidMetaBlock: the last valid block that is complete in the
 * stream (at or before length - 128), as above. */
enum err_code rs_read_last_valid_meta_block(struct stream *s, struct meta *out, bool *found,
        struct err *e);

/* getPosOfTransCompletedBefore (005-39): the record to walk from to reach
 * spos: the one named by the last valid block at or before spos; in a cut
 * stream, the first valid block from there on that names a record at or
 * after the first position. lastTrans -1 means the first record, 128, or
 * SPOS_NULL if the stream is not longer than 128. ERR_FORMAT
 * ("StreamFormatException") if no valid block names a record at or after
 * the first position. */
enum err_code rs_pos_of_trans_completed_before(struct stream *s, int64_t spos, int64_t *out,
        struct err *e);

/* isIncompleteCreation (005-33): whether the stream holds a creation that a
 * crash cut, and no committed record (012-02, 4.5). Only reads. */
enum err_code rs_is_incomplete_creation(struct stream *s, int64_t creation_length, bool *out,
        struct err *e);

/* Db.refuseOtherNodeSize (005-50), which a start runs before it writes: the
 * last valid meta block's maximum node size must be the start's. None (no
 * valid block): ERR_OK, as recovery refuses it; 0, a block written before
 * 2026-10-27: ERR_FORMAT, "VersioningStreamException"; another size:
 * ERR_FORMAT, "StreamFormatException". */
enum err_code rs_check_node_size(struct stream *s, int32_t max_node_size, struct err *e);

/* What Java's RecoverableStream.recover() would do to the stream, found
 * without writing (012-02, 4.4). The fill itself is 012-10's. */
struct rs_recovery {
    struct meta last_valid;     /* the last valid meta block; recovery's in-memory block
                                   becomes a copy of it */
    int32_t meta_fill;          /* fixMetaBlockIfNeeded: the bytes that complete a meta
                                   block that the end cuts (or is at): the fill-out
                                   template's from offset 128 - meta_fill; 0 if none */
    int64_t walk_from;          /* the record that the block names (128 if -1) */
    int64_t last_whole;         /* the last record of the walk that is whole, committed or
                                   not; SPOS_NULL if none */
    int64_t torn;               /* the record that the end cuts, or SPOS_NULL */
    int32_t torn_have;          /* its record bytes in the stream */
    int32_t header_fix_len;     /* the bytes that complete its size field and byte 4
                                   (transHeaderFixBytes), 0 to 4 */
    uint8_t header_fix[4];
    int32_t torn_size;          /* its size, with the header fix */
    int64_t zero_fill;          /* the zeros appended after it (appendZeros) */
    int64_t length_after;       /* the stream's length after recover(), its meta blocks
                                   counted */
};

/* checkLastTransSpos (bergdb 019-34, as Java's since release 2026.3): the
 * last transaction that block, the last valid one, names is SPOS_NULL, or
 * from the first transaction byte (and the stream's first position) up to
 * the block, as a valid meta block names a transaction written before it;
 * else ERR_FORMAT, "StreamFormatException", which names the block and the
 * position. Unaligned positions are taken: this layer does not align
 * records. Called before recovery writes anything; before, a position past
 * the stream's end gave the walk's IllegalArgumentException. */
enum err_code rs_check_last_trans_spos(struct stream *s, const struct meta *block,
        struct err *e);

/* The plan of recover(): readLastValidMetaBlock (none: ERR_FORMAT, "Could
 * not find *any* valid meta block"), checkLastTransSpos (bergdb 019-34,
 * release 2026.3: the block's lastTrans SPOS_NULL or from the first
 * transaction byte up to the block, else ERR_FORMAT,
 * "StreamFormatException"), fixMetaBlockIfNeeded, and
 * fixLastTransactionIfNeeded's walk by the records' sizes from the block's
 * lastTrans, with its refusals ("Bad transaction size", ERR_FORMAT; a walk
 * past the end, ERR_ARG). NodeStream.recover's check of a stream shorter
 * than 128 bytes is the caller's. */
enum err_code rs_plan_recovery(struct stream *s, struct rs_recovery *r, struct err *e);

/* RecoverableStream's appending side: the stream and the in-memory meta
 * block (RecoverableStream.metaBlock), whose bytes every block written
 * has, as they are at that moment. Its fields are set by the database:
 * the creation sets the id, the startup distance, the node size and the
 * time (Db.writePrimordialTransaction); each record its lastTrans, after
 * its append (rs_append_record); setStartupDistance the startup distance;
 * a start makes it a copy of the last valid block
 * (rs_use_last_valid_meta_block) and sets lastTrans to the last committed
 * record. */
struct rs {
    struct stream *s;
    struct meta meta;
    int64_t posOfLastValidMetaBlock;            /* -1 until known */
    int64_t lastTransSposOfLastValidMetaBlock;  /* -1 until known */
};

/* RecoverableStream(aos, new MetaBlock()): the block as meta_init makes it
 * (magic, version, last byte 10, lastTrans -1, the rest 0). */
void rs_init(struct rs *r, struct stream *s);

/* RecoverableStream.append: the record's 'size' bytes appended, a meta
 * block written each time they reach a multiple of 200,000 (also when the
 * record ends there: "size >= distanceToMeta"; and first, before any byte,
 * when the stream's length is at a multiple, as for the creation at 0).
 * With useChecks (always, for a record): the last byte must be 10 and the
 * size field (at buf[0], as Java reads it at 0 whatever the offset) the
 * size (ERR_ARG, "IllegalArgumentException"), and the stream must not end
 * inside a meta block (ERR_FORMAT, "StreamFormatException"), checked
 * before anything is written. The stream's errors as they are (Java's
 * StreamIoException: ERR_IO). */
enum err_code rs_append(struct rs *r, const uint8_t *buf, int32_t size, bool useChecks,
        struct err *e);

/* The tail of NodeStream.appendNodes, for a record serialized at
 * rs_next_spos(length): appended with the checks, then the in-memory
 * block's lastTrans set to its position, *tpos. */
enum err_code rs_append_record(struct rs *r, const uint8_t *buf, int32_t size, int64_t *tpos,
        struct err *e);

/* Recovery's steps 1 and 3 (RecoverableStream.recover, 012-02, 4.4)
 * without the fill (012-10): readLastValidMetaBlock, which also sets the
 * two positions above, and the in-memory block a copy of it
 * (setFromOtherMetaBlock), its reserved bytes included. None: ERR_FORMAT,
 * "StreamFormatException", "Could not find *any* valid meta block". */
enum err_code rs_use_last_valid_meta_block(struct rs *r, struct err *e);

#endif
