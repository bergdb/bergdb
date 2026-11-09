/*
 * nstream: the reads of Java's bergdb.core.NodeStream (bergdb 012-06): the
 * trans iterator (NodeStream.TransIterator), the records in order from a
 * position; a node read by its position (readNode, readNodeHeader); a
 * record's bytes by its position (readTransBytes). Appends (appendNodes)
 * and recovery's fill come in 012-09 and 012-10. Prefix ns_.
 */
#ifndef BERGDB_NSTREAM_H
#define BERGDB_NSTREAM_H

#include <stdbool.h>
#include <stdint.h>
#include "err.h"
#include "mem.h"
#include "snode.h"
#include "stream.h"

/* A growable buffer of bytes, through the allocator (MEM_BUFFER). */
struct ns_buf {
    uint8_t *p;
    int64_t cap;
};

void ns_buf_free(struct ns_buf *b, struct mem *m);

/* NodeStream.TransIterator: the committed records from a start position.
 * Not exact: from the record that rs_pos_of_trans_completed_before gives
 * for it (005-39). Exact: from the position itself, where a committed
 * record must be (005-28). */
struct ns_iter {
    struct stream *s;
    struct mem *m;
    int64_t start_pos;
    bool exact;
    bool started;           /* a record has been read, committed or not */
    int64_t tpos;           /* the current record's position */
    int64_t last_pos;       /* the position of its last byte */
    int64_t next_trans_pos;
    int64_t trans_count;    /* committed records so far */
    int64_t trans_time;     /* the current record's time */
    bool trans_ok;
    int32_t size;           /* the current record's size: its bytes are buf.p[0..size) */
    struct ns_buf buf;
};

void ns_iter_init(struct ns_iter *it, struct stream *s, struct mem *m, int64_t start_pos,
        bool exact);

/* TransIterator.next: the next committed record, *has = true, its bytes in
 * it->buf.p and its position in it->tpos; or *has = false at the end.
 * Refused as Java refuses: a size below 17 ("Bad transaction size"), a
 * last byte neither 0 nor 10 ("Bad lastByte"), an exact start at a failed
 * record (ERR_FORMAT, "StreamFormatException"); a read past the end, the
 * stream's ERR_IO. A size larger than the record bytes left in the stream
 * is refused before its bytes are allocated, with the error that the read
 * would give. */
enum err_code ns_iter_next(struct ns_iter *it, bool *has, struct err *e);

void ns_iter_free(struct ns_iter *it);

/* NodeStream.readNode: the node at spos (at least 128, else ERR_FORMAT,
 * "StreamFormatException", "Bad node position": a check since bergdb 019-32,
 * release 2026.3, Java's assert before, ERR_ARG "AssertionError" in C); its
 * size field above 6 ("Bad node byte size"); its bytes read
 * into buf, at least 1,024 of them, zeros after the node, as Java's buffer;
 * parsed by sn_bytes_to_node. *out is a view into buf. */
enum err_code ns_read_node(struct stream *s, struct mem *m, int64_t spos, struct ns_buf *buf,
        struct sn_node *out, struct err *e);

/* NodeStream.readNodeHeader: the type and the id of the node at spos, from
 * its first 32 bytes (Java reads 32 whatever the node's size); a type that
 * is not a node's: "unknown node type". */
enum err_code ns_read_node_header(struct stream *s, int64_t spos, int32_t *type, int64_t *id,
        struct err *e);

/* NodeStream.readTransBytes: the record at tpos, its size field above 6
 * ("Bad transaction byte size"), its bytes into buf; *size is its size. */
enum err_code ns_read_trans_bytes(struct stream *s, struct mem *m, int64_t tpos,
        struct ns_buf *buf, int32_t *size, struct err *e);

/* NodeStream.checkReadSize(pos, size, length), the readers' check of a size
 * read from the stream (also for tests): true, and the StreamFormatException
 * ("Bad item byte size, ..."), if size is below 8, or pos is at or past the
 * length, or the size's last byte from pos is (rs_get_spos). */
bool ns_bad_read_size(int64_t pos, int32_t size, int64_t length, struct err *e);

#endif
