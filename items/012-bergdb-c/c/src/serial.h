/*
 * serial: the record writer, ported from Java's bergdb.core.StoredTrans
 * .Serializer and NodeStream.appendNodes (bergdb 012-09; 012-02, sections 5
 * and 8.3 to 8.11). Prefix ser_. The parser is 012-06's (strans.h).
 *
 * A record is serialized whole, then appended in one call
 * (rs_append_record), which writes the meta blocks it reaches. First
 * prepareToSerialize: every node of the record gets its new position, in
 * the record's order (the top nodes, the key nodes, the value nodes), before
 * any byte is written, so that a node names the new position of a node
 * written after it in the same record; a key node's previous position is
 * kept for its prevPos field; a value node gets its offset from the record
 * (offsetFromTrans, its distance in the stream) and its position; the
 * record's size, with the end of nodes, the got-dirty pairs, the last byte
 * and the zeros that pad it to a multiple of 8, is compared with the record
 * limit (005-17: above it, ERR_LIMIT, Java's DbException). Then the header
 * (the size, format 5, the time, the startup position, topPos: the newest
 * written top node's position after prepareToSerialize), the top and key
 * nodes as longs (nwrite.h), the value nodes as bytes, the end of nodes, the
 * got-dirty pairs (each node's id and its position at that moment), the
 * zeros and the last byte, 10.
 *
 * The buffers (MEM_BUFFER) are kept and grown from one record to the next;
 * Java's shrinking every 97th record changes no byte and is left out.
 */
#ifndef BERGDB_SERIAL_H
#define BERGDB_SERIAL_H

#include <stdbool.h>
#include <stdint.h>
#include "err.h"
#include "mem.h"
#include "rstream.h"
#include "tnode.h"
#include "transnodes.h"
#include "transseq.h"

struct serial {
    struct mem *mem;
    int64_t *long_buffer;       /* the header, the top and key nodes, as longs */
    int32_t long_cap;
    uint8_t *byte_buffer;       /* the record */
    int64_t byte_cap;
    int64_t *prev_pos;          /* each key node's position before this record */
    int32_t prev_cap;
    int32_t total_size;         /* the record's size */
    int32_t extra_zeros;        /* the padding */
    int64_t trans_last_spos;    /* the position of the record's last byte */
    int64_t trans_next_spos;    /* the next record's position */
};

/* new Serializer(): nothing allocated until the first record. */
void ser_init(struct serial *s, struct mem *m);

/* Frees the buffers. */
void ser_free(struct serial *s);

/* What appendNodes gives (Trans's output fields). */
struct ser_out {
    int64_t tpos;
    int64_t last_pos;
    int64_t next_pos;
};

/* Serializer.serialize: the record of the transaction at time tt, for the
 * position trans_start_pos, into s->byte_buffer[0 .. s->total_size); the
 * positions of tn's nodes set (prepareToSerialize). ERR_LIMIT (the record
 * limit, "DbException"), ERR_NOMEM. */
enum err_code ser_serialize(struct serial *s, struct transnodes *tn, int64_t tt,
        int64_t trans_start_pos, int64_t startup_pos, const struct ts_info *got_dirty,
        const struct tnode *top, int64_t record_limit, struct err *e);

/* NodeStream.appendNodes: the record of the transaction at time tt, with
 * the nodes of tn, the startup position, the got-dirty nodes of
 * 'got_dirty' (struct node objects, TransInfo.gotDirtyNodes) and the newest
 * written top node 'top' (NULL: -1), serialized at the stream's next
 * position (rs_next_spos) and appended with the meta blocks it reaches;
 * then the in-memory block's lastTrans is its position. record_limit is
 * StoredTrans.recordLimit. Errors: ERR_LIMIT ("DbException": the record
 * limit), ERR_NOMEM, the append's (ERR_IO, ERR_FORMAT, ERR_ARG). The nodes'
 * positions are set before any check, as Java's. */
enum err_code ser_append_nodes(struct serial *s, struct rs *r, struct transnodes *tn, int64_t tt,
        int64_t startup_pos, const struct ts_info *got_dirty, const struct tnode *top,
        int64_t record_limit, struct ser_out *out, struct err *e);

#endif
