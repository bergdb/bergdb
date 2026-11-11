/*
 * strans: a record parsed, ported from Java's StoredTrans.Parser
 * (bergdb 012-06; 012-02, section 5): the 32-byte header (size, format 5,
 * time, startupPos, topPos), the nodes (snode) until a node size of 0, the
 * got-dirty list, and lastPos, computed from what was parsed. The checks in
 * Java's order. The writer (StoredTrans.Serializer) comes in 012-09.
 * Prefix st_.
 *
 * The parsed record is a view into the record's bytes, as its nodes are
 * (snode.h): it is valid while the bytes are. Its array of nodes is
 * allocated through the allocator (MEM_BUFFER), kept and grown from one
 * parse to the next, and freed by st_free.
 */
#ifndef BERGDB_STRANS_H
#define BERGDB_STRANS_H

#include <stdint.h>
#include "err.h"
#include "mem.h"
#include "snode.h"

/* StoredTrans.RECORD_FORMAT: 6 since release 2026.4 (bergdb 023-07, section
 * 5.8; 022-07): a record's deletes are rerun with the upward unlink, the
 * empty key first, root collapse and the take-back (dag.c's delete_upward),
 * and a space split in place of a segment root that the transaction made
 * repoints the segment leaf's klong, so a record means another tree than in
 * format 5, which release 2026.3 and earlier wrote and which is refused. */
#define ST_RECORD_FORMAT 6
#define ST_MAX_RECORD_SIZE (INT32_MAX - 8)      /* StoredTrans.MAX_RECORD_SIZE */

struct st_record {
    int64_t tpos;               /* the record's position */
    int32_t size;               /* its size field, the content's (015-72) */
    int64_t tt;                 /* the transaction's time */
    int64_t startup_pos;
    int64_t top_pos;
    int64_t last_pos;           /* the position of its last byte, from what was parsed */
    struct sn_node *nodes;      /* its nodes, in order */
    int32_t nnodes;
    int32_t got_dirty_count;    /* the got-dirty pairs: st_got_dirty_id and _pos */
    const uint8_t *got_dirty;
    int32_t cap;                /* the nodes array's capacity */
};

/* An empty record, with no array. */
void st_init(struct st_record *r);

/* Frees the nodes array. */
void st_free(struct st_record *r, struct mem *m);

/* StoredTrans.Parser.parse: the record at tpos, its bytes buf[0] to
 * buf[len - 1] (len may exceed the record). Its checks, in order: len at
 * least 17 ("buffer too short"); tpos not negative and a multiple of 8
 * (ERR_ARG); the size field from 41 to len ("Bad transaction size in
 * header"); the format 5 ("VersioningStreamException", with Java's text of
 * StoredTrans.formatRefused); the nodes (sn_bytes_to_node) until a node
 * size of 0, each size from 8 to what is left of the record ("Bad node
 * size"), and the end marker within it ("Missing node end marker"); room
 * for the got-dirty count and the last byte, and the count 0 to (size -
 * offset - 1) / 16; room for the padding; the content's end, with the
 * padding, at the size field (bergdb 015-72, release 2026.3); lastPos 7
 * modulo 8 (Java's assert). Each a "StreamFormatException" but the
 * assert's. Within the record's size since bergdb 005-74 (release 2026.2):
 * before, within the buffer, and a node size below 0, which Java took (its
 * offset went back), was refused by C alone, as "none: C refuses". */
enum err_code st_parse(struct st_record *r, int64_t tpos, const uint8_t *buf, int32_t len,
        struct mem *m, struct err *e);

/* Db.checkStartupPos (bergdb 015-75, release 2026.3): refuses a parsed
 * record whose startupPos cannot be one that the take wrote: negative, not
 * a multiple of 8, in the first meta block (only 0 is), or after the
 * record's own position; a "StreamFormatException" that names the record,
 * the position and the problem. Before, Java asserted only that it was not
 * negative. */
enum err_code st_check_startup_pos(const struct st_record *r, struct err *e);

int64_t st_got_dirty_id(const struct st_record *r, int32_t i);
int64_t st_got_dirty_pos(const struct st_record *r, int32_t i);

/* StoredTrans.toString, into buf (n bytes, cut there): "tt:T, tpos:P,
 * lastPos:L, startupPos:S, topPos:O, nodeCount:N", and when the record has
 * got-dirty pairs a line "got dirty: " with each id and position followed
 * by a space. The start's refusals of the records' order and times end
 * with it, as Java's (bergdb 022-01, step 4). */
void st_to_string(const struct st_record *r, char *buf, size_t n);

/* StoredTrans.computeZeroCount: the zeros that pad n bytes to a multiple
 * of 8. */
int32_t st_compute_zero_count(int64_t n);

#endif
