/* strans: ported from Java's StoredTrans.Parser; see strans.h. */
#include "strans.h"
#include <inttypes.h>
#include <stdio.h>
#include <string.h>
#include "bytes.h"
#include "jsem.h"
#include "rstream.h"

#define AIOOBE "ArrayIndexOutOfBoundsException"
#define ST_STR_(x) #x
#define ST_STR(x) ST_STR_(x)

void st_init(struct st_record *r) {
    memset(r, 0, sizeof *r);
}

void st_free(struct st_record *r, struct mem *m) {
    mem_free(m, r->nodes, (size_t) r->cap * sizeof *r->nodes, MEM_BUFFER);
    r->nodes = NULL;
    r->cap = 0;
    r->nnodes = 0;
}

int32_t st_compute_zero_count(int64_t transSizeBefore) {
    const int32_t N = RS_TRANS_ALIGNMENT;
    int32_t result = (int32_t) (N - transSizeBefore % N);
    result = (result == 8) ? 0 : result;
    return result;
}

static enum err_code oob(struct err *e, int64_t off, int32_t len) {
    return err_set(e, ERR_FORMAT, AIOOBE, "Index %lld out of bounds for length %d",
            (long long) off, (int) len);
}

static bool in(int32_t len, int64_t off, int64_t n) {
    return off >= 0 && n >= 0 && off <= (int64_t) len - n;
}

static const char *formatRefused(int32_t v) {
    return v > ST_RECORD_FORMAT
            ? "A larger number is a database written by a newer version of BergDB."
            : "A smaller number is a database written by an older version of BergDB, which "
              "cannot be opened: format 5 was written by release 2026.3 and earlier "
              "(bergdb 023-07, section 5.8), format 2 until 2026-10-15 (bergdb 011-11, M18).";
}

enum err_code st_parse(struct st_record *r, int64_t tpos, const uint8_t *buffer, int32_t len,
        struct mem *m, struct err *e) {
    int32_t offset;
    enum err_code rc;

    r->nnodes = 0;
    r->got_dirty_count = 0;
    r->got_dirty = NULL;

    if (len < 16 + 1) {
        return err_set(e, ERR_FORMAT, "StreamFormatException", "buffer too short, %d",
                (int) len);
    }
    if (tpos < 0) {
        return err_set(e, ERR_ARG, "IllegalArgumentException", "transPos < 0, %lld",
                (long long) tpos);
    }
    if (tpos % RS_TRANS_ALIGNMENT != 0) {
        return err_set(e, ERR_ARG, "IllegalArgumentException", "bad transPos, %lld",
                (long long) tpos);
    }

    r->tpos = tpos;
    offset = 0;
    int32_t byteSize = bytes_get_int_le(buffer + offset);
    offset += 4;
    r->size = byteSize;
    /* Header, node end marker, got-dirty count and last byte (bergdb 005-74,
     * option A, as Java's since release 2026.2; before, only len < byteSize,
     * "buffer too small"). */
    if (byteSize < 32 + 4 + 4 + 1 || len < byteSize) {
        return err_set(e, ERR_FORMAT, "StreamFormatException", "Bad transaction size in "
                "header: %d, buffer size: %d.", (int) byteSize, (int) len);
    }

    int8_t version = j_l2b(buffer[offset]);
    offset++;
    if (version != ST_RECORD_FORMAT) {
        int32_t v = version & 0xff;
        return err_set(e, ERR_FORMAT, "VersioningStreamException", "Cannot parse stored "
                "transaction of format version %d; this version of BergDB reads format %d only."
                " %s", (int) v, ST_RECORD_FORMAT, formatRefused(v));
    }
    offset += 3;    /* three unused bytes */

    if (!in(len, offset, 24)) {
        return oob(e, len, len);
    }
    r->tt = bytes_get_long_le(buffer + offset);
    offset += 8;
    r->startup_pos = bytes_get_long_le(buffer + offset);
    offset += 8;
    r->top_pos = bytes_get_long_le(buffer + offset);
    offset += 8;

    /* The nodes: Parser.next until it gives null. Within the record's size
     * since bergdb 005-74 (release 2026.2): before, the end of the buffer
     * ended the nodes, and a negative size went back (C refused it). */
    while (true) {
        if (offset > byteSize - 4) {
            return err_set(e, ERR_FORMAT, "StreamFormatException", "Missing node end marker at "
                    "offset %d, transaction size %d.", (int) offset, (int) byteSize);
        }
        int32_t nodeSize = bytes_get_int_le(buffer + offset);
        if (nodeSize == 0) {
            offset += 4;
            break;
        }
        /* The common node header is 8 bytes; checked before parsing or
         * advancing. */
        if (nodeSize < 8 || nodeSize > byteSize - offset) {
            return err_set(e, ERR_FORMAT, "StreamFormatException", "Bad node size, %d, at offset "
                    "%d of transaction at %lld, size %d.", (int) nodeSize, (int) offset,
                    (long long) tpos, (int) byteSize);
        }
        if (r->nnodes == r->cap) {
            int32_t c2 = r->cap == 0 ? 16 : 2 * r->cap;
            struct sn_node *n2 = mem_realloc(m, r->nodes, (size_t) r->cap * sizeof *r->nodes,
                    (size_t) c2 * sizeof *r->nodes, MEM_BUFFER);
            if (n2 == NULL) {
                return err_set(e, ERR_NOMEM, "OutOfMemoryError", "the nodes of a record");
            }
            r->nodes = n2;
            r->cap = c2;
        }
        int64_t spos = rs_get_spos(tpos, offset);
        rc = sn_bytes_to_node(spos, buffer, len, offset, nodeSize, &r->nodes[r->nnodes], e);
        if (rc != ERR_OK) {
            return rc;
        }
        r->nnodes++;
        offset += nodeSize;
    }

    /* The got-dirty node ids. */
    if (offset > byteSize - 5) {
        return err_set(e, ERR_FORMAT, "StreamFormatException", "No room for gotDirtyCount and "
                "last byte.");
    }
    int32_t gotDirtyCount = bytes_get_int_le(buffer + offset);
    offset += 4;
    if (gotDirtyCount < 0 || gotDirtyCount > (byteSize - offset - 1) / 16) {
        return err_set(e, ERR_FORMAT, "StreamFormatException", "bad gotDirtyCount, %d",
                (int) gotDirtyCount);
    }
    r->got_dirty_count = gotDirtyCount;
    r->got_dirty = buffer + offset;
    offset += 16 * gotDirtyCount;

    /* Room for RecoverableStream.LAST_BYTE. */
    offset += 1;
    int32_t transSizeBefore = offset;
    int32_t count = st_compute_zero_count(transSizeBefore);
    if (count > byteSize - transSizeBefore) {
        return err_set(e, ERR_FORMAT, "StreamFormatException", "No room for transaction "
                "padding, size %d, required %lld.", (int) byteSize,
                (long long) ((int64_t) transSizeBefore + count));
    }
    int32_t transSize = transSizeBefore + count;
    /* The content fills the record exactly, as the serializer writes it (bergdb 015-72, as
     * Java's since release 2026.3): a size field larger than the content made the walk
     * skip the records it covered. */
    if (transSize != byteSize) {
        return err_set(e, ERR_FORMAT, "StreamFormatException", "The record at %lld ends at "
                "offset %d by its content, and its size says %d.", (long long) tpos,
                (int) transSize, (int) byteSize);
    }
    r->last_pos = rs_get_spos(tpos, transSize - 1);
    if (r->last_pos % RS_TRANS_ALIGNMENT != RS_TRANS_ALIGNMENT - 1) {
        return err_set(e, ERR_FORMAT, "AssertionError", "Bad lastPos: %lld, transSize:%d, "
                "transPos: %lld", (long long) r->last_pos, (int) transSize, (long long) tpos);
    }
    return ERR_OK;
}

enum err_code st_check_startup_pos(const struct st_record *r, struct err *e) {
    const int64_t sp = r->startup_pos;
    const char *problem;
    if (sp < 0) {
        problem = "negative";
    } else if (sp % RS_TRANS_ALIGNMENT != 0) {
        problem = "not a multiple of " ST_STR(RS_TRANS_ALIGNMENT);
    } else if (sp != 0 && sp < META_BLOCK_SIZE) {
        problem = "in the first meta block";
    } else if (sp > r->tpos) {
        problem = "after the record";
    } else {
        return ERR_OK;
    }
    return err_set(e, ERR_FORMAT, "StreamFormatException", "The record at %lld has startupPos "
            "%lld, %s.", (long long) r->tpos, (long long) sp, problem);
}

int64_t st_got_dirty_id(const struct st_record *r, int32_t i) {
    return bytes_get_long_le(r->got_dirty + 16 * i);
}

int64_t st_got_dirty_pos(const struct st_record *r, int32_t i) {
    return bytes_get_long_le(r->got_dirty + 16 * i + 8);
}

void st_to_string(const struct st_record *r, char *buf, size_t n) {
    int w = snprintf(buf, n, "tt:%" PRId64 ", tpos:%" PRId64 ", lastPos:%" PRId64 ", startupPos:%"
            PRId64 ", topPos:%" PRId64 ", nodeCount:%d", r->tt, r->tpos, r->last_pos,
            r->startup_pos, r->top_pos, (int) r->nnodes);
    if (r->got_dirty_count > 0 && w >= 0 && (size_t) w < n) {
        w += snprintf(buf + w, n - (size_t) w, "\ngot dirty: ");
        for (int32_t i = 0; i < r->got_dirty_count && w >= 0 && (size_t) w < n; i++) {
            w += snprintf(buf + w, n - (size_t) w, "%" PRId64 " %" PRId64 " ",
                    st_got_dirty_id(r, i), st_got_dirty_pos(r, i));
        }
    }
}
