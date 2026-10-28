/* strans: ported from Java's StoredTrans.Parser; see strans.h. */
#include "strans.h"
#include <string.h>
#include "bytes.h"
#include "jsem.h"
#include "rstream.h"

#define AIOOBE "ArrayIndexOutOfBoundsException"

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
              "cannot be opened: format 2 was written until 2026-10-15 (bergdb 011-11, M18).";
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
    if (len < byteSize) {
        return err_set(e, ERR_FORMAT, "StreamFormatException", "buffer too small, size in "
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

    /* The nodes: Parser.next until it gives null. */
    while (true) {
        if (offset + 4 >= len) {
            break;
        }
        if (!in(len, offset, 4)) {
            return oob(e, offset, len);
        }
        int32_t nodeSize = bytes_get_int_le(buffer + offset);
        if (nodeSize == 0) {
            offset += 4;
            break;
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
        if (nodeSize < 0) {
            return err_set(e, ERR_FORMAT, "none: C refuses", "node size %d at offset %d of the"
                    " record at %lld: below 0, Java's parser goes back", (int) nodeSize,
                    (int) offset, (long long) tpos);
        }
        offset += nodeSize;
    }

    /* The got-dirty node ids. */
    if (!in(len, offset, 4)) {
        return oob(e, offset, len);
    }
    int32_t gotDirtyCount = bytes_get_int_le(buffer + offset);
    offset += 4;
    if (gotDirtyCount < 0 || gotDirtyCount > (len - offset) / 16) {
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
    int32_t transSize = transSizeBefore + count;
    r->last_pos = rs_get_spos(tpos, transSize - 1);
    if (r->last_pos % RS_TRANS_ALIGNMENT != RS_TRANS_ALIGNMENT - 1) {
        return err_set(e, ERR_FORMAT, "AssertionError", "Bad lastPos: %lld, transSize:%d, "
                "transPos: %lld", (long long) r->last_pos, (int) transSize, (long long) tpos);
    }
    return ERR_OK;
}

int64_t st_got_dirty_id(const struct st_record *r, int32_t i) {
    return bytes_get_long_le(r->got_dirty + 16 * i);
}

int64_t st_got_dirty_pos(const struct st_record *r, int32_t i) {
    return bytes_get_long_le(r->got_dirty + 16 * i + 8);
}
