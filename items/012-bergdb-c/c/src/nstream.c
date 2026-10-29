/* nstream: the reads of Java's NodeStream; see nstream.h. */
#include "nstream.h"
#include <string.h>
#include "bytes.h"
#include "jsem.h"
#include "rstream.h"
#include "spos.h"

void ns_buf_free(struct ns_buf *b, struct mem *m) {
    mem_free(m, b->p, (size_t) b->cap, MEM_BUFFER);
    b->p = NULL;
    b->cap = 0;
}

/* At least n bytes in b. */
static enum err_code ensure(struct ns_buf *b, struct mem *m, int64_t n, struct err *e) {
    if (b->cap >= n) {
        return ERR_OK;
    }
    uint8_t *p = mem_realloc(m, b->p, (size_t) b->cap, (size_t) n, MEM_BUFFER);
    if (p == NULL) {
        return err_set(e, ERR_NOMEM, "OutOfMemoryError", "a buffer of %lld bytes",
                (long long) n);
    }
    b->p = p;
    b->cap = n;
    return ERR_OK;
}

/* A read of n record bytes at pos would pass the end of the stream: the error that
 * the read gives, without the allocation of its buffer: RecoverableStream's
 * StreamIoException of the stream's EOFException (012-14, 7.4). */
static bool past_end(struct stream *s, int64_t pos, int64_t n, struct err *e) {
    if (rs_trans_pos(pos) + n <= rs_trans_pos(stream_length(s))) {
        return false;
    }
    err_set(e, ERR_IO, "StreamIoException", "EOFException: Cannot read %lld record bytes at "
            "%lld, past the end of"
            " the stream, %lld.", (long long) n, (long long) pos,
            (long long) stream_length(s));
    return true;
}

void ns_iter_init(struct ns_iter *it, struct stream *s, struct mem *m, int64_t start_pos,
        bool exact) {
    memset(it, 0, sizeof *it);
    it->s = s;
    it->m = m;
    it->start_pos = start_pos;
    it->exact = exact;
}

void ns_iter_free(struct ns_iter *it) {
    ns_buf_free(&it->buf, it->m);
}

enum err_code ns_iter_next(struct ns_iter *it, bool *has, struct err *e) {
    enum err_code rc;
    *has = false;
    while (true) {
        if (!it->started) {
            if (it->exact) {
                it->tpos = it->start_pos;
            } else {
                int64_t p;
                rc = rs_pos_of_trans_completed_before(it->s, it->start_pos, &p, e);
                if (rc != ERR_OK) {
                    return rc;
                }
                if (p == SPOS_NULL) {
                    return ERR_OK;      /* No valid transactions in stream. */
                }
                it->tpos = p;
            }
        } else {
            it->tpos = it->next_trans_pos;
        }

        if (it->tpos >= stream_length(it->s)) {
            return ERR_OK;
        }

        uint8_t sizeBytes[4];
        rc = rs_read(it->s, it->tpos, sizeBytes, 4, e);
        if (rc != ERR_OK) {
            return rc;
        }
        int32_t size = bytes_get_int_le(sizeBytes);
        if (size < 16 + 0 + 1) {
            return err_set(e, ERR_FORMAT, "StreamFormatException", "Bad transaction size, %d, "
                    "transPos=%lld, stream size: %lld, transCount=%lld", (int) size,
                    (long long) it->tpos, (long long) stream_length(it->s),
                    (long long) it->trans_count);
        }
        if (past_end(it->s, it->tpos, size, e)) {
            return e->code;
        }
        rc = ensure(&it->buf, it->m, size, e);
        if (rc != ERR_OK) {
            return rc;
        }
        rc = rs_read(it->s, it->tpos, it->buf.p, size, e);
        if (rc != ERR_OK) {
            return rc;
        }
        it->size = size;
        int8_t lastByte = j_l2b(it->buf.p[size - 1]);
        if (lastByte != 0 && lastByte != RS_LAST_BYTE) {
            return err_set(e, ERR_FORMAT, "StreamFormatException", "Bad lastByte: %d",
                    (int) lastByte);
        }
        it->trans_ok = lastByte != 0;
        it->last_pos = rs_get_spos(it->tpos, size - 1);
        it->next_trans_pos = rs_get_spos(it->tpos, size);
        it->started = true;
        if (!it->trans_ok) {
            if (it->exact && it->tpos == it->start_pos) {
                return err_set(e, ERR_FORMAT, "StreamFormatException", "Transaction at start "
                        "pos %lld is not committed (its last byte is 0).", (long long) it->tpos);
            }
            continue;
        }
        it->trans_count++;
        it->trans_time = bytes_get_long_le(it->buf.p + 8);
        *has = true;
        return ERR_OK;
    }
}

enum err_code ns_read_node(struct stream *s, struct mem *m, int64_t spos, struct ns_buf *buf,
        struct sn_node *out, struct err *e) {
    enum err_code rc;
    uint8_t sizeBytes[4];
    if (spos < 128) {
        return err_set(e, ERR_ARG, "AssertionError", "bad spos, %lld", (long long) spos);
    }
    rc = rs_read(s, spos, sizeBytes, 4, e);
    if (rc != ERR_OK) {
        return rc;
    }
    int32_t size = bytes_get_int_le(sizeBytes);
    if (size <= 6) {
        return err_set(e, ERR_FORMAT, "StreamFormatException", "Bad node byte size, %d. At spos"
                " %lld.", (int) size, (long long) spos);
    }
    if (past_end(s, spos, size, e)) {
        return e->code;
    }
    int32_t length = size < 1024 ? 1024 : size;
    rc = ensure(buf, m, length, e);
    if (rc != ERR_OK) {
        return rc;
    }
    rc = rs_read(s, spos, buf->p, size, e);
    if (rc != ERR_OK) {
        return rc;
    }
    memset(buf->p + size, 0, (size_t) (length - size));
    return sn_bytes_to_node(spos, buf->p, length, 0, size, out, e);
}

enum err_code ns_read_node_header(struct stream *s, int64_t spos, int32_t *type, int64_t *id,
        struct err *e) {
    uint8_t buffer[32];
    enum err_code rc = rs_read(s, spos, buffer, 32, e);
    if (rc != ERR_OK) {
        return rc;
    }
    int8_t t = j_l2b(buffer[4]);
    if (t == NODE_TOP) {
        *id = bytes_get_long_le(buffer + SN_TOP_ID_OFFSET);
    } else if (t == NODE_KEY) {
        *id = bytes_get_long_le(buffer + SN_KEY_ID_OFFSET);
    } else if (t == NODE_VALUE || t == NODE_DELETE) {
        *id = bytes_get_long_le(buffer + SN_VALUE_ID_OFFSET);
    } else {
        static const char digits[] = "0123456789abcdef";
        char h[17];
        for (int i = 0; i < 8; i++) {
            h[2 * i] = digits[buffer[i] >> 4];
            h[2 * i + 1] = digits[buffer[i] & 15];
        }
        h[16] = '\0';
        return err_set(e, ERR_FORMAT, "StreamFormatException", "unknown node type, %d, spos: "
                "%lld, node header bytes: %s", (int) t, (long long) spos, h);
    }
    *type = t;
    return ERR_OK;
}

enum err_code ns_read_trans_bytes(struct stream *s, struct mem *m, int64_t tpos,
        struct ns_buf *buf, int32_t *size, struct err *e) {
    uint8_t sizeBytes[4];
    enum err_code rc = rs_read(s, tpos, sizeBytes, 4, e);
    if (rc != ERR_OK) {
        return rc;
    }
    int32_t n = bytes_get_int_le(sizeBytes);
    if (n <= 6) {
        return err_set(e, ERR_FORMAT, "StreamFormatException", "Bad transaction byte size, %d. "
                "At spos %lld.", (int) n, (long long) tpos);
    }
    if (past_end(s, tpos, n, e)) {
        return e->code;
    }
    rc = ensure(buf, m, n, e);
    if (rc != ERR_OK) {
        return rc;
    }
    rc = rs_read(s, tpos, buf->p, n, e);
    if (rc != ERR_OK) {
        return rc;
    }
    *size = n;
    return ERR_OK;
}
