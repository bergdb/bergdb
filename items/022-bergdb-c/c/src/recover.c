/* recover: RecoverableStream.recover with its fill; see recover.h. */
#include "recover.h"
#include <assert.h>
#include <inttypes.h>
#include <string.h>
#include "bytes.h"
#include "spos.h"

#define D META_BLOCK_DISTANCE
#define M META_BLOCK_SIZE

/* transHeaderFixBytes: the bytes that complete a record's size field and its
 * byte 4, when 1 to 4 of its bytes exist. Returns their number. */
static int32_t trans_header_fix_bytes(const uint8_t *existing, int32_t n, uint8_t *fix) {
    assert(n >= 1 && n < 5);
    int32_t bytesToAdd = 5 - n;
    uint8_t buffer[5] = { 0, 0, 0, 0, 0 };
    memcpy(buffer, existing, (size_t) n);
    int32_t sizeFromBuffer = bytes_get_int_le(buffer);
    bool existingSizeTooSmall = sizeFromBuffer < RS_MIN_TRANS_SIZE;
    fix[bytesToAdd - 1] = RS_TORN_HEADER_FILLER;
    for (int32_t i = 0; i < bytesToAdd - 1; i++) {
        fix[i] = existingSizeTooSmall && i == 0 ? 1 : 0;
    }
    return bytesToAdd;
}

/* appendZeros: through append without its checks, 10,000 bytes at a time. */
static enum err_code append_zeros(struct rs *r, int64_t zeroCount, struct err *e) {
    static const uint8_t zeros[10000];
    while (zeroCount > 0) {
        int32_t len = (int32_t) (zeroCount > (int64_t) sizeof zeros ? (int64_t) sizeof zeros
                : zeroCount);
        enum err_code rc = rs_append(r, zeros, len, false, e);
        if (rc != ERR_OK) {
            return rc;
        }
        zeroCount -= len;
    }
    return ERR_OK;
}

/* fixMetaBlockIfNeeded */
static enum err_code fix_meta_block_if_needed(struct rs *r, struct rs_recovery *plan,
        struct err *e) {
    int64_t size = stream_length(r->s);
    int32_t blockPos = (int32_t) (size % D);
    if (size > 0 && blockPos < M) {
        /* In the middle of a meta block, or at the position of one not begun
         * (005-27): the block filled out is invalid. */
        int32_t byteCount = M - blockPos;
        uint8_t fill[M];
        for (int32_t i = 0; i < byteCount; i++) {
            fill[i] = meta_fill_out_template(blockPos + i);
        }
        plan->meta_fill = byteCount;
        return stream_append(r->s, fill, byteCount, e);
    }
    return ERR_OK;
}

/* fixLastTransactionIfNeeded */
static enum err_code fix_last_transaction_if_needed(struct rs *r, int64_t spos,
        struct rs_recovery *plan, struct err *e) {
    enum err_code rc;
    plan->walk_from = spos;
    while (true) {
        int64_t remaining;
        rc = rs_remaining_trans_bytes(spos, stream_length(r->s), &remaining, e);
        if (rc != ERR_OK) {
            return rc;
        }
        if (remaining == 0) {
            break;      /* We are done! */
        }
        assert(remaining > 0);

        if (remaining < 5) {
            /* Special case, transaction header not completely written. */
            uint8_t existing[4];
            rc = rs_read(r->s, spos, existing, (int32_t) remaining, e);
            if (rc != ERR_OK) {
                return rc;
            }
            plan->torn_have = (int32_t) remaining;
            plan->header_fix_len = trans_header_fix_bytes(existing, (int32_t) remaining,
                    plan->header_fix);
            rc = rs_append(r, plan->header_fix, plan->header_fix_len, false, e);
            if (rc != ERR_OK) {
                return rc;
            }
            rc = rs_remaining_trans_bytes(spos, stream_length(r->s), &remaining, e);
            if (rc != ERR_OK) {
                return rc;
            }
        }

        uint8_t buffer[4];
        rc = rs_read(r->s, spos, buffer, 4, e);
        if (rc != ERR_OK) {
            return rc;
        }
        int32_t transSize = bytes_get_int_le(buffer);
        if (transSize < (4 + 1)) {      /* Java's "|| transSize > MAX_TRANS_SIZE" is never true */
            return err_set(e, ERR_FORMAT, "StreamFormatException", "Bad transaction size in db "
                    "stream, %d, spos %" PRId64 ". Stream length: %" PRId64, (int) transSize,
                    spos, stream_length(r->s));
        }

        if (remaining < transSize) {
            /* Bad last transaction, not enough stream space for it: zero fill. */
            plan->torn = spos;
            if (plan->header_fix_len == 0) {
                plan->torn_have = (int32_t) remaining;
            }
            plan->torn_size = transSize;
            plan->zero_fill = transSize - remaining;
            rc = append_zeros(r, transSize - remaining, e);
            if (rc != ERR_OK) {
                return rc;
            }
            break;      /* We are done! */
        }
        if (plan->header_fix_len > 0) {
            /* A header completed to a whole record (a size of 5): failed. */
            plan->torn = spos;
            plan->torn_size = transSize;
        }
        plan->last_whole = spos;
        spos = rs_get_spos(spos, transSize);
    }
    return ERR_OK;
}

enum err_code rcv_recover(struct rs *r, struct rs_recovery *plan, struct err *e) {
    memset(plan, 0, sizeof *plan);
    plan->last_whole = SPOS_NULL;
    plan->torn = SPOS_NULL;

    /* readLastValidMetaBlock, before anything is written (005-40); it also sets
     * the positions of the last valid block. */
    enum err_code rc = rs_use_last_valid_meta_block(r, e);
    if (rc != ERR_OK) {
        return rc;
    }
    plan->last_valid = r->meta;
    rc = rs_check_last_trans_spos(r->s, &plan->last_valid, e);     /* 019-34 */
    if (rc != ERR_OK) {
        return rc;
    }

    rc = fix_meta_block_if_needed(r, plan, e);
    if (rc != ERR_OK) {
        return rc;
    }

    /* metaBlock.setFromOtherMetaBlock(lastBlock): done above. */
    int64_t spos = meta_last_trans(&plan->last_valid) == SPOS_NULL ? M
            : meta_last_trans(&plan->last_valid);
    rc = fix_last_transaction_if_needed(r, spos, plan, e);
    plan->length_after = stream_length(r->s);
    return rc;
}
