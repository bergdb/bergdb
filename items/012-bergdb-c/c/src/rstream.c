/* rstream: ported from Java's bergdb.storage.RecoverableStream, its reading
 * side; see rstream.h. */
#include "rstream.h"
#include <string.h>
#include "bytes.h"
#include "spos.h"

#define D META_BLOCK_DISTANCE
#define M META_BLOCK_SIZE

int64_t rs_get_spos(int64_t sposStart, int64_t size) {
    const int64_t startOffset = sposStart % D;
    const int64_t transBytesPerBlock = D - M;
    int64_t blockCount = size / transBytesPerBlock;
    const int64_t left = size - blockCount * transBytesPerBlock;

    if (startOffset + left >= D) {
        blockCount++;
    }

    return sposStart + size + blockCount * M;
}

int64_t rs_trans_pos(int64_t spos) {
    const int64_t blockCount = spos / D;
    const int64_t blockOffset = spos % D;
    int64_t result = blockCount * (D - M);
    result += blockOffset > M ? blockOffset - M : 0;
    return result;
}

enum err_code rs_get_start_spos(int64_t spos, int64_t size, int64_t *out, struct err *e) {
    const int64_t transBytesPerBlock = D - M;
    const int64_t transPos = rs_trans_pos(spos) - size;
    if (spos < 0 || spos % D < M || transPos < 0 || size < 0) {
        return err_set(e, ERR_ARG, "IllegalArgumentException",
                "No transaction start %lld transaction bytes before spos %lld.",
                (long long) size, (long long) spos);
    }
    *out = (transPos / transBytesPerBlock) * D + M + transPos % transBytesPerBlock;
    return ERR_OK;
}

enum err_code rs_remaining_trans_bytes(int64_t spos, int64_t streamSize, int64_t *out,
        struct err *e) {
    if (spos > streamSize) {
        return err_set(e, ERR_ARG, "IllegalArgumentException", "spos >= streamSize, %lld, %lld",
                (long long) spos, (long long) streamSize);
    }
    int64_t transPos1 = rs_trans_pos(spos);
    int64_t transPos2 = rs_trans_pos(streamSize);
    *out = transPos2 - transPos1;
    return ERR_OK;
}

int64_t rs_next_spos(int64_t length) {
    int32_t blockPos = (int32_t) (length % D);
    return blockPos < M ? length + (M - blockPos) : length;
}

enum err_code rs_read(struct stream *s, int64_t pos, uint8_t *buffer, int32_t size,
        struct err *e) {
    enum err_code rc;
    int32_t blockPos = (int32_t) (pos % D);

    if (blockPos >= 0 && blockPos < M) {
        /* If in meta block, position right after it. */
        pos += M - blockPos;
    }

    blockPos = (int32_t) (pos % D);
    int32_t distanceToMeta = D - blockPos;

    while (size >= distanceToMeta) {
        rc = stream_read(s, pos, buffer, distanceToMeta, e);
        if (rc != ERR_OK) {
            return rc;
        }
        size -= distanceToMeta;
        buffer += distanceToMeta;
        pos += distanceToMeta + M;
        distanceToMeta = D - M;
    }

    if (size > 0) {
        rc = stream_read(s, pos, buffer, size, e);
        if (rc != ERR_OK) {
            return rc;
        }
    }
    return ERR_OK;
}

static void hex(char *out, const uint8_t *b, int n) {
    static const char digits[] = "0123456789abcdef";
    for (int i = 0; i < n; i++) {
        out[2 * i] = digits[b[i] >> 4];
        out[2 * i + 1] = digits[b[i] & 15];
    }
    out[2 * n] = '\0';
}

enum err_code rs_read_meta_block(struct stream *s, int64_t blockPos, struct meta *out,
        struct err *e) {
    uint8_t header[6];
    uint8_t metaBytes[M];
    enum err_code rc = stream_read(s, blockPos, header, 6, e);
    if (rc != ERR_OK) {
        return rc;
    }
    if (!meta_begins_as_block(header, 4)) {
        char got[9];
        hex(got, header, 4);
        return err_set(e, ERR_FORMAT, "BadMagicBytes",
                "Expected magic bytes: 62657267, got: %s", got);
    }
    int32_t version = bytes_get_ushort_le(header + 4);
    if (version != META_VERSION_154) {
        return err_set(e, ERR_FORMAT, "VersioningStreamException",
                "Cannot read meta block with version %d. Version supported: %d", (int) version,
                META_VERSION_154);
    }
    rc = stream_read(s, blockPos, metaBytes, M, e);
    if (rc != ERR_OK) {
        return rc;
    }
    meta_from_bytes(out, metaBytes, blockPos);
    return ERR_OK;
}

enum err_code rs_read_a_valid_meta_block(struct stream *s, int64_t spos, struct meta *out,
        bool *found, struct err *e) {
    const int64_t metaIndex = spos / D;
    const int64_t firstIndex = (stream_first_pos(s) + D - 1) / D;

    *found = false;
    for (int64_t i = metaIndex; i >= firstIndex; i--) {
        int64_t blockPos = i * D;
        enum err_code rc = rs_read_meta_block(s, blockPos, out, e);
        if (rc != ERR_OK) {
            return rc;
        }
        if (meta_is_valid(out)) {
            rc = meta_check_format(out, e);
            if (rc != ERR_OK) {
                return rc;
            }
            *found = true;
            return ERR_OK;
        }
    }
    return ERR_OK;
}

enum err_code rs_read_last_valid_meta_block(struct stream *s, struct meta *out, bool *found,
        struct err *e) {
    int64_t spos = stream_length(s) - M;
    spos = spos < 0 ? 0 : spos;
    return rs_read_a_valid_meta_block(s, spos, out, found, e);
}

enum err_code rs_pos_of_trans_completed_before(struct stream *s, int64_t spos, int64_t *out,
        struct err *e) {
    const int64_t firstPos = stream_first_pos(s);
    struct meta meta;
    bool found;
    enum err_code rc = rs_read_a_valid_meta_block(s, spos, &meta, &found, e);
    if (rc != ERR_OK) {
        return rc;
    }
    int64_t blockPos = found ? meta.pos : (firstPos + D - 1) / D * D;

    for (; blockPos + M <= stream_length(s); blockPos += D) {
        rc = rs_read_meta_block(s, blockPos, &meta, e);
        if (rc != ERR_OK) {
            return rc;
        }
        if (!meta_is_valid(&meta)) {
            continue;
        }
        rc = meta_check_format(&meta, e);
        if (rc != ERR_OK) {
            return rc;
        }
        int64_t result = meta_last_trans(&meta);
        if (result == SPOS_NULL) {
            if (stream_length(s) <= M) {
                *out = SPOS_NULL;
                return ERR_OK;
            }
            result = M;     /* spos of very first transaction */
        }
        if (result >= firstPos) {
            *out = result;
            return ERR_OK;
        }
    }

    return err_set(e, ERR_FORMAT, "StreamFormatException", "No valid meta block names a "
            "transaction at or after the first position of the stream, %lld.",
            (long long) firstPos);
}

enum err_code rs_is_incomplete_creation(struct stream *s, int64_t creationLength, bool *out,
        struct err *e) {
    const int64_t length = stream_length(s);
    uint8_t block[M];
    enum err_code rc;

    *out = false;
    if (length == 0 || length > creationLength || stream_first_pos(s) > 0) {
        return ERR_OK;
    }
    int32_t n = (int32_t) (length < M ? length : M);
    rc = stream_read(s, 0, block, n, e);
    if (rc != ERR_OK) {
        return rc;
    }
    if (!meta_begins_as_block(block, n)) {
        return ERR_OK;      /* Not a BergDB stream, a wrong crypto key, or another version. */
    }
    if (length < M) {
        *out = true;
        return ERR_OK;
    }
    struct meta first;
    meta_from_bytes(&first, block, 0);
    if (!meta_is_valid(&first) || meta_last_trans(&first) != SPOS_NULL) {
        return ERR_OK;
    }

    const int64_t transBytes = length - M;
    if (transBytes < 4) {
        *out = true;        /* No transaction, or a part of its size. */
        return ERR_OK;
    }
    uint8_t sizeBytes[4];
    rc = stream_read(s, M, sizeBytes, 4, e);
    if (rc != ERR_OK) {
        return rc;
    }
    int32_t transSize = bytes_get_int_le(sizeBytes);
    if (transBytes != transSize) {
        *out = transBytes < transSize;      /* Cut; else more bytes follow it. */
        return ERR_OK;
    }
    uint8_t lastByte;
    rc = stream_read(s, length - 1, &lastByte, 1, e);
    if (rc != ERR_OK) {
        return rc;
    }
    *out = lastByte == 0;
    return ERR_OK;
}

enum err_code rs_check_node_size(struct stream *s, int32_t maxNodeSize, struct err *e) {
    struct meta last;
    bool found;
    enum err_code rc = rs_read_last_valid_meta_block(s, &last, &found, e);
    if (rc != ERR_OK) {
        return rc;
    }
    if (!found) {
        return ERR_OK;      /* recover() refuses it. */
    }
    const int32_t size = meta_max_node_size(&last);
    if (size == 0) {
        return err_set(e, ERR_FORMAT, "VersioningStreamException", "The database's meta block "
                "has no maximum node size: it was written by a version of BergDB before "
                "2026-10-27, which this one does not start (bergdb 005-50). The start has "
                "written nothing.");
    }
    if (size != maxNodeSize) {
        return err_set(e, ERR_FORMAT, "StreamFormatException", "The database's maximum node "
                "size is %d, and this start uses %d. A database must be started with the node "
                "size it was created with: %d. The start has written nothing (bergdb 005-50).",
                (int) size, (int) maxNodeSize, (int) size);
    }
    return ERR_OK;
}

/* The length of a stream of length 'len' after RecoverableStream.append of
 * n bytes, with the meta blocks it writes when the bytes reach their
 * positions (append's loop, without its checks). */
static int64_t length_after_append(int64_t len, int64_t n) {
    int32_t blockPos = (int32_t) (len % D);
    int64_t distanceToMeta = D - blockPos;
    if (blockPos == 0) {
        distanceToMeta = 0;     /* Special case */
    }
    while (n >= distanceToMeta) {
        len += distanceToMeta + M;
        n -= distanceToMeta;
        distanceToMeta = D - M;
    }
    return len + n;
}

/* transHeaderFixBytes: what completes the size field and byte 4 of a record
 * of which only 1 to 4 bytes exist. */
static int32_t trans_header_fix_bytes(const uint8_t *existing, int32_t n, uint8_t *fix) {
    uint8_t buffer[5] = { 0, 0, 0, 0, 0 };
    int32_t bytesToAdd = 5 - n;
    memcpy(buffer, existing, (size_t) n);
    int32_t sizeFromBuffer = bytes_get_int_le(buffer);
    bool existingSizeTooSmall = sizeFromBuffer < RS_MIN_TRANS_SIZE;
    fix[bytesToAdd - 1] = RS_TORN_HEADER_FILLER;
    for (int32_t i = 0; i < bytesToAdd - 1; i++) {
        fix[i] = existingSizeTooSmall && i == 0 ? 1 : 0;
    }
    return bytesToAdd;
}

enum err_code rs_plan_recovery(struct stream *s, struct rs_recovery *r, struct err *e) {
    enum err_code rc;
    bool found;

    memset(r, 0, sizeof *r);
    r->last_whole = SPOS_NULL;
    r->torn = SPOS_NULL;

    /* readLastValidMetaBlock, before anything is written (005-40). */
    rc = rs_read_last_valid_meta_block(s, &r->last_valid, &found, e);
    if (rc != ERR_OK) {
        return rc;
    }
    if (!found) {
        return err_set(e, ERR_FORMAT, "StreamFormatException", "Could not find *any* valid "
                "meta block. At least the very first meta block must be valid in a db stream.");
    }

    /* fixMetaBlockIfNeeded. */
    int64_t length = stream_length(s);
    int32_t blockPos = (int32_t) (length % D);
    if (length > 0 && blockPos < M) {
        r->meta_fill = M - blockPos;
        length += r->meta_fill;
    }

    /* fixLastTransactionIfNeeded, from the record the block names. */
    int64_t spos = meta_last_trans(&r->last_valid) == SPOS_NULL ? M
            : meta_last_trans(&r->last_valid);
    r->walk_from = spos;
    while (true) {
        int64_t remaining;
        uint8_t header[5];
        rc = rs_remaining_trans_bytes(spos, length, &remaining, e);
        if (rc != ERR_OK) {
            return rc;
        }
        if (remaining == 0) {
            break;      /* We are done! */
        }

        if (remaining < 5) {
            /* Special case, transaction header not completely written. */
            rc = rs_read(s, spos, header, (int32_t) remaining, e);
            if (rc != ERR_OK) {
                return rc;
            }
            r->header_fix_len = trans_header_fix_bytes(header, (int32_t) remaining,
                    r->header_fix);
            memcpy(header + remaining, r->header_fix, (size_t) r->header_fix_len);
            r->torn_have = (int32_t) remaining;
            length = length_after_append(length, r->header_fix_len);
            rc = rs_remaining_trans_bytes(spos, length, &remaining, e);
            if (rc != ERR_OK) {
                return rc;
            }
        } else {
            rc = rs_read(s, spos, header, 4, e);
            if (rc != ERR_OK) {
                return rc;
            }
        }

        int32_t transSize = bytes_get_int_le(header);
        if (transSize < (4 + 1)) {     /* Java's "|| transSize > MAX_TRANS_SIZE" is never true */
            return err_set(e, ERR_FORMAT, "StreamFormatException", "Bad transaction size in db "
                    "stream, %d, spos %lld. Stream length: %lld", (int) transSize,
                    (long long) spos, (long long) length);
        }

        if (remaining < transSize) {
            /* Bad last transaction: zero fill to correct. */
            r->torn = spos;
            if (r->header_fix_len == 0) {
                r->torn_have = (int32_t) remaining;
            }
            r->torn_size = transSize;
            r->zero_fill = transSize - remaining;
            length = length_after_append(length, r->zero_fill);
            break;      /* We are done! */
        }
        if (r->header_fix_len > 0) {
            /* A header completed to a whole record (a size of 5): failed, as its byte 4
             * is not 10, and whole. */
            r->torn = spos;
            r->torn_size = transSize;
        }

        r->last_whole = spos;
        spos = rs_get_spos(spos, transSize);
    }
    r->length_after = length;
    return ERR_OK;
}
