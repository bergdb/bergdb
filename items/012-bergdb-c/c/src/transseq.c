/* transseq: ported from Java's TransSeq and StartupPos; see transseq.h. */
#include "transseq.h"
#include <assert.h>
#include <stddef.h>
#include "bytes.h"
#include "jsem.h"

struct ts_info *ts_info_new(struct mem *m) {
    struct ts_info *info = mem_zalloc(m, sizeof *info, MEM_STATE);
    return info;
}

enum err_code ts_info_add_node(struct ts_info *info, struct mem *m, void *node, int64_t id,
        int32_t type, struct err *e) {
    if (info->ndirty == info->cap) {
        int32_t c2 = info->cap == 0 ? 4 : 2 * info->cap;
        struct ts_node *n2 = mem_realloc(m, info->gotDirtyNodes,
                (size_t) info->cap * sizeof *n2, (size_t) c2 * sizeof *n2, MEM_STATE);
        if (n2 == NULL) {
            return err_set(e, ERR_NOMEM, "OutOfMemoryError", "a TransInfo's got-dirty nodes");
        }
        info->gotDirtyNodes = n2;
        info->cap = c2;
    }
    struct ts_node *x = &info->gotDirtyNodes[info->ndirty++];
    x->node = node;
    x->id = id;
    x->type = type;
    return ERR_OK;
}

void ts_info_free(struct ts_info *info, struct mem *m) {
    if (info == NULL) {
        return;
    }
    mem_free(m, info->gotDirtyNodes, (size_t) info->cap * sizeof *info->gotDirtyNodes,
            MEM_STATE);
    mem_free(m, info, sizeof *info, MEM_STATE);
}

void ts_info_free_chain(struct ts_info *info, struct mem *m) {
    while (info != NULL) {
        struct ts_info *next = info->next;
        ts_info_free(info, m);
        info = next;
    }
}

void ts_init(struct ts_seq *s, struct mem *m) {
    s->mem = m;
    s->first = NULL;
    s->last = NULL;
    s->size = 0;
    s->dirtyCount = 0;
    s->ownBytes = 0;
}

void ts_free(struct ts_seq *s) {
    ts_info_free_chain(s->first, s->mem);
    s->first = NULL;
    s->last = NULL;
    s->size = 0;
    s->dirtyCount = 0;
    s->ownBytes = 0;
}

bool ts_is_empty(const struct ts_seq *s) {
    return s->first == NULL;
}

int32_t ts_size(const struct ts_seq *s) {
    return s->size;
}

int64_t ts_span(const struct ts_seq *s) {
    return s->first == NULL ? 0 : s->last->tpos - s->first->tpos;
}

enum err_code ts_add(struct ts_seq *s, struct ts_info *info, struct err *e) {
    if (info == NULL) {
        return err_set(e, ERR_ARG, "IllegalArgumentException", "info == null not allowed");
    }

    if (ts_is_empty(s)) {
        s->first = info;
        s->last = info;
    } else {
        if (info->tpos <= s->last->tpos) {
            return err_set(e, ERR_ARG, "IllegalArgumentException",
                    "info.tpos <= last.tpos, %lld, %lld", (long long) info->tpos,
                    (long long) s->last->tpos);
        }
        s->last->next = info;
        s->last = info;
    }
    info->next = NULL;

    s->size += 1;
    s->dirtyCount += info->ndirty;
    s->ownBytes += info->ownBytes;
    return ERR_OK;
}

int64_t ts_pos_of_trans_before(const struct ts_seq *s, int64_t limit) {
    int64_t result = -1;        /* Spos.NULL */
    const struct ts_info *t = s->first;
    while (t != NULL && t->tpos < limit) {
        result = t->tpos;
        t = t->next;
    }
    return result;
}

int64_t ts_own_bytes(int64_t valueBytes) {
    return 48 + valueBytes;
}

int32_t ts_dither_fp(int64_t pos) {
    int64_t z = pos * J64(0x9E3779B97F4A7C15);
    z = (z ^ j_ushr64(z, 30)) * J64(0xBF58476D1CE4E5B9);
    z = (z ^ j_ushr64(z, 27)) * J64(0x94D049BB133111EB);
    return (int32_t) j_ushr64(z ^ j_ushr64(z, 31), 48);
}

int64_t ts_share_fp(int64_t D, int64_t o, int64_t O, int64_t S, int32_t sd) {
    if (j_ushr64(D, 32) != 0 || j_ushr64(o, 31) != 0 || j_ushr64(S, 47) != 0 || O < 1
            || sd < 1) {
        return INT64_MAX;
    }
    const int64_t p = D * o;
    const int64_t q = S << 16;
    const int64_t xHi = j_mulhi64(p, q);       /* the unsigned high word, as p, q >= 0 */
    const int64_t xLo = p * q;
    /* Y = X / O: xHi is below 2^62, so its signed division is the unsigned one. */
    const int64_t yHi = xHi / O;
    const int64_t yLo = ts_divlu(xHi % O, xLo, O);
    const int64_t qHi = yHi / sd;
    const int64_t qLo = ts_divlu(yHi % sd, yLo, sd);
    const int64_t max = D << 16;
    return qHi != 0 || j_cmpu64(qLo, max) > 0 ? max : qLo;
}

int64_t ts_divlu(int64_t u1, int64_t u0, int64_t v) {
    assert(v != 0 && j_cmpu64(u1, v) < 0);
    const int64_t b = INT64_C(1) << 32;         /* the number base, 32-bit digits */
    const int s = j_nlz64(v);                   /* 0 to 63 */
    v = j_shl64(v, s);                          /* normalized */
    const int64_t vn1 = j_ushr64(v, 32), vn0 = v & INT64_C(0xFFFFFFFF);
    const int64_t un32 = j_shl64(u1, s) | (s == 0 ? 0 : j_ushr64(u0, 64 - s));
    const int64_t un10 = j_shl64(u0, s);
    const int64_t un1 = j_ushr64(un10, 32), un0 = un10 & INT64_C(0xFFFFFFFF);

    int64_t q1 = j_divu64(un32, vn1);
    int64_t rhat = j_remu64(un32, vn1);
    while (q1 >= b || j_cmpu64(q1 * vn0, j_shl64(rhat, 32) + un1) > 0) {
        q1--;
        rhat += vn1;
        if (rhat >= b) {
            break;
        }
    }

    const int64_t un21 = j_shl64(un32, 32) + un1 - q1 * v;  /* below v, modulo 2^64 */
    int64_t q0 = j_divu64(un21, vn1);
    rhat = j_remu64(un21, vn1);
    while (q0 >= b || j_cmpu64(q0 * vn0, j_shl64(rhat, 32) + un0) > 0) {
        q0--;
        rhat += vn1;
        if (rhat >= b) {
            break;
        }
    }
    return j_shl64(q1, 32) + q0;
}

int64_t ts_take(struct ts_seq *s, int64_t currentSp, int64_t streamLength,
        int32_t startupDistance, int64_t recordOwnBytes, int64_t maxBytes, ts_cost_fn cost,
        void *ctx, struct ts_info **taken_out, int32_t *ntaken) {
    int64_t newSp = currentSp;
    struct ts_info *head = NULL;
    struct ts_info *tail = NULL;

    *taken_out = NULL;
    *ntaken = 0;
    if (ts_is_empty(s)) {
        return newSp;
    }

    assert(s->ownBytes > 0);    /* every record has own bytes, see ts_own_bytes() */
    /* The deadline: d_h, or the span of the section's transactions while
     * it is longer. */
    const int64_t twice = 2 * (int64_t) startupDistance;
    const int64_t span = ts_span(s);
    const int64_t hardSp = streamLength - (twice >= span ? twice : span);
    /* The share and the dither in units of 2^-16 (bergdb 005-79). */
    const int64_t share = ts_share_fp(s->dirtyCount, recordOwnBytes, s->ownBytes,
            streamLength - currentSp, startupDistance);
    const int64_t u = ts_dither_fp(streamLength);

    int64_t taken = 0;
    int64_t bytes = 0;

    while (s->first != NULL) {
        struct ts_info *first = s->first;
        const int32_t count = first->ndirty;

        /* Before the deadline, a transaction that does not fit in what is
         * left of the share is taken if the part that fits is larger than
         * u. In units of 2^-16. */
        if (first->tpos > hardSp && ((taken + count) << 16) > share
                && share - (taken << 16) <= u * count) {
            break;
        }

        if (maxBytes != INT64_MAX) {
            const int64_t c = cost(ctx, first);
            if (bytes + c > maxBytes) {
                break;
            }
            bytes += c;
        }

        newSp = first->tpos;

        /* The nodes go to the record: the caller's, from the chain. */
        taken += count;
        s->dirtyCount -= count;
        s->ownBytes -= first->ownBytes;
        s->first = first->next;
        s->size -= 1;

        first->next = NULL;
        if (tail == NULL) {
            head = first;
        } else {
            tail->next = first;
        }
        tail = first;
        *ntaken += 1;
    }

    if (s->first == NULL) {
        s->last = NULL;
    }

    *taken_out = head;
    return newSp;
}

/* java.util.zip.CRC32's update over n bytes: CRC-32 (IEEE 802.3, reflected,
 * polynomial 0xEDB88320), bit by bit; crc is the value inverted. */
static uint32_t crc32_update(uint32_t crc, const uint8_t *b, int n) {
    crc = ~crc;
    for (int i = 0; i < n; i++) {
        crc ^= b[i];
        for (int k = 0; k < 8; k++) {
            crc = (crc >> 1) ^ (UINT32_C(0xEDB88320) & (0u - (crc & 1u)));
        }
    }
    return ~crc;
}

/* MyChecksum.updateWithLong: the long's 8 bytes, little-endian. */
static uint32_t crc32_long(uint32_t crc, int64_t value) {
    uint8_t buffer[8];
    bytes_put_long_le(value, buffer);
    return crc32_update(crc, buffer, 8);
}

int64_t ts_checksum(const struct ts_seq *s) {
    uint32_t sum = 0;
    sum = crc32_long(sum, s->size);
    sum = crc32_long(sum, s->dirtyCount);
    sum = crc32_long(sum, s->ownBytes);

    for (const struct ts_info *info = s->first; info != NULL; info = info->next) {
        sum = crc32_long(sum, info->lastPos);
        sum = crc32_long(sum, info->tt);
        sum = crc32_long(sum, info->tpos);
        sum = crc32_long(sum, info->startupPos);
        sum = crc32_long(sum, info->ownBytes);

        for (int32_t i = 0; i < info->ndirty; i++) {
            uint8_t type = (uint8_t) info->gotDirtyNodes[i].type;  /* Checksum.update(int) */
            sum = crc32_update(sum, &type, 1);
            sum = crc32_long(sum, info->gotDirtyNodes[i].id);
        }
    }
    return (int64_t) sum;
}

void ts_visit_got_dirty_nodes(const struct ts_seq *s, int64_t limit, ts_visit_fn visit,
        void *ctx) {
    const struct ts_info *info = s->first;
    while (info != NULL && info->tpos <= limit) {
        for (int32_t i = 0; i < info->ndirty; i++) {
            visit(ctx, &info->gotDirtyNodes[i], info->tpos, info->lastPos);
        }
        info = info->next;
    }
}

enum err_code ts_startup_pos_init(struct ts_startup_pos *p, int64_t pos, struct err *e) {
    if (pos < 0) {
        return err_set(e, ERR_ARG, "IllegalArgumentException", "startupPos %lld",
                (long long) pos);
    }
    p->startupPos = pos;
    ts_startup_pos_release_for_evict(p);
    return ERR_OK;
}

int64_t ts_startup_pos_get(const struct ts_startup_pos *p) {
    return p->startupPos;
}

void ts_startup_pos_set(struct ts_startup_pos *p, int64_t pos) {
    assert(pos >= 0);
    p->startupPos = pos;
}

void ts_startup_pos_release_for_evict(struct ts_startup_pos *p) {
    p->evictPos = p->startupPos;
}
