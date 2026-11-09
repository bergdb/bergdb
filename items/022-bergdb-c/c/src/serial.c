/* serial: the record writer; see serial.h. */
#include "serial.h"
#include <assert.h>
#include <string.h>
#include "bytes.h"
#include "jsem.h"
#include "klong.h"
#include "node.h"
#include "nwrite.h"
#include "spos.h"
#include "strans.h"

void ser_init(struct serial *s, struct mem *m) {
    memset(s, 0, sizeof *s);
    s->mem = m;
}

void ser_free(struct serial *s) {
    mem_free(s->mem, s->long_buffer, (size_t) s->long_cap * sizeof *s->long_buffer, MEM_BUFFER);
    mem_free(s->mem, s->byte_buffer, (size_t) s->byte_cap, MEM_BUFFER);
    mem_free(s->mem, s->prev_pos, (size_t) s->prev_cap * sizeof *s->prev_pos, MEM_BUFFER);
    s->long_buffer = NULL;
    s->byte_buffer = NULL;
    s->prev_pos = NULL;
    s->long_cap = s->prev_cap = 0;
    s->byte_cap = 0;
}

static enum err_code nomem(struct err *e) {
    return err_set(e, ERR_NOMEM, "OutOfMemoryError", "out of memory");
}

/* resizePrevPosIfNeeded: room for every key node's previous position. */
static bool resize_prev_pos(struct serial *s, int32_t keyCount) {
    if (s->prev_cap >= keyCount) {
        return true;
    }
    int32_t ncap = keyCount < 100 ? 100 : keyCount + keyCount / 5;
    int64_t *n = mem_alloc(s->mem, (size_t) ncap * sizeof *n, MEM_BUFFER);
    if (n == NULL) {
        return false;
    }
    mem_free(s->mem, s->prev_pos, (size_t) s->prev_cap * sizeof *s->prev_pos, MEM_BUFFER);
    s->prev_pos = n;
    s->prev_cap = ncap;
    return true;
}

/* resizeBuffersIfNeeded: the long buffer for the header and the top and key
 * nodes (longs longs), the byte buffer for the record (bytes). */
static bool resize_buffers(struct serial *s, int64_t longs, int64_t bytes) {
    if (s->long_cap < longs) {
        int64_t ncap = longs + longs / 5 + 16;
        int64_t *n = mem_alloc(s->mem, (size_t) ncap * sizeof *n, MEM_BUFFER);
        if (n == NULL) {
            return false;
        }
        mem_free(s->mem, s->long_buffer, (size_t) s->long_cap * sizeof *n, MEM_BUFFER);
        s->long_buffer = n;
        s->long_cap = (int32_t) ncap;
    }
    if (s->byte_cap < bytes) {
        int64_t ncap = bytes + bytes / 5 + 64;
        uint8_t *n = mem_alloc(s->mem, (size_t) ncap, MEM_BUFFER);
        if (n == NULL) {
            return false;
        }
        mem_free(s->mem, s->byte_buffer, (size_t) s->byte_cap, MEM_BUFFER);
        s->byte_buffer = n;
        s->byte_cap = ncap;
    }
    return true;
}

/* checkStreamPointersOfKeyNodes and checkStreamPointers, which Java runs with
 * assertions on (as C's asserts always are): after prepareToSerialize, no
 * key klong's reference is -1, no index node's position is -1 or a vpos,
 * and no stream pointer's reference is -1 or a vpos. */
static void check_stream_pointers(const struct transnodes *tn) {
    for (int32_t i = 0; i < tn->key_count; i++) {
        const struct knode *keyNode = tn->key_nodes[i];
        for (int32_t j = 0; j < keyNode->size; j++) {
            if (kl_get_type(keyNode->klongs[j]) == KL_TYPE_KEY) {
                int64_t spos = kn_get_serialized_ref(keyNode, j);
                assert(spos_is_valid(spos) && "Bad stream pointer of KeyNode");
                (void) spos;
            }
        }
    }
    for (int32_t k = 0; k < tn->top_count + tn->key_count; k++) {
        const struct node *node = tns_get(tn, k);
        assert(!spos_is_null(node->spos) && "Spos of node is NULL");
        assert(!spos_is_vpos(node->spos) && "Spos of index node is vpos");
        int32_t count = node_size(node);
        for (int32_t i = 0; i < count; i++) {
            struct pointer p;
            node_get_pointer(node, i, &p);
            if (!ptr_is_null(&p) && p.node == NULL) {
                int64_t spos = node_serialized_ref(node, i);
                assert(!spos_is_null(spos) && "spos of node pointer is NULL");
                assert(!spos_is_vpos(spos) && "spos of index node pointer is vpos");
                (void) spos;
            }
        }
    }
}

/* prepareToSerialize: the nodes' new positions, the size, the limit. */
static enum err_code prepare(struct serial *s, struct transnodes *tn, int64_t transStartPos,
        int32_t gotDirtyCount, int64_t recordLimit, struct err *e) {
    int64_t size = 32;  /* the header: size (4), format (4), time (8), startupPos (8),
                           topPos (8) */
    int64_t currentPos = rs_get_spos(transStartPos, size);

    if (!resize_prev_pos(s, tn->key_count)) {
        return nomem(e);
    }

    for (int32_t i = 0; i < tn->top_count; i++) {
        struct tnode *node = tn->top_nodes[i];
        node->n.spos = currentPos;
        size += nw_top_byte_size(node);
        currentPos = rs_get_spos(transStartPos, size);
    }

    int32_t prevPosIndex = 0;
    for (int32_t i = 0; i < tn->key_count; i++) {
        struct knode *node = tn->key_nodes[i];
        s->prev_pos[prevPosIndex++] = node->n.spos;
        node->n.spos = currentPos;
        size += nw_key_byte_size(node);
        currentPos = rs_get_spos(transStartPos, size);
    }

    const int64_t topAndKey = size;

    /* The offset from the record, in the stream, then the position (005-34). */
    for (int32_t i = 0; i < tn->value_count; i++) {
        struct vnode *node = tn->value_nodes[i];
        node->offset_from_trans = (uint32_t) j_l2i(currentPos - transStartPos);
        node_set_spos(&node->n, currentPos);
        size += nw_value_byte_size_long(node->len, tn->key_n[i]);
        currentPos = rs_get_spos(transStartPos, size);
    }

    size += 4;                          /* the end of nodes */
    size += 4;                          /* the number of got-dirty ids */
    size += 16 * (int64_t) gotDirtyCount;   /* the got-dirty pairs */
    size += 1;                          /* RecoverableStream.LAST_BYTE */
    s->extra_zeros = st_compute_zero_count(size);
    size += s->extra_zeros;

    if (size > recordLimit) {
        return err_set(e, ERR_LIMIT, "DbException", "The record of the transaction would "
                "take %lld bytes, more than the limit, %lld (bergdb 005-17).",
                (long long) size, (long long) recordLimit);
    }

    s->total_size = (int32_t) size;
    assert(s->total_size % RS_TRANS_ALIGNMENT == 0);
    s->trans_last_spos = rs_get_spos(transStartPos, s->total_size - 1);
    s->trans_next_spos = rs_get_spos(transStartPos, s->total_size);
    if (!resize_buffers(s, topAndKey / 8, size)) {
        return nomem(e);
    }
    return ERR_OK;
}

/* serializeToBuffer: the header, the nodes, the end. */
static void serialize_to_buffer(struct serial *s, const struct transnodes *tn, int64_t tt,
        int64_t startupPos, int64_t topPos, const struct ts_info *gotDirty) {
    int64_t *lb = s->long_buffer;
    uint8_t *bb = s->byte_buffer;
    int32_t longOffset = 0;

    /* serializeHeader */
    lb[longOffset++] = (int64_t) s->total_size | ((int64_t) ST_RECORD_FORMAT << 32);
    lb[longOffset++] = tt;
    lb[longOffset++] = startupPos;
    lb[longOffset++] = topPos;

    /* serializeNodes */
    int32_t prevPosIndex = 0;
    for (int32_t i = 0; i < tn->top_count; i++) {
        longOffset += nw_top_to_longs(tn->top_nodes[i], lb, longOffset);
    }
    for (int32_t i = 0; i < tn->key_count; i++) {
        longOffset += nw_key_to_longs(tn->key_nodes[i], lb, longOffset,
                s->prev_pos[prevPosIndex++]);
    }
    bytes_longs_to_le(lb, longOffset, bb);      /* copyLongBufferToByteBuffer */
    int32_t offset = longOffset * 8;
    for (int32_t i = 0; i < tn->value_count; i++) {
        offset += nw_value_to_bytes(tn->value_nodes[i], tn->keys[i], tn->key_n[i], bb, offset);
    }

    /* serializeEnd */
    bytes_put_int_le(0, bb + offset);           /* the end of nodes */
    offset += 4;
    const int32_t count = gotDirty == NULL ? 0 : gotDirty->ndirty;
    bytes_put_int_le(count, bb + offset);
    offset += 4;
    for (int32_t i = 0; i < count; i++) {
        const struct node *node = gotDirty->gotDirtyNodes[i].node;
        bytes_put_long_le(node->id, bb + offset);
        offset += 8;
        bytes_put_long_le(node->spos, bb + offset);
        offset += 8;
    }
    memset(bb + offset, 0, (size_t) s->extra_zeros);
    offset += s->extra_zeros;
    bb[offset] = RS_LAST_BYTE;
    offset += 1;
    assert(offset == s->total_size);
    assert(s->total_size % 8 == 0);
}

enum err_code ser_serialize(struct serial *s, struct transnodes *tn, int64_t tt,
        int64_t trans_start_pos, int64_t startup_pos, const struct ts_info *got_dirty,
        const struct tnode *top, int64_t record_limit, struct err *e) {
    assert(tt >= 0);
    assert(trans_start_pos >= 0);
    const int32_t gotDirtyCount = got_dirty == NULL ? 0 : got_dirty->ndirty;
    enum err_code rc = prepare(s, tn, trans_start_pos, gotDirtyCount, record_limit, e);
    if (rc != ERR_OK) {
        return rc;
    }
    /* After prepareToSerialize: a top node of this record has its new position. */
    const int64_t topPos = top == NULL ? SPOS_NULL : top->n.spos;
    assert(top == NULL || (spos_is_valid(topPos) && !spos_is_vpos(topPos)));
    check_stream_pointers(tn);
    serialize_to_buffer(s, tn, tt, startup_pos, topPos, got_dirty);
    return ERR_OK;
}

enum err_code ser_append_nodes(struct serial *s, struct rs *r, struct transnodes *tn, int64_t tt,
        int64_t startup_pos, const struct ts_info *got_dirty, const struct tnode *top,
        int64_t record_limit, struct ser_out *out, struct err *e) {
    const int64_t pos = rs_next_spos(stream_length(r->s));     /* getNextPos */
    enum err_code rc = ser_serialize(s, tn, tt, pos, startup_pos, got_dirty, top, record_limit,
            e);
    if (rc != ERR_OK) {
        return rc;
    }
    out->tpos = pos;
    out->last_pos = s->trans_last_spos;
    out->next_pos = s->trans_next_spos;

    /* rstream.append(buffer, 0, size, true, tt); then lastTrans */
    int64_t appended;
    rc = rs_append_record(r, s->byte_buffer, s->total_size, &appended, e);
    if (rc != ERR_OK) {
        return rc;
    }
    assert(appended == pos);
    return ERR_OK;
}
