/* meta: ported from Java's bergdb.storage.MetaBlock; see meta.h. */
#include "meta.h"
#include <string.h>
#include "bytes.h"
#include "spos.h"

static const uint8_t MAGIC[4] = { 'b', 'e', 'r', 'g' };

void meta_init(struct meta *mb) {
    memset(mb, 0, sizeof *mb);
    mb->pos = -1;
    memcpy(mb->block, MAGIC, 4);
    bytes_put_int_le(META_VERSION_154, mb->block + 4);
    mb->block[META_BLOCK_SIZE - 1] = META_LAST_BYTE;
    meta_set_last_trans(mb, SPOS_NULL);
}

void meta_from_bytes(struct meta *mb, const uint8_t *b, int64_t pos) {
    memcpy(mb->block, b, META_BLOCK_SIZE);
    mb->pos = pos;
}

bool meta_is_valid(const struct meta *mb) {
    return mb->block[META_BLOCK_SIZE - 1] == META_LAST_BYTE;
}

enum err_code meta_check_format(const struct meta *mb, struct err *e) {
    if (!meta_is_valid(mb)) {
        return ERR_OK;
    }
    /* checkMagic. */
    for (int i = 0; i < 4; i++) {
        if (mb->block[i] != MAGIC[i]) {
            return err_set(e, ERR_FORMAT, "StreamFormatException",
                    "Illegal first bytes of block, offset=%d, value=%d.", i,
                    (int) (int8_t) mb->block[i]);
        }
    }
    int64_t last = meta_last_trans(mb);
    if (last < 0 && last != SPOS_NULL) {
        return err_set(e, ERR_FORMAT, "StreamFormatException",
                "Meta block, bad last transaction spos: %lld.", (long long) last);
    }
    int64_t time = meta_time(mb);
    if (time < 0) {
        return err_set(e, ERR_FORMAT, "StreamFormatException", "Meta block, bad time, %lld.",
                (long long) time);
    }
    return ERR_OK;
}

int32_t meta_version(const struct meta *mb) {
    return bytes_get_ushort_le(mb->block + 4);
}

int64_t meta_time(const struct meta *mb) {
    return bytes_get_long_le(mb->block + 8);
}

int64_t meta_last_trans(const struct meta *mb) {
    return bytes_get_long_le(mb->block + 16);
}

const uint8_t *meta_id(const struct meta *mb) {
    return mb->block + 24;
}

int32_t meta_startup_distance(const struct meta *mb) {
    return bytes_get_int_le(mb->block + 40);
}

int32_t meta_max_node_size(const struct meta *mb) {
    return bytes_get_ushort_le(mb->block + 44);
}

void meta_set_time(struct meta *mb, int64_t time) {
    bytes_put_long_le(time, mb->block + 8);
}

void meta_set_last_trans(struct meta *mb, int64_t spos) {
    bytes_put_long_le(spos, mb->block + 16);
}

void meta_set_id(struct meta *mb, const uint8_t id[16]) {
    memcpy(mb->block + 24, id, 16);
}

void meta_set_startup_distance(struct meta *mb, int32_t startup_distance) {
    bytes_put_int_le(startup_distance, mb->block + 40);
}

bool meta_set_max_node_size(struct meta *mb, int32_t max_node_size) {
    return bytes_put_ushort_le(max_node_size, mb->block + 44);
}

uint8_t meta_fill_out_template(int32_t i) {
    if (i < 4) {
        return MAGIC[i];
    }
    if (i == 4) {
        return (uint8_t) (META_VERSION_154 & 0xff);
    }
    if (i == 5) {
        return (uint8_t) (META_VERSION_154 >> 8);
    }
    return 0;
}

bool meta_begins_as_block(const uint8_t *bytes, int32_t n) {
    const int32_t m = n < 4 + 2 ? n : 4 + 2;
    for (int32_t i = 0; i < m; i++) {
        if (bytes[i] != meta_fill_out_template(i)) {
            return false;
        }
    }
    return true;
}
