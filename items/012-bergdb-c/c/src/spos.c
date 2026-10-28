/* spos: ported from Java's bergdb.dag.Spos, line for line. */
#include "spos.h"

bool spos_is_valid(int64_t spos) {
    return spos >= 0;
}

int64_t spos_next_vpos(int64_t vpos) {
    return vpos % 2 == 0 ? vpos + 1 : vpos + 2;
}

bool spos_newer(int64_t pos, int64_t ref) {
    return spos_is_vpos(ref) ? !spos_is_vpos(pos) && pos >= 0 : pos > ref;
}

bool spos_is_vpos(int64_t spos) {
    return spos % 2 == 1;
}

bool spos_is_valid_or_null(int64_t spos) {
    return spos >= 0 || spos == SPOS_NULL;
}

bool spos_is_null(int64_t spos) {
    return spos == SPOS_NULL;
}

int32_t spos_add_to_align(int32_t a, int32_t mod) {
    return (mod - (a % mod)) % mod;
}
