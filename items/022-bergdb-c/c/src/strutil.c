/* strutil: ported from Java's bergdb.common.StringUtil, line for line. */
#include "strutil.h"

bool su_is_well_formed_utf8(const uint8_t *b, int32_t length) {
    const int32_t end = length;
    int32_t i = 0;
    while (i < end) {
        int32_t c = b[i];
        if (c < 0x80) {
            i++;
            continue;
        }
        int32_t more;           /* the continuation bytes */
        int32_t low = 0x80;     /* the first continuation byte's range */
        int32_t high = 0xbf;
        if (c >= 0xc2 && c <= 0xdf) {
            more = 1;
        } else if (c == 0xe0) {
            more = 2;
            low = 0xa0;
        } else if (c == 0xed) {
            more = 2;
            high = 0x9f;
        } else if (c >= 0xe1 && c <= 0xef) {
            more = 2;
        } else if (c == 0xf0) {
            more = 3;
            low = 0x90;
        } else if (c == 0xf4) {
            more = 3;
            high = 0x8f;
        } else if (c >= 0xf1 && c <= 0xf3) {
            more = 3;
        } else {
            return false;
        }
        if (end - i <= more) {
            return false;
        }
        int32_t c1 = b[i + 1];
        if (c1 < low || c1 > high) {
            return false;
        }
        for (int32_t k = 2; k <= more; k++) {
            int32_t ck = b[i + k];
            if (ck < 0x80 || ck > 0xbf) {
                return false;
            }
        }
        i += more + 1;
    }
    return true;
}
