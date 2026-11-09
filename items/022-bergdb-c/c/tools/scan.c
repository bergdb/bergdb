/*
 * bergdb-scan: C's scanner of a BergDB stream (bergdb 012-06), a port of
 * Java's StreamScan (c/test/cross/java/StreamScan.java, 012-02), whose
 * header defines the text, "streamscan 1". It prints the same text for the
 * same stream, byte for byte, so that the two compare with diff (012-05,
 * cross.sh). The scan's own decoding is ported line for line from
 * StreamScan; where StreamScan runs Java's parsers (StoredTrans.parse) and
 * Java's record walk (NodeStream.TransIterator) as a check, this runs C's
 * (strans, nstream), and their error lines say "C's" where Java's say
 * "Java's", with C's error in place of Java's exception: the text after
 * "error" is the implementation's own (StreamScan's header).
 *
 * Usage: bergdb-scan PATH
 *   PATH  a directory with *.bergdb files, or a flat file (the stream from
 *         position 0)
 *
 * Exit status: 0; 1 if an error line was printed; 2 on bad usage; 3 where
 * Java's scanner throws (a directory it refuses, a read past the end, a
 * value node too short to hold its fields): the text up to there, then the
 * reason on standard error, as cross.sh's Batch does with an exception
 * (status 3); 4 if the allocator's count is not 0 at the end (a leak).
 */
#include <inttypes.h>
#include <stdarg.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "bytes.h"
#include "checksum.h"
#include "mem.h"
#include "nstream.h"
#include "plat.h"
#include "rstream.h"
#include "sha256.h"
#include "snode.h"
#include "spos.h"
#include "stream.h"
#include "strans.h"

#define MBS META_BLOCK_SIZE
#define MBD META_BLOCK_DISTANCE

/* A node as the scan decoded it (StreamScan.RawNode): its arrays are read
 * from the record's bytes, which live while the record is checked. */
struct raw_node {
    int64_t pos;
    int32_t type;
    int64_t id;
    int64_t time;               /* a top node's root time */
    int64_t ordinal;
    int64_t prev_pos;
    int32_t leaf;
    int64_t offset;             /* a value node's stored offset */
    int64_t root;               /* a top node's root pointer */
    int32_t n;                  /* a top node's h, a key node's n */
    const uint8_t *arr;         /* skip pointers (pos, time) or klongs (n) then refs (n) */
    const uint8_t *value;       /* NULL for a delete */
    int32_t value_len;
    const uint8_t *key;
    int32_t key_n;
};

struct scan {
    FILE *out;
    struct mem mem;
    struct err err;
    struct stream s;
    bool stream_open;
    int64_t next_meta;          /* the position of the next meta block to print */
    int errors;
    bool thrown;                /* Java's scanner would have thrown: stop */
    char why[400];              /* what it would have thrown */

    struct ns_buf rec;          /* the record's bytes */
    struct ns_buf raw;          /* raw bytes */
    struct st_record st;        /* C's parse of the record */
    struct raw_node *nodes;     /* the scan's nodes of the record */
    int32_t nnodes, cap_nodes;
    int64_t *committed;         /* the committed records' positions */
    int32_t ncommitted, cap_committed;
    int64_t *walk;              /* C's walk's records */
    int32_t nwalk, cap_walk;
};

/* ======== Text ======== */

static void throw_(struct scan *sc, const char *format, ...) {
    va_list args;
    va_start(args, format);
    if (!sc->thrown) {
        vsnprintf(sc->why, sizeof sc->why, format, args);
    }
    va_end(args);
    sc->thrown = true;
}

static void error(struct scan *sc, const char *format, ...) {
    va_list args;
    sc->errors++;
    fputs("error ", sc->out);
    va_start(args, format);
    vfprintf(sc->out, format, args);
    va_end(args);
    fputc('\n', sc->out);
}

/* StreamScan.ptr: a pointer, decimal/0xhex, or -1. */
static const char *ptr(int64_t p, char *buf) {
    if (p == SPOS_NULL) {
        return "-1";
    }
    snprintf(buf, 48, "%" PRId64 "/0x%" PRIx64, p, (uint64_t) p);
    return buf;
}

static void put_hex(FILE *out, const uint8_t *b, int64_t n) {
    static const char digits[] = "0123456789abcdef";
    for (int64_t i = 0; i < n; i++) {
        fputc(digits[b[i] >> 4], out);
        fputc(digits[b[i] & 15], out);
    }
}

static void put_hex16(FILE *out, int64_t x) {
    fprintf(out, "%016" PRIx64, (uint64_t) x);
}

static bool is_zero(const uint8_t *b, int64_t n) {
    for (int64_t i = 0; i < n; i++) {
        if (b[i] != 0) {
            return false;
        }
    }
    return true;
}

static void put_zero_or_hex(FILE *out, const uint8_t *b, int64_t n) {
    if (is_zero(b, n)) {
        fputs("zero", out);
    } else {
        put_hex(out, b, n);
    }
}

static const char *tf(bool b) {
    return b ? "true" : "false";
}

static int64_t le64(const uint8_t *b, int64_t o) {
    return bytes_get_long_le(b + o);
}

static int32_t le32(const uint8_t *b, int64_t o) {
    return bytes_get_int_le(b + o);
}

static int32_t le16u(const uint8_t *b, int64_t o) {
    return bytes_get_ushort_le(b + o);
}

static int32_t le16(const uint8_t *b, int64_t o) {
    return bytes_get_short_le(b + o);
}

/* StreamScan.klong: a klong's decoded fields. */
static void put_klong(FILE *out, int64_t k) {
    int32_t type = (int32_t) ((uint64_t) k >> 62);
    switch (type) {
    case 0:
        fprintf(out, "time=%" PRId64, k & INT64_C(0x3fffffffffffffff));
        break;
    case 1: {
        int32_t len = (int32_t) (((uint64_t) k >> 3) & 7);
        fprintf(out, "key len=%d bytes=", (int) len);
        for (int32_t i = 0; i < len; i++) {
            uint8_t b = (uint8_t) ((uint64_t) k >> (54 - 8 * i));
            put_hex(out, &b, 1);
        }
        break;
    }
    case 2:
        fputs("type2", out);
        break;
    default:
        fputs("del", out);
    }
}

/* ======== Reading ======== */

/* StreamScan.transPos and transBytesBetween. */
static int64_t trans_pos(int64_t spos) {
    int64_t blocks = spos / MBD;
    int64_t offset = spos % MBD;
    return blocks * (MBD - MBS) + (offset > MBS ? offset - MBS : 0);
}

static int64_t trans_bytes_between(int64_t pos, int64_t end) {
    return trans_pos(end) - trans_pos(pos);
}

static bool ensure(struct scan *sc, struct ns_buf *b, int64_t n) {
    if (b->cap >= n) {
        return true;
    }
    uint8_t *p = mem_realloc(&sc->mem, b->p, (size_t) b->cap, (size_t) n, MEM_BUFFER);
    if (p == NULL) {
        throw_(sc, "OutOfMemoryError: %" PRId64 " bytes", n);
        return false;
    }
    b->p = p;
    b->cap = n;
    return true;
}

/* Raw bytes, meta blocks included (View.read); NULL if Java's read throws. */
static const uint8_t *read_raw(struct scan *sc, int64_t pos, int32_t n) {
    if (!ensure(sc, &sc->raw, n < 1 ? 1 : n)) {
        return NULL;
    }
    if (pos < stream_first_pos(&sc->s) || pos + n > stream_length(&sc->s)
            || stream_read(&sc->s, pos, sc->raw.p, n, &sc->err) != ERR_OK) {
        throw_(sc, "IOException: read of %d bytes at %" PRId64 ", outside %" PRId64 " to %"
                PRId64, (int) n, pos, stream_first_pos(&sc->s), stream_length(&sc->s));
        return NULL;
    }
    return sc->raw.p;
}

/* Record bytes from pos, meta blocks skipped (RecoverableStream.read). */
static const uint8_t *read_rec(struct scan *sc, struct ns_buf *b, int64_t pos, int32_t n) {
    if (!ensure(sc, b, n < 1 ? 1 : n)) {
        return NULL;
    }
    if (rs_read(&sc->s, pos, b->p, n, &sc->err) != ERR_OK) {
        throw_(sc, "%s: %s", sc->err.java, sc->err.text);
        return NULL;
    }
    return b->p;
}

/* ======== The walk ======== */

static void meta(struct scan *sc, int64_t p) {
    const int64_t length = stream_length(&sc->s);
    if (p + MBS > length) {
        int32_t n = (int32_t) (length - p);
        const uint8_t *b = read_raw(sc, p, n);
        if (b == NULL) {
            return;
        }
        fprintf(sc->out, "meta pos=%" PRId64 " partial=%d bytes=", p, (int) n);
        put_hex(sc->out, b, n);
        fputc('\n', sc->out);
        return;
    }
    const uint8_t *b = read_raw(sc, p, MBS);
    char pb[48];
    if (b == NULL) {
        return;
    }
    fprintf(sc->out, "meta pos=%" PRId64 " magic=", p);
    put_hex(sc->out, b, 4);
    fprintf(sc->out, " version=%d time=%" PRId64 " lastTrans=%s id=", (int) le32(b, 4),
            le64(b, 8), ptr(le64(b, 16), pb));
    put_hex(sc->out, b + 24, 16);
    fprintf(sc->out, " startupDistance=%d maxNodeSize=%d reserved=", (int) le32(b, 40),
            (int) le16u(b, 44));
    put_zero_or_hex(sc->out, b + 46, 81);
    fprintf(sc->out, " last=%d\n", (int) b[127]);
    if (b[127] == META_LAST_BYTE && memcmp(b, "berg", 4) != 0) {
        error(sc, "meta block at %" PRId64 " is valid but its magic bytes are not berg", p);
    }
}

/* Prints the meta blocks that start before pos. */
static void flush_metas(struct scan *sc, int64_t pos) {
    const int64_t length = stream_length(&sc->s);
    while (!sc->thrown && sc->next_meta < pos && sc->next_meta < length) {
        meta(sc, sc->next_meta);
        sc->next_meta += MBD;
    }
}

/* Where the walk starts (StreamScan.startOfWalk). */
static int64_t start_of_walk(struct scan *sc) {
    const int64_t first = stream_first_pos(&sc->s);
    const int64_t length = stream_length(&sc->s);
    for (int64_t m = sc->next_meta; m + MBS <= length; m += MBD) {
        const uint8_t *b = read_raw(sc, m, MBS);
        if (b == NULL) {
            return SPOS_NULL;
        }
        if (b[MBS - 1] != RS_LAST_BYTE) {
            continue;
        }
        int64_t last = le64(b, 16);
        if (last == SPOS_NULL) {
            if (length <= MBS) {
                return SPOS_NULL;
            }
            last = MBS;
        }
        if (last >= first) {
            return last;
        }
    }
    if (length - first < MBS) {
        return SPOS_NULL;
    }
    if (first == 0 && length > MBS) {
        error(sc, "no valid meta block; the walk starts at %d", MBS);
        return MBS;
    }
    error(sc, "no valid meta block names a record at or after the first position %" PRId64,
            first);
    return SPOS_NULL;
}

static struct raw_node *new_raw(struct scan *sc) {
    if (sc->nnodes == sc->cap_nodes) {
        int32_t c2 = sc->cap_nodes == 0 ? 16 : 2 * sc->cap_nodes;
        struct raw_node *n2 = mem_realloc(&sc->mem, sc->nodes,
                (size_t) sc->cap_nodes * sizeof *n2, (size_t) c2 * sizeof *n2, MEM_BUFFER);
        if (n2 == NULL) {
            throw_(sc, "OutOfMemoryError");
            return NULL;
        }
        sc->nodes = n2;
        sc->cap_nodes = c2;
    }
    struct raw_node *x = &sc->nodes[sc->nnodes];
    memset(x, 0, sizeof *x);
    return x;
}

static bool add_pos(struct scan *sc, int64_t **list, int32_t *n, int32_t *cap, int64_t pos) {
    if (*n == *cap) {
        int32_t c2 = *cap == 0 ? 64 : 2 * *cap;
        int64_t *l2 = mem_realloc(&sc->mem, *list, (size_t) *cap * sizeof *l2,
                (size_t) c2 * sizeof *l2, MEM_BUFFER);
        if (l2 == NULL) {
            throw_(sc, "OutOfMemoryError");
            return false;
        }
        *list = l2;
        *cap = c2;
    }
    (*list)[(*n)++] = pos;
    return true;
}

/* The ikey's text of a bkey (StreamScan.ikeyText): false if not printable. */
static bool ikey_printable(const uint8_t *bkey, int32_t n) {
    for (int32_t i = 0; i < n; i++) {
        int32_t c = bkey[i] == 1 ? '/' : (bkey[i] - 2) & 0xff;
        if (c < 0x21 || c > 0x7e || c == '=') {
            return false;
        }
    }
    return true;
}

/* Prints a node; false if the record cannot be parsed further. */
static bool node(struct scan *sc, int64_t tpos, const uint8_t *r, int32_t rsize, int32_t off,
        int32_t size) {
    FILE *out = sc->out;
    char pb[48];
    int64_t pos = rs_get_spos(tpos, off);
    flush_metas(sc, pos + 1);
    if (sc->thrown) {
        return false;
    }
    int32_t type = r[off + 4];
    int32_t format = r[off + 5];
    int32_t sum = le16u(r, off + 6);
    int32_t computed = cks_sum_with_zero_replace(r, off, size, off + 6);
    char head[200];
    snprintf(head, sizeof head, " pos=%" PRId64 " off=%d size=%d type=%d format=%d sum=%04x"
            " sumOk=%s", pos, (int) off, (int) size, (int) type, (int) format, (unsigned) sum,
            tf(sum == computed));
    struct raw_node *raw = new_raw(sc);
    if (raw == NULL) {
        return false;
    }
    raw->pos = pos;
    raw->type = type;
    switch (type) {
    case NODE_TOP: {
        if (size < 40) {
            error(sc, "top node at %" PRId64 " of size %d", pos, (int) size);
            return false;
        }
        int32_t h = (int8_t) r[off + 8];
        int64_t ordinal = (int64_t) ((uint64_t) le64(r, off + 8) >> 16);
        raw->id = le64(r, off + 16);
        raw->time = le64(r, off + 24);
        raw->ordinal = ordinal;
        int64_t root = le64(r, off + 32);
        fprintf(out, "top%s h=%d b9=%d ordinal=%" PRId64 " id=%" PRId64 " rootTime=%" PRId64
                " root=%s\n", head, (int) h, (int) r[off + 9], ordinal, raw->id, raw->time,
                ptr(root, pb));
        if (h < 0 || 40 + 16 * h != size) {
            error(sc, "top node at %" PRId64 ": h %d does not fit size %d", pos, (int) h,
                    (int) size);
            return false;
        }
        raw->root = root;
        raw->n = h;
        raw->arr = r + off + 40;
        for (int32_t i = 0; i < h; i++) {
            int64_t p = le64(r, off + 40 + 16 * i);
            int64_t t = le64(r, off + 48 + 16 * i);
            fprintf(out, "  skip i=%d pos=%s time=%" PRId64 "\n", (int) i, ptr(p, pb), t);
        }
        break;
    }
    case NODE_KEY: {
        if (size < 32) {
            error(sc, "key node at %" PRId64 " of size %d", pos, (int) size);
            return false;
        }
        int64_t prev = le64(r, off + 8);
        int32_t leaf = r[off + 16];
        int32_t n = le16(r, off + 17);
        raw->id = le64(r, off + 24);
        raw->prev_pos = prev;
        raw->leaf = leaf;
        fprintf(out, "key%s prevPos=%s leaf=%d n=%d reserved=", head, ptr(prev, pb), (int) leaf,
                (int) n);
        put_zero_or_hex(out, r + off + 19, 5);
        fprintf(out, " id=%" PRId64 "\n", raw->id);
        if (n < 0 || 32 + 16 * n != size) {
            error(sc, "key node at %" PRId64 ": n %d does not fit size %d", pos, (int) n,
                    (int) size);
            return false;
        }
        raw->n = n;
        raw->arr = r + off + 32;
        for (int32_t i = 0; i < n; i++) {
            int64_t k = le64(r, off + 32 + 8 * i);
            int64_t ref = le64(r, off + 32 + 8 * n + 8 * i);
            fprintf(out, "  klong i=%d raw=0x", (int) i);
            put_hex16(out, k);
            fputc(' ', out);
            put_klong(out, k);
            fprintf(out, " ref=%s\n", ptr(ref, pb));
        }
        break;
    }
    case NODE_VALUE:
    case NODE_DELETE: {
        bool isValue = type == NODE_VALUE;
        /* Java reads the id, the stored offset, and the length or the key size before it
         * prints anything; past the record's bytes, it throws. */
        if ((int64_t) off + 24 > rsize) {
            throw_(sc, "ArrayIndexOutOfBoundsException: a %s node at %" PRId64 " of size %d,"
                    " its fields past the record's %d bytes", isValue ? "value" : "delete",
                    pos, (int) size, (int) rsize);
            return false;
        }
        int32_t o = off + 8;
        raw->id = le64(r, o);
        o += 8;
        int32_t stored = le32(r, o);
        raw->offset = stored;
        o += 4;
        char line[400];
        snprintf(line, sizeof line, "%s%s id=%" PRId64 " offset=%d", isValue ? "value" : "delete",
                head, raw->id, (int) stored);
        if (isValue) {
            int32_t len = le32(r, o);
            o += 4;
            if (len < 0 || o + (int64_t) len + 4 > off + size) {
                fprintf(out, "%s\n", line);
                error(sc, "value node at %" PRId64 ": bad value length %d", pos, (int) len);
                return false;
            }
            char h[65];
            sha256_hex(r + o, (size_t) len, h);
            raw->value = r + o;
            raw->value_len = len;
            size_t l = strlen(line);
            snprintf(line + l, sizeof line - l, " length=%d sha256=%s", (int) len, h);
            o += len;
        }
        int32_t keySize = le32(r, o);
        o += 4;
        if (keySize <= 0 || keySize % 8 != 0 || o + (int64_t) keySize > off + size) {
            fprintf(out, "%s keySize=%d\n", line, (int) keySize);
            error(sc, "value node at %" PRId64 ": bad key size %d", pos, (int) keySize);
            return false;
        }
        int32_t nsegs = keySize / 8;
        raw->key = r + o;
        raw->key_n = nsegs;
        fprintf(out, "%s keySize=%d segs=", line, (int) keySize);
        for (int32_t i = 0; i < nsegs; i++) {
            if (i > 0) {
                fputc(',', out);
            }
            put_hex16(out, le64(r, o + 8 * i));
        }
        /* The bkey (StreamScan.bkeyOf): each segment's bytes, by its length. */
        uint8_t *bkey = NULL;
        int32_t nb = 0;
        if (!ensure(sc, &sc->raw, (int64_t) nsegs * 7 + 1)) {
            return false;
        }
        bkey = sc->raw.p;
        for (int32_t i = 0; i < nsegs; i++) {
            uint64_t s = (uint64_t) le64(r, o + 8 * i);
            int32_t len = (int32_t) ((s >> 3) & 7);
            for (int32_t j = 0; j < len; j++) {
                bkey[nb++] = (uint8_t) (s >> (54 - 8 * j));
            }
        }
        fputs(" key=", out);
        put_hex(out, bkey, nb);
        if (ikey_printable(bkey, nb)) {
            fputs(" ikey=", out);
            for (int32_t i = 0; i < nb; i++) {
                fputc(bkey[i] == 1 ? '/' : (bkey[i] - 2) & 0xff, out);
            }
        }
        o += keySize;
        int32_t pad = off + size - o;
        fprintf(out, " pad=%d padZero=%s\n", (int) pad, tf(is_zero(r + o, pad)));
        if (pad < 0 || pad >= 4) {
            error(sc, "value node at %" PRId64 ": %d bytes of padding", pos, (int) pad);
        }
        break;
    }
    default:
        fprintf(out, "node%s\n", head);
        error(sc, "unknown node type %d at %" PRId64, (int) type, pos);
        return false;
    }
    sc->nnodes++;
    return true;
}

/* ======== C's own parser, as a check of the raw fields (checkJavaParse) ======== */

static void check_parse(struct scan *sc, int64_t tpos, const uint8_t *r, int32_t rsize,
        int64_t time, int64_t startupPos, int64_t topPos, const uint8_t *dirty, int32_t ndirty,
        int64_t lastPos) {
    struct st_record *t = &sc->st;
    if (st_parse(t, tpos, r, rsize, &sc->mem, &sc->err) != ERR_OK) {
        error(sc, "C's parser refuses the record at %" PRId64 ": %s: %s", tpos, sc->err.java,
                sc->err.text);
        return;
    }
    char where[120];
    snprintf(where, sizeof where, "record at %" PRId64 ": C's parser and the scan disagree on ",
            tpos);
    if (t->tt != time) error(sc, "%sthe time", where);
    if (t->startup_pos != startupPos) error(sc, "%sstartupPos", where);
    if (t->top_pos != topPos) error(sc, "%stopPos", where);
    if (t->last_pos != lastPos) {
        error(sc, "%slastPos, %" PRId64 " and %" PRId64, where, t->last_pos, lastPos);
    }
    if (t->got_dirty_count != ndirty
            || (ndirty > 0 && memcmp(t->got_dirty, dirty, (size_t) ndirty * 16) != 0)) {
        error(sc, "%sgot-dirty list", where);
    }
    if (t->nnodes != sc->nnodes) {
        error(sc, "%sthe node count, %d and %d", where, (int) t->nnodes, (int) sc->nnodes);
        return;
    }
    for (int32_t i = 0; i < t->nnodes; i++) {
        const struct sn_node *n = &t->nodes[i];
        const struct raw_node *x = &sc->nodes[i];
        char w[200];
        snprintf(w, sizeof w, "%snode %d at %" PRId64 ", ", where, (int) i, x->pos);
        if (n->spos != x->pos) error(sc, "%sspos %" PRId64, w, n->spos);
        if ((n->type & 0xff) != x->type) error(sc, "%stype %d", w, (int) n->type);
        if (n->id != x->id) error(sc, "%sid %" PRId64, w, n->id);
        if (n->type == NODE_TOP) {
            if (n->ordinal != x->ordinal) error(sc, "%sordinal", w);
            if (n->root_time != x->time) error(sc, "%sroot time", w);
            if (n->root != x->root) error(sc, "%sroot pointer", w);
            for (int32_t j = 0; j < n->h; j++) {
                int64_t rp = le64(x->arr, 16 * j);
                int64_t rt = le64(x->arr, 16 * j + 8);
                if (sn_skip_pos(n, j) != rp) error(sc, "%sskip pointer %d", w, (int) j);
                int64_t time2 = rp == SPOS_NULL ? -1 : rt;
                if (sn_skip_time(n, j) != time2) error(sc, "%sskip time %d", w, (int) j);
                if (rp == SPOS_NULL && rt != -1) {
                    error(sc, "%san unset skip pointer with time %" PRId64, w, rt);
                }
            }
        } else if (n->type == NODE_KEY) {
            if (n->prev_pos != x->prev_pos) error(sc, "%sprevPos", w);
            if (n->leaf != (x->leaf == 1)) error(sc, "%sleaf", w);
            if (n->n != x->n) error(sc, "%ssize", w);
            for (int32_t j = 0; j < n->n && j < x->n; j++) {
                if (sn_klong(n, j) != le64(x->arr, 8 * j)) error(sc, "%sklong %d", w, (int) j);
                if (sn_ref(n, j) != le64(x->arr, 8 * x->n + 8 * j)) {
                    error(sc, "%sref %d", w, (int) j);
                }
            }
        } else {
            bool sameValue = (n->value == NULL) == (x->value == NULL)
                    && (n->value == NULL || (n->value_len == x->value_len
                    && memcmp(n->value, x->value, (size_t) x->value_len) == 0));
            if (!sameValue) error(sc, "%svalue", w);
            if (n->key_n != x->key_n
                    || memcmp(n->key, x->key, (size_t) x->key_n * 8) != 0) {
                error(sc, "%skey", w);
            }
            /* ValueNode.getTpos: NULL for a vpos (an odd position) */
            int64_t getTpos = spos_is_null(n->spos) || spos_is_vpos(n->spos) ? SPOS_NULL
                    : n->spos - (int64_t) (uint32_t) n->offset_from_trans;
            if (getTpos != tpos) error(sc, "%stpos from the offset, %" PRId64, w, getTpos);
            if (rs_get_spos(tpos, x->offset) != x->pos) {
                error(sc, "%sthe stored offset %" PRId64, w, x->offset);
            }
        }
    }
}

/* Prints the record at pos; returns the position after it, or -1 if the walk cannot go
 * on (or Java's scanner would have thrown: sc->thrown). */
static int64_t record(struct scan *sc, int64_t pos) {
    FILE *out = sc->out;
    char pb[48], pb2[48];
    const int64_t length = stream_length(&sc->s);
    int64_t have = trans_bytes_between(pos, length);
    if (have < 4) {
        flush_metas(sc, pos + 1);
        if (sc->thrown) return -1;
        fprintf(out, "torn pos=%" PRId64 " size=? have=%" PRId64 "\n", pos, have);
        return -1;
    }
    const uint8_t *sb = read_rec(sc, &sc->rec, pos, 4);
    if (sb == NULL) return -1;
    int32_t size = le32(sb, 0);
    if (size < RS_MIN_TRANS_SIZE) {
        flush_metas(sc, pos + 1);
        if (sc->thrown) return -1;
        error(sc, "record at %" PRId64 " has size %d, below %d", pos, (int) size,
                RS_MIN_TRANS_SIZE);
        return -1;
    }
    if (have < size) {
        flush_metas(sc, pos + 1);
        if (sc->thrown) return -1;
        fprintf(out, "torn pos=%" PRId64 " size=%d have=%" PRId64 "\n", pos, (int) size, have);
        return -1;
    }
    const uint8_t *r = read_rec(sc, &sc->rec, pos, size);
    if (r == NULL) return -1;
    int64_t next = rs_get_spos(pos, size);
    int64_t lastPos = rs_get_spos(pos, size - 1);
    int32_t last = r[size - 1];
    flush_metas(sc, pos + 1);
    if (sc->thrown) return -1;
    if (last != RS_LAST_BYTE) {
        char h[65];
        sha256_hex(r, (size_t) size, h);
        fprintf(out, "record pos=%" PRId64 " size=%d last=%d sha256=%s next=%" PRId64 "\n", pos,
                (int) size, (int) last, h, next);
        if (last != 0) {
            error(sc, "record at %" PRId64 " has last byte %d, neither 10 nor 0", pos,
                    (int) last);
        }
        return next;
    }
    if (!add_pos(sc, &sc->committed, &sc->ncommitted, &sc->cap_committed, pos)) return -1;
    if (size < 32 + 4 + 4 + 1) {
        error(sc, "committed record at %" PRId64 " of size %d is too short", pos, (int) size);
        return next;
    }
    fprintf(out, "record pos=%" PRId64 " size=%d format=%d b5=", pos, (int) size, (int) r[4]);
    put_hex(out, r + 5, 3);
    fprintf(out, " time=%" PRId64 " startupPos=%s topPos=%s last=%d lastPos=%" PRId64 " next=%"
            PRId64 "\n", le64(r, 8), ptr(le64(r, 16), pb), ptr(le64(r, 24), pb2), (int) last,
            lastPos, next);

    sc->nnodes = 0;
    int32_t off = 32;
    while (true) {
        if (off + 4 > size - 1) {
            error(sc, "record at %" PRId64 ": no end of nodes before offset %d", pos, (int) off);
            return next;
        }
        int32_t nodeSize = le32(r, off);
        if (nodeSize == 0) {
            break;
        }
        if (nodeSize < 8 || off + (int64_t) nodeSize > size - 1) {
            error(sc, "record at %" PRId64 ": bad node size %d at offset %d", pos,
                    (int) nodeSize, (int) off);
            return next;
        }
        if (!node(sc, pos, r, size, off, nodeSize)) {
            return sc->thrown ? -1 : next;
        }
        off += nodeSize;
    }
    int64_t p = rs_get_spos(pos, off);
    flush_metas(sc, p + 1);
    if (sc->thrown) return -1;
    fprintf(out, "nodes-end pos=%" PRId64 " off=%d\n", p, (int) off);
    off += 4;

    if (off + 4 > size - 1) {
        error(sc, "record at %" PRId64 ": no got-dirty count", pos);
        return next;
    }
    int32_t count = le32(r, off);
    p = rs_get_spos(pos, off);
    flush_metas(sc, p + 1);
    if (sc->thrown) return -1;
    fprintf(out, "gotdirty pos=%" PRId64 " off=%d count=%d\n", p, (int) off, (int) count);
    off += 4;
    if (count < 0 || off + INT64_C(16) * count > size - 1) {
        error(sc, "record at %" PRId64 ": bad got-dirty count %d", pos, (int) count);
        return next;
    }
    const uint8_t *dirty = r + off;
    for (int32_t i = 0; i < count; i++) {
        fprintf(out, "  dirty i=%d id=%" PRId64 " pos=%s\n", (int) i, le64(r, off),
                ptr(le64(r, off + 8), pb));
        off += 16;
    }

    int32_t pad = size - 1 - off;
    p = rs_get_spos(pos, off);
    flush_metas(sc, p + 1);
    if (sc->thrown) return -1;
    fprintf(out, "padding pos=%" PRId64 " off=%d count=%d zero=%s\n", p, (int) off, (int) pad,
            tf(is_zero(r + off, pad)));
    if (pad >= 8) {
        error(sc, "record at %" PRId64 ": %d bytes after the got-dirty list", pos, (int) pad);
    }
    flush_metas(sc, lastPos + 1);
    if (sc->thrown) return -1;
    fprintf(out, "last pos=%" PRId64 " byte=%d\n", lastPos, (int) last);

    check_parse(sc, pos, r, size, le64(r, 8), le64(r, 16), le64(r, 24), dirty, count, lastPos);
    return next;
}

/* C's record walk from the first position, as startup's (checkJavaWalk). */
static void check_walk(struct scan *sc, bool torn) {
    struct ns_iter it;
    bool has;
    enum err_code rc;
    sc->nwalk = 0;
    ns_iter_init(&it, &sc->s, &sc->mem, stream_first_pos(&sc->s), false);
    while ((rc = ns_iter_next(&it, &has, &sc->err)) == ERR_OK && has) {
        if (!add_pos(sc, &sc->walk, &sc->nwalk, &sc->cap_walk, it.tpos)) {
            ns_iter_free(&it);
            return;
        }
    }
    ns_iter_free(&it);
    bool same = sc->nwalk == sc->ncommitted && (sc->nwalk == 0
            || memcmp(sc->walk, sc->committed, (size_t) sc->nwalk * sizeof *sc->walk) == 0);
    if (rc != ERR_OK) {
        if (!(torn && same)) {
            error(sc, "C's record walk fails: %s: %s", sc->err.java, sc->err.text);
        }
        return;
    }
    if (!same) {
        if (sc->nwalk == 0 || sc->ncommitted == 0) {
            error(sc, "C's record walk finds %d committed records, the scan %d", (int) sc->nwalk,
                    (int) sc->ncommitted);
        } else {
            error(sc, "C's record walk finds %d committed records, the scan %d, first %" PRId64
                    " and %" PRId64, (int) sc->nwalk, (int) sc->ncommitted, sc->walk[0],
                    sc->committed[0]);
        }
    }
}

static void run(struct scan *sc) {
    const int64_t first = stream_first_pos(&sc->s);
    const int64_t length = stream_length(&sc->s);
    fprintf(sc->out, "stream first=%" PRId64 " length=%" PRId64 "\n", first, length);

    int64_t pos = start_of_walk(sc);
    if (sc->thrown) return;
    if (pos > first && pos != SPOS_NULL) {
        int64_t from = first % MBD < MBS ? first - first % MBD + MBS : first;
        if (pos > from) {
            flush_metas(sc, from);
            if (sc->thrown) return;
            fprintf(sc->out, "gap from=%" PRId64 " to=%" PRId64 "\n", from, pos);
        }
    }

    bool torn = length - first < MBS;
    while (pos != SPOS_NULL && pos < length) {
        int64_t next = record(sc, pos);
        if (sc->thrown) return;
        if (next < 0) {
            torn = true;
            break;
        }
        pos = next;
    }
    flush_metas(sc, INT64_MAX);
    if (sc->thrown) return;
    check_walk(sc, torn);
    if (sc->thrown) return;
    fprintf(sc->out, "end length=%" PRId64 "\n", length);
}

/* ======== The view: the directory or the flat file (StreamScan.View.open) ======== */

static bool is_14_digits(const char *s, size_t n) {
    if (n != 14) {
        return false;
    }
    for (size_t i = 0; i < n; i++) {
        if (s[i] < '0' || s[i] > '9') {
            return false;
        }
    }
    return true;
}

static void open_view(struct scan *sc, const char *path) {
    if (plat_is_dir(path)) {
        struct plat_entry *all;
        int32_t n;
        if (plat_list_dir(path, &sc->mem, &all, &n, &sc->err) != ERR_OK) {
            throw_(sc, "%s: %s", sc->err.java, sc->err.text);
            return;
        }
        int64_t expected = -1;
        int32_t nfiles = 0;
        bool badSize = false;
        for (int32_t i = 0; i < n && !sc->thrown; i++) {
            const char *name = all[i].name;
            size_t len = strlen(name);
            if (!(len >= 7 && strcmp(name + len - 7, ".bergdb") == 0)) {
                fprintf(sc->out, "other name=%s size=%" PRId64 "\n", name, all[i].size);
                continue;
            }
            int64_t start = -1;
            if (is_14_digits(name, len - 7)) {
                start = strtoll(name, NULL, 10) * 100000;
            }
            fprintf(sc->out, "file name=%s first=%" PRId64 " size=%" PRId64 "\n", name, start,
                    all[i].size);
            if (start < 0) {
                throw_(sc, "IOException: bad file name %s", name);
            } else if (expected >= 0 && start != expected) {
                throw_(sc, "IOException: file %s starts at %" PRId64 ", the files before it end "
                        "at %" PRId64, name, start, expected);
            } else if (all[i].is_dir) {
                throw_(sc, "FileNotFoundException: %s/%s (Is a directory)", path, name);
            }
            nfiles++;
            expected = start + all[i].size;
        }
        /* The files before the last: lengths that are multiples of 100,000. */
        int32_t seen = 0;
        for (int32_t i = 0; i < n && !sc->thrown; i++) {
            size_t len = strlen(all[i].name);
            if (!(len >= 7 && strcmp(all[i].name + len - 7, ".bergdb") == 0)) {
                continue;
            }
            seen++;
            if (seen < nfiles && all[i].size % 100000 != 0) {
                badSize = true;
            }
        }
        plat_free_entries(&sc->mem, all, n);
        if (sc->thrown) {
            return;
        }
        if (badSize) {
            throw_(sc, "IOException: a file before the last has a size that is not a multiple "
                    "of 100,000");
            return;
        }
        if (stream_open_dir(&sc->s, path, &sc->mem, &sc->err) != ERR_OK) {
            throw_(sc, "%s: %s", sc->err.java, sc->err.text);
            return;
        }
        sc->stream_open = true;
        return;
    }

    /* A flat file: the stream from position 0, read into a memory stream. */
    FILE *f = fopen(path, "rb");
    if (f == NULL) {
        throw_(sc, "FileNotFoundException: %s", path);
        return;
    }
    stream_open_memory(&sc->s, &sc->mem);
    sc->stream_open = true;
    uint8_t chunk[1 << 16];
    size_t k;
    while ((k = fread(chunk, 1, sizeof chunk, f)) > 0) {
        if (stream_append_memory(&sc->s, chunk, (int64_t) k, &sc->err) != ERR_OK) {
            throw_(sc, "%s: %s", sc->err.java, sc->err.text);
            break;
        }
    }
    fclose(f);
}

int main(int argc, char **argv) {
    static struct scan scan;
    struct scan *sc = &scan;
    if (argc != 2) {
        fprintf(stderr, "Usage: bergdb-scan PATH\n");
        return 2;
    }
    static char outbuf[1 << 16];
    setvbuf(stdout, outbuf, _IOFBF, sizeof outbuf);
    sc->out = stdout;
    mem_init(&sc->mem);
    err_clear(&sc->err);
    st_init(&sc->st);

    fputs("streamscan 1\n", sc->out);
    open_view(sc, argv[1]);
    if (!sc->thrown) {
        sc->next_meta = (stream_first_pos(&sc->s) + MBD - 1) / MBD * MBD;
        run(sc);
    }
    fflush(sc->out);

    if (sc->stream_open) {
        stream_close(&sc->s);
    }
    ns_buf_free(&sc->rec, &sc->mem);
    ns_buf_free(&sc->raw, &sc->mem);
    st_free(&sc->st, &sc->mem);
    mem_free(&sc->mem, sc->nodes, (size_t) sc->cap_nodes * sizeof *sc->nodes, MEM_BUFFER);
    mem_free(&sc->mem, sc->committed, (size_t) sc->cap_committed * sizeof *sc->committed,
            MEM_BUFFER);
    mem_free(&sc->mem, sc->walk, (size_t) sc->cap_walk * sizeof *sc->walk, MEM_BUFFER);
    if (sc->mem.live_total != 0) {
        fprintf(stderr, "bergdb-scan: %" PRId64 " bytes live at the end\n", sc->mem.live_total);
        return 4;
    }
    if (sc->thrown) {
        fprintf(stderr, "bergdb-scan: Java's scanner throws here: %s\n", sc->why);
        return 3;
    }
    return sc->errors == 0 ? 0 : 1;
}
