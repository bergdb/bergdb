/*
 * bergdb-run: C's runner of a cross workload, Java's Run (bergdb 012-05,
 * section 6.2, "bergdb-run 1"; the workload format, "bergdb-workload 1", is
 * section 6.1), on C's database through the API, include/bergdb.h, only, as
 * Run uses Db's public API. For the same workload it prints Run's text, and
 * writes Java's bytes (bergdb 012-09).
 *
 * Usage: bergdb-run [-v] [-segments A[-B]] [-budget N] [-mem] WORKLOAD DIR
 *   -v           also print each get's and each check's key-value pairs
 *   -segments    run only segments A to B (0-based; the segments are
 *                separated by restart lines); DIR holds the database that
 *                segment A-1 left
 *   -budget N    the memory budget at every start is N bytes (in place of
 *                the workload's "set budget", or of none: no eviction);
 *                its setbudget lines still apply (012-12: the bytes and
 *                the text must not change with the budget)
 *   -mem         also print to standard error, at each segment's end, the
 *                index's resident bytes (bergdb_stats) then and at most
 *                after any line of the segment, the budget, the pinned bytes
 *                (then and at most), the most resident bytes over the budget
 *                plus the pinned (maxOver: 0 or less when the budget holds), the
 *                allocator's live and peak bytes (012-12), and the stream's
 *                durable length before the segment's close (cross.sh's crash
 *                variants of a workload that reclaims, 012-11, Q1)
 * Exit status: 0; 1 if a transaction or a call was refused, or the start
 * failed; 2 on a bad workload or usage; 3 for a workload that C cannot run
 * yet: none since 012-11 (restarts, -segments from 1 and a DIR that has a
 * stream start the existing database, 012-10; reclaim, 012-11).
 *
 * The workload is parsed whole first, as Java's Workload.read: a bad line
 * anywhere exits 2 before anything runs. The names of Java's exceptions
 * that refused lines and starts print come from bergdb_errmsg, whose text
 * begins with them.
 */
#include <errno.h>
#include <inttypes.h>
#include <limits.h>
#include <stdarg.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <dirent.h>
#include "bergdb.h"
#include "sha256.h"

/* ======== Memory and errors of the tool ======== */

static void *xmalloc(size_t n) {
    void *p = malloc(n == 0 ? 1 : n);
    if (p == NULL) {
        fprintf(stderr, "bergdb-run: out of memory\n");
        exit(2);
    }
    return p;
}

static void *xrealloc(void *p, size_t n) {
    void *q = realloc(p, n == 0 ? 1 : n);
    if (q == NULL) {
        fprintf(stderr, "bergdb-run: out of memory\n");
        exit(2);
    }
    return q;
}

static const char *wl_path;

/* Workload.BadWorkload: the message, and exit 2. */
static void bad(int number, const char *fmt, ...) {
    va_list ap;
    fflush(stdout);
    fprintf(stderr, "Run: %s: ", wl_path);
    if (number > 0) {
        fprintf(stderr, "workload line %d: ", number);
    }
    va_start(ap, fmt);
    vfprintf(stderr, fmt, ap);
    va_end(ap);
    fprintf(stderr, "\n");
    exit(2);
}

/* ======== The workload (Workload.java) ======== */

struct line {
    int number;             /* 1-based */
    char *text;             /* the line's copy, which the words point into */
    char **words;
    int nwords;
    int segment;
    int trans;              /* the t line's index, else -1 */
};

struct workload {
    int max_node;           /* 30 */
    int64_t startup_distance;   /* -1: not set */
    int64_t retain;         /* -1: not set; INT64_MAX: forever */
    const char *fraction;   /* NULL: not set */
    char *fraction_line;    /* the copy of the set line that fraction points into */
    int64_t budget;         /* -1 */
    struct line *lines;
    int nlines;
    int cap;
    int segments;
    int trans_count;
    bool reclaims;          /* a retain setting or setter other than forever */
};

/* Java's Long.parseLong: an optional sign, decimal digits, in range. */
static bool parse_long(const char *s, int64_t *out) {
    const char *p = s;
    bool neg = false;
    if (*p == '+' || *p == '-') {
        neg = *p == '-';
        p++;
    }
    if (*p == '\0') {
        return false;
    }
    uint64_t v = 0;
    for (; *p != '\0'; p++) {
        if (*p < '0' || *p > '9') {
            return false;
        }
        uint64_t d = (uint64_t) (*p - '0');
        if (v > (UINT64_MAX - d) / 10) {
            return false;
        }
        v = v * 10 + d;
        if (v > (uint64_t) INT64_MAX + (neg ? 1u : 0u)) {
            return false;
        }
    }
    *out = neg ? (int64_t) (0 - v) : (int64_t) v;
    return true;
}

static int64_t need_long(int number, const char *s) {
    int64_t v;
    if (!parse_long(s, &v)) {
        bad(number, "For input string: \"%s\"", s);
    }
    return v;
}

static int32_t need_int(int number, const char *s) {
    int64_t v = need_long(number, s);
    if (v < INT32_MIN || v > INT32_MAX) {
        bad(number, "For input string: \"%s\"", s);
    }
    return (int32_t) v;
}

/* Long.parseUnsignedLong */
static uint64_t need_ulong(int number, const char *s) {
    const char *p = s;
    if (*p == '+') {
        p++;
    }
    if (*p == '\0') {
        bad(number, "For input string: \"%s\"", s);
    }
    uint64_t v = 0;
    for (; *p != '\0'; p++) {
        if (*p < '0' || *p > '9') {
            bad(number, "For input string: \"%s\"", s);
        }
        uint64_t d = (uint64_t) (*p - '0');
        if (v > (UINT64_MAX - d) / 10) {
            bad(number, "For input string: \"%s\"", s);
        }
        v = v * 10 + d;
    }
    return v;
}

/* Double.parseDouble, as far as the workloads use it: strtod's decimal
 * text gives the same double. */
static double need_double(int number, const char *s) {
    char *end;
    errno = 0;
    double d = strtod(s, &end);
    if (end == s || *end != '\0') {
        bad(number, "For input string: \"%s\"", s);
    }
    return d;
}

static int64_t wl_time(int number, const char *s) {
    int64_t t = need_long(number, s);
    if (t < 0) {
        bad(number, "negative time");
    }
    return t;
}

static int64_t lookup_time(int number, const char *s) {
    return strcmp(s, "latest") == 0 ? INT64_MAX : wl_time(number, s);
}

static int64_t retain_of(int number, const char *v) {
    return strcmp(v, "forever") == 0 ? INT64_MAX : need_long(number, v);
}

static int hexval(int c) {
    if (c >= '0' && c <= '9') return c - '0';
    if (c >= 'a' && c <= 'f') return c - 'a' + 10;
    if (c >= 'A' && c <= 'F') return c - 'A' + 10;
    return -1;
}

/* Workload.unescape: %XX into bytes, other bytes as they are. *n the
 * length; the result malloc'ed. */
static uint8_t *unescape(int number, const char *s, size_t *n) {
    size_t len = strlen(s);
    uint8_t *out = xmalloc(len + 1);
    size_t o = 0;
    for (size_t i = 0; i < len; i++) {
        if (s[i] == '%') {
            if (i + 2 >= len) {
                bad(number, "bad escape in %s", s);
            }
            int a = hexval((unsigned char) s[i + 1]), b = hexval((unsigned char) s[i + 2]);
            if (a < 0 || b < 0) {
                bad(number, "bad hex digit in %s", s);
            }
            out[o++] = (uint8_t) (a << 4 | b);
            i += 2;
        } else {
            out[o++] = (uint8_t) s[i];
        }
    }
    *n = o;
    return out;
}

/* Strict UTF-8, as Java's decoder with REPORT: no overlong forms, no
 * surrogates, at most U+10FFFF. */
static bool valid_utf8(const uint8_t *p, size_t n) {
    size_t i = 0;
    while (i < n) {
        uint8_t c = p[i];
        size_t k;
        uint32_t cp;
        if (c < 0x80) {
            i++;
            continue;
        } else if (c >= 0xc2 && c <= 0xdf) {
            k = 1;
            cp = c & 0x1fu;
        } else if (c >= 0xe0 && c <= 0xef) {
            k = 2;
            cp = c & 0x0fu;
        } else if (c >= 0xf0 && c <= 0xf4) {
            k = 3;
            cp = c & 0x07u;
        } else {
            return false;
        }
        for (size_t j = 1; j <= k; j++) {
            if (i + j >= n || (p[i + j] & 0xc0) != 0x80) {
                return false;
            }
            cp = cp << 6 | (p[i + j] & 0x3fu);
        }
        if ((k == 2 && (cp < 0x800 || (cp >= 0xd800 && cp <= 0xdfff)))
                || (k == 3 && (cp < 0x10000 || cp > 0x10ffff))) {
            return false;
        }
        i += k + 1;
    }
    return true;
}

/* Workload.key: the bkey of a key word, malloc'ed. */
static uint8_t *wl_key(int number, const char *word, size_t *n) {
    uint8_t *ikey = unescape(number, word, n);
    if (!valid_utf8(ikey, *n)) {
        bad(number, "key not UTF-8: %s", word);
    }
    if (*n == 0) {
        bad(number, "empty key");
    }
    if (bergdb_ikey_to_bkey(ikey, *n, ikey) != BERGDB_OK) {
        bad(number, "bad key: %s", word);
    }
    return ikey;
}

static int32_t wl_size(int number, const char *s, const char *word) {
    int32_t n = need_int(number, s);
    if (n < 0) {
        bad(number, "negative size: %s", word);
    }
    return n;
}

/* Workload.value: s:TEXT, x:HEX, z:N or r:SEED:N; malloc'ed. */
static uint8_t *wl_value(int number, const char *word, size_t *n) {
    if (strncmp(word, "s:", 2) == 0) {
        return unescape(number, word + 2, n);
    }
    if (strncmp(word, "x:", 2) == 0) {
        const char *h = word + 2;
        size_t len = strlen(h);
        if (len % 2 != 0) {
            bad(number, "odd hex length: %s", word);
        }
        uint8_t *b = xmalloc(len / 2);
        for (size_t i = 0; i < len / 2; i++) {
            int a = hexval((unsigned char) h[2 * i]), c = hexval((unsigned char) h[2 * i + 1]);
            if (a < 0 || c < 0) {
                bad(number, "bad hex digit in %s", word);
            }
            b[i] = (uint8_t) (a << 4 | c);
        }
        *n = len / 2;
        return b;
    }
    if (strncmp(word, "z:", 2) == 0) {
        int32_t size = wl_size(number, word + 2, word);
        *n = (size_t) size;
        uint8_t *b = xmalloc((size_t) size);
        memset(b, 0, (size_t) size);
        return b;
    }
    if (strncmp(word, "r:", 2) == 0) {
        const char *p = word + 2;
        const char *colon = strchr(p, ':');
        if (colon == NULL || strchr(colon + 1, ':') != NULL) {
            bad(number, "r:SEED:N expected: %s", word);
        }
        char seed_text[64];
        size_t sl = (size_t) (colon - p);
        if (sl == 0 || sl >= sizeof seed_text) {
            bad(number, "r:SEED:N expected: %s", word);
        }
        memcpy(seed_text, p, sl);
        seed_text[sl] = '\0';
        uint64_t seed = need_ulong(number, seed_text);
        int32_t size = wl_size(number, colon + 1, word);
        /* Workload.random: xorshift64* */
        uint64_t x = seed == 0 ? UINT64_C(0x9E3779B97F4A7C15) : seed;
        uint8_t *b = xmalloc((size_t) size);
        for (int32_t i = 0; i < size; i += 8) {
            x ^= x >> 12;
            x ^= x << 25;
            x ^= x >> 27;
            uint64_t w = x * UINT64_C(0x2545F4914F6CDD1D);
            for (int k = 0; k < 8 && i + k < size; k++) {
                b[i + k] = (uint8_t) (w >> (8 * k));
            }
        }
        *n = (size_t) size;
        return b;
    }
    bad(number, "bad value: %s", word);
    return NULL;
}

/* Workload.words: split on spaces and tabs; a word that starts with '#'
 * ends the line. */
static int split(char *text, char ***out) {
    int n = 0, cap = 8;
    char **w = xmalloc((size_t) cap * sizeof *w);
    char *p = text;
    for (;;) {
        while (*p == ' ' || *p == '\t' || *p == '\r' || *p == '\n' || *p == '\f'
                || *p == '\v') {
            p++;
        }
        if (*p == '\0') {
            break;
        }
        char *start = p;
        while (*p != '\0' && *p != ' ' && *p != '\t' && *p != '\r' && *p != '\n'
                && *p != '\f' && *p != '\v') {
            p++;
        }
        if (*p != '\0') {
            *p++ = '\0';
        }
        if (start[0] == '#') {
            break;
        }
        if (n == cap) {
            cap *= 2;
            w = xrealloc(w, (size_t) cap * sizeof *w);
        }
        w[n++] = start;
    }
    *out = w;
    return n;
}

static void need(int number, int nwords, char **words, int n) {
    if (nwords != n) {
        bad(number, "%s takes %d argument(s)", words[0], n - 1);
    }
}

static void check_trans(int number, char **words, int nwords) {
    if (nwords < 2) {
        bad(number, "t TIME|- OPS");
    }
    if (strcmp(words[1], "-") != 0) {
        wl_time(number, words[1]);
    }
    int i = 2;
    while (i < nwords) {
        size_t n;
        if (strcmp(words[i], "p") == 0 && i + 2 < nwords) {
            free(wl_key(number, words[i + 1], &n));
            free(wl_value(number, words[i + 2], &n));
            i += 3;
        } else if (strcmp(words[i], "d") == 0 && i + 1 < nwords) {
            free(wl_key(number, words[i + 1], &n));
            i += 2;
        } else {
            bad(number, "bad operation at word %d", i + 1);
        }
    }
}

static void setting(struct workload *w, int number, char **words, int nwords) {
    need(number, nwords, words, 3);
    const char *v = words[2];
    if (strcmp(words[1], "maxnode") == 0) {
        w->max_node = need_int(number, v);
        if (w->max_node != 8 && w->max_node != 14 && w->max_node != 30 && w->max_node != 62) {
            bad(number, "maxnode 8, 14, 30 or 62");
        }
    } else if (strcmp(words[1], "sd") == 0) {
        w->startup_distance = need_int(number, v);
    } else if (strcmp(words[1], "retain") == 0) {
        w->retain = retain_of(number, v);
        if (w->retain != INT64_MAX) {
            w->reclaims = true;
        }
    } else if (strcmp(words[1], "fraction") == 0) {
        need_double(number, v);
        w->fraction = v;
    } else if (strcmp(words[1], "budget") == 0) {
        w->budget = need_long(number, v);
    } else {
        bad(number, "unknown setting %s", words[1]);
    }
}

/* Workload.parse */
static void wl_read(const char *path, struct workload *w) {
    memset(w, 0, sizeof *w);
    w->max_node = 30;
    w->startup_distance = -1;
    w->retain = -1;
    w->budget = -1;
    w->segments = 1;
    FILE *f = fopen(path, "r");
    if (f == NULL) {
        fprintf(stderr, "Run: %s: %s\n", path, strerror(errno));
        exit(2);
    }
    bool header = false, settingsDone = false;
    int number = 0, segment = 0;
    char *text = NULL;
    size_t textcap = 0;
    ssize_t len;
    while ((len = getline(&text, &textcap, f)) >= 0) {
        number++;
        char *copy = xmalloc((size_t) len + 1);
        memcpy(copy, text, (size_t) len + 1);
        char **words;
        int nwords = split(copy, &words);
        if (nwords == 0) {
            free(words);
            free(copy);
            continue;
        }
        if (!header) {
            if (!(nwords == 2 && strcmp(words[0], "bergdb-workload") == 0
                    && strcmp(words[1], "1") == 0)) {
                bad(number, "expected \"bergdb-workload 1\"");
            }
            header = true;
            free(words);
            free(copy);
            continue;
        }
        const char *cmd = words[0];
        int trans = -1;
        if (strcmp(cmd, "set") == 0) {
            if (settingsDone) {
                bad(number, "a set line after the first operation");
            }
            setting(w, number, words, nwords);
            if (w->fraction == words[2]) {
                free(w->fraction_line);     /* copy stays: fraction points into it */
                w->fraction_line = copy;
            } else {
                free(copy);
            }
            free(words);
            continue;
        }
        if (strcmp(cmd, "clock") != 0) {
            settingsDone = true;
        }
        bool restart = false;
        if (strcmp(cmd, "t") == 0) {
            trans = w->trans_count++;
            check_trans(number, words, nwords);
        } else if (strcmp(cmd, "clock") == 0) {
            need(number, nwords, words, 2);
            wl_time(number, words[1]);
        } else if (strcmp(cmd, "now") == 0 || strcmp(cmd, "sync") == 0) {
            need(number, nwords, words, 1);
        } else if (strcmp(cmd, "restart") == 0) {
            need(number, nwords, words, 1);
            restart = true;
        } else if (strcmp(cmd, "setsd") == 0) {
            need(number, nwords, words, 2);
            need_int(number, words[1]);
        } else if (strcmp(cmd, "setretain") == 0) {
            need(number, nwords, words, 2);
            if (retain_of(number, words[1]) != INT64_MAX) {
                w->reclaims = true;
            }
        } else if (strcmp(cmd, "setfraction") == 0) {
            need(number, nwords, words, 2);
            need_double(number, words[1]);
        } else if (strcmp(cmd, "setbudget") == 0) {
            need(number, nwords, words, 2);
            need_long(number, words[1]);
        } else if (strcmp(cmd, "check") == 0) {
            need(number, nwords, words, 2);
            lookup_time(number, words[1]);
        } else if (strcmp(cmd, "get") == 0) {
            if (nwords < 3) {
                bad(number, "get TIME KEY...");
            }
            lookup_time(number, words[1]);
            for (int i = 2; i < nwords; i++) {
                size_t n;
                free(wl_key(number, words[i], &n));
            }
        } else {
            bad(number, "unknown command %s", cmd);
        }
        if (w->nlines == w->cap) {
            w->cap = w->cap == 0 ? 256 : w->cap * 2;
            w->lines = xrealloc(w->lines, (size_t) w->cap * sizeof *w->lines);
        }
        struct line *l = &w->lines[w->nlines++];
        l->number = number;
        l->text = copy;
        l->words = words;
        l->nwords = nwords;
        l->segment = segment;
        l->trans = trans;
        if (restart) {
            segment++;
            w->segments++;
        }
    }
    free(text);
    fclose(f);
    if (!header) {
        bad(0, "empty workload");
    }
}

/* ======== Text ======== */

/* Workload.keyText */
static void key_text(const uint8_t *bkey, size_t n, char *out) {
    static const char HEX_UPPER[] = "0123456789ABCDEF";
    size_t o = 0;
    for (size_t i = 0; i < n; i++) {
        int b = bkey[i];
        if (b == 1) {
            out[o++] = '/';
            continue;
        }
        int c = (b - 2) & 0xff;
        if (c >= 0x21 && c <= 0x7e && c != '%' && c != '/' && c != '=' && c != '#') {
            out[o++] = (char) c;
        } else {
            out[o++] = '%';
            out[o++] = HEX_UPPER[c >> 4];
            out[o++] = HEX_UPPER[c & 15];
        }
    }
    out[o] = '\0';
}

static char *keytext;
static size_t keytext_cap;

static const char *key_text_of(const uint8_t *bkey, size_t n) {
    if (3 * n + 1 > keytext_cap) {
        keytext_cap = 3 * n + 1;
        keytext = xrealloc(keytext, keytext_cap);
    }
    key_text(bkey, n, keytext);
    return keytext;
}

/* Run.value: "len=L sha256=H" */
static void value_text(const uint8_t *v, size_t len, char *out, size_t cap) {
    char h[65];
    sha256_hex(v, len, h);
    snprintf(out, cap, "len=%zu sha256=%s", len, h);
}

/* The simple name of Java's exception that bergdb_errmsg's text begins with. */
static const char *java_name(bergdb_db *db, const char *msg, char *out, size_t cap) {
    if (db != NULL) {
        msg = bergdb_errmsg(db);
    }
    size_t i = 0;
    while (msg[i] != '\0' && msg[i] != ':' && i + 1 < cap) {
        out[i] = msg[i];
        i++;
    }
    out[i] = '\0';
    if (i == 0) {
        snprintf(out, cap, "Unknown");
    }
    return out;
}

/* ======== The run (Run.java) ======== */

struct run {
    struct workload *w;
    const char *dir;
    FILE *out;
    bool verbose;
    struct bergdb_test_clock clock;
    bergdb_db *db;
    int refusals;
    struct sha256 reads;
    int64_t read_count;
    int64_t budget;             /* -budget N; -1: the workload's */
    bool mem_report;            /* -mem */
    struct bergdb_mem mem;      /* the allocator's counts, with -mem */
    int64_t max_resident;       /* the most resident bytes after a line of the segment */
    int64_t max_over;           /* the most resident bytes over the budget plus the pinned */
    int64_t max_pinned;         /* the most pinned bytes after a line of the segment */
};

static bool has_stream(const char *dir) {
    DIR *d = opendir(dir);
    if (d == NULL) {
        return false;
    }
    struct dirent *e;
    bool found = false;
    while ((e = readdir(d)) != NULL) {
        size_t n = strlen(e->d_name);
        if (n >= 7 && strcmp(e->d_name + n - 7, ".bergdb") == 0) {
            found = true;
            break;
        }
    }
    closedir(d);
    return found;
}

/* Run.start: the open of the segment; false after "start error=NAME". */
static bool start(struct run *r) {
    bool create = !has_stream(r->dir);
    struct bergdb_options opt;
    bergdb_options_init(&opt);
    /* testSetupExceptStream: the test clock (Run's), no eviction, retain
     * forever, the test id. */
    opt.clock = bergdb_test_clock_time;
    opt.clock_ctx = &r->clock;
    opt.cache_size_indicator = BERGDB_NO_EVICT;
    opt.retain_duration = BERGDB_FOREVER;
    memcpy(opt.id, bergdb_test_id, BERGDB_ID_SIZE);
    opt.max_node_size = r->w->max_node;
    if (r->w->startup_distance >= 0) {
        opt.startup_distance = (int32_t) r->w->startup_distance;
    }
    if (r->w->budget >= 0) {
        opt.cache_size_indicator = r->w->budget;
    }
    if (r->budget >= 0) {
        opt.cache_size_indicator = r->budget;
    }
    if (r->mem_report) {
        opt.mem = &r->mem;
    }
    if (r->w->retain >= 0) {
        opt.retain_duration = r->w->retain;
    }
    char errbuf[BERGDB_ERRBUF_SIZE];
    struct bergdb_start_info si;
    char name[128];
    int rc = bergdb_open(r->dir, &opt, &r->db, &si, errbuf);
    if (rc == BERGDB_OK && r->w->fraction != NULL) {
        rc = bergdb_set_reclaim_internal_fraction(r->db, need_double(0, r->w->fraction));
        if (rc != BERGDB_OK) {
            java_name(r->db, NULL, name, sizeof name);
            bergdb_close(r->db);
            r->db = NULL;
            fprintf(r->out, "start error=%s\n", name);
            return false;
        }
    }
    if (rc != BERGDB_OK) {
        fprintf(r->out, "start error=%s\n", java_name(NULL, errbuf, name, sizeof name));
        r->db = NULL;
        return false;
    }
    fprintf(r->out, "start create=%d startPos=%" PRId64 " startupDistance=%d startTime=%"
            PRId64 " transCount=%d lastPos=%" PRId64 "\n", create ? 1 : 0, si.start_pos,
            (int) si.startup_distance, si.start_time, (int) si.trans_count, si.last_pos);
    return true;
}

static void status(struct run *r) {
    struct bergdb_stats s;
    bergdb_stats(r->db, &s);
    fprintf(r->out, "status length=%" PRId64 " firstAvailablePos=%" PRId64
            " firstAvailableTime=%" PRId64 " startupDistance=%d\n", s.stream_length,
            s.first_available_pos, s.first_available_lookup_time, (int) s.startup_distance);
}

static void hex_of(const uint8_t *d, char out[65]) {
    static const char HEX[] = "0123456789abcdef";
    for (int i = 0; i < 32; i++) {
        out[2 * i] = HEX[d[i] >> 4];
        out[2 * i + 1] = HEX[d[i] & 15];
    }
    out[64] = '\0';
}

static void end_segment(struct run *r, int segment) {
    if (r->read_count > 0) {
        uint8_t d[32];
        char h[65];
        sha256_final(&r->reads, d);
        hex_of(d, h);
        fprintf(r->out, "reads n=%" PRId64 " sha256=%s\n", r->read_count, h);
        sha256_init(&r->reads);
        r->read_count = 0;
    }
    status(r);
    if (r->mem_report) {
        struct bergdb_stats s;
        bergdb_stats(r->db, &s);
        fprintf(stderr, "mem segment=%d resident=%" PRId64 " maxResident=%" PRId64
                " budget=%" PRId64 " pinned=%" PRId64 " maxPinned=%" PRId64 " maxOver=%" PRId64
                " evicted=%" PRId64 " live=%" PRId64 " peak=%" PRId64 " durable=%" PRId64 "\n",
                segment, s.resident_bytes, r->max_resident, s.cache_size_indicator,
                s.pinned_bytes, r->max_pinned, r->max_over, s.evicted, r->mem.live_total,
                r->mem.peak_total, s.durable_length);
        r->max_resident = r->max_pinned = r->max_over = 0;
    }
    bergdb_close(r->db);
    r->db = NULL;
    fprintf(r->out, "end segment=%d\n", segment);
}

/* Refused: a call returned an error. */
static void refused(struct run *r, const struct line *l) {
    char name[128];
    r->refusals++;
    java_name(r->db, NULL, name, sizeof name);
    if (strcmp(l->words[0], "t") == 0) {
        fprintf(r->out, "refused trans i=%d cmd=t error=%s\n", l->trans, name);
    } else {
        fprintf(r->out, "refused line=%d cmd=%s error=%s\n", l->number, l->words[0], name);
    }
}

static void set_clock(struct run *r, const struct line *l, int64_t t) {
    if (t <= r->clock.time) {
        bad(l->number, "time %" PRId64 " not after the clock's %" PRId64, t, r->clock.time);
    }
    bergdb_test_clock_set(&r->clock, t);
}

/* Run.trans */
static int trans(struct run *r, const struct line *l) {
    char **x = l->words;
    if (strcmp(x[1], "-") != 0) {
        set_clock(r, l, need_long(l->number, x[1]));
    }
    bergdb_trans *t;
    int rc = bergdb_trans_new(r->db, &t);
    if (rc != BERGDB_OK) {
        return rc;
    }
    for (int i = 2; i < l->nwords; ) {
        size_t kn, vn;
        uint8_t *key = wl_key(l->number, x[i + 1], &kn);
        if (strcmp(x[i], "p") == 0) {
            uint8_t *value = wl_value(l->number, x[i + 2], &vn);
            rc = bergdb_trans_put(t, key, kn, value, vn);
            free(value);
            i += 3;
        } else {
            rc = bergdb_trans_delete(t, key, kn);
            i += 2;
        }
        free(key);
        if (rc != BERGDB_OK) {
            bergdb_trans_free(t);
            return rc;
        }
    }
    struct bergdb_executed ex;
    rc = bergdb_execute(r->db, t, &ex);
    bergdb_trans_free(t);
    if (rc != BERGDB_OK) {
        return rc;
    }
    fprintf(r->out, "trans i=%d tt=%" PRId64 " tpos=%" PRId64 " lastPos=%" PRId64 "\n",
            l->trans, ex.tt, ex.tpos, ex.last_pos);
    return BERGDB_OK;
}

/* A check's pairs: each kv line digested (and printed with -v); none kept. */
struct check_ctx {
    struct run *r;
    struct sha256 md;
    int64_t count;
};

static int check_pair(void *ctx, const struct bergdb_kvt *kvt) {
    struct check_ctx *c = ctx;
    char v[128];
    if (kvt->value == NULL) {
        snprintf(v, sizeof v, "none");
    } else {
        value_text(kvt->value, kvt->value_len, v, sizeof v);
    }
    const char *k = key_text_of(kvt->key, kvt->key_len);
    size_t need = strlen(k) + strlen(v) + 96;
    char *line = xmalloc(need);
    snprintf(line, need, "kv key=%s %s time=%" PRId64 " pos=%" PRId64, k, v, kvt->time,
            kvt->pos);
    sha256_update(&c->md, (const uint8_t *) line, strlen(line));
    sha256_update(&c->md, (const uint8_t *) "\n", 1);
    if (c->r->verbose) {
        fprintf(c->r->out, "  %s\n", line);
    }
    free(line);
    c->count++;
    return BERGDB_CONTINUE;     /* digested here; nothing kept in the read context */
}

/* Run.check: the whole state at a time, getMany forward from the first key. */
static int check(struct run *r, int64_t time, const char *word) {
    bergdb_read *rd;
    int rc = bergdb_read_new(r->db, &rd);
    if (rc != BERGDB_OK) {
        return rc;
    }
    struct check_ctx c;
    c.r = r;
    c.count = 0;
    sha256_init(&c.md);
    struct bergdb_range range;
    bergdb_range_init(&range);
    range.lookup_time = time;
    range.stop = check_pair;
    range.stop_ctx = &c;
    struct bergdb_many many;
    rc = bergdb_get_many(r->db, rd, &range, &many);
    bergdb_read_free(rd);
    if (rc == BERGDB_NOT_AVAILABLE) {
        fprintf(r->out, "check at=%s unavailable\n", word);
        return BERGDB_OK;
    }
    if (rc != BERGDB_OK) {
        return rc;
    }
    uint8_t d[32];
    char h[65];
    sha256_final(&c.md, d);
    hex_of(d, h);
    fprintf(r->out, "check at=%s actual=%" PRId64 " count=%" PRId64 " sha256=%s\n", word,
            many.actual_lookup_time, c.count, h);
    return BERGDB_OK;
}

/* Run.get */
static int get(struct run *r, const struct line *l) {
    int64_t time = lookup_time(l->number, l->words[1]);
    bergdb_read *rd;
    int rc = bergdb_read_new(r->db, &rd);
    if (rc != BERGDB_OK) {
        return rc;
    }
    for (int i = 2; i < l->nwords; i++) {
        size_t kn;
        uint8_t *key = wl_key(l->number, l->words[i], &kn);
        const char *kt = key_text_of(key, kn);
        size_t need = strlen(kt) + strlen(l->words[1]) + 256;
        char *s = xmalloc(need);
        int o = snprintf(s, need, "get at=%s key=%s ", l->words[1], kt);
        struct bergdb_one one;
        rc = bergdb_get_one(r->db, rd, time, key, kn, &one);
        free(key);
        if (rc == BERGDB_NOT_AVAILABLE) {
            snprintf(s + o, need - (size_t) o, "unavailable");
        } else if (rc != BERGDB_OK) {
            free(s);
            bergdb_read_free(rd);
            return rc;
        } else if (one.value == NULL) {
            snprintf(s + o, need - (size_t) o, "none");
        } else {
            char v[128];
            value_text(one.value, one.value_len, v, sizeof v);
            snprintf(s + o, need - (size_t) o, "%s time=%" PRId64 " tpos=%" PRId64, v,
                    one.time, one.tpos);
        }
        sha256_update(&r->reads, (const uint8_t *) s, strlen(s));
        sha256_update(&r->reads, (const uint8_t *) "\n", 1);
        r->read_count++;
        if (r->verbose) {
            fprintf(r->out, "  %s\n", s);
        }
        free(s);
    }
    bergdb_read_free(rd);
    return BERGDB_OK;
}

/* Run.execute: one line; BERGDB_OK, or the call's error (a refusal). */
static int execute(struct run *r, const struct line *l) {
    char **x = l->words;
    const char *c = x[0];
    if (strcmp(c, "clock") == 0) {
        set_clock(r, l, need_long(l->number, x[1]));
        return BERGDB_OK;
    }
    if (strcmp(c, "t") == 0) {
        return trans(r, l);
    }
    if (strcmp(c, "now") == 0) {
        int64_t t;
        int rc = bergdb_current_time(r->db, &t);
        if (rc == BERGDB_OK) {
            fprintf(r->out, "now time=%" PRId64 "\n", t);
        }
        return rc;
    }
    if (strcmp(c, "sync") == 0) {
        int rc = bergdb_sync(r->db, 0, BERGDB_SYNC_STRONG);
        if (rc == BERGDB_OK) {
            status(r);
        }
        return rc;
    }
    if (strcmp(c, "restart") == 0) {
        end_segment(r, l->segment);
        return BERGDB_OK;
    }
    if (strcmp(c, "setsd") == 0) {
        return bergdb_set_startup_distance(r->db, need_int(l->number, x[1]));
    }
    if (strcmp(c, "setretain") == 0) {
        return bergdb_set_retain_duration(r->db, retain_of(l->number, x[1]));
    }
    if (strcmp(c, "setfraction") == 0) {
        return bergdb_set_reclaim_internal_fraction(r->db, need_double(l->number, x[1]));
    }
    if (strcmp(c, "setbudget") == 0) {
        return bergdb_set_cache_size_indicator(r->db, need_long(l->number, x[1]));
    }
    if (strcmp(c, "check") == 0) {
        return check(r, lookup_time(l->number, x[1]), x[1]);
    }
    if (strcmp(c, "get") == 0) {
        return get(r, l);
    }
    bad(l->number, "unknown command");
    return BERGDB_OK;
}

/* Run.run(from, to) */
static int run(struct run *r, int from, int to) {
    struct workload *w = r->w;
    fprintf(r->out, "bergdb-run 1\n");
    if (to > w->segments - 1) {
        to = w->segments - 1;
    }
    int li = 0;
    for (; li < w->nlines && w->lines[li].segment < from; li++) {
        /* Earlier segments: only the clock, which is kept across restarts. */
        const struct line *l = &w->lines[li];
        if (strcmp(l->words[0], "clock") == 0
                || (strcmp(l->words[0], "t") == 0 && strcmp(l->words[1], "-") != 0)) {
            bergdb_test_clock_set(&r->clock, need_long(l->number, l->words[1]));
        }
    }
    for (int segment = from; segment <= to; segment++) {
        fprintf(r->out, "segment i=%d\n", segment);
        sha256_init(&r->reads);
        r->read_count = 0;
        for (; li < w->nlines && w->lines[li].segment == segment; li++) {
            const struct line *l = &w->lines[li];
            if (strcmp(l->words[0], "clock") != 0 && r->db == NULL && !start(r)) {
                return 1;
            }
            if (execute(r, l) != BERGDB_OK) {
                refused(r, l);
            }
            if (r->mem_report && r->db != NULL) {
                struct bergdb_stats s;
                if (bergdb_stats(r->db, &s) == BERGDB_OK) {
                    if (s.resident_bytes > r->max_resident) {
                        r->max_resident = s.resident_bytes;
                    }
                    if (s.pinned_bytes > r->max_pinned) {
                        r->max_pinned = s.pinned_bytes;
                    }
                    int64_t free_bytes = s.resident_bytes - s.pinned_bytes;
                    int64_t over = free_bytes > s.cache_size_indicator
                            ? free_bytes - s.cache_size_indicator : 0;
                    if (over > r->max_over) {
                        r->max_over = over;
                    }
                }
            }
        }
        if (segment == w->segments - 1) {
            /* The last segment ends at the end of the workload, not at a restart. */
            if (r->db == NULL && !start(r)) {
                return 1;
            }
            end_segment(r, segment);
        }
    }
    return r->refusals == 0 ? 0 : 1;
}

static int usage(const char *msg) {
    fprintf(stderr, "Run: %s\n", msg);
    fprintf(stderr, "Usage: bergdb-run [-v] [-segments A[-B]] [-budget N] [-mem] WORKLOAD DIR\n");
    return 2;
}

int main(int argc, char **argv) {
    bool verbose = false;
    bool mem_report = false;
    int64_t budget = -1;
    int from = 0, to = INT_MAX;
    int i = 1;
    for (; i < argc && argv[i][0] == '-'; i++) {
        if (strcmp(argv[i], "-v") == 0) {
            verbose = true;
        } else if (strcmp(argv[i], "-segments") == 0 && i + 1 < argc) {
            const char *s = argv[++i];
            const char *dash = strchr(s, '-');
            char a[32];
            int64_t v;
            size_t al = dash == NULL ? strlen(s) : (size_t) (dash - s);
            if (al == 0 || al >= sizeof a) {
                return usage("bad -segments");
            }
            memcpy(a, s, al);
            a[al] = '\0';
            if (!parse_long(a, &v) || v < 0 || v > INT_MAX) {
                return usage("bad -segments");
            }
            from = (int) v;
            to = from;
            if (dash != NULL) {
                if (!parse_long(dash + 1, &v) || v < 0 || v > INT_MAX) {
                    return usage("bad -segments");
                }
                to = (int) v;
            }
        } else if (strcmp(argv[i], "-budget") == 0 && i + 1 < argc) {
            if (!parse_long(argv[++i], &budget) || budget < 1) {
                return usage("bad -budget");
            }
        } else if (strcmp(argv[i], "-mem") == 0) {
            mem_report = true;
        } else {
            return usage("unknown option");
        }
    }
    if (argc - i != 2) {
        return usage("WORKLOAD DIR expected");
    }
    wl_path = argv[i];
    struct workload w;
    wl_read(argv[i], &w);

    static char outbuf[1 << 16];
    setvbuf(stdout, outbuf, _IOFBF, sizeof outbuf);
    struct run r;
    memset(&r, 0, sizeof r);
    r.w = &w;
    r.dir = argv[i + 1];
    r.out = stdout;
    r.verbose = verbose;
    r.budget = budget;
    r.mem_report = mem_report;
    int status = run(&r, from, to);
    if (r.db != NULL) {
        bergdb_close(r.db);
    }
    /* The workload, freed, so that leaks finds nothing of the tool's. */
    for (int k = 0; k < w.nlines; k++) {
        free(w.lines[k].words);
        free(w.lines[k].text);
    }
    free(w.lines);
    free(w.fraction_line);
    fflush(stdout);
    return status;
}
