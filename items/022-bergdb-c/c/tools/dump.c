/*
 * bergdb-dump: C's dumper of a database directory (bergdb 012-08), the
 * text of Java's Dump (012-05, section 6.3, "bergdb-dump 1"), byte for
 * byte: the start, the status, the latest state forward and backward, the
 * state at sampled times, ranges and prefixes from sampled keys, getOne of
 * the sampled keys at the sampled times, and getTrans of every committed
 * record. The database is opened by the bounded startup (012-10, sdb.h:
 * Level 2, as Java's Db.start), which recovers a crashed stream as Java's
 * start does and writes its fill (so give it a copy, as Java's Dump says);
 * or, with -replay, read by a full replay of its stream (replay.h, 012-08,
 * Level 1), which writes nothing. Either way only databases without
 * reclaim's table and cut (012-11).
 *
 * Usage: bergdb-dump [-maxnode N] [-large] [-replay] [-check] DIR SCAN
 *   -maxnode N  the database's node size, 8, 14, 30 (default) or 62
 *   -large      the latest state as its digest only, the states at latest
 *               and the middle time only, getTrans of 1,000 records at most
 *   -replay     open by the full replay (Level 1), not the bounded startup
 *   -check      linkToCanonical's check by node id at the start, as Java's
 *               under -ea (005-57); it reads a header per pointer of D
 *
 * Or: bergdb-dump -probe [-maxnode N] [-check] DIR: the start alone, and one
 * line of what it rebuilt and read, the text of the probe of 012-10's
 * Progress (StartProbe, outside the repository): the startup position, D
 * (TransSeq.checksum), the newest written top node and the super root, the
 * node table (its handles, canonical and dirty objects, a CRC32 of its
 * entries sorted), the followers' loads, the reads of the files.
 * Exit: 0; 1 if the start failed (a line "start error=NAME"); 2 on bad
 * usage; 3 if C cannot read the database (an empty or a cut stream,
 * reclaim's table: 012-09 to 012-11), the reason on standard error, and
 * nothing printed after the header; 4 if the allocator's count is not 0 at
 * the end. On standard error, the last line: what the start read
 * ("bergdb-dump: start read ...").
 */
#define _POSIX_C_SOURCE 200809L
#include <inttypes.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "getmany.h"
#include "keys.h"
#include "mdb.h"
#include "mem.h"
#include "replay.h"
#include "sdb.h"
#include "sha256.h"
#include "snode.h"
#include "stream.h"

#define KEYS 48
#define TIMES 12
#define RANGES 12
#define TRANS_LARGE 1000

static void *xmalloc(size_t n) {
    void *p = malloc(n == 0 ? 1 : n);
    if (p == NULL) {
        fprintf(stderr, "bergdb-dump: out of memory\n");
        exit(5);
    }
    return p;
}

static void *xrealloc(void *p, size_t n) {
    void *q = realloc(p, n == 0 ? 1 : n);
    if (q == NULL) {
        fprintf(stderr, "bergdb-dump: out of memory\n");
        exit(5);
    }
    return q;
}

/* ======== The scan's samples (Dump.Scan) ======== */

struct bytes {
    uint8_t *p;
    int32_t n;
};

struct scan {
    int64_t *positions;         /* committed records */
    int64_t *times;
    int64_t npos, cappos;
    char **key_hex;             /* the keys' hex, sorted, distinct */
    int64_t nkeys, capkeys;
};

/* Dump.Scan.field: the value of " name=" in a line, into out; false if none. */
static bool field(const char *line, const char *name, char *out, size_t cap) {
    char key[32];
    snprintf(key, sizeof key, " %s=", name);
    const char *p = strstr(line, key);
    if (p == NULL) {
        return false;
    }
    p += strlen(key);
    size_t n = strcspn(p, " \n");
    if (n >= cap) {
        n = cap - 1;
    }
    memcpy(out, p, n);
    out[n] = '\0';
    return true;
}

static int cmp_str(const void *a, const void *b) {
    return strcmp(*(char *const *) a, *(char *const *) b);
}

static bool read_scan(const char *path, struct scan *s) {
    FILE *f = fopen(path, "r");
    if (f == NULL) {
        return false;
    }
    char *line = NULL;
    size_t cap = 0;
    ssize_t len;
    size_t vcap = 0;
    char *v = NULL;
    while ((len = getline(&line, &cap, f)) >= 0) {
        if ((size_t) len + 1 > vcap) {
            vcap = (size_t) len + 1;
            v = xrealloc(v, vcap);
        }
        if (strncmp(line, "record ", 7) == 0 && strstr(line, " time=") != NULL) {
            char pos[32], time[32];
            if (!field(line, "pos", pos, sizeof pos) || !field(line, "time", time, sizeof time)) {
                continue;
            }
            if (s->npos == s->cappos) {
                s->cappos = s->cappos == 0 ? 1024 : 2 * s->cappos;
                s->positions = xrealloc(s->positions, (size_t) s->cappos * sizeof(int64_t));
                s->times = xrealloc(s->times, (size_t) s->cappos * sizeof(int64_t));
            }
            s->positions[s->npos] = strtoll(pos, NULL, 10);
            s->times[s->npos] = strtoll(time, NULL, 10);
            s->npos++;
        } else if (strncmp(line, "value ", 6) == 0 || strncmp(line, "delete ", 7) == 0) {
            /* Dump.Scan.keys skips an empty key's hex */
            if (field(line, "key", v, vcap) && v[0] != '\0') {
                if (s->nkeys == s->capkeys) {
                    s->capkeys = s->capkeys == 0 ? 1024 : 2 * s->capkeys;
                    s->key_hex = xrealloc(s->key_hex, (size_t) s->capkeys * sizeof(char *));
                }
                s->key_hex[s->nkeys] = xmalloc(strlen(v) + 1);
                strcpy(s->key_hex[s->nkeys], v);
                s->nkeys++;
            }
        }
    }
    free(line);
    free(v);
    fclose(f);
    /* A TreeSet<String>: sorted, distinct. */
    qsort(s->key_hex, (size_t) s->nkeys, sizeof(char *), cmp_str);
    int64_t w = 0;
    for (int64_t i = 0; i < s->nkeys; i++) {
        if (w > 0 && strcmp(s->key_hex[w - 1], s->key_hex[i]) == 0) {
            free(s->key_hex[i]);
            continue;
        }
        s->key_hex[w++] = s->key_hex[i];
    }
    s->nkeys = w;
    return true;
}

static void free_scan(struct scan *s) {
    for (int64_t i = 0; i < s->nkeys; i++) {
        free(s->key_hex[i]);
    }
    free(s->key_hex);
    free(s->positions);
    free(s->times);
}

static int hexval(char c) {
    return c <= '9' ? c - '0' : (c | 0x20) - 'a' + 10;
}

/* Dump.sample's index: those at i * size / n. */
static int64_t sample_index(int64_t i, int64_t size, int64_t n) {
    return size <= n ? i : i * size / n;
}

static int64_t sample_count(int64_t size, int64_t n) {
    return size <= n ? size : n;
}

/* ======== Text ======== */

/* Workload.keyText */
static void key_text(const uint8_t *bkey, int32_t n, char *out) {
    static const char HEX_UPPER[] = "0123456789ABCDEF";
    size_t o = 0;
    for (int32_t i = 0; i < n; i++) {
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

/* Dump.time */
static void time_text(int64_t t, char *out, size_t cap) {
    if (t == INT64_MAX) {
        snprintf(out, cap, "latest");
    } else {
        snprintf(out, cap, "%" PRId64, t);
    }
}

/* ======== The dump ======== */

struct dump {
    FILE *out;
    struct mem mem;
    struct stream s;
    struct replay r;
    struct sdb sdb;
    bool use_replay;            /* -replay: the full replay, else the bounded startup */
    bool check;                 /* -check */
    bool large;
    char *keytext;              /* scratch for key_text: 3 bytes a key byte, and a 0 */
    size_t keytext_cap;
    uint8_t *keybytes;          /* scratch for Keys.toBytes */
    size_t keybytes_cap;
};

static char *key_text_of(struct dump *d, const uint8_t *bkey, int32_t n) {
    size_t need = 3 * (size_t) n + 1;
    if (need > d->keytext_cap) {
        d->keytext_cap = need;
        d->keytext = xrealloc(d->keytext, need);
    }
    key_text(bkey, n, d->keytext);
    return d->keytext;
}

/* Keys.toBytes(segments) into the scratch */
static uint8_t *key_bytes_of(struct dump *d, const int64_t *segs, int32_t n, int32_t *len) {
    size_t need = 7 * (size_t) n + 1;
    if (need > d->keybytes_cap) {
        d->keybytes_cap = need;
        d->keybytes = xrealloc(d->keybytes, need);
    }
    *len = keys_to_bytes(segs, n, d->keybytes);
    return d->keybytes;
}

/* Run.value: "len=L sha256=H" */
static void value_text(const uint8_t *v, int32_t len, char *out, size_t cap) {
    char h[65];
    sha256_hex(v, (size_t) len, h);
    snprintf(out, cap, "len=%d sha256=%s", (int) len, h);
}

/* A getMany's pairs: each kv line digested, printed or kept as asked. */
struct pairs {
    struct dump *d;
    struct sha256 md;
    int64_t count;
    bool print;                 /* print each kv line as it comes */
    bool keep;                  /* keep the lines in text, indented */
    char *text;
    size_t text_len, text_cap;
    uint8_t *last_key;          /* the last pair's bkey */
    int32_t last_key_n;
    size_t last_key_cap;
};

static bool pairs_add(void *ctx, const struct kvt *kvt) {
    struct pairs *p = ctx;
    struct dump *d = p->d;
    int32_t kn;
    uint8_t *k = key_bytes_of(d, kvt->key, kvt->key_n, &kn);
    if ((size_t) kn > p->last_key_cap) {
        p->last_key_cap = (size_t) kn;
        p->last_key = xrealloc(p->last_key, p->last_key_cap);
    }
    memcpy(p->last_key, k, (size_t) kn);
    p->last_key_n = kn;
    char *kt = key_text_of(d, k, kn);
    char vt[100];
    value_text(kvt->value->value, kvt->value->len, vt, sizeof vt);
    size_t need = strlen(kt) + strlen(vt) + 80;
    char *line = xmalloc(need);
    int n = snprintf(line, need, "kv key=%s %s time=%" PRId64 " pos=%" PRId64, kt, vt,
            kvt->time, kvt->spos);
    sha256_update(&p->md, (const uint8_t *) line, (size_t) n);
    sha256_update(&p->md, (const uint8_t *) "\n", 1);
    if (p->print) {
        fprintf(d->out, "%s\n", line);
    }
    if (p->keep) {
        size_t add = (size_t) n + 3;
        if (p->text_len + add + 1 > p->text_cap) {
            p->text_cap = 2 * (p->text_len + add + 1);
            p->text = xrealloc(p->text, p->text_cap);
        }
        memcpy(p->text + p->text_len, "  ", 2);
        memcpy(p->text + p->text_len + 2, line, (size_t) n);
        p->text[p->text_len + 2 + (size_t) n] = '\n';
        p->text_len += add;
        p->text[p->text_len] = '\0';
    }
    free(line);
    p->count++;
    return true;
}

static void pairs_init(struct pairs *p, struct dump *d) {
    memset(p, 0, sizeof *p);
    p->d = d;
    sha256_init(&p->md);
}

static void pairs_free(struct pairs *p) {
    free(p->text);
    free(p->last_key);
}

static void digest_hex(struct pairs *p, char out[65]) {
    uint8_t h[32];
    sha256_final(&p->md, h);
    for (int i = 0; i < 32; i++) {
        snprintf(out + 2 * i, 3, "%02x", h[i]);
    }
}

/* Dump.many: a getMany; false if the time is not available. Exits on a
 * failure of the read (NOMEM, or a database that cannot be read). */
static bool many(struct dump *d, int64_t time, const uint8_t *start, int32_t start_n, bool incl,
        bool fwd, const struct gm_stop *stop, struct pairs *p, int64_t *actual) {
    struct getmany g;
    struct mdb *db = &d->r.db;
    if (d->use_replay) {
        mdb_new_get_many(db, &g);
    } else {
        sdb_new_get_many(&d->sdb, &g);
    }
    g.lookup_time = time;
    int64_t *segs = NULL;
    if (start != NULL) {
        int32_t n = keys_segment_count(start_n);
        segs = xmalloc((size_t) n * sizeof *segs);
        keys_to_segments(start, start_n, segs);
        g.start_key = segs;
        g.start_key_n = n;
    }
    g.inclusive = incl;
    g.forward = fwd;
    if (stop != NULL) {
        g.stop_condition = *stop;
    }
    g.result.add = pairs_add;
    g.result.ctx = p;
    /* Db.getMany: the first available lookup time (reclaim's) */
    if (g.lookup_time < (d->use_replay ? d->r.first_available_time
            : d->sdb.first_available_time)) {
        free(segs);
        return false;
    }
    if (d->use_replay) {
        if (!mdb_get_many(db, &g)) {
            fprintf(stderr, "bergdb-dump: a getMany failed\n");
            exit(5);
        }
    } else {
        struct err e;
        err_clear(&e);
        if (sdb_get_many(&d->sdb, &g, &e) != ERR_OK) {
            fprintf(stderr, "bergdb-dump: a getMany failed: %s, %s\n", e.java, e.text);
            exit(5);
        }
    }
    *actual = g.actual_lookup_time;
    free(segs);
    return true;
}

/* Dump.state */
static void state(struct dump *d, int64_t t) {
    struct pairs p;
    pairs_init(&p, d);
    int64_t actual;
    char tt[32];
    time_text(t, tt, sizeof tt);
    if (many(d, t, NULL, 0, true, true, NULL, &p, &actual)) {
        char h[65];
        digest_hex(&p, h);
        fprintf(d->out, "state at=%s actual=%" PRId64 " count=%" PRId64 " sha256=%s\n", tt,
                actual, p.count, h);
    } else {
        fprintf(d->out, "state at=%s unavailable\n", tt);
    }
    pairs_free(&p);
}

/* Dump.range: its pairs in *p; false if not available. */
static bool range(struct dump *d, int64_t t, const uint8_t *start, int32_t start_n, bool incl,
        bool fwd, const struct gm_stop *stop, const char *stop_text, struct pairs *p) {
    pairs_init(p, d);
    p->keep = true;
    char tt[32];
    time_text(t, tt, sizeof tt);
    char *kt = key_text_of(d, start, start_n);
    fprintf(d->out, "range at=%s start=%s incl=%d fwd=%d stop=%s", tt, kt, incl ? 1 : 0,
            fwd ? 1 : 0, stop_text);
    int64_t actual;
    if (many(d, t, start, start_n, incl, fwd, stop, p, &actual)) {
        fprintf(d->out, " count=%" PRId64 "\n", p->count);
        if (p->text_len > 0) {
            fputs(p->text, d->out);
        }
        return true;
    }
    fprintf(d->out, " unavailable\n");
    return false;
}

/* Dump.trans */
static void trans(struct dump *d, int64_t pos) {
    const struct st_record *st;
    struct err e;
    err_clear(&e);
    enum err_code rc = d->use_replay ? replay_get_trans(&d->r, pos, &st, &e)
            : sdb_get_trans(&d->sdb, pos, &st, &e);
    if (rc == ERR_NOT_AVAILABLE) {
        fprintf(d->out, "trans pos=%" PRId64 " unavailable\n", pos);
        return;
    }
    if (rc != ERR_OK) {
        fprintf(d->out, "trans pos=%" PRId64 " error=%s\n", pos, e.java);
        return;
    }
    int32_t values = 0;
    for (int32_t i = 0; i < st->nnodes; i++) {
        if (st->nodes[i].type == NODE_VALUE || st->nodes[i].type == NODE_DELETE) {
            values++;
        }
    }
    fprintf(d->out, "trans pos=%" PRId64 " tt=%" PRId64 " lastPos=%" PRId64 " startupPos=%"
            PRId64 " topPos=%" PRId64 " values=%d\n", st->tpos, st->tt, st->last_pos,
            st->startup_pos, st->top_pos, (int) values);
    int64_t *segs = NULL;
    for (int32_t i = 0; i < st->nnodes; i++) {
        const struct sn_node *n = &st->nodes[i];
        if (n->type != NODE_VALUE && n->type != NODE_DELETE) {
            continue;
        }
        segs = xrealloc(segs, (size_t) n->key_n * sizeof *segs);
        for (int32_t j = 0; j < n->key_n; j++) {
            segs[j] = sn_seg(n, j);
        }
        int32_t kn;
        uint8_t *k = key_bytes_of(d, segs, n->key_n, &kn);
        char *kt = key_text_of(d, k, kn);
        if (n->type == NODE_DELETE) {
            fprintf(d->out, "  delete key=%s\n", kt);
        } else {
            char vt[100];
            value_text(n->value, n->value_len, vt, sizeof vt);
            fprintf(d->out, "  value key=%s %s\n", kt, vt);
        }
    }
    free(segs);
}

/* The times of the samples: a LinkedHashSet<Long>. */
struct times {
    int64_t *t;
    int64_t n, cap;
};

static void times_add(struct times *ts, int64_t t) {
    for (int64_t i = 0; i < ts->n; i++) {
        if (ts->t[i] == t) {
            return;
        }
    }
    if (ts->n == ts->cap) {
        ts->cap = ts->cap == 0 ? 32 : 2 * ts->cap;
        ts->t = xrealloc(ts->t, (size_t) ts->cap * sizeof *ts->t);
    }
    ts->t[ts->n++] = t;
}

static int dump(struct dump *d, const char *dir, const char *scan_path, int32_t max_node) {
    FILE *out = d->out;
    fputs("bergdb-dump 1\n", out);
    struct scan sc;
    memset(&sc, 0, sizeof sc);
    if (!read_scan(scan_path, &sc)) {
        fprintf(stderr, "bergdb-dump: cannot read %s\n", scan_path);
        return 2;
    }

    struct err e;
    err_clear(&e);
    enum err_code rc;
    int64_t startPos, startTime, lastPos, length;
    int32_t transCount, startupDistance;
    int64_t firstPos, firstTime;
    if (d->use_replay) {
        if (stream_open_dir(&d->s, dir, &d->mem, &e) != ERR_OK) {
            free_scan(&sc);
            fprintf(stderr, "bergdb-dump: the directory %s: %s, %s\n", dir, e.java, e.text);
            return 3;
        }
        rc = replay_open(&d->r, &d->s, &d->mem, max_node, &e);
    } else {
        if (stream_open_dir_rw(&d->s, dir, 0, &d->mem, &e) != ERR_OK) {
            free_scan(&sc);
            fprintf(stderr, "bergdb-dump: the directory %s: %s, %s\n", dir, e.java, e.text);
            return 3;
        }
        rc = sdb_open(&d->sdb, &d->s, &d->mem, max_node, d->check, &e);
    }
    if (rc != ERR_OK) {
        /* Java's start that throws closes its storage: what the start
         * appended (recovery's fill) is written (005-32). */
        struct err e2;
        if (d->use_replay) {
            stream_close(&d->s);
        } else if (stream_finish(&d->s, &e2) != ERR_OK) {
            fprintf(stderr, "bergdb-dump: the close failed: %s, %s\n", e2.java, e2.text);
        }
        free_scan(&sc);
        if (strcmp(e.java, "UnsupportedOperationException") == 0) {
            fprintf(stderr, "bergdb-dump: C cannot read this database: %s\n", e.text);
            return 3;
        }
        fprintf(out, "start error=%s\n", e.java);
        fprintf(stderr, "bergdb-dump: the start failed: %s, %s\n", e.java, e.text);
        return 1;
    }
    if (d->use_replay) {
        struct replay *r = &d->r;
        startPos = r->start_pos;
        startTime = r->start_time;
        transCount = r->trans_count;
        lastPos = r->last_pos;
        length = r->length;
        startupDistance = r->startup_distance;
        firstPos = r->first_available_pos;
        firstTime = r->first_available_time;
    } else {
        struct sdb *b = &d->sdb;
        startPos = b->start.start_pos;
        startTime = b->start.start_time;
        transCount = b->start.trans_count;
        lastPos = b->start.last_pos;
        length = stream_length(&d->s);
        startupDistance = b->start.startup_distance;
        firstPos = b->first_available_pos;
        firstTime = b->first_available_time;
        fprintf(stderr, "bergdb-dump: start read %" PRId64 " records walked (%" PRId64
                " bytes), %" PRId64 " section records (%" PRId64 " bytes), %" PRId64
                " nodes, %" PRId64 " loads, %" PRId64 " headers; %" PRId64 " pairs rerun\n",
                b->start.walk_records, b->start.walk_bytes, b->start.section_records,
                b->start.section_bytes, b->nc.reads, b->nc.loads, b->nc.header_reads,
                b->start.rerun_pairs);
    }
    /* Java's StartInfo.startupDistance: the distance in force after the start
     * since bergdb 005-73, F1 (release 2026.2); -1 before. */
    fprintf(out, "start startPos=%" PRId64 " startupDistance=%d startTime=%" PRId64
            " transCount=%d lastPos=%" PRId64 "\n", startPos, (int) startupDistance, startTime,
            (int) transCount, lastPos);

    fprintf(out, "status length=%" PRId64 " firstAvailablePos=%" PRId64 " firstAvailableTime=%"
            PRId64 " startupDistance=%d\n", length, firstPos, firstTime, (int) startupDistance);

    /* The latest state, forward and backward. */
    struct pairs p;
    char h[65];
    int64_t actual;
    pairs_init(&p, d);
    p.print = !d->large;
    many(d, INT64_MAX, NULL, 0, true, true, NULL, &p, &actual);
    digest_hex(&p, h);
    fprintf(out, "latest count=%" PRId64 " sha256=%s\n", p.count, h);
    pairs_free(&p);
    pairs_init(&p, d);
    many(d, INT64_MAX, NULL, 0, true, false, NULL, &p, &actual);
    digest_hex(&p, h);
    fprintf(out, "backward count=%" PRId64 " sha256=%s\n", p.count, h);
    pairs_free(&p);

    /* The samples: the keys, sorted by their bytes. */
    int64_t nk = sample_count(sc.nkeys, KEYS);
    struct bytes *keys = xmalloc((size_t) (nk == 0 ? 1 : nk) * sizeof *keys);
    for (int64_t i = 0; i < nk; i++) {
        const char *hx = sc.key_hex[sample_index(i, sc.nkeys, KEYS)];
        int32_t n = (int32_t) (strlen(hx) / 2);
        keys[i].p = xmalloc((size_t) n + 1);
        keys[i].n = n;
        for (int32_t j = 0; j < n; j++) {
            keys[i].p[j] = (uint8_t) (hexval(hx[2 * j]) * 16 + hexval(hx[2 * j + 1]));
        }
    }
    /* The times: of the records at or after firstPos. */
    int64_t *rt = xmalloc((size_t) (sc.npos + 1) * sizeof *rt);
    int64_t nrt = 0;
    for (int64_t i = 0; i < sc.npos; i++) {
        if (sc.positions[i] >= firstPos) {
            rt[nrt++] = sc.times[i];
        }
    }
    struct times ts = { NULL, 0, 0 };
    for (int64_t i = 0; i < sample_count(nrt, TIMES); i++) {
        int64_t t = rt[sample_index(i, nrt, TIMES)];
        times_add(&ts, t - 1);
        times_add(&ts, t);
    }
    times_add(&ts, INT64_MAX);
    if (firstTime > 0) {
        times_add(&ts, firstTime - 1);  /* before the first available time */
    }
    free(rt);

    /* The state at the sampled times (-large: at latest and at the middle time). */
    int64_t middle = ts.n > 2 ? ts.t[ts.n / 2] : INT64_MAX;
    if (d->large) {
        state(d, INT64_MAX);
        state(d, middle);
    } else {
        for (int64_t i = 0; i < ts.n; i++) {
            state(d, ts.t[i]);
        }
    }

    /* Ranges, at latest and at the middle time, from each range key. */
    int64_t nrk = sample_count(nk, RANGES);
    int64_t rtimes[2] = { INT64_MAX, middle };
    for (int ti = 0; ti < 2; ti++) {
        int64_t t = rtimes[ti];
        for (int64_t ki = 0; ki < nrk; ki++) {
            const struct bytes *key = &keys[sample_index(ki, nk, RANGES)];
            uint8_t *after = xmalloc((size_t) key->n + 1);
            memcpy(after, key->p, (size_t) key->n);
            after[key->n] = 0x23;           /* the ikey character '!' */
            uint8_t *k2 = NULL;
            int32_t k2n = -1;               /* -1: null; 0: new byte[0] */
            for (int si = 0; si < 2; si++) {
                const uint8_t *start = si == 0 ? key->p : after;
                int32_t sn = si == 0 ? key->n : key->n + 1;
                for (int incl = 1; incl >= 0; incl--) {
                    for (int fwd = 1; fwd >= 0; fwd--) {
                        struct gm_get_n gn;
                        struct gm_stop stop = gm_get_n(&gn, 5);
                        struct pairs rp;
                        bool ok = range(d, t, start, sn, incl == 1, fwd == 1, &stop, "get5",
                                &rp);
                        if (k2n < 0 && ok && rp.count >= 2) {
                            k2 = xmalloc((size_t) rp.last_key_n + 1);
                            memcpy(k2, rp.last_key, (size_t) rp.last_key_n);
                            k2n = rp.last_key_n;
                        }
                        if (k2n < 0) {
                            k2n = 0;
                        }
                        pairs_free(&rp);
                    }
                }
            }
            if (k2n > 0) {
                int32_t n2 = keys_segment_count(k2n);
                int64_t *s2 = xmalloc((size_t) n2 * sizeof *s2);
                keys_to_segments(k2, k2n, s2);
                int32_t n1 = keys_segment_count(key->n);
                int64_t *s1 = xmalloc((size_t) n1 * sizeof *s1);
                keys_to_segments(key->p, key->n, s1);

                size_t cap = 3 * (size_t) (k2n > key->n ? k2n : key->n) + 40;
                char *text = xmalloc(cap);
                struct gm_endpoint ep;
                struct gm_stop stop = gm_endpoint(&ep, s2, n2, true, false);
                snprintf(text, cap, "to=%s endIncl=1", key_text_of(d, k2, k2n));
                struct pairs rp;
                range(d, t, key->p, key->n, true, true, &stop, text, &rp);
                pairs_free(&rp);
                stop = gm_endpoint(&ep, s1, n1, false, true);
                snprintf(text, cap, "to=%s endIncl=0", key_text_of(d, key->p, key->n));
                range(d, t, k2, k2n, true, false, &stop, text, &rp);
                pairs_free(&rp);
                free(text);
                free(s1);
                free(s2);
            }
            int32_t pn = (key->n + 1) / 2;
            int32_t nps = keys_segment_count(pn);
            int64_t *ps = xmalloc((size_t) nps * sizeof *ps);
            keys_to_segments(key->p, pn, ps);
            struct gm_prefix_n pfx;
            struct gm_stop stop = gm_prefix_n(&pfx, ps, nps, 10);
            struct pairs rp;
            range(d, t, key->p, pn, true, true, &stop, "prefix10", &rp);
            pairs_free(&rp);
            free(ps);
            free(k2);
            free(after);
        }
    }

    /* getOne of the sampled keys at the sampled times. */
    struct getdata gd;
    if (d->use_replay) {
        mdb_new_get_data(&d->r.db, &gd);
    } else {
        sdb_new_get_data(&d->sdb, &gd);
    }
    for (int64_t ki = 0; ki < nk; ki++) {
        const struct bytes *key = &keys[ki];
        int32_t n = keys_segment_count(key->n);
        int64_t *segs = xmalloc((size_t) n * sizeof *segs);
        keys_to_segments(key->p, key->n, segs);
        for (int64_t i = 0; i < ts.n; i++) {
            int64_t t = ts.t[i];
            char tt[32];
            time_text(t, tt, sizeof tt);
            fprintf(out, "one at=%s key=%s ", tt, key_text_of(d, key->p, key->n));
            if (t < firstTime) {
                fputs("unavailable\n", out);
                continue;
            }
            struct vnode *v;
            if (d->use_replay) {
                if (!mdb_get_one(&d->r.db, t, segs, n, &gd, &v)) {
                    fprintf(stderr, "bergdb-dump: a getOne failed\n");
                    exit(5);
                }
            } else if (sdb_get_one(&d->sdb, t, segs, n, &gd, &v, &e) != ERR_OK) {
                fprintf(stderr, "bergdb-dump: a getOne failed: %s, %s\n", e.java, e.text);
                exit(5);
            }
            if (v == NULL) {
                fputs("none\n", out);
            } else {
                char vt[100];
                value_text(v->value, v->len, vt, sizeof vt);
                fprintf(out, "%s time=%" PRId64 " tpos=%" PRId64 "\n", vt, gd.kv_time, gd.tpos);
            }
        }
        free(segs);
    }

    /* getTrans of every committed record at or after the first available position. */
    int64_t *positions = xmalloc((size_t) (sc.npos + 1) * sizeof *positions);
    int64_t np = 0;
    for (int64_t i = 0; i < sc.npos; i++) {
        if (sc.positions[i] >= firstPos) {
            positions[np++] = sc.positions[i];
        }
    }
    if (d->large) {
        for (int64_t i = 0; i < sample_count(np, TRANS_LARGE); i++) {
            trans(d, positions[sample_index(i, np, TRANS_LARGE)]);
        }
    } else {
        for (int64_t i = 0; i < np; i++) {
            trans(d, positions[i]);
        }
    }
    free(positions);

    if (d->use_replay) {
        replay_close(&d->r);
        stream_close(&d->s);
    } else {
        sdb_close(&d->sdb);
        if (stream_finish(&d->s, &e) != ERR_OK) {
            fprintf(stderr, "bergdb-dump: the close failed: %s, %s\n", e.java, e.text);
            exit(5);
        }
    }
    fputs("end\n", out);

    for (int64_t i = 0; i < nk; i++) {
        free(keys[i].p);
    }
    free(keys);
    free(ts.t);
    free_scan(&sc);
    return 0;
}

/* ======== -probe ======== */

static int cmp_cstr(const void *a, const void *b) {
    return strcmp(*(char *const *) a, *(char *const *) b);
}

/* java.util.zip.CRC32's update */
static uint32_t crc32_update(uint32_t crc, const uint8_t *p, size_t n) {
    crc = ~crc;
    for (size_t i = 0; i < n; i++) {
        crc ^= p[i];
        for (int k = 0; k < 8; k++) {
            crc = (crc >> 1) ^ (0xedb88320u & (0u - (crc & 1u)));
        }
    }
    return ~crc;
}

static int probe(struct dump *d, const char *dir, int32_t max_node) {
    struct err e;
    err_clear(&e);
    if (stream_open_dir_rw(&d->s, dir, 0, &d->mem, &e) != ERR_OK) {
        fprintf(stderr, "bergdb-dump: the directory %s: %s, %s\n", dir, e.java, e.text);
        return 3;
    }
    enum err_code rc = sdb_open(&d->sdb, &d->s, &d->mem, max_node, d->check, &e);
    if (rc != ERR_OK) {
        struct err e2;
        stream_finish(&d->s, &e2);
        printf("probe dir=%s error=%s\n", dir, e.java);
        return rc == ERR_ARG ? 3 : 1;
    }
    struct sdb *b = &d->sdb;
    int64_t reads = d->s.file_reads, bytes = d->s.file_read_bytes;
    int64_t nh = nt_size(&b->nt);
    char **lines = xmalloc((size_t) (nh == 0 ? 1 : nh) * sizeof *lines);
    int64_t k = 0, canonical = 0, dirty = 0;
    for (int64_t i = 0; i < nt_slots(&b->nt); i++) {
        struct handle *h = nt_slot(&b->nt, i);
        if (h == NULL) {
            continue;
        }
        char line[80];
        struct node *o = h->obj;
        if (o == NULL) {
            snprintf(line, sizeof line, "%" PRId64 ":-", h->id);
        } else {
            snprintf(line, sizeof line, "%" PRId64 ":%" PRId64 "%s%s", h->id, o->spos,
                    node_is_canonical(o) ? "c" : "", node_is_dirty(o) ? "d" : "");
            canonical += node_is_canonical(o) ? 1 : 0;
            dirty += node_is_dirty(o) ? 1 : 0;
        }
        lines[k] = xmalloc(strlen(line) + 1);
        strcpy(lines[k], line);
        k++;
    }
    qsort(lines, (size_t) k, sizeof *lines, cmp_cstr);
    uint32_t crc = 0;
    for (int64_t i = 0; i < k; i++) {
        crc = crc32_update(crc, (const uint8_t *) lines[i], strlen(lines[i]));
        crc = crc32_update(crc, (const uint8_t *) "\n", 1);
        free(lines[i]);
    }
    /* The canonical objects' contents: a key node's klongs, references and the
     * references the record rule would write now; a top node's ordinal, root
     * time, references and written references. */
    int64_t nc = 0;
    for (int64_t i = 0; i < nt_slots(&b->nt); i++) {
        struct handle *h = nt_slot(&b->nt, i);
        if (h == NULL || h->obj == NULL || !node_is_canonical(h->obj)) {
            continue;
        }
        struct node *o = h->obj;
        size_t cap = 64 + 72 * (size_t) (node_size(o) + 1);
        char *line = xmalloc(cap);
        int len = snprintf(line, cap, "%" PRId64 ":%" PRId64, o->id, o->spos);
        if (node_type(o) == NODE_TYPE_KEY_NODE) {
            const struct knode *kn = (const struct knode *) o;
            len += snprintf(line + len, cap - (size_t) len, ":K%d", (int) kn->size);
            for (int32_t j = 0; j < kn->size; j++) {
                len += snprintf(line + len, cap - (size_t) len, ",%" PRId64 "/%" PRId64 "/%"
                        PRId64, kn->klongs[j], kn_get_pointer_pos(kn, j),
                        kn_get_serialized_ref(kn, j));
            }
        } else {
            const struct tnode *tn = (const struct tnode *) o;
            len += snprintf(line + len, cap - (size_t) len, ":T%" PRId64 "/%" PRId64,
                    tn->top_node_id, tn->root_time);
            for (int32_t j = 0; j < tn_get_size(tn); j++) {
                len += snprintf(line + len, cap - (size_t) len, ",%" PRId64 "/%" PRId64,
                        tn_get_pointer_pos(tn, j), tn_get_serialized_ref(tn, j));
            }
        }
        lines[nc++] = line;
    }
    qsort(lines, (size_t) nc, sizeof *lines, cmp_cstr);
    uint32_t crc2 = 0;
    for (int64_t i = 0; i < nc; i++) {
        crc2 = crc32_update(crc2, (const uint8_t *) lines[i], strlen(lines[i]));
        crc2 = crc32_update(crc2, (const uint8_t *) "\n", 1);
        free(lines[i]);
    }
    free(lines);
    struct tnode *top = b->newest_written_top;
    struct tnode *sr = tds_get_super_root(&b->dag.top_ds);
    printf("probe dir=%s startPos=%" PRId64 " transCount=%d startupPos=%" PRId64 " D=%" PRId64
            " Dsize=%d top=%" PRId64 "@%" PRId64 " superRoot=%" PRId64 "@%" PRId64
            " handles=%" PRId64 " canonical=%" PRId64 " dirty=%" PRId64 " table=%" PRIx32
            " content=%" PRIx32 " loads=%" PRId64 " reads=%" PRId64 " bytes=%" PRId64 "\n", dir,
            b->start.start_pos, (int) b->start.trans_count, b->start.startup_pos,
            ts_checksum(&b->ts), (int) ts_size(&b->ts), top->n.id, top->n.spos, sr->n.id,
            sr->n.spos, k, canonical, dirty, crc, crc2, b->nc.loads, reads, bytes);
    sdb_close(b);
    if (stream_finish(&d->s, &e) != ERR_OK) {
        fprintf(stderr, "bergdb-dump: the close failed: %s, %s\n", e.java, e.text);
        return 5;
    }
    return 0;
}

int main(int argc, char **argv) {
    int32_t maxNode = 30;
    bool large = false, replay = false, check = false, probeOnly = false;
    int i = 1;
    for (; i < argc && argv[i][0] == '-'; i++) {
        if (strcmp(argv[i], "-maxnode") == 0 && i + 1 < argc) {
            maxNode = (int32_t) strtol(argv[++i], NULL, 10);
        } else if (strcmp(argv[i], "-large") == 0) {
            large = true;
        } else if (strcmp(argv[i], "-replay") == 0) {
            replay = true;
        } else if (strcmp(argv[i], "-check") == 0) {
            check = true;
        } else if (strcmp(argv[i], "-probe") == 0) {
            probeOnly = true;
        } else {
            fprintf(stderr, "Dump: unknown option %s\n", argv[i]);
            fprintf(stderr, "Usage: bergdb-dump [-maxnode N] [-large] [-replay] [-check] DIR "
                    "SCAN\n");
            return 2;
        }
    }
    if (probeOnly && argc - i == 1) {
        static struct dump pd;
        pd.check = check;
        mem_init(&pd.mem);
        int st = probe(&pd, argv[i], maxNode);
        fflush(stdout);
        if (pd.mem.live_total != 0) {
            fprintf(stderr, "bergdb-dump: %" PRId64 " bytes live at the end\n", pd.mem.live_total);
            return 4;
        }
        return st;
    }
    if (argc - i != 2 || (maxNode != 8 && maxNode != 14 && maxNode != 30 && maxNode != 62)) {
        fprintf(stderr, "Usage: bergdb-dump [-maxnode N] [-large] DIR SCAN\n");
        return 2;
    }
    static char outbuf[1 << 16];
    setvbuf(stdout, outbuf, _IOFBF, sizeof outbuf);
    static struct dump d;
    d.out = stdout;
    d.large = large;
    d.use_replay = replay;
    d.check = check;
    mem_init(&d.mem);
    int status = dump(&d, argv[i], argv[i + 1], maxNode);
    fflush(stdout);
    free(d.keytext);
    free(d.keybytes);
    if (d.mem.live_total != 0) {
        fprintf(stderr, "bergdb-dump: %" PRId64 " bytes live at the end\n", d.mem.live_total);
        return 4;
    }
    return status;
}
