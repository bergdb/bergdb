/* reclaim: Java's Reclaim; see reclaim.h. Java's names in the comments. */
#include "reclaim.h"
#include <assert.h>
#include <inttypes.h>
#include <stdio.h>
#include <string.h>
#include "db.h"
#include "getmany.h"
#include "jsem.h"
#include "keys.h"
#include "node.h"
#include "spos.h"
#include "strmap.h"
#include "trans.h"
#include "vnode.h"

#define NEXT_SEPARATOR "----next----"

static enum err_code nomem(struct err *e) {
    return err_set(e, ERR_NOMEM, "OutOfMemoryError", "out of memory");
}

static void key_segments(const char *ikey, int64_t *segs, int32_t *n) {
    uint8_t bkey[64];
    const int32_t len = (int32_t) strlen(ikey);
    bool ok = keys_ikey_to_bkey((const uint8_t *) ikey, len, bkey);
    assert(ok && keys_segment_count(len) <= 8);
    (void) ok;
    keys_to_segments(bkey, len, segs);
    *n = keys_segment_count(len);
}

void rc_init(struct reclaim *r, struct mem *m) {
    memset(r, 0, sizeof *r);
    r->mem = m;
    key_segments(RC_TABLE_KEY_NAME, r->tableKey, &r->tableKey_n);
    key_segments(RC_CURRENT_KEY_NAME, r->currentKey, &r->currentKey_n);
    r->retainDuration = INT64_MAX;
    r->internalFraction = RC_DEFAULT_INTERNAL_FRACTION;
    r->iterationCount = 0;
    r->pendingCut = -1;
    r->stepReserve = RC_DEFAULT_STEP_RESERVE;
}

void rc_row_free(struct mem *m, struct rc_row *row) {
    if (row->lastKey != NULL) {
        mem_free(m, row->lastKey, (size_t) row->lastKey_n * sizeof *row->lastKey, MEM_STATE);
    }
    row->lastKey = NULL;
    row->lastKey_n = 0;
    row->lastKeyNull = true;
}

void rc_free(struct reclaim *r) {
    for (int32_t i = 0; i < r->nrows; i++) {
        rc_row_free(r->mem, &r->rows[i]);
    }
    mem_free(r->mem, r->rows, (size_t) r->cap * sizeof *r->rows, MEM_STATE);
    r->rows = NULL;
    r->nrows = 0;
    r->cap = 0;
}

/* row->lastKey = a copy of key (NULL: null). false on NOMEM, the row as
 * before. */
static bool row_set_last_key(struct mem *m, struct rc_row *row, const int64_t *key,
        int32_t n, bool isNull) {
    int64_t *copy = NULL;
    if (!isNull && n > 0) {
        copy = mem_alloc(m, (size_t) n * sizeof *copy, MEM_STATE);
        if (copy == NULL) {
            return false;
        }
        memcpy(copy, key, (size_t) n * sizeof *copy);
    }
    rc_row_free(m, row);
    row->lastKey = copy;
    row->lastKey_n = isNull ? 0 : n;
    row->lastKeyNull = isNull;
    return true;
}

/* IterationInfo.set(o), o's lastKey moved into row (o's left null). */
static void row_move(struct mem *m, struct rc_row *row, struct rc_row *o) {
    rc_row_free(m, row);
    *row = *o;
    o->lastKey = NULL;
    o->lastKey_n = 0;
    o->lastKeyNull = true;
}

/* ======== Settings ======== */

enum err_code rc_set_retain_duration(struct reclaim *r, int64_t d, struct err *e) {
    const int64_t SMALLEST = 1 * INT64_C(10000000);     /* 1 * Clock.UNITS_PER_SEC */
    if (d < SMALLEST) {
        return err_set(e, ERR_ARG, "IllegalArgumentException", "retainDuration = %" PRId64
                " is too small.", d);
    }
    r->retainDuration = d;
    return ERR_OK;
}

enum err_code rc_set_internal_fraction(struct reclaim *r, double f, struct err *e) {
    if (f < 0.001 || f > 0.90) {
        return err_set(e, ERR_ARG, "IllegalArgumentException", "Illegal internalFraction "
                "value, %.17g", f);
    }
    r->internalFraction = f;
    return ERR_OK;
}

enum err_code rc_set_step_reserve(struct reclaim *r, int64_t bytes, struct err *e) {
    if (bytes < 1) {
        return err_set(e, ERR_ARG, "IllegalArgumentException", "Illegal step reserve, %" PRId64,
                bytes);
    }
    r->stepReserve = bytes;
    return ERR_OK;
}

/* ======== The texts ======== */

size_t rc_row_text_cap(const struct rc_row *row) {
    /* 11 names with '=' and '\n' (under 140 bytes), 9 numbers of at most 20
     * characters, two booleans, and the key's segments, 21 each. */
    return 400 + 21 * (size_t) (row->lastKeyNull ? 1 : row->lastKey_n);
}

size_t rc_row_text(const struct rc_row *row, char *buf, size_t cap) {
    /* StringMap.serialize in HashMap's order for these 11 names (012-02,
     * 8.13; t_reclaim.c checks it against sm_serialize). */
    size_t o = 0;
#define PUT(...) o += (size_t) snprintf(buf + o, cap - o, __VA_ARGS__)
    assert(cap >= rc_row_text_cap(row));
    PUT("pCut=%" PRId64 "\n", row->pCut);
    PUT("tEnd=%" PRId64 "\n", row->tEnd);
    PUT("cut=%s\n", row->cut ? "true" : "false");
    PUT("pStart=%" PRId64 "\n", row->pStart);
    PUT("tStart=%" PRId64 "\n", row->tStart);
    if (row->lastKeyNull) {
        PUT("lastKey=null\n");
    } else {
        /* b.append(l + " ") for each segment, then trim() */
        PUT("lastKey=");
        for (int32_t i = 0; i < row->lastKey_n; i++) {
            PUT(i == 0 ? "%" PRId64 : " %" PRId64, row->lastKey[i]);
        }
        PUT("\n");
    }
    PUT("rewritten=%" PRId64 "\n", row->rewritten);
    PUT("pEnd=%" PRId64 "\n", row->pEnd);
    PUT("pSafe=%" PRId64 "\n", row->pSafe);
    PUT("done=%s\n", row->done ? "true" : "false");
    PUT("kvCount=%" PRId64 "\n", row->kvCount);
#undef PUT
    assert(o < cap);
    return o;
}

enum err_code rc_table_text(const struct reclaim *r, char **out, size_t *n, size_t *cap,
        struct err *e) {
    size_t c = 1;
    for (int32_t i = 0; i < r->nrows; i++) {
        c += rc_row_text_cap(&r->rows[i]) + sizeof NEXT_SEPARATOR + 1;
    }
    char *buf = mem_alloc(r->mem, c, MEM_BUFFER);
    if (buf == NULL) {
        return nomem(e);
    }
    size_t o = 0;
    buf[0] = '\0';
    for (int32_t i = 0; i < r->nrows; i++) {
        o += rc_row_text(&r->rows[i], buf + o, c - o);
        o += (size_t) snprintf(buf + o, c - o, "%s\n", NEXT_SEPARATOR);
    }
    *out = buf;
    *n = o;
    *cap = c;
    return ERR_OK;
}

static enum err_code bad(struct err *e, const char *what) {
    return err_set(e, ERR_FORMAT, "InternalDataException", "%s in %s.", what, RC_TABLE_KEY_NAME);
}

/* getLong(m, key): a required long. */
static enum err_code required_long(const struct sm *m, const char *key, int64_t *out,
        struct err *e) {
    if (!sm_has_long(m, key)) {
        return err_set(e, ERR_FORMAT, "InternalDataException", "Missing or non-long key '%s' "
                "from %s.", key, RC_TABLE_KEY_NAME);
    }
    return sm_get_long(m, key, out, e);
}

static int64_t optional_long(const struct sm *m, const char *key, int64_t otherwise) {
    int64_t v;
    struct err e;
    if (sm_has_long(m, key) && sm_get_long(m, key, &v, &e) == ERR_OK) {
        return v;
    }
    return otherwise;
}

static bool is_space(char c) {
    return (unsigned char) c <= ' ';     /* String.trim() */
}

enum err_code rc_row_parse(struct mem *mem, const char *s, size_t n, struct rc_row *row,
        struct err *e) {
    struct sm m;
    sm_init(&m, mem);
    memset(row, 0, sizeof *row);
    row->lastKeyNull = true;
    row->pEnd = -1;
    row->pSafe = -1;
    enum err_code rc = sm_parse(&m, s, n, e);
    if (rc == ERR_OK) {
        rc = required_long(&m, "pStart", &row->pStart, e);
    }
    if (rc == ERR_OK) {
        rc = required_long(&m, "tStart", &row->tStart, e);
    }
    if (rc == ERR_OK) {
        rc = required_long(&m, "tEnd", &row->tEnd, e);
    }
    if (rc == ERR_OK) {
        rc = required_long(&m, "kvCount", &row->kvCount, e);
    }
    const char *last = rc == ERR_OK ? sm_get(&m, "lastKey") : NULL;
    if (rc == ERR_OK && last == NULL) {
        rc = bad(e, "Missing lastKey");
    }
    if (rc == ERR_OK && strcmp(last, "null") != 0) {
        /* last.split(" "), each part trimmed, the non-empty ones parsed. */
        const size_t len = strlen(last);
        int32_t count = 0;
        for (size_t i = 0; i < len; i++) {
            if (!is_space(last[i]) && (i == 0 || is_space(last[i - 1]))) {
                count++;
            }
        }
        int64_t *segs = count == 0 ? NULL : mem_alloc(mem, (size_t) count * sizeof *segs,
                MEM_STATE);
        if (count > 0 && segs == NULL) {
            rc = nomem(e);
        }
        int32_t k = 0;
        size_t i = 0;
        while (rc == ERR_OK && i < len) {
            while (i < len && last[i] == ' ') {
                i++;
            }
            size_t j = i;
            while (j < len && last[j] != ' ') {
                j++;
            }
            /* part.trim() */
            size_t a = i, b = j;
            while (a < b && is_space(last[a])) {
                a++;
            }
            while (b > a && is_space(last[b - 1])) {
                b--;
            }
            if (b > a) {
                int64_t v;
                if (k >= count || !sm_parse_long(last + a, b - a, &v)) {
                    rc = err_set(e, ERR_FORMAT, "InternalDataException", "Bad value of lastKey "
                            "in %s, %s", RC_TABLE_KEY_NAME, last);
                } else {
                    segs[k++] = v;
                }
            }
            i = j;
        }
        if (rc == ERR_OK) {
            /* Each part that parsed is one run of characters: k == count. */
            assert(k == count);
            row->lastKey = segs;
            row->lastKey_n = k;
            row->lastKeyNull = false;
        } else if (segs != NULL) {
            mem_free(mem, segs, (size_t) count * sizeof *segs, MEM_STATE);
        }
    }
    const char *doneString = rc == ERR_OK ? sm_get(&m, "done") : NULL;
    if (rc == ERR_OK && doneString == NULL) {
        rc = err_set(e, ERR_FORMAT, "InternalDataException", "Missing 'done' in %s",
                RC_TABLE_KEY_NAME);
    }
    if (rc == ERR_OK && strcmp(doneString, "true") != 0 && strcmp(doneString, "false") != 0) {
        rc = err_set(e, ERR_FORMAT, "InternalDataException", "Bad value of 'done' in %s, "
                "'%s'.", RC_TABLE_KEY_NAME, doneString);
    }
    if (rc == ERR_OK) {
        row->done = strcmp(doneString, "true") == 0;
        /* Missing before 2026-10-13: */
        const char *cut = sm_get(&m, "cut");
        row->cut = cut != NULL && strcmp(cut, "true") == 0;
        row->rewritten = optional_long(&m, "rewritten", 0);
        row->pEnd = optional_long(&m, "pEnd", row->pStart);
        row->pSafe = optional_long(&m, "pSafe", -1);
        row->pCut = optional_long(&m, "pCut", row->pStart);
    }
    sm_free(&m);
    if (rc != ERR_OK) {
        rc_row_free(mem, row);
    }
    return rc;
}

/* rows.add: false on NOMEM. */
static bool rows_room(struct reclaim *r) {
    if (r->nrows == r->cap) {
        int32_t ncap = r->cap == 0 ? 8 : 2 * r->cap;
        struct rc_row *n = mem_realloc(r->mem, r->rows, (size_t) r->cap * sizeof *n,
                (size_t) ncap * sizeof *n, MEM_STATE);
        if (n == NULL) {
            return false;
        }
        r->rows = n;
        r->cap = ncap;
    }
    return true;
}

enum err_code rc_table_parse(struct reclaim *r, const char *s, size_t n, struct err *e) {
    const size_t sl = strlen(NEXT_SEPARATOR);
    size_t i = 0;
    int32_t added = 0;
    while (i <= n) {
        /* the next part: up to the separator or the end */
        size_t j = i;
        while (j < n && !(j + sl <= n && memcmp(s + j, NEXT_SEPARATOR, sl) == 0)) {
            j++;
        }
        size_t a = i, b = j;
        while (a < b && is_space(s[a])) {
            a++;
        }
        while (b > a && is_space(s[b - 1])) {
            b--;
        }
        if (b > a) {
            if (!rows_room(r)) {
                return nomem(e);
            }
            struct rc_row row;
            enum err_code rc = rc_row_parse(r->mem, s + a, b - a, &row, e);
            if (rc != ERR_OK) {
                return rc;
            }
            r->rows[r->nrows++] = row;
            added++;
        }
        if (j >= n) {
            break;
        }
        i = j + sl;
    }
    if (r->nrows == 0) {
        return err_set(e, ERR_FORMAT, "InternalDataException", "Error in bergdb data, key: %s",
                RC_TABLE_KEY_NAME);
    }
    (void) added;
    return ERR_OK;
}

/* ======== The table in the stream ======== */

/* Executes an internal transaction t; ERR_RERUN as db_execute gives it. */
static enum err_code execute_internal(struct db *db, struct trans *t, struct err *e) {
    t->is_internal = true;
    return db_execute(db, t, e);
}

/* storeTable: the table in an internal transaction. A RerunException is a
 * bug (a write-only transaction). */
static enum err_code store_table(struct db *db, struct err *e) {
    struct reclaim *r = &db->reclaim;
    char *text;
    size_t n, cap;
    enum err_code rc = rc_table_text(r, &text, &n, &cap, e);
    if (rc != ERR_OK) {
        return rc;
    }
    struct tr_builder b;
    struct trans t;
    tr_builder_init(&b, db->mem);
    tr_init(&t, db->mem);
    rc = tr_put_segments(&b, r->tableKey, r->tableKey_n, (const uint8_t *) text, (int32_t) n, e);
    mem_free(db->mem, text, cap, MEM_BUFFER);
    if (rc == ERR_OK) {
        rc = tr_build(&b, &t, e);
    }
    if (rc == ERR_OK) {
        rc = execute_internal(db, &t, e);
        if (rc == ERR_RERUN) {
            rc = err_set(e, ERR_ARG, "Bug", "RerunException for write-only trans unexpected, "
                    "%s", e->text);
        }
    }
    tr_free(&t);
    tr_builder_free(&b);
    return rc;
}

/* ======== Iterations ======== */

/* currentIteration: the index of the last row if it is not done, or -1. */
static int32_t current_iteration(const struct reclaim *r) {
    if (r->nrows == 0) {
        return -1;
    }
    return r->rows[r->nrows - 1].done ? -1 : r->nrows - 1;
}

/* lastPStart: pStart of the last iteration started, or 0. */
static int64_t last_p_start(const struct reclaim *r) {
    return r->nrows == 0 ? 0 : r->rows[r->nrows - 1].pStart;
}

/* lastTStart: tStart of the last iteration started, or Long.MIN_VALUE / 2. */
static int64_t last_t_start(const struct reclaim *r) {
    return r->nrows == 0 ? INT64_MIN / 2 : r->rows[r->nrows - 1].tStart;
}

/* ---- The maintenance follower (NodeCollection.MaintenanceFollower) ---- */

/* The database's maintenance follower (db_maintenance_follower: loads
 * without installing or swizzling), and the ids of the index nodes
 * followed: a set with open addressing (INT64_MIN free; ids are 0 or more). */
struct maintenance {
    struct op_follower inner;
    struct mem *mem;
    int64_t *ids;
    int32_t cap;            /* a power of two, or 0 */
    int32_t n;              /* indexNodes() */
};

static uint32_t id_slot(int64_t id, int32_t cap) {
    uint64_t h = (uint64_t) id * UINT64_C(0x9E3779B97F4A7C15);
    return (uint32_t) (h >> 32) & (uint32_t) (cap - 1);
}

static bool ids_add(struct maintenance *mf, int64_t id) {
    if (2 * (mf->n + 1) > mf->cap) {
        int32_t ncap = mf->cap == 0 ? 64 : 2 * mf->cap;
        int64_t *n = mem_alloc(mf->mem, (size_t) ncap * sizeof *n, MEM_STATE);
        if (n == NULL) {
            return false;
        }
        for (int32_t i = 0; i < ncap; i++) {
            n[i] = INT64_MIN;
        }
        for (int32_t i = 0; i < mf->cap; i++) {
            if (mf->ids[i] != INT64_MIN) {
                uint32_t s = id_slot(mf->ids[i], ncap);
                while (n[s] != INT64_MIN) {
                    s = (s + 1) & (uint32_t) (ncap - 1);
                }
                n[s] = mf->ids[i];
            }
        }
        mem_free(mf->mem, mf->ids, (size_t) mf->cap * sizeof *mf->ids, MEM_STATE);
        mf->ids = n;
        mf->cap = ncap;
    }
    uint32_t s = id_slot(id, mf->cap);
    while (mf->ids[s] != INT64_MIN) {
        if (mf->ids[s] == id) {
            return true;
        }
        s = (s + 1) & (uint32_t) (mf->cap - 1);
    }
    mf->ids[s] = id;
    mf->n++;
    return true;
}

static struct node *maintenance_follow(void *ctx, struct node *predecessor, int32_t index,
        struct opdata *op) {
    struct maintenance *mf = ctx;
    struct node *result = mf->inner.follow(mf->inner.ctx, predecessor, index, op);
    if (result != NULL && node_is_index_node(result) && !ids_add(mf, result->id)) {
        return NULL;        /* NOMEM: db->op_err stays clear, so the read gives NOMEM */
    }
    return result;
}

static void maintenance_free(struct maintenance *mf) {
    mem_free(mf->mem, mf->ids, (size_t) mf->cap * sizeof *mf->ids, MEM_STATE);
    mf->ids = NULL;
    mf->cap = 0;
    mf->n = 0;
}

/* ---- The step's scan: its stop condition and its result ---- */

struct scan {
    struct maintenance *mf;
    struct mem *mem;
    int64_t size;           /* an approximation of the stream space of the step's KVs */
    int64_t writeSize;
    int64_t maxNodes;
    bool split;
    bool eod;
    /* g.result's keys: segments in one array, each key's offset and count */
    int64_t *segs;
    int64_t nsegs;
    int64_t segs_cap;
    int64_t *offs;          /* offs[i], ns[i]: the i:th key */
    int32_t *ns;
    int32_t n;
    int32_t cap;
};

static int32_t scan_handle_kvt(void *ctx, const struct kvt *kvt) {
    struct scan *s = ctx;
    s->size += kvt->key_n * 8 + kvt->value->len + 100;
    /* lastKeyOfStep: the result's last key (every pair is added) */
    if (s->mf->n > s->maxNodes) {
        s->split = true;
        return GM_ADD_AND_STOP;
    }
    return s->size > s->writeSize ? GM_ADD_AND_STOP : GM_ADD;
}

static void scan_eod(void *ctx) {
    ((struct scan *) ctx)->eod = true;
}

static bool scan_add(void *ctx, const struct kvt *kvt) {
    struct scan *s = ctx;
    if (s->n == s->cap) {
        int32_t ncap = s->cap == 0 ? 64 : 2 * s->cap;
        int64_t *o = mem_alloc(s->mem, (size_t) ncap * sizeof *o, MEM_STATE);
        int32_t *k = mem_alloc(s->mem, (size_t) ncap * sizeof *k, MEM_STATE);
        if (o == NULL || k == NULL) {
            mem_free(s->mem, o, (size_t) ncap * sizeof *o, MEM_STATE);
            mem_free(s->mem, k, (size_t) ncap * sizeof *k, MEM_STATE);
            return false;
        }
        if (s->n > 0) {
            memcpy(o, s->offs, (size_t) s->n * sizeof *o);
            memcpy(k, s->ns, (size_t) s->n * sizeof *k);
        }
        mem_free(s->mem, s->offs, (size_t) s->cap * sizeof *s->offs, MEM_STATE);
        mem_free(s->mem, s->ns, (size_t) s->cap * sizeof *s->ns, MEM_STATE);
        s->offs = o;
        s->ns = k;
        s->cap = ncap;
    }
    if (s->nsegs + kvt->key_n > s->segs_cap) {
        int64_t ncap = s->segs_cap == 0 ? 256 : 2 * s->segs_cap;
        while (ncap < s->nsegs + kvt->key_n) {
            ncap *= 2;
        }
        int64_t *g = mem_realloc(s->mem, s->segs, (size_t) s->segs_cap * sizeof *g,
                (size_t) ncap * sizeof *g, MEM_STATE);
        if (g == NULL) {
            return false;
        }
        s->segs = g;
        s->segs_cap = ncap;
    }
    memcpy(s->segs + s->nsegs, kvt->key, (size_t) kvt->key_n * sizeof *kvt->key);
    s->offs[s->n] = s->nsegs;
    s->ns[s->n] = kvt->key_n;
    s->nsegs += kvt->key_n;
    s->n++;
    return true;
}

static void scan_free(struct scan *s) {
    mem_free(s->mem, s->segs, (size_t) s->segs_cap * sizeof *s->segs, MEM_STATE);
    mem_free(s->mem, s->offs, (size_t) s->cap * sizeof *s->offs, MEM_STATE);
    mem_free(s->mem, s->ns, (size_t) s->cap * sizeof *s->ns, MEM_STATE);
    s->segs = NULL;
    s->offs = NULL;
    s->ns = NULL;
}

/* The row's value transformation: what the step made dirty so far counted
 * in its rewritten bytes, and the row's text stored (Trans.dirtiedBytes is
 * known during the step only). No allocation: the buffer is the step's. */
struct row_transform {
    struct trans *t;            /* stepTrans */
    struct rc_row *next;
    char *buf;
    size_t cap;
    int64_t dirtiedStored;
    bool called;
};

static void row_transform_value(void *ctx, int64_t tt, const uint8_t *previous,
        size_t previous_len, const uint8_t **value, size_t *value_len) {
    struct row_transform *rt = ctx;
    (void) tt;
    (void) previous;
    (void) previous_len;
    rt->dirtiedStored = rt->t->dirtied_bytes;
    rt->next->rewritten += rt->dirtiedStored;
    size_t n = rc_row_text(rt->next, rt->buf, rt->cap);
    rt->called = true;
    *value = (const uint8_t *) rt->buf;
    *value_len = n;
}

/* The bytes counted for an index node in a step's reserve: a key node of
 * the maximum node size with arrays twice that long (stepNodeBytes). */
static int64_t step_node_bytes(const struct db *db) {
    return 80 + INT64_C(48) * db->max_node_size;
}

/*
 * step(it, writeSize): scans KVs at time tStart after lastKey, about
 * writeSize bytes of them, rewrites each live value stored before pCut,
 * touches the key range, and stores the table row as it is after the step;
 * all in one internal transaction. After the last step (the scan reached the
 * end), the iteration is done, and tEnd and pEnd are stored.
 */
static enum err_code step(struct db *db, int32_t iti, const int64_t writeSize, struct err *e) {
    struct reclaim *r = &db->reclaim;
    struct mem *m = db->mem;
    enum err_code rc;

    struct maintenance mf;
    memset(&mf, 0, sizeof mf);
    mf.mem = m;

    /* The step's reserve, in index nodes followed (WP J6). */
    int64_t maxNodes = r->stepReserve / step_node_bytes(db);
    maxNodes = maxNodes > 1 ? maxNodes : 1;

    struct scan sc;
    memset(&sc, 0, sizeof sc);
    sc.mf = &mf;
    sc.mem = m;
    sc.writeSize = writeSize;
    sc.maxNodes = maxNodes;

    struct getmany g;
    db_new_get_many(db, &g);
    mf.inner = db_maintenance_follower(db);
    g.gd.op.pointer_follower.follow = maintenance_follow;
    g.gd.op.pointer_follower.ctx = &mf;
    {
        const struct rc_row *it = &r->rows[iti];
        g.start_key = it->lastKeyNull ? NULL : it->lastKey;
        g.start_key_n = it->lastKeyNull ? 0 : it->lastKey_n;
        assert(g.start_key == NULL || g.start_key_n > 0);
        g.inclusive = false;
        g.lookup_time = it->tStart;
    }
    g.stop_condition.handle_kvt = scan_handle_kvt;
    g.stop_condition.eod = scan_eod;
    g.stop_condition.ctx = &sc;
    g.result.add = scan_add;
    g.result.ctx = &sc;
    rc = db_get_many(db, &g, e);

    struct tr_builder b;
    struct trans t;
    tr_builder_init(&b, m);
    tr_init(&t, m);
    struct rc_row next;
    memset(&next, 0, sizeof next);
    next.lastKeyNull = true;
    char *textBuf = NULL;
    size_t textCap = 0;
    int64_t stepLookupTime = -1;
    int64_t rewritten = 0;

    for (int32_t i = 0; rc == ERR_OK && i < sc.n; i++) {
        const int64_t *key = sc.segs + sc.offs[i];
        const int32_t key_n = sc.ns[i];
        struct getdata gd;
        db_new_get_data(db, &gd);
        gd.op.pointer_follower.follow = maintenance_follow;
        gd.op.pointer_follower.ctx = &mf;
        struct vnode *value;
        if (stepLookupTime == -1) {
            rc = db_get_one(db, INT64_MAX, key, key_n, &gd, &value, e);
            stepLookupTime = gd.actual_lookup_time;
        } else {
            rc = db_get_one(db, stepLookupTime, key, key_n, &gd, &value, e);
        }
        if (rc != ERR_OK) {
            break;
        }
        /* If the KV still exists and its value is stored before pCut, it is
         * rewritten to the stream. A value not yet written (tpos Spos.NULL,
         * 005-34) is after the cut. */
        const struct rc_row *it = &r->rows[iti];
        if (value != NULL && value->len >= 0 && gd.tpos != SPOS_NULL && gd.tpos < it->pCut) {
            rc = tr_key_read_segments(&b, key, key_n, e);
            if (rc == ERR_OK) {
                rc = tr_put_segments(&b, key, key_n, value->value, value->len, e);
            }
            rewritten += key_n * 8 + value->len + RC_VALUE_NODE_BYTES;
        }
    }

    /* next = it.copy(); next.lastKey = lastKeyOfStep; kvCount, rewritten. */
    if (rc == ERR_OK) {
        const struct rc_row *it = &r->rows[iti];
        next = *it;
        next.lastKey = NULL;
        next.lastKey_n = 0;
        next.lastKeyNull = true;
        bool ok;
        if (sc.n > 0) {
            ok = row_set_last_key(m, &next, sc.segs + sc.offs[sc.n - 1], sc.ns[sc.n - 1], false);
        } else {
            ok = row_set_last_key(m, &next, it->lastKey, it->lastKey_n, it->lastKeyNull);
        }
        if (!ok) {
            rc = nomem(e);
        }
        next.kvCount += sc.n;
        next.rewritten += rewritten;
    }
    struct row_transform rt;
    memset(&rt, 0, sizeof rt);
    if (rc == ERR_OK) {
        /* The text's room: the row's, with rewritten's digits at their most. */
        textCap = rc_row_text_cap(&next);
        textBuf = mem_alloc(m, textCap, MEM_BUFFER);
        if (textBuf == NULL) {
            rc = nomem(e);
        }
    }
    if (rc == ERR_OK) {
        rt.t = &t;
        rt.next = &next;
        rt.buf = textBuf;
        rt.cap = textCap;
        struct tr_transform tf = { NULL, row_transform_value, &rt };
        /* Not done yet: done is stored with tEnd and pEnd, below. */
        rc = tr_put_segments_tf(&b, r->currentKey, r->currentKey_n, (const uint8_t *) "", 0, &tf,
                e);
    }
    if (rc == ERR_OK) {
        rc = tr_build(&b, &t, e);
    }
    bool executed = false;
    if (rc == ERR_OK) {
        const struct rc_row *it = &r->rows[iti];
        if (stepLookupTime != -1) {
            t.read_time = stepLookupTime;
        }
        /* Q7 in 011-01: a touch of the range, so that nodes with deleted
         * keys only are written again too. */
        t.touch = true;
        t.touch_from = it->lastKeyNull ? NULL : it->lastKey;
        t.touch_from_n = it->lastKeyNull ? 0 : it->lastKey_n;
        if (sc.eod) {
            t.touch_to = NULL;
            t.touch_to_n = 0;
        } else {
            t.touch_to = next.lastKeyNull ? NULL : next.lastKey;
            t.touch_to_n = next.lastKeyNull ? 0 : next.lastKey_n;
        }
        rc = execute_internal(db, &t, e);
        if (rc == ERR_RERUN) {
            rc = ERR_OK;        /* The same step is tried at a later transaction. */
        } else if (rc == ERR_OK) {
            executed = true;
        }
    }
    if (executed) {
        assert(rt.called);
        struct rc_row *it = &r->rows[iti];
        row_move(m, it, &next);
        r->steps++;
        if (sc.split) {
            r->splitSteps++;
        }
        if (sc.eod) {
            /* The row is stored as done together with tEnd and pEnd
             * (Reclaim.Tester.testCrashBeforeIterationEnd). */
            it->done = true;
            it->tEnd = t.tt;
            it->pEnd = t.tpos;
            r->iterationCount++;
        }
    }
    rc_row_free(m, &next);
    if (textBuf != NULL) {
        mem_free(m, textBuf, textCap, MEM_BUFFER);
    }
    tr_free(&t);
    tr_builder_free(&b);
    scan_free(&sc);
    maintenance_free(&mf);
    if (rc == ERR_OK && executed && sc.eod) {
        rc = store_table(db, e);
    }
    return rc;
}

/* markSafePositions: pSafe of the done rows whose last step the startup
 * pos has passed, the stream length now (streamSize). */
static enum err_code mark_safe_positions(struct db *db, int64_t streamSize, struct err *e) {
    struct reclaim *r = &db->reclaim;
    const int64_t startupPos = ts_startup_pos_get(&db->startup_pos);
    bool changed = false;
    for (int32_t i = 0; i < r->nrows; i++) {
        struct rc_row *row = &r->rows[i];
        if (row->done && row->pSafe == -1 && startupPos >= row->pEnd) {
            row->pSafe = streamSize;
            changed = true;
        }
    }
    return changed ? store_table(db, e) : ERR_OK;
}

/* pretruncate(pos) */
static enum err_code pretruncate(struct db *db, int64_t pos, struct err *e) {
    return stream_pretruncate(&db->stream, pos, e);
}

/*
 * pretruncateIfPossible: the cut decided at the pStart of the latest
 * iteration that is done, safe, ended before the retention window, and
 * starts at or before the transaction named by the last valid meta block.
 * The table marks that iteration (cut) and is written before the cut is
 * made (cut_if_durable).
 */
static enum err_code pretruncate_if_possible(struct db *db, int64_t timeNow, struct err *e) {
    struct reclaim *r = &db->reclaim;
    const int64_t tRetain = r->retainDuration;
    const int64_t metaTransPos = db->rs.lastTransSposOfLastValidMetaBlock;
    const int64_t startupPos = ts_startup_pos_get(&db->startup_pos);
    int32_t cutRow = -1;
    for (int32_t i = 0; i < r->nrows; i++) {
        const struct rc_row *row = &r->rows[i];
        if (row->done && timeNow - tRetain > row->tEnd
                && row->pSafe != -1 && startupPos >= row->pSafe
                && metaTransPos >= row->pCut
                && row->pCut > r->firstAvailablePos
                && (cutRow == -1 || row->pStart > r->rows[cutRow].pStart)) {
            cutRow = i;
        }
    }
    if (cutRow == -1 || r->rows[cutRow].cut) {
        return ERR_OK;      /* Nothing to cut, or already cut there. */
    }

    /* Removes rows no longer needed, marks the cut and stores the table. */
    const int64_t cutPStart = r->rows[cutRow].pStart;
    int32_t k = 0;
    for (int32_t i = 0; i < r->nrows; i++) {
        if (r->rows[i].pStart < cutPStart) {
            rc_row_free(r->mem, &r->rows[i]);
        } else {
            r->rows[k++] = r->rows[i];
        }
    }
    r->nrows = k;
    struct rc_row *row = NULL;
    for (int32_t i = 0; i < r->nrows; i++) {
        if (r->rows[i].pStart == cutPStart) {
            row = &r->rows[i];
        }
    }
    assert(row != NULL);
    row->cut = true;
    const int64_t pCut = row->pCut;
    const int64_t tEnd = row->tEnd;
    enum err_code rc = store_table(db, e);
    if (rc != ERR_OK) {
        return rc;
    }

    /* The states from tEnd on are complete after the cut (Q6 in 011-01). */
    r->firstAvailableLookupTime = tEnd;
    r->firstAvailablePos = pCut;
    r->pendingCut = pCut;
    r->pendingCutDurableAt = stream_length(&db->stream);
    return ERR_OK;
}

/* cutIfDurable: the pending cut made when the stream is durable up to
 * pendingCutDurableAt, past the table that marks the cut and the meta block
 * that recovery starts from. */
static enum err_code cut_if_durable(struct db *db, struct err *e) {
    struct reclaim *r = &db->reclaim;
    if (r->pendingCut != -1 && stream_durable_length(&db->stream) >= r->pendingCutDurableAt) {
        enum err_code rc = pretruncate(db, r->pendingCut, e);
        if (rc != ERR_OK) {
            return rc;
        }
        r->pendingCut = -1;
    }
    return ERR_OK;
}

enum err_code rc_transaction_completed(struct db *db, const struct trans *t, struct err *e) {
    struct reclaim *r = &db->reclaim;
    if (t->is_internal) {
        return ERR_OK;
    }
    /* This is correct since meta blocks are written eagerly. */
    const int64_t streamSize = t->next_pos;
    int32_t current = current_iteration(r);
    enum err_code rc;

    if (current == -1 && r->retainDuration != INT64_MAX
            && streamSize > last_p_start(r) + INT64_C(2) * db->startup_distance
            && t->tt - last_t_start(r) >= j_d2l(RC_ITERATION_SPACING
                    * (double) r->retainDuration)) {
        if (!rows_room(r)) {
            return nomem(e);
        }
        struct rc_row *row = &r->rows[r->nrows];
        memset(row, 0, sizeof *row);
        row->lastKeyNull = true;
        row->pEnd = -1;
        row->pSafe = -1;
        row->pStart = streamSize;
        row->tStart = t->tt;
        row->pCut = r->nrows == 0 ? streamSize : last_p_start(r);
        r->nrows++;
        current = r->nrows - 1;
        rc = store_table(db, e);
        if (rc != ERR_OK) {
            return rc;
        }
    }

    if (current != -1) {
        const struct rc_row *it = &r->rows[current];
        int64_t allowed = j_d2l(r->internalFraction * (double) (streamSize - it->pStart))
                - it->rewritten;
        if (allowed > RC_MIN_STEP_SIZE) {
            rc = step(db, current, allowed < RC_MAX_STEP_SIZE ? allowed : RC_MAX_STEP_SIZE, e);
            if (rc != ERR_OK) {
                return rc;
            }
        }
    }

    rc = mark_safe_positions(db, streamSize, e);
    if (rc == ERR_OK) {
        rc = pretruncate_if_possible(db, t->tt, e);
    }
    if (rc == ERR_OK) {
        rc = cut_if_durable(db, e);
    }
    return rc;
}

/* ======== initFromDb ======== */

/* The value of key at the latest time, copied (NUL-terminated) into *out of
 * *cap bytes (MEM_BUFFER), or *out NULL if none. */
static enum err_code read_text(struct db *db, const int64_t *key, int32_t key_n, char **out,
        size_t *n, size_t *cap, struct err *e) {
    struct getdata gd;
    db_new_get_data(db, &gd);
    struct vnode *v;
    *out = NULL;
    enum err_code rc = db_get_one(db, INT64_MAX, key, key_n, &gd, &v, e);
    if (rc != ERR_OK || v == NULL || v->len < 0) {
        return rc;
    }
    char *buf = mem_alloc(db->mem, (size_t) v->len + 1, MEM_BUFFER);
    if (buf == NULL) {
        return nomem(e);
    }
    memcpy(buf, v->value, (size_t) v->len);
    buf[v->len] = '\0';
    *out = buf;
    *n = (size_t) v->len;
    *cap = (size_t) v->len + 1;
    return ERR_OK;
}

enum err_code rc_init_from_db(struct db *db, struct err *e) {
    struct reclaim *r = &db->reclaim;
    char *text;
    size_t n, cap;
    enum err_code rc = read_text(db, r->tableKey, r->tableKey_n, &text, &n, &cap, e);
    if (rc != ERR_OK) {
        return rc;
    }
    if (text != NULL) {
        rc = rc_table_parse(r, text, n, e);
        mem_free(db->mem, text, cap, MEM_BUFFER);
        if (rc != ERR_OK) {
            return rc;
        }
        /* The progress of the iteration in progress, stored by its last step. */
        rc = read_text(db, r->currentKey, r->currentKey_n, &text, &n, &cap, e);
        if (rc != ERR_OK) {
            return rc;
        }
        if (text != NULL) {
            struct rc_row c;
            rc = rc_row_parse(db->mem, text, n, &c, e);
            mem_free(db->mem, text, cap, MEM_BUFFER);
            if (rc != ERR_OK) {
                return rc;
            }
            for (int32_t i = 0; i < r->nrows && rc == ERR_OK; i++) {
                struct rc_row *row = &r->rows[i];
                if (row->pStart == c.pStart && !row->done && !c.done) {
                    struct rc_row copy = c;
                    copy.lastKey = NULL;
                    copy.lastKeyNull = true;
                    copy.lastKey_n = 0;
                    if (!row_set_last_key(db->mem, &copy, c.lastKey, c.lastKey_n,
                            c.lastKeyNull)) {
                        rc = nomem(e);
                    } else {
                        row_move(db->mem, row, &copy);
                    }
                }
            }
            rc_row_free(db->mem, &c);
            if (rc != ERR_OK) {
                return rc;
            }
        }
    }

    /* The first available lookup time from the row marked cut
     * (Reclaim.Tester.testFirstAvailableTimeAfterRestart). */
    int32_t cutRow = -1;
    for (int32_t i = 0; i < r->nrows; i++) {
        if (r->rows[i].cut && (cutRow == -1 || r->rows[i].pStart > r->rows[cutRow].pStart)) {
            cutRow = i;
        }
    }
    int64_t firstPos = 0;
    int64_t firstTime = 0;
    if (cutRow != -1) {
        firstPos = r->rows[cutRow].pCut;
        firstTime = r->rows[cutRow].tEnd;
        if (stream_first_pos(&db->stream) < firstPos) {
            rc = pretruncate(db, firstPos, e);  /* A crash came between the table write and the cut. */
            if (rc != ERR_OK) {
                return rc;
            }
        }
    }
    r->firstAvailableLookupTime = firstTime;
    r->firstAvailablePos = firstPos;
    return ERR_OK;
}

enum err_code rc_first_available_of_table(struct mem *m, const char *s, size_t n, int64_t *pos,
        int64_t *time, struct err *e) {
    struct reclaim r;
    rc_init(&r, m);
    enum err_code rc = rc_table_parse(&r, s, n, e);
    *pos = 0;
    *time = 0;
    if (rc == ERR_OK) {
        int32_t cutRow = -1;
        for (int32_t i = 0; i < r.nrows; i++) {
            if (r.rows[i].cut && (cutRow == -1 || r.rows[i].pStart > r.rows[cutRow].pStart)) {
                cutRow = i;
            }
        }
        if (cutRow != -1) {
            *pos = r.rows[cutRow].pCut;
            *time = r.rows[cutRow].tEnd;
        }
    }
    rc_free(&r);
    return rc;
}
