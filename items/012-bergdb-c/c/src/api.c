/* api: include/bergdb.h's functions; see api.h. */
#include "api.h"
#include <assert.h>
#include <stddef.h>
#include <stdio.h>
#include <string.h>
#include "getmany.h"
#include "keys.h"
#include "nstream.h"
#include "rstream.h"
#include "spos.h"
#include "strans.h"
#include "vnode.h"

/* The caller's struct bergdb_mem is the library's struct mem (mem.h): the
 * same fields in the same order. */
_Static_assert(sizeof(struct bergdb_mem) == sizeof(struct mem), "bergdb_mem is struct mem");
_Static_assert(offsetof(struct bergdb_mem, live_total) == offsetof(struct mem, live_total),
        "bergdb_mem is struct mem");
_Static_assert(offsetof(struct bergdb_mem, fail_at) == offsetof(struct mem, fail_at),
        "bergdb_mem is struct mem");
_Static_assert((int) BERGDB_MEM_KINDS == (int) MEM_KINDS, "the memory kinds");

/* DatabaseId.TEST_ID (testId()). */
const uint8_t bergdb_test_id[BERGDB_ID_SIZE] = {
    0x7d, 0xee, 0xf4, 0x8a, 0x84, 0x66, 0xf3, 0x87,
    0xc0, 0xbb, 0x72, 0x9d, 0x2c, 0x8a, 0xab, 0x38
};

int api_code(enum err_code code) {
    switch (code) {
    case ERR_OK: return BERGDB_OK;
    case ERR_IO: return BERGDB_IO;
    case ERR_FORMAT: return BERGDB_FORMAT;
    case ERR_ARG: return BERGDB_ARG;
    case ERR_NOT_AVAILABLE: return BERGDB_NOT_AVAILABLE;
    case ERR_NOMEM: return BERGDB_NOMEM;
    case ERR_LIMIT: return BERGDB_LIMIT;
    case ERR_IN_USE: return BERGDB_IN_USE;
    case ERR_RERUN: return BERGDB_RERUN;
    case ERR_STATE: return BERGDB_STATE;
    case ERR_FAILED: return BERGDB_FAILED;
    case ERR_NOT_CREATED: return BERGDB_NOT_CREATED;
    }
    return BERGDB_FORMAT;
}

const char *bergdb_errname(int code) {
    switch (code) {
    case BERGDB_OK: return "BERGDB_OK";
    case BERGDB_RERUN: return "BERGDB_RERUN";
    case BERGDB_NOT_AVAILABLE: return "BERGDB_NOT_AVAILABLE";
    case BERGDB_FAILED: return "BERGDB_FAILED";
    case BERGDB_IO: return "BERGDB_IO";
    case BERGDB_FORMAT: return "BERGDB_FORMAT";
    case BERGDB_STATE: return "BERGDB_STATE";
    case BERGDB_ARG: return "BERGDB_ARG";
    case BERGDB_LIMIT: return "BERGDB_LIMIT";
    case BERGDB_NOT_CREATED: return "BERGDB_NOT_CREATED";
    case BERGDB_IN_USE: return "BERGDB_IN_USE";
    case BERGDB_NOMEM: return "BERGDB_NOMEM";
    default: return "BERGDB_UNKNOWN";
    }
}

const char *bergdb_errmsg(const bergdb_db *db) {
    return db == NULL ? "" : db->errmsg;
}

/* The call's result: the error's text into errmsg, "" on success. */
static int done(bergdb_db *db, enum err_code rc, const struct err *e) {
    if (rc == ERR_OK) {
        db->errmsg[0] = '\0';
    } else {
        snprintf(db->errmsg, sizeof db->errmsg, "%s: %s", e->java, e->text);
    }
    return api_code(rc);
}

/* A call's success. */
static int ok_done(bergdb_db *db) {
    db->errmsg[0] = '\0';
    return BERGDB_OK;
}

static int fail_arg(bergdb_db *db, const char *what) {
    struct err e;
    err_set(&e, ERR_ARG, "IllegalArgumentException", "%s", what);
    return db == NULL ? BERGDB_ARG : done(db, ERR_ARG, &e);
}

static int fail_state(bergdb_db *db) {
    struct err e;
    err_set(&e, ERR_STATE, "IllegalDbStateException", "a call from a callback of the same "
            "database");
    return done(db, ERR_STATE, &e);
}

static int fail_nomem(bergdb_db *db) {
    struct err e;
    err_set(&e, ERR_NOMEM, "OutOfMemoryError", "out of memory");
    return done(db, ERR_NOMEM, &e);
}

/* ======== Opening and closing ======== */

void bergdb_options_init(struct bergdb_options *opt) {
    memset(opt, 0, sizeof *opt);
    opt->max_node_size = 30;
    opt->startup_distance = 50 * 1000000;
    opt->cache_size_indicator = 200 * 1000000;
    opt->retain_duration = BERGDB_FOREVER;
    opt->clock = NULL;
    opt->clock_ctx = NULL;
    opt->mem = NULL;
}

static bool all_zero(const uint8_t *p, size_t n) {
    for (size_t i = 0; i < n; i++) {
        if (p[i] != 0) {
            return false;
        }
    }
    return true;
}

int bergdb_open(const char *dir, const struct bergdb_options *opt, bergdb_db **out,
        struct bergdb_start_info *info, char *errbuf) {
    struct bergdb_options defaults;
    struct err e;
    if (errbuf != NULL) {
        errbuf[0] = '\0';
    }
    if (out == NULL) {
        if (errbuf != NULL) {
            snprintf(errbuf, BERGDB_ERRBUF_SIZE, "IllegalArgumentException: db NULL");
        }
        return BERGDB_ARG;
    }
    *out = NULL;
    if (opt == NULL) {
        bergdb_options_init(&defaults);
        opt = &defaults;
    }

    /* The database's struct, through the caller's counts or its own. */
    struct mem tmp;
    struct mem *m;
    if (opt->mem != NULL) {
        m = (struct mem *) (void *) opt->mem;
    } else {
        mem_init(&tmp);
        m = &tmp;
    }
    bergdb_db *db = mem_zalloc(m, sizeof *db, MEM_STATE);
    if (db == NULL) {
        if (errbuf != NULL) {
            snprintf(errbuf, BERGDB_ERRBUF_SIZE, "OutOfMemoryError: out of memory");
        }
        return BERGDB_NOMEM;
    }
    if (opt->mem == NULL) {
        db->own_mem = tmp;
        m = &db->own_mem;
    }
    db->mem = m;

    struct db_config cfg;
    memset(&cfg, 0, sizeof cfg);
    cfg.max_node_size = opt->max_node_size;
    cfg.startup_distance = opt->startup_distance;
    cfg.cache_size_indicator = opt->cache_size_indicator;
    cfg.retain_duration = opt->retain_duration;
    cfg.clock = opt->clock;
    cfg.clock_ctx = opt->clock_ctx;
    cfg.random_id = all_zero(opt->id, BERGDB_ID_SIZE);
    memcpy(cfg.id, opt->id, BERGDB_ID_SIZE);

    struct db_start_info si;
    db->in_callback = true;     /* the clock may be called */
    enum err_code rc = db_open(&db->db, dir, &cfg, m, &si, &e);
    db->in_callback = false;
    if (rc != ERR_OK) {
        if (errbuf != NULL) {
            snprintf(errbuf, BERGDB_ERRBUF_SIZE, "%s: %s", e.java, e.text);
        }
        mem_free(m, db, sizeof *db, MEM_STATE);
        return api_code(rc);
    }
    if (info != NULL) {
        info->start_pos = si.start_pos;
        info->startup_distance = si.startup_distance;
        info->start_time = si.start_time;
        info->trans_count = si.trans_count;
        info->last_pos = si.last_pos;
    }
    *out = db;
    return BERGDB_OK;
}

void bergdb_trans_free(bergdb_trans *t);
void bergdb_read_free(bergdb_read *rd);

int bergdb_close(bergdb_db *db) {
    struct err e;
    if (db == NULL) {
        return BERGDB_OK;
    }
    if (db->in_callback) {
        return fail_state(db);
    }
    while (db->trans_list != NULL) {
        bergdb_trans_free(db->trans_list);
    }
    while (db->read_list != NULL) {
        bergdb_read_free(db->read_list);
    }
    enum err_code rc = db_close(&db->db, &e);
    struct mem *m = db->mem;
    mem_free(m, db, sizeof *db, MEM_STATE);     /* counts, then frees: m may be in db */
    return api_code(rc);
}

/* ======== Keys ======== */

int bergdb_ikey_to_bkey(const uint8_t *ikey, size_t len, uint8_t *bkey) {
    if (ikey == NULL || bkey == NULL || len > INT32_MAX) {
        return BERGDB_ARG;
    }
    return keys_ikey_to_bkey(ikey, (int32_t) len, bkey) ? BERGDB_OK : BERGDB_ARG;
}

void bergdb_bkey_to_ikey(const uint8_t *bkey, size_t len, uint8_t *ikey) {
    keys_bkey_to_ikey(bkey, (int32_t) len, ikey);
}

/* A bkey's segments into a block of m's (MEM_CALLER); NULL on NOMEM. */
static int64_t *segments(struct mem *m, const uint8_t *key, size_t len, int32_t *n) {
    *n = keys_segment_count((int32_t) len);
    int64_t *seg = mem_alloc(m, (size_t) *n * sizeof *seg, MEM_CALLER);
    if (seg != NULL) {
        keys_to_segments(key, (int32_t) len, seg);
    }
    return seg;
}

static void free_segments(struct mem *m, int64_t *seg, int32_t n) {
    mem_free(m, seg, (size_t) n * sizeof *seg, MEM_CALLER);
}

/* ======== Transactions ======== */

int bergdb_trans_new(bergdb_db *db, bergdb_trans **out) {
    if (db == NULL || out == NULL) {
        return fail_arg(db, "NULL");
    }
    if (db->in_callback) {
        return fail_state(db);
    }
    bergdb_trans *t = mem_zalloc(db->mem, sizeof *t, MEM_CALLER);
    if (t == NULL) {
        return fail_nomem(db);
    }
    t->db = db;
    tr_builder_init(&t->b, db->mem);
    tr_init(&t->t, db->mem);
    t->next = db->trans_list;
    if (t->next != NULL) {
        t->next->prev = t;
    }
    db->trans_list = t;
    *out = t;
    db->errmsg[0] = '\0';
    return BERGDB_OK;
}

void bergdb_trans_free(bergdb_trans *t) {
    if (t == NULL || t->db->in_callback) {
        return;
    }
    bergdb_db *db = t->db;
    if (t->prev != NULL) {
        t->prev->next = t->next;
    } else {
        db->trans_list = t->next;
    }
    if (t->next != NULL) {
        t->next->prev = t->prev;
    }
    tr_free(&t->t);
    tr_builder_free(&t->b);
    mem_free(db->mem, t, sizeof *t, MEM_CALLER);
}

static int trans_check(bergdb_trans *t, const uint8_t *key, size_t key_len) {
    if (t == NULL) {
        return BERGDB_ARG;
    }
    if (t->db->in_callback) {
        return fail_state(t->db);
    }
    if (key == NULL || key_len > INT32_MAX) {
        return fail_arg(t->db, "key NULL or over INT32_MAX bytes");
    }
    return BERGDB_OK;
}

int bergdb_trans_put_transformed(bergdb_trans *t, const uint8_t *key, size_t key_len,
        const uint8_t *value, size_t value_len, const struct bergdb_transform *tf) {
    int c = trans_check(t, key, key_len);
    if (c != BERGDB_OK) {
        return c;
    }
    if (value == NULL || value_len > INT32_MAX) {
        return fail_arg(t->db, "value == null not allowed, use delete() to delete a "
                "key-value pair.");
    }
    struct err e;
    struct tr_transform trf;
    if (tf != NULL) {
        trf.key = tf->key;
        trf.value = tf->value;
        trf.ctx = tf->ctx;
    }
    enum err_code rc = tr_put(&t->b, key, (int32_t) key_len, value, (int32_t) value_len,
            tf == NULL ? NULL : &trf, &e);
    return done(t->db, rc, &e);
}

int bergdb_trans_put(bergdb_trans *t, const uint8_t *key, size_t key_len,
        const uint8_t *value, size_t value_len) {
    return bergdb_trans_put_transformed(t, key, key_len, value, value_len, NULL);
}

int bergdb_trans_delete(bergdb_trans *t, const uint8_t *key, size_t key_len) {
    int c = trans_check(t, key, key_len);
    if (c != BERGDB_OK) {
        return c;
    }
    struct err e;
    enum err_code rc = tr_delete(&t->b, key, (int32_t) key_len, &e);
    return done(t->db, rc, &e);
}

int bergdb_trans_key_read(bergdb_trans *t, const uint8_t *key, size_t key_len) {
    int c = trans_check(t, key, key_len);
    if (c != BERGDB_OK) {
        return c;
    }
    struct err e;
    enum err_code rc = tr_key_read(&t->b, key, (int32_t) key_len, &e);
    return done(t->db, rc, &e);
}

int bergdb_trans_lookup_time(bergdb_trans *t, int64_t time) {
    if (t == NULL) {
        return BERGDB_ARG;
    }
    if (t->db->in_callback) {
        return fail_state(t->db);
    }
    struct err e;
    enum err_code rc = tr_lookup_time(&t->b, time, &e);
    return done(t->db, rc, &e);
}

int bergdb_execute(bergdb_db *db, bergdb_trans *t, struct bergdb_executed *out) {
    if (db == NULL || t == NULL || t->db != db) {
        return fail_arg(db, "a NULL, or a transaction of another database");
    }
    if (db->in_callback) {
        return fail_state(db);
    }
    struct err e;
    enum err_code rc = tr_build(&t->b, &t->t, &e);     /* execute(Trans.Builder) */
    if (rc == ERR_OK) {
        db->in_callback = true;     /* the clock and the transformations run */
        rc = db_execute(&db->db, &t->t, &e);
        db->in_callback = false;
    }
    if (rc == ERR_OK && out != NULL) {
        out->tt = t->t.tt;
        out->tpos = t->t.tpos;
        out->last_pos = t->t.last_pos;
        out->next_pos = t->t.next_pos;
        out->startup_pos = t->t.startup_pos;
        out->node_count = t->t.node_count;
    }
    return done(db, rc, &e);
}

/* ======== Reads ======== */

int bergdb_read_new(bergdb_db *db, bergdb_read **out) {
    if (db == NULL || out == NULL) {
        return fail_arg(db, "NULL");
    }
    if (db->in_callback) {
        return fail_state(db);
    }
    bergdb_read *rd = mem_zalloc(db->mem, sizeof *rd, MEM_CALLER);
    if (rd == NULL) {
        return fail_nomem(db);
    }
    rd->db = db;
    rd->next = db->read_list;
    if (rd->next != NULL) {
        rd->next->prev = rd;
    }
    db->read_list = rd;
    *out = rd;
    db->errmsg[0] = '\0';
    return BERGDB_OK;
}

void bergdb_read_free(bergdb_read *rd) {
    if (rd == NULL || rd->db->in_callback) {
        return;
    }
    bergdb_db *db = rd->db;
    if (rd->prev != NULL) {
        rd->prev->next = rd->next;
    } else {
        db->read_list = rd->next;
    }
    if (rd->next != NULL) {
        rd->next->prev = rd->prev;
    }
    mem_free(db->mem, rd->buf, rd->cap, MEM_CALLER);
    mem_free(db->mem, rd->kvts, rd->kvt_cap * sizeof *rd->kvts, MEM_CALLER);
    mem_free(db->mem, rd, sizeof *rd, MEM_CALLER);
}

/* Room for n more bytes in the read context's buffer; false on NOMEM. */
static bool buf_room(bergdb_read *rd, size_t n) {
    if (rd->used + n <= rd->cap) {
        return true;
    }
    size_t ncap = rd->cap == 0 ? 256 : rd->cap;
    while (ncap < rd->used + n) {
        ncap *= 2;
    }
    uint8_t *b = mem_realloc(rd->db->mem, rd->buf, rd->cap, ncap, MEM_CALLER);
    if (b == NULL) {
        return false;
    }
    rd->buf = b;
    rd->cap = ncap;
    return true;
}

/* Room for one more pair; false on NOMEM. */
static bool kvt_room(bergdb_read *rd) {
    if (rd->nkvts < rd->kvt_cap) {
        return true;
    }
    size_t ncap = rd->kvt_cap == 0 ? 16 : rd->kvt_cap * 2;
    struct bergdb_kvt *k = mem_realloc(rd->db->mem, rd->kvts, rd->kvt_cap * sizeof *k,
            ncap * sizeof *k, MEM_CALLER);
    if (k == NULL) {
        return false;
    }
    rd->kvts = k;
    rd->kvt_cap = ncap;
    return true;
}

int bergdb_get_one(bergdb_db *db, bergdb_read *rd, int64_t lookup_time,
        const uint8_t *key, size_t key_len, struct bergdb_one *out) {
    if (db == NULL || rd == NULL || rd->db != db || key == NULL || out == NULL
            || key_len > INT32_MAX) {
        return fail_arg(db, "a NULL, a key over INT32_MAX bytes, or a read context of "
                "another database");
    }
    if (db->in_callback) {
        return fail_state(db);
    }
    int32_t n;
    int64_t *seg = segments(db->mem, key, key_len, &n);
    if (seg == NULL) {
        return fail_nomem(db);
    }
    struct err e;
    struct getdata gd;
    struct vnode *v = NULL;
    db_new_get_data(&db->db, &gd);
    enum err_code rc = db_get_one(&db->db, lookup_time, seg, n, &gd, &v, &e);
    free_segments(db->mem, seg, n);
    if (rc != ERR_OK) {
        return done(db, rc, &e);
    }
    rd->used = 0;
    rd->nkvts = 0;
    memset(out, 0, sizeof *out);
    out->actual_lookup_time = gd.actual_lookup_time;
    if (v != NULL && v->len >= 0) {
        if (!buf_room(rd, (size_t) v->len + 1)) {
            return fail_nomem(db);
        }
        memcpy(rd->buf, v->value, (size_t) v->len);
        out->value = rd->buf;
        out->value_len = (size_t) v->len;
        out->time = gd.kv_time;
        out->tpos = gd.tpos;
    }
    obj_collect(&db->db.cx);    /* the end of the call: a safe point (012-07, 6.4.4) */
    return ok_done(db);
}

void bergdb_range_init(struct bergdb_range *r) {
    memset(r, 0, sizeof *r);
    r->lookup_time = BERGDB_LATEST;
    r->inclusive = true;
    r->forward = true;
    r->end_inclusive = true;
}

/* A getMany's state: the range's stop conditions in the header's order, the
 * sink into the read context, the pair given to a stop function. */
struct many {
    bergdb_read *rd;
    const struct bergdb_range *range;
    struct gm_stop prefix, endpoint, getn;
    bool has_prefix, has_endpoint, has_getn;
    struct gm_prefix sp;
    struct gm_endpoint se;
    struct gm_get_n sn;
    bool eod;
    bool bad_answer;
    bool nomem;
    uint8_t *scratch;           /* a key's bytes for the stop function */
    size_t scratch_cap;
    size_t *offs;               /* each added pair's key and value offsets in rd->buf */
    size_t offs_cap;
};

/* A kvt's key as bytes in the scratch; false on NOMEM. */
static bool scratch_key(struct many *mc, const struct kvt *kvt, size_t *len) {
    size_t need = (size_t) keys_byte_size(kvt->key, kvt->key_n) + 1;
    if (need > mc->scratch_cap) {
        uint8_t *s = mem_realloc(mc->rd->db->mem, mc->scratch, mc->scratch_cap, need,
                MEM_CALLER);
        if (s == NULL) {
            return false;
        }
        mc->scratch = s;
        mc->scratch_cap = need;
    }
    *len = (size_t) keys_to_bytes(kvt->key, kvt->key_n, mc->scratch);
    return true;
}

static int32_t many_handle(void *ctx, const struct kvt *kvt) {
    struct many *mc = ctx;
    int32_t a;
    if (mc->has_prefix && (a = mc->prefix.handle_kvt(mc->prefix.ctx, kvt)) != GM_ADD) {
        return a;
    }
    if (mc->has_endpoint && (a = mc->endpoint.handle_kvt(mc->endpoint.ctx, kvt)) != GM_ADD) {
        return a;
    }
    if (mc->range->stop != NULL) {
        size_t klen;
        if (!scratch_key(mc, kvt, &klen)) {
            mc->nomem = true;
            return -1;
        }
        struct bergdb_kvt k;
        k.key = mc->scratch;
        k.key_len = klen;
        k.value = kvt->value == NULL || kvt->value->len < 0 ? NULL : kvt->value->value;
        k.value_len = k.value == NULL ? 0 : (size_t) kvt->value->len;
        k.time = kvt->time;
        k.pos = kvt->spos;
        a = mc->range->stop(mc->range->stop_ctx, &k);
        if (a < BERGDB_ADD || a > BERGDB_ADD_AND_STOP) {
            mc->bad_answer = true;
            return -1;
        }
        if (a != BERGDB_ADD) {
            return a;
        }
    }
    if (mc->has_getn) {
        return mc->getn.handle_kvt(mc->getn.ctx, kvt);
    }
    return GM_ADD;
}

static void many_eod(void *ctx) {
    struct many *mc = ctx;
    mc->eod = true;
}

static bool many_add(void *ctx, const struct kvt *kvt) {
    struct many *mc = ctx;
    bergdb_read *rd = mc->rd;
    size_t klen = (size_t) keys_byte_size(kvt->key, kvt->key_n);
    size_t vlen = kvt->value == NULL || kvt->value->len < 0 ? 0 : (size_t) kvt->value->len;
    if (!kvt_room(rd) || !buf_room(rd, klen + vlen + 1)) {
        return false;
    }
    if (rd->nkvts * 2 + 2 > mc->offs_cap) {
        size_t ncap = mc->offs_cap == 0 ? 32 : mc->offs_cap * 2;
        size_t *o = mem_realloc(rd->db->mem, mc->offs, mc->offs_cap * sizeof *o,
                ncap * sizeof *o, MEM_CALLER);
        if (o == NULL) {
            return false;
        }
        mc->offs = o;
        mc->offs_cap = ncap;
    }
    struct bergdb_kvt *k = &rd->kvts[rd->nkvts];
    mc->offs[rd->nkvts * 2] = rd->used;
    keys_to_bytes(kvt->key, kvt->key_n, rd->buf + rd->used);
    rd->used += klen;
    mc->offs[rd->nkvts * 2 + 1] = rd->used;
    if (vlen > 0) {
        memcpy(rd->buf + rd->used, kvt->value->value, vlen);
    }
    rd->used += vlen;
    k->key_len = klen;
    k->value_len = vlen;
    k->value = kvt->value == NULL || kvt->value->len < 0 ? NULL : rd->buf;     /* fixed below */
    k->time = kvt->time;
    k->pos = kvt->spos;
    rd->nkvts++;
    return true;
}

int bergdb_get_many(bergdb_db *db, bergdb_read *rd, const struct bergdb_range *range,
        struct bergdb_many *out) {
    if (db == NULL || rd == NULL || rd->db != db || range == NULL || out == NULL
            || range->start_key_len > INT32_MAX || range->prefix_len > INT32_MAX
            || range->end_key_len > INT32_MAX || range->max_count < 0) {
        return fail_arg(db, "a bad argument of getMany");
    }
    if (db->in_callback) {
        return fail_state(db);
    }
    struct mem *m = db->mem;
    int32_t ns = 0, np = 0, ne = 0;
    int64_t *start = NULL, *prefix = NULL, *end = NULL;
    bool ok = true;
    if (range->start_key != NULL) {
        ok = (start = segments(m, range->start_key, range->start_key_len, &ns)) != NULL;
    }
    if (ok && range->prefix != NULL) {
        ok = (prefix = segments(m, range->prefix, range->prefix_len, &np)) != NULL;
    }
    if (ok && range->end_key != NULL) {
        ok = (end = segments(m, range->end_key, range->end_key_len, &ne)) != NULL;
    }
    struct err e;
    enum err_code rc = ERR_OK;
    struct many mc;
    memset(&mc, 0, sizeof mc);
    mc.rd = rd;
    mc.range = range;
    rd->used = 0;
    rd->nkvts = 0;
    struct getmany g;
    if (!ok) {
        rc = err_set(&e, ERR_NOMEM, "OutOfMemoryError", "out of memory");
    } else {
        db_new_get_many(&db->db, &g);
        g.lookup_time = range->lookup_time;
        g.start_key = start;
        g.start_key_n = ns;
        g.inclusive = range->inclusive;
        if (!range->forward) {
            gm_set_backward(&g);
        }
        if (prefix != NULL) {
            mc.prefix = gm_prefix(&mc.sp, prefix, np);
            mc.has_prefix = true;
        }
        if (end != NULL) {
            mc.endpoint = gm_endpoint(&mc.se, end, ne, range->end_inclusive, !range->forward);
            mc.has_endpoint = true;
        }
        if (range->max_count > 0) {
            mc.getn = gm_get_n(&mc.sn, range->max_count);
            mc.has_getn = true;
        }
        g.stop_condition.handle_kvt = many_handle;
        g.stop_condition.eod = many_eod;
        g.stop_condition.ctx = &mc;
        g.result.add = many_add;
        g.result.ctx = &mc;
        db->in_callback = true;
        rc = db_get_many(&db->db, &g, &e);
        db->in_callback = false;
        if (rc == ERR_NOMEM && mc.bad_answer) {
            rc = err_set(&e, ERR_ARG, "IllegalArgumentException", "a stop function's answer "
                    "out of range");
        }
    }
    if (rc == ERR_OK) {
        for (size_t i = 0; i < rd->nkvts; i++) {
            rd->kvts[i].key = rd->buf + mc.offs[2 * i];
            if (rd->kvts[i].value != NULL) {
                rd->kvts[i].value = rd->buf + mc.offs[2 * i + 1];
            }
        }
        out->kvts = rd->kvts;
        out->count = rd->nkvts;
        out->actual_lookup_time = g.actual_lookup_time;
        out->get_op_count = g.get_op_count;
        out->eod = mc.eod;
    }
    mem_free(m, mc.scratch, mc.scratch_cap, MEM_CALLER);
    mem_free(m, mc.offs, mc.offs_cap * sizeof *mc.offs, MEM_CALLER);
    if (start != NULL) {
        free_segments(m, start, ns);
    }
    if (prefix != NULL) {
        free_segments(m, prefix, np);
    }
    if (end != NULL) {
        free_segments(m, end, ne);
    }
    return done(db, rc, &e);
}

int bergdb_get_trans(bergdb_db *db, bergdb_read *rd, int64_t tpos, struct bergdb_stored *out) {
    if (db == NULL || rd == NULL || rd->db != db || out == NULL) {
        return fail_arg(db, "NULL, or a read context of another database");
    }
    if (db->in_callback) {
        return fail_state(db);
    }
    struct err e;
    const int64_t inBlock = tpos % META_BLOCK_DISTANCE;
    if (tpos < 0 || tpos % RS_TRANS_ALIGNMENT != 0 || inBlock < META_BLOCK_SIZE) {
        err_set(&e, ERR_ARG, "IllegalArgumentException", "Not a position of a transaction, "
                "%lld.", (long long) tpos);
        return done(db, ERR_ARG, &e);
    }
    enum err_code rc = db_check_active(&db->db, "getTrans", &e);
    if (rc != ERR_OK) {
        return done(db, rc, &e);
    }
    struct ns_iter it;
    struct st_record rec;
    bool has = false;
    ns_iter_init(&it, &db->db.stream, db->mem, tpos, true);
    st_init(&rec);
    rc = ns_iter_next(&it, &has, &e);
    if (rc != ERR_OK) {
        /* Corrupt data, as for the other reads (005-34): the database fails. */
        rc = db_fail_on_storage(&db->db, "A read", &e);
    } else if (!has) {
        rc = err_set(&e, ERR_ARG, "IllegalArgumentException", "Not a position of a "
                "transaction, %lld: at or past the end of the stream.", (long long) tpos);
    } else {
        rc = st_parse(&rec, it.tpos, it.buf.p, it.size, db->mem, &e);
        if (rc != ERR_OK && rc != ERR_NOMEM) {
            rc = db_fail_on_storage(&db->db, "A read", &e);
        }
    }
    if (rc == ERR_OK) {
        rd->used = 0;
        rd->nkvts = 0;
        for (int32_t i = 0; i < rec.nnodes && rc == ERR_OK; i++) {
            const struct sn_node *x = &rec.nodes[i];
            if (x->type != NODE_VALUE && x->type != NODE_DELETE) {
                continue;
            }
            size_t klen;
            int64_t *seg = mem_alloc(db->mem, (size_t) x->key_n * sizeof *seg, MEM_CALLER);
            if (seg == NULL) {
                rc = err_set(&e, ERR_NOMEM, "OutOfMemoryError", "out of memory");
                break;
            }
            for (int32_t k = 0; k < x->key_n; k++) {
                seg[k] = sn_seg(x, k);
            }
            klen = (size_t) keys_byte_size(seg, x->key_n);
            size_t vlen = x->value_len < 0 ? 0 : (size_t) x->value_len;
            if (!kvt_room(rd) || !buf_room(rd, klen + vlen + 1)) {
                mem_free(db->mem, seg, (size_t) x->key_n * sizeof *seg, MEM_CALLER);
                rc = err_set(&e, ERR_NOMEM, "OutOfMemoryError", "out of memory");
                break;
            }
            struct bergdb_kvt *kv = &rd->kvts[rd->nkvts++];
            kv->key = (const uint8_t *) (uintptr_t) rd->used;     /* an offset until the end */
            keys_to_bytes(seg, x->key_n, rd->buf + rd->used);
            rd->used += klen;
            kv->key_len = klen;
            kv->value = x->value == NULL ? NULL : (const uint8_t *) (uintptr_t) rd->used;
            if (vlen > 0) {
                memcpy(rd->buf + rd->used, x->value, vlen);
            }
            rd->used += vlen;
            kv->value_len = vlen;
            kv->time = rec.tt;
            kv->pos = x->spos;
            mem_free(db->mem, seg, (size_t) x->key_n * sizeof *seg, MEM_CALLER);
        }
    }
    if (rc == ERR_OK) {
        for (size_t i = 0; i < rd->nkvts; i++) {
            rd->kvts[i].key = rd->buf + (uintptr_t) rd->kvts[i].key;
            if (rd->kvts[i].value != NULL) {
                rd->kvts[i].value = rd->buf + (uintptr_t) rd->kvts[i].value;
            }
        }
        out->tt = rec.tt;
        out->tpos = rec.tpos;
        out->last_pos = rec.last_pos;
        out->startup_pos = rec.startup_pos;
        out->top_pos = rec.top_pos;
        out->values = rd->kvts;
        out->count = rd->nkvts;
    }
    st_free(&rec, db->mem);
    ns_iter_free(&it);
    return done(db, rc, &e);
}

/* ======== Durability, the clock, settings, status ======== */

int bergdb_sync(bergdb_db *db, int64_t pos, int level) {
    if (db == NULL) {
        return BERGDB_ARG;
    }
    if (level != BERGDB_SYNC_NONE && level != BERGDB_SYNC_ORDINARY
            && level != BERGDB_SYNC_STRONG) {
        return fail_arg(db, "a bad sync level");
    }
    if (db->in_callback) {
        return fail_state(db);
    }
    struct err e;
    if (level == BERGDB_SYNC_NONE || pos < 0) {
        return ok_done(db);
    }
    if (pos > 0 && pos >= db_stream_length(&db->db)) {
        return fail_arg(db, "a position at or past the end of the stream");
    }
    enum err_code rc = db_sync(&db->db, pos, &e);
    return done(db, rc, &e);
}

int bergdb_current_time(bergdb_db *db, int64_t *time) {
    if (db == NULL || time == NULL) {
        return fail_arg(db, "NULL");
    }
    if (db->in_callback) {
        return fail_state(db);
    }
    db->in_callback = true;
    *time = db_current_time(&db->db);
    db->in_callback = false;
    db->errmsg[0] = '\0';
    return BERGDB_OK;
}

int bergdb_lookup_time(bergdb_db *db, int64_t wanted, int64_t *actual) {
    if (db == NULL || actual == NULL) {
        return fail_arg(db, "NULL");
    }
    if (db->in_callback) {
        return fail_state(db);
    }
    *actual = db_lookup_time(&db->db, wanted);
    db->errmsg[0] = '\0';
    return BERGDB_OK;
}

int bergdb_set_startup_distance(bergdb_db *db, int32_t distance) {
    if (db == NULL) {
        return BERGDB_ARG;
    }
    if (db->in_callback) {
        return fail_state(db);
    }
    struct err e;
    db->in_callback = true;
    enum err_code rc = db_set_startup_distance(&db->db, distance, &e);
    db->in_callback = false;
    return done(db, rc, &e);
}

int bergdb_set_cache_size_indicator(bergdb_db *db, int64_t size) {
    if (db == NULL) {
        return BERGDB_ARG;
    }
    if (db->in_callback) {
        return fail_state(db);
    }
    struct err e;
    enum err_code rc = db_set_cache_size_indicator(&db->db, size, &e);
    return done(db, rc, &e);
}

int bergdb_set_retain_duration(bergdb_db *db, int64_t duration) {
    if (db == NULL) {
        return BERGDB_ARG;
    }
    if (db->in_callback) {
        return fail_state(db);
    }
    struct err e;
    enum err_code rc = db_set_retain_duration(&db->db, duration, &e);
    return done(db, rc, &e);
}

int bergdb_set_reclaim_internal_fraction(bergdb_db *db, double fraction) {
    if (db == NULL) {
        return BERGDB_ARG;
    }
    if (db->in_callback) {
        return fail_state(db);
    }
    struct err e;
    enum err_code rc = db_set_reclaim_internal_fraction(&db->db, fraction, &e);
    return done(db, rc, &e);
}

int bergdb_stats(bergdb_db *db, struct bergdb_stats *s) {
    if (db == NULL || s == NULL) {
        return fail_arg(db, "NULL");
    }
    if (db->in_callback) {
        return fail_state(db);
    }
    memset(s, 0, sizeof *s);
    s->stream_length = db_stream_length(&db->db);
    s->durable_length = stream_durable_length(&db->db.stream);
    s->last_trans_pos_of_last_valid_meta_block = db->db.rs.lastTransSposOfLastValidMetaBlock;
    s->first_available_lookup_time = db_first_available_time(&db->db);
    s->first_available_pos = db_first_available_pos(&db->db);
    s->startup_distance = db->db.startup_distance;
    s->cache_size_indicator = db->db.cache_size_indicator;
    s->retain_duration = db->db.retain_duration;
    s->internal_fraction = db->db.internal_fraction;
    s->reclaim_iteration_count = 0;
    s->transaction_count = db->db.transaction_count;
    s->kv_count = db->db.kv_count;
    s->get_op_count = db->db.get_op_count;
    db->errmsg[0] = '\0';
    return BERGDB_OK;
}
