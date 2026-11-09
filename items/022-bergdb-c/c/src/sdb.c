/* sdb: a database opened by the bounded startup, for reads; see sdb.h. */
#include "sdb.h"
#include <assert.h>
#include <inttypes.h>
#include <string.h>
#include "keys.h"
#include "reclaim.h"
#include "snode.h"
#include "spos.h"

/* Reclaim.TABLE_KEY_NAME, the ikey of reclaim's table (012-02, 8.13). */
static const char TABLE_KEY_NAME[] = "/#i/dreclaim/-table.txt";
/* Reclaim.SETTINGS_KEY_NAME, reclaim's settings (015-87). */
static const char SETTINGS_KEY_NAME[] = RC_SETTINGS_KEY_NAME;

static enum err_code unsupported(struct err *e, const char *why) {
    return err_set(e, ERR_ARG, "UnsupportedOperationException", "%s", why);
}

/* The roots of the database's objects (012-07, 6.4): the node table's
 * handles, the Dag's super root, the newest written top node, D's nodes;
 * each one counted holder. *n their number; the array is the caller's to
 * release: MEM_STATE, cap entries. */
static struct obj **roots_of(struct sdb *d, int32_t *n, int32_t *cap) {
    int64_t count = nt_size(&d->nt) + 2;
    for (struct ts_info *t = d->ts.first; t != NULL; t = t->next) {
        count += t->ndirty;
    }
    struct obj **roots = mem_alloc(d->mem, (size_t) count * sizeof *roots, MEM_STATE);
    if (roots == NULL) {
        return NULL;
    }
    int32_t k = 0;
    for (int64_t i = 0; i < nt_slots(&d->nt); i++) {
        struct handle *h = nt_slot(&d->nt, i);
        if (h != NULL) {
            roots[k++] = &h->o;
        }
    }
    if (d->dag_made) {
        struct tnode *sr = tds_get_super_root(&d->dag.top_ds);
        if (sr != NULL) {
            roots[k++] = &sr->n.o;
        }
    }
    if (d->newest_written_top != NULL) {
        roots[k++] = &d->newest_written_top->n.o;
    }
    for (struct ts_info *t = d->ts.first; t != NULL; t = t->next) {
        for (int32_t i = 0; i < t->ndirty; i++) {
            roots[k++] = &((struct node *) t->gotDirtyNodes[i].node)->o;
        }
    }
    *n = k;
    *cap = (int32_t) count;
    return roots;
}

int64_t sdb_recount(struct sdb *d) {
    int32_t n, cap;
    struct obj **roots = roots_of(d, &n, &cap);
    if (roots == NULL) {
        return -1;
    }
    int64_t wrong = obj_recount(&d->cx, roots, n, NULL);
    mem_free(d->mem, roots, (size_t) cap * sizeof *roots, MEM_STATE);
    return wrong;
}

/* Close's walk: every object, without trusting the counts. Without memory
 * for the roots, the table's handles are walked one at a time. */
static void free_all(struct sdb *d) {
    int32_t n, cap;
    struct obj **roots = roots_of(d, &n, &cap);
    if (roots != NULL) {
        obj_free_all(&d->cx, roots, n);
        mem_free(d->mem, roots, (size_t) cap * sizeof *roots, MEM_STATE);
        if (d->dag_made) {
            d->dag.top_ds.super_root = NULL;
        }
        d->newest_written_top = NULL;
        for (struct ts_info *t = d->ts.first; t != NULL; t = t->next) {
            t->ndirty = 0;      /* their nodes are freed */
        }
        nt_free(&d->nt, false);
    } else {
        /* No room for the roots' list: every holder lets go, and the safe
         * point frees what the counts let go; the recount checks them. */
        if (d->dag_made) {
            dag_free(&d->dag);
        }
        obj_release(&d->cx, d->newest_written_top == NULL ? NULL : &d->newest_written_top->n.o);
        d->newest_written_top = NULL;
        for (struct ts_info *t = d->ts.first; t != NULL; t = t->next) {
            for (int32_t i = 0; i < t->ndirty; i++) {
                obj_release(&d->cx, &((struct node *) t->gotDirtyNodes[i].node)->o);
            }
            t->ndirty = 0;
        }
        nt_free(&d->nt, true);
        obj_collect(&d->cx);
    }
    ts_free(&d->ts);
    nc_free(&d->nc);
    if (d->gt_open) {
        ns_iter_free(&d->gt);
        d->gt_open = false;
    }
    st_free(&d->gt_rec, d->mem);
}

/* The value of an internal key at the latest time, as Java's getOne
 * through the readers' follower: *v NULL if none. */
static enum err_code get_latest(struct sdb *d, const char *ikey, size_t len,
        struct vnode **v, struct err *e) {
    uint8_t bkey[64];
    bool ok = len <= sizeof bkey && keys_ikey_to_bkey((const uint8_t *) ikey, (int32_t) len,
            bkey);
    assert(ok);
    (void) ok;
    int64_t segs[8];
    int32_t n = keys_segment_count((int32_t) len);
    assert(n <= 8);
    keys_to_segments(bkey, (int32_t) len, segs);
    struct getdata gd;
    sdb_new_get_data(d, &gd);
    enum err_code rc = sdb_get_one(d, INT64_MAX, segs, n, &gd, v, e);
    if (rc == ERR_OK && *v != NULL && (*v)->len < 0) {
        *v = NULL;
    }
    return rc;
}

/* Reclaim.initFromDb: reclaim's settings checked, as a start refuses any
 * other form than the one the setters write (rc_settings_parse, 015-87),
 * though sdb uses none; the table read at the latest time, as Java's (a
 * getOne through the readers' follower); the first available position and
 * time from the row marked cut with the largest pStart (rc_first_available_
 * of_table), or 0 and 0 without the table; and a cut that the table marks
 * but the stream does not show yet made (pretruncate), as Java's start does
 * (012-11). The current row matters for the steps only, which sdb does not
 * make. */
static enum err_code init_from_db(struct sdb *d, struct err *e) {
    struct vnode *v;
    d->first_available_pos = 0;
    d->first_available_time = 0;
    enum err_code rc = get_latest(d, SETTINGS_KEY_NAME, sizeof SETTINGS_KEY_NAME - 1, &v, e);
    if (rc == ERR_OK && v != NULL) {
        int64_t retain;
        int32_t fraction;
        rc = rc_settings_parse(d->mem, (const char *) v->value, (size_t) v->len, &retain,
                &fraction, e);
    }
    if (rc == ERR_OK) {
        rc = get_latest(d, TABLE_KEY_NAME, sizeof TABLE_KEY_NAME - 1, &v, e);
    }
    if (rc != ERR_OK || v == NULL) {
        return rc;
    }
    int64_t pos, time;
    rc = rc_first_available_of_table(d->mem, (const char *) v->value, (size_t) v->len, &pos,
            &time, e);
    if (rc != ERR_OK) {
        return rc;
    }
    if (pos > 0 && stream_first_pos(d->s) < pos) {
        rc = stream_pretruncate(d->s, pos, e);  /* A crash came between the table write and the cut. */
        if (rc != ERR_OK) {
            return rc;
        }
    }
    d->first_available_pos = pos;
    d->first_available_time = time;
    return ERR_OK;
}

enum err_code sdb_open(struct sdb *d, struct stream *s, struct mem *m, int32_t max_node_size,
        bool check_link, struct err *e) {
    memset(d, 0, sizeof *d);
    d->mem = m;
    d->s = s;
    d->max_node_size = max_node_size;
    stream_as_storage(s);               /* StorageManager's BufferedStream (022-02, D6) */
    obj_ctx_init(&d->cx, m);
    rs_init(&d->rs, s);
    nt_init(&d->nt, &d->cx, m);
    nc_init(&d->nc, &d->cx, m, s, &d->nt);
    d->nc.check_link = check_link;
    ts_init(&d->ts, m);
    st_init(&d->gt_rec);
    err_clear(&d->failure);

    enum err_code rc;
    /* handleEmptyStream: the creation is 012-09's. */
    if (stream_length(s) == 0) {
        rc = unsupported(e, "an empty stream, which Java's start creates (012-09)");
        free_all(d);
        return rc;
    }
    struct sr_env env = { m, &d->cx, &d->rs, &d->nt, &d->nc, &d->dag, &d->ts, max_node_size,
            1, NULL };
    rc = sr_check_and_recover(&env, &d->plan, e);
    if (rc == ERR_OK) {
        rc = sr_start(&env, &d->start, e);
        d->dag_made = d->start.dag_made;
        d->newest_written_top = d->start.newest_written_top;
    }
    if (rc == ERR_OK) {
        d->last_trans_time = d->start.last_trans_time;  /* setLastTransTimeOfDbClock */
        rc = init_from_db(d, e);
    }
    if (rc != ERR_OK) {
        free_all(d);
        return rc;
    }
    obj_collect(&d->cx);
    return ERR_OK;
}

void sdb_close(struct sdb *d) {
    free_all(d);
}

void sdb_new_get_data(struct sdb *d, struct getdata *gd) {
    dag_new_get_data(&d->dag, gd);
    gd->op.pointer_follower.follow = nc_follow_reader;
    gd->op.pointer_follower.ctx = &d->nc;
    gd->op.err = &d->nc.err;        /* the Dag's own failures (019-32) */
}

void sdb_new_get_many(struct sdb *d, struct getmany *g) {
    gm_init(g, &d->dag, d->mem);
    g->gd.op.pointer_follower.follow = nc_follow_reader;
    g->gd.op.pointer_follower.ctx = &d->nc;
    g->gd.op.err = &d->nc.err;
    g->collect = &d->cx;
}

int64_t sdb_lookup_time(const struct sdb *d, int64_t wanted) {
    const int64_t last = d->last_trans_time;
    return wanted > last ? last : wanted;
}

/* failOnStorage: a read that failed fails the database (005-30). */
static enum err_code fail_on_storage(struct sdb *d, struct err *e) {
    if (e->code == ERR_NOMEM) {
        return ERR_NOMEM;
    }
    if (!d->failed) {
        d->failed = true;
        d->failure = *e;
    }
    return err_set(e, e->code, "DbFailedException", "A read failed: %s", d->failure.text);
}

static enum err_code check_failed(const struct sdb *d, struct err *e) {
    if (d->failed) {
        return err_set(e, d->failure.code, "DbFailedException", "The database has failed: %s",
                d->failure.text);
    }
    return ERR_OK;
}

enum err_code sdb_get_one(struct sdb *d, int64_t lookupTime, const int64_t *key, int32_t n,
        struct getdata *gd, struct vnode **out, struct err *e) {
    enum err_code rc = check_failed(d, e);
    if (rc != ERR_OK) {
        return rc;
    }
    obj_collect(&d->cx);        /* the last call's value goes now */
    if (lookupTime < d->first_available_time) {
        return err_set(e, ERR_NOT_AVAILABLE, "LookupTimeNotAvailableException", "lookup time %"
                PRId64 " is before the first available time %" PRId64, lookupTime,
                d->first_available_time);
    }
    gd->actual_lookup_time = sdb_lookup_time(d, lookupTime);
    gd->node_depth = 0;
    err_clear(&d->nc.err);
    if (!dag_get_one(&d->dag, gd->actual_lookup_time, key, n, gd, out)) {
        *e = d->nc.err;
        if (e->code == ERR_OK) {
            err_set(e, ERR_NOMEM, "OutOfMemoryError", "a getOne");
        }
        return fail_on_storage(d, e);
    }
    return ERR_OK;
}

enum err_code sdb_get_many(struct sdb *d, struct getmany *g, struct err *e) {
    enum err_code rc = check_failed(d, e);
    if (rc != ERR_OK) {
        return rc;
    }
    obj_collect(&d->cx);
    if (g->lookup_time < d->first_available_time) {
        return err_set(e, ERR_NOT_AVAILABLE, "LookupTimeNotAvailableException", "lookup time %"
                PRId64 " is before the first available time %" PRId64, g->lookup_time,
                d->first_available_time);
    }
    g->actual_lookup_time = sdb_lookup_time(d, g->lookup_time);
    err_clear(&d->nc.err);
    bool ok = dag_get_many(&d->dag, g);
    obj_collect(&d->cx);
    if (!ok) {
        *e = d->nc.err;
        if (e->code == ERR_OK) {
            err_set(e, ERR_NOMEM, "OutOfMemoryError", "a getMany");
        }
        return fail_on_storage(d, e);
    }
    return ERR_OK;
}

enum err_code sdb_get_trans(struct sdb *d, int64_t tpos, const struct st_record **out,
        struct err *e) {
    /* Refused before it reads (005-34). */
    const int64_t inBlock = tpos % META_BLOCK_DISTANCE;
    if (tpos < 0 || tpos % RS_TRANS_ALIGNMENT != 0 || inBlock < META_BLOCK_SIZE) {
        return err_set(e, ERR_ARG, "IllegalArgumentException", "Not a position of a "
                "transaction, %" PRId64 ".", tpos);
    }
    enum err_code rc = check_failed(d, e);
    if (rc != ERR_OK) {
        return rc;
    }
    if (d->gt_open) {
        ns_iter_free(&d->gt);
    }
    ns_iter_init(&d->gt, d->s, d->mem, tpos, true);
    d->gt_open = true;
    bool has = false;
    rc = ns_iter_next(&d->gt, &has, e);
    if (rc == ERR_OK && has) {
        rc = st_parse(&d->gt_rec, d->gt.tpos, d->gt.buf.p, d->gt.size, d->mem, e);
    }
    if (rc == ERR_NOT_AVAILABLE) {
        return err_set(e, ERR_NOT_AVAILABLE, "LookupTimeNotAvailableException", "The "
                "transaction at stream pos %" PRId64 " is no longer available: reclaim has "
                "removed it.", tpos);
    }
    if (rc != ERR_OK) {
        return fail_on_storage(d, e);
    }
    if (!has) {
        /* At or past the end of the stream (005-43). */
        return err_set(e, ERR_ARG, "IllegalArgumentException", "Not a position of a "
                "transaction, %" PRId64 ": at or past the end of the stream.", tpos);
    }
    *out = &d->gt_rec;
    return ERR_OK;
}
