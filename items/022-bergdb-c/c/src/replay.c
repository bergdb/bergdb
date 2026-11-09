/* replay: C's reads of Java's databases by a full replay; see replay.h. */
#include "replay.h"
#include <assert.h>
#include <string.h>
#include "bytes.h"
#include "keys.h"
#include "snode.h"
#include "spos.h"

/* Db.CREATION_LENGTH: the creation's record ends at 264. */
#define CREATION_LENGTH 264

/* Reclaim.TABLE_KEY_NAME, the ikey of reclaim's table (012-02, 8.13). */
static const char TABLE_KEY_NAME[] = "/#i/dreclaim/-table.txt";

static enum err_code unsupported(struct err *e, const char *why) {
    return err_set(e, ERR_ARG, "UnsupportedOperationException", "%s", why);
}

/* A scratch array of n segments, grown through the allocator. */
struct segs {
    int64_t *p;
    int32_t cap;
};

static bool segs_ensure(struct segs *s, struct mem *m, int32_t n) {
    if (s->cap >= n) {
        return true;
    }
    int32_t cap = n < 16 ? 16 : n;
    int64_t *p = mem_realloc(m, s->p, (size_t) s->cap * sizeof *p, (size_t) cap * sizeof *p,
            MEM_BUFFER);
    if (p == NULL) {
        return false;
    }
    s->p = p;
    s->cap = cap;
    return true;
}

static void segs_free(struct segs *s, struct mem *m) {
    mem_free(m, s->p, (size_t) s->cap * sizeof *s->p, MEM_BUFFER);
    s->p = NULL;
    s->cap = 0;
}

/* Db.getStartupPosFromLastTransaction: the startupPos of the last committed
 * record, walking from transPos (the meta block's last transaction). */
static enum err_code startup_pos_from_last_transaction(struct replay *r, int64_t transPos,
        int64_t *out, struct err *e) {
    if (transPos == SPOS_NULL) {
        transPos = META_BLOCK_SIZE;     /* The first transaction. */
    }
    assert(transPos >= 0 && "bad transPos");

    struct ns_iter iter;
    struct st_record rec;
    ns_iter_init(&iter, &r->view, r->mem, transPos, true);
    st_init(&rec);
    int64_t result = transPos;
    int64_t lastTpos = SPOS_NULL;
    enum err_code rc = ERR_OK;

    while (true) {
        bool has;
        rc = ns_iter_next(&iter, &has, e);
        if (rc != ERR_OK || !has) {
            break;
        }
        rc = st_parse(&rec, iter.tpos, iter.buf.p, iter.size, r->mem, e);
        if (rc != ERR_OK) {
            break;
        }
        result = rec.startup_pos;
        /* Db.checkStartupPos (bergdb 015-75, as Java's since release 2026.3). */
        rc = st_check_startup_pos(&rec, e);
        if (rc != ERR_OK) {
            break;
        }
        lastTpos = rec.tpos;
    }
    st_free(&rec, r->mem);
    ns_iter_free(&iter);
    if (rc != ERR_OK) {
        return rc;
    }
    if (lastTpos != SPOS_NULL) {
        meta_set_last_trans(&r->meta, lastTpos);
    }
    *out = result;
    return ERR_OK;
}

/* Db.readTransactions, counted: the startup section's records from
 * startupPos, as StartInfo reports them. */
static enum err_code read_transactions(struct replay *r, int64_t startupPos, struct err *e) {
    if (startupPos == 0) {
        startupPos = META_BLOCK_SIZE;
    }
    struct ns_iter ti;
    struct st_record rec;
    ns_iter_init(&ti, &r->view, r->mem, startupPos, true);
    st_init(&rec);
    enum err_code rc = ERR_OK;
    r->trans_count = 0;
    while (true) {
        bool has;
        rc = ns_iter_next(&ti, &has, e);
        if (rc != ERR_OK || !has) {
            break;
        }
        rc = st_parse(&rec, ti.tpos, ti.buf.p, ti.size, r->mem, e);
        if (rc != ERR_OK) {
            break;
        }
        if (r->trans_count == 0) {
            r->start_time = rec.tt;
        }
        r->trans_count++;
        r->last_pos = rec.last_pos;
    }
    st_free(&rec, r->mem);
    ns_iter_free(&ti);
    if (rc == ERR_OK && r->trans_count == 0) {
        /* setLastTransTimeOfDbClock */
        rc = err_set(e, ERR_FORMAT, "StreamFormatException",
                "No transactions in startup transaction set.");
    }
    return rc;
}

/* The full replay: every committed record from the creation on, its value
 * and delete nodes applied at its time. */
static enum err_code replay_all(struct replay *r, struct err *e) {
    struct ns_iter ti;
    struct st_record rec;
    struct segs key = { NULL, 0 };
    ns_iter_init(&ti, &r->view, r->mem, META_BLOCK_SIZE, true);
    st_init(&rec);
    enum err_code rc = ERR_OK;

    while (true) {
        bool has;
        rc = ns_iter_next(&ti, &has, e);
        if (rc != ERR_OK || !has) {
            break;
        }
        rc = st_parse(&rec, ti.tpos, ti.buf.p, ti.size, r->mem, e);
        if (rc != ERR_OK) {
            break;
        }

        if (!r->made) {
            /* The creation: its Dag, as Db.writePrimordialTransaction makes it. */
            for (int32_t i = 0; i < rec.nnodes; i++) {
                if (rec.nodes[i].type == NODE_VALUE || rec.nodes[i].type == NODE_DELETE) {
                    rc = err_set(e, ERR_FORMAT, "StreamFormatException", "C's replay: the "
                            "first record, at %lld, is not a creation: it has a value node",
                            (long long) rec.tpos);
                    goto done;
                }
            }
            if (!mdb_create(&r->db, r->mem, rec.tt, r->max_node_size)) {
                rc = err_set(e, ERR_NOMEM, "OutOfMemoryError", "the replay's database");
                goto done;
            }
            r->made = true;
            r->records++;
            continue;
        }

        if (rec.tt <= r->db.last_transaction_time) {
            rc = err_set(e, ERR_FORMAT, "StreamFormatException", "C's replay: the record at "
                    "%lld has the time %lld, not after the last one, %lld", (long long) rec.tpos,
                    (long long) rec.tt, (long long) r->db.last_transaction_time);
            goto done;
        }
        mdb_begin(&r->db, rec.tt);
        for (int32_t i = 0; i < rec.nnodes; i++) {
            const struct sn_node *n = &rec.nodes[i];
            if (n->type != NODE_VALUE && n->type != NODE_DELETE) {
                continue;
            }
            if (!segs_ensure(&key, r->mem, n->key_n)) {
                rc = err_set(e, ERR_NOMEM, "OutOfMemoryError", "a key of %d segments",
                        (int) n->key_n);
                goto done;
            }
            for (int32_t j = 0; j < n->key_n; j++) {
                key.p[j] = sn_seg(n, j);
            }
            r->db.have_value_pos = true;
            r->db.value_spos = n->spos;
            r->db.value_id = n->id;
            r->db.value_tpos = n->tpos;
            if (!mdb_put(&r->db, key.p, n->key_n, n->type == NODE_DELETE ? NULL : n->value,
                    n->value_len)) {
                rc = err_set(e, ERR_NOMEM, "OutOfMemoryError", "a put of the replay");
                goto done;
            }
            r->pairs++;
        }
        mdb_end(&r->db);
        r->records++;
    }
    if (rc == ERR_OK && !r->made) {
        rc = err_set(e, ERR_FORMAT, "StreamFormatException", "C's replay: no creation record");
    }
done:
    segs_free(&key, r->mem);
    st_free(&rec, r->mem);
    ns_iter_free(&ti);
    return rc;
}

/* Reclaim.initFromDb, as far as the replay goes: without the table, the
 * first available position and time are 0. */
static enum err_code init_reclaim(struct replay *r, struct err *e) {
    uint8_t bkey[sizeof TABLE_KEY_NAME];
    int32_t len = (int32_t) (sizeof TABLE_KEY_NAME - 1);
    bool ok = keys_ikey_to_bkey((const uint8_t *) TABLE_KEY_NAME, len, bkey);
    assert(ok);
    (void) ok;
    int64_t segs[8];
    int32_t n = keys_segment_count(len);
    assert(n <= 8);
    keys_to_segments(bkey, len, segs);

    struct getdata gd;
    struct vnode *v;
    mdb_new_get_data(&r->db, &gd);
    if (!mdb_get_one(&r->db, INT64_MAX, segs, n, &gd, &v)) {
        return err_set(e, ERR_NOMEM, "OutOfMemoryError", "a read of reclaim's table");
    }
    if (v != NULL) {
        return unsupported(e, "the database has reclaim's table: its first available time and "
                "position are 012-11's to read");
    }
    r->first_available_pos = 0;
    r->first_available_time = 0;
    return ERR_OK;
}

enum err_code replay_open(struct replay *r, struct stream *s, struct mem *m,
        int32_t max_node_size, struct err *e) {
    enum err_code rc;
    memset(r, 0, sizeof *r);
    r->mem = m;
    r->s = s;
    r->max_node_size = max_node_size;
    st_init(&r->gt_rec);
    stream_as_storage(s);               /* StorageManager's BufferedStream (022-02, D6) */

    /* handleEmptyStream: Java creates the database (012-09). */
    if (stream_length(s) == 0) {
        return unsupported(e, "an empty stream, which Java's start creates (012-09)");
    }

    /* refuseIncompleteCreation (005-33) */
    bool incomplete;
    rc = rs_is_incomplete_creation(s, CREATION_LENGTH, &incomplete, e);
    if (rc != ERR_OK) {
        goto fail;
    }
    if (incomplete) {
        rc = err_set(e, ERR_FORMAT, "DatabaseNotCreatedException", "The stream holds a "
                "creation that did not complete.");
        goto fail;
    }

    /* refuseOtherNodeSize (005-50), then nodeStream.recover(): its plan. */
    rc = rs_check_node_size(s, max_node_size, e);
    if (rc == ERR_OK) {
        rc = rs_plan_recovery(s, &r->plan, e);
    }
    if (rc != ERR_OK) {
        if (strcmp(e->java, "BadMagicBytes") == 0) {
            e->java = "BadCryptoKey";
        }
        goto fail;
    }
    r->length = r->plan.length_after;
    r->view = *s;
    if (r->plan.torn != SPOS_NULL) {
        r->view.length = r->plan.torn;
    }

    /* handleStartParams: the in-memory meta block is the last valid one. */
    r->meta = r->plan.last_valid;
    rc = meta_check_format(&r->meta, e);
    if (rc != ERR_OK) {
        goto fail;
    }
    rc = startup_pos_from_last_transaction(r, meta_last_trans(&r->meta), &r->start_pos, e);
    if (rc != ERR_OK) {
        goto fail;
    }
    r->startup_distance = meta_startup_distance(&r->meta);

    /* readTransactions and setLastTransTimeOfDbClock */
    rc = read_transactions(r, r->start_pos, e);
    if (rc != ERR_OK) {
        goto fail;
    }

    /* startDb: here the full replay, from the stream's first record. */
    if (stream_first_pos(s) != 0) {
        rc = unsupported(e, "a cut stream: a full replay reads the stream from its start "
                "(012-10, 012-11)");
        goto fail;
    }
    rc = replay_all(r, e);
    if (rc != ERR_OK) {
        goto fail;
    }

    /* reclaim.initFromDb() */
    rc = init_reclaim(r, e);
    if (rc != ERR_OK) {
        goto fail;
    }
    obj_collect(&r->db.cx);
    return ERR_OK;

fail:
    replay_close(r);
    return rc;
}

void replay_close(struct replay *r) {
    if (r->made) {
        mdb_free(&r->db);
        r->made = false;
    }
    if (r->gt_open) {
        ns_iter_free(&r->gt);
        r->gt_open = false;
    }
    st_free(&r->gt_rec, r->mem);
}

/* Db.getTrans */
enum err_code replay_get_trans(struct replay *r, int64_t tpos, const struct st_record **out,
        struct err *e) {
    /* Refused before it reads (005-34): it would read the middle of a
     * record as a transaction. */
    const int64_t inBlock = tpos % META_BLOCK_DISTANCE;
    if (tpos < 0 || tpos % RS_TRANS_ALIGNMENT != 0 || inBlock < META_BLOCK_SIZE) {
        return err_set(e, ERR_ARG, "IllegalArgumentException", "Not a position of a "
                "transaction, %lld.", (long long) tpos);
    }
    if (r->failed) {
        return err_set(e, ERR_IO, "DbFailedException", "The database has failed.");
    }

    if (r->gt_open) {
        ns_iter_free(&r->gt);
    }
    ns_iter_init(&r->gt, &r->view, r->mem, tpos, true);
    r->gt_open = true;
    bool has = false;
    enum err_code rc;
    if (r->plan.torn != SPOS_NULL && tpos == r->plan.torn) {
        /* Java reads the torn record after its fill: failed, not committed. */
        rc = err_set(e, ERR_FORMAT, "StreamFormatException", "Transaction at start pos %lld is "
                "not committed (its last byte is 0).", (long long) tpos);
    } else {
        rc = ns_iter_next(&r->gt, &has, e);
    }
    if (rc == ERR_OK && has) {
        rc = st_parse(&r->gt_rec, r->gt.tpos, r->gt.buf.p, r->gt.size, r->mem, e);
    }
    if (rc == ERR_NOT_AVAILABLE) {
        /* isReadBelowCut: reclaim has removed it. */
        return err_set(e, ERR_NOT_AVAILABLE, "LookupTimeNotAvailableException", "The "
                "transaction at stream pos %lld is no longer available: reclaim has removed it.",
                (long long) tpos);
    }
    if (rc == ERR_NOMEM) {
        return rc;
    }
    if (rc != ERR_OK) {
        /* failOnStorage: a read that failed, or corrupt data, fails the database. */
        r->failed = true;
        return err_set(e, rc, "DbFailedException", "A read failed: %s", e->text);
    }
    if (!has) {
        /* At or past the end of the stream (005-43). */
        return err_set(e, ERR_ARG, "IllegalArgumentException", "Not a position of a "
                "transaction, %lld: at or past the end of the stream.", (long long) tpos);
    }
    *out = &r->gt_rec;
    return ERR_OK;
}
