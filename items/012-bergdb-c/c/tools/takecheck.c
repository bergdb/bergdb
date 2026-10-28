/*
 * bergdb-takecheck: replays the take (bergdb 012-09, part 1; 012-02,
 * section 8.7) from a stream that Java wrote, with C's take (transseq) on
 * C's parsed records (nstream, strans), and compares each record's
 * decisions with what the record holds. It is 012-02's check_scan.py in
 * C, on the module that 012-09 writes with, and stronger: it also checks
 * which index nodes each record holds and in what order.
 *
 * For each committed record after the creation (oldest first), with D the
 * transactions after the startup position, each with its position, its
 * got-dirty count (the pairs of its record, in order) and its own bytes
 * (48 and the sizes of its value and delete nodes), the record's position
 * as the stream's length, its own bytes, and the startup distance in force
 * (that of the last valid meta block at or before the record's last byte:
 * the setting changes only before setStartupDistance's dummy record,
 * which holds a block), it calls ts_take as Db.store does, and checks:
 *
 *   sp     the new startup position is the record's startupPos;
 *   nodes  the record's index nodes are the got-dirty nodes of the
 *          transactions taken, each once (by id), in the take's order, the
 *          top nodes first, then the key nodes.
 *
 * The byte budget (005-17), recordLimit minus the record's fixed bytes,
 * is given with bounds that make it smaller than Java's (the record's
 * whole got-dirty count in the fixed bytes) and the costs larger (a node
 * not in the record at 4,096 bytes, the largest a node can be); a record
 * where the bounds reach the budget is counted as undecided, an error. A
 * stream that a cut shortened at the front (reclaim) is replayed from the
 * first record whose startup position is in the stream, as the scan
 * script did. Failed records (recovery's fill) are no transactions and
 * are skipped, as every walk skips them.
 *
 * Usage: bergdb-takecheck [-v] DIR...
 * Prints a line per directory, "takecheck DIR records=N takes=T taken=K
 * nodes=M errors=E", the first errors of each, and a last line
 * "TAKECHECK OK: ..." or "TAKECHECK FAILED: ...". Exit status 0, 1 if any
 * error, 2 on bad usage.
 */
#include <inttypes.h>
#include <stdarg.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "keys.h"
#include "mem.h"
#include "meta.h"
#include "nstream.h"
#include "rstream.h"
#include "snode.h"
#include "stream.h"
#include "strans.h"
#include "transseq.h"

#define MAX_NODE_BYTES 4096     /* above any node's size: a top node is at most 808 */
#define SHOW_ERRORS 10

/* An id and where it was met (or its type), for sorting. */
struct idx {
    int64_t id;
    int32_t at;
    int32_t type;
};

struct check {
    struct mem mem;
    struct err err;
    bool verbose;
    /* The valid meta blocks: positions and startup distances. */
    int64_t *mpos;
    int32_t *msd;
    int32_t nmeta, cap_meta;
    /* Records seen before the replay starts (a cut stream), as TransInfos. */
    struct ts_info **pending;
    int32_t npending, cap_pending;
    /* Per directory. */
    int64_t records, takes, taken, nodes, errors, undecided;
    /* In all. */
    int64_t all_records, all_takes, all_taken, all_nodes, all_errors, dirs;
    /* Why the transactions were taken: they fit in the share, by the
     * dither, or by the deadline alone; and the takes that stopped at a
     * transaction that d_h = 2 sd alone would have taken (the span term,
     * D4:B of 007-07, decided them). */
    int64_t fits, dither, deadline, stops_span;
    /* The cost's bound for the current record, and the costs asked for. */
    const struct st_record *rec;
    int64_t cost_sum;
    /* check_nodes' buffers. */
    struct idx *met, *rec_ids;
    int32_t cap_met, cap_rec;
};

static void error(struct check *c, const char *fmt, ...) {
    va_list ap;
    c->errors++;
    if (c->errors <= SHOW_ERRORS || c->verbose) {
        printf("  error: ");
        va_start(ap, fmt);
        vprintf(fmt, ap);
        va_end(ap);
        printf("\n");
    }
}

/* The startup distance in force for a record that ends at lastPos. */
static int32_t sd_at(const struct check *c, int64_t lastPos) {
    int32_t sd = c->nmeta > 0 ? c->msd[0] : -1;
    for (int32_t i = 0; i < c->nmeta && c->mpos[i] <= lastPos; i++) {
        sd = c->msd[i];
    }
    return sd;
}

/* The cost of a transaction's nodes (TransSeq.recordBytes), bounded from
 * above: a node of the record its size there (exact: the take's nodes are
 * written as they are at the take), another the largest a node can be. */
static int64_t cost_bound(void *ctx, const struct ts_info *info) {
    struct check *c = ctx;
    int64_t bytes = 0;
    for (int32_t i = 0; i < info->ndirty; i++) {
        int64_t size = MAX_NODE_BYTES;
        for (int32_t k = 0; k < c->rec->nnodes; k++) {
            const struct sn_node *n = &c->rec->nodes[k];
            if ((n->type == NODE_TOP || n->type == NODE_KEY)
                    && n->id == info->gotDirtyNodes[i].id) {
                size = n->size;
                break;
            }
        }
        bytes += size + 16;
    }
    c->cost_sum += bytes;
    return bytes;
}

/* A TransInfo of a record: its got-dirty pairs' ids, in order. */
static struct ts_info *info_of(struct check *c, const struct st_record *r, int64_t own) {
    struct ts_info *info = ts_info_new(&c->mem);
    if (info == NULL) {
        return NULL;
    }
    info->tpos = r->tpos;
    info->lastPos = r->last_pos;
    info->tt = r->tt;
    info->startupPos = r->startup_pos;
    info->ownBytes = own;
    for (int32_t i = 0; i < r->got_dirty_count; i++) {
        if (ts_info_add_node(info, &c->mem, NULL, st_got_dirty_id(r, i), 0, &c->err)
                != ERR_OK) {
            ts_info_free(info, &c->mem);
            return NULL;
        }
    }
    return info;
}

static int by_at(const void *a, const void *b) {
    const struct idx *x = a, *y = b;
    return x->at < y->at ? -1 : x->at > y->at;
}

static int by_id(const void *a, const void *b) {
    const struct idx *x = a, *y = b;
    if (x->id != y->id) {
        return x->id < y->id ? -1 : 1;
    }
    return x->at < y->at ? -1 : x->at > y->at;
}

static bool grow(struct check *c, struct idx **p, int32_t *cap, int32_t need) {
    if (need <= *cap) {
        return true;
    }
    int32_t c2 = *cap == 0 ? 64 : *cap;
    while (c2 < need) {
        c2 *= 2;
    }
    struct idx *p2 = mem_realloc(&c->mem, *p, (size_t) *cap * sizeof **p,
            (size_t) c2 * sizeof **p, MEM_BUFFER);
    if (p2 == NULL) {
        return false;
    }
    *p = p2;
    *cap = c2;
    return true;
}

/* The record's index nodes against the taken transactions' got-dirty
 * nodes: each id once (the first time the take met it, as
 * TransNodes.isInTransNodes), in the take's order, top nodes first. */
static void check_nodes(struct check *c, const struct st_record *r, struct ts_info *taken) {
    int32_t nmet = 0, nrec = 0;
    struct idx *met, *rec;

    for (struct ts_info *t = taken; t != NULL; t = t->next) {
        if (!grow(c, &c->met, &c->cap_met, nmet + t->ndirty)) {
            error(c, "out of memory");
            return;
        }
        for (int32_t i = 0; i < t->ndirty; i++) {
            c->met[nmet].id = t->gotDirtyNodes[i].id;
            c->met[nmet].at = nmet;
            nmet++;
        }
    }
    if (!grow(c, &c->rec_ids, &c->cap_rec, r->nnodes)) {
        error(c, "out of memory");
        return;
    }
    met = c->met;
    rec = c->rec_ids;
    for (int32_t i = 0; i < r->nnodes; i++) {
        if (r->nodes[i].type == NODE_TOP || r->nodes[i].type == NODE_KEY) {
            rec[nrec].id = r->nodes[i].id;
            rec[nrec].at = i;
            rec[nrec].type = r->nodes[i].type;
            nrec++;
        }
    }
    /* The ids met, each once: sorted by id and order, the first kept. */
    qsort(met, (size_t) nmet, sizeof *met, by_id);
    int32_t n = 0;
    for (int32_t i = 0; i < nmet; i++) {
        if (n == 0 || met[n - 1].id != met[i].id) {
            met[n++] = met[i];
        }
    }
    nmet = n;
    c->nodes += nmet;
    /* The record's index nodes by id, with their types. */
    qsort(rec, (size_t) nrec, sizeof *rec, by_id);
    for (int32_t i = 1; i < nrec; i++) {
        if (rec[i].id == rec[i - 1].id) {
            error(c, "record %" PRId64 ": index node %" PRId64 " twice", r->tpos, rec[i].id);
            return;
        }
    }
    if (nrec != nmet) {
        error(c, "record %" PRId64 ": %d index nodes, the take met %d", r->tpos, (int) nrec,
                (int) nmet);
        return;
    }
    /* The same ids (both sorted): the types of the ids met. */
    for (int32_t i = 0; i < nmet; i++) {
        if (met[i].id != rec[i].id) {
            error(c, "record %" PRId64 ": node %" PRId64 " met by the take is not in the "
                    "record", r->tpos, met[i].id);
            return;
        }
        met[i].type = rec[i].type;
    }
    /* In the take's order, each with its type in the record. */
    qsort(met, (size_t) nmet, sizeof *met, by_at);
    /* The record: the top nodes met, in order, then the key nodes. */
    int32_t index = 0;
    for (int pass = 0; pass < 2; pass++) {
        const int32_t type = pass == 0 ? NODE_TOP : NODE_KEY;
        for (int32_t k = 0; k < nmet; k++) {
            if (met[k].type != type) {
                continue;
            }
            while (index < r->nnodes && r->nodes[index].type != NODE_TOP
                    && r->nodes[index].type != NODE_KEY) {
                index++;
            }
            if (index == r->nnodes || r->nodes[index].type != type
                    || r->nodes[index].id != met[k].id) {
                error(c, "record %" PRId64 ": the %s node %" PRId64 " that the take met is "
                        "not next in the record", r->tpos, type == NODE_TOP ? "top" : "key",
                        met[k].id);
                return;
            }
            index++;
        }
    }
}

static void free_pending(struct check *c) {
    for (int32_t i = 0; i < c->npending; i++) {
        ts_info_free(c->pending[i], &c->mem);
    }
    mem_free(&c->mem, c->pending, (size_t) c->cap_pending * sizeof *c->pending, MEM_STATE);
    c->pending = NULL;
    c->npending = c->cap_pending = 0;
}

static bool add_pending(struct check *c, struct ts_info *info) {
    if (c->npending == c->cap_pending) {
        int32_t c2 = c->cap_pending == 0 ? 64 : 2 * c->cap_pending;
        struct ts_info **p2 = mem_realloc(&c->mem, c->pending,
                (size_t) c->cap_pending * sizeof *p2, (size_t) c2 * sizeof *p2, MEM_STATE);
        if (p2 == NULL) {
            return false;
        }
        c->pending = p2;
        c->cap_pending = c2;
    }
    c->pending[c->npending++] = info;
    return true;
}

static bool read_metas(struct check *c, struct stream *s) {
    const int64_t length = stream_length(s);
    c->nmeta = 0;
    for (int64_t m = (stream_first_pos(s) + META_BLOCK_DISTANCE - 1) / META_BLOCK_DISTANCE
            * META_BLOCK_DISTANCE; m + META_BLOCK_SIZE <= length; m += META_BLOCK_DISTANCE) {
        struct meta mb;
        if (rs_read_meta_block(s, m, &mb, &c->err) != ERR_OK) {
            error(c, "meta block at %" PRId64 ": %s: %s", m, c->err.java, c->err.text);
            return false;
        }
        if (!meta_is_valid(&mb)) {
            continue;
        }
        if (c->nmeta == c->cap_meta) {
            int32_t c2 = c->cap_meta == 0 ? 64 : 2 * c->cap_meta;
            int64_t *p2 = mem_realloc(&c->mem, c->mpos, (size_t) c->cap_meta * sizeof *p2,
                    (size_t) c2 * sizeof *p2, MEM_STATE);
            if (p2 == NULL) {
                return false;
            }
            c->mpos = p2;
            int32_t *s2 = mem_realloc(&c->mem, c->msd, (size_t) c->cap_meta * sizeof *s2,
                    (size_t) c2 * sizeof *s2, MEM_STATE);
            if (s2 == NULL) {
                return false;
            }
            c->msd = s2;
            c->cap_meta = c2;
        }
        c->mpos[c->nmeta] = m;
        c->msd[c->nmeta] = meta_startup_distance(&mb);
        c->nmeta++;
    }
    return true;
}

static void check_dir(struct check *c, const char *dir) {
    struct stream s;
    struct ts_seq d;
    struct st_record r;
    struct ns_iter it;
    bool has;
    enum err_code rc;

    c->records = c->takes = c->taken = c->nodes = c->errors = c->undecided = 0;
    printf("takecheck %s\n", dir);
    if (stream_open_dir(&s, dir, &c->mem, &c->err) != ERR_OK) {
        error(c, "open: %s: %s", c->err.java, c->err.text);
        goto summary;
    }
    ts_init(&d, &c->mem);
    st_init(&r);
    if (!read_metas(c, &s)) {
        goto close;
    }

    bool simulating = false;
    int64_t sp = 0;
    int64_t first_rec = -1;
    ns_iter_init(&it, &s, &c->mem, stream_first_pos(&s), false);
    while ((rc = ns_iter_next(&it, &has, &c->err)) == ERR_OK && has) {
        if (st_parse(&r, it.tpos, it.buf.p, it.size, &c->mem, &c->err) != ERR_OK) {
            error(c, "record %" PRId64 ": C's parser refuses it: %s: %s", it.tpos,
                    c->err.java, c->err.text);
            break;
        }
        c->records++;
        if (first_rec < 0) {
            first_rec = r.tpos;
        }
        int64_t own = 48;
        for (int32_t i = 0; i < r.nnodes; i++) {
            if (r.nodes[i].type == NODE_VALUE || r.nodes[i].type == NODE_DELETE) {
                own += r.nodes[i].size;
            }
        }
        if (r.tpos == META_BLOCK_SIZE) {
            /* The creation: not in D. */
            sp = r.startup_pos;
            simulating = true;
            continue;
        }
        if (simulating) {
            const int32_t sd = sd_at(c, r.last_pos);
            struct ts_info *taken;
            int32_t ntaken;
            const int64_t fixedBytes = own + 16 * (int64_t) r.got_dirty_count;
            const int64_t maxBytes = (int64_t) ST_MAX_RECORD_SIZE - fixedBytes;
            c->rec = &r;
            c->cost_sum = 0;
            /* For the counts of why each transaction was taken: the take's
             * values, from D's sums before it (TransSeq.take's). */
            const int64_t dcount = d.dirtyCount, obytes = d.ownBytes;
            int64_t newSp = ts_take(&d, sp, r.tpos, sd, own, maxBytes, cost_bound, c, &taken,
                    &ntaken);
            c->takes++;
            c->taken += ntaken;
            if (taken != NULL || !ts_is_empty(&d)) {
                const int64_t twice = 2 * (int64_t) sd;
                const double share = ts_share(dcount, own, obytes, r.tpos - sp, sd);
                const double u = ts_dither(r.tpos);
                int64_t got = 0;
                for (struct ts_info *t = taken; t != NULL; t = t->next) {
                    const int32_t count = t->ndirty;
                    if (!((double) (got + count) > share)) {
                        c->fits++;
                    } else if (share - (double) got > u * (double) count) {
                        c->dither++;
                    } else {
                        c->deadline++;
                    }
                    got += count;
                }
                if (!ts_is_empty(&d) && d.first->tpos <= r.tpos - twice) {
                    c->stops_span++;    /* a stop that d_h = 2 sd alone would have taken */
                }
            }
            if (c->cost_sum > maxBytes) {
                c->undecided++;
                error(c, "record %" PRId64 ": the bounds of the byte budget reach it: "
                        "undecided", r.tpos);
            }
            if (newSp != r.startup_pos) {
                error(c, "record %" PRId64 ": the take gives startupPos %" PRId64 ", the record"
                        " has %" PRId64 " (sd %d, D %d transactions)", r.tpos, newSp,
                        r.startup_pos, (int) sd, (int) (ts_size(&d) + ntaken));
                ts_info_free_chain(taken, &c->mem);
                break;      /* the replay of this stream stops at its first difference */
            } else {
                check_nodes(c, &r, taken);
            }
            ts_info_free_chain(taken, &c->mem);
        } else if (r.startup_pos >= first_rec) {
            /* The startup position is in the stream: D is the records after
             * it, up to this one. */
            simulating = true;
            for (int32_t i = 0; i < c->npending; i++) {
                if (c->pending[i]->tpos > r.startup_pos) {
                    if (ts_add(&d, c->pending[i], &c->err) != ERR_OK) {
                        error(c, "D: %s", c->err.text);
                        ts_info_free(c->pending[i], &c->mem);
                    }
                } else {
                    ts_info_free(c->pending[i], &c->mem);
                }
                c->pending[i] = NULL;
            }
            c->npending = 0;
        }
        struct ts_info *info = info_of(c, &r, own);
        if (info == NULL) {
            error(c, "out of memory");
            break;
        }
        if (simulating) {
            if (ts_add(&d, info, &c->err) != ERR_OK) {
                error(c, "D: %s", c->err.text);
                ts_info_free(info, &c->mem);
            }
            sp = r.startup_pos;
        } else if (!add_pending(c, info)) {
            ts_info_free(info, &c->mem);
            error(c, "out of memory");
            break;
        }
    }
    if (rc != ERR_OK) {
        error(c, "C's record walk fails: %s: %s", c->err.java, c->err.text);
    }
    ns_iter_free(&it);

close:
    free_pending(c);
    ts_free(&d);
    st_free(&r, &c->mem);
    stream_close(&s);
summary:
    printf("takecheck %s records=%" PRId64 " takes=%" PRId64 " taken=%" PRId64 " nodes=%"
            PRId64 " errors=%" PRId64 "\n", dir, c->records, c->takes, c->taken, c->nodes,
            c->errors);
    c->all_records += c->records;
    c->all_takes += c->takes;
    c->all_taken += c->taken;
    c->all_nodes += c->nodes;
    c->all_errors += c->errors;
    c->dirs++;
}

int main(int argc, char **argv) {
    static struct check check;
    struct check *c = &check;
    int i = 1;
    mem_init(&c->mem);
    err_clear(&c->err);
    if (i < argc && strcmp(argv[i], "-v") == 0) {
        c->verbose = true;
        i++;
    }
    if (i == argc) {
        fprintf(stderr, "Usage: bergdb-takecheck [-v] DIR...\n");
        return 2;
    }
    for (; i < argc; i++) {
        check_dir(c, argv[i]);
        fflush(stdout);
    }
    mem_free(&c->mem, c->mpos, (size_t) c->cap_meta * sizeof *c->mpos, MEM_STATE);
    mem_free(&c->mem, c->msd, (size_t) c->cap_meta * sizeof *c->msd, MEM_STATE);
    mem_free(&c->mem, c->met, (size_t) c->cap_met * sizeof *c->met, MEM_BUFFER);
    mem_free(&c->mem, c->rec_ids, (size_t) c->cap_rec * sizeof *c->rec_ids, MEM_BUFFER);
    if (c->mem.live_total != 0) {
        printf("TAKECHECK FAILED: %" PRId64 " bytes live at the end\n", c->mem.live_total);
        return 1;
    }
    printf("taken because they fit: %" PRId64 ", by the dither: %" PRId64 ", by the deadline "
            "alone: %" PRId64 "; takes that stopped at a transaction that 2 sd alone would "
            "have taken (the span term): %" PRId64 "\n", c->fits, c->dither, c->deadline,
            c->stops_span);
    printf("TAKECHECK %s: %" PRId64 " directories, %" PRId64 " records, %" PRId64
            " takes replayed, %" PRId64 " transactions taken, %" PRId64 " index nodes in "
            "order, %" PRId64 " errors\n", c->all_errors == 0 ? "OK" : "FAILED", c->dirs,
            c->all_records, c->all_takes, c->all_taken, c->all_nodes, c->all_errors);
    return c->all_errors == 0 ? 0 : 1;
}
