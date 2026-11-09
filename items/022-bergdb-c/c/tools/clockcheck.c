/*
 * bergdb-clockcheck: replays a cross workload's clock through C's DbClock
 * (bergdb 012-09, part 1; 012-01, 4.4; 012-02, 2.6 and 8.1) and compares
 * every transaction's time with the record that Java wrote, and every
 * currentTime() with Java's.
 *
 * The test clock is set by the workload's "clock T" and "t T" lines, as
 * Java's runner sets it (012-05, 6.1). Each segment's start makes a new
 * DbClock: at the creation (the first start, at the first line of the
 * segment that is neither "clock" nor "set") it reads the clock for the
 * creation's record; at a restart its last transaction time is the last
 * record's and its last read time 0 (C3). Then, in the workload's order:
 *
 *   t      a user transaction: transactionBegin, its time against the
 *          record at the position Run printed for it; then the internal
 *          transactions that follow it in the stream (reclaim's steps and
 *          table), each at the clock as it is;
 *   now    currentTime(), against Run's "now time=T";
 *   setsd  when the next record holds /#i/-dummy: the dummy transaction,
 *          and the internal ones after it;
 *   setretain, setfraction
 *          when the next record holds reclaim's settings
 *          (/#i/dreclaim/-settings.txt, 015-87): the setter's internal
 *          transaction. The header's set retain and set fraction are
 *          applied once, after the creation (022-01, D3): the settings'
 *          records right after the creation's are met there.
 *
 * Every record of the stream must be met, in order. A stream that reclaim
 * cut at the front is skipped (its first records are gone), as is a
 * workload with a refused transaction.
 *
 * Usage: bergdb-clockcheck WORKLOAD DIR RUN.txt
 * Prints "clockcheck DIR records=R times=T nows=N equal", or the first
 * difference. Exit status 0 equal, 1 a difference, 2 bad usage, 3 skipped.
 */
#include <inttypes.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "bergdb.h"
#include "clock.h"
#include "keys.h"
#include "mem.h"
#include "nstream.h"
#include "snode.h"
#include "stream.h"
#include "strans.h"

#define MAX_ITEMS 2000000

struct rec {
    int64_t tpos;
    int64_t tt;
    bool dummy;
    bool settings;      /* a setter's record of reclaim's settings (015-87) */
};

static struct rec recs[MAX_ITEMS];
static int64_t user_tpos[MAX_ITEMS];
static int64_t user_tt[MAX_ITEMS];
static int64_t now_time[MAX_ITEMS];
static int32_t nrecs, nusers, nnows;
static int32_t k, ui, ni;           /* the next record, user transaction and now */
static int64_t times, nows;
static struct bergdb_test_clock clk;
static struct dbclock dbc;
static const char *dir;
static struct mem mem;
static struct err err;

/* A record of one value, of the key ikey: setStartupDistance's dummy
 * transaction (/#i/-dummy), or a setter's of reclaim's settings. Reclaim's
 * steps rewrite these values too, among others, with their row. */
static bool has_only(const struct st_record *r, const char *ikey) {
    uint8_t bkey[64];
    int64_t seg[8];
    const int32_t n = (int32_t) strlen(ikey);
    keys_ikey_to_bkey((const uint8_t *) ikey, n, bkey);
    const int32_t ns = keys_segment_count(n);
    keys_to_segments(bkey, n, seg);
    int32_t values = 0;
    for (int32_t i = 0; i < r->nnodes; i++) {
        values += r->nodes[i].type == NODE_VALUE || r->nodes[i].type == NODE_DELETE;
    }
    if (values != 1) {
        return false;
    }
    for (int32_t i = 0; i < r->nnodes; i++) {
        const struct sn_node *x = &r->nodes[i];
        if (x->type != NODE_VALUE || x->key_n != ns) {
            continue;
        }
        bool same = true;
        for (int32_t j = 0; j < ns && same; j++) {
            same = sn_seg(x, j) == seg[j];
        }
        if (same) {
            return true;
        }
    }
    return false;
}

static int differ(const char *what, int64_t c, int64_t java) {
    printf("clockcheck %s DIFFERENCE %s: C %" PRId64 ", Java %" PRId64 "\n", dir, what, c, java);
    return 1;
}

/* One transaction through DbClock, a user transaction or an internal one
 * (015-55): its time against record k's. */
static int transaction(const char *what, bool user) {
    int64_t t;
    if (k >= nrecs) {
        printf("clockcheck %s DIFFERENCE %s: no record left\n", dir, what);
        return 1;
    }
    if (dbclock_transaction_begin(&dbc, user, &t, &err) != ERR_OK) {
        printf("clockcheck %s DIFFERENCE %s refused: %s\n", dir, what, err.text);
        return 1;
    }
    dbclock_transaction_end(&dbc);
    if (t != recs[k].tt) {
        char w[160];
        snprintf(w, sizeof w, "%s, the time of the record at %" PRId64, what, recs[k].tpos);
        return differ(w, t, recs[k].tt);
    }
    k++;
    times++;
    return 0;
}

/* The internal transactions that follow: records that are neither the
 * next user transaction's nor a dummy nor a setter's. */
static int internal_after(void) {
    while (k < nrecs && !(ui < nusers && recs[k].tpos == user_tpos[ui]) && !recs[k].dummy
            && !recs[k].settings) {
        if (transaction("an internal transaction", false) != 0) {
            return 1;
        }
    }
    return 0;
}

/* The settings' records that follow: a setter's internal transaction each. */
static int settings_after(const char *what) {
    while (k < nrecs && recs[k].settings) {
        if (transaction(what, false) != 0) {
            return 1;
        }
    }
    return 0;
}

static int start(void) {
    if (k == 0) {
        dbclock_init(&dbc, bergdb_test_clock_time, &clk);
        int status = transaction("the creation", true);
        return status != 0 ? status : settings_after("the header's settings");
    }
    dbclock_init(&dbc, bergdb_test_clock_time, &clk);
    dbclock_set_last_trans_time(&dbc, recs[k - 1].tt);
    return 0;
}

static bool read_stream(void) {
    struct stream s;
    struct ns_iter it;
    struct st_record r;
    bool has;
    enum err_code rc;
    if (stream_open_dir(&s, dir, &mem, &err) != ERR_OK) {
        printf("clockcheck %s error: %s\n", dir, err.text);
        return false;
    }
    st_init(&r);
    ns_iter_init(&it, &s, &mem, stream_first_pos(&s), false);
    while ((rc = ns_iter_next(&it, &has, &err)) == ERR_OK && has && nrecs < MAX_ITEMS) {
        if (st_parse(&r, it.tpos, it.buf.p, it.size, &mem, &err) != ERR_OK) {
            rc = err.code;
            break;
        }
        recs[nrecs].tpos = r.tpos;
        recs[nrecs].tt = r.tt;
        recs[nrecs].dummy = has_only(&r, "/#i/-dummy");
        recs[nrecs].settings = has_only(&r, "/#i/dreclaim/-settings.txt");
        nrecs++;
    }
    bool ok = rc == ERR_OK && stream_first_pos(&s) == 0;
    if (rc != ERR_OK) {
        printf("clockcheck %s error: the walk: %s\n", dir, err.text);
    }
    ns_iter_free(&it);
    st_free(&r, &mem);
    stream_close(&s);
    return ok;
}

/* The first two words of a workload line; false for a blank or comment line. */
static bool words(char *line, char **w1, char **w2) {
    *w1 = strtok(line, " \t\r\n");
    *w2 = *w1 == NULL ? NULL : strtok(NULL, " \t\r\n");
    if (*w2 != NULL && (*w2)[0] == '#') {
        *w2 = NULL;
    }
    return *w1 != NULL && (*w1)[0] != '#';
}

/* Reads a line into buf, the rest of a longer one dropped. */
static bool read_line(FILE *f, char *buf, int size) {
    if (fgets(buf, size, f) == NULL) {
        return false;
    }
    size_t n = strlen(buf);
    if (n > 0 && buf[n - 1] != '\n') {
        int c;
        while ((c = fgetc(f)) != EOF && c != '\n') {
        }
    }
    return true;
}

int main(int argc, char **argv) {
    static char line[8192];
    if (argc != 4) {
        fprintf(stderr, "Usage: bergdb-clockcheck WORKLOAD DIR RUN.txt\n");
        return 2;
    }
    dir = argv[2];
    mem_init(&mem);
    err_clear(&err);

    FILE *run = fopen(argv[3], "r");
    if (run == NULL) {
        fprintf(stderr, "bergdb-clockcheck: cannot read %s\n", argv[3]);
        return 2;
    }
    while (read_line(run, line, sizeof line)) {
        long long i, tt, tpos, t;
        if (sscanf(line, "trans i=%lld tt=%lld tpos=%lld", &i, &tt, &tpos) == 3
                && nusers < MAX_ITEMS) {
            user_tt[nusers] = tt;
            user_tpos[nusers++] = tpos;
        } else if (sscanf(line, "now time=%lld", &t) == 1 && nnows < MAX_ITEMS) {
            now_time[nnows++] = t;
        } else if (strncmp(line, "refused", 7) == 0 || strncmp(line, "start error", 11) == 0) {
            fclose(run);
            printf("clockcheck %s skipped: a refusal in the run\n", dir);
            return 3;
        }
    }
    fclose(run);
    if (!read_stream()) {
        if (mem.live_total == 0 && nrecs > 0) {
            printf("clockcheck %s skipped: the stream does not begin at 0 (a cut)\n", dir);
            return 3;
        }
        return 1;
    }

    FILE *wl = fopen(argv[1], "r");
    if (wl == NULL) {
        fprintf(stderr, "bergdb-clockcheck: cannot read %s\n", argv[1]);
        return 2;
    }
    int status = 0;
    bool started = false;
    bool header = false;
    while (status == 0 && read_line(wl, line, sizeof line)) {
        char *w1, *w2;
        if (!words(line, &w1, &w2)) {
            continue;
        }
        if (!header) {
            header = true;      /* bergdb-workload 1 */
            continue;
        }
        if (strcmp(w1, "restart") == 0) {
            if (!started) {
                status = start();       /* an empty segment: a start and a close */
            }
            started = false;
            continue;
        }
        if (strcmp(w1, "clock") == 0) {
            clk.time = strtoll(w2, NULL, 10);
            continue;
        }
        if (strcmp(w1, "set") == 0) {
            continue;
        }
        if (!started) {
            status = start();
            started = true;
            if (status != 0) {
                break;
            }
        }
        if (strcmp(w1, "t") == 0) {
            if (w2 != NULL && strcmp(w2, "-") != 0) {
                clk.time = strtoll(w2, NULL, 10);
            }
            if (ui >= nusers || k >= nrecs || recs[k].tpos != user_tpos[ui]) {
                printf("clockcheck %s DIFFERENCE transaction %d: not the next record (%" PRId64
                        ")\n", dir, (int) ui, k < nrecs ? recs[k].tpos : -1);
                status = 1;
                break;
            }
            status = transaction("a transaction", true);
            if (status == 0 && recs[k - 1].tt != user_tt[ui]) {
                status = differ("Run's time", recs[k - 1].tt, user_tt[ui]);
            }
            ui++;
            if (status == 0) {
                status = internal_after();
            }
        } else if (strcmp(w1, "now") == 0) {
            int64_t t = dbclock_current_time(&dbc);
            if (ni >= nnows) {
                printf("clockcheck %s DIFFERENCE a now that Run did not print\n", dir);
                status = 1;
            } else if (t != now_time[ni]) {
                status = differ("currentTime", t, now_time[ni]);
            }
            ni++;
            nows++;
        } else if (strcmp(w1, "setsd") == 0) {
            if (k < nrecs && recs[k].dummy) {
                status = transaction("setStartupDistance's dummy", true);
                if (status == 0) {
                    status = internal_after();
                }
            }
        } else if (strcmp(w1, "setretain") == 0 || strcmp(w1, "setfraction") == 0) {
            status = settings_after("a setter's settings");
        }
    }
    fclose(wl);
    if (status == 0 && !started) {
        status = start();
    }
    if (status == 0 && (k != nrecs || ui != nusers || ni != nnows)) {
        printf("clockcheck %s DIFFERENCE records met %d of %d, transactions %d of %d, nows %d "
                "of %d\n", dir, (int) k, (int) nrecs, (int) ui, (int) nusers, (int) ni,
                (int) nnows);
        status = 1;
    }
    if (status == 0) {
        printf("clockcheck %s records=%d times=%" PRId64 " nows=%" PRId64 " equal\n", dir,
                (int) nrecs, times, nows);
    }
    return status;
}
