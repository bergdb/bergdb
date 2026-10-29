/*
 * bergdb-allocfail: allocation failures in turn (bergdb 012-14, done item 7;
 * 012-01, 4.5, point 7). tools/run.c's runner (Java's Run) runs a workload
 * on a directory once as it is (the reference), then once for each
 * allocation number N = 1, 2, 3, ..., each run in a child process of its
 * own, with the database's allocator (bergdb_options.mem, the counts of
 * every database of the run, restarts included) set to fail allocation
 * number N, until a run makes fewer than N allocations. In each run:
 *
 *   - the call whose allocation failed gives BERGDB_NOMEM (a refusal) or
 *     BERGDB_FAILED (the database has failed, P7); no other code;
 *   - after a refusal the database is as it was: the call is made again
 *     (the one failure has passed), and the run goes on to the reference's
 *     text and the reference's files, byte for byte;
 *   - after a failure every later call of that database fails, the run goes
 *     on through its restarts, and at its end the directory opens again
 *     (with no failure: the start rebuilds the database from the stream, as
 *     after a crash), and its stream is a prefix of the reference's;
 *   - a refused open leaves nothing: the allocator's live bytes are 0; and
 *     after every close they are 0 too (the test build: under the
 *     sanitizers and the allocator's checks of each free).
 *
 * The calls are run.c's, renamed by the build to the wrappers below
 * (af_NAME for bergdb_NAME), which make a refused call again. A getMany's
 * pairs reach run.c's stop function only when the call succeeds: the
 * wrapper collects them and passes them on after (run.c's function always
 * goes on, BERGDB_CONTINUE, which the wrapper answers in its place).
 *
 * Usage: bergdb-allocfail [-budget N] [-from N] [-to N] WORKLOAD OUT
 *   -budget N  run's -budget (eviction under the failures)
 *   -from, -to the allocation numbers (1 to the run's allocations)
 * OUT is made: OUT/ref (the reference's directory), OUT/ref.txt, and per run
 * OUT/run, OUT/run.txt (removed after a run that passes). Prints
 * "allocfail runs=R refused=F failed=D first=CALL:N... " and ALLOCFAIL OK or
 * ALLOCFAIL FAILED (exit 1) with the runs that failed a check.
 */
#define _DARWIN_C_SOURCE
#include <dirent.h>
#include <errno.h>
#include <inttypes.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#include <sys/wait.h>
#include <unistd.h>
#include "bergdb.h"

int run_main(int argc, char **argv);

/* The reference run's exit status (0, or 1 for a workload with refused
 * lines), which every run that has not failed its database must give too. */
static int ref_status;

/* The run's state, in the child. */
static struct {
    struct bergdb_mem mem;
    struct bergdb_options opt;      /* the last open's options, for the reopen */
    bool have_opt;
    const char *dir;                /* the run's directory */
    const char *ref;                /* the reference's */
    bool prefix_checked;
    const char *hit;                /* the call whose allocation failed */
    int hit_rc;
    int checks_failed;
    char why[512];
} AF;

static void bad(const char *fmt, const char *a, long long b) {
    AF.checks_failed++;
    if (AF.why[0] == '\0') {
        snprintf(AF.why, sizeof AF.why, fmt, a, b);
    }
}

/* A call's result: a NOMEM refusal is noted and the caller makes the call
 * again; a FAILED is noted once, as the failure's. */
static bool note(const char *call, int rc) {
    if (rc == BERGDB_NOMEM || rc == BERGDB_FAILED) {
        if (AF.hit == NULL) {
            AF.hit = call;
            AF.hit_rc = rc;
        } else if (rc == BERGDB_NOMEM) {
            bad("a second NOMEM, from %s (the allocation number fails once) %lld", call, 0);
        }
    }
    return rc == BERGDB_NOMEM;
}

static void check_prefix(void);

int af_open(const char *dir, const struct bergdb_options *opt, bergdb_db **db,
        struct bergdb_start_info *info, char *errbuf) {
    struct bergdb_options o = *opt;
    AF.dir = dir;
    o.mem = &AF.mem;
    AF.opt = o;
    AF.have_opt = true;
    int rc = bergdb_open(dir, &o, db, info, errbuf);
    if (note("open", rc)) {
        if (AF.mem.live_total != 0) {
            bad("a refused open left %s%lld live bytes", "", (long long) AF.mem.live_total);
        }
        rc = bergdb_open(dir, &o, db, info, errbuf);
    }
    return rc;
}

int af_close(bergdb_db *db) {
    int rc = bergdb_close(db);
    note("close", rc);
    if (AF.mem.live_total != 0) {
        bad("%s%lld live bytes after a close", "", (long long) AF.mem.live_total);
    }
    if (AF.hit_rc == BERGDB_FAILED && !AF.prefix_checked) {
        /* The failed database, closed: its stream holds the records before the
         * failure, a prefix of the reference's (from the later of the two first
         * positions, as reclaim cuts at its own moments). */
        AF.prefix_checked = true;
        check_prefix();
    }
    return rc;
}

#define AGAIN(name, call) \
    int rc = call; \
    if (note(name, rc)) { \
        rc = call; \
    } \
    return rc

int af_trans_new(bergdb_db *db, bergdb_trans **t) {
    AGAIN("trans_new", bergdb_trans_new(db, t));
}

int af_trans_put(bergdb_trans *t, const uint8_t *key, size_t key_len, const uint8_t *value,
        size_t value_len) {
    AGAIN("trans_put", bergdb_trans_put(t, key, key_len, value, value_len));
}

int af_trans_delete(bergdb_trans *t, const uint8_t *key, size_t key_len) {
    AGAIN("trans_delete", bergdb_trans_delete(t, key, key_len));
}

int af_execute(bergdb_db *db, bergdb_trans *t, struct bergdb_executed *out) {
    AGAIN("execute", bergdb_execute(db, t, out));
}

int af_read_new(bergdb_db *db, bergdb_read **rd) {
    AGAIN("read_new", bergdb_read_new(db, rd));
}

int af_get_one(bergdb_db *db, bergdb_read *rd, int64_t lookup_time, const uint8_t *key,
        size_t key_len, struct bergdb_one *out) {
    AGAIN("get_one", bergdb_get_one(db, rd, lookup_time, key, key_len, out));
}

int af_sync(bergdb_db *db, int64_t pos, int level) {
    AGAIN("sync", bergdb_sync(db, pos, level));
}

int af_current_time(bergdb_db *db, int64_t *time) {
    AGAIN("current_time", bergdb_current_time(db, time));
}

int af_set_startup_distance(bergdb_db *db, int32_t distance) {
    AGAIN("set_startup_distance", bergdb_set_startup_distance(db, distance));
}

int af_set_cache_size_indicator(bergdb_db *db, int64_t size) {
    AGAIN("set_cache_size_indicator", bergdb_set_cache_size_indicator(db, size));
}

int af_set_retain_duration(bergdb_db *db, int64_t duration) {
    AGAIN("set_retain_duration", bergdb_set_retain_duration(db, duration));
}

int af_set_reclaim_internal_fraction(bergdb_db *db, double fraction) {
    AGAIN("set_reclaim_internal_fraction", bergdb_set_reclaim_internal_fraction(db, fraction));
}

/* getMany: the pairs collected, and passed on after a success. */
struct pairs {
    struct bergdb_kvt *kvt;
    size_t n, cap;
};

static uint8_t *dup_bytes(const uint8_t *p, size_t n) {
    if (p == NULL) {
        return NULL;
    }
    uint8_t *q = malloc(n == 0 ? 1 : n);
    if (q == NULL) {
        fprintf(stderr, "allocfail: out of memory\n");
        exit(2);
    }
    memcpy(q, p, n);
    return q;
}

static int collect(void *ctx, const struct bergdb_kvt *kvt) {
    struct pairs *p = ctx;
    if (p->n == p->cap) {
        p->cap = p->cap == 0 ? 64 : 2 * p->cap;
        struct bergdb_kvt *k2 = realloc(p->kvt, p->cap * sizeof *k2);
        if (k2 == NULL) {
            fprintf(stderr, "allocfail: out of memory\n");
            exit(2);
        }
        p->kvt = k2;
    }
    struct bergdb_kvt *x = &p->kvt[p->n++];
    *x = *kvt;
    x->key = dup_bytes(kvt->key, kvt->key_len);
    x->value = dup_bytes(kvt->value, kvt->value_len);
    return BERGDB_CONTINUE;
}

static void free_pairs(struct pairs *p) {
    for (size_t i = 0; i < p->n; i++) {
        free((void *) p->kvt[i].key);
        free((void *) p->kvt[i].value);
    }
    free(p->kvt);
    memset(p, 0, sizeof *p);
}

int af_get_many(bergdb_db *db, bergdb_read *rd, const struct bergdb_range *range,
        struct bergdb_many *out) {
    if (range == NULL || range->stop == NULL) {
        AGAIN("get_many", bergdb_get_many(db, rd, range, out));
    }
    struct bergdb_range r = *range;
    struct pairs p = {0};
    r.stop = collect;
    r.stop_ctx = &p;
    int rc = bergdb_get_many(db, rd, &r, out);
    if (note("get_many", rc)) {
        free_pairs(&p);
        rc = bergdb_get_many(db, rd, &r, out);
    }
    if (rc == BERGDB_OK) {
        for (size_t i = 0; i < p.n; i++) {
            if (range->stop(range->stop_ctx, &p.kvt[i]) != BERGDB_CONTINUE) {
                bad("run.c's stop function did not go on%s %lld", "", 0);
            }
        }
    }
    free_pairs(&p);
    return rc;
}

/* ======== Files ======== */

static uint8_t *read_file(const char *path, size_t *n) {
    FILE *f = fopen(path, "rb");
    if (f == NULL) {
        return NULL;
    }
    size_t cap = 65536, len = 0;
    uint8_t *b = malloc(cap);
    size_t k;
    while (b != NULL && (k = fread(b + len, 1, cap - len, f)) > 0) {
        len += k;
        if (len == cap) {
            cap *= 2;
            uint8_t *b2 = realloc(b, cap);
            if (b2 == NULL) {
                free(b);
                b = NULL;
            }
            b = b2;
        }
    }
    fclose(f);
    *n = len;
    return b;
}

static int cmp_names(const void *a, const void *b) {
    return strcmp(*(char *const *) a, *(char *const *) b);
}

/* The names in dir, sorted; n of them. */
static char **names_of(const char *dir, int *n) {
    DIR *d = opendir(dir);
    char **names = NULL;
    int count = 0, cap = 0;
    struct dirent *e;
    *n = 0;
    if (d == NULL) {
        return NULL;
    }
    while ((e = readdir(d)) != NULL) {
        if (e->d_name[0] == '.') {
            continue;
        }
        if (count == cap) {
            cap = cap == 0 ? 16 : 2 * cap;
            char **n2 = realloc(names, (size_t) cap * sizeof *n2);
            if (n2 == NULL) {
                exit(2);
            }
            names = n2;
        }
        names[count++] = strdup(e->d_name);
    }
    closedir(d);
    qsort(names, (size_t) count, sizeof *names, cmp_names);
    *n = count;
    return names;
}

static void free_names(char **names, int n) {
    for (int i = 0; i < n; i++) {
        free(names[i]);
    }
    free(names);
}

/* The same names and bytes in both directories. */
static bool same_dir(const char *a, const char *b) {
    int na, nb;
    char **xa = names_of(a, &na), **xb = names_of(b, &nb);
    bool same = na == nb;
    for (int i = 0; same && i < na; i++) {
        char pa[4096], pb[4096];
        size_t la = 0, lb = 0;
        same = strcmp(xa[i], xb[i]) == 0;
        snprintf(pa, sizeof pa, "%s/%s", a, xa[i]);
        snprintf(pb, sizeof pb, "%s/%s", b, xb[i]);
        uint8_t *ba = same ? read_file(pa, &la) : NULL, *bb = same ? read_file(pb, &lb) : NULL;
        same = same && ba != NULL && bb != NULL && la == lb && memcmp(ba, bb, la) == 0;
        free(ba);
        free(bb);
    }
    free_names(xa, na);
    free_names(xb, nb);
    return same;
}

/* The stream of dir: the bytes of its .bergdb files from the first, as far
 * as they are contiguous; *first its first position. */
static uint8_t *stream_at(const char *dir, int64_t *first, size_t *len) {
    int n;
    char **names = names_of(dir, &n);
    uint8_t *s = NULL;
    *len = 0;
    *first = -1;
    for (int i = 0; i < n; i++) {
        size_t l = strlen(names[i]);
        if (l != 21 || strcmp(names[i] + 14, ".bergdb") != 0) {
            continue;
        }
        char p[4096];
        size_t fl = 0;
        snprintf(p, sizeof p, "%s/%s", dir, names[i]);
        int64_t start = strtoll(names[i], NULL, 10) * 100000;
        if (*first < 0) {
            *first = start;
        }
        if (start != *first + (int64_t) *len) {
            break;      /* a gap */
        }
        uint8_t *f = read_file(p, &fl);
        if (f == NULL) {
            break;
        }
        uint8_t *s2 = realloc(s, *len + fl + 1);
        if (s2 == NULL) {
            exit(2);
        }
        s = s2;
        memcpy(s + *len, f, fl);
        *len += fl;
        free(f);
    }
    free_names(names, n);
    if (*first < 0) {
        *first = 0;
    }
    return s;
}

static void check_prefix(void) {
    int64_t fr, fs;
    size_t lr, ls;
    uint8_t *r = stream_at(AF.ref, &fr, &lr), *s = stream_at(AF.dir, &fs, &ls);
    int64_t from = fr > fs ? fr : fs;
    int64_t endr = fr + (int64_t) lr, ends = fs + (int64_t) ls;
    if (ends > endr) {
        bad("the failed database's stream is longer than the reference's (%s%lld bytes)", "",
                (long long) ends);
    } else if (from < ends && memcmp(r + (from - fr), s + (from - fs), (size_t) (ends - from))
            != 0) {
        bad("the failed database's stream is not a prefix of the reference's (%s%lld bytes)",
                "", (long long) ends);
    }
    free(r);
    free(s);
}

/* Removes a directory of files (a database's, a run's), or one level of
 * directories of files (OUT); without a shell, as it runs once a run. */
static void rm_rf(const char *path) {
    int n;
    char **names = names_of(path, &n);
    for (int i = 0; i < n; i++) {
        char p[4096];
        snprintf(p, sizeof p, "%s/%s", path, names[i]);
        if (unlink(p) != 0) {
            rm_rf(p);       /* a directory */
        }
    }
    free_names(names, n);
    rmdir(path);
}

/* ======== Runs ======== */

/* The child's run: allocation number at (0: none) fails. Exit status: 0
 * no failure hit, 10 a refusal, 11 a failed database, 1 a check failed; the
 * line for the parent in result. */
static int child(int at, char **runargs, int nrunargs, const char *out, const char *dir,
        const char *text, const char *result) {
    if (freopen(text, "w", stdout) == NULL) {
        return 2;
    }
    memset(&AF, 0, sizeof AF);
    AF.mem.fail_at = at;
    char refdir[4096];
    snprintf(refdir, sizeof refdir, "%s/ref", out);
    AF.ref = refdir;
    char *args[16];
    int na = 0;
    args[na++] = "bergdb-run";
    for (int i = 0; i < nrunargs; i++) {
        args[na++] = runargs[i];
    }
    args[na++] = (char *) dir;
    args[na] = NULL;
    int status = run_main(na, args);
    fflush(stdout);
    int64_t allocs = AF.mem.allocs;
    if (at == 0) {
        return status;
    }
    if (AF.hit == NULL && AF.mem.failed > 0) {
        /* The failed allocation reached no call: the library absorbed it. */
        AF.hit = "absorbed";
        AF.hit_rc = 0;
    }
    if (at > 0) {
        char ref[4096], reftext[4096];
        snprintf(ref, sizeof ref, "%s/ref", out);
        snprintf(reftext, sizeof reftext, "%s/ref.txt", out);
        if (AF.hit == NULL || AF.hit_rc != BERGDB_FAILED) {
            if (status != ref_status) {
                bad("exit status %s%lld, not the reference's", "", status);
            }
            size_t la = 0, lb = 0;
            uint8_t *a = read_file(text, &la), *b = read_file(reftext, &lb);
            if (a == NULL || b == NULL || la != lb || memcmp(a, b, la) != 0) {
                bad("the run's text is not the reference's%s %lld", "", 0);
            }
            free(a);
            free(b);
            if (!same_dir(dir, ref)) {
                bad("the run's files are not the reference's%s %lld", "", 0);
            }
        } else {
            /* A failed database: the directory opens again, its stream a prefix of
             * the reference's (from 0). */
            if (!AF.have_opt) {
                bad("FAILED without an open%s %lld", "", 0);
            } else {
                bergdb_db *db;
                char errbuf[BERGDB_ERRBUF_SIZE];
                AF.mem.fail_at = 0;
                int rc = bergdb_open(dir, &AF.opt, &db, NULL, errbuf);
                if (rc != BERGDB_OK) {
                    bad("the failed database's directory does not open again: %s %lld", errbuf,
                            rc);
                } else {
                    bergdb_close(db);
                    if (AF.mem.live_total != 0) {
                        bad("%s%lld live bytes after the reopen's close", "",
                                (long long) AF.mem.live_total);
                    }
                }
            }
        }
    }
    FILE *f = fopen(result, "a");
    if (f != NULL) {
        fprintf(f, "at=%d allocs=%" PRId64 " hit=%s rc=%s status=%d checks=%s%s\n", at,
                allocs, AF.hit != NULL ? AF.hit : "-",
                AF.hit == NULL ? "-" : AF.hit_rc == BERGDB_NOMEM ? "NOMEM"
                : AF.hit_rc == BERGDB_FAILED ? "FAILED" : "none", status,
                AF.checks_failed == 0 ? "ok" : "FAILED: ", AF.why);
        fclose(f);
    }
    if (AF.checks_failed > 0) {
        return 1;
    }
    if (AF.hit == NULL) {
        return allocs < at || at == 0 ? 0 : 1;
    }
    return AF.hit_rc == BERGDB_NOMEM ? 10 : AF.hit_rc == BERGDB_FAILED ? 11 : 12;
}

static int fork_run(int at, char **runargs, int nrunargs, const char *out, const char *dir,
        const char *text, const char *result) {
    fflush(stdout);
    pid_t pid = fork();
    if (pid < 0) {
        perror("fork");
        exit(2);
    }
    if (pid == 0) {
        _exit(child(at, runargs, nrunargs, out, dir, text, result));
    }
    int st;
    if (waitpid(pid, &st, 0) < 0) {
        perror("waitpid");
        exit(2);
    }
    if (WIFSIGNALED(st)) {
        return 128 + WTERMSIG(st);
    }
    return WEXITSTATUS(st);
}

int main(int argc, char **argv) {
    char *runargs[8];
    int nr = 0;
    int from = 1, to = 1 << 30, child_at = -1;
    int i = 1;
    for (; i < argc && argv[i][0] == '-'; i++) {
        if (strcmp(argv[i], "-budget") == 0 && i + 1 < argc) {
            runargs[nr++] = argv[i++];
            runargs[nr++] = argv[i];
        } else if (strcmp(argv[i], "-from") == 0 && i + 1 < argc) {
            from = atoi(argv[++i]);
        } else if (strcmp(argv[i], "-to") == 0 && i + 1 < argc) {
            to = atoi(argv[++i]);
        } else if (strcmp(argv[i], "-child") == 0 && i + 1 < argc) {
            child_at = atoi(argv[++i]);     /* one run in this process (a debugger's) */
        } else {
            break;
        }
    }
    if (argc - i != 2) {
        fprintf(stderr, "Usage: bergdb-allocfail [-budget N] [-from N] [-to N] WORKLOAD OUT\n");
        return 2;
    }
    runargs[nr++] = argv[i];
    const char *out = argv[i + 1];
    char ref[4096], reftext[4096], dir[4096], text[4096], result[4096];
    snprintf(ref, sizeof ref, "%s/ref", out);
    snprintf(reftext, sizeof reftext, "%s/ref.txt", out);
    snprintf(dir, sizeof dir, "%s/run", out);
    snprintf(text, sizeof text, "%s/run.txt", out);
    snprintf(result, sizeof result, "%s/results.txt", out);
    if (child_at < 0) {
        rm_rf(out);
    }
    char parents[4096];
    snprintf(parents, sizeof parents, "%s", out);
    for (char *q = parents + 1; *q != '\0'; q++) {
        if (*q == '/') {
            *q = '\0';
            mkdir(parents, 0777);   /* the parents, as mkdir -p */
            *q = '/';
        }
    }
    if (child_at < 0 && mkdir(out, 0777) != 0) {
        fprintf(stderr, "allocfail: cannot make %s\n", out);
        return 2;
    }
    if (child_at >= 0) {
        /* OUT/ref and OUT/ref.txt from an earlier run; the run in OUT/run. */
        rm_rf(dir);
        return child(child_at, runargs, nr, out, dir, text, result);
    }
    int st = fork_run(0, runargs, nr, out, ref, reftext, result);
    if (st != 0 && st != 1) {
        printf("ALLOCFAIL FAILED: the reference run, status %d\n", st);
        return 1;
    }
    ref_status = st;
    int64_t runs = 0, refused = 0, failed = 0, absorbed = 0, bad_runs = 0;
    int at = from;
    for (; at <= to; at++) {
        rm_rf(dir);
        st = fork_run(at, runargs, nr, out, dir, text, result);
        runs++;
        if (st == 0) {
            break;      /* fewer allocations than at: every number has failed once */
        }
        if (st == 10) {
            refused++;
        } else if (st == 11) {
            failed++;
        } else if (st == 12) {
            absorbed++;
        } else {
            bad_runs++;
            if (bad_runs <= 10) {
                printf("allocfail: run at=%d: status %d (see %s)\n", at, st, result);
            }
            char keep[4200];
            snprintf(keep, sizeof keep, "%s/failed-%d", out, at);
            rename(dir, keep);
        }
    }
    rm_rf(dir);
    remove(text);
    printf("allocfail runs=%" PRId64 " refused=%" PRId64 " failed=%" PRId64 " absorbed=%"
            PRId64 " bad=%" PRId64 " allocations=%d\n", runs, refused, failed, absorbed,
            bad_runs, at - 1);
    if (bad_runs > 0) {
        printf("ALLOCFAIL FAILED: %" PRId64 " runs failed a check (%s)\n", bad_runs, result);
        return 1;
    }
    printf("ALLOCFAIL OK: %" PRId64 " runs, each allocation number failed once: %" PRId64
            " refused (NOMEM, then the same text and bytes), %" PRId64 " failed databases"
            " (P7, opened again), %" PRId64 " absorbed (no call failed; the same text and"
            " bytes), the allocator's count 0 after every close\n", runs, refused, failed,
            absorbed);
    return 0;
}
