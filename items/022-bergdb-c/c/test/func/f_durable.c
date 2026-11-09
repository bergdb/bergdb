/* Functional tests of durability (bergdb 012-13): what a restart finds after
 * a process is killed (SIGKILL, kill -9) after execute, after sync and while
 * a record is being written; a second process's open (BERGDB_IN_USE); a
 * write that fails (the file size limit), which fails the database (P7).
 * C alone, through include/bergdb.h only; power loss is 012-14's. The
 * killed processes are this program itself, run as a child with the
 * arguments "--child MODE ..." (durable_child), its standard output a pipe
 * to the test.
 *
 * The rules they check are the C directory's readme.md, section 9: a
 * committed transaction is in the write buffer (10 MB) until bergdb_sync,
 * bergdb_close or a full buffer writes it; a process that dies loses what
 * the buffer holds, never what was written; what was synced survives; a
 * start finds whole transactions only, a prefix of those committed: every
 * synced one, and no later one without the ones before it. */
#include <dirent.h>
#include <signal.h>
#include <spawn.h>
#include <stdlib.h>
#include <sys/resource.h>
#include <sys/stat.h>
#include <sys/time.h>
#include <sys/wait.h>
#include <unistd.h>
#include "test.h"
#include "bergdb.h"

extern char **environ;
extern const char *func_program;    /* f_api.c's main: argv[0] */

#define DU_BASE_TIME INT64_C(1000000)
#define DU_NO_KILL (-1)

static void du_temp_dir(char *out, size_t cap) {
    const char *t = getenv("TMPDIR");
    snprintf(out, cap, "%s/bergdb-func-XXXXXX", t != NULL ? t : "/tmp");
    if (mkdtemp(out) == NULL) {
        out[0] = '\0';
    }
}

static void du_remove_dir(const char *dir) {
    char cmd[1200];
    snprintf(cmd, sizeof cmd, "rm -rf '%s'", dir);
    if (system(cmd) != 0) {
        printf("could not remove %s\n", dir);
    }
}

static int64_t du_file_size(const char *dir, const char *name) {
    char path[1200];
    struct stat st;
    snprintf(path, sizeof path, "%s/%s", dir, name);
    return stat(path, &st) == 0 ? (int64_t) st.st_size : -1;
}

/* The bytes of the directory's .bergdb files. */
static int64_t du_stream_bytes(const char *dir) {
    DIR *d = opendir(dir);
    int64_t sum = 0;
    if (d == NULL) {
        return -1;
    }
    for (struct dirent *e = readdir(d); e != NULL; e = readdir(d)) {
        size_t len = strlen(e->d_name);
        if (len > 7 && strcmp(e->d_name + len - 7, ".bergdb") == 0) {
            sum += du_file_size(dir, e->d_name);
        }
    }
    closedir(d);
    return sum;
}

/* The options of both sides: the test clock and id, node size 8. */
static void du_options(struct bergdb_options *o, struct bergdb_test_clock *clock,
        struct bergdb_mem *m) {
    bergdb_options_init(o);
    o->clock = bergdb_test_clock_time;
    o->clock_ctx = clock;
    memcpy(o->id, bergdb_test_id, BERGDB_ID_SIZE);
    o->max_node_size = 8;
    o->startup_distance = 100000;
    o->mem = m;
}

static void du_key(const char *ikey, uint8_t *buf, size_t *len) {
    *len = strlen(ikey);
    bergdb_ikey_to_bkey((const uint8_t *) ikey, *len, buf);
}

/* Transaction i's value of /k/i: size bytes from i. */
static void du_value(int64_t i, size_t size, uint8_t *v) {
    for (size_t j = 0; j < size; j++) {
        v[j] = (uint8_t) (i * 131 + (int64_t) (j / 7));
    }
}

/* Transaction i: /k/i is du_value(i, size), /n is i as text; at time
 * DU_BASE_TIME + 1000 i. */
static int du_trans(bergdb_db *db, struct bergdb_test_clock *clock, int64_t i, size_t size,
        uint8_t *v, struct bergdb_executed *ex) {
    bergdb_trans *t;
    char ikey[32], n[32];
    uint8_t b[32];
    size_t kl;
    bergdb_test_clock_set(clock, DU_BASE_TIME + 1000 * i);
    int rc = bergdb_trans_new(db, &t);
    if (rc != BERGDB_OK) {
        return rc;
    }
    snprintf(ikey, sizeof ikey, "/k/%lld", (long long) i);
    du_key(ikey, b, &kl);
    du_value(i, size, v);
    rc = bergdb_trans_put(t, b, kl, v, size);
    snprintf(n, sizeof n, "%lld", (long long) i);
    du_key("/n", b, &kl);
    if (rc == BERGDB_OK) {
        rc = bergdb_trans_put(t, b, kl, (const uint8_t *) n, strlen(n));
    }
    if (rc == BERGDB_OK) {
        rc = bergdb_execute(db, t, ex);
    }
    bergdb_trans_free(t);
    return rc;
}

/* ======== The child ======== */

/* exec DIR COUNT SIZE SYNC_EVERY KILL_AT: transactions 0 to COUNT - 1
 * (COUNT 0: until killed) with values of SIZE bytes; a sync after every
 * SYNC_EVERY-th (0: none), then "synced I LENGTH"; after transaction
 * KILL_AT (and its sync, if it has one) "killed I", then SIGKILL. */
static int child_exec(char **argv) {
    const char *dir = argv[0];
    const int64_t count = atoll(argv[1]);
    const size_t size = (size_t) atoll(argv[2]);
    const int64_t sync_every = atoll(argv[3]);
    const int64_t kill_at = atoll(argv[4]);
    struct bergdb_test_clock clock = {0};
    struct bergdb_options o;
    struct bergdb_mem m = {0};
    bergdb_db *db;
    char errbuf[BERGDB_ERRBUF_SIZE];
    du_options(&o, &clock, &m);
    bergdb_test_clock_set(&clock, 1000);
    if (bergdb_open(dir, &o, &db, NULL, errbuf) != BERGDB_OK) {
        printf("open %s\n", errbuf);
        return 1;
    }
    uint8_t *v = malloc(size + 1);
    for (int64_t i = 0; count == 0 || i < count; i++) {
        struct bergdb_executed ex;
        int rc = du_trans(db, &clock, i, size, v, &ex);
        if (rc != BERGDB_OK) {
            printf("execute %s\n", bergdb_errmsg(db));
            return 1;
        }
        if (sync_every > 0 && (i + 1) % sync_every == 0) {
            if (bergdb_sync(db, 0, BERGDB_SYNC_ORDINARY) != BERGDB_OK) {
                printf("sync %s\n", bergdb_errmsg(db));
                return 1;
            }
            printf("synced %lld %lld\n", (long long) i, (long long) ex.next_pos);
            fflush(stdout);
        }
        if (i == kill_at) {
            printf("killed %lld\n", (long long) i);
            fflush(stdout);
            kill(getpid(), SIGKILL);
        }
    }
    free(v);
    printf("closed %s\n", bergdb_errname(bergdb_close(db)));
    return 0;
}

/* open DIR: an open of DIR, then its code's name. */
static int child_open(char **argv) {
    struct bergdb_test_clock clock = {0};
    struct bergdb_options o;
    bergdb_db *db;
    char errbuf[BERGDB_ERRBUF_SIZE];
    du_options(&o, &clock, NULL);
    bergdb_test_clock_set(&clock, 1000);
    int rc = bergdb_open(argv[0], &o, &db, NULL, errbuf);
    printf("%s %s\n", bergdb_errname(rc), errbuf);
    bergdb_close(db);
    return 0;
}

/* The system's time in milliseconds. */
static int64_t du_millis(void) {
    struct timeval tv;
    gettimeofday(&tv, NULL);
    return (int64_t) tv.tv_sec * 1000 + tv.tv_usec / 1000;
}

/* openat DIR MILLIS: waits until the system's time is MILLIS, then as
 * open: an open of DIR, its code's name and text, and a close. Several
 * children open at once so (durable_concurrent_opens_of_a_new_directory). */
static int child_open_at(char **argv) {
    const int64_t at = atoll(argv[1]);
    while (du_millis() < at) {
        usleep(100);
    }
    return child_open(argv);
}

/* fsize DIR LIMIT: the files of this process limited to LIMIT bytes
 * (RLIMIT_FSIZE; SIGXFSZ ignored, so a write past it fails with EFBIG):
 * 10 transactions of 50,000 bytes, then a sync, which must fail, and every
 * call after it, each code printed. */
static int child_fsize(char **argv) {
    struct rlimit rl;
    rl.rlim_cur = (rlim_t) atoll(argv[1]);
    rl.rlim_max = RLIM_INFINITY;
    signal(SIGXFSZ, SIG_IGN);
    if (setrlimit(RLIMIT_FSIZE, &rl) != 0) {
        printf("setrlimit failed\n");
        return 1;
    }
    struct bergdb_test_clock clock = {0};
    struct bergdb_options o;
    struct bergdb_mem m = {0};
    bergdb_db *db;
    char errbuf[BERGDB_ERRBUF_SIZE];
    du_options(&o, &clock, &m);
    bergdb_test_clock_set(&clock, 1000);
    if (bergdb_open(argv[0], &o, &db, NULL, errbuf) != BERGDB_OK) {
        printf("open %s\n", errbuf);
        return 1;
    }
    uint8_t *v = malloc(50000);
    struct bergdb_executed ex;
    for (int64_t i = 0; i < 10; i++) {
        printf("execute %s\n", bergdb_errname(du_trans(db, &clock, i, 50000, v, &ex)));
    }
    int rc = bergdb_sync(db, 0, BERGDB_SYNC_ORDINARY);
    printf("sync %s %s\n", bergdb_errname(rc), bergdb_errmsg(db));
    printf("execute %s\n", bergdb_errname(du_trans(db, &clock, 10, 100, v, &ex)));
    bergdb_read *rd;
    struct bergdb_one one;
    uint8_t b[32];
    size_t kl;
    du_key("/n", b, &kl);
    printf("read_new %s\n", bergdb_errname(bergdb_read_new(db, &rd)));
    printf("get_one %s\n", bergdb_errname(bergdb_get_one(db, rd, BERGDB_LATEST, b, kl, &one)));
    bergdb_read_free(rd);
    struct bergdb_stats s;
    rc = bergdb_stats(db, &s);
    printf("stats %s length=%lld durable=%lld\n", bergdb_errname(rc),
            (long long) s.stream_length, (long long) s.durable_length);
    printf("sync %s\n", bergdb_errname(bergdb_sync(db, 0, BERGDB_SYNC_ORDINARY)));
    printf("set_cache_size_indicator %s\n",
            bergdb_errname(bergdb_set_cache_size_indicator(db, 1000000)));
    printf("close %s\n", bergdb_errname(bergdb_close(db)));
    printf("live %lld\n", (long long) m.live_total);
    free(v);
    return 0;
}

/* fsizebig DIR LIMIT: the files limited to LIMIT bytes, as fsize; a
 * transaction of 1,000 bytes, then one of 11 MB, more than the write
 * buffer's 10 MB, so that bergdb_execute writes the buffer, and that write
 * fails; then a transaction and the close, each code printed (bergdb
 * 022-05: DbTester.testWriterWaitingForRoomAfterFailedFlush, whose writer
 * waits for room in Java's buffer thread). */
static int child_fsize_big(char **argv) {
    struct rlimit rl;
    rl.rlim_cur = (rlim_t) atoll(argv[1]);
    rl.rlim_max = RLIM_INFINITY;
    signal(SIGXFSZ, SIG_IGN);
    if (setrlimit(RLIMIT_FSIZE, &rl) != 0) {
        printf("setrlimit failed\n");
        return 1;
    }
    struct bergdb_test_clock clock = {0};
    struct bergdb_options o;
    struct bergdb_mem m = {0};
    bergdb_db *db;
    char errbuf[BERGDB_ERRBUF_SIZE];
    du_options(&o, &clock, &m);
    bergdb_test_clock_set(&clock, 1000);
    if (bergdb_open(argv[0], &o, &db, NULL, errbuf) != BERGDB_OK) {
        printf("open %s\n", errbuf);
        return 1;
    }
    const size_t big = 11 * 1000 * 1000;
    uint8_t *v = malloc(big);
    struct bergdb_executed ex;
    printf("execute %s\n", bergdb_errname(du_trans(db, &clock, 0, 1000, v, &ex)));
    int rc = du_trans(db, &clock, 1, big, v, &ex);
    printf("execute %s %s\n", bergdb_errname(rc), bergdb_errmsg(db));
    printf("execute %s\n", bergdb_errname(du_trans(db, &clock, 2, 1000, v, &ex)));
    printf("close %s\n", bergdb_errname(bergdb_close(db)));
    printf("live %lld\n", (long long) m.live_total);
    free(v);
    return 0;
}

int durable_child(int argc, char **argv) {
    if (argc >= 8 && strcmp(argv[2], "exec") == 0) {
        return child_exec(argv + 3);
    }
    if (argc >= 4 && strcmp(argv[2], "open") == 0) {
        return child_open(argv + 3);
    }
    if (argc >= 5 && strcmp(argv[2], "openat") == 0) {
        return child_open_at(argv + 3);
    }
    if (argc >= 5 && strcmp(argv[2], "fsize") == 0) {
        return child_fsize(argv + 3);
    }
    if (argc >= 5 && strcmp(argv[2], "fsizebig") == 0) {
        return child_fsize_big(argv + 3);
    }
    fprintf(stderr, "func --child: bad arguments\n");
    return 2;
}

/* ======== The parent ======== */

/* A running child: its pid and its standard output. */
struct child {
    pid_t pid;
    FILE *out;
};

/* Starts func --child with the arguments (a NULL-terminated list after
 * "--child"); false if it could not. */
static bool child_start(struct child *c, const char *const *args) {
    char *argv[16];
    int fds[2];
    int n = 0;
    argv[n++] = (char *) func_program;
    argv[n++] = (char *) "--child";
    while (*args != NULL && n < 15) {
        argv[n++] = (char *) *args++;
    }
    argv[n] = NULL;
    if (pipe(fds) != 0) {
        return false;
    }
    posix_spawn_file_actions_t fa;
    posix_spawn_file_actions_init(&fa);
    posix_spawn_file_actions_adddup2(&fa, fds[1], 1);
    posix_spawn_file_actions_addclose(&fa, fds[0]);
    int rc = posix_spawn(&c->pid, func_program, &fa, NULL, argv, environ);
    posix_spawn_file_actions_destroy(&fa);
    close(fds[1]);
    if (rc != 0) {
        close(fds[0]);
        return false;
    }
    c->out = fdopen(fds[0], "r");
    return c->out != NULL;
}

/* Reads the child's next line into line (without its newline); false at
 * the end of its output. */
static bool child_line(struct child *c, char *line, size_t cap) {
    if (fgets(line, (int) cap, c->out) == NULL) {
        return false;
    }
    line[strcspn(line, "\n")] = '\0';
    return true;
}

/* Waits for the child; its status as waitpid gives it. */
static int child_wait(struct child *c) {
    int status = 0;
    char rest[256];
    while (child_line(c, rest, sizeof rest)) {
    }
    fclose(c->out);
    waitpid(c->pid, &status, 0);
    return status;
}

/* What a restart finds: the database opened, and n, the last transaction
 * found (-1: none), with every /k/j for j up to n as written and none after
 * it (up to limit): a prefix of the transactions, whole. The database stays
 * open in *dbp. */
static int64_t restart_finds(const char *dir, struct bergdb_test_clock *clock,
        struct bergdb_mem *m, size_t size, int64_t limit, bergdb_db **dbp,
        struct bergdb_start_info *info, bool *prefix_ok) {
    struct bergdb_options o;
    char errbuf[BERGDB_ERRBUF_SIZE];
    bergdb_db *db;
    *prefix_ok = false;
    *dbp = NULL;
    du_options(&o, clock, m);
    if (bergdb_open(dir, &o, &db, info, errbuf) != BERGDB_OK) {
        printf("  restart: %s\n", errbuf);
        return -2;
    }
    *dbp = db;
    bergdb_read *rd;
    if (bergdb_read_new(db, &rd) != BERGDB_OK) {
        return -2;
    }
    struct bergdb_one one;
    uint8_t b[32];
    size_t kl;
    int64_t n = -1;
    du_key("/n", b, &kl);
    if (bergdb_get_one(db, rd, BERGDB_LATEST, b, kl, &one) != BERGDB_OK) {
        bergdb_read_free(rd);
        return -2;
    }
    if (one.value != NULL) {
        char text[32];
        memcpy(text, one.value, one.value_len < 31 ? one.value_len : 31);
        text[one.value_len < 31 ? one.value_len : 31] = '\0';
        n = atoll(text);
    }
    bool ok = true;
    uint8_t *v = malloc(size + 1);
    for (int64_t j = 0; j <= limit && ok; j++) {
        char ikey[32];
        snprintf(ikey, sizeof ikey, "/k/%lld", (long long) j);
        du_key(ikey, b, &kl);
        if (bergdb_get_one(db, rd, BERGDB_LATEST, b, kl, &one) != BERGDB_OK) {
            ok = false;
        } else if (j <= n) {
            du_value(j, size, v);
            ok = one.value != NULL && one.value_len == size && memcmp(one.value, v, size) == 0;
        } else {
            ok = one.value == NULL;
        }
        if (!ok) {
            printf("  restart: /k/%lld wrong (n %lld)\n", (long long) j, (long long) n);
        }
    }
    free(v);
    bergdb_read_free(rd);
    ok = ok && bergdb_debug_check(db) == BERGDB_OK;
    *prefix_ok = ok;
    return n;
}

/* Runs func --child exec and waits; the last "synced" transaction in
 * *synced (-1: none) and its length in *synced_len; true if the child was
 * killed by SIGKILL. */
static bool run_exec(const char *dir, int64_t count, size_t size, int64_t sync_every,
        int64_t kill_at, int64_t *synced, int64_t *synced_len) {
    char a1[24], a2[24], a3[24], a4[24], line[256];
    snprintf(a1, sizeof a1, "%lld", (long long) count);
    snprintf(a2, sizeof a2, "%zu", size);
    snprintf(a3, sizeof a3, "%lld", (long long) sync_every);
    snprintf(a4, sizeof a4, "%lld", (long long) kill_at);
    const char *args[] = { "exec", dir, a1, a2, a3, a4, NULL };
    struct child c;
    *synced = -1;
    *synced_len = -1;
    if (!child_start(&c, args)) {
        return false;
    }
    while (child_line(&c, line, sizeof line)) {
        long long i, len;
        if (sscanf(line, "synced %lld %lld", &i, &len) == 2) {
            *synced = i;
            *synced_len = len;
        }
    }
    int status = child_wait(&c);
    return WIFSIGNALED(status) && WTERMSIG(status) == SIGKILL;
}

/* A restart after a kill: open, check the prefix, one more transaction, a
 * close and an open again; the count 0. Returns the n found. */
static int64_t restart_and_go_on(const char *dir, size_t size, int64_t limit,
        struct bergdb_start_info *info, bool *ok) {
    struct bergdb_mem m = {0};
    struct bergdb_test_clock clock = {0};
    bergdb_db *db;
    bergdb_test_clock_set(&clock, DU_BASE_TIME + 1000 * (limit + 10));
    int64_t n = restart_finds(dir, &clock, &m, size, limit, &db, info, ok);
    if (db != NULL) {
        uint8_t *v = malloc(size + 1);
        struct bergdb_executed ex;
        bool more = du_trans(db, &clock, n + 1, size, v, &ex) == BERGDB_OK
                && bergdb_close(db) == BERGDB_OK;
        free(v);
        bool again;
        clock.time += 1000000;
        if (more && restart_finds(dir, &clock, &m, size, limit, &db, NULL, &again) != n + 1) {
            again = false;
        }
        *ok = *ok && more && again && bergdb_close(db) == BERGDB_OK && m.live_total == 0;
    }
    return n;
}

/* Killed after execute, after sync, and with a record partly written. */
TEST(durable_kill_after_execute_and_sync) {
    char dir[1024];
    struct bergdb_start_info info;
    int64_t synced, synced_len, n;
    bool ok;
    REQUIRE(func_program != NULL);

    /* 1. Transactions 0 to 9, a sync after 9, then 10 to 14, killed after
     * 14's execute: 0 to 9 found, nothing after them, and the stream ends
     * where the sync left it (the rest was in the write buffer). */
    du_temp_dir(dir, sizeof dir);
    REQUIRE(dir[0] != '\0');
    CHECK(run_exec(dir, 15, 1000, 10, 14, &synced, &synced_len));
    CHECK_EQ(synced, 9);
    CHECK_EQ(du_stream_bytes(dir), synced_len);
    n = restart_and_go_on(dir, 1000, 20, &info, &ok);
    CHECK(ok);
    CHECK_EQ(n, 9);
    CHECK_EQ(info.last_pos + 1, synced_len);
    du_remove_dir(dir);

    /* 2. A sync after every transaction, killed right after 14's sync: 0 to
     * 14 found. */
    du_temp_dir(dir, sizeof dir);
    REQUIRE(dir[0] != '\0');
    CHECK(run_exec(dir, 30, 1000, 1, 14, &synced, &synced_len));
    CHECK_EQ(synced, 14);
    n = restart_and_go_on(dir, 1000, 20, &info, &ok);
    CHECK(ok);
    CHECK_EQ(n, 14);
    CHECK_EQ(info.last_pos + 1, synced_len);
    du_remove_dir(dir);

    /* 3. Killed after the creation and 5 transactions, with no sync: the
     * files hold nothing (the creation too was in the buffer), and the
     * restart creates the database again, empty. */
    du_temp_dir(dir, sizeof dir);
    REQUIRE(dir[0] != '\0');
    CHECK(run_exec(dir, 10, 1000, 0, 4, &synced, &synced_len));
    CHECK_EQ(synced, -1);
    CHECK_EQ(du_stream_bytes(dir), 0);
    n = restart_and_go_on(dir, 1000, 20, &info, &ok);
    CHECK(ok);
    CHECK_EQ(n, -1);
    CHECK_EQ(info.trans_count, 1);      /* the primordial transaction, made again */
    du_remove_dir(dir);

    /* 4. Values of 1 MB, no sync, killed after transaction 12: the 10 MB
     * write buffer filled during transaction 9's record and was written
     * then, so the file ends inside that record, which the restart cuts
     * off (its zero fill); 0 to 8 found. */
    du_temp_dir(dir, sizeof dir);
    REQUIRE(dir[0] != '\0');
    CHECK(run_exec(dir, 20, 1000000, 0, 12, &synced, &synced_len));
    CHECK_EQ(du_stream_bytes(dir), 10000000);    /* the buffer, written once */
    n = restart_and_go_on(dir, 1000000, 20, &info, &ok);
    CHECK(ok);
    CHECK_EQ(n, 8);
    du_remove_dir(dir);
}

/* Killed at random moments while transactions of 1 MB are committed and
 * synced every 12 (so that the 10 MB buffer is written in the middle of a
 * record between syncs): each restart finds a prefix of the transactions,
 * whole, with every synced one. BERGDB_DURABLE_ROUNDS rounds (6 by
 * default). */
TEST(durable_kill_at_random) {
    const char *r = getenv("BERGDB_DURABLE_ROUNDS");
    const int rounds = r != NULL ? atoi(r) : 6;
    uint64_t rnd = 20261029;
    int torn = 0, unsynced_found = 0;
    REQUIRE(func_program != NULL);
    for (int round = 0; round < rounds; round++) {
        char dir[1024], line[256];
        du_temp_dir(dir, sizeof dir);
        REQUIRE(dir[0] != '\0');
        const char *args[] = { "exec", dir, "0", "1000000", "12", "-1", NULL };
        struct child c;
        REQUIRE(child_start(&c, args));
        int64_t synced = -1, synced_len = -1;
        const int syncs = test_random_below(&rnd, 3);
        int seen = 0;
        while (seen < syncs && child_line(&c, line, sizeof line)) {
            long long i, len;
            if (sscanf(line, "synced %lld %lld", &i, &len) == 2) {
                synced = i;
                synced_len = len;
                seen++;
            }
        }
        usleep((useconds_t) (test_random_below(&rnd, 60000)));
        kill(c.pid, SIGKILL);
        while (child_line(&c, line, sizeof line)) {     /* syncs before the kill landed */
            long long i, len;
            if (sscanf(line, "synced %lld %lld", &i, &len) == 2) {
                synced = i;
                synced_len = len;
            }
        }
        int status = child_wait(&c);
        CHECK(WIFSIGNALED(status) && WTERMSIG(status) == SIGKILL);
        const int64_t bytes = du_stream_bytes(dir);
        struct bergdb_start_info info;
        bool ok;
        int64_t n = restart_and_go_on(dir, 1000000, synced + 40, &info, &ok);
        CHECK(ok);
        CHECK(n >= synced);
        if (n > synced) {
            unsynced_found++;
        }
        if (n >= 0 && bytes > info.last_pos + 1) {
            torn++;
        }
        if (!ok || n < synced) {
            printf("  round %d: synced %lld (length %lld), found %lld, files %lld bytes\n", round,
                    (long long) synced, (long long) synced_len, (long long) n, (long long) bytes);
        }
        du_remove_dir(dir);
    }
    printf("  durable_kill_at_random: %d rounds, %d with a torn last record, %d with "
            "transactions found beyond the last sync\n", rounds, torn, unsynced_found);
}

/* A directory held by a database of another process: BERGDB_IN_USE until
 * it is closed (Java's lock, 005-63). Within one process, a directory is
 * opened once (readme.md, section 9, point 10; 012-13's decision). */
TEST(durable_in_use) {
    char dir[1024], line[600];
    du_temp_dir(dir, sizeof dir);
    REQUIRE(dir[0] != '\0');
    REQUIRE(func_program != NULL);
    struct bergdb_mem m = {0};
    struct bergdb_test_clock clock = {0};
    struct bergdb_options o;
    bergdb_db *db;
    du_options(&o, &clock, &m);
    bergdb_test_clock_set(&clock, 1000);
    REQUIRE(bergdb_open(dir, &o, &db, NULL, NULL) == BERGDB_OK);
    const char *args[] = { "open", dir, NULL };
    struct child c;
    REQUIRE(child_start(&c, args));
    CHECK(child_line(&c, line, sizeof line));
    CHECK(strncmp(line, "BERGDB_IN_USE DirectoryInUseException: ", 39) == 0);
    child_wait(&c);
    CHECK(bergdb_close(db) == BERGDB_OK);
    CHECK_EQ(m.live_total, 0);
    REQUIRE(child_start(&c, args));
    CHECK(child_line(&c, line, sizeof line));
    CHECK(strncmp(line, "BERGDB_OK ", 10) == 0);
    child_wait(&c);
    du_remove_dir(dir);
}

/* A write that fails (EFBIG at the file size limit) fails the database
 * (P7): the sync gives BERGDB_FAILED, and so does every later transaction
 * and read, and sync; the status works; the close gives BERGDB_IO and frees
 * everything. A restart then finds a prefix of the transactions: the
 * records that the failed write left whole. */
TEST(durable_write_fails) {
    char dir[1024], line[600];
    du_temp_dir(dir, sizeof dir);
    REQUIRE(dir[0] != '\0');
    REQUIRE(func_program != NULL);
    const char *args[] = { "fsize", dir, "150000", NULL };   /* the first file: 200 kB */
    struct child c;
    REQUIRE(child_start(&c, args));
    static const char *const expect[] = { "execute BERGDB_OK", "execute BERGDB_OK",
        "execute BERGDB_OK", "execute BERGDB_OK", "execute BERGDB_OK", "execute BERGDB_OK",
        "execute BERGDB_OK", "execute BERGDB_OK", "execute BERGDB_OK", "execute BERGDB_OK",
        "sync BERGDB_FAILED DbFailedException: A sync failed on the storage",
        "execute BERGDB_FAILED", "read_new BERGDB_OK", "get_one BERGDB_FAILED",
        "stats BERGDB_OK length=", "sync BERGDB_FAILED", "set_cache_size_indicator BERGDB_OK",
        "close BERGDB_IO", "live 0" };
    for (size_t i = 0; i < sizeof expect / sizeof expect[0]; i++) {
        bool got = child_line(&c, line, sizeof line);
        CHECK(got && strncmp(line, expect[i], strlen(expect[i])) == 0);
        if (!got || strncmp(line, expect[i], strlen(expect[i])) != 0) {
            printf("  expected \"%s\", got \"%s\"\n", expect[i], got ? line : "(end)");
        }
    }
    int status = child_wait(&c);
    CHECK(WIFEXITED(status) && WEXITSTATUS(status) == 0);
    const int64_t written = du_stream_bytes(dir);
    CHECK(written <= 150000);
    struct bergdb_start_info info;
    bool ok;
    int64_t n = restart_and_go_on(dir, 50000, 12, &info, &ok);
    CHECK(ok);
    CHECK(n >= 0 && n < 3);     /* 150,000 bytes hold 2 of the 50 kB records */
    printf("  durable_write_fails: %lld bytes written, transactions 0 to %lld found\n",
            (long long) written, (long long) n);
    du_remove_dir(dir);
}

/* A write of the full write buffer within bergdb_execute that fails
 * (EFBIG) fails the database (P7): the execute gives BERGDB_FAILED, and so
 * does the next; the close gives BERGDB_IO and frees everything. A restart
 * finds the transaction before (bergdb 022-05; DbTester's
 * testWriterWaitingForRoomAfterFailedFlush, 005-35, in C: C has no buffer
 * thread to wait for). */
TEST(durable_write_fails_in_execute) {
    char dir[1024], line[600];
    du_temp_dir(dir, sizeof dir);
    REQUIRE(dir[0] != '\0');
    REQUIRE(func_program != NULL);
    const char *args[] = { "fsizebig", dir, "150000", NULL };
    struct child c;
    REQUIRE(child_start(&c, args));
    static const char *const expect[] = { "execute BERGDB_OK",
        "execute BERGDB_FAILED DbFailedException: ", "execute BERGDB_FAILED",
        "close BERGDB_IO", "live 0" };
    for (size_t i = 0; i < sizeof expect / sizeof expect[0]; i++) {
        bool got = child_line(&c, line, sizeof line);
        CHECK(got && strncmp(line, expect[i], strlen(expect[i])) == 0);
        if (!got || strncmp(line, expect[i], strlen(expect[i])) != 0) {
            printf("  expected \"%s\", got \"%s\"\n", expect[i], got ? line : "(end)");
        }
    }
    int status = child_wait(&c);
    CHECK(WIFEXITED(status) && WEXITSTATUS(status) == 0);
    CHECK(du_stream_bytes(dir) <= 150000);
    struct bergdb_start_info info;
    bool ok;
    int64_t n = restart_and_go_on(dir, 1000, 3, &info, &ok);
    CHECK(ok);
    CHECK_EQ(n, 0);
    du_remove_dir(dir);
}

/* The directory's entries, sorted, as "NAME NAME ...". */
static void du_entries(const char *dir, char *out, size_t size) {
    struct dirent **list;
    int n = scandir(dir, &list, NULL, alphasort);
    size_t at = 0;
    out[0] = '\0';
    for (int i = 0; i < n; i++) {
        if (list[i]->d_name[0] != '.' && at < size) {
            at += (size_t) snprintf(out + at, size - at, "%s%s", at > 0 ? " " : "",
                    list[i]->d_name);
        }
        free(list[i]);
    }
    if (n >= 0) {
        free(list);
    }
}

/* A clock whose time is out of range. */
static int64_t du_negative_clock(void *ctx) {
    (void) ctx;
    return -1;
}

/* bergdb 015-06, Java's PubTester.testRefusedStartAfterOpenCreatesNoStreamFile:
 * a creation refused after the directory's open, its clock out of range
 * (BERGDB_LIMIT, 005-18), on an empty directory and on a missing one,
 * leaves only bergdb.lock, which is never deleted (005-63); an open then
 * creates the database, in one stream file. Before, the open made an empty
 * first stream file, 00000000000000.bergdb, and the refused creation left
 * it. */
TEST(durable_refused_creation) {
    char base[1024], dir[1100], got[600];
    du_temp_dir(base, sizeof base);
    REQUIRE(base[0] != '\0');
    for (int k = 0; k < 2; k++) {
        snprintf(dir, sizeof dir, "%s/%s", base, k == 0 ? "empty" : "missing");
        if (k == 0) {
            REQUIRE(mkdir(dir, 0777) == 0);
        }
        struct bergdb_mem m = {0};
        struct bergdb_test_clock clock = {0};
        struct bergdb_options o;
        struct bergdb_executed ex;
        char errbuf[BERGDB_ERRBUF_SIZE];
        uint8_t v[16];
        bergdb_db *db;
        du_options(&o, &clock, &m);
        o.clock = du_negative_clock;
        o.clock_ctx = NULL;
        CHECK_EQ(bergdb_open(dir, &o, &db, NULL, errbuf), BERGDB_LIMIT);
        CHECK(strstr(errbuf, "outside the range") != NULL);
        CHECK_EQ(m.live_total, 0);
        du_entries(dir, got, sizeof got);
        CHECK(strcmp(got, "bergdb.lock") == 0);
        if (strcmp(got, "bergdb.lock") != 0) {
            printf("  %s: %s\n", k == 0 ? "empty" : "missing", got);
        }
        du_options(&o, &clock, &m);
        bergdb_test_clock_set(&clock, 1000);
        REQUIRE(bergdb_open(dir, &o, &db, NULL, NULL) == BERGDB_OK);
        CHECK_EQ(du_trans(db, &clock, 1, sizeof v, v, &ex), BERGDB_OK);
        CHECK(bergdb_close(db) == BERGDB_OK);
        CHECK_EQ(m.live_total, 0);
        du_entries(dir, got, sizeof got);
        CHECK(strcmp(got, "00000000000000.bergdb bergdb.lock") == 0);
    }
    du_remove_dir(base);
}

/* bergdb 021-20 (020-24-10, U10-1), Java's
 * PubTesterJavadocNewUsers.testDirectoryDeletedWhileTheDatabaseRuns: a
 * database's directory deleted while the database runs, and a new database
 * created at the path. The old one fails at its next stream file, with
 * Java's text as the cause, and makes nothing in the directory now at the
 * path; its close gives BERGDB_IO; the new one keeps its data. Java
 * refuses the new start within the JVM while the old database is open; C
 * does not within the process (its lock is the process's: readme.md,
 * section 9, point 10), and neither refuses another process's, so the new
 * database here is what another process would open. Before, the old
 * database made its next file in the new directory, and the new one's next
 * open was refused (BadDirStateException). Then the case of
 * testNewDatabaseWhereAStoppedOneWasDeleted: closed, deleted, a new
 * database at the path, which keeps its data; C has no stop(), and
 * bergdb_close returns after its last write, so it passed before too. */
TEST(durable_directory_replaced) {
    char base[1024], dir[1100], want[1600];
    du_temp_dir(base, sizeof base);
    REQUIRE(base[0] != '\0');
    snprintf(dir, sizeof dir, "%s/doc", base);
    struct bergdb_mem m = {0}, m2 = {0};
    struct bergdb_test_clock clock = {0}, clock2 = {0};
    struct bergdb_options o;
    struct bergdb_executed ex;
    struct bergdb_start_info info;
    bergdb_db *old, *db;
    bool ok;
    uint8_t *v = malloc(20000);
    REQUIRE(v != NULL);

    du_options(&o, &clock, &m);
    bergdb_test_clock_set(&clock, 1000);
    REQUIRE(bergdb_open(dir, &o, &old, NULL, NULL) == BERGDB_OK);
    for (int64_t i = 0; i < 50; i++) {
        CHECK_EQ(du_trans(old, &clock, i, 20000, v, &ex), BERGDB_OK);
    }
    CHECK_EQ(bergdb_sync(old, 0, BERGDB_SYNC_ORDINARY), BERGDB_OK);
    du_remove_dir(dir);

    du_options(&o, &clock2, &m2);
    bergdb_test_clock_set(&clock2, 1000);
    REQUIRE(bergdb_open(dir, &o, &db, NULL, NULL) == BERGDB_OK);
    CHECK_EQ(du_trans(db, &clock2, 0, 100, v, &ex), BERGDB_OK);
    CHECK_EQ(bergdb_sync(db, 0, BERGDB_SYNC_ORDINARY), BERGDB_OK);

    int rc = BERGDB_OK;
    int64_t i = 50;
    for (; i < 550 && rc == BERGDB_OK; i++) {          /* up to 10 MB: a new file */
        rc = du_trans(old, &clock, i, 20000, v, &ex);
        if (rc == BERGDB_OK && i % 50 == 49) {
            rc = bergdb_sync(old, 0, BERGDB_SYNC_ORDINARY);
        }
    }
    CHECK_EQ(rc, BERGDB_FAILED);
    /* The cause's text, as far as C's limit leaves it (240 bytes). */
    snprintf(want, sizeof want, "DbFailedException: A sync failed on the storage (the cause). "
            "The database takes no more transactions or reads and must be restarted. Cause: "
            "IOException: Directory %s is no longer the database's directory: it was deleted, "
            "moved or replaced while the database had it open. Nothing more is written there.",
            dir);
    const char *got = bergdb_errmsg(old);
    const size_t prefix = (size_t) (strstr(want, dir) - want) + strlen(dir);
    CHECK(strlen(got) >= prefix && strncmp(got, want, strlen(got)) == 0);
    if (!(strlen(got) >= prefix && strncmp(got, want, strlen(got)) == 0)) {
        printf("  durable_directory_replaced: after transaction %lld: %s\n", (long long) i,
                got);
    }
    CHECK_EQ(bergdb_sync(old, 0, BERGDB_SYNC_ORDINARY), BERGDB_FAILED);
    CHECK_EQ(bergdb_close(old), BERGDB_IO);
    CHECK_EQ(m.live_total, 0);
    CHECK_EQ(bergdb_close(db), BERGDB_OK);
    CHECK_EQ(m2.live_total, 0);

    /* The new database's transaction 0, of 100 bytes, and none of the old's. */
    clock2.time += 1000000;
    CHECK_EQ(restart_finds(dir, &clock2, &m2, 100, 60, &db, &info, &ok), 0);
    CHECK(ok);
    CHECK_EQ(bergdb_close(db), BERGDB_OK);
    CHECK_EQ(m2.live_total, 0);

    /* Closed, deleted, and a new database at the path. */
    du_remove_dir(dir);
    du_options(&o, &clock, &m);
    bergdb_test_clock_set(&clock, 1000);
    REQUIRE(bergdb_open(dir, &o, &db, NULL, NULL) == BERGDB_OK);
    CHECK_EQ(du_trans(db, &clock, 0, 100, v, &ex), BERGDB_OK);
    CHECK_EQ(bergdb_close(db), BERGDB_OK);
    clock.time += 1000000;
    CHECK_EQ(restart_finds(dir, &clock, &m, 100, 60, &db, &info, &ok), 0);
    CHECK(ok);
    CHECK_EQ(bergdb_close(db), BERGDB_OK);
    CHECK_EQ(m.live_total, 0);
    free(v);
    du_remove_dir(base);
}

/* bergdb 020-24-10, U10-5, Java's
 * FileStream.testConcurrentOpensOfANewDirectory, with processes for
 * threads: eight processes open a directory that does not exist yet, two
 * levels below an existing one, at once, ten rounds. Each open is taken or
 * refused as in use (BERGDB_IN_USE, DirectoryInUseException), and at least
 * one is taken: none is refused because another made the directory first.
 * Java's mkdirs() returned false when another thread had made it, and the
 * start threw "Directory ... could not be created."; C's plat_mkdirs took
 * EEXIST already, so this passed before too. */
TEST(durable_concurrent_opens_of_a_new_directory) {
    char base[1024], dir[1100], at[32], line[600];
    du_temp_dir(base, sizeof base);
    REQUIRE(base[0] != '\0');
    REQUIRE(func_program != NULL);
    int taken = 0, refused = 0;
    for (int round = 0; round < 10; round++) {
        struct child c[8];
        bool started[8];
        snprintf(dir, sizeof dir, "%s/r%d/a/b", base, round);
        snprintf(at, sizeof at, "%lld", (long long) (du_millis() + 300));
        const char *args[] = { "openat", dir, at, NULL };
        for (int k = 0; k < 8; k++) {
            started[k] = child_start(&c[k], args);
            CHECK(started[k]);
        }
        int taken_now = 0;
        for (int k = 0; k < 8; k++) {
            if (!started[k]) {
                continue;
            }
            bool got = child_line(&c[k], line, sizeof line);
            if (got && strncmp(line, "BERGDB_OK ", 10) == 0) {
                taken_now++;
            } else if (got && strncmp(line, "BERGDB_IN_USE DirectoryInUseException: ", 39) == 0) {
                refused++;
            } else {
                CHECK(false);
                printf("  round %d: %s\n", round, got ? line : "(no line)");
            }
            int status = child_wait(&c[k]);
            CHECK(WIFEXITED(status) && WEXITSTATUS(status) == 0);
        }
        CHECK(taken_now >= 1);
        taken += taken_now;
    }
    printf("  durable_concurrent_opens_of_a_new_directory: 10 rounds of 8, %d taken, %d "
            "refused as in use\n", taken, refused);
    du_remove_dir(base);
}

const struct test durable_tests[] = {
    TEST_ENTRY(durable_kill_after_execute_and_sync),
    TEST_ENTRY(durable_kill_at_random),
    TEST_ENTRY(durable_in_use),
    TEST_ENTRY(durable_write_fails),
    TEST_ENTRY(durable_write_fails_in_execute),
    TEST_ENTRY(durable_refused_creation),
    TEST_ENTRY(durable_directory_replaced),
    TEST_ENTRY(durable_concurrent_opens_of_a_new_directory),
    TEST_END
};
