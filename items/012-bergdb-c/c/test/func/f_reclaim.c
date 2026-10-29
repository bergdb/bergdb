/* Functional tests of reclaim, Level 3 (bergdb 012-11, part 1; 012-01, 6.4),
 * through include/bergdb.h only: a long run in a directory with a short
 * retain duration keeps the directory's size bounded, its front files
 * deleted, with a sync now and then and with none (C forces the stream
 * itself for a cut, one force per cut: 012-11, 6.4, Q1, option B); a cut
 * that the table marks and the files do not show made at the next open;
 * the first available time and position
 * and the iteration count in the stats; reads before the first available
 * time refused (getOne, getMany), and getTrans of a removed record; the
 * settings' checks; a retain duration of forever stops new iterations and
 * cuts. Each test ends with the allocator's count 0. */
#include <dirent.h>
#include <stdlib.h>
#include <sys/stat.h>
#include <unistd.h>
#include "test.h"
#include "bergdb.h"

static void temp_dir(char *out, size_t cap) {
    const char *t = getenv("TMPDIR");
    snprintf(out, cap, "%s/bergdb-func-XXXXXX", t != NULL ? t : "/tmp");
    if (mkdtemp(out) == NULL) {
        out[0] = '\0';
    }
}

static void remove_dir(const char *dir) {
    char cmd[1200];
    snprintf(cmd, sizeof cmd, "rm -rf '%s'", dir);
    if (system(cmd) != 0) {
        printf("could not remove %s\n", dir);
    }
}

/* The .bergdb files: their number, total size and the first one's start. */
static void dir_files(const char *dir, int *n, int64_t *bytes, int64_t *first) {
    DIR *d = opendir(dir);
    struct dirent *x;
    *n = 0;
    *bytes = 0;
    *first = INT64_MAX;
    while (d != NULL && (x = readdir(d)) != NULL) {
        size_t len = strlen(x->d_name);
        if (len != 21 || strcmp(x->d_name + 14, ".bergdb") != 0) {
            continue;
        }
        char path[1200];
        struct stat st;
        snprintf(path, sizeof path, "%s/%s", dir, x->d_name);
        if (stat(path, &st) == 0) {
            (*n)++;
            *bytes += (int64_t) st.st_size;
        }
        int64_t start = strtoll(x->d_name, NULL, 10) * 100000;
        if (start < *first) {
            *first = start;
        }
    }
    if (d != NULL) {
        closedir(d);
    }
}

static int put(bergdb_db *db, struct bergdb_test_clock *clock, int64_t tt, const char *ikey,
        const uint8_t *v, size_t len, struct bergdb_executed *ex) {
    bergdb_trans *t;
    uint8_t b[64];
    size_t kl = strlen(ikey);
    bergdb_ikey_to_bkey((const uint8_t *) ikey, kl, b);
    bergdb_test_clock_set(clock, tt);
    int rc = bergdb_trans_new(db, &t);
    if (rc == BERGDB_OK) {
        rc = bergdb_trans_put(t, b, kl, v, len);
    }
    if (rc == BERGDB_OK) {
        rc = bergdb_execute(db, t, ex);
    }
    bergdb_trans_free(t);
    return rc;
}

TEST(api_reclaim_directory) {
    struct bergdb_mem m = {0};
    struct bergdb_test_clock clock = {0};
    struct bergdb_options o;
    bergdb_db *db;
    char dir[1024];
    temp_dir(dir, sizeof dir);
    REQUIRE(dir[0] != '\0');
    bergdb_options_init(&o);
    o.clock = bergdb_test_clock_time;
    o.clock_ctx = &clock;
    memcpy(o.id, bergdb_test_id, BERGDB_ID_SIZE);
    o.max_node_size = 8;
    o.startup_distance = 2000;
    o.retain_duration = BERGDB_UNITS_PER_SEC;
    o.mem = &m;
    int64_t time = BERGDB_UNITS_PER_SEC;
    bergdb_test_clock_set(&clock, time);
    REQUIRE(bergdb_open(dir, &o, &db, NULL, NULL) == BERGDB_OK);

    /* The settings' checks. */
    CHECK(bergdb_set_retain_duration(db, BERGDB_UNITS_PER_SEC - 1) == BERGDB_ARG);
    CHECK(strncmp(bergdb_errmsg(db), "IllegalArgumentException", 24) == 0);
    CHECK(bergdb_set_reclaim_internal_fraction(db, 0.95) == BERGDB_ARG);
    CHECK(bergdb_set_reclaim_internal_fraction(db, 0.0001) == BERGDB_ARG);
    CHECK(bergdb_set_reclaim_internal_fraction(db, 0.25) == BERGDB_OK);
    struct bergdb_stats s;
    REQUIRE(bergdb_stats(db, &s) == BERGDB_OK);
    CHECK_EQ(s.retain_duration, BERGDB_UNITS_PER_SEC);
    CHECK(s.internal_fraction == 0.25);
    CHECK_EQ(s.reclaim_iteration_count, 0);
    CHECK_EQ(s.first_available_pos, 0);
    CHECK_EQ(s.first_available_lookup_time, 0);

    uint64_t rnd = 7;
    uint8_t v[200];
    int64_t maxBytes = 0;
    int64_t firstTpos = -1;
    struct bergdb_executed ex;
    int cuts = 0;
    int64_t lastFirst = 0;
    const int N = 6000;
    for (int i = 0; i < N; i++) {
        time += BERGDB_UNITS_PER_SEC / 20;
        char key[32];
        snprintf(key, sizeof key, "/k/%d", test_random_below(&rnd, 50));
        size_t len = (size_t) (50 + test_random_below(&rnd, 150));
        for (size_t j = 0; j < len; j++) {
            v[j] = (uint8_t) test_random(&rnd);
        }
        REQUIRE(put(db, &clock, time, key, v, len, &ex) == BERGDB_OK);
        if (firstTpos == -1) {
            firstTpos = ex.tpos;
        }
        if (i % 20 == 19) {
            REQUIRE(bergdb_sync(db, 0, BERGDB_SYNC_ORDINARY) == BERGDB_OK);
        }
        int n;
        int64_t bytes, first;
        dir_files(dir, &n, &bytes, &first);
        if (first > lastFirst) {
            cuts++;
            lastFirst = first;
        }
        if (i >= N / 2 && bytes > maxBytes) {
            maxBytes = bytes;
        }
    }
    REQUIRE(bergdb_stats(db, &s) == BERGDB_OK);
    CHECK(s.reclaim_iteration_count > 5);
    CHECK(s.first_available_pos > 0);
    CHECK(s.first_available_lookup_time > 0);
    CHECK(cuts >= 3);
    /* Bounded: the second half's largest directory is a small part of the
     * stream, and about what the retention needs. */
    printf("  api_reclaim_directory: stream %lld bytes, the directory at most %lld bytes in the "
            "second half, %d cuts seen, %lld iterations\n", (long long) s.stream_length,
            (long long) maxBytes, cuts, (long long) s.reclaim_iteration_count);
    CHECK(maxBytes * 4 < s.stream_length);

    /* Reads before the first available time, and getTrans of a removed record. */
    bergdb_read *rd;
    REQUIRE(bergdb_read_new(db, &rd) == BERGDB_OK);
    uint8_t b[64];
    size_t kl = strlen("/k/1");
    bergdb_ikey_to_bkey((const uint8_t *) "/k/1", kl, b);
    struct bergdb_one gv;
    CHECK(bergdb_get_one(db, rd, s.first_available_lookup_time - 1, b, kl, &gv)
            == BERGDB_NOT_AVAILABLE);
    CHECK(strncmp(bergdb_errmsg(db), "LookupTimeNotAvailableException", 31) == 0);
    CHECK(bergdb_get_one(db, rd, s.first_available_lookup_time, b, kl, &gv) == BERGDB_OK);
    struct bergdb_range range;
    bergdb_range_init(&range);
    range.lookup_time = s.first_available_lookup_time - 1;
    struct bergdb_many many;
    CHECK(bergdb_get_many(db, rd, &range, &many) == BERGDB_NOT_AVAILABLE);
    range.lookup_time = s.first_available_lookup_time;
    CHECK(bergdb_get_many(db, rd, &range, &many) == BERGDB_OK);
    struct bergdb_stored st;
    CHECK(bergdb_get_trans(db, rd, firstTpos, &st) == BERGDB_NOT_AVAILABLE);
    CHECK(strncmp(bergdb_errmsg(db), "LookupTimeNotAvailableException", 31) == 0);
    CHECK(bergdb_get_trans(db, rd, s.first_available_pos, &st) == BERGDB_OK);
    bergdb_read_free(rd);

    /* Forever: no new iteration starts, and no cut. */
    REQUIRE(bergdb_set_retain_duration(db, BERGDB_FOREVER) == BERGDB_OK);
    int64_t firstPos = s.first_available_pos;
    for (int i = 0; i < 2000; i++) {
        time += BERGDB_UNITS_PER_SEC / 20;
        REQUIRE(put(db, &clock, time, "/k/x", v, 100, &ex) == BERGDB_OK);
        if (i % 20 == 19) {
            REQUIRE(bergdb_sync(db, 0, BERGDB_SYNC_ORDINARY) == BERGDB_OK);
        }
    }
    struct bergdb_stats s2;
    REQUIRE(bergdb_stats(db, &s2) == BERGDB_OK);
    CHECK_EQ(s2.first_available_pos, firstPos);
    CHECK(s2.reclaim_iteration_count <= s.reclaim_iteration_count + 1);

    CHECK(bergdb_close(db) == BERGDB_OK);
    CHECK_EQ(m.live_total, 0);
    remove_dir(dir);
}

/* With no sync at all: C forces the stream for each cut it decides, one
 * force per cut, and deletes the front files in that call (012-11, 6.4,
 * Q1, option B, decided by Frans 2026-10-29), so the directory stays
 * bounded as with syncs, and as Java's does with its buffer thread. The
 * stream (about 1 MB) never fills the 10 MB write buffer: without the
 * forces nothing would reach the files, and no file would be deleted,
 * until the close. */
TEST(api_reclaim_directory_no_sync) {
    struct bergdb_mem m = {0};
    struct bergdb_test_clock clock = {0};
    struct bergdb_options o;
    bergdb_db *db;
    char dir[1024];
    temp_dir(dir, sizeof dir);
    REQUIRE(dir[0] != '\0');
    bergdb_options_init(&o);
    o.clock = bergdb_test_clock_time;
    o.clock_ctx = &clock;
    memcpy(o.id, bergdb_test_id, BERGDB_ID_SIZE);
    o.max_node_size = 8;
    o.startup_distance = 2000;
    o.retain_duration = BERGDB_UNITS_PER_SEC;
    o.mem = &m;
    int64_t time = BERGDB_UNITS_PER_SEC;
    bergdb_test_clock_set(&clock, time);
    REQUIRE(bergdb_open(dir, &o, &db, NULL, NULL) == BERGDB_OK);

    uint64_t rnd = 11;
    uint8_t v[200];
    struct bergdb_executed ex;
    struct bergdb_stats s;
    REQUIRE(bergdb_stats(db, &s) == BERGDB_OK);
    int64_t durable = s.durable_length;
    int64_t firstPos = s.first_available_pos;
    int64_t lastFirst = 0, maxBytes = 0;
    int decided = 0, forces = 0, deletes = 0, forcesWithoutCut = 0, cutsNotDurable = 0;
    const int N = 6000;
    for (int i = 0; i < N; i++) {
        time += BERGDB_UNITS_PER_SEC / 20;
        char key[32];
        snprintf(key, sizeof key, "/k/%d", test_random_below(&rnd, 50));
        size_t len = (size_t) (50 + test_random_below(&rnd, 150));
        for (size_t j = 0; j < len; j++) {
            v[j] = (uint8_t) test_random(&rnd);
        }
        REQUIRE(put(db, &clock, time, key, v, len, &ex) == BERGDB_OK);
        REQUIRE(bergdb_stats(db, &s) == BERGDB_OK);
        const bool cut = s.first_available_pos != firstPos;
        const bool forced = s.durable_length != durable;
        decided += cut;
        forces += forced;
        forcesWithoutCut += forced && !cut;
        /* The cut's call forced the stream whole: the decision is durable. */
        cutsNotDurable += cut && s.durable_length != s.stream_length;
        durable = s.durable_length;
        firstPos = s.first_available_pos;
        int n;
        int64_t bytes, first;
        dir_files(dir, &n, &bytes, &first);
        if (first > lastFirst) {
            deletes++;
            lastFirst = first;
            CHECK(cut);                     /* files deleted only in a cut's call */
            CHECK(first <= s.first_available_pos);
        }
        if (i >= N / 2 && bytes > maxBytes) {
            maxBytes = bytes;
        }
    }
    printf("  api_reclaim_directory_no_sync: stream %lld bytes, the directory at most %lld "
            "bytes in the second half, %d cuts decided, %d forces, %d with files deleted\n",
            (long long) s.stream_length, (long long) maxBytes, decided, forces, deletes);
    CHECK(decided >= 3);
    CHECK_EQ(forces, decided);              /* one force per cut, none else */
    CHECK_EQ(forcesWithoutCut, 0);
    CHECK_EQ(cutsNotDurable, 0);
    CHECK(deletes >= 3);
    CHECK(maxBytes > 0);
    CHECK(maxBytes * 4 < s.stream_length);  /* bounded, as with syncs */
    CHECK(bergdb_close(db) == BERGDB_OK);
    CHECK_EQ(m.live_total, 0);
    remove_dir(dir);
}

/* Hard links in keep/ to every .bergdb file of dir not linked yet, so that
 * the files a cut deletes can be put back. */
static void keep_files(const char *dir, const char *keep) {
    DIR *d = opendir(dir);
    struct dirent *x;
    while (d != NULL && (x = readdir(d)) != NULL) {
        size_t len = strlen(x->d_name);
        if (len == 21 && strcmp(x->d_name + 14, ".bergdb") == 0) {
            char from[1200], to[1200];
            snprintf(from, sizeof from, "%s/%s", dir, x->d_name);
            snprintf(to, sizeof to, "%s/%s", keep, x->d_name);
            (void) link(from, to);      /* EEXIST: kept already */
        }
    }
    if (d != NULL) {
        closedir(d);
    }
}

/* The files of keep/ that dir lacks, linked back into dir: the cuts undone
 * on the disk, the table that marks them left as it is. */
static int restore_files(const char *dir, const char *keep) {
    DIR *d = opendir(keep);
    struct dirent *x;
    int restored = 0;
    while (d != NULL && (x = readdir(d)) != NULL) {
        if (x->d_name[0] == '.') {
            continue;
        }
        char from[1200], to[1200];
        snprintf(from, sizeof from, "%s/%s", keep, x->d_name);
        snprintf(to, sizeof to, "%s/%s", dir, x->d_name);
        if (link(from, to) == 0) {
            restored++;
        }
    }
    if (d != NULL) {
        closedir(d);
    }
    return restored;
}

/* A cut that the table marks and the files do not show (a crash after the
 * cut's force, before its deletes; or Java's directory, whose cut thread
 * deletes later) is made at the next open, as Java's initFromDb makes it:
 * C cuts as it runs (Q1, option B), the files it deleted are put back
 * after the close, and the open deletes them again; the first available
 * position and time are the table's, and reclaim goes on after the start. */
TEST(api_reclaim_pending_cut_at_open) {
    struct bergdb_mem m = {0};
    struct bergdb_test_clock clock = {0};
    struct bergdb_options o;
    bergdb_db *db;
    char dir[1024];
    temp_dir(dir, sizeof dir);
    REQUIRE(dir[0] != '\0');
    bergdb_options_init(&o);
    o.clock = bergdb_test_clock_time;
    o.clock_ctx = &clock;
    memcpy(o.id, bergdb_test_id, BERGDB_ID_SIZE);
    o.max_node_size = 8;
    o.startup_distance = 2000;
    o.retain_duration = BERGDB_UNITS_PER_SEC;
    o.mem = &m;
    int64_t time = BERGDB_UNITS_PER_SEC;
    bergdb_test_clock_set(&clock, time);
    char keep[1100];
    snprintf(keep, sizeof keep, "%s-keep", dir);
    REQUIRE(mkdir(keep, 0700) == 0);
    REQUIRE(bergdb_open(dir, &o, &db, NULL, NULL) == BERGDB_OK);
    uint64_t rnd = 3;
    uint8_t v[200];
    struct bergdb_executed ex;
    for (int i = 0; i < 3000; i++) {
        time += BERGDB_UNITS_PER_SEC / 20;
        char key[32];
        snprintf(key, sizeof key, "/k/%d", test_random_below(&rnd, 50));
        size_t len = (size_t) (50 + test_random_below(&rnd, 150));
        memset(v, (int) i, len);
        REQUIRE(put(db, &clock, time, key, v, len, &ex) == BERGDB_OK);
        keep_files(dir, keep);
    }
    struct bergdb_stats s;
    REQUIRE(bergdb_stats(db, &s) == BERGDB_OK);
    REQUIRE(s.first_available_pos > 200000);
    int n;
    int64_t bytes, first;
    dir_files(dir, &n, &bytes, &first);
    CHECK(first > 0);                       /* no sync, and cut as it ran (Q1, B) */
    CHECK(bergdb_close(db) == BERGDB_OK);
    CHECK(restore_files(dir, keep) > 0);
    remove_dir(keep);
    dir_files(dir, &n, &bytes, &first);
    CHECK_EQ(first, 0);                     /* the cuts undone on the disk */

    REQUIRE(bergdb_open(dir, &o, &db, NULL, NULL) == BERGDB_OK);
    struct bergdb_stats s2;
    REQUIRE(bergdb_stats(db, &s2) == BERGDB_OK);
    CHECK_EQ(s2.first_available_pos, s.first_available_pos);
    CHECK_EQ(s2.first_available_lookup_time, s.first_available_lookup_time);
    dir_files(dir, &n, &bytes, &first);
    CHECK(first > 0 && first <= s.first_available_pos);     /* the cut, made at the open */
    CHECK(s.first_available_pos - first < 2000000);
    bergdb_read *rd;
    REQUIRE(bergdb_read_new(db, &rd) == BERGDB_OK);
    uint8_t b[64];
    size_t kl = strlen("/k/1");
    bergdb_ikey_to_bkey((const uint8_t *) "/k/1", kl, b);
    struct bergdb_one gv;
    CHECK(bergdb_get_one(db, rd, s2.first_available_lookup_time, b, kl, &gv) == BERGDB_OK);
    CHECK(bergdb_get_one(db, rd, s2.first_available_lookup_time - 1, b, kl, &gv)
            == BERGDB_NOT_AVAILABLE);
    bergdb_read_free(rd);
    /* Reclaim goes on: more iterations, a later cut. */
    for (int i = 0; i < 1500; i++) {
        time += BERGDB_UNITS_PER_SEC / 20;
        char key[32];
        snprintf(key, sizeof key, "/k/%d", test_random_below(&rnd, 50));
        REQUIRE(put(db, &clock, time, key, v, 100, &ex) == BERGDB_OK);
    }
    REQUIRE(bergdb_stats(db, &s2) == BERGDB_OK);
    CHECK(s2.reclaim_iteration_count > 0);
    CHECK(s2.first_available_pos > s.first_available_pos);
    CHECK(bergdb_close(db) == BERGDB_OK);
    CHECK_EQ(m.live_total, 0);
    remove_dir(dir);
}

const struct test reclaim_func_tests[] = {
    TEST_ENTRY(api_reclaim_directory),
    TEST_ENTRY(api_reclaim_directory_no_sync),
    TEST_ENTRY(api_reclaim_pending_cut_at_open),
    TEST_END
};
