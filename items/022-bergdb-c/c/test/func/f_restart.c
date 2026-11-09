/* Functional tests of restarts (bergdb 022-05), through include/bergdb.h only:
 * Java's DbTesterRestart.testSameStreamAfterDecreaseWithRestartsF, smaller,
 * and DbTesterStream.testLargeTransactions and testLargeTransaction, which
 * take more than a unit test should; t_restart.c has DbTesterRestart's
 * others. Each test ends with the allocator's count 0. */
#include <dirent.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include "test.h"
#include "bergdb.h"

static void fr_temp_dir(char *out, size_t cap) {
    const char *t = getenv("TMPDIR");
    snprintf(out, cap, "%s/bergdb-restart-XXXXXX", t != NULL ? t : "/tmp");
    if (mkdtemp(out) == NULL) {
        out[0] = '\0';
    }
}

static void fr_remove_dir(const char *dir) {
    char cmd[1200];
    snprintf(cmd, sizeof cmd, "rm -rf '%s'", dir);
    if (system(cmd) != 0) {
        printf("could not remove %s\n", dir);
    }
}

static int fr_name_cmp(const void *a, const void *b) {
    return strcmp(*(const char *const *) a, *(const char *const *) b);
}

/* The stream's bytes: every NAME.bergdb file of dir, in the order of their names,
 * into a new buffer. */
static uint8_t *fr_read_stream(const char *dir, int64_t *len) {
    char *names[256];
    int n = 0;
    DIR *d = opendir(dir);
    *len = -1;
    if (d == NULL) {
        return NULL;
    }
    struct dirent *de;
    while ((de = readdir(d)) != NULL && n < 256) {
        size_t k = strlen(de->d_name);
        if (k > 7 && strcmp(de->d_name + k - 7, ".bergdb") == 0) {
            names[n++] = strdup(de->d_name);
        }
    }
    closedir(d);
    qsort(names, (size_t) n, sizeof names[0], fr_name_cmp);
    uint8_t *all = NULL;
    int64_t total = 0;
    for (int i = 0; i < n; i++) {
        char path[1200];
        snprintf(path, sizeof path, "%s/%s", dir, names[i]);
        FILE *f = fopen(path, "rb");
        if (f != NULL) {
            fseek(f, 0, SEEK_END);
            long m = ftell(f);
            fseek(f, 0, SEEK_SET);
            all = realloc(all, (size_t) (total + m + 1));
            total += (int64_t) fread(all + total, 1, (size_t) m, f);
            fclose(f);
        }
        free(names[i]);
    }
    *len = total;
    return all;
}

static void fr_options(struct bergdb_options *o, struct bergdb_test_clock *clock,
        struct bergdb_mem *m, int32_t sd) {
    bergdb_options_init(o);
    o->clock = bergdb_test_clock_time;
    o->clock_ctx = clock;
    memcpy(o->id, bergdb_test_id, BERGDB_ID_SIZE);
    o->max_node_size = 30;
    o->startup_distance = sd;
    o->mem = m;
}

/* A transaction of one put of the ikey at clock time tt. */
static int fr_put(bergdb_db *db, struct bergdb_test_clock *clock, int64_t tt, const char *ikey,
        const uint8_t *value, size_t len) {
    uint8_t bkey[64];
    const size_t kl = strlen(ikey);
    bergdb_trans *t;
    if (tt > clock->time) {
        bergdb_test_clock_set(clock, tt);
    }
    if (bergdb_ikey_to_bkey((const uint8_t *) ikey, kl, bkey) != BERGDB_OK) {
        return BERGDB_ARG;
    }
    int rc = bergdb_trans_new(db, &t);
    if (rc != BERGDB_OK) {
        return rc;
    }
    rc = bergdb_trans_put(t, bkey, kl, value, len);
    if (rc == BERGDB_OK) {
        rc = bergdb_execute(db, t, NULL);
    }
    bergdb_trans_free(t);
    return rc;
}

/* True if ikey's latest value is want's len bytes. */
static bool fr_value_is(bergdb_db *db, const char *ikey, const uint8_t *want, size_t len) {
    uint8_t bkey[64];
    const size_t kl = strlen(ikey);
    bergdb_read *rd;
    struct bergdb_one one;
    if (bergdb_ikey_to_bkey((const uint8_t *) ikey, kl, bkey) != BERGDB_OK
            || bergdb_read_new(db, &rd) != BERGDB_OK) {
        return false;
    }
    bool same = bergdb_get_one(db, rd, BERGDB_LATEST, bkey, kl, &one) == BERGDB_OK
            && one.value != NULL && one.value_len == len && memcmp(one.value, want, len) == 0;
    bergdb_read_free(rd);
    return same;
}

/* testSameStreamAfterDecreaseWithRestartsF's decreaseRun, smaller: puts of 1,000
 * random bytes at a startup distance of 1,000,000 bytes, lowered to 400,000 (the least
 * the call sets) after 1,200 of them, and 300 more, with a restart right after the call
 * and every restart_every after it (0: none); the stream. Java's: 2,000,000, 500,000,
 * 4,000 and 300. */
static uint8_t *decrease_run(int restart_every, int64_t *len) {
    char dir[1024], errbuf[BERGDB_ERRBUF_SIZE];
    struct bergdb_mem m = {0};
    struct bergdb_test_clock clock = {0};
    struct bergdb_options o;
    bergdb_db *db;
    *len = -1;
    fr_temp_dir(dir, sizeof dir);
    if (dir[0] == '\0') {
        return NULL;
    }
    fr_options(&o, &clock, &m, 1000 * 1000);
    uint64_t rnd = 1;
    int64_t time = 10;
    bool ok = bergdb_open(dir, &o, &db, NULL, errbuf) == BERGDB_OK;
    for (int i = 0; ok && i < 1500; i++) {
        bool restart = restart_every > 0 && i > 1200 && i % restart_every == 0;
        if (i == 1200) {
            CHECK_EQ(bergdb_set_startup_distance(db, 400 * 1000), BERGDB_OK);
            restart = restart_every > 0;
        }
        if (restart) {
            CHECK_EQ(bergdb_close(db), BERGDB_OK);
            ok = bergdb_open(dir, &o, &db, NULL, errbuf) == BERGDB_OK;
            if (!ok) {
                printf("    restart at %d: %s\n", i, errbuf);
                break;
            }
            struct bergdb_stats st;
            CHECK(bergdb_stats(db, &st) == BERGDB_OK && st.startup_distance == 400 * 1000);
        }
        uint8_t v[1000];
        for (int q = 0; q < 1000; q++) {
            v[q] = (uint8_t) test_random(&rnd);
        }
        char key[32];
        snprintf(key, sizeof key, "/k/%d", (int) test_random_below(&rnd, 1000));
        CHECK_EQ(fr_put(db, &clock, time++, key, v, sizeof v), BERGDB_OK);
    }
    CHECK(ok);
    if (ok) {
        CHECK_EQ(bergdb_close(db), BERGDB_OK);
    }
    CHECK_EQ(m.live_total, 0);
    uint8_t *bytes = fr_read_stream(dir, len);
    fr_remove_dir(dir);
    return bytes;
}

/* testSameStreamAfterDecreaseWithRestartsF (007-03, D4; 007-07): after a decrease of
 * the startup distance the deadline is the span of the section's transactions, which a
 * start rebuilds, and the new setting is in the meta block that the call's transaction
 * writes: the stream with restarts while the section comes down, one right after the
 * call and one every 10 transactions, is the one without, byte for byte (010, P2). */
TEST(func_restart_same_stream_after_decrease) {
    int64_t la, lb;
    uint8_t *a = decrease_run(0, &la);
    uint8_t *b = decrease_run(10, &lb);
    CHECK(la > 1500 * 1000);
    CHECK_EQ(la, lb);
    CHECK(a != NULL && b != NULL && la == lb && memcmp(a, b, (size_t) la) == 0);
    free(a);
    free(b);
}

/* DbTesterStream.testLargeTransactions and testLargeTransaction: five values of
 * 1,000,000 to 1,000,004 bytes, each its own transaction, between two small ones, at a
 * startup distance of 100,000 bytes; and one of 20,000,000 bytes, across 100 meta
 * blocks, after two small ones: after a restart every value is there, byte for byte. */
TEST(func_restart_large_values) {
    char dir[1024], errbuf[BERGDB_ERRBUF_SIZE];
    struct bergdb_mem m = {0};
    struct bergdb_test_clock clock = {0};
    struct bergdb_options o;
    bergdb_db *db;
    const size_t big = 20 * 1000 * 1000;
    uint8_t *v = malloc(big);
    REQUIRE(v != NULL);
    for (size_t i = 0; i < big; i++) {
        v[i] = (uint8_t) (i * 7 + (i >> 13));
    }
    for (int round = 0; round < 2; round++) {
        fr_temp_dir(dir, sizeof dir);
        REQUIRE(dir[0] != '\0');
        fr_options(&o, &clock, &m, round == 0 ? 100 * 1000 : 1000 * 1000);
        memset(&clock, 0, sizeof clock);
        REQUIRE(bergdb_open(dir, &o, &db, NULL, errbuf) == BERGDB_OK);
        if (round == 0) {
            CHECK_EQ(fr_put(db, &clock, 10, "/small1", (const uint8_t *) "v-small1", 8),
                    BERGDB_OK);
            for (int i = 0; i < 5; i++) {
                char key[32];
                snprintf(key, sizeof key, "/large-%d", i);
                CHECK_EQ(fr_put(db, &clock, 20 + i, key, v + i, (size_t) (1000 * 1000 + i)),
                        BERGDB_OK);
            }
            CHECK_EQ(fr_put(db, &clock, 30, "/small2", (const uint8_t *) "v-small2", 8),
                    BERGDB_OK);
        } else {
            CHECK_EQ(fr_put(db, &clock, 10, "/a", (const uint8_t *) "a", 1), BERGDB_OK);
            CHECK_EQ(fr_put(db, &clock, 20, "/b", (const uint8_t *) "b", 1), BERGDB_OK);
            CHECK_EQ(fr_put(db, &clock, 30, "/large", v, big), BERGDB_OK);
        }
        CHECK_EQ(bergdb_close(db), BERGDB_OK);
        REQUIRE(bergdb_open(dir, &o, &db, NULL, errbuf) == BERGDB_OK);
        if (round == 0) {
            CHECK(fr_value_is(db, "/small1", (const uint8_t *) "v-small1", 8));
            CHECK(fr_value_is(db, "/small2", (const uint8_t *) "v-small2", 8));
            for (int i = 0; i < 5; i++) {
                char key[32];
                snprintf(key, sizeof key, "/large-%d", i);
                CHECK(fr_value_is(db, key, v + i, (size_t) (1000 * 1000 + i)));
            }
        } else {
            CHECK(fr_value_is(db, "/a", (const uint8_t *) "a", 1));
            CHECK(fr_value_is(db, "/b", (const uint8_t *) "b", 1));
            CHECK(fr_value_is(db, "/large", v, big));
        }
        CHECK_EQ(bergdb_close(db), BERGDB_OK);
        CHECK_EQ(m.live_total, 0);
        fr_remove_dir(dir);
    }
    free(v);
}

const struct test restart_func_tests[] = {
    TEST_ENTRY(func_restart_same_stream_after_decrease),
    TEST_ENTRY(func_restart_large_values),
    TEST_END
};
