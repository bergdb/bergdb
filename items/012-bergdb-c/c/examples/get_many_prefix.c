/*
 * get_many_prefix: getMany with a prefix, against bergdb.h only (bergdb
 * 012-03). A database in memory, on the test clock and with Java's test id,
 * so that its times and bytes are the same in every run; the keys of one
 * user, read with GetMany's Prefix stop condition, then with a count
 * (PrefixN), then backward with a stop condition of the caller's and a
 * count.
 *
 * Usage: get_many_prefix    (prints the pairs; exit status 0)
 *
 * Java's output for the same calls (012-03's probe, on Java's main at
 * d025d95, through Db, GetMany.Prefix, PrefixN and a StopCondition of its
 * own), which this program must print, byte for byte, once it links
 * (012-13):
 *
 *   executed at 10010000000, positions 264 to 679
 *   prefix /user/1/: 3 pairs
 *     /user/1/mail = anna@example.org  (time 10010000000, pos 344)
 *     /user/1/name = Anna  (time 10010000000, pos 404)
 *     /user/1/phone = -  (time 10010000000, pos 452)
 *   prefix /user/1/, at most 2: 2 pairs
 *     /user/1/mail = anna@example.org  (time 10010000000, pos 344)
 *     /user/1/name = Anna  (time 10010000000, pos 404)
 *   backward, without "-", at most 3: 3 pairs
 *     /user/2/name = Cecilia  (time 10010000000, pos 548)
 *     /user/10/name = Bo  (time 10010000000, pos 500)
 *     /user/1/name = Anna  (time 10010000000, pos 404)
 *
 * And, in the same database, a Prefix of "/user/1" from "/user/1"
 * inclusive gives 0 pairs (the key equal to the prefix stops the read),
 * exclusive 4 (with "/user/10/name").
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "bergdb.h"

#define KEY_SIZE 100

static void ok(bergdb_db *db, int rc, const char *what) {
    if (rc != BERGDB_OK) {
        fprintf(stderr, "get_many_prefix: %s: %s: %s\n", what, bergdb_errname(rc),
                bergdb_errmsg(db));
        exit(1);
    }
}

/* The bkey of an ikey given as a C string, in buf; returns its length. */
static size_t bkey(const char *ikey, uint8_t *buf) {
    size_t len = strlen(ikey);
    if (len >= KEY_SIZE || bergdb_ikey_to_bkey((const uint8_t *) ikey, len, buf) != BERGDB_OK) {
        fprintf(stderr, "get_many_prefix: bad key %s\n", ikey);
        exit(1);
    }
    return len;
}

/* Prints the pairs of a getMany, the keys as ikeys. The pairs point into the
 * read context's buffer: valid until its next call. */
static void print(const char *title, const struct bergdb_many *many) {
    printf("%s: %zu pairs%s\n", title, many->count, many->eod ? ", the end of the database" : "");
    for (size_t i = 0; i < many->count; i++) {
        const struct bergdb_kvt *kvt = &many->kvts[i];
        char key[KEY_SIZE];
        bergdb_bkey_to_ikey(kvt->key, kvt->key_len, (uint8_t *) key);
        printf("  %.*s = %.*s  (time %lld, pos %lld)\n", (int) kvt->key_len, key,
                (int) kvt->value_len, (const char *) kvt->value,
                (long long) kvt->time, (long long) kvt->pos);
    }
}

/* A stop condition of the caller's (GetMany.StopCondition): a filter that
 * skips the pairs whose value is "-" (CONTINUE) and adds the others. */
static int skip_dashes(void *ctx, const struct bergdb_kvt *kvt) {
    (void) ctx;
    if (kvt->value_len == 1 && kvt->value[0] == '-') {
        return BERGDB_CONTINUE;
    }
    return BERGDB_ADD;
}

int main(void) {
    static const char *const pairs[][2] = {
        { "/user/1", "-" },             /* the prefix's own key: not read with the prefix */
        { "/user/1/mail", "anna@example.org" },
        { "/user/1/name", "Anna" },
        { "/user/1/phone", "-" },
        { "/user/10/name", "Bo" },      /* "/user/1" is its prefix, "/user/1/" is not */
        { "/user/2/name", "Cecilia" },
    };
    const size_t n = sizeof pairs / sizeof pairs[0];
    struct bergdb_test_clock clock = {0};
    struct bergdb_options opt;
    struct bergdb_executed x;
    struct bergdb_range r;
    struct bergdb_many many;
    char errbuf[BERGDB_ERRBUF_SIZE] = "";
    uint8_t key[KEY_SIZE], prefix[KEY_SIZE];
    bergdb_db *db;
    bergdb_trans *t;
    bergdb_read *rd;

    /* DbBuilder's testSetup(): the test clock, no eviction, retain forever
     * (the default), the test id, and a stream in memory (dir NULL). The
     * creation reads the clock. */
    bergdb_options_init(&opt);
    opt.cache_size_indicator = BERGDB_NO_EVICT;
    opt.clock = bergdb_test_clock_time;
    opt.clock_ctx = &clock;
    memcpy(opt.id, bergdb_test_id, BERGDB_ID_SIZE);
    if (bergdb_test_clock_set(&clock, 1000 * BERGDB_UNITS_PER_SEC) != BERGDB_OK
            || bergdb_open(NULL, &opt, &db, NULL, errbuf) != BERGDB_OK) {
        fprintf(stderr, "get_many_prefix: open: %s\n", errbuf);
        return 1;
    }

    /* One transaction with every pair, at the clock's next second. */
    ok(db, bergdb_test_clock_set(&clock, 1001 * BERGDB_UNITS_PER_SEC), "set the clock");
    ok(db, bergdb_trans_new(db, &t), "trans");
    for (size_t i = 0; i < n; i++) {
        size_t len = bkey(pairs[i][0], key);
        ok(db, bergdb_trans_put(t, key, len, (const uint8_t *) pairs[i][1], strlen(pairs[i][1])),
                "put");
    }
    ok(db, bergdb_execute(db, t, &x), "execute");
    bergdb_trans_free(t);
    printf("executed at %lld, positions %lld to %lld\n", (long long) x.tt, (long long) x.tpos,
            (long long) x.last_pos);

    ok(db, bergdb_read_new(db, &rd), "newGetMany");

    /* The keys under "/user/1/": from the prefix forward, Prefix. The start
     * is the prefix, exclusive: the prefix is a strict prefix of a key it
     * keeps (Keys.isPrefix), so a pair with the prefix itself as key would
     * stop the read at once. */
    size_t prefix_len = bkey("/user/1/", prefix);
    bergdb_range_init(&r);
    r.start_key = prefix;
    r.start_key_len = prefix_len;
    r.inclusive = false;
    r.prefix = prefix;
    r.prefix_len = prefix_len;
    ok(db, bergdb_get_many(db, rd, &r, &many), "getMany");
    print("prefix /user/1/", &many);

    /* The same with a count: PrefixN(prefix, 2). */
    r.max_count = 2;
    ok(db, bergdb_get_many(db, rd, &r, &many), "getMany");
    print("prefix /user/1/, at most 2", &many);

    /* Backward from the last key, at the time of the transaction, with a
     * stop condition of the caller's that skips "-", and a count: at most 3
     * pairs added. */
    bergdb_range_init(&r);
    r.lookup_time = x.tt;
    r.forward = false;
    r.stop = skip_dashes;
    r.max_count = 3;
    ok(db, bergdb_get_many(db, rd, &r, &many), "getMany");
    print("backward, without \"-\", at most 3", &many);

    bergdb_read_free(rd);
    if (bergdb_close(db) != BERGDB_OK) {
        fprintf(stderr, "get_many_prefix: close failed\n");
        return 1;
    }
    return 0;
}
