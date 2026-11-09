/*
 * core_demo: C's CoreDemo, after bergdb 006-08's CoreDemo.java, against
 * bergdb.h only (bergdb 012-03). It uses the Core Data API (execute, getOne,
 * getMany, getTrans) on a database in a directory, closes it, opens it again
 * and reads again: the reads must be the same.
 *
 * Usage: core_demo DIR    (DIR new or empty)
 *
 * Its output, as CoreDemo.java's:
 *
 *   getOne: apple red then green, banana yellow then null
 *   getMany at the first time: /fruit/apple=red /fruit/banana=yellow
 *   getMany at the latest time: /fruit/apple=green
 *   getTrans: the latest apple's transaction is the second one
 *   CoreDemo OK: the same reads after a restart
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "bergdb.h"

#define TEXT_SIZE 1000

static void check(int ok, const char *message) {
    if (!ok) {
        fprintf(stderr, "core_demo: %s\n", message);
        exit(1);
    }
}

/* Closes the database; stops on an error, which has no text: the database is
 * gone. */
static void close_db(bergdb_db *db) {
    int rc = bergdb_close(db);
    if (rc != BERGDB_OK) {
        fprintf(stderr, "core_demo: close: %s\n", bergdb_errname(rc));
        exit(1);
    }
}

/* Stops on an error, with its name and text. */
static void ok(bergdb_db *db, int rc, const char *what) {
    if (rc != BERGDB_OK) {
        fprintf(stderr, "core_demo: %s: %s: %s\n", what, bergdb_errname(rc), bergdb_errmsg(db));
        exit(1);
    }
}

/* The bkey of an ikey given as a C string (Java's Keys.toBytes(String)); its
 * length in *len. */
static const uint8_t *bkey(const char *ikey, uint8_t *buf, size_t *len) {
    *len = strlen(ikey);
    check(bergdb_ikey_to_bkey((const uint8_t *) ikey, *len, buf) == BERGDB_OK, "bad key");
    return buf;
}

/* Puts or deletes (value NULL) the key, an ikey. */
static void put(bergdb_db *db, bergdb_trans *t, const char *key, const char *value) {
    uint8_t buf[64];
    size_t len;
    const uint8_t *k = bkey(key, buf, &len);
    if (value != NULL) {
        ok(db, bergdb_trans_put(t, k, len, (const uint8_t *) value, strlen(value)), "put");
    } else {
        ok(db, bergdb_trans_delete(t, k, len), "delete");
    }
}

/* Appends to text, as Java's StringBuilder.append. */
static void append(char *text, const char *s) {
    size_t n = strlen(text);
    check(n + strlen(s) < TEXT_SIZE, "text too long");
    memcpy(text + n, s, strlen(s) + 1);
}

/* A value as a string in s (TEXT_SIZE bytes): "null" for none, as Java's
 * string(null) prints. The value is copied at once: it is valid only until
 * the read context's next call. */
static void string(const uint8_t *value, size_t len, char *s) {
    if (value == NULL) {
        strcpy(s, "null");
        return;
    }
    check(len < TEXT_SIZE, "value too long");
    memcpy(s, value, len);
    s[len] = 0;
}

/* getOne of an ikey at a time, as a string in s; the value's tpos in *tpos. */
static void get_one(bergdb_db *db, bergdb_read *rd, int64_t time, const char *key, char *s,
        int64_t *tpos) {
    uint8_t buf[64];
    size_t len;
    const uint8_t *k = bkey(key, buf, &len);
    struct bergdb_one one;
    ok(db, bergdb_get_one(db, rd, time, k, len, &one), "getOne");
    string(one.value, one.value_len, s);
    *tpos = one.tpos;
}

/* The reads, checked, as text: getOne at both times, getMany, getTrans. */
static void read_all(bergdb_db *db, int64_t time1, int64_t time2, char *text) {
    char apple1[TEXT_SIZE], apple2[TEXT_SIZE], banana1[TEXT_SIZE], banana2[TEXT_SIZE];
    char line[TEXT_SIZE];
    int64_t tpos, unused;
    bergdb_read *rd;

    text[0] = 0;
    ok(db, bergdb_read_new(db, &rd), "newGetData");
    get_one(db, rd, time1, "/fruit/apple", apple1, &unused);
    get_one(db, rd, BERGDB_LATEST, "/fruit/apple", apple2, &tpos);
    get_one(db, rd, time1, "/fruit/banana", banana1, &unused);
    get_one(db, rd, BERGDB_LATEST, "/fruit/banana", banana2, &unused);
    check(strcmp(apple1, "red") == 0 && strcmp(apple2, "green") == 0, "apple");
    check(strcmp(banana1, "yellow") == 0 && strcmp(banana2, "null") == 0, "banana");
    snprintf(line, sizeof line, "getOne: apple %s then %s, banana %s then %s\n",
            apple1, apple2, banana1, banana2);
    append(text, line);

    int64_t times[2] = { time1, BERGDB_LATEST };
    for (int i = 0; i < 2; i++) {
        struct bergdb_range r;
        struct bergdb_many many;
        char kvs[TEXT_SIZE] = "";
        bergdb_range_init(&r);
        r.lookup_time = times[i];
        ok(db, bergdb_get_many(db, rd, &r, &many), "getMany");
        for (size_t j = 0; j < many.count; j++) {
            const struct bergdb_kvt *kvt = &many.kvts[j];
            char key[TEXT_SIZE], value[TEXT_SIZE];
            check(kvt->key_len < TEXT_SIZE, "key too long");
            check(bergdb_bkey_to_ikey(kvt->key, kvt->key_len, (uint8_t *) key) == BERGDB_OK,
                    "a key without an ikey");                       /* Keys.toString */
            key[kvt->key_len] = 0;
            string(kvt->value, kvt->value_len, value);
            snprintf(line, sizeof line, " %s=%s", key, value);
            append(kvs, line);
        }
        check(many.count == (i == 0 ? 2u : 1u), kvs);
        snprintf(line, sizeof line, "getMany at %s:%s\n",
                i == 0 ? "the first time" : "the latest time", kvs);
        append(text, line);
    }

    struct bergdb_stored t;
    ok(db, bergdb_get_trans(db, rd, tpos, &t), "getTrans");
    check(t.tt == time2, "getTrans: another time");
    append(text, "getTrans: the latest apple's transaction is the second one\n");
    bergdb_read_free(rd);
}

int main(int argc, char **argv) {
    char errbuf[BERGDB_ERRBUF_SIZE];
    char before[TEXT_SIZE], after[TEXT_SIZE];
    struct bergdb_executed first, second;
    bergdb_db *db;
    bergdb_trans *t;

    if (argc != 2) {
        fprintf(stderr, "Usage: core_demo DIR\n");
        return 2;
    }

    /* Db.builder().mainStream(new FileStream(dir)).start(): the defaults. */
    if (bergdb_open(argv[1], NULL, &db, NULL, errbuf) != BERGDB_OK) {
        fprintf(stderr, "core_demo: open: %s\n", errbuf);
        return 1;
    }
    ok(db, bergdb_trans_new(db, &t), "trans");
    put(db, t, "/fruit/apple", "red");
    put(db, t, "/fruit/banana", "yellow");
    ok(db, bergdb_execute(db, t, &first), "execute");
    bergdb_trans_free(t);
    ok(db, bergdb_trans_new(db, &t), "trans");
    put(db, t, "/fruit/apple", "green");
    put(db, t, "/fruit/banana", NULL);
    ok(db, bergdb_execute(db, t, &second), "execute");
    bergdb_trans_free(t);
    ok(db, bergdb_sync(db, 0, BERGDB_SYNC_ORDINARY), "sync");
    read_all(db, first.tt, second.tt, before);
    close_db(db);

    if (bergdb_open(argv[1], NULL, &db, NULL, errbuf) != BERGDB_OK) {
        fprintf(stderr, "core_demo: open again: %s\n", errbuf);
        return 1;
    }
    read_all(db, first.tt, second.tt, after);
    close_db(db);

    fputs(before, stdout);
    check(strcmp(before, after) == 0, "the reads after the restart differ");
    printf("CoreDemo OK: the same reads after a restart\n");
    return 0;
}
