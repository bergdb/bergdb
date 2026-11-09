/* Unit tests of clock (bergdb 012-09, part 1): Java's @Nano tests of
 * DbClock, ported, and the rules of 012-01, 4.4: the test clock, the
 * system clock as SystemClock's code is (005-69), currentTime moving the
 * next transaction's time, the range of 005-18. */
#include "test.h"
#include "bergdb.h"
#include "clock.h"
#include "klong.h"

#define F INT64_C(10000)       /* DbClock's tests' factor "F" */

/* DbClock.test1. */
TEST(clock_dbclock_test1) {
    struct bergdb_test_clock testClock = { 0 };
    struct dbclock dbClock;
    struct err e;
    int64_t transactionTime = -1;

    dbclock_init(&dbClock, bergdb_test_clock_time, &testClock);
    CHECK_EQ(bergdb_test_clock_set(&testClock, 1 * F), BERGDB_OK);
    CHECK_EQ(dbclock_transaction_begin(&dbClock, true, &transactionTime, &e), ERR_OK);
    dbclock_transaction_end(&dbClock);

    CHECK_EQ(transactionTime, 1 * F);
}

/* DbClock.testTime. */
TEST(clock_dbclock_time) {
    struct bergdb_test_clock testClock = { 0 };
    struct dbclock dbClock;
    struct err e;
    int64_t transactionTime = -1;

    dbclock_init(&dbClock, bergdb_test_clock_time, &testClock);
    CHECK_EQ(bergdb_test_clock_set(&testClock, 1 * F), BERGDB_OK);

    int64_t time1 = dbclock_current_time(&dbClock);
    int64_t time2 = dbclock_current_time(&dbClock);
    CHECK_EQ(dbclock_transaction_begin(&dbClock, true, &transactionTime, &e), ERR_OK);
    int64_t time3 = dbclock_current_time(&dbClock);
    dbclock_transaction_end(&dbClock);
    int64_t time4 = dbclock_current_time(&dbClock);

    CHECK_EQ(time1, 1 * F);
    CHECK_EQ(time2, 1 * F);
    CHECK_EQ(time3, 1 * F);
    CHECK_EQ(time4, 1 * F + 1);
    CHECK_EQ(transactionTime, 1 * F + 1);
}

/* DbClock.testClockOutOfRange (005-18), with Java's texts. */
TEST(clock_dbclock_out_of_range) {
    struct bergdb_test_clock testClock = { 0 };
    struct dbclock dbClock;
    struct err e;
    int64_t t = -1;

    dbclock_init(&dbClock, bergdb_test_clock_time, &testClock);
    CHECK_EQ(bergdb_test_clock_set(&testClock, KL_MAX_TIME + 1), BERGDB_OK);
    CHECK_EQ(dbclock_transaction_begin(&dbClock, true, &t, &e), ERR_LIMIT);
    CHECK(strcmp(e.java, "DbException") == 0);
    CHECK(strstr(e.text, "outside the range") != NULL);
    CHECK_EQ(t, -1);
    /* Refused before it began: nothing changed, no transaction runs. */
    CHECK(!dbClock.transactionRunning);
    CHECK_EQ(dbClock.lastTransactionTime, 0);

    struct bergdb_test_clock testClock2 = { 0 };
    struct dbclock dbClock2;
    CHECK_EQ(bergdb_test_clock_set(&testClock2, 1000), BERGDB_OK);
    dbclock_init(&dbClock2, bergdb_test_clock_time, &testClock2);
    dbclock_set_last_trans_time(&dbClock2, KL_MAX_TIME);
    CHECK_EQ(dbclock_transaction_begin(&dbClock2, true, &t, &e), ERR_LIMIT);
    CHECK(strstr(e.text, "No database time is left") != NULL);
    CHECK(!dbClock2.transactionRunning);

    /* The largest time is given, to an internal transaction (015-55); a
     * negative clock time is refused. */
    struct bergdb_test_clock c3 = { 0 };
    struct dbclock d3;
    dbclock_init(&d3, bergdb_test_clock_time, &c3);
    CHECK_EQ(bergdb_test_clock_set(&c3, KL_MAX_TIME), BERGDB_OK);
    CHECK_EQ(dbclock_transaction_begin(&d3, false, &t, &e), ERR_OK);
    CHECK_EQ(t, KL_MAX_TIME);
    dbclock_transaction_end(&d3);
    c3.time = -5;       /* a caller's clock may give anything */
    CHECK_EQ(dbclock_transaction_begin(&d3, true, &t, &e), ERR_LIMIT);
    CHECK(strstr(e.text, "The clock's time, -5, is outside the range of database times, 0 to "
            "72057594037927935") != NULL);
}

/* DbClock.testTimeMarginForInternal (bergdb 015-55): a user transaction is
 * refused after LAST_USER_TIME, and an internal one, reclaim's after it,
 * still has a time, up to Klong.MAX_TIME; with Java's text. */
TEST(clock_dbclock_time_margin_for_internal) {
    struct bergdb_test_clock testClock = { 0 };
    struct dbclock dbClock;
    struct err e;
    int64_t t = -1;

    CHECK_EQ(DBCLOCK_LAST_USER_TIME, KL_MAX_TIME - 1024);
    dbclock_init(&dbClock, bergdb_test_clock_time, &testClock);
    CHECK_EQ(bergdb_test_clock_set(&testClock, DBCLOCK_LAST_USER_TIME), BERGDB_OK);
    CHECK_EQ(dbclock_transaction_begin(&dbClock, true, &t, &e), ERR_OK);
    CHECK_EQ(t, DBCLOCK_LAST_USER_TIME);
    dbclock_transaction_end(&dbClock);
    CHECK_EQ(dbclock_transaction_begin(&dbClock, false, &t, &e), ERR_OK);
    CHECK_EQ(t, DBCLOCK_LAST_USER_TIME + 1);
    dbclock_transaction_end(&dbClock);
    t = -1;
    CHECK_EQ(dbclock_transaction_begin(&dbClock, true, &t, &e), ERR_LIMIT);
    CHECK(strcmp(e.java, "DbException") == 0);
    CHECK(strcmp(e.text, "No database time is left for a user transaction: its time would be "
            "72057594037926913, after the last, 72057594037926911 (the times up to "
            "72057594037927935 are kept for reclaim's internal transactions). No transaction "
            "is executed.") == 0);
    CHECK_EQ(t, -1);
    CHECK(!dbClock.transactionRunning);
    CHECK_EQ(dbClock.lastTransactionTime, DBCLOCK_LAST_USER_TIME + 1);
    dbclock_set_last_trans_time(&dbClock, KL_MAX_TIME - 1);
    CHECK_EQ(dbclock_transaction_begin(&dbClock, false, &t, &e), ERR_OK);
    CHECK_EQ(t, KL_MAX_TIME);
    dbclock_transaction_end(&dbClock);
}

/* DbClock.testLookupTime. */
TEST(clock_dbclock_lookup_time) {
    struct bergdb_test_clock testClock = { 0 };
    struct dbclock dbClock;
    struct err e;
    int64_t t;

    dbclock_init(&dbClock, bergdb_test_clock_time, &testClock);
    CHECK_EQ(bergdb_test_clock_set(&testClock, 1 * F), BERGDB_OK);
    CHECK_EQ(dbclock_transaction_begin(&dbClock, true, &t, &e), ERR_OK);
    dbclock_transaction_end(&dbClock);
    CHECK_EQ(bergdb_test_clock_set(&testClock, 2 * F), BERGDB_OK);

    CHECK_EQ(dbclock_lookup_time(&dbClock, 100), 100);
    CHECK_EQ(dbclock_lookup_time(&dbClock, INT64_MAX), 1 * F);
    CHECK_EQ(dbclock_lookup_time(&dbClock, 1 * F), 1 * F);

    CHECK_EQ(dbclock_transaction_begin(&dbClock, true, &t, &e), ERR_OK);

    CHECK_EQ(dbclock_lookup_time(&dbClock, 100), 100);
    CHECK_EQ(dbclock_lookup_time(&dbClock, INT64_MAX), 1 * F);
    CHECK_EQ(dbclock_lookup_time(&dbClock, 1 * F), 1 * F);

    dbclock_transaction_end(&dbClock);

    CHECK_EQ(dbclock_lookup_time(&dbClock, 100), 100);
    CHECK_EQ(dbclock_lookup_time(&dbClock, INT64_MAX), 2 * F);
    CHECK_EQ(dbclock_lookup_time(&dbClock, 1 * F), 1 * F);
}

/* 012-01, 4.4: a transaction's time is later than the last transaction's
 * and the last currentTime's, so a call of currentTime moves the next
 * transaction's time when the clock has not moved; the creation reads the
 * clock the same way with both at 0, so its time is at least 1. */
TEST(clock_dbclock_rules) {
    struct bergdb_test_clock c = { 0 };
    struct dbclock d;
    struct err e;
    int64_t t;

    dbclock_init(&d, bergdb_test_clock_time, &c);
    CHECK_EQ(dbclock_transaction_begin(&d, true, &t, &e), ERR_OK);       /* the clock at 0 */
    CHECK_EQ(t, 1);
    dbclock_transaction_end(&d);

    CHECK_EQ(bergdb_test_clock_set(&c, 500), BERGDB_OK);
    CHECK_EQ(dbclock_transaction_begin(&d, true, &t, &e), ERR_OK);
    CHECK_EQ(t, 500);
    dbclock_transaction_end(&d);
    /* The clock has not moved: the last transaction's time + 1. */
    CHECK_EQ(dbclock_transaction_begin(&d, true, &t, &e), ERR_OK);
    CHECK_EQ(t, 501);
    dbclock_transaction_end(&d);

    /* currentTime: the clock's time, but at least the last transaction's. */
    CHECK_EQ(dbclock_current_time(&d), 501);
    CHECK_EQ(bergdb_test_clock_set(&c, 600), BERGDB_OK);
    CHECK_EQ(dbclock_current_time(&d), 600);
    /* ... and the next transaction is later than it: 601, not 600. */
    CHECK_EQ(dbclock_transaction_begin(&d, true, &t, &e), ERR_OK);
    CHECK_EQ(t, 601);
    dbclock_transaction_end(&d);

    /* A start sets the last transaction's time only (C3, 005-71): the
     * last read time stays as it is. */
    struct dbclock d2;
    dbclock_init(&d2, bergdb_test_clock_time, &c);
    dbclock_set_last_trans_time(&d2, 601);
    CHECK_EQ(d2.lastReadTime, 0);
    CHECK_EQ(dbclock_transaction_begin(&d2, true, &t, &e), ERR_OK);
    CHECK_EQ(t, 602);
    dbclock_transaction_end(&d2);
}

/* A clock that the test sets to any time, back too (DbClock's tests' "now"). */
static int64_t now_time(void *ctx) {
    return *(const int64_t *) ctx;
}

/* DbClock.testClockGoesBack (bergdb 020-23, Z1): a clock that goes back
 * never takes back a time that currentTime gave: a later currentTime gives
 * that time or a later one, and a later transaction a later time. The
 * second currentTime gave the clock's earlier time and kept it as the last
 * read time, and the transaction then took a time before the first one. */
TEST(clock_dbclock_clock_goes_back) {
    int64_t now = 1000;
    struct dbclock d;
    struct err e;
    int64_t t = -1;
    dbclock_init(&d, now_time, &now);
    CHECK_EQ(dbclock_transaction_begin(&d, true, &t, &e), ERR_OK);
    CHECK_EQ(t, 1000);
    dbclock_transaction_end(&d);
    now = 2000;
    CHECK_EQ(dbclock_current_time(&d), 2000);
    now = 1500;
    CHECK_EQ(dbclock_current_time(&d), 2000);
    CHECK_EQ(dbclock_transaction_begin(&d, true, &t, &e), ERR_OK);
    CHECK_EQ(t, 2001);
    dbclock_transaction_end(&d);
    CHECK_EQ(dbclock_current_time(&d), 2001);
    now = 3000;
    CHECK_EQ(dbclock_current_time(&d), 3000);
}

/* DbClock.testCurrentTimeLeavesTheMargin (bergdb 020-23, Z1): currentTime
 * gives no time after LAST_USER_TIME but a transaction's, also with the
 * clock after it or out of range, so that the times kept for reclaim's
 * internal transactions after a user transaction stay theirs (015-55). It
 * gave the clock's time, Klong.MAX_TIME, and an internal transaction after
 * it had no time left. */
TEST(clock_dbclock_current_time_leaves_the_margin) {
    int64_t now = DBCLOCK_LAST_USER_TIME - 1;
    struct dbclock d;
    struct err e;
    int64_t t = -1;
    dbclock_init(&d, now_time, &now);
    CHECK_EQ(dbclock_transaction_begin(&d, true, &t, &e), ERR_OK);
    CHECK_EQ(t, DBCLOCK_LAST_USER_TIME - 1);
    dbclock_transaction_end(&d);
    now = KL_MAX_TIME;
    CHECK_EQ(dbclock_current_time(&d), DBCLOCK_LAST_USER_TIME);
    now = KL_MAX_TIME + 1;
    CHECK_EQ(dbclock_current_time(&d), DBCLOCK_LAST_USER_TIME);
    now = DBCLOCK_LAST_USER_TIME - 5;
    for (int64_t i = 1; i <= DBCLOCK_TIME_MARGIN; i++) {
        CHECK_EQ(dbclock_transaction_begin(&d, false, &t, &e), ERR_OK);
        CHECK_EQ(t, DBCLOCK_LAST_USER_TIME + i);
        dbclock_transaction_end(&d);
        CHECK_EQ(dbclock_current_time(&d), DBCLOCK_LAST_USER_TIME + i);
    }
}

/* DbUtil.dbTimeToUtc (bergdb 020-24, U1-12): Java's strings,
 * DbUtil.testDbTimeToUtc's three and twenty edges, as Java's DbUtil gave
 * them for these times (2026-11-09, the pin of 022-02): the division toward
 * zero, the millisecond before 1970, the years 1 and 0 (1 BC, the year of
 * the era 1), 9999 and 10000 ('+'), a year BC, the leap day of 2000, 1900,
 * and both ends of a long. */
TEST(clock_time_to_utc) {
    static const struct { int64_t time; const char *utc; } cases[] = {
        { 0, "1970-01-01 00:00:00.000 UTC" },
        { INT64_C(14080262741234567), "2014-08-14 14:24:34.123 UTC" },
        { (INT64_C(1) << 56) - 1, "2198-05-04 23:50:03.792 UTC" },
        { 1, "1970-01-01 00:00:00.000 UTC" },
        { -1, "1970-01-01 00:00:00.000 UTC" },
        { 9999, "1970-01-01 00:00:00.000 UTC" },
        { -9999, "1970-01-01 00:00:00.000 UTC" },
        { -10000, "1969-12-31 23:59:59.999 UTC" },
        { -10001, "1969-12-31 23:59:59.999 UTC" },
        { (INT64_C(1) << 56) - 1025, "2198-05-04 23:50:03.792 UTC" },
        { INT64_MAX, "+31197-09-14 02:48:05.477 UTC" },
        { INT64_MIN, "+27259-04-19 21:11:54.523 UTC" },
        { INT64_MIN + 1, "+27259-04-19 21:11:54.523 UTC" },
        { INT64_C(-621355968000000000), "0001-01-01 00:00:00.000 UTC" },
        { INT64_C(-621355968000000001), "0001-01-01 00:00:00.000 UTC" },
        { INT64_C(-621672192000000000), "0001-01-01 00:00:00.000 UTC" },
        { INT64_C(-621672192000000001), "0001-01-01 00:00:00.000 UTC" },
        { INT64_C(2534023007999999999), "9999-12-31 23:59:59.999 UTC" },
        { INT64_C(2534023008000000000), "+10000-01-01 00:00:00.000 UTC" },
        { INT64_C(-1576800000000000000), "3028-04-27 00:00:00.000 UTC" },
        { INT64_C(9517824000000000), "2000-02-29 00:00:00.000 UTC" },
        { INT64_C(9518687999999999), "2000-02-29 23:59:59.999 UTC" },
        { INT64_C(-22089888000000000), "1900-01-01 00:00:00.000 UTC" },
    };
    for (size_t i = 0; i < sizeof cases / sizeof cases[0]; i++) {
        char utc[CLK_UTC_SIZE];
        clk_time_to_utc(cases[i].time, utc);
        CHECK(strcmp(utc, cases[i].utc) == 0);
        if (strcmp(utc, cases[i].utc) != 0) {
            printf("  %lld: \"%s\", Java's \"%s\"\n", (long long) cases[i].time, utc,
                    cases[i].utc);
        }
    }
}

/* CoreTestClock: forward only, 0 at first, no range of its own (DbClock
 * refuses a time out of range). */
TEST(clock_test_clock) {
    struct bergdb_test_clock c = { 0 };
    CHECK_EQ(bergdb_test_clock_time(&c), 0);
    CHECK_EQ(bergdb_test_clock_set(&c, 0), BERGDB_ARG);
    CHECK_EQ(bergdb_test_clock_set(&c, -1), BERGDB_ARG);
    CHECK_EQ(bergdb_test_clock_set(&c, 7), BERGDB_OK);
    CHECK_EQ(bergdb_test_clock_time(&c), 7);
    CHECK_EQ(bergdb_test_clock_set(&c, 7), BERGDB_ARG);
    CHECK_EQ(bergdb_test_clock_time(&c), 7);
    CHECK_EQ(bergdb_test_clock_set(&c, INT64_MAX), BERGDB_OK);
    CHECK_EQ(bergdb_test_clock_set(NULL, 1), BERGDB_ARG);
}

/* SystemClock (bergdb 005-69): milliseconds times 10,000, strictly
 * increasing; SystemClock.testStrictlyIncreasing (100,000 calls in a row,
 * each later than the one before) and testClockSetBack (a system time equal
 * to the last one, or earlier, gives the last time plus one, until the
 * system clock passes it). */
TEST(clock_system_clock) {
    struct clk_system s = { 0 };
    int64_t a = clk_system_time(&s);
    CHECK(a % 10000 == 0);
    CHECK(a > INT64_C(1700000000000) * 10000);      /* after 2023 */
    CHECK(a < KL_MAX_TIME);
    CHECK_EQ(s.lastTime, a);
    int64_t last = a;
    for (int i = 0; i < 100 * 1000; i++) {
        const int64_t time = clk_system_time(&s);
        if (time <= last) {
            CHECK_EQ(time, last + 1);               /* fails, with both */
            break;
        }
        last = time;
    }
    struct clk_system b = { 0 };
    CHECK_EQ(clk_system_time_at(&b, 1000), 1000 * INT64_C(10000));
    CHECK_EQ(clk_system_time_at(&b, 1000), 1000 * INT64_C(10000) + 1);
    CHECK_EQ(clk_system_time_at(&b, 999), 1000 * INT64_C(10000) + 2);
    CHECK_EQ(clk_system_time_at(&b, 2000), 2000 * INT64_C(10000));
    CHECK_EQ(clk_system_time_at(&b, 0), 2000 * INT64_C(10000) + 1);
    /* A last time at or above the system's: it counts up from there. */
    s.lastTime = KL_MAX_TIME - 10;
    CHECK_EQ(clk_system_time(&s), KL_MAX_TIME - 9);
    CHECK_EQ(clk_system_time(&s), KL_MAX_TIME - 8);

    /* The default of a DbClock: transaction times from the system's, and
     * strictly increasing in any case. */
    struct dbclock d;
    struct err e;
    int64_t t1, t2;
    dbclock_init(&d, NULL, NULL);
    CHECK_EQ(dbclock_transaction_begin(&d, true, &t1, &e), ERR_OK);
    dbclock_transaction_end(&d);
    CHECK_EQ(dbclock_transaction_begin(&d, true, &t2, &e), ERR_OK);
    dbclock_transaction_end(&d);
    CHECK(t1 >= a);
    CHECK(t2 > t1);
}

const struct test clock_tests[] = {
    TEST_ENTRY(clock_dbclock_test1),
    TEST_ENTRY(clock_dbclock_time),
    TEST_ENTRY(clock_dbclock_out_of_range),
    TEST_ENTRY(clock_dbclock_time_margin_for_internal),
    TEST_ENTRY(clock_dbclock_lookup_time),
    TEST_ENTRY(clock_dbclock_rules),
    TEST_ENTRY(clock_dbclock_clock_goes_back),
    TEST_ENTRY(clock_dbclock_current_time_leaves_the_margin),
    TEST_ENTRY(clock_time_to_utc),
    TEST_ENTRY(clock_test_clock),
    TEST_ENTRY(clock_system_clock),
    TEST_END
};
