/* clock: ported from Java's DbClock, SystemClock and CoreTestClock; see
 * clock.h. */
#include "clock.h"
#include <assert.h>
#include <stddef.h>
#include "bergdb.h"
#include "klong.h"
#include "plat.h"

int64_t clk_system_time(void *ctx) {
    return clk_system_time_at(ctx, plat_time_millis());
}

int64_t clk_system_time_at(struct clk_system *c, int64_t millis) {
    int64_t time = millis * 10 * 1000;
    if (time <= c->lastTime) {
        c->lastTime++;
        time = c->lastTime;
    } else {
        c->lastTime = time;     /* bergdb 005-69 */
    }
    return time;
}

/* CoreTestClock.getTime. */
int64_t bergdb_test_clock_time(void *ctx) {
    const struct bergdb_test_clock *c = ctx;
    return c->time;
}

/* CoreTestClock.setTime: "Bad time, must be larger than current time". */
int bergdb_test_clock_set(struct bergdb_test_clock *clock, int64_t time) {
    if (clock == NULL || time <= clock->time) {
        return BERGDB_ARG;
    }
    clock->time = time;
    return BERGDB_OK;
}

/* Writes v's decimal digits, at least width of them, at *p. */
static void put_digits(char **p, int64_t v, int width) {
    char d[24];
    int n = 0;
    do {
        d[n++] = (char) ('0' + v % 10);
        v /= 10;
    } while (v > 0);
    while (n < width) {
        d[n++] = '0';
    }
    while (n > 0) {
        *(*p)++ = d[--n];
    }
}

/* Java's Math.floorDiv and floorMod of a long by a positive long. */
static int64_t floor_div(int64_t a, int64_t b) {
    int64_t q = a / b;
    return (a % b != 0 && a < 0) ? q - 1 : q;
}

static int64_t floor_mod(int64_t a, int64_t b) {
    return a - floor_div(a, b) * b;
}

void clk_time_to_utc(int64_t time, char *out) {
    const int64_t ms = time / 10000;                /* Clock.UNITS_PER_SEC / 1000 */
    const int64_t secs = floor_div(ms, 1000);       /* Instant.ofEpochMilli */
    const int64_t milli = floor_mod(ms, 1000);
    const int64_t days = floor_div(secs, 86400);
    const int64_t sod = floor_mod(secs, 86400);
    /* The civil date of days since 1970-01-01 (LocalDate.ofEpochDay's
     * proleptic Gregorian calendar; the algorithm of eras of 400 years). */
    const int64_t z = days + 719468;
    const int64_t era = floor_div(z, 146097);
    const int64_t doe = z - era * 146097;
    const int64_t yoe = (doe - doe / 1460 + doe / 36524 - doe / 146096) / 365;
    const int64_t doy = doe - (365 * yoe + yoe / 4 - yoe / 100);
    const int64_t mp = (5 * doy + 2) / 153;
    const int64_t day = doy - (153 * mp + 2) / 5 + 1;
    const int64_t month = mp < 10 ? mp + 3 : mp - 9;
    const int64_t year = yoe + era * 400 + (month <= 2 ? 1 : 0);
    const int64_t yearOfEra = year >= 1 ? year : 1 - year;
    char *p = out;
    if (yearOfEra > 9999) {
        *p++ = '+';
    }
    put_digits(&p, yearOfEra, 4);
    *p++ = '-';
    put_digits(&p, month, 2);
    *p++ = '-';
    put_digits(&p, day, 2);
    *p++ = ' ';
    put_digits(&p, sod / 3600, 2);
    *p++ = ':';
    put_digits(&p, sod / 60 % 60, 2);
    *p++ = ':';
    put_digits(&p, sod % 60, 2);
    *p++ = '.';
    put_digits(&p, milli, 3);
    const char *utc = " UTC";
    while (*utc != '\0') {
        *p++ = *utc++;
    }
    *p = '\0';
}

void dbclock_init(struct dbclock *c, clk_fn clock, void *ctx) {
    c->clock = clock;
    c->ctx = ctx;
    c->system.lastTime = 0;
    c->lastTransactionTime = 0;
    c->transactionTime = 0;
    c->lastReadTime = 0;
    c->transactionRunning = false;
}

static int64_t get_time(struct dbclock *c) {
    return c->clock == NULL ? clk_system_time(&c->system) : c->clock(c->ctx);
}

int64_t dbclock_lookup_time(const struct dbclock *c, int64_t wantedLookupTime) {
    const int64_t last = c->lastTransactionTime;
    int64_t result = wantedLookupTime > last ? last : wantedLookupTime;
    return result;
}

/* bergdb 020-23, Z1 (as Java's since release 2026.4): lastReadTime never
 * decreases. A clock that went back set it to its earlier time, so that a
 * later transaction could take a time before a time returned, and a read at
 * that time changed. The clock's time is taken at most as LAST_USER_TIME: a
 * user transaction after that is refused anyway, and a time in the margin,
 * or out of range, would take the times kept for reclaim's internal
 * transactions after a user's (bergdb 015-55). */
int64_t dbclock_current_time(struct dbclock *c) {
    int64_t time;

    if (c->transactionRunning) {
        time = c->transactionTime - 1;
    } else {
        time = get_time(c);
        time = time > DBCLOCK_LAST_USER_TIME ? DBCLOCK_LAST_USER_TIME : time;
        time = time < c->lastTransactionTime ? c->lastTransactionTime : time;
        time = time < c->lastReadTime ? c->lastReadTime : time;
        c->lastReadTime = time;
    }

    return time;
}

enum err_code dbclock_transaction_begin(struct dbclock *c, bool user, int64_t *out,
        struct err *e) {
    assert(!c->transactionRunning);
    const int64_t clockTime = get_time(c);
    int64_t time = clockTime;
    time = time > c->lastTransactionTime ? time : c->lastTransactionTime + 1;
    time = time > c->lastReadTime ? time : c->lastReadTime + 1;

    /* 2026-10-21 (bergdb 005-18): a time outside 0 to 2^56 - 1 is refused
     * before the transaction begins. */
    if (clockTime < KL_MIN_TIME || clockTime > KL_MAX_TIME) {
        return err_set(e, ERR_LIMIT, "DbException", "The clock's time, %lld, is outside the "
                "range of database times, 0 to %lld (100 ns units since 1970; see "
                "Clock.getTime). No transaction is executed.", (long long) clockTime,
                (long long) KL_MAX_TIME);
    }
    if (time > KL_MAX_TIME) {
        return err_set(e, ERR_LIMIT, "DbException", "No database time is left after %lld; the "
                "largest is %lld. No transaction is executed.", (long long) (time - 1),
                (long long) KL_MAX_TIME);
    }
    /* 2026-11-05 (bergdb 015-55): a user transaction leaves the last times
     * to reclaim's internal transactions after it, which run after its go
     * point; one of them that found no time left failed the database. */
    if (user && time > DBCLOCK_LAST_USER_TIME) {
        return err_set(e, ERR_LIMIT, "DbException", "No database time is left for a user "
                "transaction: its time would be %lld, after the last, %lld (the times up to "
                "%lld are kept for reclaim's internal transactions). No transaction is "
                "executed.", (long long) time, (long long) DBCLOCK_LAST_USER_TIME,
                (long long) KL_MAX_TIME);
    }

    c->transactionTime = time;
    c->transactionRunning = true;
    assert(c->transactionTime > 0);
    *out = time;
    return ERR_OK;
}

void dbclock_transaction_end(struct dbclock *c) {
    assert(c->transactionRunning);
    c->lastTransactionTime = c->transactionTime;
    c->transactionRunning = false;
}

void dbclock_set_last_trans_time(struct dbclock *c, int64_t lastTransTime) {
    assert(!c->transactionRunning);
    c->lastTransactionTime = lastTransTime;
}
