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

int64_t dbclock_current_time(struct dbclock *c) {
    int64_t time;

    if (c->transactionRunning) {
        time = c->transactionTime - 1;
    } else {
        time = get_time(c);
        time = time < c->lastTransactionTime ? c->lastTransactionTime : time;
        c->lastReadTime = time;
    }

    return time;
}

enum err_code dbclock_transaction_begin(struct dbclock *c, int64_t *out, struct err *e) {
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
