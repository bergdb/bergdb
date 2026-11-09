/*
 * clock: the database's clock, ported from Java's bergdb.core.DbClock,
 * SystemClock and CoreTestClock (bergdb 012-09, part 1; 012-01, 4.4;
 * 012-02, 2.6 and 8.1). Prefix clk_ (the clocks) and dbclock_ (DbClock).
 *
 * Every time in the stream is a transaction's, from
 * dbclock_transaction_begin, which reads the database's clock once. The
 * only other read is dbclock_current_time (Db.currentTime). Lookup times
 * never read it.
 *
 * A clock is a function and its context (Java's Clock, DbBuilder.clock):
 * the same type as the API's bergdb_clock_fn (include/bergdb.h), so that
 * the options' clock is given as it is. Three clocks:
 *
 *   - the system clock (SystemClock), the default: milliseconds since
 *     1970 times 10,000, from plat_time_millis, strictly increasing: a
 *     system time that is not later than the last time returned gives the
 *     last time plus one, 100 ns later, until the system clock passes it
 *     (bergdb 005-69, as Java's since release 2026.2; before, the last
 *     time stayed 0, and calls within a millisecond, or after the system
 *     clock was set back, gave equal or earlier times). DbClock makes
 *     transaction times increase in any case. Its state is the database's
 *     (struct dbclock), not global (P9);
 *   - the test clock (CoreTestClock): the API's struct bergdb_test_clock,
 *     with bergdb_test_clock_time and bergdb_test_clock_set, implemented
 *     here; a time that the caller sets, forward only;
 *   - a function of the caller's.
 *
 * One caller at a time (012-01, 4.2): none of Java's synchronized and
 * volatile.
 */
#ifndef BERGDB_CLOCK_H
#define BERGDB_CLOCK_H

#include <stdbool.h>
#include <stdint.h>
#include "err.h"
#include "klong.h"

/* Clock.getTime: the time now, in 100 ns units since 1970; the type of the
 * API's bergdb_clock_fn. */
typedef int64_t (*clk_fn)(void *ctx);

#define CLK_UNITS_PER_SEC INT64_C(10000000)     /* Clock.UNITS_PER_SEC */

/* SystemClock's state: its last time, 0 at first. */
struct clk_system {
    int64_t lastTime;
};

/* SystemClock.getTime, ctx a struct clk_system. */
int64_t clk_system_time(void *ctx);

/* SystemClock.getTime(millis): as clk_system_time, with millis as the
 * system's time, in ms since 1970; for the tests. */
int64_t clk_system_time_at(struct clk_system *c, int64_t millis);

/* DbClock. */
struct dbclock {
    clk_fn clock;               /* NULL: the system clock, below */
    void *ctx;
    struct clk_system system;   /* the system clock's state, when clock is NULL */
    int64_t lastTransactionTime;    /* the last completed transaction's time */
    int64_t transactionTime;        /* the running transaction's time */
    int64_t lastReadTime;           /* the last time currentTime returned (C3: 0 at a start) */
    bool transactionRunning;
};

/* DbClock(Clock): the clock and its ctx, or NULL for the system clock
 * (DbBuilder's default, new SystemClock()); the times 0, no transaction
 * running. Java refuses a null clock; here NULL is the default's. */
void dbclock_init(struct dbclock *c, clk_fn clock, void *ctx);

/* DbClock.lookupTime: the wanted lookup time, but at most the last
 * transaction's time. Does not read the clock. */
int64_t dbclock_lookup_time(const struct dbclock *c, int64_t wantedLookupTime);

/* DbClock.currentTime: while a transaction runs, its time minus 1; else
 * the clock's time, at most DBCLOCK_LAST_USER_TIME, or, when that is
 * earlier, the last read time or the last transaction's time, which it
 * keeps as the last read time (so the next transaction's time is later,
 * and the times returned never decrease: bergdb 020-23, Z1, as Java's
 * since release 2026.4). */
int64_t dbclock_current_time(struct dbclock *c);

/* DbUtil.dbTimeToUtc: the time as Java gives it in the texts of a lookup
 * time not available, "yyyy-MM-dd HH:mm:ss.SSS UTC": its milliseconds
 * (time / 10,000, toward zero, Java's division) as an Instant, in the
 * proleptic Gregorian calendar, UTC, the year of the era (a year before 1
 * counts back from 1, as Locale.US's "yyyy"), with a '+' above 9999
 * (DateTimeFormatter's sign for "yyyy"). out holds CLK_UTC_SIZE bytes, the
 * text and its 0. For any time (bergdb 020-24, U1-12). */
#define CLK_UTC_SIZE 40
void clk_time_to_utc(int64_t time, char *out);

/* DbClock.TIME_MARGIN: the database times below 2^56 - 1 that are left when
 * user transactions are refused (bergdb 015-55): room for reclaim's
 * internal transactions after a user transaction, as Db's top ordinal
 * margin (005-02). DBCLOCK_LAST_USER_TIME, LAST_USER_TIME: the last time of
 * a user transaction; the later ones are reclaim's. */
#define DBCLOCK_TIME_MARGIN INT64_C(1024)
#define DBCLOCK_LAST_USER_TIME (KL_MAX_TIME - DBCLOCK_TIME_MARGIN)

/* DbClock.transactionBegin(user): reads the clock once; the time is the
 * clock's, but later than the last transaction's and the last read time. A
 * clock time outside 0 to 2^56 - 1, or a time above 2^56 - 1, refuses the
 * transaction before it begins (005-18), and so does a time after
 * DBCLOCK_LAST_USER_TIME for a user transaction (user true; 015-55, as
 * Java's since release 2026.3): ERR_LIMIT, "DbException", with Java's
 * texts; nothing changes. Else *time is the transaction's time (at least
 * 1) and a transaction runs. Asserts that none runs. */
enum err_code dbclock_transaction_begin(struct dbclock *c, bool user, int64_t *time,
        struct err *e);

/* DbClock.transactionEnd: the running transaction's time becomes the last
 * transaction's. Asserts that one runs. */
void dbclock_transaction_end(struct dbclock *c);

/* DbClock.setLastTransTime: at a start, the last record's time. Asserts
 * that no transaction runs. The last read time is left as it is (C3). */
void dbclock_set_last_trans_time(struct dbclock *c, int64_t lastTransTime);

#endif
