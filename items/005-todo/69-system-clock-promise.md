005-69. Fix: `SystemClock` does not keep its promise of strictly increasing times
===============================================================================

Status: open. Kind: fix. Created 2026-10-28.

Registered by Claude (Opus 5.5, Claude Code), the conductor of 012, as
012-01 (section 4.4) and its decision D5 say: a Java bug that the C clone's
planning found is registered here and not fixed in 012.


The issue
---------

`bergdb.core.SystemClock`, the default clock of `DbBuilder` (and used by
`pubimp.TimeResolver`), says in its Javadoc: "Even if system clock is set
the time returned is always strictly increasing." Its code:

    public synchronized long getTime() {
        long time = System.currentTimeMillis() * 10L*1000L;
        if (time <= lastTime) {
            lastTime++;
            time = lastTime;
        }
        return time;
    }

`lastTime` starts at 0 and is set only inside the `if`, which a real clock
(far above 0) never enters. So `lastTime` stays 0, and `getTime()` returns
equal times for calls within one millisecond, and earlier times when the
system clock is set back.

**No harm to a database.** `DbClock` makes the times it gives strictly
increasing itself: `transactionBegin` gives a time later than the last
transaction's and than the last `currentTime()`, and `currentTime()` never
goes below the last transaction's time (`DbClock`, read 2026-10-28 at
`404d2ee`). So no stream, read or test depends on `SystemClock`'s promise.
`TimeResolver` makes a new `SystemClock` for each call, so the promise could
not hold there anyway.

For 012: the C clone ports `SystemClock`'s code as it is (012-01, 4.4; C
does as Java until Java is fixed). The system clock is never part of a
byte comparison; the cross tests use the test clock.


Options
-------

* **A. Make the code keep its promise**: `lastTime = time;` when the time is
  larger, so that equal and earlier system times give `lastTime + 1`. One
  line; a unit test that calls `getTime()` many times in a row and checks
  that each is larger than the last fails before (calls within a
  millisecond) and passes after. The C clone follows.
* **B. Make the comment say what the code does**: the system time in 100 ns
  units, neither strictly increasing nor monotone; `DbClock` gives the
  database's guarantees. No behaviour changes.
* **C. Nothing.**

Recommended: A, as the class promises it, `DbBuilder` uses it by default,
and the change is one line with a test; or B, if Frans prefers one place
(`DbClock`) for the guarantee (P11). Either keeps every stream's bytes.


Done when
---------

The decision is taken; for A or B, the change with `before-commit.sh`
(`BEFORE COMMIT OK`), and the C clone's port of `SystemClock` brought in
line (a note in 012's log).
