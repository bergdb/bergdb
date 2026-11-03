005-69. Fix: `SystemClock` does not keep its promise of strictly increasing times
===============================================================================

Status: open; option A taken under D2 (016-01, section 10) and planned
for release 2026.2, Java only (see Plan for 2026.2). Kind: fix. Created
2026-10-28.

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


Plan for 2026.2
---------------

Written 2026-11-03 for 016-05 (W4). Option A, the entry's recommendation,
taken with Frans's D2 (016-01, section 10: "D2. As you recommend unless I
say otherwise here."). With D7 (15:31: "The C code does not need to be
updated for 2026.2 in this work."), the C clone's port is not brought in
line now: a later follow-up, below.

The steps, by agent F1 (016-05), after 005-82, in
`/Users/f/fl/bench/016/005-69/repo` (a new clone of `main`):

1. **The fix** (0.15 hours), `java/src/bergdb/core/SystemClock.java`:
   * `getTime()` calls a package-private `synchronized long
     getTime(long millis)` with `System.currentTimeMillis()`, so that a
     test can give it equal and earlier system times.
   * In it, `lastTime = time;` when the system's time is larger than
     `lastTime`; an equal or earlier one gives `++lastTime`. So each call
     returns a time larger than the one before, in 100 ns units, also when
     the system clock is set back: then the times go on from the last one,
     100 ns a call, until the system clock passes it.
   * The Javadoc says so; `DbClock`'s guarantees are unchanged and
     independent of it.
2. **The test** (0.2 hours), in `SystemClock` (and `SystemClock.class`
   added to `java/src/bergdb/core/Pack.java`'s list, where the unit tests
   are found), or in an existing tester of `bergdb.core`:
   * `testStrictlyIncreasing` (unit): 100,000 calls of `getTime()` in a
     row, each larger than the one before. Fails before the fix (calls in
     the same millisecond give equal times).
   * `testClockSetBack` (unit): `getTime(1000)`, `getTime(1000)`,
     `getTime(999)`, `getTime(2000)`: strictly increasing, the last one
     `2000 * 10,000`. Fails before the fix.
3. **The gate**: `java/before-commit.sh` (`BEFORE COMMIT OK`). If it fits:
   `java/stress/level1.sh quick`. No stream byte can change: the streams
   that are compared byte for byte use the test clock (StreamDigest and
   the level scripts' invariance checks), and `SystemClock`'s time only
   decides a transaction's time through `DbClock`.
4. **The review**, with 005-71's notes (016-05, section 5): 0.3 hours of
   another agent for both; the answers here, in the Log.
5. **The hand-off** (016-05, section 4), Status "done (2026.2, Java)" for
   the commit, and a line for `releases/next.md`: "`SystemClock`, the
   default clock, gives strictly increasing times as its Javadoc said
   (005-69)".

Size: about 0.75 agent-hours, the review's share included. No stop for
Frans. Done for 2026.2 when the fix and its two tests are in `main` with
`BEFORE COMMIT OK` and the review answered.

**Later, not for 2026.2** (D7): the C clone's port (`c/src/clock.c`,
`clock.h`, "SystemClock's state: its last time, 0 at first") takes the
same line, with a note in 012's log; C is a separate project, built and
tested by hand (012). Until then C keeps Java's old behaviour, which no
cross test sees (they use the test clock).

**State** (2026-11-03): planned, not started. The code read at `df6ad50`:
`SystemClock` (`lastTime` starts at 0 and is set only inside the `if`);
its users `DbBuilder` and `pubimp.TimeResolver`.


Log
---

2026-11-03. Option A planned for release 2026.2, Java only (016-05); the C
port is a later follow-up (D7). Nothing changed yet.
