005-18. Fix: a clock time of 2^56 or more is not checked; the database cannot restart
====================================================================================

Status: open. Kind: fix. Created 2026-10-21.

Found on 2026-10-21 in a review of the Java code for overflow, by Claude
(Opus 5.5, Claude Code), at Frans's request; checked with a probe.


The issue
---------

`Clock.getTime()` is documented to return at most 2^56 − 1 (100 ns units,
year 2198), and a TIME klong keeps 56 bits. Nothing checks it: only an
`assert` in `Klong.createTime`. A clock in nanoseconds (about 1.7e18 today)
is an easy mistake with `DatabaseBuilder.clock(Clock)`.

* A new database with such a clock fails its first start with
  "StreamFormatException: Time too large" (`StoredTopNode.parse`).
* An existing database opened once with it takes writes (the klongs keep
  the low 56 bits of the time), and then cannot be started again, with any
  clock, when its stream is longer than the startup distance: "Time too
  large". `DbClock` also keeps the last transaction time, so a correct
  clock afterwards still gives times above 2^56.


The fix
-------

`DbClock` refuses a clock time outside 0 to 2^56 − 1, with a `DbException`
naming the clock's value, before the transaction changes anything; also for
the primordial transaction.


Done when
---------

* Unit tests: a clock above the range is refused at start and at a
  transaction, and the database goes on with a correct clock.
* `java/before-commit.sh` prints `BEFORE COMMIT OK`.
