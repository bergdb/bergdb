021-26. Fix: a currentTime() with the clock past the end refused every later transaction
========================================================================================

Status: done. Kind: Fix. Frans: none.
Created 2026-11-09 by Frans Lundberg.

What: one `currentTime()` (`Connection`, `Database`, the Core's
`Db.currentTime()`) while the clock reads after 2^56-1025, out of range
or in the 1024 units kept for reclaim (015-55), gave 2^56-1025 and kept
it as the time that the next transaction must pass. Every user
transaction after it was refused until a restart ("No database time is
left for a user transaction: its time would be 72057594037926912, after
the last, 72057594037926911"), also when the clock was back in the
range. `Clock.getTime()`'s Javadoc says that a transaction is refused
while the clock is out of range and that the database goes on, and that
a start of an existing database succeeds with its transactions refused
while the clock is out of range (020-23, Z3). Found by a black-box user
of the C port (022), U2-1 (medium); the C reproduction
`repro_clock_poison.c` in `/Users/f/fl/bench/022/apps/u2/`. Java does the
same.

Why: a clock glitch of one reading, while an application asks for the
current time, stops all its writes until a restart.

Frans: none.

Done when: a test that fails before; the transactions refused while the
clock is out of range and taken when it is back, with `currentTime()`'s
promise kept (020-23, Z1); `BEFORE COMMIT OK`, `JAVADOC PUB OK` and
`java/stress/level1.sh` under the gate lock; a line in `releases/next.md`.

First step: `DbClock.currentTime()` and its cap at `LAST_USER_TIME`.


Log
---

2026-11-09. Registered by coord-1109 from 022's U2-1 and taken by its
agent h31 (clone `clone-h31`, on main's b3a6b05).

2026-11-09. Done by h31: commit "021-26" in `clone-h31`, to land.

* Reproduced in Java. `PubTesterJavadocRest.testCurrentTimeWithTheClockOutOfRange`:
  a put at 1001, the clock at 2^56, `currentTime()`, a put refused as out
  of range, the clock back at 2000, a put. Before the fix the last put
  threw the `DbException` above, as in C; with the test's checks of
  `currentTime()` first, "Expected 1001, got 72057594037926911".
* Why it happened. 020-23's Z1 (6ac9708, today) made `lastReadTime` never
  decrease and capped the clock's time at `LAST_USER_TIME`, so that the
  times kept for reclaim stay its own. But `currentTime()`'s promise is
  that every later transaction's time is after the time it gives: a
  time of `LAST_USER_TIME` leaves no user transaction, and it was kept
  until a restart. Before Z1 the clock's time was taken uncapped, and a
  later `currentTime()` with the clock back took it back.
* Fix, in `DbClock.currentTime()`: a clock's time after `LAST_USER_TIME`
  is not taken; the time is the last time given or the last
  transaction's, as for a clock that went back. Such a `currentTime()`
  uses up no time, as a user transaction at that clock is refused and
  uses up none. A clock at most `LAST_USER_TIME` is taken as before. The
  promise of Z1 holds: the times never decrease, every later transaction
  is after them, and no time after `LAST_USER_TIME` is given but a
  transaction's.
* Javadoc: `Clock.getTime()` (the time that `currentTime()` gives is the
  clock's, or, when that is earlier or after 2^56-1025, the last one
  given or the last transaction's) and `DbClock.currentTime()`.
* Tests: `DbClock.testCurrentTimeWithTheClockPastTheEnd` (the clock at
  2^56 and at `LAST_USER_TIME` + 1: `currentTime()` gives the last
  transaction's time, the user transaction is refused; the clock back:
  a transaction at its time) and the Pub test above, each failing before.
  `DbClock.testCurrentTimeLeavesTheMargin` (Z1's) now expects the last
  transaction's time with the clock at 2^56-1 and 2^56, and
  `LAST_USER_TIME` with the clock there; its internal transactions still
  take the whole margin.
* For 022: C's `dbclock_current_time` has the same cap (ported from Z1
  in 62345d3), and `bergdb.h`'s comment of `bergdb_current_time` ("at
  most BERGDB_MAX_TIME - 1024") follows this change.
* `releases/next.md`, Pub API.

Runs, under the gate lock (2026-11-09, 18:22 to 18:30), on the tree of
this commit and 021-27's (a test only): `BEFORE COMMIT OK (273 s)` (unit
1620, f 86, demos); `JAVADOC PUB OK`; `LEVEL 1 OK` (MEM 130, SS 1.51).
