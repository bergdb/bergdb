015-55. Fix: a user transaction at the last database time is taken, and reclaim's next internal transaction then fails the database
===================================================================================================================================

Status: done 2026-11-05, night 006-12. Kind: Fix. Created 2026-11-03 by Frans Lundberg.

After release 2026.2 (a known issue of it); in 2026.1 too.

What: review R7's finding R7-F6 (items/016-release-2026-2/06-reviews/R7.md,
section R7-F6: where, intended, actual, effect, a proposed fix), shown by a
probe in 06-reviews/R7/. No second agent has checked it yet.

Done when: a test that fails on the code before the fix passes, and the
fix is in `main` after `before-commit.sh`.

First step: verify it (016-06, section 2.6), then the probe made a test.


Log
---

2026-11-03. Registered by the coordinator of release 2026.2 (016-02).

2026-11-05. Done in night 006-12. Verified with R7's probe
(`R7ClockEndProbe`, run as it is on the base): "put 196 (clock at
Klong.MAX_TIME: true) FAILED THE DATABASE: bergdb.pub.util.DbException: No
database time is left after 72057594037927935; the largest is
72057594037927935." The probe made
`Reclaim.Tester.testUserTransactionLeavesTimesForReclaim` (with a clock
that can go back, as `CoreTestClock` cannot): before the fix the put at
`Klong.MAX_TIME` that makes a step fails the database ("the database
failed", caused by "No database time is left ..."); after it the put is
refused, the database goes on, and a put at the last user time is taken and
makes its step.

* Fix, R7's proposal: `DbClock.transactionBegin(boolean user)` refuses a
  user transaction whose time would be after `DbClock.LAST_USER_TIME`,
  `Klong.MAX_TIME - TIME_MARGIN` with a margin of 1,024 units (102.4 us),
  as `Db.TOP_ORDINAL_MARGIN` keeps 1,024 top node ordinals for the same
  transactions (005-02). `Db.executeInner` passes `!t.isInternal()`,
  before the go point as before; the primordial transaction counts as a
  user one. Internal transactions keep the whole range to
  `Klong.MAX_TIME`; reclaim's run after a user transaction, at most five,
  each one unit after the one before.
* Reclaim's settings transaction (015-87's setters) is internal and may
  use the margin; it makes no reclaim work after it, and when no time is
  left it is refused before its go point, as before. A start runs no
  transaction (`initFromDb` reads and may cut only).
* docs/levels.md, section 3, says so.
* 010-01: no setting, method, thread or global state (two constants); P7
  kept. The stream's bytes are unchanged (P2): only transactions within
  the last 1,024 units before 2^56 - 1 (the year 2198) are refused that
  were taken.
* Tests: the new test, `DbClock.testTimeMarginForInternal` (unit), and
  `Reclaim.Tester`, `DbClock`, `DbTester`, `DbTesterRestart`,
  `DbTesterFailure` pass.
