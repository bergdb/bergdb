015-58. Fix: testClock.setTime() refuses the clock's current time, which its Javadoc allows
===========================================================================================

Status: done 2026-11-05, night 006-12. Kind: Fix. Created 2026-11-04 by Frans Lundberg.

After release 2026.2 (a known issue of it); in 2026.1 too.

What: review R8's finding R8-F3 (items/016-release-2026-2/06-reviews/R8.md,
section R8-F3: where, intended, actual, effect, a proposed fix), shown by a
test or probe in 06-reviews/R8/. In 2026.1: yes (line 42 there, the same check and Javadoc).

Done when: a test that fails on the code before the fix passes, and the
fix is in `main` after `before-commit.sh`.

First step: verify it (016-06, section 2.6), then the probe made a test.


Log
---

2026-11-04. Registered by the coordinator of release 2026.2 (016-02).

2026-11-05. Done in night 006-12. Verified with R8's test, made
`PubTester.testTestClockSetTimeEqual` (with time 0 on a new clock, and an
earlier time still refused): before the fix "IllegalArgumentException: Bad
time, must be larger than current time, 0."; it passes after.

* Fix, R8's choice: the check follows the Javadoc, `time < this.time`
  throws ("Bad time, ..., must not be less than the current time, ...").
  The Javadoc is the contract users read, and the database gives each
  transaction a later time itself (`DbClock.transactionBegin`), so equal
  clock times are safe; `Clock`'s contract asks for non-decreasing times.
* The Core's copies, `bergdb.core.TestClock` and `CoreTestClock`, keep
  their strict check: they have no such Javadoc, and the Core's tests use
  them.
* 010-01: no setting, method or state. The stream's bytes are unchanged
  (P2): a test clock, not used by StreamDigest.
* Tests: the new test; `PubTester` passes.
