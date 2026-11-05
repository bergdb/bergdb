015-76. Fix: db.setStartupDistance clamps to 400,000 to 10^9 bytes without saying so: a call with a setting in force below 400,000 writes 200 kB and changes the setting
========================================================================================================================================================================

Status: done 2026-11-05, night 006-12. Kind: Fix. Created 2026-11-04 by Frans Lundberg.

After release 2026.2 (a known issue of it); new in 2026.2 (its Javadoc's promise).

What: review R6's finding R6-F5 (items/016-release-2026-2/06-reviews/R6.md,
section R6-F5: where, intended, actual, effect, a proposed fix), shown by a
test or probe in 06-reviews/R6/. No second agent has checked it yet.

Done when: a test that fails on the code before the fix passes, and the
fix is in `main` after `before-commit.sh`.

First step: verify it (016-06, section 2.6), then the probe made a test.


Log
---

2026-11-04. Registered by the coordinator of release 2026.2 (016-02).

2026-11-05. Done in the night 006-12 (W1, clone `g3c`), by R6's proposed fix,
the first of its three options: the Javadoc states the range and that the
clamped value is set; the code is unchanged. Verified with R6's probe
(`DbTester.testSetStartupDistanceInForceBelowClamp`): on a database built with
`startupDistance(2000)`, `setStartupDistance(2000)` sets 400,000 and writes the
200 kB transaction ("the setting, expected 2000, got 400000").

* Why the first option: R6 proposes it, and it is the simplest (P11). The
  other two change the Core API's behaviour: refusing an argument outside the
  range with `IllegalArgumentException` would refuse what JMX and the tests
  pass today; clamping to the builder's range (10 to 2^31 - 1) would change
  the values a call sets, which 2026.1 and 2026.2 kept within the clamp. Only the Core API and JMX reach the case: the Pub API
  clamps to 5 to 1000 MB first, inside the range. 017-07, section 2 (the
  distance in an internal KV, not the meta block) would not change this
  method's range, and is a format change for another time.
* Fix: `Db.setStartupDistance`'s Javadoc says that the value is clamped to
  400,000 to 1,000,000,000 bytes (twice `RecoverableStream.META_BLOCK_DISTANCE`
  to 10^9) and the clamped value is set; that a call whose clamped value is
  the setting in force writes nothing; that on a database whose setting is
  outside the range, which `DbBuilder.startupDistance` allows, any call writes
  and sets a value inside it; and that a negative value is refused with
  `IllegalArgumentException` and changes nothing.
* Test: `DbTester.testSetStartupDistanceClamped` (unit test) pins the stated
  contract: on a database built with 2,000, a call of 2,000 sets 400,000 and
  writes; then calls of 100 and 400,000 write nothing; `Integer.MAX_VALUE`
  sets 10^9, and 10^9 + 1 then writes nothing; -1 is refused, the setting and
  the stream unchanged. As the code is unchanged, it passes before and after
  (as 015-51's test does); R6's probe asserts the other reading of the old
  Javadoc and is not kept.
* The stream's bytes (P2): unchanged, the code is. 010-01: no departure.
* A line in `releases/next.md` (Documentation).
