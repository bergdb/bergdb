015-75. Fix: checks of stream data at a start that are asserts: without -ea a corrupt got-dirty id is accepted, with -ea it is an AssertionError
================================================================================================================================================

Status: done 2026-11-05, night 006-12. Kind: Fix. Created 2026-11-04 by Frans Lundberg.

After release 2026.2 (a known issue of it); in 2026.1 too.

What: review R6's finding R6-F4 (items/016-release-2026-2/06-reviews/R6.md,
section R6-F4: where, intended, actual, effect, a proposed fix), shown by a
test or probe in 06-reviews/R6/. No second agent has checked it yet.

Done when: a test that fails on the code before the fix passes, and the
fix is in `main` after `before-commit.sh`.

First step: verify it (016-06, section 2.6), then the probe made a test.


Log
---

2026-11-04. Registered by the coordinator of release 2026.2 (016-02).

2026-11-05. Done in night 006-12. Verified: R6's three asserts compared
stream data with what a start expects, and three new tests in
`DbTesterRestart` failed before the fix, with and without `-ea`:

* `testCorruptGotDirtyIdRefused` (R6's `R6GotDirtyIdProbe`): A's got-dirty
  entry of node 1 set to id 123456789. Before: with `-ea` "AssertionError:
  ids differ, 1 != 123456789"; without, the start succeeded.
* `testCorruptStartupPosRefused` (`R6StartupPosProbe3`): the last record's
  startupPos set to -8, `Long.MIN_VALUE`, 4, 8, 120, its position + 4, its
  position + 8, and its position with bit 40 set. Before: with `-ea` an
  `AssertionError` for the negative ones, without `-ea` an
  `IllegalArgumentException` ("Negative position not allowed"); 4 an
  `IllegalArgumentException` ("bad transPos, 4"); the others a
  `StreamFormatException` from reading at a position that is not a record
  ("Bad transaction size, 0", "No transactions in startup transaction
  set"), which does not name the cause.
* `testOlderTopPosRefused`: the last record's topPos set to an older
  version of the same top node (startup distance 100, 6 puts: 776 for
  1200). Before: with `-ea` "AssertionError: topPos 776 is not the newest
  version 1200 of top node 1"; without, the start took the newer version.

The fix, each a `StreamFormatException` that names the record and the value:

* `DbStarter.canonicalNode`: the node read at a got-dirty entry's position
  must have the entry's id.
* `DbStarter.topNodeOfLastTransaction`: the last record's topPos must be
  the newest version of its top node in the section (Rule R, as the assert
  said); the fallback to the newer version, which only a corrupt stream
  reached, is gone.
* `Db.checkStartupPos`, for each record that
  `getStartupPosFromLastTransaction` reads: the startupPos is not negative,
  a multiple of 8, 0 or not in the first meta block, and not after the
  record's own position. The take writes 0 or the position of an earlier
  record (`TransSeq.take`), so no valid stream is refused. These are the
  cheap checks of R6-F2's proposal; a startupPos that names an earlier
  record that the take never reached (R6's probe of 015-73) is not caught,
  which is 015-73's design question.

`StartupPos.set`'s `assert pos >= 0` stays: it checks the Core's own value,
after the check. 010-01: no setting, method or thread; a start's checks
only. The stream's bytes are unchanged (P2): nothing that writes changed.
