015-82. Fix: a pending cut arriving during another cut can be left unapplied after close
========================================================================================

Status: done 2026-11-05, night 006-12. Kind: Fix. Created 2026-11-04 by Frans Lundberg.

After release 2026.2 (a known issue of it); in 2026.1 too.

What: review R5's finding R5-F7 (items/016-release-2026-2/06-reviews/R5.md,
section R5-F7: where, intended, actual, effect, a proposed fix), shown by a
test or probe in 06-reviews/R5/. No second agent has checked it yet.

Done when: a test that fails on the code before the fix passes, and the
fix is in `main` after `before-commit.sh`.

First step: verify it (016-06, section 2.6), then the probe made a test.


Log
---

2026-11-04. Registered by the coordinator of release 2026.2 (016-02).

2026-11-05. Done in night 006-12. Verified: R5's probe
(R5/R5PendingCutProbe.java), made `BufferedStream.testPendingCutDuringACut`,
fails on the code before the fix, "Expected 300, got 200": the second cut,
kept while the first one was made, never reached the underlying stream.

* Fix: `BufferedStream.flushToStream` takes the pending cuts that the
  flushed bytes reach in a loop, and the last check, which finds none, and
  the publication of the flush (`streamLength`, `cStart`) are one
  synchronized step. So a `pretruncate()` either runs before that step, and
  its kept cut is made by this flush, or after it, and sees the new
  `streamLength`. `applyPendingCut` went into the loop. A cut is still made
  before the flush is published and before the listener is told, as since
  2026-10-13; a failed cut fails the storage as before.
* The argument is the monitor's alone: `pendingCut` and `streamLength` are
  read and written only under it (the consumer's own read of
  `streamLength` outside it is of its last write). The loop ends when no
  cut arrives during a cut; every caller holds the database's write lock.
* Not changed: a cut at or before the flushed length still goes to the
  underlying stream from the caller's thread, also while the consumer
  appends (R5-F5, 015-80).
* Reach: internal; Db's reclaim cuts behind the durable length, so it does
  not keep cuts in the buffer. 010-01: no setting, thread or format change;
  the stream's bytes are unchanged.
