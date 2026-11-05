015-78. Fix: the consumer discards the first storage-close IOException
======================================================================

Status: done 2026-11-05, night 006-12. Kind: Fix. Created 2026-11-04 by Frans Lundberg.

After release 2026.2 (a known issue of it); in 2026.1 too.

What: review R5's finding R5-F1 (items/016-release-2026-2/06-reviews/R5.md,
section R5-F1: where, intended, actual, effect, a proposed fix), shown by a
test or probe in 06-reviews/R5/. No second agent has checked it yet.

Done when: a test that fails on the code before the fix passes, and the
fix is in `main` after `before-commit.sh`.

First step: verify it (016-06, section 2.6), then the probe made a test.


Log
---

2026-11-04. Registered by the coordinator of release 2026.2 (016-02).

2026-11-05. Done in night 006-12, with 015-34 (the same close). Verified
with R5's test (R5/R5-F1.diff, without `seekFirstPos`, which 019-04
removed), made `DbTesterStream.testFirstCloseFailureIsReported`, which also
closes a second time: before the fix "close() 0 reports the failed close;
closes: 2, expected true".

* Fix: `BufferedStream.closeStream()`, used by the storage thread as it
  ends and by `close()`, keeps the first failure of the underlying
  stream's close (an `IOException`; an unchecked exception or an `Error`
  as the cause of one), and every `close()` throws it, unless a flush
  failed, whose failure it throws as before. `Db.close()` then throws a
  `StreamIoException`, and so does every later close (005-73, F5).
* As a side effect, the storage thread no longer ends with an uncaught
  unchecked exception of its last close (015-81's case).
* 010-01: P7 (a failed close is reported); no setting, thread or format
  change; the stream's bytes are unchanged.
