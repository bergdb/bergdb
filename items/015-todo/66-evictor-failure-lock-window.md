015-66. Fix: a failed batch releases the writer lock before failing the database
================================================================================

Status: done 2026-11-05, night 006-12. Kind: Fix. Created 2026-11-04 by Frans Lundberg.

After release 2026.2 (a known issue of it); new in 2026.2. A fault in 015-25's fix of tonight: fix it first after the release.

What: review R4's finding R4-F1 (items/016-release-2026-2/06-reviews/R4.md,
section R4-F1: where, intended, actual, effect, a proposed fix), shown by a
probe in 06-reviews/R4/. No second agent has checked it yet.

Done when: a test that fails on the code before the fix passes, and the
fix is in `main` after `before-commit.sh`.

First step: verify it (016-06, section 2.6), then the probe made a test.


Log
---

2026-11-04. Registered by the coordinator of release 2026.2 (016-02).

2026-11-05. Done in night 006-12 (W1). Verified: R4-F1 holds on the code
of the night's start. `EvictorRun.run` ran a batch (`sweep`) under the write
lock, but its catch, which fails the database (`failByEviction`, 015-25),
was outside the lock: a writer waiting for the lock could get it while the
database was still active, pass `executeInner`'s state check, commit and
append after the failure.

* Fix: the eviction thread's call of `sweep` catches what it throws and
  fails the database there, under the write lock, then rethrows; the outer
  catch keeps its `failByEviction` for anything else (`setFailed` keeps
  the first failure) and ends the thread as before. The lock order is the
  writer's own (`Db.fail` takes readSync under the write lock). The
  comments of `EvictorRun` and its catch say so.
* Test: `Eviction.testBatchFailureBeforeTheLockGoes` (unit group), R4's
  probe made a test: the hook `testBeforeTrigger`, in the thread's first
  batch, starts a writer and throws once it waits for the lock; the test
  holds readSync meanwhile and looks, with `ThreadMXBean`, at whom the
  writer waits for. Before the fix it waited for the test's readSync after
  its go point (it held the write lock) and committed; after it, it waits
  for the eviction thread's write lock, is refused with a
  `DbFailedException` whose cause is the batch's Error, and the stream is
  unchanged. About 25 ms.
* P1 to P12 (010-01): no new work, wait, thread, setting or API; P7 (a
  failed database stops) is what the fix restores. The stream's bytes of a
  valid database are unchanged.
