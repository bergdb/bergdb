015-69. Fix: a test-schedule resync overwrites concurrent readers' accounting
=============================================================================

Status: done 2026-11-05, night 006-12. Kind: Fix. Created 2026-11-04 by Frans Lundberg.

After release 2026.2 (a known issue of it); in 2026.1 too.

What: review R4's finding R4-F4 (items/016-release-2026-2/06-reviews/R4.md,
section R4-F4: where, intended, actual, effect, a proposed fix), shown by a
probe in 06-reviews/R4/. No second agent has checked it yet.

Done when: a test that fails on the code before the fix passes, and the
fix is in `main` after `before-commit.sh`.

First step: verify it (016-06, section 2.6), then the probe made a test.


Log
---

2026-11-04. Registered by the coordinator of release 2026.2 (016-02).

2026-11-05. Done in night 006-12 (W1). Verified: R4-F4 holds on the code
of the night's start (with 015-66 to 015-68). `Residents.resync`, which
the test schedules (VALUES, EVERY, RANDOM) call after their sweep in
`Eviction.afterTransaction`, counted each object of the walk under its
monitor into a local sum and then set the total to that sum. Readers do
not take the write lock: a value loaded into an object already counted
(`valueIn`, under the object's monitor) moved the object's count and the
total, and the final `bytes.set` dropped the total's part.

* Fix: `resync` counts each object of the walk that is counted with its
  bytes now and moves the total by the difference, under the object's
  monitor, as `grown` does; an object that is not counted (released since
  the walk, or not resident) is skipped, and the object counter is left
  to `added` and `released`. A load into an object before its count is
  in the new count, one after it adds its own bytes: the total keeps
  both. The counted objects are the objects of the live handles, which
  the walk starts from, so the total is the walk's sum as before when no
  reader loads. Javadoc of `resync` and the class, the comment in
  `afterTransaction`.
* Test: `Residents.testResyncWithConcurrentLoad` (unit group), R4's probe
  made a test: the test holds the last object's monitor, so that the
  resync waits there after counting the first, and loads a value into
  the first. Before the fix the total was 414 against counts of 570, and
  -156 after every object was released; after it 570 and 0.
* P1 to P12 (010-01): no new work, wait, thread, setting or API. The
  test schedules are for tests; the stream's bytes are unchanged.
