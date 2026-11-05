015-71. Fix: the audit reports a valid empty-handle cleanup as a bad table entry
================================================================================

Status: done 2026-11-05, night 006-12. Kind: Fix. Created 2026-11-04 by Frans Lundberg.

After release 2026.2 (a known issue of it); new in 2026.2.

What: review R4's finding R4-F6 (items/016-release-2026-2/06-reviews/R4.md,
section R4-F6: where, intended, actual, effect, a proposed fix), shown by a
probe in 06-reviews/R4/. No second agent has checked it yet.

Done when: a test that fails on the code before the fix passes, and the
fix is in `main` after `before-commit.sh`.

First step: verify it (016-06, section 2.6), then the probe made a test.


Log
---

2026-11-04. Registered by the coordinator of release 2026.2 (016-02).

2026-11-05. Done in night 006-12 (W1). Verified: R4-F6 holds on the code
of the night's start (with 015-66 to 015-70). `Audit.check` looked at
each handle of its copy of the node table (`Cache3.handles`, each map
under its lock in turn) without the map's lock and without asking
whether the handle was still the table's. A reader that kept nothing
removes its empty handle (`Cache3.dropIfEmpty`: LIVE to DEAD, then out
of the map, under the map's lock) without the write lock, so a removal
after the copy had passed the handle's map was reported as "the node
table has a dead handle".

* Fix: the audit looks at each handle of the copy under its map's lock,
  and only if it is still the table's (`liveHandle`); one removed since
  the copy is skipped. The check of the handles that pointers hold (a
  live one is the table's, a dead one has no object) is made under the
  handle's map lock likewise, so that its state and the table are seen
  together: the reader's cleanup makes the handle dead and removes it
  under that lock (R4's "same coherent observation"; not shown by a
  probe). Comments in `Audit.check`.
* Test: `EvictionReaderTester.testAuditWithReaderCleanup` (unit group),
  R4's probe made a test: an empty handle in map 0; the audit is held at
  the oracle's monitor, then at the lock of a later map without handles,
  inside `handles()`; the reader's `dropIfEmpty` runs, then the audit goes
  on. Before the fix the audit reported "the node table has a dead handle
  of node 107863"; after it, nothing. About 10 ms.
* P1 to P12 (010-01): the audit is test-only; it takes each map's lock
  once more for each handle, as `liveHandle` does. No new thread, wait or
  setting. The stream's bytes are unchanged.
