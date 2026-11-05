015-68. Fix: startup leaves large values retained in the writer's admission list
================================================================================

Status: done 2026-11-05, night 006-12. Kind: Fix. Created 2026-11-04 by Frans Lundberg.

After release 2026.2 (a known issue of it); new in 2026.2.

What: review R4's finding R4-F3 (items/016-release-2026-2/06-reviews/R4.md,
section R4-F3: where, intended, actual, effect, a proposed fix), shown by a
probe in 06-reviews/R4/. No second agent has checked it yet.

Done when: a test that fails on the code before the fix passes, and the
fix is in `main` after `before-commit.sh`.

First step: verify it (016-06, section 2.6), then the probe made a test.


Log
---

2026-11-04. Registered by the coordinator of release 2026.2 (016-02).

2026-11-05. Done in night 006-12 (W1). Verified: R4-F3 holds on the code
of the night's start. A start reruns the transactions after the startup
position with `Db.newPutData`, whose pointer listener puts each value over
1 MiB on the writer's admission list (`Eviction.largeValueCreated`); only
`recordWritten`, after the next record the database writes, took them off.
A database opened for reads kept them, their payloads and their key nodes,
for as long as it ran, outside the resident bytes.

* Fix: `Db.startInner` calls `eviction.recordWritten(this, <no nodes>)`
  under the write lock, before the startup's batch (`afterTransaction`):
  the admission of the rerun's large values, whose records are in the
  stream, as after a record the running database writes. Their pointers
  become stream pointers and the list is empty. The Javadoc of
  `largeValues` and `recordWritten` says so.
* Test: `Eviction.testStartAdmitsLargeValues` (unit group), from R4's
  probe: three values of 1,200 KiB, a restart with a budget of 100 MB (no
  batch takes them). Before the fix the list held 3 entries after the
  start, and 3 resident pointers held values over 1 MiB (each assertion
  checked alone); after it, none, and the value reads back.
* P1 to P12 (010-01): the work is the rerun's large values, a few
  pointers, once per start (P5); no setting, thread or API. Whether a
  pointer holds a value or its position does not change what is written
  (the eviction twins compare streams with and without eviction), so the
  stream's bytes are unchanged (P2). Gates: `before-commit.sh` and
  `level4.sh` (full).
