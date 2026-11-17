015-29. Fix: deleteIndex(Database.PRIMARY) throws Bug and leaves the primary deleting
=====================================================================================

Status: done 2026-11-09. Kind: Fix. Created 2026-11-03 by Frans Lundberg.

After release 2026.2 (a known issue of it); in 2026.1 too.

What: `deleteIndex(Database.PRIMARY)` throws `bergdb.common.Bug` from `DirToIndexesMap.remove` after `IndexManager` has set the primary index to DELETING; until a restart every `usePrimary` throws `NoSuchIndexException` ("Index is not active, but in state: deleting"). It should be refused before anything changes. In 2026.1 too. Probe: `/Users/f/fl/bench/016/015-20/review/probes/prim/PrimaryDeleteProbe`.

Source: the H5 review of 015-20, 015-22 and 015-21, "Outside the changes"
(`/Users/f/fl/bench/016/015-20/handoff/review-findings.md`), 2026-11-03.

Done when: a test that fails on the code before the fix passes, and the fix
is in `main` after `before-commit.sh`.

First step: the probe, made a test.


Log
---

2026-11-03. Registered by the coordinator of release 2026.2 (016-02).

2026-11-09. Done by release 2026.4's indexes (020-10), in night 006-15: the pseudo-index "primary" is gone: the primary scan has its own iterator (020-10, P1) and Database.PRIMARY was removed (I3); "primary" is a name like any other; 238b249 (P1), 4f8210f (I2), f3c7966 (I3). The test: PubTesterIndexJobs.testIndexNamedPrimary and PubTesterIndex.testScanIndexNamedPrimary, in `before-commit.sh`, passing on `main` at `b768ef0` (020-11). Status: done.
