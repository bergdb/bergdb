015-28. Fix: a write racing an index's creation is never indexed
================================================================

Status: done 2026-11-09. Kind: Fix. Created 2026-11-03 by Frans Lundberg.

After release 2026.2 (a known issue of it); in 2026.1 too.

What: A W transaction into a directory that has no index yet, racing `indexBuilder().start()` (`createFast()`), is never indexed: `RwEnvironmentImp` takes the index list before any read, and with no read the transaction's read time is `Long.MAX_VALUE`, so the directory's read hash never conflicts. With an index, the first read still comes after the list is taken, a smaller window, also for a deletion. A wrong answer through the Pub API (the index misses the object); in 2026.1 too. Probe: `/Users/f/fl/bench/016/015-20/review/probes/race/CreateRaceProbe` ("expected [1, 2]: [1]").

Source: the H5 review of 015-20, 015-22 and 015-21, "Outside the changes"
(`/Users/f/fl/bench/016/015-20/handoff/review-findings.md`), 2026-11-03.

Done when: a test that fails on the code before the fix passes, and the fix
is in `main` after `before-commit.sh`.

First step: the probe, made a test.


Log
---

2026-11-03. Registered by the coordinator of release 2026.2 (016-02).

2026-11-09. Done by release 2026.4's indexes (020-10), in night 006-15: a write fixes its read time first and puts the hash of its directory's virtual key in its read set, which a creation writes (020-10, 5.1 and 5.2); 249b684 (020-10, I1). The test: PubTesterIndexRaces.testRacesCreate (a write of an object, a String and a delete at each of four points of a creation; the raw entries equal the index function over the latest values), in `before-commit.sh`, passing on `main` at `fd6dd09` (020-11). Status: done.
