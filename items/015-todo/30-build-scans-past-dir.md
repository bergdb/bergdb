015-30. Fix: an index build step scans past its directory, over non-objects
===========================================================================

Status: done 2026-11-09. Kind: Fix. Created 2026-11-03 by Frans Lundberg.

After release 2026.2 (a known issue of it); in 2026.1 too.

What: `IndexBuilderImp`'s stop condition returns CONTINUE for a non-object before its prefix check, so one build step reads past its directory, through all later non-objects, to the next object or the end of the database (a build of `/a/` with 1 object, then 5,000 strings in `/b/`: "Processed 5001 entries"). Time only, no wrong answer. Probe: `/Users/f/fl/bench/016/015-20/review/probes/past/BuildPastDirProbe`.

Source: the H5 review of 015-20, 015-22 and 015-21, "Outside the changes"
(`/Users/f/fl/bench/016/015-20/handoff/review-findings.md`), 2026-11-03.

Done when: a test that fails on the code before the fix passes, and the fix
is in `main` after `before-commit.sh`.

First step: the probe, made a test.


Log
---

2026-11-03. Registered by the coordinator of release 2026.2 (016-02).

2026-11-09. Done by release 2026.4's indexes (020-10), in night 006-15: a build step reads only the directory's own keys, by the prefix of its files (020-10, 6.1); 4f8210f (020-10, I2 part 1). The test: PubTesterIndexJobs.testBuildStopsAtDir (a key after the directory and one in a subdirectory are not read), in `before-commit.sh`, passing on `main` at `b768ef0` (020-11). Status: done.
