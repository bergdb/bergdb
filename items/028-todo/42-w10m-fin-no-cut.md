028-42. Fix: timing.sh's scenario w10m-fin never reaches a cut
==============================================================

Status: open. Kind: Fix. Frans: none.
Created 2026-11-21 by Frans Lundberg.

What: `java/timing.sh`'s perf step (`performance.sh ab`, the suite
`stress/performance-release.suite`) failed on its first full run,
2026-11-21 01:52 on `092179f6`: the scenario `w10m-fin` (`n=10000000
valsize=8 work=uniform retain=0.1 mincuts=1 ops=2000000 maxops=4000000`)
wants at least one physical cut in 4,000,000 commits and got none
(`Perf$PerfFailure: only 0 physical cuts in 4000000 commits; wanted 1
(raise perf.maxops)`). The stream grew from 5.8 GB to 9.1 GB with
nothing reclaimed. Release 2026.5, the reference of the same run, also
had 0 cuts at 3.8 million commits, so the scenario's setting is the
cause, not a change of the database. The suite came with 028-23
(2026-11-19); its earlier run, 2026-11-20 04:14, was refused as the
machine was not quiet, so this was its first run.

Why: before a release, `java/timing.sh` runs on a commit near it
(AGENTS.md); a scenario that cannot pass fails the step and gives no
comparison of the other scenarios.

Frans: none.

Done when: `w10m-fin` reaches its cut on both the candidate and
release 2026.5 (a larger maxops, or the settings that make reclaim's
first cut come within it, found by a run of the scenario alone), and a
full `java/timing.sh` on a quiet machine gives its comparison.
`java/before-commit.sh` BEFORE COMMIT OK if Java changes.

The same run's other figures (java/build/timing/2026-11-21-0152,
report.txt): CORE ratio 1.102 against 2026.5 (alert above 1.10; 028-19),
longest get or commit 19.0 ms against 14.6 ms (guide 50 ms).
