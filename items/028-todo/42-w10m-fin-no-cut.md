028-42. Fix: timing.sh's scenario w10m-fin never reaches a cut
==============================================================

Status: done. Kind: Fix. Frans: none.
Created 2026-11-21 by Frans Lundberg.

What: `java/timing.sh`'s perf step (`performance.sh ab`, the suite
`stress/performance-release.suite`) failed on its first full run,
2026-11-21 01:52 on `092179f6`: the scenario `w10m-fin` (`n=10000000
valsize=8 work=uniform retain=0.1 mincuts=1 ops=2000000 maxops=4000000`)
wants at least one physical cut in 4,000,000 commits and got none
(`Perf$PerfFailure: only 0 physical cuts in 4000000 commits; wanted 1
(raise perf.maxops)`). The stream grew from 5.8 GB to 9.1 GB with
nothing reclaimed. Release 2026.5, the reference of the same run, ran
first and passed: its cut came after 3,874,405 commits, 3 % below
maxops (its progress lines, every 10 s, show 0 cuts up to 3.80M
commits); the run stopped at the candidate's failure. The suite came
with 028-23 (2026-11-19); its earlier run, 2026-11-20 04:14, was refused as the
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


Findings
--------

The scenario's setting, not a fault of reclaim (2026-11-21). Runs of
w10m-fin alone on F53, Perf with the suite's settings and maxops
10,000,000, and a copy of the harness that printed reclaim's iteration
table with each progress line (not kept); main at 092179f6 (no Java
change since) and release 2026.5's build of timing.sh:

* The first iteration begins with the measured phase (tStart 301,001,
  in transactions of the simulated clock) and has its pCut at its own
  pStart, the end of the load and the warmup (5.1 to 5.2 GB). It
  rewrites each of the 10M values, paced by the allowance: a quarter of
  the stream's growth since pStart (the default internal fraction).
  The table showed it progressing steadily on both builds: on main 1.97M
  of the 10M KVs after 0.59M commits, 6.85M after 2.07M, 9.37M after
  2.82M; `rewritten` a quarter of the growth throughout.
* Its cut frees all before pCut at once; until then nothing goes, so
  "kept" equal to "stream" in the progress lines is expected. The cut
  comes when the iteration is done,
  the startup pos has passed its pSafe, and its tEnd is older than the
  retention: retain=0.1 is 0.1 updates a key, 1,000,000 transactions.
* Main: the first iteration ended at 3,309,462 (about 3.01M commits),
  the cut came after 4,009,705 commits. Release 2026.5: ended at
  3,174,995 (about 2.87M commits), cut after 3,876,640 commits. Each cut
  is the iteration's end plus the retention, plus a few thousand commits
  for pSafe and the durable table.
* Main's first iteration takes about 135,000 commits more than 2026.5's:
  its stream grows less a commit (PE's smaller records; 1,179 against
  1,256 bytes appended a put in the failed run), and since 028-26
  (2026-11-19) its steps also charge the index nodes that PE makes
  after the step's row, so the same rewrite needs more growth. In
  026-25, section 7, before 028-26, PE cut after 2.99M commits and the
  old writer after 3.88M: the scenario's maxops had a margin of 3 % for
  the old writer from the start.

The change: `java/stress/performance-release.suite`, w10m-fin's maxops
4,000,000 to 6,000,000, and a comment on what the first cut waits for.
The other settings stay, so the scenario still measures the write speed
of a 10M database while reclaim works, up to and including its first
cut; the run ends at the cut, so its length is as before (about 1
minute of commits after a load of 1 minute, on F53). Margin: 1.50 times
main's cut, 1.55 times 2026.5's. A Java change is not needed.

Check: `performance.sh ab` with SUITE=release, ONLY='^w10m-fin$',
RUNS=1, 2026.5's build against this tree (FORCE=1: a check of the cut,
not a timing reference): both runs passed with their cut, 2026.5
after 3,876,374 commits and this tree after 4,011,943, and the
comparison ran (exit code 0).


State
-----

2026-11-21. Done except the done criterion's full `java/timing.sh` on a
quiet machine, which the day's coordinator runs after this change is
merged.


Log
---

2026-11-21. Registered by coord-1120.

2026-11-21. Taken and done by an agent of coord-1120 on the branch
`028-42-w10m-fin`: the setting, maxops 6,000,000; no fault of reclaim.
