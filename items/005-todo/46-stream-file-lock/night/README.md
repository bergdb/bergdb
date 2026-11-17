005-46's night steps
====================

Written 2026-10-27 by Claude (Opus 5.5, Claude Code), a subagent of the
session f1-cd, for W1.3 and W1.4 of 006-09 (section 3): the measurements of
005-46's "Done when" that need a quiet F53. 006-09's conductor
(`/Users/f/fl/bench/006-09/night/conductor.sh`) runs each step in its quiet
windows, when `STEP.sh.READY` exists, once.


Steps
-----

| Script | Label | Minutes | What |
|---|---|---|---|
| `soak.sh` | 46-soak | about 47, stopped at 115 | W1.3. P4's soak under ZGC on HEAD, as 009-03 and 009-04 ran it: 8 GB heap, 1.6 GB budget, 200 commits and 3 × 5,000 reads a second, retention 300 s, 30 measured minutes, one restart. The warm-up waits up to 60 minutes for its first cut, and the measured phase may extend by 15, hence 115. |
| `props.sh` | 46-props | about 6, stopped at 12 | W1.4. Props (MEM, CORE, SS), c1f1f15 and HEAD in turns, four rounds (ABBA ABBA); another pair of builds with `JARS="old new"` and `B`. |
| `perf-ab.sh` | (the main session's) | about 14, 28 with a second run; stopped at 40 | 009-01's "done" item 7: `performance.sh ab` with the quick suite, release 2026.1 against HEAD, no budget, in turns (ABBA), G1, 8 GB heap; the run 009-03 could not make on 2026-10-26. If it alerts, a second ab run, and the first reference against both candidate sessions (`confirm.txt`). Exit 0 when complete, alerts or not. |
| `scalebench-c.sh` | 46-scalebench-c | about 48, stopped at 65 | W1.4. 009-03's ScaleBench block from the OS's cache (C): 10M key24 keys, the default startup distance (10 MB, as 004-02 and 009-03), the phases warm, uniform, hot and threads (1, 2, 4, 8); 665 MB with G1 and ZGC, 133 MB with G1. One database, loaded by HEAD's jar; two rounds, the jars' order reversed in the second. |

Each runs with `sh SCRIPT` from any directory, takes its deadline from its
`# minutes:` line (a watchdog stops its JVMs there), and exits 0 on
success. `SMOKE=1` gives a run of seconds, with its outputs in
`/Users/f/fl/bench/006-09/w1/smoke`. `lib.sh` holds what they share;
`soaksum.py` reports on a soak, `nightsum.py` writes `out/summary.txt`.


The jars
--------

Made by `prep.sh` at 12:13, 2026-10-27, in `/Users/f/fl/bench/006-09/w1`
(not in the block; run it again for another HEAD):

* `head/`: `f9e295d`, the main tree's HEAD then: 005-46 (`1165c90`) and,
  after it, 005-55 (`14022ad`), 005-57's part 1 (`e773562`) and 005-51
  (`043a09c`).
* `c1f1f15/`: 005-50, the commit before 005-46.
* In `head/java/build/perf/builds/`, for `perf-ab.sh`: `2026.1`, a copy of
  the preserved build in the 009 worktree (the release commit `8e579c6`,
  jar `1c913899`), and `head-4f7cd60` (`performance.sh build`), each with
  the harness compiled by the smoke test, so that nothing is built in the
  block. The sessions go to `head/java/build/perf/runs/`.
* `sb/`: ScaleBench (004-02) with 009-03's port (`ScaleBench-009.diff`) and
  `java/stress/PerfUtil.java` (the same at both commits), compiled against
  each jar; 004-02's `pidio`.

If HEAD reads fewer a second than c1f1f15, `sh prep.sh 1165c90` and the
step again tell whether 005-46 is the cause or a later commit.


Outputs
-------

In `out/` here: `runs.txt` (each step's start and end, and its runs),
`summary.txt`, and a directory for each step (`soak/`, `props/`,
`scalebench-c/`, `perf-ab/`). Not here: the GC logs of ScaleBench, in
`/Users/f/fl/bench/006-09/w1/raw/scalebench-c/`, and the soak's run
directory with its GC log, in the clone, `head/java/build/soak/NAME/`.
The conductor keeps each step's stdout in
`/Users/f/fl/bench/006-09/night/out/LABEL.txt`.


What to look for
----------------

* The soak (`soak/NAME-report.txt`): 005-46's "the cuts are no longer its
  slowest commits and reads" (009-04, section 7.3). The report gives the
  slowest commits with their uptimes, each measured cut with its slowest
  commit and that commit's rank, the longest reads (no uptimes: the soak
  keeps none for reads), and the disk's waits: the writer's for room in
  the write buffer, and the file forces, directory forces and deletes,
  each with the five longest and their uptimes. The deletes now run on
  the thread `FileStream-cut`. Before, under ZGC (009-03's soak at
  `f4e93d8`): the cuts' commits 171.0, 63.8 and 26.2 ms, the three
  slowest; the longest forward scan 166 ms, historical get 25.9 ms,
  latest get 11.8 ms, pacing delay 166 ms.
* Props: CORE, lower is faster; 009-03 had 0.29 and 0.29 for 2026.1, 0.24
  and 0.22 for the branch. "No fewer reads a second": HEAD's CORE no
  higher than c1f1f15's beyond the spread of the rounds.
* ScaleBench (`summary.txt`, section 3): for each configuration, each run,
  the means of each jar, and HEAD's gets a second against c1f1f15's. The
  column "blocked reading" is the share of the sampled threads that waited
  on a file's or the stream's monitor (3.2 percent at 665 MB with ZGC in
  009-03); with 005-46 it should be 0.


* `performance.sh ab` (`perf-ab/ab-1.txt`, summary section 4): the
  comparison's alerts. 009-03's run with a 4 GB budget had one,
  unconfirmed: `get_longkey` 9.3 percent fewer on one thread.


Smoke tests
-----------

2026-10-27, 12:15 to 12:25, `SMOKE=1` for each script, from `/tmp`, while
other sessions ran gates: all three exit 0. With `LIMIT=1` (a one-minute
deadline) `scalebench-c.sh` stopped its running JVM, skipped the rest and
exited 1, with no process left. By hand: ScaleBench under eviction (300,000
keys, a 3 MB budget) on both jars, and Props on HEAD's jar (38.6 s); both
fine. `perf-ab.sh`, 12:37 to 12:45, with `perf-ab-smoke.suite`: its retries
on a busy machine and FORCE=1, the second run and the confirmation
(`AB2=1`), and the summaries; exit 0.

2026-10-28, by Claude (Opus 5.5, Claude Code): Props exited 1 in the
block although it had measured CORE. `Core` prints a row of progress dots
and then its result on the same line (`....CORE:0.24 (...)`), and both
`props.sh` and `nightsum.py` read only a line that starts with `CORE:`, so
the summary said "CORE ?". Both now allow the dots, and `summary.txt` is
made again from the block's files: CORE 0.23, 0.23, 0.23, 0.24 for
`c1f1f15` and 0.24, 0.23, 0.22, 0.24 for HEAD (rounds 1 to 4; means 0.233
and 0.232). The smoke test had run `Mem` only, which prints no dots, so it
could not find this. `SMOKE=1` now runs `Props` itself, one round of each
jar (about 80 s), and the step fails unless `summary.txt` has every run's
MEM, CORE and SS and a CORE mean for each jar; it caught a run with its
CORE line removed. Smoke test 09:30, exit 0 (CORE 0.26 and 0.27 on a busy
machine). `lib.sh` takes the step's directory from `$0`, so that a clone's
scripts use the clone's `lib.sh` and `nightsum.py`.
