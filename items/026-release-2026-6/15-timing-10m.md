# 026-15. The timing pass at 10M keys

Created 2026-11-14 by Frans Lundberg. Status: open (planned; to run when
the coordinator starts it).

The time that 2026.6's changes to reclaim cost or save at 10M keys, where
026-09 and 026-05 were measured in counts only: 026-04, section 2, item
1 ("one timing pass"), and 026-09, Q1 ("Not measured: time").

Frans, 2026-11-14, 11:35: "Yes, land it. Plan a 10M timing run for later
today, some time after 15:00. Won't attend this session after that and
will be back no sooner than 10:00 on Sunday, so that is a good period to
run performance testing."

The window: F53, unattended, with nothing else heavy on the machine. First
planned from 15:00 on Saturday 14 November to Sunday 09:30; then (Frans,
11:58, through coord-1114) the Lean provers run on F53 this evening and
night, and the timing pass runs **when the machine is calm after the
proofs, started by the coordinator**: when the provers stop (a usage
limit, say), tonight or a later night. run.sh takes the latest end of its
runs as its argument.

The plan, its scripts and the probes by the agent "timing" of coord-1114,
11:40 to 14:30. Everything is in /Users/f/fl/bench/2026-11-14/timing/
(called `timing/` below); nothing of it is to land.


## 1. What is measured and why

* **The question.** What 2026.6's changes to reclaim cost or save in
  time, at 10M keys, for data larger than the cache. So far they were
  measured in counts:
  * 026-09 (the keys-only scan) at 10M: a step's loads down 44 to 55 %,
    the steps down 14 to 20 %, the stream written up 1.2 to 4.4 %, back to
    empty's writes up 6.9 % (026-09, section 6.2).
  * 026-05 (P8, a step scans at its own time), 026-07 (the write buffer),
    026-08 (node size 30), 026-10 (a cut forgets ids and hashes) and the
    rest of 2026.6 so far: no timing at 10M.
  * The only timing pass, 024-29, section 9.4: workload (a) at 1M keys,
    one pass, its noise not known.
* **What is timed**, per run (one JVM): the wall time of the phase after
  the fill, the same user transactions on every build (the main
  measure); puts a second over the phase and over the window (from the
  end of the first reclaim iteration to the end); the latency of each
  user transaction (p50 to p99.99, the largest, and the count over 20 ms,
  P1's figure); the GC's pauses; the fill's time (no reclaim in it: R is
  forever until the fill ends). Reclaim's counts (cuts, steps, loads)
  are printed as a check that each build did what 026-04 and 026-09
  counted.
* **Hints, not measurements.** 026-09's count runs at 10M printed puts a
  second, on a shared machine with other runs in parallel
  (kscan/runs/before-10m-*.txt and after-10m-*.txt): in the window, (a)
  9,753 on `main` against 23,636 with 026-09, (b) 48,470 against 82,916,
  (c) 67,968 against 78,366. If that holds on a quiet machine, 026-09
  saves much of reclaim's time; this pass confirms or refutes it with
  repeated, interleaved runs.


## 2. The builds

* **R**: release 2026.5, the tag `release-2026.5` (`bf9ab5af`).
* **B**: `main` before 026-09, `3d2beedc`: 2026.6 so far (026-02, 026-05,
  026-06, 026-07, 026-08, 026-10, 026-11 and Javadoc).
* **C**: `main` with 026-09, `542927c5` (branch `026-09-keys-only-scan`,
  fetched from /Users/f/fl/bench/2026-11-13/kscan/clone). It lands on
  `main` as a fast-forward, so C is `main`'s Java after the landing.

The pairs: B against R is the rest of 2026.6, C against B is 026-09
alone, C against R is 2026.6 so far.

The harness on each: the clone `timing/clone` (of the main tree), a
worktree for each build (`timing/wt-R`, `wt-B`, `wt-C`, branches
`t2615-R`, `t2615-B`, `t2615-C`) with the same four commits on top:

* 026-04-lag's three, cherry-picked (`fc48e541`, `dfe2ca04`,
  `9859a419`): `FracRuns` (024-29) and CountGates' `f=` and `g4its=`.
  On B and C one conflict, in CountGates' header comment only, resolved
  by hand.
* 026-15's (`e133b193` on C): `FracRuns` prints TIME and LAT lines (the
  times, the latency percentiles), `twin=0` skips the twin, and `work=d
  timing=1` runs G4's fill, deletes and drive, timed, without the twin
  and G4's measures.

`FracRuns.java` is the same file on all three (md5 `b812f0f7`), and
CountGates' `Run`, `fill` and `value`, which the timed runs use, are the
same text in R and C. Built with `java/build.sh` (OpenJDK 27.0.1,
Homebrew) and preserved in `timing/builds/R`, `B`, `C` (bergdb.jar,
the stress classes, commit.txt); run.sh runs only these copies.


## 3. The workloads

026-04's four (024-29, section 9.1; 026-04, section 3) at n = 10M keys
`/k/%010d`, 100-byte values, f = 1/4 (the default), R = 1,000
transactions of a test clock, a `FileStream` with the builder's defaults
(startup distance 50 MB, cache indicator 200 MB, eviction on),
Reclaim.Stats on but its touch count off (`timing=1`), no twin:

* **(a) uniform overwrites**: a fill in random order (L0 = 6.44 GB),
  then 1,038,950 transactions of 10 puts of random keys.
* **(b) a queue**: a fill in key order (L0 = 1.81 GB), then 2,270,882
  transactions that each put 10 new keys and delete the 10 oldest.
* **(c) cold, 1 % hot**: a random fill (6.44 GB), then 4,293,233
  transactions of 10 puts among the first 1 % of the keys.
* **(d) back to empty** (G4's workload): "/a.txt", 10M keys filled in key
  order and deleted, 100 a transaction, with R from the start (startup
  distance 100 kB), then 40,000 drive transactions of 1,000 bytes.

The transaction counts of (a) to (c) are `main`'s third cut in 026-09's
runs (`cuts=99 max=...`, as kscan's rest2.sh): the same user work on
every build, B ending at about its third cut, C after its own (in (a)
C's third cut comes at 947,187), R at about its own (026-04: 1,049,715,
2,270,702, 4,301,439).

The data is larger than the cache, as in 024-29's pass: 1.8 to 6.4 GB
live after the fill, the stream up to 13 to 21 GB written and about 10 to
14 GB kept at its peak, against a 200 MB cache. F53 has 32 GB of memory
and the JVM a 6 GB heap, so the OS file cache holds much of the stream:
a load is a read from the file cache and its decoding, seldom a read
from the SSD (`purge` needs root).

Each run is one JVM: `-XX:+UseG1GC -Xms6g -Xmx6g`, a GC log
(`-Xlog:gc`), `--add-opens java.base/java.util=ALL-UNNAMED`.


## 4. Order and repeats

* **A round** is the four workloads in the order a, c, b, d; each
  workload is a block of three runs, R, B and C one after the other.
* **The builds' order in a block** turns with the round: RBC, BCR, CRB,
  CBR, RCB, BRC, and again, so that each build takes each place as often
  as the others and each pair is run in both orders.
* **Repeats**: rounds until no run fits before the end (Sunday 09:00).
  A run starts only if its expected duration (the longest of its
  workload this night, at least the estimate, plus 10 %) ends before
  then; a run that does not fit is skipped and a shorter one may go.
* **Paired comparison.** The three runs of a block are minutes apart, so
  a slow drift of the machine (heat, the file cache, a background job)
  is about the same for them; the analysis compares the runs of a block
  (paired by round), not only the medians.
* **Before each run**: 30 s of pause, then the quiet check (3 checks 20 s
  apart: no other java, lean, lake, night.sh or gate script above 20 %
  CPU, all processes below 150 % CPU together, the 1-minute load below
  4), waiting up to 30 minutes; a run that starts without it is marked
  `quiet=0` and left out of the tables (analyze.py `--all` takes it).
  Free disk at least 40 GB.


## 5. Expected duration

(The probes' numbers follow when they end.)


## 6. What counts as a gain or a loss

* **The main measure** is the phase's wall time for the same user
  transactions (a to c) and the total of fill, deletes and drive (d).
* **For each pair** (B/R, C/B, C/R) and workload, analyze.py gives the
  ratio of the medians and the ratio of the runs of each round (paired).
* **A gain**: every round's paired ratio below 1 (at least 3 rounds)
  and the ratio of the medians below 1 minus the noise, the noise being
  the larger of 3 % and either build's spread ((max - min) / median of
  its runs). **A loss**: the same above 1. Anything else is **within
  the noise**; with fewer than 3 rounds, no verdict.
* **The latencies** (p99, p99.9, the largest, the count over 20 ms) are
  reported as measured, without a rule: tails are noisy; a tail that
  doubles in every round is called out.
* **What the counts lead to expect**: C faster than B in (a) to (c), as
  its steps load about half as much (026-09, 6.2) and its extra writes
  are appends of a few %; in (d) C may be slower, as it rewrites 30 %
  more values during the fill and the deletes (026-09, 6.2).


## 7. Risks

* **Noise from other work.** The coordinator's and other sessions'
  work in the night: run.sh takes all six heavy-run slots (slot.sh
  take-timing) and holds them to the end, and the quiet check runs
  before each run; neither stops a session that does not use the slots.
  The session's own activity (tool calls) disturbs timing too (memory
  of 006-02): the coordinator stays idle or light while it runs.
* **A stale slot.** heavy2.lock has been held since 02:55 ("cost
  HeightsFitsR build"), with no such process running at 11:50. run.sh
  waits 10 minutes for the slots, then goes on with those it has (they
  still block other runs); the coordinator may release the stale one
  before 15:00.
* **The file cache.** The stream mostly fits in the OS file cache, so a
  load costs a system call and decoding, not an SSD read. A database
  larger than the memory (100M keys) would weigh loads more, so C's
  saving would be larger there; not measured here.
* **The harness's own work**: key strings by String.format, the
  accounting of records per transaction, Reclaim.Stats; the same on
  every build, it dilutes the ratios a little.
* **The test clock**: R is 1,000 transactions, not 1 s, so every build
  runs reclaim on the same schedule in transactions whatever its speed;
  that is what makes the user work the same.
* **Heat and drift**: hours of runs at full load on one core and more;
  the turning order and the paired ratios take care of a slow drift,
  not of a step change between two runs of a block.
* **Failures**: a run is killed at 3 times its estimate (perl's alarm);
  a failed run is logged and the next one goes on; 4 failures in a row
  end the pass with FAILED. caffeinate -i keeps the Mac awake (on
  power); Spotlight does not index the data directories (`.noindex`).
* **Disk**: 361 GB free at 11:50; a run peaks at about 14 GB, deleted
  after it.


## 8. How to run, the outputs, and night.sh

The coordinator, at 15:00, one command:

    nohup sh /Users/f/fl/bench/2026-11-14/timing/run.sh >/dev/null 2>&1 &

* `timing/progress.log`: a line at each start (with its expected end)
  and end; `timing/results.txt`: one RUN line a run (key=value);
  `timing/runs/`: each run's output and GC log; `timing/analysis.txt`:
  analyze.py's tables, renewed after each run; `timing/DONE` at the end,
  `timing/FAILED` with a reason if it gives up.
* `touch timing/STOP` ends it early: the run going on finishes, no other
  starts, DONE as usual.
* Options (environment): `END="2026-11-15 02:00"` ends sooner, `ROUNDS=N`
  stops after N rounds, `THEN_NIGHT=1` starts java/night.sh in the main
  tree when done, if 2.5 hours remain before 09:30.
* `python3 timing/analyze.py timing/results.txt` gives the tables at any
  time.

night.sh: (estimate follows with the probes).


State
=====

2026-11-14, 11:40: registered by coord-1114; the agent "timing" writes
the plan (sections to follow) and its scripts.

(Updated at the end of the agent's work.)
