# 026-15. The timing pass at 10M keys

Created 2026-11-14 by Frans Lundberg. Status: done (run 2026-11-14 15:58 to
2026-11-15 03:11; results in section 9).

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

* **R**: release 2026.5, the tag `release-2026.5` (`3611130c`).
* **B**: `main` before 026-09, `d6774508`: 2026.6 so far (026-02, 026-05,
  026-06, 026-07, 026-08, 026-10, 026-11 and Javadoc).
* **C**: `main` with 026-09, `4c645015` (branch `026-09-keys-only-scan`,
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
and the JVM a 6 GB heap, so on a quiet machine the OS file cache holds
much of the stream: a load is then mostly a read from the file cache and
its decoding (`purge`, for a cold file cache, needs root). With less
memory free the loads go to the SSD: in the probes, R's run of (a), with
a second JVM and the Lean gates beside it, had its main thread on the
CPU 37 % of the time (557 s in 1,522 s), the stack samples in `pread`.

Each run is one JVM: `-XX:+UseG1GC -Xms6g -Xmx6g`, a GC log
(`-Xlog:gc`), `--add-opens java.base/java.util=ALL-UNNAMED`.


## 4. Order and repeats

* **A round** is the four workloads in the order a, c, b, d; each
  workload is a block of three runs, R, B and C one after the other.
* **The builds' order in a block** turns with the round: RBC, BCR, CRB,
  CBR, RCB, BRC, and again, so that each build takes each place as often
  as the others and each pair is run in both orders.
* **Repeats**: rounds until no run fits before the end that the
  coordinator gives. A run starts only if its expected duration (the
  longest seen for its build and workload, else the probe's, plus 10 %)
  ends before then; a run that does not fit is skipped and a shorter one
  may go. 3 rounds are the least for a verdict (section 6).
* **Paired comparison.** The three runs of a block are minutes apart, so
  a slow drift of the machine (heat, the file cache, a background job)
  is about the same for them; the analysis compares the runs of a block
  (paired by session and round), not only the medians.
* **Before each run**: 30 s of pause, then the quiet check (3 checks 20 s
  apart: no other java, lean, lake, night.sh or gate script above 20 %
  CPU, all processes below 250 % CPU together, the 1-minute load below
  4), waiting up to 30 minutes (QUIETWAIT); a run that starts without it
  is marked `quiet=0` and left out of the tables (analyze.py `--all`
  takes it). Waiting for quiet never fails the pass. Free disk at least
  40 GB. (F53 idle with VS Code open: about 90 to 110 % CPU in all,
  WindowServer and VS Code's renderer most of it.)


## 5. Expected duration: the probes

The probes, 2026-11-14, 11:44 to 13:00: one run of each workload on each
build at 10M keys, through the same FracRuns arguments and JVM flags as
run.sh (`timing/probe/probe.sh`, outputs in `timing/probe/`). Not timing
runs: two JVMs at a time (lane 1 the (a) runs, lane 2 the others), and
the coordinator's Lean gates beside them until about 12:08; C's run of
(a), 12:52 to 13:00, ran alone. Seconds; puts a second in the window;
the latencies of the window's transactions (d: of the deletes) in µs.

| Probe | Wall  | Fill | Phase | Window | Puts/s | p50   | p99    | >20 ms |
|---|---|---|---|---|---|---|---|---|
| R a   | 2,862 | 131  | 2,729 | 1,835  | 3,448  | 1,999 | 13,805 | 1,207  |
| B a   | 1,178 | 98   | 1,078 | 577    | 10,937 | 521   | 4,949  | 37     |
| C a   | 485   | 78   | 406   | 241    | 26,181 | 225   | 2,147  | 27     |
| R c   | 928   | 130  | 795   | 387    | 59,398 | 42    | 2,019  | 31     |
| B c   | 743   | 98   | 644   | 344    | 66,904 | 40    | 1,024  | 23     |
| C c   | 753   | 96   | 656   | 333    | 68,990 | 44    | 1,154  | 43     |
| R b   | 525   | 23   | 473   | 321    | 39,648 | 75    | 2,056  | 109    |
| B b   | 388   | 22   | 341   | 214    | 59,407 | 53    | 921    | 27     |
| C b   | 351   | 20   | 302   | 183    | 69,481 | 50    | 782    | 20     |
| R d   | 89    | 43   | 89    |        |        | 407   | 759    | 8      |
| B d   | 90    | 41   | 89    |        |        | 446   | 748    | 12     |
| C d   | 84    | 40   | 84    |        |        | 384   | 789    | 8      |

* **Every run worked**, and B's and C's counts are 026-09's (section
  6.2): the same steps in (a), (b) and (c) (B 568,053, 582,109, 682,339;
  C 491,210, 477,651, 572,022), the loads within 0.01 %. R's (a) did
  645,181 steps, 2 cuts by the last transaction.
* **Not to be read as results**: the (a) runs overlapped other work in
  different amounts (R's with the Lean gates and lane 2, B's with lane 2,
  C's alone). They are the durations the pass plans with; the pass
  measures. The largest latencies (up to 1.3 s in R's (b)) are GC pauses
  of the shared machine (G1 pauses of 0.8 and 1.3 s in R's runs).
* **A round** by these numbers: (a) 4,525 s, (c) 2,424 s, (b) 1,264 s,
  (d) 263 s, plus 12 pauses and quiet checks of about 70 s: about **2.6
  hours**; on a quiet machine likely nearer 2 hours (R's and B's (a) had
  company). 3 rounds: 6 to 8 hours.
* **With W calm hours** the pass does about W / 2.3 rounds. Started at
  15:00 with the end at 09:00 it would have done 6 to 8. For a short
  window (under 7 hours), `WORKS="a b"` (about 1.7 hours a round: (a)
  is where the hints are largest, (b) the queue) gives 3 rounds in about
  5 hours.
* run.sh's estimates (est0) are these walls, (a) of C rounded up to 600
  s; each run's time limit is 4 times its estimate plus 5 minutes (R's
  (a): 3.3 hours).


## 6. What counts as a gain or a loss

* **The main measure** is the phase's wall time for the same user
  transactions (a to c) and the total of fill, deletes and drive (d);
  the window's time (the same transactions on B and C: both reach the
  end of the first iteration at the same transaction) is compared too.
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
* **What the counts and the probes lead to expect**: C faster than B in
  (a), much (the probes: 406 s against 1,078 s of phase, with company),
  and a little in (b); in (c) about the same (the probes: 656 and 644 s,
  as most of (c)'s time is the user's puts, its steps loading little of
  the hot range); (d) about the same (C rewrites 30 % more values during
  the fill and deletes, 026-09, 6.2, but the probes show 84 against 90
  s). B against R: faster in (a) and (b) by the probes, to be measured.


## 7. Risks

* **The provers come back.** The pass starts when the provers stop; if
  they start again (a usage limit reset), two cases:
  * with `SLOTS=1` (the default) run.sh holds all six heavy-run slots
    (slot.sh take-timing) to its end, so provers that take a slot through
    slot.sh wait until the pass ends;
  * with `SLOTS=0` they start, and the runs that overlap them wait up to
    QUIETWAIT and then run marked `quiet=0`, left out of the tables:
    machine time spent for nothing, and the provers slowed.
  The coordinator chooses at the start (section 8).
* **Noise from other work** that takes no slot (a session's own builds,
  its tool calls, the VS Code window): the quiet check before each run
  catches what is running then, not what starts during a run. The
  coordinator stays idle or light while the pass runs (006-02's
  finding: a session's own activity disturbs timing).
* **A stale slot.** heavy2.lock has been held since 02:55 ("cost
  HeightsFitsR build"), with no such process at 11:50 and 13:00. run.sh
  waits 10 minutes (SLOTWAIT) for all slots, then goes on with those it
  has (they still block others) and logs the owners; the coordinator may
  release the stale one first.
* **The file cache** decides how much a load costs (section 3): the pass
  measures a quiet machine with about 20 GB for the file cache. A
  database larger than the memory (100M keys) would weigh loads more,
  where C's saving would be larger; not measured.
* **The harness's own work**: key strings by String.format, the
  accounting of records per transaction, Reclaim.Stats; the same on
  every build, it dilutes the ratios a little.
* **The test clock**: R is 1,000 transactions, not 1 s, so every build
  runs reclaim on the same schedule in transactions whatever its speed;
  that is what makes the user work the same.
* **Heat and drift**: hours of runs; the turning order and the paired
  ratios take care of a slow drift, not of a step change within a block.
* **Failures**: a run is killed at its limit (perl's alarm, exit 142); a
  failed run is logged and the next one goes on; 4 failures in a row end
  the pass with FAILED. caffeinate -i keeps the Mac awake while run.sh
  lives (on power); Spotlight does not index the data directories
  (`.noindex`).
* **Disk**: 373 GB free at 13:00; a run peaks at about 14 GB (and 21 GB
  of stream written), deleted after it; run.sh needs 40 GB free.
* **performance.sh** is not used: its suites go to 1M keys, its databases
  have no eviction (`noEvict()`, test-only) and fit the cache, the small
  and in-cache case that matters last.


## 8. How to run, the outputs, and night.sh

The coordinator, when the machine is calm, one command with the latest
end of the runs ("YYYY-MM-DD HH:MM", local time):

    nohup sh /Users/f/fl/bench/2026-11-14/timing/run.sh "2026-11-15 09:00" >/dev/null 2>&1 &

* Options, in the environment before `sh`: `SLOTS=0` (take no slots,
  section 7), `WORKS="a b"` (fewer workloads), `ROUNDS=N` (stop after N
  rounds), `QUIETWAIT=S` (the longest wait for quiet before a run, 1,800
  s), `THEN_NIGHT=1` (when done, start java/night.sh in the main tree if
  2.5 hours remain before the end plus 30 minutes).
* `touch timing/STOP` ends it early: the run going on finishes, no other
  starts, DONE as usual; the next start removes STOP.
* **Outputs**: `timing/progress.log`, a line at each start (with its
  expected end) and end; `timing/results.txt`, one RUN line a run
  (key=value, with its session and round); `timing/runs/`, each run's
  output and GC log; `timing/analysis.txt`, analyze.py's tables, renewed
  after each run; `timing/DONE` at the end, `timing/FAILED` with a reason
  if it gives up. A second start (another night) appends to the same
  results.txt; analyze.py takes all sessions.
* `python3 timing/analyze.py timing/results.txt` gives the tables at any
  time (markdown, rows within 100 characters but for the wide ones).

**night.sh after the pass.** The last runs in the main tree's
`java/build/night/`: 125 minutes (2026-11-11), 153 minutes (2026-11-12,
of it 53 for the tree tests); `night.sh large` 396 minutes (2026-11-09,
the large conformance set 288 of them). So night.sh fits when the timing
ends 2.5 hours before the window's end (7 hours for `large`). With the
timing first: a calm window of 9.5 hours or more holds 3 rounds and
night.sh (`THEN_NIGHT=1`, the end 2.5 hours before the window's); a
shorter one, the timing alone. From 15:00 to 09:30 (the first plan):
timing until about 06:45 (6 or 7 rounds), then night.sh.


## 9. Results

Run on F53 from 2026-11-14, 15:58, to 2026-11-15, 03:11, started by
coord-1114's waiter after 025-02's provers had ended; stopped by STOP
after 105 runs (9 rounds; Frans, 03:07, asked for the proofs to go on).
Every run ok, every run quiet (`quiet=1`). analyze.py's tables are
[15-timing-10m/analysis.txt](15-timing-10m/analysis.txt), the runs
[15-timing-10m/results.txt](15-timing-10m/results.txt).

The phase's wall time, ratio of the medians, with section 6's verdict
(9 rounds paired; d 8):

* **(a) uniform overwrites:** B/R 0.959 (gain), C/B 0.953 (gain), C/R
  0.914 (gain, 8.6 % less time). The window (after the first reclaim
  iteration): C/B 0.934, C/R 0.905.
* **(b) a queue:** B/R 0.919, C/B 0.914, C/R 0.840 (all gains; 16 % less
  time). Window: C/B 0.859, C/R 0.797.
* **(c) cold, 1 % hot:** B/R 0.969, C/B 0.942, C/R 0.913 (gains). Window:
  B/R 0.979 (within the noise), C/B 0.889, C/R 0.871.
* **(d) back to empty:** B/R 0.999 (within the noise), C/B 0.942, C/R
  0.942 (gains). Section 6 expected C to be slower here (30 % more
  values rewritten); it is 5.8 % faster.

What it means: 026-09 (the keys-only scan) saves time in every workload
at 10M keys, 4.7 to 8.6 % of the phase and 6.6 to 14.1 % of the window
in (a) to (c), with half the loads (C's loads 21.7M against B's 43.5M in
(a)). The rest of 2026.6 (B against R) saves 3 to 8 % in (a) to (c) and
nothing in (d). The latencies' tails (p99, p99.9, the largest) are about
the same for the three builds; C has the fewest transactions over 20 ms
in (a) to (c) (44, 31, 38 against R's 57, 42, 46). Measured with the
stream mostly in the OS file cache (section 7): with a database larger
than the memory C's saving would likely be larger.


State
=====

2026-11-14, 11:40: registered by coord-1114; the agent "timing" writes
the plan (sections to follow) and its scripts.

2026-11-14, 13:10: **READY** (`timing/READY`). The plan is sections 1 to
8. The builds R, B and C are made and preserved (`timing/builds/`); the
probes at 10M ran, every run worked, and B's and C's counts match
026-09's (section 5). run.sh was tried end to end at n = 20,000 on all
three builds (`timing/dry/`: 12 of 12 runs, DONE, analysis.txt), the
slots' take and release with a tiny run, the quiet check's wait and its
time-out, the refusal of a missing or past end time. Changed at 11:58
(Frans, through coord-1114): no start at 15:00; the coordinator starts
it when the machine is calm after the proofs, with the end time as the
argument. Before the start, for the coordinator: release heavy2.lock if
stale; choose SLOTS (section 7); give the end; THEN_NIGHT=1 if night.sh
is to follow. Not done: the pass itself. Nothing here is committed;
nothing of `timing/` is to land.

2026-11-15, 06:10 (coord-1114): run and done; section 9. The pass's
files stay in /Users/f/fl/bench/2026-11-14/timing/; the tables and the
run lines are copied to 15-timing-10m/.
