# BergDB performance harness

Written by Claude (Sonnet 5.5) for Frans Lundberg, 2026-10-14.

Status: **the harness exists and has been smoke-tested; no reference has been recorded.**
This is the tooling for task 3 of the [Level 3 plan](level3-plan.md), the performance
reference before Level 4. The reference runs, `docs/level3-performance.md` and the
frozen thresholds follow task 1 (the power-loss repairs change the storage path that
the durable-commit and restart measurements use) and are not part of this document.
Nothing here is a measurement of the database.

## What there is

| File | Purpose |
|---|---|
| [java/stress/performance.sh](../java/stress/performance.sh) | The runner: `smoke`, `reference`, `build`, `ab`, `compare`, `summary`, `calibrate`, `promote`, `list` |
| [java/stress/performance.suite](../java/stress/performance.suite) | The principal scenarios (read, write, restart), with the runs of each |
| [java/stress/performance-grid.suite](../java/stress/performance-grid.suite) | The rest of the grid (`SUITE=grid`) |
| [java/stress/performance-smoke.suite](../java/stress/performance-smoke.suite) | Small scenarios for `smoke` |
| [java/stress/Perf.java](../java/stress/Perf.java) | The harness: one JVM per run, modes `write`, `read`, `restart` |
| [java/stress/PerfUtil.java](../java/stress/PerfUtil.java) | Bounded histogram, JSON, GC log reader, JVM facts |
| [java/stress/PerfTool.java](../java/stress/PerfTool.java) | `finish` (GC log into the result), `summary`, `compare`, `calibrate`, `selftest` |

`LoadTest.java` and `ReclaimCost.java` are not changed; the harness reuses their
definitions (the load and update traces, WE and SE, the record attribution of
`Reclaim.Stats`), because the gates use those programs and must not move. The
reader harness (`ReclaimReaders.java`) checks correctness under cuts, not speed; its
scan check is reused in `Perf.verifyScan`.

## Running

    java/stress/performance.sh smoke                  # a few minutes; checks the plumbing and the correctness checks
    java/stress/performance.sh build level3-ref       # a preserved copy of the sources and its jar (never replaced)
    BUILD=level3-ref java/stress/performance.sh reference ref1    # the principal suite, about 1.5 hours
    java/stress/performance.sh ab level3-ref current  # a candidate against the reference, alternating (ABBA)
    java/stress/performance.sh compare REFSESSION CANDSESSION [CAND2SESSION]
    java/stress/performance.sh summary SESSION --md   # tables for the report

The header of `performance.sh` lists the environment variables (`SUITE`, `RUNS`, `ONLY`, `GC`,
`HEAP`, `OSCACHE`, `FORCE`, `DISKMIN_GB`, ...). `PROGRESS` lines in a run's stdout file show a long run
advancing. Sessions are written to `java/build/perf/runs/COMMIT-TIME-SUITE-GC-HEAP[-LABEL]/`
(ignored by Git): `session.json`, and `SCENARIO/runK/` with, per JVM, the stdout, the GC and
safepoint log, `MODE.result.json` (compact) and `MODE.raw.json` (histograms, one-second
throughput, samples, the slowest commits). `promote` copies the compact files to
`java/bench/reference/NAME/`, which is what is committed. Preserved builds are in
`java/build/perf/builds/`.

The runner refuses to start a reference run when the machine is not quiet (under 90%
idle CPU); `FORCE=1` overrides, and the results are then not a reference.

## How the sizes were chosen

Single pilot runs on 2026-10-14, on a machine that was not idle (another job was running; the
numbers are not cited here and are not a reference), set the operation counts so that every
finite-retention scenario reaches at least six physical cuts without the extension: 100-byte
values 4.3 million commits, 1,000-byte values 1.0 to 1.4 million, 10 KB values 0.3 million; the
suite uses a margin above that, so that the runs of a scenario have equal length and a finite
scenario has the same trace as its infinite partner. `mincuts` and `maxops` guard the assumption: a
run that cannot reach the cuts fails. The principal suite takes about 1 to 1.5 hours per set of
runs on this machine, the grid about as much again.

## What a run is

Every run is a separate JVM: G1 (or `GC=zgc`, `GC=parallel`, a separate configuration),
`-Xms = -Xmx` (default 8 GB, not pretouched, so that the resident set size is informative),
assertions **off** (the gates run with them on), unified logging of `gc*` and `safepoint`
to the run directory. The flags are recorded in each result and must be equal to compare.

* **write**: load `n` keys (a seeded shuffle, 100 per transaction), a warm-up of one update
  per key, then the *measured phase* on a `FileStream` on disk. Then `sync`, a restart
  in the same JVM, and a check of every key (`verify.sec`, reported separately).
  `commit=append` measures `execute()`; `commit=durable` also `sync(ORDINARY)` and reports
  both (`commit.append.*`, `commit.durable.*`); `threads=T` committing threads (their keys
  are disjoint, so that the final state does not depend on the interleaving); `rate=R`
  paces the commits and reports `delay.*`, from the *intended* arrival to completion.
  `retain=K` switches finite retention on at the start of the measured phase (K updates per
  key within the window; reclaim then runs automatically) and the phase goes on until
  `mincuts` physical cuts (files deleted) were observed, at most `maxops`.
  `retain=inf` is the default of the API.
* **read**: load, a history of updates with a snapshot at the middle (infinite retention),
  warm-up, then, for latest gets, historical gets and long-key gets, an uncounted warm-up
  window, `windows` windows of untimed bulk gets (the throughput is the median of the
  windows, with their minimum, maximum and CV) and a timed pass (latency distribution); gets from `mtthreads`
  threads; forward and backward scans of `scanlen` KVs, also at the historical time. Every
  value is checked against the model; the first scans completely (order, count, values).
  Everything is resident (no eviction in Level 3), the OS file cache is irrelevant.
* **restart**: the write mode with `keep=1` and `halt=1` (the directory is kept; the JVM
  ends with `Runtime.halt` after `sync`, no `close`), then a *fresh JVM* on that directory:
  startup time and what it reran (bounded-startup recovery), the first `firstgets` reads
  with a cold node cache, the same reads again, a mixed phase (one writer, `mixreaders`
  readers; a reader checks that the version it reads lies between the versions committed
  before and started after the read), and a check of every key. The OS file cache is *warm*
  unless `OSCACHE=cold` and `purge` succeeded; the state is in every result.

The clock is simulated (`CoreTestClock`), as in `LoadTest` and `ReclaimCost`: a transaction is
`tstep` time units after the one before and the retention is `R = K * n / tsize` transactions,
so the schedule of reclaim (when iterations start, when cuts are decided) does not depend on
the speed of the machine. What is measured is wall-clock time. Wall-clock retention is the
job of the soak (task 2).

## The workload as a function of its parameters

All parameters are `-Dperf.NAME=VALUE`; defaults are in `Perf.java`; the effective values are
in every result (`workload`) and hashed (`workloadId`, with `TRACE_VERSION`). Two sessions
with different ids for a scenario are not compared. To regenerate the data set and trace of
a result, run the same command (`command` in `session.json`, the properties in the suite file).

* Key `k` of `n` is the 4-byte big-endian integer; the `nlong` keys after them are
  `"/perf/long/" + 9 digits + "/"` and filler up to `longlen` bytes (so a long key is spread
  over `longlen/7` segments). Key order is index order; internal keys (`/#i/`) sort between
  the two groups, and the scans stay inside one group.
* The value of key `k` at version `v` is `valsize` bytes: `k` (4 bytes), `v` (4 bytes), then
  `(byte)(k + v + i)` at position `i`. A read checks size, `k`, `v` and the last byte (the full
  value in the end check).
* Load: `Random(seed)` shuffles `0..N-1` (Fisher-Yates from the end); batches of `batch`.
  Updates: `Random(seed + 7)` for the warm-up, `Random(seed*31 + 1000 + t)` for committing
  thread `t`; `uniform`: any key; `hot`: 90% of the picks on the first 1% of the keys;
  `cold`: all picks on the first 10%. `tsize` puts per transaction, no key twice in one.
  With `T` threads, thread `t` picks only keys `k` with `k % T == t`.
* `tstep = max(1 ms, ceil(1 s / (K n / tsize)))`, `R = tstep * K n / tsize`; for infinite
  retention the same `tstep` with `K = 1`.

## What is measured

Names in `metrics` of `MODE.result.json` (microseconds for `_us`):

* Throughput and latency: `commits_per_s`, `puts_per_s`, `user_mb_per_s`; histograms
  `commit.append.*`, `commit.durable.*`, `delay.*`, `get_*.get.*`, `scan_*.*`, `first_gets.*`,
  `second_gets.*`, `mix.*`, each with `count, mean, p50, p95, p99, p999, max`. The histogram
  has a bounded size (buckets 0.8% wide, upper edge reported, exact count, mean and maximum);
  nothing is accumulated per operation. `*.ops_per_s` is the mean of the untimed windows
  (with `_min`, `_max`, `window_cv`).
* Efficiency: `bytes_appended_per_put`, `bytes_appended_per_user_byte`, `we` (user bytes per
  stream byte), `se`, `se_min`, `se_offered`, `kept_mb_*` (finite retention), and the
  attribution `rec.user_*`, `rec.step_*`, `rec.table_*`, `rec.other_*` per put from
  `Reclaim.Stats` (counters describe the record that writes a node, not who made it dirty).
  `reclaim.iterations_done`, `reclaim.steps`, `reclaim.cuts_logical`, `reclaim.cuts_physical`
  (a move of the `FileStream` first position, polled every 20 ms: a deletion of files).
* Storage and memory, sampled once per second: `storage.files_max`, `storage.disk_mb_max`,
  `disk_over_kept_*`, `heap.used_mb_max`, `heap.after_gc_mb_max` (the pools' usage after their
  last collection; for G1 the old generation updates only after old collections),
  `rss_mb_max`, `dirty_nodes_max`; the series are in `MODE.raw.json`.
* GC from the log, over the measured window: `gclog.pause.*` (count, total, max, p99),
  `gclog.safepoint.*`, `gclog.full_gcs`, `gclog.heap_after_gc_max_mb`; the five longest
  pauses and, for the five slowest commits, the pauses and safepoints that overlapped
  them (`gcLog`, `slowestCommits` in the result). `gc.mxbean.*` is the same from the
  platform beans.
* Restart: `startup.sec`, `startup.transactions_rerun`, `startup.read_from_mb`,
  `startup.section_mb`, `startup.first_available_lookup_age_s`; `first_get_us` and the mean
  per decade of reads (`first_gets.blockN`); `first_over_second_mean`.

The timing of an operation is two `System.nanoTime()` calls around the call; building
the transaction and generating values are outside it. Value checking is in the loops
of the bulk gets (a few array reads), and the same in every build.

## Comparing

`compare` takes a reference and one or two candidate sessions (a tracked reference in
`java/bench/reference/` works as well). For each scenario it first checks that the
**workload id, mode, JVM version, vendor, flags, collector, heap, CPU count, memory, OS
build, file system, OS file cache state and the harness source hash** are equal, and
otherwise prints `INCOMPATIBLE` and the reasons, with no percentages (exit code 3). Then,
for each primary metric, medians over runs with CV and sample counts:

* Thresholds are per class (`warm_read_throughput`, `throughput`, `latency_p50`,
  `latency_p99`, `latency_p999`, `size`, `startup`, `gc`) in `java/bench/thresholds.json`.
  Until that file exists and is frozen, only the provisional target of the plan raises
  alerts: warm gets (`get_latest`, `get_historical`, `get_longkey`) worse than the reference
  by more than 5%.
* An **alert** needs a median worse than the threshold *and* every candidate run on the bad
  side of the reference median, with at least 3 runs on both sides; fewer runs say "no
  conclusion", a worse median that is not consistent says "noise?". An alert prints both
  medians, the CVs and the run counts. It is *unconfirmed*: the plan requires a matched
  rerun. With two candidate sessions, `compare` says `CONFIRMED` only for alerts in both.
* Maxima (`latency_max`, `gclog.*.max_ms`) never alert; a maximum much larger than the
  reference's is marked `EXPLAIN`, and `summary` lists the slowest commits with the GC
  pauses that overlapped them.
* `calibrate SESSION SESSION...` (sessions of the *same* build, for example from
  `ab level3-ref level3-ref`) proposes class thresholds from the deviation between the
  sessions' medians and the run-to-run CV (2 x the 90th percentile of the first, or 3 x the
  median of the second, rounded up to 0.5%; the warm-read class never below 5%), and warns
  if the repeatability is worse than the 5% target. `OUT=java/bench/thresholds.json` writes
  the proposal with `frozen: false`; freezing is an edit (or `--freeze`) in a commit before
  Level 4 work.

Exit codes: 0 nothing to report, 1 alerts, 3 incompatible, 4 a failed or missing run.
A failed run (wrong value, exception) stops `performance.sh` at once.

## The sequence for the reference

1. Task 1 is done: the power-loss repairs are in the source and the Level 1 to 3 gates pass.
2. `java/stress/performance.sh smoke` passes.
3. `java/stress/performance.sh build level3-ref` (and keep the directory: it is the preserved reference build).
4. A quiet machine (no other jobs, charger, no other benchmark): `BUILD=level3-ref performance.sh reference ref1`.
5. `performance.sh ab level3-ref level3-ref` for the matched rerun (two sessions of the same build),
   then `calibrate` on the two sessions, review `java/bench/thresholds.json`, freeze it.
6. `performance.sh promote SESSION level3-ref-v1`, write `docs/level3-performance.md` from
   `summary.md`, name the reference in step 0 of [level4-plan.md](level4-plan.md), and commit.
7. In Level 4, `performance.sh ab level3-ref current` alternates the reference build and the
   candidate; changes both need go into a common baseline first.

## Limitations (stated, not measured)

* One machine class per reference; the machine facts (`session.json`) must match. Spotlight,
  Time Machine and other system activity are not controlled; `quiet_check` looks at CPU only.
* The OS file cache is warm in the default configuration; reads that go to the device are
  measured only with `OSCACHE=cold`, which needs `sudo purge`. A fresh JVM alone is not cold.
* Simulated time drives reclaim; wall-clock behaviour over hours is the soak's job.
* Durable commits are dominated by the configured buffering (100 ms) and by whatever the
  storage path does to make bytes durable; their numbers depend on the task-1 repairs and
  are not evidence of device-level durability.
* `System.nanoTime()` on the Apple M1 ticks at 24 MHz: latencies are multiples of 41.7 ns. The
  throughput of the bulk windows does not depend on it; the per-get percentiles do (0.4 us
  steps in the sub-microsecond range).
* The sampled RSS, dirty-set size and storage numbers are once-per-second samples; physical
  cuts are polled every 20 ms. G1 `heap.after_gc_mb_max` from the beans underestimates; the
  GC log value is better.
* The harness changes allocation and timing slightly (value generation, two clock reads per
  timed operation, a transaction listener); the same in every build, so it cancels in a
  comparison and does not in an absolute number.
* Assertions are off. The Level 1 to 3 gates are correctness gates and run with them on.
* Eviction does not exist yet; data larger than the cache is a separate Level 4 requirement.
