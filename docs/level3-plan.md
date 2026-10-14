# BergDB Level 3: durability, soak and performance baseline

By Codex for Frans Lundberg, 2026-10-14.

Status: task 1 complete for the tested macOS/APFS and Linux VM FileStream
paths, under the assumptions in the durability report. Tasks 2 and 3 remain
planned. Complete all three before implementing Level 4.
This file replaces the completed 13 October plan. Implementation status and
review results are in [levels.md](levels.md); the eviction design is in
[level4-plan.md](level4-plan.md).

## Starting point and decisions

Level 3 passes the recorded full Level 1–3 gates, including concurrent
readers, changing retention, exact cuts, restart invariance and crashes in
the existing complete-record model. The local baseline for this work is
`2e0bfe6`. Earlier commit IDs in the recorded review are historical provenance
from before this repository. Current power-loss evidence is in
[level3-durability.md](level3-durability.md); long-running disk performance
remains to be measured.

Keep the agreed policy:

* Infinite retention remains the public API default. Finite retention
  automatically schedules reclaim; infinite retention starts no new
  reclamation iterations. Do not add a separate enable/disable setting or
  require an explicit retention choice in existing API calls.
* An admitted read may expire if a cut overtakes its actual finite snapshot.
  A successful result must still match that snapshot, and expiry must not
  poison the database. Growing retention does not restore removed history.
* Keep f = 0.25, the default startup distance of 50 MB, and the 16 KB reclaim
  scan target. Record overrides; the last KV may exceed the scan target.
* Preserve the intentional buffered/group-commit timing. Measure append
  commits and durable commits separately; do not change batching merely to
  improve a benchmark. Public value-time APIs remain removed.

Pin the exact source commit, any working-tree diff, build and configuration
for every run. Correctness repairs from task 1 must be included in tasks 2
and 3. Any later production change requires a new matched reference run.
No Level 4 implementation is part of this plan.

## 1. Close the power-loss gap

Implemented on the tested FileStream path: explicit file/name forces, a
directory force after each prefix removal, and propagation of deferred-cut
failures before durable publication. The bounded fault model includes
unordered deletion survival and cold recovery. See the
[durability report](level3-durability.md) for tests, native audits and limits.

The existing durable-cut regression checks that a cut waits for the
reported durable length. `CutStream.truncate()` refuses to lose bytes before
the stream length at the last cut. Consequently the current crash tests
cannot expose replacement bytes disappearing while old-file deletion
survives. A process kill alone does not test that failure mode.

### Failure model and recovery tests

Add a test storage implementation with separate volatile and durable bytes,
file creation, and deletion state. Appending, forcing data/metadata, advancing
the reported durable frontier, and deleting a file must be distinct events.
A simulated power loss discards unforced state and can preserve deletion.
Do not make a cut implicitly force the replacement bytes in the test model.

Exercise faults before and after each dependency of a real reclaim cut:
value rewrites, index writeout, pEnd/pSafe progress, the cut table and recovery
meta block, the force completion, durable-frontier publication, file rotation,
and deletion of each old file. Include a crash after the decision but before
the physical cut, and crashes partway through deletion of multiple files.

Recover through a fresh database and cold node graph. Check the latest
recovered state against the durable transaction oracle, all promised retained
historical states in small cases, the lookup frontier, and subsequent writes,
syncs and another restart. An append-only commit without a completed sync
may be lost; an acknowledged durable commit must survive. Surviving extra
transactions must form a valid recoverable state, not a mixture of versions.

Include a negative control: weakening the force/frontier ordering must make
the new test fail. With correct ordering, replacement bytes needed after a
persistent deletion must already be durable; if they are not, deletion must
not yet have been permitted. Inject force and deletion failures as well as
crashes, and verify that failed forcing never advances durability.

### Verify the production storage path

Trace `StorageManager.getDurableLength()`, buffered stream completion,
`FileStream`'s `RandomAccessFile` mode, file rotation and deletion. Establish
which OS operations actually complete before the durable frontier is
published. Inspect the tested JDK implementation and confirm the call order
with platform tracing or an instrumented integration test where available.

Verify the device-flush path on the tested macOS configuration, including
whether the required full-flush primitive is reached. Check the Linux path
on a Linux runner before making the same claim there. Account for the
persistence of newly created files and their directory entries before old
files can disappear. Do not infer device durability from a Java method name,
"rws", elapsed time, or a successful process-restart test alone.

Make the necessary storage/ordering repairs without changing the public
retention policy. State the OS, filesystem and device assumptions and any
platform still unverified. A simulation establishes ordering under its
model; record that separately from evidence about the real storage stack.

**Done when:** the new fault tests pass and catch the weakened implementation,
the supported flush path and deletion ordering are verified, and all full
Level 1–3 gates pass after production repairs. Record evidence and remaining
platform limitations in `levels.md`. Do not mark the power-loss gap closed
on a platform whose flush semantics remain unknown.

## 2. Run a longer file-backed soak

Use real `FileStream` storage with physical file deletion. The main run must
have at least **two measured hours**, excluding load and warm-up, at least
**ten physical reclaim cuts**, and at least **three cold database restarts**.
Extend the run if those cut/restart conditions have not been reached.
Use only disposable benchmark directories: existing harnesses empty or
remove their configured data directories.

Start with a pilot using 1 million keys and 1,000-byte values, finite retention
of five minutes, one writer, and two to four concurrent readers. Include
latest and retained historical gets, forward/backward scans, updates, deletes
and reinserts, and a hot subset alongside uniform updates. Include long keys
in the correctness trace. If that scale cannot fit the current implementation
on the test machine, record the limit and choose a documented smaller scale;
Level 3 has no eviction and cannot promise a fixed heap bound.

Use wall-clock retention for the soak. Calibrate writer rate and retention
against available memory, then freeze them for the measured run. Record
updates per key per retention window and whether the workload is paced or
runs at maximum throughput. The existing accelerated-clock tests remain
useful correctness tests but do not substitute for elapsed soak time.

Use a bounded or external reference model and bounded streaming histograms,
so the harness does not accumulate every historical result or latency sample
for hours. Verify returned values at each operation's actual snapshot. Count
admission and in-flight expiry separately; an expiry must not replace a wrong
successful answer. Check retained history and current values after each
restart, with exhaustive checks on a smaller companion case.

Record at least:

* Throughput and latency p50, p95, p99, p99.9 and maximum for append commits,
  durable commits, gets and scans; sample counts and measurement windows.
* Time of the slowest commits, reclaim steps, cut decisions and physical
  deletions, so outliers can be compared with storage activity and GC.
* GC count, total pause time, pause distribution and maximum; safepoint
  pauses, heap/RSS peaks, allocation and dirty-node peaks where measurable.
* Total appended bytes, retained logical bytes, actual files/bytes on disk,
  startup time and lookup frontier after each restart, and all failures.

Record the full JVM version, architecture, heap flags and actual collector.
Keep GC/safepoint logging consistent across comparable runs. Add a ZGC
comparison if supported and feasible, as a separate configuration; do not
silently change the collector between baseline and Level 4 runs.

Separate warm-up, steady running, restart/recovery and validation phases.
Keep validation overhead visible. Run a matched infinite-retention control
for the shorter performance trace in task 3; it need not pretend to have a
steady storage size during an indefinitely growing history.

**Done when:** the long run meets its duration/cut/restart conditions with
zero correctness or storage failures, metrics and raw logs are retained,
and a report explains the worst observed pauses and any memory growth.
Observed maxima are measurements, not latency guarantees.

## 3. Record a simple performance baseline before Level 4

The goal is a sanity check, not a regression gate: when Level 4 works, we
should see that read and write performance did not collapse compared with
Levels 2 and 3. A more complete baseline is made after Level 4 works.

Use `java/stress/performance.sh quick` (suite `performance-quick.suite`; about
15 minutes, three runs per scenario). It records:

* Warm resident gets (latest, historical, long keys) and scans in both
  directions, all resident.
* Updates with 1,000-byte values, infinite and finite retention: commits per
  second, bytes appended per user byte, write and store efficiency, latency
  percentiles and maximum, GC pauses.
* Restart after finite retention: startup time and first reads.

Run it on a quiet machine, on the source after task 1, and note the commit, JDK
and machine. Keep the summary table (`summary.md` of the session) in
`docs/level3-performance.md`, with the exact command, and the compact results
with `performance.sh promote`. After Level 4, run the same command and compare
by eye: a loss of more than about 10-20% in warm reads, or a gross stall,
needs an explanation. Results of concurrent benchmark jobs are not a baseline.

The fuller machinery (`performance.sh reference`, the grid suite, `ab`,
`compare`, `calibrate`, thresholds and alerts, see
[performance-harness.md](performance-harness.md)) exists and is tested, but is
not required now. Use it for the complete baseline after Level 4 works.

**Done when:** the quick baseline is recorded in `docs/level3-performance.md`
and named in step 0 of `level4-plan.md`. Data larger than the managed cache
remains a separate Level 4 validation requirement.

## Completion and history

Complete task 1 first, then run tasks 2 and 3 against the resulting fixed
production source. Rerun the full Level 1–3 correctness gates after any
production or harness change, record the final source identity and outcomes
in `levels.md`, and leave Level 4 unimplemented. Update this plan's status
only after its acceptance criteria are met. Do not commit on Frans's behalf.

The completed W1–W5 implementation and independent review outcomes remain in
`levels.md`. Older commit IDs describe provenance in the earlier repository;
they are not local Git commands. The imported work is local commit `2bd52c0`;
this power-loss task starts from local `2e0bfe6` and records its new source
identity in `level3-durability.md`.
