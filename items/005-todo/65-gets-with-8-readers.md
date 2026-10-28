005-65. Investigate: gets of 27 and 36 ms with 8 readers at 665 MB under ZGC
==============================================================================

Status: open. Kind: investigate. Created 2026-10-28.

Registered at Frans's decision on item 009's target 2 (2026-10-28,
decision 2 of 006-09, section 8): "Register the 8-thread case as a new 005
entry: ScaleBench C from the OS cache, 665 MB, ZGC, 8 threads, longest
gets 27 and 36 ms (bf19075: 2.1 ms), 22 and 26 waits of a reader's load
for the eviction thread over 10 ms. Hypothesis to test, not a finding:
[...]". Item 009 is closed with target 2 met in P4's soak and the pause
probe, not yet with 8 threads at 665 MB under ZGC: this entry.


The issue
---------

006-09's quiet block ran 009-03's ScaleBench block from the OS's cache
(regime C; 10M key24 keys, the default startup distance of 10 MB, 665 MB
budget, 2,660 MB heap) on F53, HEAD `4f7cd60` against `bf19075` (005-50,
the commit before 005-46), two rounds in turns (005-46,
`night/scalebench-c.sh`; the numbers below from its `out/summary.txt` and
`out/scalebench-c/f53-c-10m-b665-zgc-*.txt`). Under ZGC:

| | `bf19075`, rounds 1 and 2 | `4f7cd60`, rounds 1 and 2 |
|---|---|---|
| 8 threads: gets a second | 395,448 and 400,486 | 727,507 and 710,841 |
| 8 threads: the longest get | 2.8 and 1.4 ms (mean 2.1) | 27.4 and 36.5 ms |
| 8 threads: a reader's load waiting for the eviction thread over 10 ms | 0 and 0 | 26 and 22 |
| 4 threads: gets a second | 590,743 and 603,118 | 711,200 and 686,657 |
| 4 threads: the longest get | 1.1 and 0.4 ms | 6.0 and 4.1 ms |
| the longest eviction batch of the run (bound: 2 ms by the clock) | 2 and 2 ms | 17 and 11 ms |
| 4 sampled readers blocked on a file's monitor | 3.7 and 3.5 percent | none |

Under G1 the longest gets are G1's pauses, for both jars. At 665 MB under
G1 neither jar has a wait over 10 ms; at 133 MB under G1 `4f7cd60` has a
few (1 and 3 with 4 and 8 threads in round 1, 1 with 8 in round 2),
`bf19075` none. The collector's pauses under ZGC were far below a
millisecond. ScaleBench's get phases write nothing, so no
commit, force or cut is under a get.

A load waits for the eviction thread in `Eviction.afterLoad` (009-02,
step 3d): when the resident bytes are over the trigger by more than the
band between the high and low marks, it wakes the eviction thread and
parks in steps of 50 microseconds until a batch has ended, at most
`LOAD_WAIT_NANOS`, 2 ms. A wait of over 10 ms is therefore more than the
code's bound: the reader parked for longer than it asked, or did not run
when its park ended. The batches overran their 2 ms the same way: a batch
ends after `BATCH_NANOS` by the clock, so 11 and 17 ms mean that the
eviction thread did not run for most of the batch.

The step ran `NOT QUIET`: the conductor started it after 30 minutes
without a quiet machine (the 1-minute load 2.76 at its start), and
another session's work may have taken cores.

These are within 009's runs the only gets above about 20 ms that are
neither the collector's nor s1's disk (009-03, section 0). s1's get of
2,760 ms with one reader (009-03, section 9) is not part of this entry:
Frans accepted it as not BergDB's (one reader, no writer, no collection or
safepoint, the run's memory cgroup at its limit with the kernel reclaiming
about 56 times a second).


The hypothesis (to test, not a finding)
---------------------------------------

F53 is an Apple M1 Pro with 8 performance cores and 2 efficiency cores
(`sysctl hw.perflevel0.physicalcpu`: 8; the JVM sees 10 CPUs). Since
005-46 (`eaec93e`) the readers no longer block on a file's monitor
(`bf19075`: 3 to 13 percent of the samples in last night's runs), so 8
readers keep all 8 performance cores busy, and the eviction thread, ZGC's
concurrent threads and a reader whose park has ended wait for a core.
Then the eviction thread falls behind: its batches stretch (11 and 17 ms)
and the loads that wait for it wait longer than their 2 ms. With 4
readers there are cores to spare. Also, the step ran not quiet.

It would be **refuted** if, in a quiet block:

* `bf19075` also has waits over 10 ms or gets over 20 ms with 8 threads;
* the waits come at 4 threads, or at 6 threads with the process well
  below 8 cores of CPU;
* or the eviction thread gets as much CPU with 8 threads as with 4 while
  the batches still stretch (then something holds it other than the
  cores, such as a lock).

It is **supported** if `eaec93e` and `4f7cd60` have the long gets and
waits with 8 threads only, the process then uses about 8 cores or more,
and the eviction batches' time by the clock is well above the eviction
thread's CPU time (descheduled within its batches) with 8 threads, not
with 4. If only `4f7cd60` has them, one of the commits after 005-46 is the
cause: 005-55 (`cec0032`), 005-57 (`07b6375`) or 005-51 (`c2aab10`, the
eviction thread's waits without a timeout).


The test
--------

ScaleBench C as last night, 665 MB, ZGC, at 4, 6 and 8 threads, on
`bf19075`, `eaec93e` (005-46 alone) and `4f7cd60` (006-09's HEAD) in
turns, two rounds, with 8 sampled readers, in a quiet block on F53. A
patch to ScaleBench, `ScaleBench-065.diff` on top of 009-03's port, adds
to each threads phase the CPU time of the thread `bergdb-evictor`, of the
readers and of the rest of the process (the collector's threads, the
compiler), read with `ThreadMXBean` and the process's CPU time (no
safepoint), and the phase's longest after-load wait.

The step: [65-gets-with-8-readers/night/](65-gets-with-8-readers/night/).

* `prep.sh` makes, before the block, a clone of each of the three
  commits, built, the patched ScaleBench compiled against each jar, and
  004-02's `pidio`, in `/Users/f/fl/bench/006-09/d2-009-builds/` (made
  2026-10-28, 09:23 to 09:27; jars `af8a63b6` for `bf19075`, `5267f684`
  for `eaec93e`, `e62f8257` for `4f7cd60`, by the first 8 bytes of their
  SHA-256).
* `threads.sh` (`# minutes: 30`, about 17): the 10M load with
  `4f7cd60`'s jar, then two rounds of each build (ABC CBA), each run the
  phases warm and threads (4, 6 and 8, 30 s each) and 20 s of 8 sampled
  readers. `sum.py` writes `out/summary.txt`: a row for each run and
  thread count (gets a second, p99.9 and max, the waits over 10 ms and the
  longest, the batches and their time by the clock, the CPU of the
  readers, of the rest and of the eviction thread, in cores), each
  build's means, the longest gets per run, the sampled readers' states.
  It uses only the prebuilt jars and classes; it exits 0 only if every
  run ended with `SCALEBENCH OK` and the summary has all of their thread
  phases with the eviction thread's CPU.
* Smoke test, 2026-10-28, 09:28 (`SMOKE=1`: 20,000 keys, a startup
  distance of 100 KB and a 0.5 MB budget so that the eviction thread
  runs, phases of a second): exit 0 in about a minute, 18 of 18 rows
  parsed. A first smoke test with the night's budget evicted nothing, and
  the check of the parsed summary failed it, as it should.
* ScaleBench is in the package `bergdb.core` and names `SyncLevel`
  without an import. The three builds have `bergdb.core.SyncLevel`; since
  005-56 (`04f1546`) `main` has it in `bergdb.pub.util`, so compiling
  ScaleBench against a jar of `main` needs that import added.
* `ScaleBench-065.diff` and `sum.py`, second version (2026-10-28, for the
  section Reading): for each after-load call, the resident bytes and the
  trigger read just before it, so that the calls over the trigger (they
  enter `evictorLock`), those under pressure (only they may park) and the
  calls over 10 ms under pressure are counted; the gets over 10 ms of each
  threads phase; with thread contention monitoring on, the blocked and
  waited counts and times of the readers and of the eviction thread; and
  the machine's busy cores in each phase (`getCpuLoad`), so the other
  processes' too. `sum.py` prints them in two more tables and each build's
  sums or means; its first table, which `threads.sh` checks, is unchanged.
  Smoke test 2026-10-28, 10:06 (`SMOKE=1` with
  `B=/Users/f/fl/bench/006-10/w2-builds`: links to the three clones in
  `d2-009-builds`, and ScaleBench patched with this version and compiled
  against each jar): exit 0 in about a minute, 18 of 18 rows, every new
  cell filled. `d2-009-builds/sb` still has the classes of the first
  version, so `prep.sh` must run again before the block for the night to
  measure these.

The ScaleBench outputs and GC logs stay out of the repository (013-01,
section 4): `out/` beside the step, the GC logs in the builds directory.


Done when
---------

The runs of the test in a quiet block, the explanation written here (the
hypothesis confirmed or refuted, and by what), and a recommendation for
Frans: nothing (a machine with as many readers as cores is outside the
target), a change (for example, a reader that runs a batch itself instead
of waiting for the eviction thread; or the eviction thread at a higher
priority), or more measurements. A change to `java/` is a decision for
Frans after the explanation.


First step
----------

`threads.sh` in the next quiet block on F53 (006-10, W2), after its
`.READY` marker.


Size and order
--------------

S, measurements only, unless a change follows. Needs a quiet F53. Comes
from item 009 (target 2) and 005-46, which made the readers faster;
touches 005-51 (the eviction thread's waits).
