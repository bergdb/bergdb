005-65. Investigate: gets of 27 and 36 ms with 8 readers at 665 MB under ZGC
==============================================================================

Status: open, measured (Results, 2026-10-28 night); a fix is Frans's
decision (Recommendation). Kind: investigate. Created 2026-10-28.

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


Reading
-------

By Claude (Opus 5.5, Claude Code), 2026-10-28, for 006-10's W2.1: the
code on the path at `4f7cd60` (the same at `bf19075` and `eaec93e` but
for 005-51's wait, see the commits below) and last night's outputs
(005-46's `night/out/scalebench-c/`, the GC logs in
`/Users/f/fl/bench/006-09/w1/raw/scalebench-c/`). No timed runs. The
explanation only: a fix is Frans's choice after the runs (2026-10-28).

**The path.**

* A get that misses the cache follows a pointer on the slow path
  (`NodeCollection.followStreamPointer`). On the way a load enters the
  predecessor's monitor, the map's monitor (`Cache3.liveOrNewHandle`), the
  handle's monitor for the read (009-02, T7a), and for each stream read
  `BufferedStream`'s monitor (`BufferedStream.read`) and the JDK channel's
  `sun.nio.ch.NativeThreadSet` (the positional read's `add` and `remove`).
  Then, with no lock held, `NodeCollection.followPointer` calls the load
  listener, `Eviction.afterLoad` (set in `Db`'s constructor). ScaleBench
  wraps that call and times it: the column "waits > 10 ms" counts the
  calls over 10 ms.
* `Eviction.afterLoad` reads the resident bytes. At or below the trigger
  it returns. Above it, it calls `Eviction.wake`, which enters the monitor
  `evictorLock`, sets `wanted`, starts the thread if there is none, and
  calls `notifyAll`. Only when the resident bytes are over the trigger by
  more than the gap between the watermarks (`high - low`, 166 MB at a
  665 MB budget: pressure) does the reader then park, in steps of 50
  microseconds (`LockSupport.parkNanos`), until the thread's count
  `batches` changes or `LOAD_WAIT_NANOS`, 2 ms by the clock, has passed.
* So `LOAD_WAIT_NANOS` bounds the park loop only. Nothing bounds the
  entry into `evictorLock`: a reader waits there while another thread
  holds the monitor, and, once it is free, until the reader runs again.
* The eviction thread (`Eviction.EvictorRun`) enters `evictorLock` too: to
  read `wanted` and wait (`evictorLock.wait()`, with no timeout since
  005-51), again on each `notifyAll` that wakes it, and after each series
  of batches (its `finally`). In between it runs batches, each under the
  write lock (`sweep(db, true)`), and counts them in `batches`, a volatile
  field that parked readers read without the lock.
* A batch (`Eviction.sweep`) takes CLOCK steps over the node table, one of
  its 4,096 maps at a time (`Cache3.clockStep`), from where the last batch
  stopped. It ends at the first of: the resident bytes down to the low
  watermark; 4,096 handles examined (65,536 under pressure); two rounds of
  the hand; `BATCH_NANOS`, 2 ms, by the clock; a writer waiting. So it is
  bounded by time and by work, and the clock is read between maps, not
  within one.
* In a map, `clockStep` holds the map's monitor (the `HashMap`) for the
  whole map. For each handle: a volatile read of its object;
  `Eviction.detachable` (in TransNodes, `Residents.isPinned`, a stream
  position); the CLOCK bit cleared or tested; a compareAndSet to DEAD; and
  `Cache3.kill`, whose `Residents.released` enters the object's monitor and
  adds to two `AtomicLong`s. For each pinned key node of the map,
  `unswizzleValues` enters its monitor for each value pointer. A batch
  allocates an `ArrayList` and a `Detachable`, and a `long[4]` for each
  map; under ZGC each load and store of a reference has its barrier.
* A map holds 1/4,096 of the live handles, so a step takes microseconds
  to tens of microseconds, and the work alone overruns the 2 ms by that
  much. A batch of 17 ms had about 15 ms in which the thread did not run:
  off its core (holding the write lock and, within a step, a map's
  monitor), or parked on a monitor held by a reader that was itself off
  its core (a map's: readers enter it in `Cache3.liveOrNewHandle`,
  `liveHandle`, `getNode` and `dropIfEmpty`; an object's: `Node.swizzle`,
  `KeyNode.setPointee`, `Residents.added`, `followValuePointer`). Not page
  faults: a batch reads no file, and the heap is pre-touched
  (`-XX:+AlwaysPreTouch`, `-Xms` equal to `-Xmx`). An efficiency core makes
  a batch do less in its 2 ms, not last longer.
* A long batch makes no load wait unless the resident bytes are under
  pressure. A writer would wait for it (the write lock); ScaleBench's get
  phases have none.

**What last night's outputs already show.**

* **No load waited for a batch.** The park loop needs the resident bytes
  over 831 MB (665 + 166). ScaleBench samples them every second: the most
  in each of the four ZGC runs was 665.0 to 665.5 MB (the JSON's
  `maxima`). A batch freed about 0.6 MB (the last batch of each run), and
  with 8 threads `4f7cd60` ran 5,001 and 4,964 batches in 30 s, about
  100 MB a second; to fall 166 MB behind, the thread would have had to
  stop for over a second and a half. Its longest batch was 17 ms. So the
  after-load calls over 10 ms were spent in `Eviction.wake`, at the entry
  into `evictorLock`, or a reader lost its core within the call.
* **Running readers rarely lost their cores for long.** A thread that runs
  Java or VM code reaches a safepoint well within a millisecond unless it
  is off its core; a thread parked on a monitor, or in the kernel's read,
  does not hold one up. In `4f7cd60`'s 8-thread phases the GC logs have
  182 and 181 safepoints, a median time to reach of 0.07 ms, and one over
  2 ms: 7.0 ms (ZRelocateStartYoung in round 1, 8 threads running). Had
  readers lost their cores for 10 ms or more often enough to put 26 and 22
  such pauses into their after-load calls (3.7 and 3.1 percent of their
  time), about 30 times as many would have fallen elsewhere in their gets,
  and a tenth or more of the safepoints would have waited over 2 ms
  (allowing for about half of a reader's time in the kernel's read); 1 of
  363 did. So the long calls were most likely readers queued on
  `evictorLock` whose turn came late: a holder off its core (rare, as the
  one 7 ms reach shows), or a reader woken from the monitor's queue that
  waited for a core or lost the monitor again to readers that came first
  (a Java monitor is not fair).
* **The call's cost grows with the readers, most with 8 under ZGC on
  `4f7cd60`.** The mean after-load call (the JSON's `afterLoadMs` over
  `afterLoadCalls`) on `4f7cd60` under ZGC: 17, 41 to 43, 105 to 112 and
  426 to 493 ns with 1, 2, 4 and 8 threads. With 8 threads: `bf19075` under
  ZGC 138 to 147 ns; `4f7cd60` under G1 154 to 161 ns, with about as many
  calls a second (579,000 to 595,000, against 589,000 to 602,000) and no
  call over 10 ms. The resident bytes stay at the budget (a batch frees its
  0.6 MB, and the loads fill it again within milliseconds), so a large
  share of the calls must enter `evictorLock` (tonight's runs count them).
  Under ZGC the same number of calls cost about three times as much as
  under G1. G1's batches are shorter (below), so fewer of its calls may
  find the bytes over the trigger; but the larger difference is most
  likely what the machine has to spare.
* **ZGC's workers took cores.** ZGC ran up to 3 concurrent workers ("GC
  Workers Max: 3 (dynamic)"), about 2 a cycle. With `4f7cd60` and 8 threads
  its cycles ran back to back (236 and 234 cycles, 35.0 and 34.9 s of
  cycle time in the 30 s phase); with `bf19075` 83 and 81 cycles, 16.4 and
  14.9 s. So with `4f7cd60` and 8 threads: 8 readers that do not block,
  the eviction thread, about 2 workers (up to 3), the compiler and
  ScaleBench's sampler, on 10 cores (8 performance, 2 efficiency); and
  more from other processes (the 1-minute load average was 2.76 at the
  step's start, with no JVM, gate, Lean build or `night.sh` running). With
  4 threads, about 7 to 8.
* **The batches stretched with 8 readers on `4f7cd60` only.** The mean
  batch under ZGC: 1.24 to 1.28 ms with 4 threads, 1.81 to 1.88 ms with 8
  (under G1 0.54 to 0.63 and 1.04 to 1.14 ms); `bf19075` 1.20 and 1.26 to
  1.29 ms. The longest batch so far was 2 ms through the 4-thread phase and
  became 17 and 11 ms in the 8-thread phase; with `bf19075` 2 ms
  throughout. That is the eviction thread off its core in a batch, as the
  entry's hypothesis says.
* **Not the collector, not allocation.** No allocation stall in the four
  ZGC GC logs (every `Allocation Stalls` line 0); pauses of at most
  0.025 ms; in the threads phases no safepoint over 7.1 ms, its reach
  included (the longer ones, up to 13 ms, are the sampled phase's thread
  dumps).

**The commits from `bf19075` to `4f7cd60`.** Seven commits; four change
`java/src` (`git log bf19075..4f7cd60 -- java/src`). `Eviction`'s load path
and batch (`afterLoad`, `wake`, `EvictorRun`'s loop, `sweep`), `Cache3`,
`Residents` and `bergdb.dag` are the same in all three builds, but for
005-51's wait.

* `eaec93e`, 005-46: a read takes no lock on its file (`FileStream`'s
  `DbFile.read`: positional reads on a `FileChannel` of each file's own;
  the list of files a volatile array). It is the only one that changes
  what readers do in this benchmark, and the most likely to matter, by
  what it lets them do. With 8 threads `4f7cd60` made 1.8 times the gets
  and the after-load calls of `bf19075` (727,507 against 395,448 gets a
  second; 602,000 against 328,000 calls), so the eviction thread ran 2.3
  times the batches (5,001 against 2,160), the readers entered
  `evictorLock` about twice as often, and ZGC collected without a break.
  And all 8 readers stayed runnable, where `bf19075`'s queued on the
  file's monitor (BLOCKED in 3.5 and 3.7 percent of the samples with 4
  threads; with 8 its gets a second fell below its own with 4). Readers
  still meet on short monitors (the path above); the smoke tests' samples,
  at a 0.5 MB budget and not the night's regime, show readers BLOCKED in
  `Eviction.wake`, on `BufferedStream` and on `NativeThreadSet`.
* `cec0032`, 005-55: `Db.finalize()` removed; tests close their databases.
  Nothing on the get path or in eviction at runtime: it cannot explain the
  waits.
* `07b6375`, 005-57: rule 4 at the start by position, without header reads
  (`DbStarter.linkD`, `NodeCollection.linkToCanonical`). It runs before the
  phases, and the readers' path after the start is unchanged. Both jars
  counted the same pinned bytes, 44,704,880 (`Eviction.stats`; the get
  phases write nothing, so that is D as the start left it), so eviction
  worked on the same state. It cannot explain the waits.
* `c2aab10`, 005-51: the idle eviction thread waits with no timeout
  (`evictorLock.wait()` for `wait(1000)`), and the close ends it
  (`Eviction.endThread`, from `Db.closeStorage`). Under load `notifyAll`
  wakes it either way; no request is lost (`wanted` is set and read under
  the monitor); and loads call `wake` every few microseconds, so the old
  timeout never ran out. It cannot explain the waits.

So `eaec93e` alone should show the case: tonight `eaec93e` like `4f7cd60`,
within the noise.

**The hypotheses, and what tonight's runs would show.** The columns named
are `sum.py`'s; those marked (+) come from the second version of
`ScaleBench-065.diff` and `sum.py` (The test).

* **H1, the entry's: the eviction thread falls behind for want of cores,
  its batches stretch, and the loads that wait for it wait longer than
  2 ms.** Its first half fits last night (batches of 17 and 11 ms with 8
  threads on `4f7cd60` only); its second half does not, as no load waited
  for a batch (above).
  * Holds as stated if, with 8 threads on `eaec93e` and `4f7cd60` only,
    the after-load calls over 10 ms began under pressure ("of them under
    pressure" (+) close to "after-load > 10 ms"), the readers parked
    ("readers parked ms" (+) well above 0; samples TIMED_WAITING in
    `Eviction.afterLoad`), and the batches' time by the clock was well
    above the eviction thread's CPU ("batch wall over eviction CPU" well
    above 1).
  * Refuted as the cause of the waits if the long calls began without
    pressure, as last night's resident bytes say they did. Its first half
    may still hold, as a finding about batches, which a writer waits for.
* **H2: the monitor in `Eviction.wake`.** Every load over the trigger
  enters `evictorLock`; with 8 readers it is a hot monitor, and a reader
  that queues for it waits until the holder lets go and until it runs
  again.
  * Holds if the long calls began without pressure ("of them under
    pressure" (+) 0), the readers did not park ("readers parked ms" (+)
    near 0), the mean call ("after-load ns a call" (+)) with 8 threads is
    several times that with 4 on `eaec93e` and `4f7cd60` and less so on
    `bf19075`, "readers blocked %" (+) rises with the threads, the sampled
    readers show BLOCKED in `Eviction.wake` on `java.lang.Object`, and the
    gets over 10 ms (+) are not many more than the calls over 10 ms (the
    long gets are these calls).
  * Refuted if the long calls began under pressure; or if the gets over
    10 ms far outnumber the calls over 10 ms (ten times or more): then the
    long gets come from something that every part of a get meets (H3 on
    its own), and the calls are only a sample of it.
* **H3: not enough cores.** With 8 readers on `eaec93e` and `4f7cd60` more
  threads are runnable than there are cores (8 readers, the eviction
  thread, up to 3 of ZGC's workers, the rest), and a thread that loses its
  core, or is woken, waits for a time slice (on macOS about 10 ms for an
  ordinary thread) or more. H1 and H2 need it for anything to last 10 ms.
  * Holds if, with 8 threads on `eaec93e` and `4f7cd60`, the machine is at
    about 9.5 to 10 of its 10 cores ("machine cores" (+)), the rest of the
    process (ZGC) at 1.5 to 3 cores ("rest"), and the eviction thread's
    share neither running nor waiting ("the rest %" (+)) and "batch wall
    over eviction CPU" are above their values with 4 threads; and if there
    are idle cores with 4 threads, and with `bf19075` at 8.
  * Refuted if the long waits come while the machine has idle cores
    ("machine cores" clearly below 10, such as 9 or less): then the monitor
    alone makes them, a queued reader losing `evictorLock` again and again
    to readers that come first.
* **H4: the other processes** (the step ran not quiet).
  * Holds if the waits are gone tonight, with "other processes' cores" (+)
    near 0.
  * Refuted if the waits stay with 8 threads while the other processes use
    next to nothing.
* **H5: a commit after 005-46** (005-55, 005-57, 005-51).
  * Holds if only `4f7cd60` has the waits.
  * Refuted if `eaec93e` has them about as often, as this reading expects.

Which change, if any, follows from the runs: the examples under Done when
answer H1 (a thread behind for want of cores); H2 points at the entry into
`evictorLock` on every load over the trigger.

**What threads.sh measures.** As committed in `fab16db`, it cannot tell
H1 from H2 (whether a long call could park), H3 from the monitor alone (it
does not see the machine's cores, and of the eviction thread only its
CPU), or H4, and it does not count long gets. The second version adds
them (The test). Its cost: two volatile reads and at most two counter
increments a load, and the timing of contended monitor entries; the same
for the three builds. For the eviction thread, a wait's re-entry into
`evictorLock` counts as waited and as blocked both, so `sum.py` splits its
time into running, waiting (the re-entry included) and the rest. To use it
tonight, its commit goes into `main` and `prep.sh` runs again before the
block (about 3 minutes; it makes the clones and ScaleBench's classes
again), then `SMOKE=1`.


Results, 2026-10-28 night
-------------------------

By Claude (Opus 5.5, Claude Code), 2026-10-29, from `threads.sh`'s run in
006-10's W2: 2026-10-28, 19:34 to 19:50, quiet (load 1.55 at the start,
AC power, two idle sessions), `threads: OK, 0 problems`. The 10M load with
`4f7cd60`'s jar, then the builds in turns, ABC CBA. `sum.py`'s summary is
kept as
[night/results-2026-10-28.txt](65-gets-with-8-readers/night/results-2026-10-28.txt);
the raw outputs stay out of the repository. Each row below is a build's
two rounds: counts summed, the longest the most of the two, the rest
means.

**Gets and after-load calls.** "Over the trigger": the calls that enter
`evictorLock` in `Eviction.wake`. "Under pressure": the calls that may
park for a batch. The readers parked 0 ms in every phase.

| build | threads | gets a second | longest get ms | gets > 10 ms | after-load > 10 ms | of them under pressure | after-load ns a call | over the trigger, k a second | readers blocked % |
|---|---|---|---|---|---|---|---|---|---|
| `bf19075` | 4 | 595,058 | 2.2 | 0 | 0 | 0 | 78 | 2 | 0.54 |
| `bf19075` | 6 | 439,162 | 1.5 | 0 | 0 | 0 | 135 | 1 | 15.28 |
| `bf19075` | 8 | 402,044 | 0.6 | 0 | 0 | 0 | 132 | 1 | 26.55 |
| `eaec93e` | 4 | 700,173 | 5.9 | 0 | 0 | 0 | 101 | 3 | 0.01 |
| `eaec93e` | 6 | 746,007 | 10.5 | 2 | 0 | 0 | 167 | 11 | 0.14 |
| `eaec93e` | 8 | 717,384 | 26.4 | 269 | 57 | 0 | 472 | 78 | 2.34 |
| `4f7cd60` | 4 | 699,194 | 5.1 | 0 | 0 | 0 | 109 | 3 | 0.01 |
| `4f7cd60` | 6 | 743,908 | 9.7 | 0 | 0 | 0 | 157 | 8 | 0.11 |
| `4f7cd60` | 8 | 721,958 | 38.9 | 329 | 67 | 0 | 448 | 78 | 2.38 |

**CPU and cores.** In cores (CPU time over the phase's 30 s). The
eviction thread's "rest": its share neither running nor waiting for a
request (runnable without a core, or blocked). The longest batch is the
run's so far (`Eviction` keeps no maximum per phase), the most of the two
rounds.

| build | threads | readers | rest of the process | eviction thread | eviction running % | batch wall over eviction CPU | eviction thread, the rest % | longest batch ms | machine cores | other processes' cores |
|---|---|---|---|---|---|---|---|---|---|---|
| `bf19075` | 4 | 3.99 | 1.19 | 0.124 | 12.4 | 0.98 | -0.1 | 2 | 5.46 | 0.15 |
| `bf19075` | 6 | 5.28 | 0.83 | 0.100 | 10.1 | 0.99 | -0.1 | 2 | 6.47 | 0.26 |
| `bf19075` | 8 | 6.24 | 0.70 | 0.092 | 9.2 | 0.99 | -0.1 | 2 | 7.33 | 0.31 |
| `eaec93e` | 4 | 3.99 | 1.50 | 0.157 | 15.7 | 0.98 | -0.1 | 2 | 5.86 | 0.21 |
| `eaec93e` | 6 | 5.96 | 1.68 | 0.245 | 24.5 | 1.00 | 0.3 | 16 | 8.07 | 0.19 |
| `eaec93e` | 8 | 7.41 | 1.68 | 0.313 | 31.3 | 1.02 | 1.1 | 16 | 9.62 | 0.22 |
| `4f7cd60` | 4 | 3.99 | 1.50 | 0.154 | 15.4 | 0.98 | -0.1 | 4 | 5.86 | 0.20 |
| `4f7cd60` | 6 | 5.96 | 1.69 | 0.249 | 24.9 | 1.01 | 0.4 | 6 | 8.11 | 0.21 |
| `4f7cd60` | 8 | 7.39 | 1.66 | 0.316 | 31.6 | 1.02 | 1.1 | 23 | 9.55 | 0.18 |

**Further figures** (from the JSON of each run, and derived):

* With 8 threads a phase made about 590,000 after-load calls a second
  (17.6 and 17.9 million in 30 s, `eaec93e` and `4f7cd60` round 1). 13
  percent of them entered `evictorLock` (2.26 and 2.41 million), against
  0.5 percent with 4 threads and 1.5 to 1.7 percent with 6.
* With 8 threads the after-load calls took 3.4 percent of the readers'
  time (8.3 and 7.7 s of 240 reader-seconds). But the calls over 10 ms
  are a fifth of the gets over 10 ms (57 of 269, 67 of 329): six times
  their share of the time.
* A reader's mean block on a monitor (blocked percent times the readers,
  over the blocks a second) was about 120 to 140 microseconds with 8
  threads on `eaec93e` and `4f7cd60`, about 15 with 6, and about 35 on
  `bf19075` with 8 (its file's monitor, held across a read).
* The sampled readers (8, 20 s): on `eaec93e` and `4f7cd60` BLOCKED in
  `Eviction.wake` on `java.lang.Object` in 1.7, 1.3, 0.1 and 1.5 percent
  of the samples, the most frequent BLOCKED place in three of the four
  runs (in the fourth `BufferedStream.read`, 1.1 percent); also BLOCKED
  in `BufferedStream.read`, `Cache3.liveOrNewHandle` and on
  `NativeThreadSet`, each 0.1 to 1.3 percent. On `bf19075` BLOCKED on
  `FileStream$DbFile` in 18.4 and 18.5 percent.

**The hypotheses, against the predictions written before the run.**

* **The entry's hypothesis: partly supported.** The long gets come with 8
  threads only, on `eaec93e` and `4f7cd60` only, with the process at about
  9.4 cores and the machine at 9.6 of its 10. But the eviction thread did
  not fall behind. Its batches' time by the clock was 1.02 times its CPU
  time, not "well above". It got twice the CPU with 8 threads as with 4
  (0.31 against 0.16 cores). No load waited for it.
* **H1, the eviction thread behind: refuted as the cause of the waits.**
  None of the 124 after-load calls over 10 ms began under pressure. The
  readers never parked. Its first half holds only for a few batches: the
  longest grew to 11 to 23 ms with 8 threads (16 ms once with 6), while
  the mean batch stayed on its core. A writer would wait for such a batch;
  ScaleBench's get phases have none.
* **H2, the monitor in `Eviction.wake`: holds, for the long after-load
  calls.** They began without pressure and did not park. The mean call
  with 8 threads was 4.4 times that with 4 on `eaec93e` and `4f7cd60`
  (472 against 101 ns, 448 against 109), 1.7 times on `bf19075`. Readers
  blocked rose 0.01, 0.13, 2.3 percent with 4, 6, 8 threads. The samples
  show BLOCKED in `Eviction.wake` on `java.lang.Object`. Its refutation by
  count is not met: the gets over 10 ms are 4.7 and 4.9 times the calls
  over 10 ms, under ten times. But it accounts for only a fifth of the
  long gets.
* **H3, not enough cores: holds.** With 8 threads the machine was at 9.62
  and 9.55 cores, the rest of the process at 1.66 to 1.68. The eviction
  thread's rest was 1.1 percent against -0.1 with 4, and its batch ratio
  1.02 against 0.98. There were idle cores with 4 threads (5.9) and with
  `bf19075` at 8 (7.3), and no long call there. With 6 threads (8.1
  cores) the case is at its edge: no call over 10 ms, 2 gets over 10 ms
  in four phases, the longest 10.5 ms.
* **H4, the other processes: refuted.** They used 0.17 to 0.24 cores, and
  the waits stayed: 57 and 67 calls over 10 ms in two phases, against
  last night's 48.
* **H5, a commit after 005-46: refuted.** `eaec93e` had 57 calls and 269
  gets over 10 ms, `4f7cd60` 67 and 329: within the noise. 005-46 alone
  brings the case.
* **The Reading's other predictions.** As predicted: no load waited for a
  batch; `eaec93e` like `4f7cd60`; the call's cost growing with the
  readers. Not as predicted: the Reading expected the long gets to be
  mostly these calls (running readers rarely lose their cores). Four of
  five gets over 10 ms had no after-load call over 10 ms.

**The explanation, as far as the numbers carry it.**

1. Since 005-46 the readers do not queue on a file's monitor. With 8
   threads the process runs 7.4 cores of readers, 1.7 of ZGC and the
   compiler and 0.3 of eviction: about 9.4 of F53's 10 cores (8
   performance, 2 efficiency), the machine 9.6. `bf19075`'s readers spend
   27 percent of their time blocked on the file's monitor, so its process
   leaves cores free.
2. With no core free, a thread that blocks on a monitor, or is woken,
   waits for a core. The monitors' waits grow (about 120 to 140
   microseconds a block with 8 threads, 15 with 6), and some last a
   scheduler's time slice, 10 ms or more.
3. `evictorLock` concentrates them. With faster loads the resident bytes
   are over the trigger more of the time, and 13 percent of the loads
   (78,000 a second) enter `evictorLock` and call `notifyAll`, against
   0.5 percent with 4 threads, though the eviction thread is already awake
   for most of them. The after-load call is 3.4 percent of a reader's time
   but a fifth of the gets over 10 ms.
4. The other four fifths of the gets over 10 ms fall elsewhere in the get:
   at the path's other monitors (`BufferedStream`, a map's `HashMap`,
   `NativeThreadSet`) or as a reader that loses its core. These numbers
   cannot tell those apart.
5. The eviction thread is not the bottleneck. It runs 31 percent of the
   time, on its core within its batches. A few batches stretch to 11 to
   23 ms: a writer's concern, not a reader's here.


Recommendation
--------------

For Frans to decide; no change made.

* **(a) Fix the hot monitor (the explanation points here).**
  `Eviction.wake` enters `evictorLock` and calls `notifyAll` on every
  load over the trigger. A volatile flag read before the monitor (a
  request pending, or the thread awake in its batches) would let a load
  skip it; only a load that finds no request pending enters. The thread
  must re-check the resident bytes under the lock before it waits, or a
  request could be lost and, since 005-51's wait has no timeout, the
  flag would stay set while the thread sleeps. Cost: about 10 to 20 lines
  in `Eviction`, a test for the lost request (a load and the thread's
  wait racing), `before-commit.sh`, and one `threads.sh` run (17
  minutes). Expected: the entries into `evictorLock` from about 78,000 a
  second to about the batch series' rate, the after-load call near its
  4-thread cost, the after-load calls over 10 ms near 0, and the gets
  over 10 ms down by about a fifth, not to 0.
* **(b) Accept the rest as outside the target.** The other four fifths
  are a machine with as many runnable threads as cores (8 readers and
  ZGC's workers on 10 cores, 2 of them efficiency cores). BergDB's code
  can do little more there than not hold readers on monitors. With 6
  readers on F53 the longest get was 10.5 ms. The ~20 ms target is for
  BergDB's own code; this is the scheduler's.
* **Recommended:** (a), as it is cheap and removes BergDB's own share,
  then (b), stated in 009's target 2 as readers up to the cores less the
  collector's.
* **To measure first, if the explanation should be complete before a
  fix:** where the other four fifths spend their time. Two cheap
  variations of `threads.sh`, one night block: 7 threads, and 8 threads
  with `-XX:ConcGCThreads=1` (the machine below 9 cores with 8 readers).
  If the gets over 10 ms go when a core is free, saturation is the rest
  of the cause. Then, if needed, time the get's parts in ScaleBench (the
  stream read, each monitor entry on the path) and count those over
  10 ms, as for the after-load call.


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
`.READY` marker. Done 2026-10-28, 19:34 to 19:50 (Results). Next:
Frans's decision on the Recommendation.


Size and order
--------------

S, measurements only, unless a change follows. Needs a quiet F53. Comes
from item 009 (target 2) and 005-46, which made the readers faster;
touches 005-51 (the eviction thread's waits).
