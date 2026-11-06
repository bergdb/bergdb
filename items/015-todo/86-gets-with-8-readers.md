015-86. Investigate: gets of 27 and 36 ms with 8 readers at 665 MB under ZGC
==============================================================================

Status: done (2026-11-06; see Outcome). Frans chose Option 1 of "Options
for Frans's decision, 2026-11-06": the fix stays, and the long gets with 8
readers are readers off their cores on a full machine, closed as
explained; Option 4 is to consider after release 2026.3 (017-07, section
5). Moved from 005-65 on 2026-11-05, with its contents as
they were in 005-65 (Frans's plan, approved 2026-11-05, 07:17); its
files stay in [005-todo/65-gets-with-8-readers/](../005-todo/65-gets-with-8-readers/).
Measured (Results, 2026-10-28 night); Frans decided on 2026-10-29
(Decision and fix): the fix, in `main` since 2026-10-29 (`988fe1a`),
and the rest of the long gets accepted as a full machine. Rerun with
the fix in night 1 of release 2026.2 (Results, 2026-11-04 night): the
loads' entries into `evictorLock` with 8 readers from 81,877 to 484 a
second, but the gets over 10 ms rose (298 to 492). Left: the
Recommendation's AB/BA step, about 24 minutes in a quiet block,
approved by Frans (decided 2026-11-04/05). **Run 2026-11-05, 08:11 to
08:31 (State): the rise is the fix's.** With 8 threads the fix had more
gets over 10 ms than `5a6befd` in 4 of 4 rounds, 1,009 against 513 in
sum (1.97 times), and its longest gets were longer (37 to 71 ms against
21 to 37 ms), while its readers' waits over 10 ms fell (20 against 90).
So, as Frans decided, the decision is his: left, the Recommendation's
measurements (7 threads; 8 threads with `-XX:ConcGCThreads=1`; the get's
parts timed in ScaleBench) before any change to `java/`, then his
decision. **Measured in Q-A of night 006-12, 2026-11-05, 22:50 to 23:33
(Results, Q-A of night 006-12): the long gets with 8 readers are readers
off their cores on a full machine.** With 7 readers both builds have 32
to 38 gets over 10 ms in four runs, no rise with the fix; with 8 readers
and `-XX:ConcGCThreads=1`, 22 and 85 (ZGC then stalls allocations); the
long gets' time is 99.7 percent off core, half of them within the
kernel's read. Decided by Frans on 2026-11-06, 11:09 to 11:11 (Outcome).
Kind: investigate. Created 2026-10-28 as 005-65.

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

The step: [65-gets-with-8-readers/night/](../005-todo/65-gets-with-8-readers/night/).

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
[night/results-2026-10-28.txt](../005-todo/65-gets-with-8-readers/night/results-2026-10-28.txt);
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

Decided by Frans on 2026-10-29: (a), then (b) (Decision and fix).

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


Decision and fix, 2026-10-29
----------------------------

**Frans's decision** (2026-10-29, 09:49): option A of the
Recommendation, (a) and then (b). The fix is in `main` (`988fe1a`), by
Claude (Opus 5.5, Claude Code), for 006-10. The rest of the long gets is
accepted as a full machine: with every core busy (8 readers and ZGC's
workers on F53's 10 cores), a thread that blocks on a monitor or is woken
waits for a core, and that wait comes from the operating system's
scheduling, outside BergDB's target of about 20 ms (010-P1; Frans,
2026-10-27: "The target of 20 ms is for the BergDB code."). 009's target 2
is not reworded here.

**The fix** (`Eviction.wake`, `afterLoad`, `EvictorRun`; the protocol in
wake's comment, with its interleavings). A load over the trigger enters
`evictorLock` only when no request to the eviction thread is pending: wake
reads the flag `wanted`, now volatile, first, and returns if it is set.
The flag is still written only under `evictorLock`: set by wake, with
`notifyAll`, and cleared by the thread when it takes the request, before
its batches.

* The thread reads the flag under the lock before each `wait()`, which
  lets the lock go atomically, so a request made as it is about to wait
  is either seen or wakes it: nothing is lost although the wait has no
  timeout (005-51).
* A caller that finds the flag set made its change before it read it (a
  load its bytes, `setBudget` its lower trigger), and the thread clears
  the flag after that read and then reads the bytes and the trigger for
  its batches: they see the change. So the re-check before the wait is of
  the flag, not of the resident bytes as (a) had it: that would be needed
  for a flag that meant "the thread awake in its batches", and it would
  spin after a batch that freed nothing.
* The thread ends only with no request pending: at the close (the state
  set, then `endThread`), or on an interrupt while it waits with none.
  Until now an interrupt ended it also with a request pending, which with
  the skip would have left the loads without eviction for good.
* A reader under pressure reads `batches` before wake and parks as
  before, at most `LOAD_WAIT_NANOS`, whether its request is new or was
  pending.
* No new thread, timer or setting (010-P3, P10).

Found while writing out `setBudget`'s interleaving, and fixed in the same
commit with one line: a batch that ended while `setBudget` ran could put
back the trigger of the old budget, as `Eviction.sweep` computed it
outside the monitor that `setBudget` holds; a decrease then waited until
the resident bytes passed the old budget (005-52's feature, a narrow
race). Now sweep computes the trigger in its `synchronized (this)` block.
A review by a subagent (Opus 5.5, from the code and not from this text)
found no bug in the change, the same race, and that a batch that throws
ends the thread for good, as before 005-65; wake's comment says so.

**Tests.** `Eviction.testNoLostRequest` (unit, 15 bursts, about 0.2 s;
`testNoLostRequestF`, 300 bursts, about 2 s): a database of 2,000 keys of
300 bytes, started cold with a budget of 50 kB; 8 reader threads read in
bursts of 100 random gets each, so that the eviction thread sleeps and
wakes again and again; after each burst, within 2 s, the thread must wait
with no request pending (never asleep with one), and the resident bytes
must be at most the trigger, or its last batch have freed nothing (then it
stops until the next request, by design, 005-51).
`Eviction.testInterruptWithRequestPending`: under `evictorLock` the test
makes a request without `notifyAll` and interrupts the waiting thread, as
a wake that an interrupt overtakes; the thread must take the request;
idle, an interrupt ends it, and the next loads start a new thread. 005-51's
idle test and 005-52's lowered-budget tests pass as before.

Run many times, also on deliberately broken versions of the fix
([fix/run.sh](../005-todo/65-gets-with-8-readers/fix/run.sh), with `mkvariant.py` and
`RaceLoop`; F53 busy with other sessions' work and the gates, load 8 to
20). The fix's runs: 200 unit and 40 F on the final code (15,000 bursts),
200 unit and 20 F on a first version of the tests (30 bursts a unit run;
12,000 bursts).

| version | runs | race test failed | interrupt test failed |
|---|---|---|---|
| the fix | 400 unit, 60 F | 0 | 0 |
| after its batches the thread waits without checking the flag | 40 unit | 40, each at the first burst: "request pending true, batches running false, the thread WAITING" | 40 |
| an interrupt ends the thread also with a request pending (the code before) | 40 unit | 0 | 40: "the thread null" |
| the flag cleared after the batches, not when the thread takes the request | 70 F (21,000 bursts) | 0 | 0 |

The race test catches at once the lost wake-up that the skip makes
possible: the thread asleep with a request pending, which no load would
ever end. It does not catch the last version, which loses a load only in
the few instructions between the batches' last check of the bytes and the
clear, and only if no load follows before the burst ends; the fix clears
the flag where the code always did.

**An untimed count** ([fix/run.sh](../005-todo/65-gets-with-8-readers/fix/run.sh):
`EntriesProbe` with the counters of `mkcount.py`; 1M keys of 100 bytes on
disk, from the OS's cache, a budget of 20 MB, ZGC, 8 reader threads, 10 s
after 3 s of warming; `main` before the fix (`4a69f53`) and the fix in
turns, two runs each; F53 busy, load 13 to 16, so the gets a second are
not a measurement). A second:

| | before the fix | the fix |
|---|---|---|
| loads | 568,868 and 578,966 | 582,643 and 573,324 |
| after-load calls over the trigger | 116,037 and 127,780 | 124,931 and 101,492 |
| of them entering `evictorLock` | all | 584 and 551 |
| the eviction thread's entries | 786 and 796 | 765 and 753 |
| requests taken (series of batches) | 393 and 398 | 382 and 377 |

The loads enter the monitor about 1.5 times a series of batches, the
first loads after the thread has taken a request, as (a) expected ("about
the batch series' rate"). A first count in the morning, on `633ad86`
against a first version of the fix, gave 76,800 and 189,566 entries a
second against 526 and 564. The output:
[fix/results-2026-10-29.txt](../005-todo/65-gets-with-8-readers/fix/results-2026-10-29.txt).

**Gates**, in the clone on `4a69f53` (`main` with 005-64's buffer time of
50 ms) with the fix, nice 10, F53 shared with other sessions' work
([fix/gates.txt](../005-todo/65-gets-with-8-readers/fix/gates.txt)); in `main` as
`988fe1a` on `5a6befd`, the same `java/`:

* `before-commit.sh`: "BEFORE COMMIT OK (100 s)", 1,071 unit tests and
  78 f-tests.
* `level4.sh` (full): "LEVEL 4 OK": EVICTION INVARIANCE OK in all nine
  configurations, 0 audits failed; conformance with the Lean model, 45
  traces, C-P and C-H 0 of 10,344 transactions failing.
* `level2.sh quick`: "LEVEL 2 OK".
* `core-build.sh unit f`: "CORE BUILD OK".
* StreamDigest (`all`, `main`'s class against `main`'s jar and the
  fix's): "DIGESTS IDENTICAL (36 of 36)"
  ([fix/digest-base.txt](../005-todo/65-gets-with-8-readers/fix/digest-base.txt),
  [fix/digest-fix.txt](../005-todo/65-gets-with-8-readers/fix/digest-fix.txt)). With
  `-Devictbudget=20000`, so that every database runs the capacity
  controller at a budget of 20 kB and the eviction thread and the skip
  run in the reads and restarts modes, the fix's 36 digests are those
  without eviction. `main`'s own run with that budget differed in one
  line, the physical cut of l3-node62's reads mode (`firstPos` 9,000,000
  against 8,000,000, and so `sha256all`), with `sha256` from the decided
  cut the same: the physical cut depends on timing (005-72), and in three
  more runs of l3-node62 with that budget it was at 8 or 9 MB in each
  mode, for both builds.


Results, 2026-11-04 night
-------------------------

From [night/rerun-016.sh](../005-todo/65-gets-with-8-readers/night/rerun-016.sh)
(`threads.sh` on State's four builds), the conductor's step `65-rerun` in
window 2 of night 1 of release 2026.2 (016-02, 016-05 section 6):
2026-11-04, 02:53 to 03:13, quiet by the conductor's check and by
`threads.sh`'s (1-minute load 1.54 at 02:54, six minutes after `night.sh`
ended; AC power; one idle session), exit 0, `threads: OK, 0 problems`.
The 10M load with `4f7cd60`'s jar, then the builds in turns, ABCD DCBA;
the jars of State's step 1; JDK 27 and macOS 27.0.1, as on the first
night. `sum.py`'s summary is kept as
[night/results-2026-11-04.txt](../005-todo/65-gets-with-8-readers/night/results-2026-11-04.txt).
The raw outputs stay out of the repository (013-01, section 4): the runs'
text and JSON, `runs.txt` and `summary.txt` in
`/Users/f/fl/bench/016/night1/005-65-out/`, the GC logs in
`/Users/f/fl/bench/006-10/e65-builds/raw/threads/`; the conductor's
record in `/Users/f/fl/bench/016/night1/out/65-rerun.txt` and
`results.txt`.

Each row is a build's two runs: counts summed, the longest the most of
the two, the rest means. "Into `evictorLock`": the after-load calls that
enter the monitor in `Eviction.wake`; before the fix every call over the
trigger, with it an estimate (the calls that found `wanted` clear just
before the call; State).

| Build | Threads | Gets a second | Longest get, ms | Gets > 10 ms | After-load > 10 ms | After-load, ns a call | Into `evictorLock`, a second | Readers blocked, % |
|---|---|---|---|---|---|---|---|---|
| `bf19075` | 4 | 608,542 | 19.2 |   4 |  0 |  74 |  2,295 |  0.60 |
| `bf19075` | 6 | 437,382 | 18.9 |   7 |  0 | 142 |  1,096 | 16.14 |
| `bf19075` | 8 | 402,390 | 16.5 |  18 |  1 | 141 |    915 | 27.00 |
| `5a6befd` | 4 | 689,380 | 12.5 |   4 |  0 | 103 |  3,147 |  0.01 |
| `5a6befd` | 6 | 736,479 |  9.2 |   0 |  0 | 173 |  7,072 |  0.10 |
| `5a6befd` | 8 | 713,827 | 49.3 | 298 | 49 | 459 | 81,877 |  2.57 |
| `988fe1a` | 4 | 676,100 | 11.7 |   1 |  0 | 117 |    341 |  0.01 |
| `988fe1a` | 6 | 746,254 |  9.5 |   0 |  0 | 148 |    445 |  0.03 |
| `988fe1a` | 8 | 726,532 | 47.8 | 492 | 20 | 194 |    484 |  0.89 |
| `4f7cd60` | 4 | 677,051 | 10.8 |   3 |  0 | 109 |  3,032 |  0.01 |
| `4f7cd60` | 6 | 745,716 | 13.8 |   7 |  0 | 160 |  7,407 |  0.11 |
| `4f7cd60` | 8 | 725,154 | 30.5 | 268 | 51 | 443 | 70,300 |  2.31 |

**Further figures, with 8 threads** (from the summary, the runs' JSON and
the GC logs):

* No reader parked in any phase, and none of the after-load calls over
  10 ms began under pressure, as on 2026-10-28.
* The gets over 10 ms run by run: the fix 238 and 254; `5a6befd` 164 and
  134; `4f7cd60` 144 and 124. On 2026-10-28 `eaec93e` and `4f7cd60` had
  122 to 175 a run. In gets: 11.3 in a million with the fix, 7.0 on
  `5a6befd`, 6.2 on `4f7cd60`. The longest gets: 47.8 and 24.4 ms with the
  fix, 31.8 and 49.3 on `5a6befd`, 30.5 and 21.0 on `4f7cd60`.
* p99.9 of the gets: 69.6 and 68.1 microseconds with the fix, 74.8 and
  120.3 on `5a6befd`, 72.2 and 70.7 on `4f7cd60`. Gets a second: the fix
  1.8 percent above `5a6befd`, 0.2 above `4f7cd60`, within the noise.
* The machine: 9.64 of its 10 cores with the fix, 9.75 on `5a6befd`, 9.54
  on `4f7cd60`, 7.86 on `bf19075`.
* The eviction thread: 0.354 cores with the fix, 0.301 on `5a6befd`, 0.315
  on `4f7cd60`; about 5,400 batches a phase with the fix against 5,100;
  the batches' time by the clock 1.03 times its CPU time (1.06 and 1.02),
  so on its core. The longest batch so far: 14 and 39 ms with the fix, 7
  and 13 on `5a6befd`, 18 and 10 on `4f7cd60`.
* The sampled readers (8, 20 s): BLOCKED in `Eviction.wake` on
  `java.lang.Object` in 1.3 and 0.6 percent of the samples on `5a6befd`,
  0.7 and 0.4 on `4f7cd60`, in none with the fix; with the fix BLOCKED
  most in `BufferedStream.read` (1.1 and 0.3 percent).
* The safepoints of the 8-thread phases (GC logs): with the fix 0 of 350
  took over 2 ms to reach, `5a6befd` 2 of 337 (3.4 and 2.0 ms), `4f7cd60`
  2 of 358 (2.1 and 2.4 ms). As on 2026-10-28 (Reading), running readers
  rarely lost their cores for long, so the long gets most likely fall
  where a safepoint does not wait for a reader: in the kernel's read, or
  blocked on a monitor.

**The night's floor.** This night was noisier than 2026-10-28 for every
build: gets of 6.1 to 19.2 ms with 4 threads (the first night at most
5.9), and on `bf19075` with 8 threads 18 gets over 10 ms, a longest of
16.5 ms and one after-load call of 10.2 ms (the first night none, 0.6 ms
and none). The other processes used 0.13 to 0.72 cores in the phases, but
1.35 to 1.39 in `bf19075`'s second run, the last (03:11 to 03:13). What
made the floor is not known. The builds ran in turns, so the comparison
between them stands; this night's counts and the first night's are not
comparable one to one.

**Against the expectation** (State, step 3), with 8 threads, the fix
against `5a6befd`:

* The entries into `evictorLock` from about 78,000 a second to a few
  hundred: **met**. 81,877 to 484 a second (`4f7cd60`: 70,300): 5 in
  1,000 of the calls over the trigger (97,540 a second with the fix), and
  fewer than 1 in 1,000 of all after-load calls (about 600,000 a
  second).
* The after-load call near its cost with 4 threads: **met, in the main**.
  459 to 194 ns, against 117 with 4 threads: 1.7 times the 4-thread cost,
  where it was 4.5 times (`bf19075`: 1.9).
* The after-load calls over 10 ms near 0: **not met**. 49 to 20 (8 and
  12), down three fifths. With the fix fewer than 1 in 1,000 calls
  enters the monitor; the numbers do not tell whether the 20 are among
  those or readers that lost their core within the call (the call is
  timed whole).
* The gets over 10 ms down by about a fifth, not to 0: **refuted**. Up
  from 298 to 492, and 268 on `4f7cd60`. Each of the fix's two runs is
  above each of the eight runs with 8 threads of the builds with 005-46
  and without the fix (`eaec93e`, `5a6befd`, `4f7cd60`), on both nights.
  The longest get did not change.

**What is shown, and what is not.**

* Shown: the fix does what it was made for. With 8 readers the loads no
  longer queue on `evictorLock`: 484 entries a second instead of 81,877,
  the readers blocked 0.89 percent of their time instead of 2.57, no
  sample BLOCKED in `Eviction.wake`, the after-load call 2.4 times
  cheaper, its calls over 10 ms down three fifths. Nothing got worse with
  4 and 6 threads, and the gets a second and the p99.9 are as before.
* Not shown: that the fix shortens the long gets. With 8 readers their
  count rose by about two thirds, and the longest stayed where it was
  (24.4 and 47.8 ms, against 21.0 to 49.3 before the fix). The runs, two a
  build on a night with a higher floor, do not tell whether the rise is
  the fix's or the night's, nor where in the get the time goes: only the
  after-load call is timed. Two readings, not tested: readers that no
  longer block on the monitor stay runnable on a full machine (9.6 of 10
  cores) and meet the path's other monitors and the kernel's read more
  often (with the fix BLOCKED most in `BufferedStream.read`); or the
  eviction thread, which runs more with the fix (0.354 cores against
  0.301), holds a map's monitor that readers enter while it is off its
  core (its longest batch 39 ms in one run).
* 2026.2's release notes (Limits) say "gets of up to 39 ms with 8 readers
  and ZGC's workers on F53's 10 cores": this night's longest were 47.8 ms
  with the fix and 49.3 ms before it.

**Recommendation** (for Frans; a stop, 016-05 section 8, as the result
goes against State's step 3). Keep the fix: it removes BergDB's own share,
the hot monitor, as designed; the only cost seen is the rise of the gets
over 10 ms, not yet known to be its. Before the close, one more step in a
quiet block: `threads.sh` with
`BUILDS="5a6befd 988fe1a" ROUNDS=4` and State's `B` (the two builds in
turns AB BA AB BA, about 20 minutes, the database loaded by the fix's jar;
no new build), to tell whether the rise of the gets over 10 ms is the
fix's. If it is not: the entry closes, the rest of the long gets accepted
as a full machine (Frans's decision of 2026-10-29). If it is: the
Recommendation's measurements of 2026-10-28 (7 threads; 8 threads with
`-XX:ConcGCThreads=1`; the get's parts timed in ScaleBench, as the
after-load call is) before any change to `java/`, which is Frans's to
decide.


Results, Q-A of night 006-12
----------------------------

Written 2026-11-06 by the night's coordinator's agent, from the block's
files; the numbers from its digest (`out/summary.txt`) and the steps'
`sum.py`, `gcsum.py` and `parts.py` outputs, the stalls by phase counted
from the GC logs.

**What ran.** Q-A, the first quiet block of night 006-12 on F53 (006-12,
section 3, W2, "Q-A"): the marker at 22:15, the runs 2026-11-05,
22:50:22 to 23:33:31. Everything is outside the repository (013-01,
section 4) in `/Users/f/fl/bench/006-12/qa/`: `README.md` (how it ran),
`block.sh`, `step.sh` (a copy of `threads.sh` that only reads the
repository), `results.txt`, `block.log`, `out/summary.txt` (the digest),
and per step `out/STEP/` (`runs.txt`, the runs' text and JSON, the GC
logs, `summary.txt`, `gc.txt`, for step 3 `parts.txt`). ScaleBench C as
in the AB/BA step (State): 10M key24 keys, 665 MB budget, ZGC, 2,660 MB
heap; the builds of `/Users/f/fl/bench/006-10/e65-builds`, A `5a6befd`
(`main` before the fix, jar `79925f95`) and B `988fe1a` (the fix, jar
`2b5202f0`); four rounds in turns, AB BA AB BA; each run 30 s of 7
threads, then 30 s of 8 threads, then 20 s of 8 sampled readers, so each
step has its own 8-thread control in the same JVMs. One 10M load for all
steps, with B's jar (118.9 s). The steps, in Frans's order, each exit 0,
"OK, 0 problems", 13 minutes each:

1. `t7`: 7 and 8 threads.
2. `cgc1`: the same with `-XX:ConcGCThreads=1` (otherwise ZGC used up to
   3 workers a cycle).
3. `parts`: as `t7`, with ScaleBench patched by `ScaleBench-086-parts.diff`
   on top of `ScaleBench-065.diff` (`qa/sb3/`, compiled against the two
   jars). For each reader it times the stream's reads (the `FileStream`
   under `BufferedStream`: the kernel's read and the `FileChannel`'s own
   locks) and the after-load calls, and reads the reader's CPU time and
   monitor counts at each batch of 64 gets. Each get over 10 ms is
   recorded with its parts and the GC pauses and safepoints that overlap
   it, and `parts.py` puts it in the first class that holds at least half
   its time: read (the stream's reads), after-load, safepoint, shared
   batch (another long get in its batch), blocked (on a monitor, outside
   the reads), off core (the batch's wall time less its CPU time, not
   blocked: runnable without a core, or waiting in the kernel), on core,
   mixed. Blocked time is in whole ms; a batch's figures include its
   other 63 gets (about 0.7 ms).

**The quiet verdict.** `results.txt` has every step "NOT QUIET (load 1.72
at 22:50)": the block waited from 22:15 for a 1-minute load below 1.5
twice 30 s apart, and it was below 1.5 only twice, not in a row (1.39 at
22:27:14, 1.48 at 22:45:50; otherwise 1.49 to 3.33). Nothing else was
running that the check looks for (no other JVM, gate, build, Lean or
`night.sh` in any check); the top processes were `sysmond`, the Claude
sessions, Finder, VS Code, the Wi-Fi drivers, and once ControlCenter and
WindowServer (22:41). At 22:50 it ran, as planned. The loads of 9.76 to
11.56 at the later steps' starts and at the end are the benchmark's own:
each step started as the one before ended, and within the phases the
machine was at 8.62 to 9.77 of its 10 cores, of which the other processes
used 0.14 to 0.29 (one phase 0.45: `cgc1`, A's round 2, 8 threads), as in
the AB/BA step (0.16 to 0.24). The noise is that of the AB/BA step or
less, with 8 threads:

| Runs                | Build | Gets > 10 ms, per round | Sum   | CV, rounds | CV, gets a second |
|---|---|---|---|---|---|
| AB/BA, 2026-11-05   | A     | 116 114 162 121         |   513 | 18 %       | 0.84 %            |
| AB/BA, 2026-11-05   | B     | 244 287 216 262         | 1,009 | 12 %       | 1.42 %            |
| Q-A, `t7`           | A     | 139 134 124 163         |   560 | 12 %       | 1.60 %            |
| Q-A, `t7`           | B     | 239 252 246 231         |   968 |  4 %       | 0.76 %            |
| Q-A, `parts`        | A     | 157 151 153 179         |   640 |  8 %       | 0.55 %            |
| Q-A, `parts`        | B     | 256 264 217 284         | 1,021 | 11 %       | 1.32 %            |

So the verdict does not weaken these comparisons: the builds ran in turns,
the 8-thread counts are within 10 percent of the AB/BA step's (560 and
968 against 513 and 1,009), and the fix has more in 4 of 4 rounds again.

**The three measurements.** Sums of the four runs; the longest get the
most of the four; machine cores the mean of the phases.

| Step    | Build     | Threads | Gets a second | Gets > 10 ms | Per round       | Longest, ms | After-load > 10 ms | Machine cores |
|---|---|---|---|---|---|---|---|---|
| `t7`    | `5a6befd` | 7 | 725,011 |    36 | 20 3 3 10       |  24.0 |   6 | 9.00 |
| `t7`    | `988fe1a` | 7 | 732,643 |    32 | 6 6 16 4        |  33.2 |   0 | 9.10 |
| `t7`    | `5a6befd` | 8 | 706,957 |   560 | 139 134 124 163 |  52.5 | 107 | 9.56 |
| `t7`    | `988fe1a` | 8 | 710,889 |   968 | 239 252 246 231 |  48.8 |  22 | 9.64 |
| `cgc1`  | `5a6befd` | 7 | 742,355 |    93 | 35 0 42 16      | 219.1 |   2 | 8.79 |
| `cgc1`  | `988fe1a` | 7 | 751,203 |   184 | 37 70 35 42     | 246.1 |   0 | 8.75 |
| `cgc1`  | `5a6befd` | 8 | 699,004 |    22 | 6 2 12 2        |  16.9 |   3 | 9.70 |
| `cgc1`  | `988fe1a` | 8 | 716,414 |    85 | 19 43 17 6      | 111.6 |   4 | 9.70 |
| `parts` | `5a6befd` | 7 | 703,578 |    37 | 9 6 11 11       |  30.8 |   5 | 8.97 |
| `parts` | `988fe1a` | 7 | 707,185 |    38 | 4 6 16 12       |  26.3 |   2 | 9.02 |
| `parts` | `5a6befd` | 8 | 687,716 |   640 | 157 151 153 179 |  34.4 |  99 | 9.56 |
| `parts` | `988fe1a` | 8 | 696,008 | 1,021 | 256 264 217 284 |  89.1 |  22 | 9.60 |

**(1) 7 threads (`t7`).** With 7 readers the gets over 10 ms fall from 560
to 36 (A) and from 968 to 32 (B): 0.41 and 0.36 in a million gets, against
6.6 and 11.4 with 8. **The rise with the fix is gone**: B has fewer than A
in sum (0.89 times), more in 2 of the 4 rounds; by the AB/BA step's rule
(at least 3 of 4 rounds and 1.3 times) it is not the fix's. `parts`
repeats it: 37 and 38 (1.03 times; B more in 2 rounds, as many in 1). The
longest gets with 7 readers are still 24.0 and 33.2 ms (`parts`: 30.8 and
26.3): rare, not gone. The readers' CPU: with 7, 6.77 to 6.81 cores of 7
(97 percent of their time), with 8, 7.33 to 7.44 of 8 (92 to 93 percent);
blocked on monitors, A 0.80 and B 0.24 percent with 7, A 2.40 and B 1.08
with 8. 7 is one fewer than F53's 8 performance cores, and with it the
machine is at 9.0 of 10 cores rather than 9.6; the step does not tell
which of the two matters (the 2 efficiency cores' share is not
measured).

**(2) 8 threads with `-XX:ConcGCThreads=1` (`cgc1`).** With the same 8
readers, ZGC limited to one worker, the gets over 10 ms fall from 560 to 22
(A, minus 96 percent) and from 968 to 85 (B, minus 91 percent): 0.26 and
0.99 in a million. The fix has more in 4 of 4 rounds (3.9 times, 63 more;
without B's round 2, which had allocation stalls in its 8-thread phase, 42
against A's 20 in the other three rounds). The longest with 8: A 11.4 to
16.9 ms, B 16.8 to 20.9 ms and 111.6 ms (that stall). The machine was as
busy as without the setting (9.70 cores); the readers got more of it, 7.65
to 7.71 cores of 8 in 7 of the 8 phases (one 7.32) against 7.33 to 7.44,
and the rest of the process less, 1.42 to 1.64 cores against 1.66 to
1.82. **The cost: one worker does not keep ZGC ahead.** The GC logs
have 1,196 allocation-stall cycle counts (`gcsum.py`; 0 in `t7` and
`parts`) and 65 safepoints over 2 ms, the
longest 53.2 ms (`t7`: 33, the longest 19.4 ms). Counted by phase (the
GC logs' stall lines): in the 7-thread phase, the first after the
warm-up, in 7 of 8 runs (14 to 72 stalls a run, the longest 100.2 to
246.0 ms: the 7-thread rows' longest
gets and most of their 93 and 184); in the 8-thread phase only in B's
round 2 (34, the longest 111.3 ms); after it, in the sampled phase, in 3
of B's runs. So the setting is no option for this heap (2,660 MB, 4 times
the budget); it shows that with a core left by the collector, 8 readers
have about as few long gets as 7.

**(3) The get's parts (`parts`).** The instrumentation cost 2.1 to 3.5
percent of the gets a second against `t7`; the counts are 3 to 19 percent
above `t7`'s. The recorded gets over 10 ms (643 and 1,026 with 8 threads,
the histogram's 640 and 1,021), sums of the four runs:

| Build     | Threads | Recorded | Read | After-load | Blocked | Off core | Other | Their ms | Off core ms | Read ms | Blocked ms |
|---|---|---|---|---|---|---|---|---|---|---|---|
| `5a6befd` | 7 |    37 |  12 |   5 |   2 |  16 | 2 |    513 |    511 |   183 |    67 |
| `988fe1a` | 7 |    38 |  19 |   2 |   4 |  13 | 0 |    512 |    510 |   246 |    89 |
| `5a6befd` | 8 |   643 | 267 | 100 |  61 | 215 | 0 |  7,893 |  7,869 | 3,321 | 2,192 |
| `988fe1a` | 8 | 1,026 | 499 |  22 | 110 | 393 | 2 | 12,980 | 12,949 | 6,187 | 2,236 |

"Other": shared batch (A 2 with 7 threads, B 2 with 8); no get was in the
classes safepoint, on core or mixed (safepoints overlapping the long gets:
2 and 3 ms in all, with 8). After-load ms with 8: A 1,147, B 282.

* **The long gets' time is off core.** 99.7 and 99.8 percent of it is wall
  time without CPU time (with 7 threads too): the reader was not running.
  It is not BergDB's code running, not the collector's pauses, not a
  safepoint. The batches of the 40 longest gets had 0.5 to 1.7 ms of CPU
  for wall times of 23 to 91 ms.
* **About half of it falls within the stream's read**, the kernel's read
  from the OS cache: the class read 267 of 643 (A) and 499 of 1,026 (B),
  42 and 48 percent of the time; the stream reads over 10 ms 260 and 490
  (with 7 threads 13 and 19), the longest 34.4 and 35.2 ms. The readers'
  stream reads are 1.674 a get for both builds and take 131 to 136 s of
  each 8-thread phase's 240 reader-seconds. The rest is off core outside
  the read (215 and 393), and blocked on a monitor (61 and 110; 2,192 and
  2,236 ms, 28 and 17 percent of the time; the monitor is not recorded,
  and the samples have the readers BLOCKED most in `BufferedStream.read`
  with B, 0.5 to 1.0 percent, in `Eviction.wake` with A).
* **The fix's extra long gets** (383 more): read +232, off core +178,
  blocked +49, after-load -78. The fix removes most of the after-load
  class (100 to 22: the hot monitor, as designed); what it adds are gets
  off core, in the read and outside it.
* What `parts.py` cannot tell: whether a reader off core was runnable
  without a core or waiting in the kernel (for example on the file's
  locks in the read); the efficiency cores' share. Not measured.

**What they explain.** The hypothesis of 2026-10-28 (a machine with as
many runnable threads as cores) is supported for the gets over 10 ms with
8 readers, and so for the fix's rise:

* With 8 readers, ZGC's 3 workers and the eviction thread there are more
  runnable threads than F53's 10 cores at times; a reader off its core for
  10 to 90 ms makes a long get, wherever it is in the get (half the time
  in the kernel's read, where most of its time goes).
* One reader fewer (`t7`) or two ZGC workers fewer (`cgc1`, the same 8
  readers reading the same file) take the count down by 91 to 96 percent.
  A cause in the kernel's read that grew with the readers would not go
  with fewer collector workers; a cause in BergDB's code would show as on
  core or blocked time, which is at most 28 percent of it.
* The rise with the fix comes only where the machine is full: with 7
  readers none (32 against 36), with 8 readers 1.6 to 1.7 times. A
  reading, not shown: the fix's readers block less (1.08 against 2.40
  percent of their time) and its eviction thread runs more (0.313 against
  0.285 cores), so more threads are runnable on a full machine and readers
  lose their cores more often. On an oversubscribed scheduler a small
  change of demand makes a large change in the waits.
* Not explained: why with 7 readers the longest gets still reach 24 to 33
  ms (off core too, rare: 0.4 in a million).


Options for Frans's decision, 2026-11-06
----------------------------------------

The evidence is in Results, Q-A of night 006-12. A change to `java/` is
Frans's to decide (Done when).

* **Option 1: keep the fix and close 015-86 as explained (recommended).**
  What changes: no code. This entry gets its Outcome (the long gets with 8
  readers on F53 are readers off their cores with as many runnable threads
  as cores, the operating system's scheduling, outside the ~20 ms target
  for BergDB's code, Frans's decision of 2026-10-29), and Status "done".
  The text that cites it changes with it: docs/levels.md section 7's case
  "not yet explained" (it still cites 005-65) becomes explained, and the
  next release's notes (`releases/next.md`; 2026.2's notes have "As many
  readers as cores" in their Limits) get the measured advice: readers at
  most the cores less the collector's workers (on F53 7 readers: 0.4 gets
  over 10 ms in a million, the same with and without the fix). Frans may
  also have 009's target 2 stated that way (the first Recommendation's (b);
  not reworded on 2026-10-29). Cost: items and docs text, about half an
  agent-hour, no gate. It leaves: with 8 readers on F53, 1.6 to 2.0 times
  as many gets over 10 ms as before the fix (about 11 to 12 in a million),
  longest gets of 30 to 89 ms; with 7 readers rare gets of up to 33 ms;
  and the open split of off core (runnable or waiting in the kernel).
* **Option 2: revert the fix (`988fe1a`).** What changes: `Eviction.wake`,
  `afterLoad` and `EvictorRun` back to `5a6befd`'s, every load over the
  trigger into `evictorLock` again; the commit's other two changes should
  stay (`sweep`'s trigger computed under its monitor, against the
  `setBudget` race, and an interrupt with a request pending not ending the
  thread), so it is a partial revert, with `testNoLostRequest` adjusted.
  Cost: a change in `Eviction`, `before-commit.sh`, `level4.sh` (the
  eviction mechanism), one 15-minute run in a quiet block; about 2
  agent-hours. Gain: with 8 readers about 40 percent fewer gets over 10 ms
  (560 against 968, 513 against 1,009), none with 7. It brings back
  BergDB's own share (`t7`, 8 threads): 67,000 to 78,000 entries into
  `evictorLock` a second, readers blocked 2.40 percent of their time
  against 1.08, 107 after-load calls over 10 ms against 22, 26.8 waits over
  10 ms a run against 5.5. It trades a cost in BergDB's code for fewer of the scheduler's
  gets, on a full machine only.
* **Option 3: keep the fix and measure more before closing.** What: 8
  readers with `-XX:ConcGCThreads=2` (does ZGC keep up, with no
  allocation stall, while most long gets go?), as `step.sh` with that
  option, both builds in turns; it would give users with as many readers
  as cores a measured JVM setting, as a separate recommendation (the GC
  choice is not BergDB's code; Frans, 2026-10-27). The split of off core
  into runnable and waiting in the kernel needs a scheduler trace, which
  needs root on F53 (no passwordless sudo): not proposed. Cost: about 15
  minutes of a quiet block, an agent-hour, no change to `java/`. It leaves
  the entry open until then; the outcome would be Option 1 with one more
  line of advice.
* **Option 4: a change against the blocked share.** Every stream read
  enters `BufferedStream`'s monitor (the bounds check in `read`, about 1.2
  million entries a second with 8 readers), and with the fix it is where
  the samples find readers BLOCKED most. The blocked class is 110 of B's
  1,026 long gets (17 percent of their time): the most such a change could
  remove. Change: the lengths read without the monitor for a read wholly in
  the file. Cost: a change to a core storage class under concurrent
  appends, its tests, `before-commit.sh` and the level scripts, a `parts`
  run; about 3 to 5 agent-hours. It leaves the off-core gets (over 80
  percent of the time), and by the fix's experience readers that block less
  stay runnable more on a full machine, so it may not lower the count.
  Not recommended now. Since 2026-11-06 a topic to consider after release
  2026.3, as reader scaling (017-07, section 5; Outcome).

**Recommended:** Option 1. The fix removes BergDB's own share as designed;
the gets it seems to add are the scheduler's on a full machine, and they
go, for both builds alike, when one reader or two collector workers fewer
leave a core. Option 3 only if Frans wants a JVM setting to recommend for
as many readers as cores.


Outcome
-------

**Frans's decision, 2026-11-06, 11:09 to 11:11: Option 1**, keep the fix
(`988fe1a`) and close this entry as explained. The long gets with 8
readers on F53 are readers off their cores on a full machine: 8 readers
and ZGC's workers on F53's 8 performance and 2 efficiency cores, so the
operating system's scheduling, outside the ~20 ms target for BergDB's own
code (Frans, 2026-10-29). With 7 readers the fix adds none (32 against 36
gets over 10 ms; Results, Q-A of night 006-12). The texts that cite it:
docs/levels.md, section 7 (explained, no longer the open case); the next
release's notes, under Known issues and limits (at most as many readers as
the cores less the collector's workers, 7 on F53, with the figures);
010-01, P1, and 009-01's target 2 (a sentence each). No change to `java/`.

**Option 4 to consider after 2026.3.** Frans, in the same exchange: "How
about Option 4 for a later release. Should that be a thing to consider?"
The coordinator's answer: yes, as reader scaling rather than as this
entry's fix, and not for 2026.3 (the bug-free Core is its target, and the
change is a risk in a core storage class under concurrent appends);
measure first. Frans: "Yes, both." It is 017-07, section 5.

Left, not measured: what the off-core time is (runnable without a core,
or waiting in the kernel; that needs a scheduler trace, and root on F53),
and why with 7 readers the longest gets still reach 24 to 33 ms.


State
-----

**2026-11-06, 11:09 to 11:11: done, by Frans's decision** (Outcome):
Option 1, and Option 4 to 017-07, section 5.

**2026-11-06: Q-A run (night 006-12); Frans's decision left.** Known
(Results, Q-A of night 006-12): the gets over 10 ms with 8 readers, and the
fix's rise of them, are readers off their cores on a full machine: with 7
readers 36 and 32 in four runs (no rise), with 8 readers and
`-XX:ConcGCThreads=1` 22 and 85 (but allocation stalls of up to 246 ms),
with 8 readers 560 and 968; their time 99.7 percent off core, about half
within the kernel's read, the after-load class cut from 100 to 22 by the
fix. Q-A ran NOT QUIET by its start check (load 1.72 at 22:50), with noise
as low as the AB/BA step's. Frans decides: Options for Frans's decision,
2026-11-06 (1, keep the fix and close as explained, recommended; 2, revert
the fix; 3, measure `ConcGCThreads=2` first; 4, the `BufferedStream`
monitor). Next step: by his decision; with Option 1, this entry's Outcome
and Status "done", 015's readme line, and the texts of docs/levels.md
section 7 and `releases/next.md` by whoever keeps them; no `java/`, no
gate.

**2026-11-05: Frans's decision, and the AB/BA step not yet run.** Frans,
decided 2026-11-04/05 (asked 2026-11-04, 19:23; answered 2026-11-05,
07:17), on the Recommendation of Results, 2026-11-04 night: "Run the AB/BA
step in tonight's quiet block. Close the entry if the fix isn't the cause;
otherwise take the measurements and move the decision to 015." The step
was to run in the morning's quiet block on F53, after 005-47's runs, by
Claude (Opus 5.5, Claude Code), and did not: F53 was not quiet by the
block's limit of 07:55. macOS's `mediaanalysisd` was paused by the
coordinator at Frans's word from 07:32:35 to 07:56:17, but the 1-minute
load stayed at 1.33 to 3.11 (VS Code; from 07:50 another session's C
build), below 1.5 only three times and never twice in a row, and 3.02 at
07:55:59; so the runs were skipped (005-47, Left, has the details; the
block's log in `/Users/f/fl/bench/quiet-block-2026-11-05/block.log`).

Left, for the next quiet block (about 24 minutes: the 10M load with the
fix's jar, then 8 runs, AB BA AB BA, within `threads.sh`'s 30):

    cd /Users/f/fl/repos/bergdb/items/005-todo/65-gets-with-8-readers/night
    B=/Users/f/fl/bench/006-10/e65-builds BUILDS="5a6befd 988fe1a" ROUNDS=4 sh threads.sh

* `B` checked 2026-11-05: the clones `5a6befd` and `988fe1a` at their
  commits, clean, their jars those of step 1 (`79925f95` and `2b5202f0`),
  `sb/classes-5a6befd` and `sb/classes-988fe1a` in place. No `prep.sh`.
* Before the run, set `$B/raw/threads` aside: it holds the GC logs of
  2026-11-04, and the run writes logs of the same names for both builds'
  rounds 1 and 2. After it, move `night/out/` and this run's
  `$B/raw/threads` out of the repository to a dated directory under
  `/Users/f/fl/bench/`, and put the old logs back.
  `/Users/f/fl/bench/quiet-block-2026-11-05/block.sh` does all of this
  (after 005-47's runs); its time limit (07:55) is to be changed for
  another block.
* How to read it, written before any run: the rise is the fix's if, with
  8 threads, the fix has more gets over 10 ms than `5a6befd` in at least
  3 of the 4 rounds and at least 1.3 times as many in sum (2026-11-04:
  492 against 298, 1.65 times); otherwise it is not shown to be the fix's,
  and the entry closes as Frans decided. If it is the fix's: the
  measurements of the Recommendation, and the decision moves to 015.

**2026-11-05, 08:11:47 to 08:31:41: the AB/BA step, run.** In the
coordinator's second quiet block of the morning
(`/Users/f/fl/bench/quiet-block-2026-11-05-2/block.sh` and its
`block.log`), after 015-85's runs; `mediaanalysisd` paused at Frans's
word for the block. Not quite quiet: the 1-minute load 1.77 at the
block's start of runs, 1.88 at `threads.sh`'s own check (08:12:02, "3
idle" sessions); at the block's end VS Code's `cpptools` took about 70
percent of a core, so the last rounds may have had it too, for both
builds alike (the rounds in turns). `threads: OK, 0 problems`. The
outputs in `/Users/f/fl/bench/005-65-abba-2026-11-05/` (`out/summary.txt`,
`out/runs.txt`, `gc-logs/`); the 2026-11-04 GC logs put back in
`$B/raw/threads`.

With 8 threads, per round (A is `5a6befd`, `main` before the fix; B is
`988fe1a`, the fix):

| Round | Gets > 10 ms, A | Gets > 10 ms, B | Longest get ms, A | Longest get ms, B | Waits > 10 ms, A | Waits > 10 ms, B |
|---|---:|---:|---:|---:|---:|---:|
| 1     | 116 | 244 | 25.7 | 62.2 | 18 | 2 |
| 2     | 114 | 287 | 23.3 | 57.1 | 23 | 5 |
| 3     | 162 | 216 | 37.2 | 70.8 | 27 | 7 |
| 4     | 121 | 262 | 21.5 | 37.1 | 22 | 6 |
| Sum   | 513 | 1,009 | | | 90 | 20 |

* By the rule written before the run, **the rise is the fix's**: B has
  more gets over 10 ms in 4 of 4 rounds, 1.97 times as many in sum.
* The fix does what it was made for: no load enters `evictorLock` (0
  against 66 to 76 thousand a second), the after-load call is cheaper,
  and the readers' waits for the eviction thread over 10 ms fall from 90
  to 20. With 4 and 6 threads nothing changes (no get over 10 ms but two
  in A's 6-thread runs); gets a second are the same within 0.4 percent.
* With the fix the eviction thread runs more (0.318 against 0.280
  cores, more batches: 4,899 to 4,981 against 4,612 to 4,799 a phase),
  and its batches take longer by the clock (9.8 to 9.9 s against 8.4 to
  8.8 s a phase). One explanation, not checked: before the fix the
  loads' entries into `evictorLock` slowed the readers a little, and so
  the loads; with the fix the readers go faster into the eviction
  thread's batches, and on a machine with as many runnable threads as
  cores a reader that is off its core during a batch waits longer. The
  sampled readers' states show more `BLOCKED in BufferedStream.read` with
  the fix in rounds 2 and 4 (1.5 and 1.8 percent).
* Left, as Frans decided ("otherwise take the measurements and move the
  decision to 015"; the entry is in 015 since the morning): the
  Recommendation's measurements, then his decision. Not run today.

Rerun on 2026-11-04 (Results, 2026-11-04 night): the expectation of step
3 is met for the monitor (the entries into `evictorLock`, the after-load
call's cost) and not for the long gets, which rose. The entry stays open
for Frans's decision on the Recommendation of that section; docs/levels.md
section 7's "not yet explained" stays (016-04), and the release notes'
known issue stays as it is (016-01, section 4.2). Steps 1 and 2 below are
done; `B` still holds the four builds and `sb/`.

As written on 2026-10-29: open until the thread sweep reruns with the fix
in a quiet block on F53, as on 2026-10-28
([night/](../005-todo/65-gets-with-8-readers/night/)), with four builds in turns:
`bf19075` and `4f7cd60` (the first night's reference and HEAD), `5a6befd`
(`main` before the fix) and `988fe1a` (the fix). Made for it on
2026-10-29: the third version of `ScaleBench-065.diff` counts the
after-load calls that enter `evictorLock` (an estimate: with the fix, the
calls that found `wanted` clear just before the call), `sum.py` prints
them in its tables of where the time went, and `prep.sh` compiles
ScaleBench with `bergdb.pub.util.SyncLevel` for a jar of `main` (005-56).

1. Before the block, not quiet (under a minute, then about 2 minutes),
   from the repository's `items/005-todo/65-gets-with-8-readers/night/`:
   `B=/Users/f/fl/bench/006-10/e65-builds BUILDS="bf19075 5a6befd 988fe1a 4f7cd60" sh prep.sh`,
   then the same `B` and `BUILDS` with `SMOKE=1 sh threads.sh`, which must
   print `threads (SMOKE): OK`. Done 2026-10-29, 10:44 to 10:47, with
   these four builds (jars `308e7d01`, `79925f95`, `2b5202f0` and
   `517165ee`, by the first 8 bytes of their SHA-256): `threads (SMOKE):
   OK, 0 problems`, 24 of 24 rows; in its small runs (20,000 keys, a
   0.5 MB budget) `5a6befd` entered `evictorLock` 351,000 to 382,000 times
   a second, the fix 1,000 to 3,000. So `B` is ready, and step 2 can run
   as it is; step 1 again only if `B` is lost.
2. In the block, the same `B` and `BUILDS` with `sh threads.sh`: about 21
   minutes (the 10M load with `4f7cd60`'s jar, as on 2026-10-28, then 8
   runs, ABCD DCBA), within its `# minutes: 30`. The summary in
   `night/out/summary.txt`; the raw outputs stay out of the repository.
3. Expected, by (a): with 8 threads, the fix against `5a6befd`, the
   entries into `evictorLock` from about 78,000 a second to a few hundred,
   the after-load call near its cost with 4 threads, the after-load calls
   over 10 ms near 0, and the gets over 10 ms down by about a fifth, not
   to 0. Then the results here, and the entry closes.


Done when
---------

The runs of the test in a quiet block, the explanation written here (the
hypothesis confirmed or refuted, and by what), and a recommendation for
Frans: nothing (a machine with as many readers as cores is outside the
target), a change (for example, a reader that runs a batch itself instead
of waiting for the eviction thread; or the eviction thread at a higher
priority), or more measurements. A change to `java/` is a decision for
Frans after the explanation. Since Frans's decision of 2026-10-29: the
rerun with the fix (State), written here.


First step
----------

`threads.sh` in the next quiet block on F53 (006-10, W2), after its
`.READY` marker. Done 2026-10-28, 19:34 to 19:50 (Results). Frans decided
and the fix is in `main`, 2026-10-29 (Decision and fix). The rerun ran
2026-11-04 (Results, 2026-11-04 night). Next: Frans's decision on its
Recommendation (State). The AB/BA step ran 2026-11-05 (State), and
the Recommendation's measurements in Q-A of night 006-12 (Results, Q-A of
night 006-12). Frans decided on 2026-11-06 (Outcome): done.


Size and order
--------------

S, measurements only, unless a change follows. Needs a quiet F53. Comes
from item 009 (target 2) and 005-46, which made the readers faster;
touches 005-51 (the eviction thread's waits).


Plan for 2026.2
---------------

Written 2026-11-03 for 016-05 (W4): State's steps 2 and 3, in night 1's
quiet block, then the explanation and the close. The fix it measures is in
the release; the rerun changes no code. With Frans's message of 15:40
("try your best to finish this work by 07:00 tomorrow in the morning"),
the block is in window 2 only, from `night.sh`'s end (about 03:00) to
06:05 (the conductor's end of window 2), and this step runs first
(016-05, section 6).

**The builds**, checked on 2026-11-03 (read only): in
`/Users/f/fl/bench/006-10/e65-builds`, four clones, each at its commit
with a clean tree and its jar, the jars those of State's step 1 (the first
8 hex digits of their SHA-256):

| Build     | What                                       | Jar SHA-256 |
|---|---|---|
| `bf19075` | 005-50, the first night's reference        | `308e7d01`  |
| `5a6befd` | `main` before the fix (012-16's commit)    | `79925f95`  |
| `988fe1a` | the fix                                    | `2b5202f0`  |
| `4f7cd60` | 006-09's HEAD, the first night's; the load | `517165ee`  |

And `sb/`: `src` (ScaleBench with `ScaleBench-065.diff`), `classes-` of
each build, `pidio`; `smoke/`, the smoke of 2026-10-29 (24 of 24 rows).
The JVM is `/opt/homebrew/opt/openjdk` (JDK 27; Q2's JDK 17 is installed
as `openjdk@17` beside it and changes nothing here). Disk: 439 GB free
for the 10M database in `$B/sbdata`.

The steps, by agent F2 (016-05), first in its row:

1. **The step script** (written 2026-11-03):
   [night/rerun-016.sh](../005-todo/65-gets-with-8-readers/night/rerun-016.sh), a
   wrapper with `# minutes: 30` that sets `B` and `BUILDS` (above) and
   runs `threads.sh`, which checks every jar, class and tool it needs
   (exit 2 if one is missing), keeps its own quiet check (two checks 15 s
   apart) and its deadline of 30 minutes, and checks its parsed summary
   (24 rows: 8 runs, three thread phases each). Not `performance.sh`, so
   no `FORCE=1`.
2. **The smoke and READY** (0.3 hours, by day, untimed): `SMOKE=1 sh
   /Users/f/fl/repos/bergdb/items/005-todo/65-gets-with-8-readers/night/rerun-016.sh`,
   about a minute (outputs in `$B/smoke`, outside the repository); it
   must print `threads (SMOKE): OK, 0 problems; ...`. Then `touch
   .../night/rerun-016.sh.READY`, and the last line with its time in
   this entry's Log. Planned by 18:00; at the latest by 01:30.
3. **The block**: the conductor's step `65-rerun` (its `steps.txt` line in
   016-05, section 6), about 21 minutes. Its outputs land in this
   entry's `night/out/` in the main tree (untracked; `threads.sh`'s
   `OUTROOT`) and in `$B/raw/threads`.
4. **The morning** (1.2 hours, F2 or another agent, from about 05:00 or
   06:00):
   * `night/out/summary.txt` copied to
     `night/results-2026-11-04.txt`; `night/out/` moved to
     `/Users/f/fl/bench/016/005-65/out-2026-11-04/` (raw outputs stay out
     of the repository).
   * A section "Results, 2026-11-04 night" here, as the 2026-10-28 one:
     per build and thread count, the gets a second, the longest get, the
     gets over 10 ms, the after-load calls over 10 ms, the entries into
     `evictorLock` a second, the readers blocked.
   * The explanation, against State's step 3 (expected by (a)): with 8
     threads, the fix against `5a6befd`, the entries into `evictorLock`
     from about 78,000 a second to a few hundred, the after-load call near
     its 4-thread cost, the after-load calls over 10 ms near 0, the gets
     over 10 ms down by about a fifth, not to 0. Confirmed or refuted, by
     which numbers.
   * The recommendation of "Done when": with the expectation met,
     nothing (as many readers as cores is outside the target, Frans's
     decision of 2026-10-29); otherwise more measurements or a change,
     which is Frans's to decide (a stop, 016-05, section 8).
   * With the expectation met: an Outcome, Status "done (2026-11-04)";
     docs/levels.md, section 7's "not yet explained" is updated by 016-04's
     agent from it. The hand-off as 016-05, section 4 (no `java/`, no
     gate).
   * If the step did not run, was `NOT QUIET` (the conductor's
     `results.txt`), or failed: the entry stays open, its State says so,
     and the release notes keep 005-65's known issue as it is (016-01,
     section 4.2); the release does not wait for it.
5. **The review** (0.2 hours): another agent reads the results' section
   against `summary.txt`, the numbers only.

Size: about 1.5 agent-hours and 30 minutes of the block (about 21 used).
Depends on nothing of tonight's code: the four builds are fixed. No stop
for Frans unless the results go against the expectation.

**State** (2026-11-03, 16:06): the wrapper is smoke-tested and READY;
its step `65-rerun` is in night 1's `steps.txt`
(`/Users/f/fl/bench/016/night1/`). `prep.sh` need not run again (State's step 1: only if `B`
is lost).

**State** (2026-11-04): steps 1 to 4 done. Step 3 ran 02:53 to 03:13,
quiet, exit 0. Step 4: the summary kept as `night/results-2026-11-04.txt`;
`night/out/` moved to `/Users/f/fl/bench/016/night1/005-65-out/` (not to
the `out-2026-11-04/` named above); the markers `rerun-016.sh.READY` and
`.DONE` removed; the results, the explanation and the recommendation in
Results, 2026-11-04 night. The expectation is not met for the long gets,
so the entry stays open, a stop for Frans (016-05, section 8). Left: step
5, the review of the results' numbers against `summary.txt`.


Log
---

2026-11-03. Planned for night 1 of release 2026.2 (016-05): the rerun in
window 2, by `night/rerun-016.sh` (written, not yet smoke-tested), then
the results, the explanation and the close in the morning.

2026-11-03, 16:06. `SMOKE=1 sh night/rerun-016.sh`: "threads (SMOKE):
OK, 0 problems" (16:04 to 16:05, beside other runs, so its numbers mean
nothing). `rerun-016.sh.READY` written; the step `65-rerun` (30 minutes)
added to night 1's `steps.txt`, first in window 2.

2026-11-04. The rerun, by the conductor's step `65-rerun` in night 1's
window 2: 02:53 to 03:13, quiet, exit 0, `threads: OK, 0 problems`.
Written up in Results, 2026-11-04 night: with 8 readers the fix takes the
loads' entries into `evictorLock` from 81,877 to 484 a second and the
after-load call from 459 to 194 ns, its calls over 10 ms from 49 to 20;
the gets over 10 ms rose from 298 to 492, the longest unchanged (47.8 ms
with the fix, 49.3 before it). Against State's step 3: open, for Frans's
decision. The summary kept as `night/results-2026-11-04.txt`; the raw
outputs moved to `/Users/f/fl/bench/016/night1/005-65-out/`; the markers
removed.

2026-11-05. Frans approved the Recommendation's AB/BA step (decided
2026-11-04/05). Not run in the morning's quiet block: F53 not quiet by
07:55, although `mediaanalysisd` was paused from 07:32 to 07:56 (State).
Left for the next quiet block, with the command and how to read it.

2026-11-05, 08:11 to 08:31. The AB/BA step, run in the coordinator's
second quiet block: the rise of the gets over 10 ms is the fix's (1,009
against 513 with 8 threads, more in 4 of 4 rounds). Left: the
Recommendation's measurements, then Frans's decision (State).

2026-11-06. Q-A of night 006-12, written by the night's coordinator's
agent: the three measurements, run 2026-11-05, 22:50 to 23:33, NOT QUIET
by the start check (load 1.72), noise as in the AB/BA step. Gets over
10 ms, A against B: 7 threads 36 and 32 (no rise); 8 threads 560 and 968;
8 threads with `-XX:ConcGCThreads=1` 22 and 85, with allocation stalls of
up to 246 ms; the long gets' time 99.7 percent off core, about half within
the kernel's read. Written up in Results, Q-A of night 006-12, with Options
for Frans's decision (Option 1 recommended: keep the fix, close as
explained); State updated.

2026-11-06, 11:09 to 11:11. Frans chose Option 1, and Option 4 to
consider after 2026.3 (Outcome). Done: the Outcome, docs/levels.md
section 7, the next release's notes (Known issues and limits), 010-01's
P1, 009-01's target 2, 017-07's section 5, and 015's readme (Closed).
