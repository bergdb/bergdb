006-16. Plan: Props across BergDB's history, 2013 to the 2026.4 candidate
=========================================================================

Written 2026-11-09, 08:40 to 09:00, before the measured CORE runs, for Frans
Lundberg's request of 08:21: "About the old Props, basic performance
properties. Something we can use and compare with 2012 era too. Study this and
the results for the old code (pre 2026) and the 2026 releases, include the
2026.4 candidate." The method follows 006-02 (its `run.sh`, its rules for a
quiet machine); the scripts are in this directory, the builds and the raw
output in the work directory `/Users/f/fl/bench/006-16/`.


What is measured
----------------

Props (`bergdb.dev.props.Props`, created 2015-01-06 from CorePerf of 2012 to
2014, MemPerf and StreamSize) prints three numbers, all better when lower:

* **MEM**: heap bytes per KV after one million KVs (keys `"0"` to
  `"999999"`, empty values, 100 per transaction, `testSetup()` with a dummy
  main stream: no eviction, retain forever); the heap after `System.gc()`,
  after minus before. One thread, no timing.
* **CORE**: four Core tests, each in a new database of 100,000 KVs (4-byte
  binary keys, empty values, batches of 10,000), five rounds in one JVM, the
  best time of each divided by cissi's of July 2013 (1.0, 0.4, 0.2 and 5.0 us),
  the geometric mean of the four:
  `get`, one thread, random gets for 2 s (after 10,000 warm-up gets);
  `get4t`, four threads for 1 s, the time per get of all threads together;
  `getmany`, one thread, forward scans of 10,000 KVs for 2 s after 0.5 s of
  warm-up, the time per KV; `set`, 100,000 single-KV transactions with random
  4-byte keys, run twice (200,000) into a new database with a dummy stream
  after a warm-up of 50,000 in another, the time per transaction.
* **SS**: stream bytes per user byte, the geometric mean of four scenarios
  of 100 MB each (KVs of 1,000 bytes for SS1 and SS2, 100 bytes for SS3 and
  SS4; 100 KVs per transaction for SS1 and SS3, one for SS2 and SS4) into a
  `MemoryStream` with the default builder.

MEM and SS do not depend on time (006-02: the same in every run of a
version, and equal to cissi's for the same code and object layout). CORE
depends on the machine and on what else runs; `get4t` most (006-02,
section 7).


The builds
----------

Fourteen, a series from the oldest code in Git to the 2026.4 candidate:

| Name       | Commit    | What                                                        | Props |
|------------|-----------|-------------------------------------------------------------|-------|
| 2013.1     | `9ffbdf9` | release-2013.1.130606 (KissDB), the first release: 2012's work | p16   |
| 2013-07-05 | `550ce4e` | the code of CORE's baseline, run on cissi 2013-07-05 10:53  | p16   |
| 2013.3     | `466a18f` | release-2013.3-3                                            | p16   |
| 2014.1     | `7e29e8e` | release-2014.1-3, the last release with the node stream     | p16   |
| 2015.1     | `f51fc8d` | release-2015.1-1, the KV stream (kv2), the first Props      | own   |
| 2015.4     | `9384bce` | release-2015.4-2, the last public release                   | own   |
| 2015-12-28 | `bc11dbf` | "Typical output (2015-12-28)" (006-02)                      | own   |
| 2017-07-29 | `dbf131a` | the last Props run on cissi (006-02)                        | own   |
| 2017-08-01 | `195cf88` | the 2017 import (006-02)                                    | own   |
| 2026-10-19 | `11ea2f6` | 006-02's 2026 code                                          | own   |
| 2026.1     | `a42947c` | the release jar, `releases/2026.1/`                         | own   |
| 2026.2     | `95bde62` | the release jar                                             | own   |
| 2026.3     | `929fa33` | the release jar                                             | own   |
| 2026.4c    | `f3af680` | the 2026.4 candidate: main at 08:22 today, kept all day     | own   |

The first eight from F1-007's `bergdb-git.bundle`, the next two from this
repository, all compiled as 006-02 did (one `javac --release 8` of `git
archive`; 2013.1 without `src-icu`, whose ICU jar is not in Git and which
nothing else needs). The rebuilt 2015-12-28, 2017-07-29, 2017-08-01 and
2026-10-19 have the same class hashes as 006-02's builds. 2026.1 to 2026.3
are the release jars as released (checked against `SHA256SUMS`); 2026.4c is
the candidate's `java/build.sh` jar, built the way the release jars were.

**Which Props.** "own" is the version's own `bergdb.dev.props.Props`. From
2015.1 to 2026.4c it is the same code but renames, comments and the builder
lines of the Core tests: the tests' `FixedDurationEvictBoss` (the default
eviction until it was removed on 2015-08-16) in 2015.1 and 2015.4, and
`retainForever()` until 2026-11-05 (015-87), the default since 2013-07-07.
Before 2015 there is no Props: **p16** (`P16.java.in`, made for each API of
the time by `run.sh`) runs MEM and SS as ports of 2015-12-28's `Mem` and
`SS1` to `SS4` (`set` instead of `put` until 2013.3, `db.sync()` instead of
`sync(SyncLevel)` until 2014, a `NullStream` for the `DummyStream`), and CORE
from the code's own four tests (`Get.run`, `GetThreaded.get4t`,
`PerfGetMany.standard`, `Set.normal`), called as CorePerf called them in 2013
and 2014; these are the tests that Props's Core runs, with the same
workload: their sizes, threads, times and keys are the same from 2013.1 to
2026 (checked by diff), and CorePerf's fifth test, `set2`, is left out as in
Props. One deviation: SS's builder gets `retainForever()`, the default from
2013-07-07; 2013.1's default (7 days, with reclaim) fails in its own
`GetMany` during SS.


The machine and the JVM
-----------------------

F53 (MacBookPro18,3, M1 Pro, 8 performance and 2 efficiency cores, 32 GB,
macOS 27, on the charger), OpenJDK 27 (Homebrew), default flags (G1, compact
object headers), no `-ea`, as Props was run from 2013 to 2017 and in 006-02.
Every build runs on JDK 27; no other JDK is needed.


The runs
--------

1. **MEM and SS, at any time** (`run.sh memss memss`): one run of `Mem` (or
   p16 `mem`) and one of `SS` (p16 `ss`) of each build, fresh JVMs, while the
   machine is busy. Every Props run below repeats them.
2. **CORE, on a quiet machine only** (`run.sh rounds main 6`): six rounds,
   each a full Props run (MEM, CORE, SS in one fresh JVM) of each of the 14
   builds; the order round-robin, forward (2013.1 to 2026.4c) in rounds 1, 3,
   5 and backward in rounds 2, 4, 6, so that each build has runs early and
   late in the block; 10 s between runs. A Props run takes about 30 to 50 s,
   so the block takes about 1.5 to 2 hours with the waits.
   * The block starts after 4 quiet checks in a row, 30 s apart; each run
     after 2 more, 10 s apart. A check is quiet when the 1-minute load average
     is under 1.5, no other JVM runs (`ps`; the editor's idle Java language
     server excepted), no other session's `QUIET-BLOCK` marker exists
     (`/Users/f/fl/bench/*/QUIET-BLOCK`, `/Users/f/fl/bench/coord/*/`), the
     commit gate is not running (`lockf -t 0
     /Users/f/fl/bench/006-15/gate.lock true` succeeds), and no
     `before-commit.sh`, `night.sh`, `performance.sh`, `perf.sh`, level
     script or `lake build` runs. A run waits as long as it takes; no run is
     taken in noise. Each run file records the check (load, JVMs, markers,
     gate, busy sessions) and the load after the run.
   * During the block `/Users/f/fl/bench/006-16/QUIET-BLOCK` says so to the
     other sessions, and this session stays idle (006-02's lesson: its own
     tool calls disturb `get4t`).
   * If the machine is not quiet by 13:00, or the block cannot finish by then,
     the item is finished with what has run and says what is missing and the
     commands to run it. Four rounds are the minimum for a CORE figure.
3. Nothing else: no other flags or JVMs (006-02 measured the collector and
   the object header).


Analysis
--------

* Per build and number (MEM, CORE and its four parts, SS and its four): the
  median, minimum and maximum over the runs (`summary.py`); the ratio of the
  median to CORE's 1.00 (cissi, July 2013) and to 2026.3.
* **What counts as a difference.** MEM: 2 bytes per KV or more (006-02: a
  build's runs within 1). SS: 0.01 or more in SS or a scenario (it does not
  vary). CORE and its parts, printed with two decimals (a step is about 3
  percent at F53's 0.25 to 0.35): a difference of the medians of two steps or
  more, or of one step when the ranges do not overlap; for `get4t`, only when
  the ranges do not overlap.
* **2026.4c against 2026.3**: a regression is a difference by that rule in
  the worse direction, in MEM, SS or CORE or any of its parts.
* **The 2013 comparison**: on F53 the 2013-07-05 build is the very code whose
  times on cissi define CORE's 1.00 (in fact cissi gave 0.89 that day: the
  baseline is rounded up); so its CORE on F53 is the factor of the machine
  and the JVM for that code, and every later build's CORE is comparable to
  it. Cissi's figures of 2013 to 2017 in Frans's logs (F1-007 `bergdb/log.md`,
  the comments of `Core.java`, `Props.java`, `Mem.java`, `SS.java`) are set
  beside the F53 figures of the same code. 2012's figures (Rose, a 32-bit
  netbook, and linda, a Linode server; `doc/log-old/2012-log.txt`,
  `doc/2012/`) are of other tests and machines: quoted, not compared, but for
  the one link that exists (Rose and cissi ran the same CorePerf in June and
  July 2013).
* What changed and why, from the history (commits and items), where a number
  moves.


Deliverables
------------

* `runs/` (copied from the work directory): one file per run, and
  `machine.txt`.
* `summary.py` and `summary.txt`: the tables, from the runs.
* `run.sh`, `P16.java.in`: the builds and the runs.
* The report, [../16-props-across-releases.md](../16-props-across-releases.md);
  its line in 006's index.

Nothing in `java/`, `lean/` or `docs/` changes; nothing is committed.
