006-16. Props across BergDB's history, 2013 to the 2026.4 candidate
====================================================================

Created 2026-11-09 by Frans Lundberg. Status: open.

**State (2026-11-09, 09:05): MEM and SS done for all 14 builds; CORE not run:
needs a quiet F53.** The timed block waited from 08:37 for a quiet machine and
was stopped by the day's coordinator at about 09:00 (the 2026.4 release runs
need F53 today); no CORE run was taken. The builds are ready in the work
directory `/Users/f/fl/bench/006-16/`; the commands to run CORE, for a night
coordinator, are in section 4. When CORE is in, fill sections 2 and 3's CORE
rows and set the status to done.

At Frans's request (2026-11-09, 08:21): "About the old Props, basic
performance properties. Something we can use and compare with 2012 era too.
Study this and the results for the old code (pre 2026) and the 2026 releases,
include the 2026.4 candidate." After 006-02 (Props on the 2015, 2017 and
2026-10-19 code), whose method and scripts this item reuses. The plan,
written before the measured runs, is
[16-props-across-releases/plan.md](16-props-across-releases/plan.md); the
scripts and every run's output are in
[16-props-across-releases/](16-props-across-releases/). Nothing outside this
item and the work directory was changed.


Summary
-------

Props prints three numbers, all better when lower: **MEM**, heap bytes per KV
with a million small KVs; **CORE**, four Core tests against cissi's times of
July 2013 (1.00); **SS**, stream bytes per user byte in four scenarios. MEM and
SS do not depend on the machine; CORE does. F53, JDK 27, default flags.

| Build      | Code date  | Commit    | MEM | SS (SS1, SS2, SS3, SS4)       | CORE        |
|------------|------------|-----------|-----|-------------------------------|-------------|
| 2013.1     | 2013-06-06 | `9ffbdf9` | 144 | 1.83 (1.14, 1.58, 1.50, 4.12) | not run     |
| 2013-07-05 | 2013-07-05 | `550ce4e` | 144 | 1.83 (1.14, 1.58, 1.50, 4.12) | not run     |
| 2013.3     | 2013-11-30 | `466a18f` | 153 | 2.11 (1.31, 1.73, 1.90, 4.64) | not run     |
| 2014.1     | 2014-07-25 | `7e29e8e` | 153 | 2.12 (1.31, 1.74, 1.90, 4.64) | not run     |
| 2015.1     | 2015-01-08 | `f51fc8d` | 153 | 1.56 (1.25, 1.34, 1.66, 2.12) | not run     |
| 2015.4     | 2015-07-29 | `9384bce` | 153 | 1.48 (1.16, 1.26, 1.60, 2.06) | not run     |
| 2015-12-28 | 2015-12-28 | `bc11dbf` | 158 | 1.48 (1.14, 1.23, 1.59, 2.16) | 0.28 (006-02) |
| 2017-07-29 | 2017-07-29 | `dbf131a` | 166 | 1.52 (1.15, 1.24, 1.65, 2.26) | 0.29 (006-02) |
| 2017-08-01 | 2017-08-01 | `195cf88` | 271 | 1.56 (1.16, 1.25, 1.74, 2.36) | 0.32 (006-02) |
| 2026-10-19 | 2026-10-19 | `11ea2f6` | 227 | 1.50 (1.10, 1.19, 1.62, 2.37) | 0.30 (006-02) |
| 2026.1     | 2026-10-25 | `a42947c` | 191 | 1.50 (1.10, 1.19, 1.62, 2.37) | 0.29 (notes) |
| 2026.2     | 2026-11-04 | `95bde62` | 129 | 1.51 (1.10, 1.20, 1.65, 2.40) | 0.24 (notes) |
| 2026.3     | 2026-11-06 | `929fa33` | 129 | 1.51 (1.10, 1.20, 1.65, 2.40) | not run     |
| 2026.4c    | 2026-11-09 | `f3af680` | 130 | 1.51 (1.10, 1.20, 1.65, 2.40) | not run     |

MEM and SS: one run of each build today (MEM does not move by more than 1
between runs, 006-02; SS does not move at all). CORE: not measured today; the
figures in brackets are earlier quiet measurements of the same code on F53,
for orientation only: 006-02 (2026-10-19, medians of 6 to 10 runs) and
2026.2's release notes ("Release Props", 2026-11-06, medians of 3). The 2013
and 2014 builds run a port of Props (p16, section 1); the others their own.

1. **The 2026.4 candidate against 2026.3: no change in SS; MEM 130 against
   129**, which is within the range "129 to 130 since handles" that
   `level1.sh`'s limit records (`f648f96`) and below this item's threshold of
   2; CORE not measured. Props does not touch objects: it writes `byte[]`
   values through `Db` (MEM's and SS's keys are Strings made into key
   segments), so format 2 of stored objects (020-07, 020-08) cannot change
   it. The Core changes since 2026.3 are 019-46 (a reader's
   `Cache3.dropIfEmpty`, the read path: `get`, `get4t`, `getmany` should be
   checked when CORE runs), 019-47 (startup only) and 021-04 to 021-06
   (well-formed UTF-8 in strings and keys, outside CORE's timed loops).
2. **MEM from 2013 to 2026.4c: 144 to 130 bytes per KV, the lowest ever since
   2026.2.** It rose to 153 (2013.3), 158 (2015-12-28), 166 (2017-07-29) and
   271 (the 2017 import's node table, 006-02), then fell with 005-08's tree-bin
   fix (191, 2026.1) and handles (129, 2026.2; 009).
3. **SS: 2026.3 and 2026.4c (1.51) write 18 percent less than 2013's node
   stream (1.83) and 29 percent less than 2014.1 (2.12); the KV stream of
   2015.1 (kv2) made the big step** (SS4, single 100-byte KVs: 4.64 to 2.12).
   Since 2015.4 SS has stayed between 1.48 and 1.56.
4. **The port is checked against Frans's own figures**: SS of 2015.1 and 2015.4
   on F53 equals cissi's to the last digit (1.56 (1.25, 1.34, 1.66, 2.12) on
   2015-01-08; 1.48 (1.16, 1.26, 1.60, 2.06) on 2015-07-24 and 28), and p16's
   SS1 and SS2 of 2014.1, 1.31 and 1.74, are the 1.31 and 1.74 that Frans
   measured on the node-stream branch on 2014-11-09 (then numbered SS2 and
   SS1; F1-007 `bergdb/log.md`, 141109 and 150104).
5. **The 2012 era**: no code before 2013-06-06 is in Git; 2013.1 is the first
   release, the result of 2012's work, and the oldest code that runs. 2012's
   figures are of other tests on other machines (section 3).


1. What Props measures
----------------------

`bergdb.dev.props.Props` was created on 2015-01-06 (`35dac3d`, `3e4eedb`) from
three older tools: CorePerf (`kissdb.dev.CorePerf`, 2012 to 2014, whose four
tests and baselines became CORE), MemPerf / `PerfDBMem` (2012) and the
StreamSize tests (`StreamSizeSSX`, 2013 to 2014). Its numbers, as run since
2015 (the workloads in detail are in [plan.md](16-props-across-releases/plan.md)):

* **MEM** (`Mem`): one million KVs (keys `"0"` to `"999999"`, empty values,
  100 per transaction), `testSetup()` with a dummy main stream (no eviction,
  retain forever); the heap in use after `System.gc()`, after minus before,
  per KV. One thread, nothing timed. It depends on the JVM's object layout
  (006-02: JDK 27's compact headers give 8 to 11 bytes less than cissi's Java 7
  and 8), not on the machine.
* **CORE** (`Core`): four tests, each on a new database of 100,000 KVs (4-byte
  keys, empty values): `get` (one thread, random gets, 2 s), `get4t` (four
  threads, 1 s; time per get of all threads together), `getmany` (scans of
  10,000 KVs, 2 s; time per KV), `set` (200,000 single-KV transactions to a
  dummy stream; time per transaction); five rounds in one JVM, the best time
  of each divided by cissi's of July 2013 (1.0, 0.4, 0.2 and 5.0 us), then the
  geometric mean. Printed with two decimals: a step is about 3 percent at
  F53's 0.25 to 0.35. `get4t` is the part that other work on the machine
  disturbs (006-02, section 7).
* **SS** (`SS`, `SS1` to `SS4`): 100 MB of KVs of 1,000 bytes (SS1, SS2) or
  100 bytes (SS3, SS4), 100 KVs per transaction (SS1, SS3) or one (SS2, SS4),
  into a `MemoryStream` with the default builder; stream length over user
  bytes, and the geometric mean. Deterministic: the same in every run and on
  every machine for the same code; it depends on the default startup distance
  (10 MB until 2013-07-07, 20 MB to 2026-10-13, 50 MB since; 006-02, section
  6).

**Props's versions.** From 2015.1 to 2026.4c Props and its four Core tests are
the same code but renames (`CORE` and `MEM` to `Core` and `Mem`, 2015-08-18),
comments, and the builder lines of the tests: `FixedDurationEvictBoss` in the
read tests until the old eviction was removed (2015-08-16, `fb72cde`),
`retainForever()` until 015-87 (2026-11-05, `60f29c7`; forever is the default
since 2013-07-07). Each of these builds runs its own Props. Before 2015 there
is no Props. **p16** ([P16.java.in](16-props-across-releases/P16.java.in)),
made for each API of the time by `run.sh`, runs MEM and SS as ports of
2015-12-28's `Mem` and `SS1` to `SS4` (`Trans.builder().set` until 2013.3,
`db.sync()` until 2014, `NullStream` for `DummyStream`), and CORE from the
code's own four tests (`Get.run`, `GetThreaded.get4t`, `PerfGetMany.standard`,
`Set.normal`), called as CorePerf called them; their sizes, threads, times and
keys are the same from 2013.1 to 2026 (checked by diff), CorePerf's fifth test
`set2` is left out as in Props, and in 2013 the `set` test's database still
had stream writing on, as Props's `set` has. One deviation: p16's SS builder
gets `retainForever()`, the default from 2013-07-07 (`8cbd702`); 2013.1's
default (7 days, with reclaim) fails in its own `GetMany` during SS (an
`ArrayIndexOutOfBoundsException`, `runs/smoke/`).

**Stability.** MEM: within 1 byte per KV between runs (006-02: ranges of 0 to
1 in 10 runs). SS: identical in every run. CORE: 006-02 found ranges of 0.01
to 0.03 on a quiet F53, more for `get4t` with any other work on the machine.

**The builds** (`run.sh build`): 2013.1 to 2017-07-29 from F1-007's
`bergdb-git.bundle`, 2017-08-01 and 2026-10-19 from this repository, all
compiled as 006-02 did (one `javac --release 8` of `git archive`; 2013.1
without `src-icu`, whose ICU jar is not in Git and which nothing else needs).
The rebuilt 2015-12-28, 2017-07-29, 2017-08-01 and 2026-10-19 have the same
class hashes as 006-02's builds. 2026.1 to 2026.3 are the release jars,
checked against their `SHA256SUMS`; 2026.4c is `f3af680` (main at 08:22),
built by its own `java/build.sh`, as the release jars were. Every build runs
on JDK 27.


2. MEM and SS, build by build
-----------------------------

From [summary.txt](16-props-across-releases/summary.txt); one run of each,
2026-11-09, 08:33 to 08:36, on a busy F53 (MEM and SS do not depend on it).
Ratios to 2026.3; cissi's figures for the same code from Frans's logs (Java
7 and 8, 12-byte object headers; F1-007 `bergdb/log.md`, `Props.java`,
`Mem.java`, `SS.java`).

| Build      | MEM | MEM / 2026.3 | cissi MEM          | SS   | SS / 2026.3 | cissi SS         |
|------------|-----|--------------|--------------------|------|-------------|------------------|
| 2013.1     | 144 | 1.12         |                    | 1.83 | 1.21        |                  |
| 2013-07-05 | 144 | 1.12         |                    | 1.83 | 1.21        |                  |
| 2013.3     | 153 | 1.19         |                    | 2.11 | 1.40        |                  |
| 2014.1     | 153 | 1.19         |                    | 2.12 | 1.40        | 1.31, 1.74 (SS1, SS2) |
| 2015.1     | 153 | 1.19         | 161 (2015-01-08)   | 1.56 | 1.03        | 1.56, the same   |
| 2015.4     | 153 | 1.19         | 161 (2015-07-28)   | 1.48 | 0.98        | 1.48, the same   |
| 2015-12-28 | 158 | 1.22         | 169                | 1.48 | 0.98        | 1.47             |
| 2017-07-29 | 166 | 1.29         | 169                | 1.52 | 1.01        | 1.52             |
| 2017-08-01 | 271 | 2.10         |                    | 1.56 | 1.03        |                  |
| 2026-10-19 | 227 | 1.76         |                    | 1.50 | 0.99        |                  |
| 2026.1     | 191 | 1.48         |                    | 1.50 | 0.99        |                  |
| 2026.2     | 129 | 1.00         |                    | 1.51 | 1.00        |                  |
| 2026.3     | 129 | 1.00         |                    | 1.51 | 1.00        |                  |
| 2026.4c    | 130 | 1.01         |                    | 1.51 | 1.00        |                  |

What moves MEM, from the history:

* 2013-07-05 to 2013.3, +9: probably the "forward-pointers" branch, taken in
  October 2013 (`cd48930`, 2013-10-11: "Let's use this branch! CorePerf fast
  enough (0.90)"). Not analysed further.
* 2015.4 to 2015-12-28, +5: Cache2's weak references to key nodes (August
  2015; Frans in `Mem.java`: "150818, Mem:185 ... Now using more advanced
  caching (Cache2 class)", 169 on cissi by 2015-12-28). 2015-12-28 to 2017-07-29, +8:
  `ValueNode.offsetFromTrans` (2016-03-30, `3c99e78`; 006-02, section 10).
* 2017-07-29 to 2017-08-01, +105: Cache3, the node table, its `CacheEntry`,
  the ids of value nodes and the 256 maps whose bins became trees (006-02,
  sections 4 and 10). To 2026-10-19, -44: D1's in-place splits (006-02).
* 2026-10-19 to 2026.1, -36: 005-08's fix of the tree bins, `Cache3.mapIndex`
  by Fibonacci hashing (MEM 191, as 006-02's experiment predicted). 2026.1 to 2026.2, -62: handles (009; the
  2026.2 notes: "MEM, heap bytes per KV: 129 to 130 since handles, against
  191"). 2026.2, 2026.3 and 2026.4c: 129 to 130.

What moves SS:

* 2013.1 and 2013-07-05 are the same (1.83); their default startup distance is
  10 MB, from 2013.2 (2013-07-07) on 20 MB.
* 2013-07-05 to 2013.3, 1.83 to 2.11 (SS4 4.12 to 4.64): the 20 MB distance
  and the code of the autumn of 2013 (forward pointers); not separated.
* 2014.1 to 2015.1, 2.12 to 1.56: the KV stream (branch kv2, 2014-11; Frans
  2014-11-09: "Go for kv2 branch! Faster and more compact stream!"); SS4 from
  4.64 to 2.12. 2015.1 to 2015.4, 1.56 to 1.48: between 2015-04-22 (1.56)
  and 2015-05-15 (1.48) by Frans's notes in `SS.java`; not traced to a
  commit.
* 2015-12-28 to 2017-08-01, 1.48 to 1.56: ids of got-dirty nodes in stored
  transactions (`bc11dbf`), the value nodes' ids (`290e766`, +0.08 on SS3 and
  SS4; 006-02). 2017-08-01 to 2026-10-19, to 1.50: the 50 MB startup distance
  (2026-10-13; the whole difference, 006-02, section 6). 2026.1 to 2026.2,
  1.50 to 1.51 (SS3 1.62 to 1.65, SS4 2.37 to 2.40): 005-49's take (2026.2's
  notes: "SS depends on the startup distance and the take, which 2026.2
  changed"; `level1.sh`'s SS limits raised after 007-07, `f6fc56b`).


3. CORE, and the comparison with 2012 and 2013
----------------------------------------------

**Not measured today** (section 4). What is known:

* **On F53, earlier quiet runs** of builds that this item also has: 2015-12-28
  0.28 (0.29, 0.325, 0.27, 0.24), 2017-07-29 0.29, 2017-08-01 0.32,
  2026-10-19 0.30 (006-02, medians of 6 to 10 runs); 2026.1 0.29 and 2026.2
  0.24 (0.26, 0.17, 0.25, 0.32) (2026.2's notes, medians of 3, 2026-11-06:
  `get4t` takes about half the time since handles).
* **One unquiet run** of the p16 driver, a smoke test of 2013.1 at 08:36 with
  a 1-minute load of about 5 (another session's gate had just ended): CORE
  0.37 (0.29, 0.49, 0.25, 0.52). Not a measurement; it shows that the 2013
  code runs the four tests on F53 (`runs/smoke/`).
* **cissi, Frans's laptop of 2013** (Intel i7, 2.1 GHz), CorePerf and Props
  from his logs, the four tests only (CORE recomputed from the raw times
  where the log has five tests):

| Date       | Code                                  | CORE | get, get4t, getmany, set |
|------------|---------------------------------------|------|--------------------------|
| 2013-06-29 | KissDB, 3 weeks after 2013.1          | 0.89 | 0.80, 1.02, 0.84, 0.89   |
| 2013-07-05 | `550ce4e`, the baseline's own run     | 0.89 | 0.87, 0.98, 0.84, 0.87   |
| 2013-09-27 | 2013.2.130818 and later               | 0.91 | 0.81, 0.97, 1.02, 0.87   |
| 2014-07-15 | about 2014.1                          | 0.89 | 0.78, 1.03, 0.86, 0.92   |
| 2014-11-09 | kv2 branch (main branch: 0.89)        | 0.75 | 0.74, 0.96, 0.84, 0.54   |
| 2015-01-08 | 2015.1                                | 0.79 | 0.81, 1.00, 0.86, 0.54   |
| 2015-07-28 | 2015.4                                | 0.78 | 0.77, 0.99, 0.85, 0.58   |
| 2015-12-28 | `bc11dbf`                             | 0.81 | 0.82, 0.99, 0.87, 0.60   |
| 2017-07-29 | `dbf131a`                             | 0.76 | 0.76, 0.94, 0.77, 0.61   |

  So **1.00 is not quite cissi on the code of 2013**: the baseline times were
  rounded up by hand ("Resulting profile (manual edit)", `Core.java`); cissi
  gave 0.89 on the very code of 2013-07-05. The kv2 stream halved `set`
  (0.92 to 0.54) at the end of 2014; the reads hardly moved from 2013 to 2017.
* **The 2012 era**: Rose, a 32-bit netbook, and linda, a Linode server, ran
  `PerfDBGet` and `PerfDBSet` with other sizes (50,000 KVs) and setups (2012
  log and `doc/2012/`): a get 3.5 to 6.4 us on Rose, 1.6 us on linda; a set 10
  to 30 us on Rose, 3.5 us on linda; memory "around 100 bytes overhead per
  KV" (`PerfDBMem`, 100,000 KVs, a 32-bit JVM); stream overhead "40 bytes per
  KV, 460 bytes per transaction" (2012-05-18). Not comparable with Props. The
  one link: on 2013-06-06, the day of 2013.1, CorePerf on Rose gave 6.33,
  4.22, 1.37 and 37.0 us, CORE 7.6 in cissi's units; cissi ran the same tests
  about 7 times faster three weeks later (Frans, 2013-06-29: "0.13! 7 times
  faster than when run on Rose").

**When CORE has run**, the F53 figure of the 2013-07-05 build over cissi's 0.89
is the factor of the machine and the JVM for the baseline's own code, and every
build's CORE on F53 can be read against it and against cissi's column above.


4. What is left: CORE on a quiet F53
------------------------------------

The 14 builds are in `/Users/f/fl/bench/006-16/builds/` (the work directory's
`run.sh` and `P16.java.in` are the same as this item's). One command runs the
block of the plan, six rounds of a full Props run of each build, round-robin
(forward in odd rounds, backward in even ones), each run only after quiet
checks (the 1-minute load under 1.5, no other JVM but the editor's language
server, no other session's `QUIET-BLOCK`, the gate's lock free, no
before-commit, night, performance, level or lake runner; 4 checks 30 s apart
before the block, 2 checks 10 s apart before each run), with its own marker
`/Users/f/fl/bench/006-16/QUIET-BLOCK` while it runs; about 1.5 to 2 hours:

    cd /Users/f/fl/bench/006-16
    DEADLINE=2400 sh run.sh rounds main 6 > block-main.log 2>&1

`DEADLINE` (HHMM, default 1300) stops the block before a run that would start
at or after that time of day; it compares HHMM, so give `DEADLINE=0700` to a
block started after midnight, and `DEADLINE=2400` (none) to one started
before. The session that starts it must stay idle until it ends (006-02: its
own tool calls disturb `get4t`). Then:

    python3 -I summary.py > summary.txt
    I=~/fl/repos/bergdb/items/006-2026-q4/16-props-across-releases
    cp -R runs/* $I/runs/ && cp summary.txt $I/

`summary.py` makes the CORE table from the timed runs only (median, range,
number of runs, the ratio to 2026.3). What counts as a difference, from the
plan: two steps of the medians, or one step with ranges that do not overlap;
for `get4t` only ranges that do not overlap.


5. A yardstick going forward
----------------------------

* **Props is a good long-term yardstick back to 2013** for what it covers:
  MEM and SS are exact and machine-free (SS of 2015 matches cissi's to the
  digit; MEM differs from cissi's by the object header only), and with p16
  every release from 2013.1 runs it. CORE is tied to cissi's 2013 times, so
  it is comparable across code on one machine, and across machines only
  through a build measured on both (2015-12-28 and 2017-07-29 by 006-02; the
  2013-07-05 build when CORE runs).
* **What it misses**: everything that is not small and in memory. A million
  KVs at most, 100,000 in CORE; `set` writes to a dummy stream (no I/O, no
  force); nothing is evicted or reclaimed; no startup, no restart; no large
  values; no Pub API or user indexes; get4t is the only concurrency, four
  readers and no writer; MEM counts the heap after the load, not the peak.
  These are what 2026's harness covers (`java/stress/performance.sh`, the
  ScaleBench and bounded-startup measurements of 004, 007 and 016).
* **Recommendation**: keep Props as it is (its value is the unchanged
  workload; `level1.sh` already checks MEM and SS), keep p16 and this item's
  `run.sh` as the way to run it on a list of builds, and add a build to
  `run.sh`'s list at each release, with one round-robin block of CORE on a
  quiet F53 per release (a night step). Do not add tests to Props itself; a
  large-database, eviction or startup property belongs in the 2026 harness,
  where a release's notes already report it.


6. Files
--------

In [16-props-across-releases/](16-props-across-releases/):

* [plan.md](16-props-across-releases/plan.md): the plan, written before the
  timed runs.
* [run.sh](16-props-across-releases/run.sh): the builds, the runs, the quiet
  checks and the block (its header); run it from the work directory, where
  the builds are.
* [P16.java.in](16-props-across-releases/P16.java.in): Props for the code of
  2013 and 2014 (p16).
* [summary.py](16-props-across-releases/summary.py) and
  [summary.txt](16-props-across-releases/summary.txt): the tables.
* `runs/`: one file per run (the version, commit, class hash, which Props, the
  quiet check, the output), `machine.txt`, `failed/` (four MEM runs that
  named the wrong class on a case-insensitive disk, repeated) and `smoke/`
  (the first SS of 2013.1, with its default reclaim, and the unquiet p16 run).


Log
---

2026-11-09, 08:22 to 09:05. Created at Frans's request, by an AI agent for
the day's coordinator. Studied Props and its history (the original Git
history, Frans's logs of 2012 to 2017), built the 14 versions (08:30 to
08:33), wrote p16 and the plan, ran MEM and SS of every build (08:33 to
08:36). The timed CORE block waited for a quiet F53 from 08:37 (another
session's commit gate and other work kept the load over 1.5) and was stopped
at the coordinator's request at about 09:00: the 2026.4 release runs need F53
today. A plain `kill` did not stop it, as its trap on TERM only removed the
marker; it was killed with `kill -9`, and the trap now exits too. CORE is left
for a quiet night (section 4). Status open.
