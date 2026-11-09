# 020-12 Format 2 measured: 020-08's step 4

Created 2026-11-09 by Frans Lundberg. Status: done. The measurements of
020-08, section 7, made on a quiet machine in the morning of night 006-15:
format 2 of stored objects and the rest of 2026.4's Pub layer at `7231771`
against format 1 at `ae68938` (ObjectBench, M1 to M8), and the Core at
`7231771` against release 2026.3 (`performance.sh`'s quick suite); what
the numbers mean, the three figures that the night's runs left open, and
the two that are worse.


## 1. In short

* **Objects are smaller and faster.** A `Payment` is 36 bytes against 71.
  Against format 1, the writer takes 0.29 to 0.66 of the time (M1), the
  read of bytes with its copy and full check 0.16 to 0.74 (M2), a field's
  lookup 0.13 to 0.44 (M3), a get into `Payment` 0.70 and as `DbObject`
  0.84 (M4), a put into an indexed directory 0.89 (M5), and a build over
  1,000,000 `Payment`s 0.46: 226,000 objects a second against 105,000
  (M6).
* **The Core did not move.** `performance.sh ab`, quick suite, release
  2026.3 against `7231771`: NO ALERTS; every throughput within 5 %, the
  three restarts' startup 2.3 to 4.5 % slower (17 to 28 ms, section 4).
* **Two figures are worse by more than 10 %** (section 5):
  * M4, a get as `byte[]`: 624 ns against 464, **1.34**, but not the
    get's code: alone in a fresh JVM, on the same 1,000,000 `Payment`s,
    the get as `byte[]` takes 471 ns against 504 (0.93), and on equal
    `byte[]` values 1.00 and 0.98. The 1.34 comes from where ObjectBench
    measures it, after M1 to M3 and two other get loops in the same JVM.
    Not a fault.
  * M8, a `w()` of one `String` put at an object key: 2.6 µs against
    2.3, **1.13**: the cost of 020-10, section 5.1's rule (I1), by design,
    about 0.3 µs a `w()`; a `w()` of 100 puts 0.98, keys with `.txt` 1.00.
    A known cost, not a fault; for Frans to accept or to have cut.
* **M1's `Blob`** is settled: 0.64, no regression.


## 2. How

* **Machine**: F53, Apple M1 Pro, 10 cores, 32 GB, macOS 27.0.1. **JVM**:
  OpenJDK 27 (Homebrew), G1, `-Xms8g -Xmx8g`.
* **Builds**:
  * format 1: `ae68938` (020-10's P1, the last code before 020-08's step
    2), built outside the repository in
    `/Users/f/fl/bench/006-15/format1-build/` (020-08, section 8.6);
  * 2026.4: `7231771`, `main` final for the night, the preserved build
    `cand-7231771` (`performance.sh build`, jar `6a634771`);
  * release 2026.3: the tag `release-2026.3`, `929fa33`, the preserved
    build `rel-2026.3` (`performance.sh build` in a clone at the tag,
    `/Users/f/fl/bench/006-15/rel-2026.3/`, jar `cafb5559`).
* **Quiet**: before each run, four checks 15 s apart: the 1-minute load
  under 1.5, no other JVM in `ps`, no other session's QUIET-BLOCK marker;
  markers of its own during the runs; the night's coordinator kept every
  other agent idle. The load around ObjectBench's JVMs (each JVM's own
  included after it): 1.08 to 1.90; `performance.sh`: CPU 98.4 % idle
  before its runs.
* **ObjectBench** (020-08, section 8.6), `full`: 5 JVMs a build in ABBA
  order, the median of each figure over its build's JVMs, the range their
  minimum and maximum; 03:43 to 03:51.
* **`performance.sh ab`** with `SUITE=quick` (`performance-quick.suite`:
  `read-1k`, `w-uni-1k-inf`, `w-uni-1k-fin`, `r-1k-fin`), 3 runs a
  scenario and build alternating, the harness compiled from `7231771`
  against each jar; 03:52 to 04:05. Its reference is release 2026.3, as
  the coordinator asked, not section 7's `pre-f2`: it spans everything
  since the release, the night's Core fixes included.
* **A fault of the tool**: `java/stress/objectbench.sh` compiles
  ObjectBench once, with `build.sh` against this tree, and runs that class
  on both jars; since B3 (`48378fe`) it imports `bergdb.pub.DbObject`,
  which format 1's jar does not have (`bergdb.pubimp.DbObject`), so the
  script no longer runs the reference. The quiet run compiled the same
  source twice, the reference's copy with `import
  bergdb.pubimp.DbObject;` (the only difference), each against its jar,
  and ran them as the script does. Fixed after this step in 621ee0e:
  the script compiles ObjectBench for each build.
* **A probe of M4** (section 5), after the two runs: `ProbeM4`, a get as
  `byte[]` alone; 6 JVMs a build in ABBA order; 04:19 to 04:23.
* **Kept**: the scripts, each JVM's output, the comparison and the probe
  in `/Users/f/fl/bench/006-15/020-12/` (`objectbench/`, `probe-m4/`);
  the comparison's sessions in
  `/Users/f/fl/bench/006-15/clone-step4q/java/build/perf/runs/`.


## 3. ObjectBench

M1, the writer, and M2, the read of bytes, in ns an object; M7, the
object's bytes. f1 is format 1 (`ae68938`), f2 format 2 (`7231771`).

| Sample      | M1 f1    | M1 f2    | Ratio | M2 f1   | M2 f2   | Ratio | M7 f1   | M7 f2   |
|-------------|----------|----------|-------|---------|---------|-------|---------|---------|
| `Person`    |    325.0 |    145.2 |  0.45 |   142.2 |    24.8 |  0.17 |      30 |      16 |
| `Payment`   |    702.2 |    321.6 |  0.46 |   197.9 |    51.8 |  0.26 |      71 |      36 |
| `Foobar`    |  1,269.1 |    841.7 |  0.66 |   343.7 |   133.8 |  0.39 |     243 |     182 |
| `Dialog`    |  1,218.6 |    351.2 |  0.29 |   368.2 |    61.7 |  0.17 |     102 |      37 |
| `IndexInfo` |  1,323.6 |    573.1 |  0.43 |   562.2 |    91.2 |  0.16 |     146 |      96 |
| `Customer`  |  2,473.7 |  1,322.2 |  0.53 |   612.6 |   237.2 |  0.39 |     349 |     226 |
| `Order`     |  7,449.1 |  2,975.0 |  0.40 | 1,564.8 |   610.8 |  0.39 |     917 |     493 |
| `Blob`      | 17,505.3 | 11,210.7 |  0.64 | 8,784.0 | 6,465.0 |  0.74 | 100,089 | 100,072 |

M3, a lookup on a `DbObject` made once, hot, and M4, a get end to end
(1,000,000 `Payment`s in a database in memory; each round 4,096 random
keys, a third of 1,000,000 gets each way, one thread), in ns:

| Figure                  | Format 1                  | 2026.4              | Ratio |
|-------------------------|---------------------------|---------------------|-------|
| M3 `Payment.amount`     | 91.4 (48.4–106.8)         | 24.1 (23.9–24.3)    |  0.26 |
| M3 `Payment.from`       | 197.4 (79.9–198.8)        | 24.9 (24.9–25.7)    |  0.13 |
| M3 `Customer.zip`       | 91.2 (63.2–142.9)         | 39.7 (39.6–39.8)    |  0.44 |
| M3 `Dialog.personB.id`  | 233.8 (232.9–342.6)       | 63.7 (63.0–64.0)    |  0.27 |
| M4 get into `Payment`   | 1,211.4 (1,199.8–1,226.1) | 844.0 (698.3–855.7) |  0.70 |
| M4 get as `DbObject`    | 910.3 (904.2–931.9)       | 760.2 (615.4–771.3) |  0.84 |
| M4 get as `byte[]`      | 463.9 (463.5–470.3)       | 623.8 (499.9–634.1) |  1.34 |

M5, puts of `Payment`, one a transaction, into a directory with a string
index on `from` and into one without; M6, a string index built over
1,000,000 `Payment`s; M7, the stream's bytes a `Payment` after 1,000,000;
M8, `w()`s of `String` puts at keys without a suffix (object keys) and
with `.txt`, one put and 100 puts a `w()`:

| Figure                           | Format 1                  | 2026.4                    | Ratio |
|----------------------------------|---------------------------|---------------------------|-------|
| M5 put, indexed, µs              | 7.3 (7.0–7.8)             | 6.5 (6.3–6.6)             |  0.89 |
| M5 put, not indexed, µs          | 3.0 (2.9–3.1)             | 2.3 (2.3–2.3)             |  0.77 |
| M6 build, s                      | 9.6 (9.4–9.8)             | 4.4 (4.3–4.5)             |  0.46 |
| M6 build, objects a second       | 104,593 (102,266–106,810) | 226,196 (222,267–231,257) |  2.16 |
| M7 stream bytes a `Payment`      | 133.3                     | 99.1                      |  0.74 |
| M8 1 put a `w()`, object key, µs | 2.3 (2.3–2.5)             | 2.6 (2.6–2.8)             |  1.13 |
| M8 1 put a `w()`, `.txt` key, µs | 3.0 (2.9–3.1)             | 3.0 (2.9–3.0)             |  1.00 |
| M8 100 puts, object keys, µs     | 240.5 (235.6–242.5)       | 234.8 (233.7–235.7)       |  0.98 |
| M8 100 puts, `.txt` keys, µs     | 253.3 (247.4–264.3)       | 259.6 (257.7–262.6)       |  1.02 |


## 4. The Core: `performance.sh ab`, quick suite

Release 2026.3 (`929fa33`) against `7231771`, medians of 3 runs (the CV
of each under 3 % but for the maximum below):

| Scenario       | Metric                     | 2026.3    | 7231771   | Change |
|----------------|----------------------------|-----------|-----------|--------|
| `read-1k`      | `get_latest.ops_per_s`     | 1,264,180 | 1,266,780 | +0.2 % |
| `read-1k`      | `get_historical.ops_per_s` | 1,217,550 | 1,237,860 | +1.7 % |
| `read-1k`      | `get_latest_mt4.ops_per_s` | 4,270,370 | 4,332,470 | +1.5 % |
| `read-1k`      | `get_longkey.ops_per_s`    | 863,296   | 904,232   | +4.7 % |
| `read-1k`      | `scan_fwd.kvs_per_s`       | 3,750,230 | 3,886,870 | +3.6 % |
| `read-1k`      | `scan_back.kvs_per_s`      | 3,987,270 | 4,076,150 | +2.2 % |
| `w-uni-1k-inf` | `commits_per_s`            | 99,849    | 99,779    | −0.1 % |
| `w-uni-1k-inf` | `restart.startup_sec`      | 0.649     | 0.677     | +4.3 % |
| `w-uni-1k-inf` | `commit.append.max_us`     | 33,465    | 152,802   | +357 % |
| `w-uni-1k-fin` | `commits_per_s`            | 64,603    | 64,282    | −0.5 % |
| `w-uni-1k-fin` | `restart.startup_sec`      | 0.642     | 0.670     | +4.5 % |
| `r-1k-fin`     | `mix.commits_per_s`        | 52,532    | 52,230    | −0.6 % |
| `r-1k-fin`     | `mix.gets_per_s`           | 2,391,980 | 2,412,610 | +0.9 % |
| `r-1k-fin`     | `startup.sec`              | 0.734     | 0.751     | +2.3 % |

The comparison's verdict: NO ALERTS (exit code 0); 128 more metrics with
nothing to report.

* **The maximum append** (`EXPLAIN` in the comparison, a maximum of 3
  runs, CV 92 % and 49 %) is a G1 pause, not BergDB's code: each run's
  slowest append is one of its young collections' pauses, the one that
  fell inside a timed append (`write.gc.log`; 2026.3: 51.2 and 33.5 ms
  against pauses of 51.1 and 33.2 ms, and 0.09 ms in the run where none
  fell inside one; `7231771`: 167.3, 55.2 and 152.8 ms against 167.1,
  55.1 and 152.7 ms). Both builds make the same three collections a run,
  of the same pauses (29 to 33, 51 to 57 and 153 to 175 ms); which one
  an append meets is chance. The append's p50 (7.6 µs) and p99.9 (27.0 to
  27.5 µs) are the same in both.
* **The restarts' startup**, 17 to 28 ms slower in all three (CV 0.1 to
  1.1 %), under the suite's 5 % and far from a fault; a likely cause, not
  measured: 019-47's fix (`c126d7d`), which makes the start's admission
  pass over every resident key node's pointers.


## 5. The open figures, settled

The night's runs, not quiet (020-08, section 8.6), left three figures
open. The quiet run:

* **M1's `Blob`**: 1.35 in the night's quick run, 0.45 in its full run;
  quiet, 0.64 (11,211 ns against 17,505, the ranges apart). Not a
  regression: the 1.35 was the busy machine.
* **M8, I1's cost**: 1.20 and 1.09 in the night's runs; quiet, **1.13**:
  2.6 µs against 2.3, the ranges apart (2.6–2.8 against 2.3–2.5). A
  regression of 13 % on a common path, a `w()` of one put at a key
  without a suffix, so above the line. It is the cost of 020-10, section
  5.1's rule, by design: since I1 every put or delete at an object key,
  whatever its value and whether its directory has an index or not, fixes
  the read time first, puts the index set's hash into the read set, reads
  the index set under the manager's lock and goes through `executeRw`;
  that rule fixed 015-28, 015-43 and 015-46. It is about 0.3 µs a `w()`:
  keys with `.txt`, which skip it, are unchanged (1.00), and 100 puts a
  `w()` hide it (0.98 and 1.02). A put of an object pays it too and is
  still faster than format 1's (M5, not indexed: 0.77). Not a fault,
  decided here under Frans's delegation of 2026-11-08, 22:17: a known
  cost of a correctness rule, for 020-11 to list, and for Frans to accept
  or to have cut; a cut must keep 020-10, section 5.2's invariant, which
  the lock gives.
* **M4's get as `byte[]`**: 1.46 in the night's full run, 1.01 in its
  quick one; quiet, **1.34**: 624 ns against 464, the ranges apart
  (499.9–634.1 against 463.5–470.3). In ObjectBench, but not in the get:
  the code of a get as `byte[]` is the same in both builds but for a few
  tests of the class (`ConnectionImp.get`, `getInternal`, the Core's
  `getOne` and `KvToObjectImp.createObject`, which returns the stored
  array), and the tree's shape does not depend on the values (30
  pointers a node). A probe, `ProbeM4`, measured that get alone, as M4
  does (a database in memory, 1,000,000 keys `/g/p0` and on, 1,000 puts
  a transaction, rounds of 4,096 random keys and 333,333 gets, the median
  of 11 rounds), in a fresh JVM for each build, 6 JVMs a build in ABBA
  order, three databases one after the other in each: the `Payment`s of
  M4 (`Connection.put` of the object: 71 bytes in format 1, 35 at the
  key read back in format 2), then `byte[]` values of 36 and of 71
  bytes. Medians of the 6 JVMs, in ns (load 1.33 to 2.08, each JVM's own
  included after it):

  | Values               | Format 1            | 2026.4              | Ratio |
  |----------------------|---------------------|---------------------|-------|
  | `Payment`s, first    | 503.8 (501.5–509.2) | 470.8 (466.0–474.2) |  0.93 |
  | 36-byte `byte[]`s    | 571.1 (567.8–574.4) | 570.1 (467.6–578.2) |  1.00 |
  | 71-byte `byte[]`s    | 575.5 (461.4–579.2) | 564.3 (556.4–575.0) |  0.98 |

  So the get as `byte[]` is not slower in 2026.4, and a little faster on
  M4's own data. What moves it is the JVM's state when the loop runs: in
  format 1's build, values of 71 bytes took 504 ns in the JVM's first
  database (the `Payment`s) and 576 ns in its third (the `byte[]`s); in
  ObjectBench the loop runs after M1 to M3 and after M4's gets into
  `Payment` and as `DbObject`, whose code differs between the builds, and
  the candidate's five JVMs spread from 500 to 634 ns, all three M4
  figures together (its fastest JVM: 698, 615 and 500 ns). Not a fault of
  BergDB; a weakness of the figure, which a later ObjectBench could
  measure in a JVM of its own.


## 6. What it means for the plan

020-08, section 7, asked three questions of the numbers:

* **M2 and the full check at every read** (020-07, section 7.4's lookups
  on unchecked bytes, its Q2, and a view without a copy, 020-08, section
  4.3): the copy and the full check take 25 to 611 ns for the samples up
  to 500 bytes, 52 ns for a `Payment`, 6 % of a get into `Payment` (844
  ns), and 0.16 to 0.39 of format 1's parse (0.74 for the 100 KB
  `Blob`). Not worth unchecked lookups or a view without a copy for
  2026.4.
* **M5**: a put into an indexed directory 0.89 of format 1's, the
  entries made from checked bytes. No change.
* **M1 and the writer's way 2** (020-08, section 4.4): the writer takes
  0.29 to 0.66 of format 1's time. Way 1 stays.


## 7. Log

2026-11-09. Measured and written in night 006-15 by the coordinator's
agent C, at the coordinator's request, in a clone at `7231771`: the
quiet runs 03:43 to 04:05 and the probe of M4 04:19 to 04:23; 020-08's
step 4 done, and 020-08 done. Nothing in `java/` changed.
