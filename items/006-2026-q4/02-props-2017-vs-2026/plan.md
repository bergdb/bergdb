006-02. Plan: Props on the 2017 and the 2026 code, on F53
=========================================================

By Claude (Opus 5.5, Claude Code) for Frans Lundberg, 2026-10-19, at 13:35,
before the measured runs. Frans's request: run the 2013 to 2017 Props suite on
the latest code and on the 2017 version, on F53, with the installed JVM only;
see what the code changed and what the new hardware changed; compare with
"Typical output (2015-12-28)"; work unattended.


What Props measures
-------------------

`bergdb.dev.props.Props` (2014 to 2017) prints three numbers:

* **MEM**: heap bytes per KV after one million small KVs (keys `"0"` to
  `"999999"`, empty values, 100 per transaction, a `DummyStream`). Lower is
  better.
* **CORE**: the speed of the Core layer: four tests (`get`: single-thread
  gets, 100k KVs; `get4t`: four threads; `getmany`: scans, per KV; `set`:
  single-KV transactions), each run 5 times in one JVM, the best time of each
  divided by a fixed baseline measured on cissi in July 2013 (1.0, 0.4, 0.2 and
  5.0 us). CORE is the geometric mean of the four ratios. Lower is better; 1.00
  is cissi in July 2013.
* **SS**: stream bytes per user byte, the geometric mean of four scenarios
  (1,000-byte or 100-byte KVs, 100 or 1 KV per transaction, 100 MB of data
  each, a `MemoryStream`). It does not depend on time, so it should not
  depend on the machine or the JVM. Lower is better.

The benchmark code (the `props` package and the four test classes) is the
same in all the versions below, except for renames and comments.


The versions
------------

| Name | Commit | What |
|---|---|---|
| 2015-12-28 | `bc11dbf` (original history, F1-007's `bergdb-git.bundle`) | The commit that recorded "Typical output (2015-12-28)" in `Props.java` |
| 2017-07-29 | `dbf131a` (same) | The code of the last Props run on cissi, 2017-07-29 (F1-007 `bergdb/log.md`) |
| 2017-08-01 | `195cf88` (this repository; identical to the original `49aa48d`, checked) | **The 2017 version**: the import that the 2026 work started from |
| 2026-10-19 | `11ea2f6` (this repository, HEAD; production source as at `ed60789`) | **The 2026 code** |

The two older ones are added because a pilot (below) showed that the 2017
import is not the code that was measured on cissi: two days of an unfinished
cache rewrite (Cache3, ids on value nodes, NodeCollection) lie between the
last cissi run and the import. Running the code that cissi ran gives a
comparison of the machines with the same code.

All four are compiled by the installed javac 27 with the flags of
`java/build.sh` (`--release 8`), from `git archive` of the commit, into
`java/build/props-006-02/` (ignored by Git).


The machine
-----------

F53: MacBookPro18,3, Apple M1 Pro (8 performance and 2 efficiency cores),
32 GB, macOS 27.0.1, on the charger. OpenJDK 27 (Homebrew), default flags: G1,
8 GB maximum heap, compressed oops, compact object headers on (a JDK 27
default). No `-ea`, as Props was run in 2015 (`j bergdb.dev.props.Props`).
Cissi, for the old numbers: a laptop from 2013, Intel i7 at 2.1 GHz, 8 GB,
Ubuntu, HotSpot 1.7.0_76 (2015-12-28) and OpenJDK 1.8.0_131 (2017-07-29).
The JVM differs with the machine; Frans accepted that limitation: hardware
and JVM are measured together.


The pilot (done before this plan)
---------------------------------

One run of each version, 13:23 to 13:31: every version builds and runs on JDK
27, a Props run takes 40 to 50 seconds, and the numbers raise the questions
the plan answers (the 2017 import has a larger MEM and a slower `set` than the
code before it; SS of the 2015 code is within 1 percent of cissi's, not
equal).


The runs
--------

Every run is a fresh JVM. Before each, `run.sh` waits for at least 90 percent
idle CPU and records it. Ten seconds between runs.

1. **Main, 2017 against 2026.** `run.sh ab main 5 2017-08-01 2026-10-19`: five
   ABBA blocks, ten Props runs of each version, default flags.
2. **Cissi's code.** `run.sh ab cissi 3 2015-12-28 2017-07-29`: six runs of
   each, default flags. Compared with cissi's numbers for the same code: the
   effect of the machine and the JVM together.
3. **The old JVM defaults.** Java 7 and 8 used the parallel collector and
   12-byte object headers; JDK 27 uses G1 and 8-byte headers. Two runs of each
   version with `-XX:+UseParallelGC`, and two with `-XX:+UseParallelGC
   -XX:-UseCompactObjectHeaders`. This shows how much of the change from cissi
   these two defaults explain; the JIT and the rest of the JVM still differ.
4. **The startup distance.** The default startup distance was 20 MB in 2017
   and is 50 MB since 2026-10-13 (`docs/log.md`); it changes what is written to
   the stream. `Probe006.java` (this directory) repeats MEM, SS and Core's
   `set` with a chosen startup distance. Runs: `ss` at 20 and 50 MB (one each,
   SS is deterministic or nearly), `mem` and `set` at 20 and 50 MB (two each),
   for 2017-08-01 and 2026-10-19. This separates the change of the default
   from the change of the code.
5. If a difference between 2017 and 2026 is large and not explained by 3 and
   4, a short look at the code that causes it, with a probe only if cheap.


Analysis
--------

* Per version and set of runs: the median, minimum and maximum of each number
  (CORE, its four parts, MEM, SS and its four parts), `summary.py`.
* 2026 against 2017: the ratio of the medians, and whether the ranges overlap.
  With ten runs a side, a difference of a few percent in a part that varies
  less than that is real; the Props parts vary more than that (the 2013 log
  says get4t and getmany can vary by a factor of 3 on a busy machine), so the
  spread decides.
* F53 against cissi: the median of the same code on F53 over cissi's single
  number (cissi's spread is not known; its log shows CORE between 0.75 and
  0.82 on similar code).
* SS: its spread over runs; equal to cissi's for the same code or not.


Deliverables
------------

* `runs/`: one file per run (machine state, command, output), and
  `machine.txt`.
* `summary.txt`: the output of `summary.py`.
* The report, [../02-props-2017-vs-2026.md](../02-props-2017-vs-2026.md).
* The item's readme: the table, the files, the log.

Nothing in `java/`, `lean/` or `docs/` changes; nothing is committed.
