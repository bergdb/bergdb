012-15. Task: speed, memory and size against Java
=================================================

Created 2026-10-27 by Claude (Opus 5.5, Claude Code), with 012-01, for
Frans Lundberg. **Status: done 2026-10-29 04:58 (started 03:18)**, in
the clone `/Users/f/fl/bench/012/15-perf`, for the conductor to copy in;
approved with 012-01 by Frans's go (012-01, 9.1).
Phase E (012-01, section 8). Effort: high. After: 012-13.


# 1. The goal

Numbers, not targets (012-01, section 1, item 8): how fast and how large
the C clone is against Java on F53, measured the same way, for 012-16's
report and for the decision on what comes next.

Done when this file has, with the method, the commits, the scripts and
the summary tables (raw output stays out of the repository, 013-01,
section 4):

1. **Writes**: transactions a second for single puts and for batches,
   without and with `sync`, for 1M and 10M keys; bytes appended per put
   (equal by construction, so a check).
2. **Reads**: `getOne` a second, latest and historical, from memory and
   with a small budget; `getMany` keys a second.
3. **Startup**: the time to open a database of 10M keys at startup
   distances of 50 and 200 MB, warm (in the OS cache), as 007-05 measures
   Java's.
4. **Memory**: C's bytes per key (resident set and the budget's count)
   against Java's heap bytes per key (Props MEM, 006-02).
5. **Size**: lines of C (code lines, as 006-08 counts them, against its
   estimate of 10,000 to 17,000) and the library's machine code at `-O2`
   and `-Os` on arm64, against 006-08's estimate and LMDB's 53 kB.
6. One thread for both, as C has one caller; Java's numbers with several
   readers noted beside, as what C does not do.


# 2. Read first

* 006-02 (Props: MEM, CORE, SS), 007-05 (startup time), 009-03 (Java's
  measurements), `java/props.sh`, `java/perf.sh`,
  `java/stress/performance.sh`; 006-08, sections 5 and 6.3.
* The memory notes on timing on F53: quiet windows, no own activity during
  a run, startup distances of 50 MB and more.


# 3. The work

1. C programs for each measurement, and Java's counterparts from the
   existing tools where they exist (Props, `StartupBench`), or small ones
   in the harness.
2. The runs in quiet windows, Java and C in turns, each at least three
   times; medians reported.
3. The table and a short reading of it.


# 4. Tests

None; the measurements run on code that passed 012-14.


# 5. Notes

* Timing runs disturb, and are disturbed by, other sessions: run only in
  a quiet window, in the background, with this session idle until they
  end.
* Optimizations are not this task's: if C is slow somewhere, say where,
  and propose; a change must keep the bytes (012-01, 4.2).


# 6. Progress

## 6.1 Method

Commit: the clone of main `237d7c1` with 012-13 merged (`5338504`), and
this task's benchmark files, which change nothing in `src/`. F53: Apple M1
Pro (8 performance and 2 efficiency cores), 32 GB, macOS 27, on the
charger. C: Apple clang 21, the release build (`-O2`, asserts on, as
every build of the clone: the C readme, section 3, rule 12). Java:
OpenJDK 27 (Homebrew), G1, `-Xms12g -Xmx12g`, no `-ea`.

The programs, in `c/bench/` (built by `build.sh`; `c/readme.md`, section 1):

* `cbench.c` (C, `build/release/bench-cbench`) and `JBench.java` (Java,
  in package `bergdb.core`, compiled against the cross harness's classes):
  the same workloads, through `bergdb.h` and through Java's `Db`. Mode
  `run`: a new database on disk (node size 30, retain forever, the test
  clock moved 1/10,000 s a transaction, the test id, no eviction), keys of
  24 bytes (`/scale/key/` and 13 digits, StartupBench's of 007-05) with
  values of 8 bytes. Phases: `load` (the keys in a random order, 1,000
  puts a transaction), `batch` (puts to random keys, 1,000 a transaction),
  `single` (transactions of one put), `syncone` (one put, then a sync at
  ORDINARY: `F_FULLFSYNC` in both), `syncbatch` (1,000 puts, then a sync),
  `get` (getOne of random keys, latest), `hist` (the same at the time
  just after the load), `many` (getMany of 10,000 keys from a random key),
  `close`, then `lowopen` (the open again with a cache size indicator, the
  budget, of 16 MB) and `lowget` (getOne latest under it). Java also does
  `get4t`: getOne with four threads, what C does not do (one caller).
  Rounds: 3; a run's figure is its best round, as Props'. The random
  numbers are `java.util.Random`'s in both (C has a port), so that both
  write the same bytes: the stream lengths after each phase are equal, and
  the files of the smoke run are equal byte for byte (one SHA-256). Mode
  `start`: opens a database (no eviction), times the open (Java:
  `new FileStream`, `build()` and `start()`; C: `bergdb_open`), and checks
  2,000 random keys. Mode `mem` (C only): Props' MEM workload of 006-02.
* `bench.sh smoke|timed OUT`: builds, then runs C and Java in turns, each
  run a fresh process under `/usr/bin/time -l` (its maximum resident set),
  each after a wait for a quiet machine (no other JVM, `cc`, `cross.sh`,
  gates or Lean; at least 85 percent idle CPU) and 5 s of cool-down; the
  whole timed part runs as one background script with its log.
* `summary.py OUT`: the tables, medians over the runs.
* `size.sh`: code lines (006-08's `lines.py`) and the machine code
  (`llvm-size`, text + data, as 006-08's `c-size.sh`).

Raw output: `/Users/f/fl/bench/012/15-out/` (outside the repository).

## 6.2 Size (item 5)

`sh c/bench/size.sh` (output `15-out/size/size.txt`), at `de7613d`:

| | Lines | Code lines (006-08's count) |
|---|---:|---:|
| The library: `src/*.c`, `src/*.h`, `include/bergdb.h` | 22,003 | 16,146 |
| of which `mdb`, `replay`, `sdb` (tests' and tools' modules, not linked into an application) | | 870 |
| Unit tests (`test/unit`) | 14,491 | 12,493 |
| Functional tests (`test/func`) | 2,806 | 2,428 |
| Tools (`tools/`) | 4,451 | 3,897 |
| The cross harness's Java (`test/cross/java`) | 4,269 | 3,590 |

006-08 (6.3) estimated 10,300 to 16,000 code lines without reclaim and
11,200 to 17,300 with it, from Java's 14,677: the library's 16,146 are in
the upper part of that range, 1.10 lines of C a line of Java's Core. The
largest modules: `db` 1,395, `dag` 1,223, `api` 1,095, `reclaim` 1,001,
`starter` 939, `knode` 922, `stream` 734.

Machine code, arm64, every module of `src/` (text + data as `llvm-size`
counts them, which 006-08's `c-size.sh` used for LMDB's 52.7 kB):

| Build | Code and data | Bytes a code line | Against LMDB (52.7 kB, `-Os`) |
|---|---:|---:|---:|
| `-O2` (the release build) | 196.3 kB | 12.2 | 3.7 |
| `-Os` | 170.4 kB | 10.6 | 3.2 |
| `-Os -DNDEBUG` (asserts off) | 149.9 kB | 9.3 | 2.8 |
| `-Os`, linked into `core_demo` with `-dead_strip` (41 of the 44 objects; the linker's map) | 145.3 kB | | 2.8 |

At `-Os`: 136.2 kB of instructions, 23.2 kB of strings (Java's exception
texts and the asserts' texts; 14.8 kB without asserts), 10.5 kB of
constants, of which 10,000 bytes are one array of zeros (`recover.c`'s
fill, which a loop could write). 006-08 expected 45 to 110 kB at 4.4 to 6.3
bytes a line; the clone takes 9.3 to 10.6, so it is 1.4 to 1.6 times the
upper estimate, about three times LMDB.
`-O2` against `-Os`: 15 percent larger.

## 6.3 Memory, Props' MEM (item 4, the deterministic part)

Props' MEM workload (006-02): a million keys `"0"` to `"999999"`, empty
values, 100 puts a transaction, no eviction; the live bytes after the puts
minus before, per key. Java: `bergdb.dev.props.Mem` on this commit's jar
(the clone's `java/build.sh`), three runs. C: `bench-cbench mem`, the
allocator's live bytes (the stream in files, so that the stream's bytes
are not counted, as Java's `DummyStream` keeps none).

| | Bytes a key |
|---|---:|
| Java, heap after `System.gc()` (MEM) | 129, 129, 130 |
| C, the allocator's live bytes | 123.1 |
| of which index objects / values / handles / node table / state | 69.2 / 40.0 / 3.8 / 4.5 / 5.6 |
| C, the process's resident set's growth, without the write buffer's 10 MB | 146.4 |

C's index and Java's heap are about the same per key (C 5 percent less).
The resident set is 19 percent above the allocator's count (158.5 MB
against 133.3 MB at the end): `malloc`'s own rounding and lists.
An empty value costs C 40 bytes (a value object). The figures at 1M and
10M keys of 24 bytes with 8-byte values come from the timed runs (6.4).

## 6.4 The timed runs (items 1 to 4)

`sh c/bench/bench.sh timed OUT` from 04:03 to 04:29, then `extra` (04:31
to 04:37, at `9bf584a`) and an LTO comparison (04:49 to 04:54); `timed`
at `23b8581`. The library is `5338504`'s in all: this task's commits
change only `c/bench/`, `build.sh` and the documents. Every run a fresh process, C and Java in turns, after the quiet
check: 96 to 98 percent idle CPU during the 1M runs, 85 to 87 percent from
04:08 (another process, not ours, took about 1.5 cores of 10; nothing of
012's or the gates ran). The figures are medians of 3 runs each (2 for
`extra`); each run's figure for reads is its best of 3 rounds. The spread
between runs was under 2 percent for nearly every figure (`summary.txt`
has the ranges). Outputs: `15-out/timed/`, `15-out/extra/`, `15-out/lto/`,
each with `log.txt` and `summary.txt`.

**Writes** (puts or transactions a second; one thread; no eviction; sd
50 MB):

| | 1M: C | 1M: Java | C/Java | 10M: C | 10M: Java | C/Java |
|---|---:|---:|---:|---:|---:|---:|
| load: new keys, 1,000 puts a transaction (puts/s) | 360,714 | 355,911 | 1.01 | 153,971 | 143,023 | 1.08 |
| batch: updates, 1,000 puts a transaction (puts/s) | 256,684 | 241,912 | 1.06 | 111,938 | 100,325 | 1.12 |
| single: transactions of one put (/s) | 205,199 | 157,044 | 1.31 | 100,221 | 80,480 | 1.25 |
| syncone: one put, then a sync (/s) | 147 | 210 | 0.70 | 190 | 189 | 1.01 |
| syncbatch: 1,000 puts, then a sync (/s) | 112 | 102 | 1.11 | 87.5 | 76.3 | 1.15 |

The batches' transactions a second are the puts over 1,000 (load: 361
against 356 at 1M, 154 against 143 at 10M). `extra` timed the first sync
alone, after 405 MB written without one: C 0.45 s (2.2 a second), Java 6
ms; after it, `syncone` was C 198 and Java 196 a second (1M, 2 runs each).
At 10M keys and sd 200 MB (C's make, one run): load 214,203 puts/s,
batch 154,313.

**Bytes appended per put** (item 1's check): equal in C and Java in every
run, as the stream's length after every phase is; the smoke run's files
are equal byte for byte.

| | load | batch | single | syncone | syncbatch |
|---|---:|---:|---:|---:|---:|
| 1M keys, sd 50 MB | 127.32 | 236.02 | 418.83 | 120.32 | 245.13 |
| 10M keys, sd 50 MB | 521.07 | 744.46 | 996.06 | 595.20 | 460.11 |
| 10M keys, sd 200 MB (C only) | 231.33 | 436.39 | | | |

**Reads** (getOne a second, getMany keys a second; one thread):

| | 1M: C | 1M: Java | C/Java | 10M: C | 10M: Java | C/Java |
|---|---:|---:|---:|---:|---:|---:|
| getOne latest, in memory | 768,644 | 1,048,215 | 0.73 | 479,757 | 601,339 | 0.80 |
| getOne historical (at the load's end), in memory | 863,176 | 888,168 | 0.97 | 490,502 | 629,035 | 0.78 |
| getMany, 10,000 keys from a random key (keys/s) | 5,565,214 | 7,011,951 | 0.79 | 5,689,124 | 7,092,354 | 0.80 |
| getOne latest, budget 16 MB (after an open) | 131,897 | 225,534 | 0.58 | 36,195 | 110,269 | 0.33 |
| getOne latest, budget 128 MB (`extra`) | 390,760 | 570,531 | 0.68 | | | |
| Java's getOne latest with 4 threads (C: one caller) | | 3,763,461 | | | 2,195,968 | |

**Startup** (seconds, warm: the OS cache holds the stream; C and Java
open the same database; the open: C's `bergdb_open`, Java's `new
FileStream`, `build()` and `start()` in a fresh JVM):

| Database | Section | Transactions read | C | Java | C/Java |
|---|---:|---:|---:|---:|---:|
| 10M keys, sd 50 MB (the last 10M run's) | 40.8 MB | 26,349 | 0.99 | 2.42 | 0.41 |
| 10M keys, sd 200 MB (C's make, 3M updates, as 007-05's) | 205.9 MB | 448 | 4.55 | 10.3 | 0.44 |
| 1M keys, sd 50 MB, budget 16 MB (`extra`) | 52.7 MB | 98,020 | 1.03 | 1.96 | 0.53 |
| the same, budget 128 MB | 52.7 MB | 98,020 | 0.93 | 1.90 | 0.49 |
| `lowopen`: 1M, budget 16 MB, in the same process after the close | | | 1.01 | 1.77 | 0.57 |
| `lowopen`: 10M, budget 16 MB, likewise | | | 1.12 | 2.35 | 0.48 |

The creation of a database: C 6 to 11 ms, Java 75 to 90 ms. The close:
C 0.49 s at 1M and 3.4 s at 10M, Java 1 to 2 ms (6.5).

**Memory** (bytes a key; C: the allocator's live bytes; Java: the heap
after `System.gc()`; both minus the empty database's):

| | 1M: C | 1M: Java | 10M: C | 10M: Java |
|---|---:|---:|---:|---:|
| after the load | 187.2 | 201.6 | 179.9 | 185.3 |
| after the writes (updates kept: no eviction) | 378.9 | 397.5 | 216.3 | 224.0 |
| C's resident bytes (`bergdb_stats`) after the load | 180.2 | | 178.9 | |
| C's process resident set after the load, all of it | 229.6 | | 205.5 | |
| the run's maximum resident set (process) | 0.82 GB | 6.4 GB | 2.53 GB | 8.0 to 10.4 GB |

C after the load at 10M: index objects 117.3 bytes a key, values 48.0,
handles 6.5, the node table 7.1, state 0.7. Java's maximum resident set
follows the heap it was given (`-Xms12g`), not what it needs. Under the
16 MB budget, after the gets: C 100.4 MB live (1M) and 147.3 MB (10M),
Java's heap 110 MB and 150 MB; both hold about D, which is over the
budget (C's pinned bytes 89 and 139 MB). After an open: 10M at sd 50 MB,
C 169 MB live (the open's peak 322 MB, resident set 345 MB), Java's heap
173 MB (maximum resident set 1.25 GB); at sd 200 MB, C 645 MB (peak
1.14 GB, resident set 1.18 GB), Java 616 MB (2.52 GB). The open of 1M
keys under a budget of 16 MB peaked at 472 MB of C's allocator and ended
at 99 MB: it evicts at its end (6.5).

**C's build with link-time optimization** (`-O2 -flto`, the library and
`bench-cbench`; the same bytes: the stream lengths equal; 1M keys, 3 runs
each in turns; `15-out/lto/`, its `build.sh` and `run.sh`):

| | `-O2` (release) | `-O2 -flto` | Gain |
|---|---:|---:|---:|
| load (puts/s) | 358,426 | 481,986 | 1.34 |
| batch (puts/s) | 256,048 | 320,001 | 1.25 |
| single (/s) | 206,275 | 255,880 | 1.24 |
| getOne latest | 760,841 | 888,312 | 1.17 |
| getOne historical | 850,722 | 974,743 | 1.15 |
| getMany (keys/s) | 5,569,727 | 6,858,240 | 1.23 |
| getOne, budget 16 MB | 122,568 | 151,383 | 1.24 |
| the open, budget 16 MB (s) | 1.00 | 0.86 | 1.16 |

## 6.5 Reading

* **Writes: C is as fast as Java or faster**, 1.01 to 1.35 times. The
  work of a put, the index's copy-on-write and the node writer, is the
  same code; C gains most where a transaction does little (single puts,
  1.25 to 1.35), probably as Java's per-transaction objects (the builder,
  the STM's sets, the record's buffers) weigh most there (not profiled). The bytes are the same by
  construction, and checked.
* **A sync costs the device's flush in both** (`F_FULLFSYNC`, about 5 ms:
  190 a second). C's first sync after a long run without one is slow
  (0.45 s after 405 MB), as C writes with `write` and forces only at a
  sync, while Java's buffer thread forces every write as it goes (C
  readme, section 9, point 1); the 1M `syncone` row (0.70) is that first
  sync, and without it C and Java are equal (198 and 196).
* **Reads in memory: C is slower, 0.73 to 0.80 of Java** (0.97 for the
  historical getOne at 1M). The profile (6.7, 03:35) puts C's time in the
  key nodes' linear search, the same algorithm as Java's; C's port calls
  small helpers across modules (`kl_delete_bit`, `kl_*`), which `-O2`
  cannot inline across files, while the JIT inlines across classes and
  specializes `search`'s kind. Link-time optimization alone gains 15 to 24
  percent on reads (and 24 to 34 on writes), which brings getOne to about
  0.85 of Java and getMany to 0.98. getMany itself is not profiled.
* **Reads under a small budget: C is slower, 0.33 to 0.68**, and the
  further D is over the budget, the slower. At 16 MB, D (89 MB at 1M, 139
  MB at 10M) cannot be evicted, and C's CLOCK sweep at the end of every
  call (Level 4 in the calls, 012-12) walks the node table and finds
  little to take: 43 percent of the samples at 1M. Java evicts on a
  thread of its own, on another core, so its reader pays none of it. At
  128 MB, above D, C is at 0.68, near its in-memory ratio.
* **Startup: C is 1.9 to 2.4 times faster** (0.41 to 0.53 of Java's
  time; 0.57 for the reopen of 1M keys in the same process), from 40 MB
  sections to 206 MB, on the same databases and reading
  the same section. Java's start runs in a fresh JVM, its first calls
  interpreted, and allocates on a collected heap; C's reads and reruns the
  same records with the allocator's blocks.
* **The close is C's slow call**: 3.4 s at 10M keys, where C frees every
  block (18 million, about 190 ns each), while Java leaves its heap to the
  collector (2 ms). The creation is the other way: 6 ms against 80.
* **Memory: C needs 3 to 7 percent less than Java's heap** for the same
  index (Props' MEM: 123 against 129; 24-byte keys: 180 to 187 against
  185 to 202); the process's resident set is 1.1 to 1.2 times the
  allocator's count. Java's process needs its heap's size and more.
* **Size: three times LMDB** (6.2): 145 to 196 kB, 9.3 to 12.2 bytes a
  code line against LMDB's 6.3, from the asserts (20 kB), the error
  texts (15 kB) and one 10 kB constant.

Proposals, each keeping the bytes (none changes what is written; 012-01,
4.2); not made here:

1. **Build the release with `-flto`**, or move the small hot helpers
   (`klong`, `keys`, `node`) into their headers as `static inline`:
   measured +15 to +34 percent (above). Its code size is not measured.
2. **Bound the sweep when the pinned bytes exceed the budget**: skip it
   while the last full sweep found nothing to take and nothing new was
   unpinned, or sweep a fixed share of the table a call. Under a 16 MB
   budget that is up to 43 percent of a read's time.
3. **Evict during the open's loads**, not only at its end: the open of 1M
   keys under 16 MB peaked at 472 MB (012-12 chose the end of the open).
4. **The close's frees**: an arena or slabs for the index objects would
   make the close a few frees; or document that it takes about 0.2 µs a
   resident object.
5. **The first sync**: an option for the application to force in steps
   (every N MB written), or a note in the C readme's section 9 that a long
   run without a sync makes the first one long.
6. **Size**: `recover.c`'s 10,000-byte array of zeros (a loop can write
   the fill), and the error texts (23 kB of strings with the asserts' at
   `-Os`) if a target needs it smaller.

## 6.6 Not measured

* Cold starts (`purge` needs root on F53; 007-05 measured Java's cold
  starts on s1), and anything on s1.
* 50M keys; values other than 8 bytes; deletes; reclaim (retain forever
  throughout).
* Java with another collector or a smaller heap; Java's peak memory during
  its start (only its heap after the start's `System.gc()`).
* Java's writes at sd 200 MB (only C's make); reads under a 128 MB budget
  at 10M keys.
* The code size of the `-flto` build; the size on a Cortex-M4.
* Power and wakeups.

## 6.7 Log

* 03:18 Started. Read the plan, 006-02, 006-08, 007-05, 012-12's 6.4.
* 03:30 The programs written and smoke-tested at 100,000 keys (the machine
  busy with the conductor's cross test, so no timing): C and Java write
  the same files, start the same section, find every key.
* 03:31 Size (6.2) and Props' MEM (6.3) measured.
* 03:35 One run of each at 1M keys to size the timed plan (the machine
  busy: not results): 45 s for C, 37 s for Java; the same stream lengths
  after every phase. Profiles with macOS's `sample` (shapes, not times,
  `15-out/est/`): C's getOne in memory spends its time in the key nodes'
  search (`search`, `kn_search_eq`: the linear scan of a node's klongs,
  as Java's), with `kl_delete_bit` as a call of its own (another module,
  no inlining across files); under the 16 MB budget, 43 percent of the
  samples are in `ev_run`, the CLOCK sweep at the end of each call, as
  the pinned bytes (D, 94.5 MB at 1M keys after 1M updates) exceed the
  budget, so the sweep finds little to take (012-12, 6.5's note), and 19
  percent in `pread`. (A peak of 358 MB noted here at first was the
  run's, not the open's: the count is the process's; 6.4 has the open's.)
* 04:01 The conductor: the machine quiet. 04:03 to 04:29 `bench.sh timed`
  (27 runs, none waited more than 13 s for quiet); 6.4.
* 04:31 `bench.sh extra`: the first sync alone, a 128 MB budget, opens
  under budgets. Its opens stopped at once (a variable of the loop was
  overwritten by the quiet check; fixed in `bench.sh`) and were run again
  as `extrastarts` at 04:36.
* 04:38 The LTO build (outside the repository, `15-out/lto/build.sh`); its
  first run waited 10 minutes on the editor's JVM (its one-off script had
  not `bench.sh`'s exclusion), then ran 04:49 to 04:54.
* 04:55 The tables (6.4), the reading and the proposals (6.5), what was not
  measured (6.6).
* 04:58 The C gate on the clone at `34f115e`: **C BEFORE COMMIT OK (146
  s)** (`15-out/gate-15.txt`).

## 6.8 For the conductor

* Files (under `items/012-bergdb-c/`): this file; new `c/bench/cbench.c`,
  `c/bench/JBench.java`, `c/bench/bench.sh`, `c/bench/summary.py`,
  `c/bench/size.sh`; changed `c/build.sh` (builds `bench/*.c` as
  `bench-NAME` in both builds) and `c/readme.md` (the layout, section 2).
  Nothing in `c/src/`, `java/`, `lean/` or `docs/`.
* `build.sh` now builds `bench-cbench` in the test build too (with the
  sanitizers), about a second more; `before-commit.sh` does not run it.
* Raw outputs: `/Users/f/fl/bench/012/15-out/` (`timed/`, `extra/`,
  `lto/`, `size/`, `mem/`, `est/`, `smoke/`); the data directories are
  deleted.
* For 012-16: the tables of 6.2 to 6.4 and the reading of 6.5; proposal 1
  (`-flto`) is the cheapest gain, proposal 2 the largest under a budget.
