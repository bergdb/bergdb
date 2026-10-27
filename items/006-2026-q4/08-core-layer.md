# 006-08 The Core Layer: built alone, its size, a C clone

Created 2026-10-26 by Claude (Opus 5.5, Claude Code), at Frans's request.
Reworked on 2026-10-27, at his request, around what matters: that the Core
can be built, that it is independent, and whether a C clone for an
embedded target is feasible. Status: done.


## 1. The questions

Frans, 2026-10-26: "Check BergDB Core Layer independence. Can a version be
build from the bergdb.core package with dependencies. The user of the
database would call the methods of Db directly. Ensure there are not
dependencies on classes in packages beyond what is allowed according to
the package.html documentation."

The same day: "Is The Core independent from the test of the code. How
large would a build of only the Core be compared to the full database.
Assume users would call the methods of Db directly instead. How large
would the core be. How many lines of code? Do not cound test code. This
question is relevant for the possibility of using the database or some
type of clone to C or rust for an embedded target where code size
matters."

2026-10-27: "What is important is that Core can be built. It is still
independent. And the feasibility for a C embedded clone."

The terms. The Core Layer is `bergdb.core` and the packages it may use,
directly or not, by the `package.html` files: `common`, `dag`, `nanotest`,
`pub.util`, `storage` and `stream` (010-01, P12). The Core is what `Db` and
`DbBuilder` need of it, without the test code: all that a user who calls
`Db` directly needs. A code line has code on it: it is not blank and not
only a comment. The tools and their output are in
[08-core-layer/](08-core-layer/) (section 7).


## 2. The answers

* **The Core can be built.** The Core Layer compiles alone, with an empty
  class path, into a jar of 680 kB. A program outside `bergdb` calls `Db`
  with only that jar, and the Core Layer's tests pass on it. Without its
  test code the Core is 121 source files, in a jar of 335 kB that needs
  only `java.base`.
* **It is independent.** Of the layers above: no class of the Core Layer
  uses `pub` or `pubimp`, and each of its packages uses only what its
  `package.html` allows. Of its test code: the tests are in the production
  files, but the production code needs them in one line only. With the
  tests removed, the Core compiles, runs, and writes the same stream, byte
  for byte, as the Core with its tests.
* **Its size.** 14,677 code lines: two thirds of BergDB's production code,
  22,017 code lines. The full build, `build/bergdb.jar`, is 3.3 MB, most
  of it the ICU classes (their jar alone is 2.0 MB).
* **A C clone for an embedded target is feasible, and its size is not the
  obstacle.** By an estimate, it would be 10,000 to 17,000 lines of C. By
  three C libraries measured here, that is about 35 to 90 kB of code on a
  Cortex-M4, and 45 to 110 kB on arm64, where LMDB is 53 kB. The open
  questions are elsewhere: the memory and the writes at the small startup
  distances that a small target needs, a written stream format, and power
  loss on raw flash (section 6).


## 3. The Core can be built

By `core-build.sh` at `c7c6f10` (`runs/core-build.txt`), the Core Layer's
seven packages compile from `java/src` alone, with an empty class path and
source path: 175 source files, 415 classes, a jar of 680 kB. Of the JDK they
need `java.base` and `java.management`, for `Jmx`. `CoreDemo` is a program
outside the `bergdb` packages, with that jar alone on its class path. It
writes to a database in a directory with `execute`, reads with `getOne`,
`getMany` and `getTrans`, and reads the same after a restart. The Core
Layer's own tests pass on that jar alone: 648 unit tests and 52 f-tests, of
BergDB's 1,023 and 71.

Without the test code (section 4), by `core-size.sh` at `c7c6f10`
(`runs/core-size.txt`):

| Build | Source files | Classes | Jar | JDK |
|---|---|---|---|---|
| The Core Layer, with its tests | 175 | 415 | 680 kB | `java.base`, `java.management` |
| The Core Layer, without its tests | 137 | 262 | 365 kB | |
| The Core: what `Db` and `DbBuilder` need, without tests | 121 | 234 | 335 kB; 293 kB without debug information | `java.base` |
| All of `java/src` and `src-icu`, without tests | 207 | 377 | 520 kB, and the ICU jar, 2,021 kB | |
| `build/bergdb.jar`: all, with the tests, `src-dev` and ICU | | | 3,263 kB | |

`javac` finds what `Db` and `DbBuilder` need: on the two files, with the
stripped copy as source path, it compiles what they use, directly or not,
and nothing more. `CoreDemo` runs on that jar alone. Of the Core Layer,
`Db` does not need `Jmx`, `DbScan`, `KeyFactory`, `DagComparison`,
`KvComparison`, `DagNodeIterator`, `StatsNodeVisitor`, `OneFileStream`,
`ReadOnlyStream` and a few small classes of `common`.


## 4. The Core is independent

**Of the layers above.** No class of the Core Layer uses `pub` or
`pubimp`. `deps.py` finds no such use in the imports or in qualified names,
and `javac` with an empty class path could not compile one. Each of the
seven packages uses only what its `package.html` allows. Two did not,
until 2026-10-26:

* `FileStreamPowerLossTester`, a tester in `stream`, used `core` and
  `storage`. It moved to `core`, and `FileStreamIo`, the file system seam
  that it replaces, became public.
* `dag` and `stream` used `nanotest`; their lists now name it.

That change passed `before-commit.sh` and step 7 of `level3.sh`, the
power-loss test (`runs/`). The uses that their lists do not allow are now
all in `pub` and `pubimp`, outside the Core Layer: 005-56.

**Of its test code.** The tests are in the production files: 342 `@Nano`
methods in the Core Layer's 137 production files, beside 304 in its 16
tester files. There are also `test*` and `main()` methods, nested `Tester`
classes (`RecoverableStream.Tester`), and private helpers that only tests
use (`Eviction`'s twins). 52 production files use `nanotest`, and a few
also a tester (`DbHelper` uses `KeyNodeTester`, `StoredTopNode` uses
`TopTester`), in the test code but for one line (below). As `nanotest` is
part of the Core Layer, none of this makes the Core depend on anything
outside it.

And the production code does not depend on the tests. `strip.py` removes
them from a copy, and what is left compiles alone with one line changed:
`KeyNode.checkLastTimeIndex()`, a consistency check, calls `nanotest`'s
`Assert.assertEquals`. The copy throws `AssertionError` itself, as the
line could.

**The same Core.** By P2 (010-01) the stream is a function of the
transactions, so a build of the Core that behaves the same writes the same
bytes. `CoreSame` runs a fixed workload on a database in a directory: 6,000
transactions of puts and deletes on 3,000 keys, from a seeded random
generator and a test clock. Index nodes are written (a startup distance of
20 kB), eviction runs (a cache of 64 kB), reclaim cuts the front of the
stream (a retain duration of 5 s), and the database restarts every 1,000
transactions. On the Core Layer with its tests and on the Core without
them, the stream has the same SHA-256 (7.7 MB kept, 7.0 MB cut), and so has
the latest state (2,691 keys).

Some test-only code is still reached by the Core, and stays in it and in
its counts: `Audit` and `TestClock` (304 code lines), `Db.TestHooks`, and
`DbBuilder`'s test settings (`evictionSchedule`, `auditEvery`,
`secondTopOrdinal`).


## 5. The Core's size

By `core-size.sh` (`runs/core-size.txt`):

| Code | Lines | Code lines |
|---|---|---|
| All of `java/src`, with its tests | 66,810 | 43,984 |
| All of `java/src` and `src-icu`, without tests | 38,348 | 22,017 |
| The Core Layer, with its tests | 47,770 | 31,445 |
| The Core Layer, without its tests | 27,346 | 15,773 |
| The Core | 25,649 | 14,677 |

The Core is 93 percent of the Core Layer without its tests, and two thirds
of all production code. The rest is the upper layers, `pub`, `pubimp` and
`src-icu` (6,244 code lines), and the classes of the Core Layer that `Db`
does not need (1,096). Its largest classes are `Db` (1,320 code lines),
`KeyNode` (1,219), `Dag` and `StorageManager` (802 each), `Reclaim` (714)
and `FileStream` (661). Each file's lines are in `runs/closure-lines.txt`;
section 6.2 groups them.


## 6. A C clone for an embedded target

### 6.1 What a clone is

The same database: a multiversion ordered map from (key, time) to value in
one append-only stream, with index nodes written lazily into it, so that
startup reads only the stream's tail. The same Core Data API: `execute`,
`getOne`, `getMany`, `getTrans`. A first clone would be single-threaded: one
task calls it.

### 6.2 What it ports, rewrites and leaves out

The Core's 14,677 code lines (`runs/closure-lines.txt`):

| Part | Java code lines | In a C clone |
|---|---|---|
| The index and its versions, `dag`: key, top and value nodes, `Klong`, `GetMany`, `Dag` | 3,617 | ported |
| The database, the rest of `core`: `Db` (1,320), `StoredTrans`, `DbStarter`, `NodeCollection`, `NodeStream`, `Trans`, `TransSeq` and others | 4,877 | ported |
| The record format and recovery: `RecoverableStream`, `MetaBlock`, the exceptions | 592 | ported |
| Bytes and checksums: `Bytes`, `MyChecksum` and small helpers of `common` | 252 | ported |
| Reclaim: `Reclaim`, `CutStream`, `StringMap` | 850 | ported, if the stream must not grow forever |
| Memory: `Cache3`, `Eviction`, `Residents`, `Handle` | 930 | rewritten: a node table and CLOCK, in the calls |
| The write path: `StorageManager`, `BufferedStream`, the replica rules | 1,261 | rewritten: one buffer, no replicas |
| The storage: `FileStream`, `FileStreamIo`, `AppendOnlyStream` | 715 | rewritten for the target: files or raw flash |
| Encryption: `Salsa`, `SalsaStream` | 243 | left out, or the target's own |
| `MemoryStream`, `DbUtil`, `BuildInfo`, `Util`, `StringUtil`, `SeedGenerator` | 958 | left out, or from the C library |
| Test-only: `Audit`, `TestClock` | 304 | left out |
| `pub.util`: the exceptions, `Clock`, `Job`, `StorageInfo` | 78 | error codes |

So 9,338 code lines are ported, and 850 more with reclaim; 2,906 are
rewritten; 1,583 are left out.

### 6.3 Code size

An estimate; no line of a clone exists. Suppose a line of Java takes 1 to
1.5 lines of C. The node code is mostly arrays of 64-bit numbers, which C
has too. But C has no collections, so it needs a hash table, an array
that grows, and a sorted map for a transaction's keys. Its errors are
return codes, not exceptions, and memory is freed by hand. Then the 9,338
ported lines are 9,300 to 14,000 lines of C. The rewritten parts,
single-threaded, would be about 1,000 to 2,000 lines, and reclaim 850 to
1,300. In all, 10,300 to 16,000 lines of C without reclaim, and 11,200 to
17,300 with it.

Machine code per line, measured by `c-size.sh` (`runs/c-size.txt`) on three
C libraries, compiled with `clang -Os`:

| Library | Code lines | Code and data | Bytes a line |
|---|---|---|---|
| LMDB 0.9.33, a copy-on-write B+tree database, arm64 | 8,339 | 52.7 kB | 6.3 |
| littlefs 2.9.3, a power-loss safe file system for flash, arm64 | 5,419 | 26.2 kB | 4.8 |
| littlefs 2.9.3, Cortex-M4 (Thumb-2) | 5,419 | 18.9 kB | 3.5 |
| SQLite 3.49.1, its default options, arm64 | 165,015 | 731 kB | 4.4 |

On a Cortex-M4 a clone would take more than littlefs's 3.5 bytes a line:
its keys, positions and times are 64-bit, which a 32-bit core handles in
pairs of registers. At 3.5 to 5 bytes a line, 10,300 to 17,300 lines are
about 35 to 90 kB of code, two to five times littlefs's. On arm64, at 4.4
to 6.3 bytes a line, they are 45 to 110 kB: LMDB's size to twice it, and a
sixth or less of SQLite's default build. The jar sizes do not predict it:
bytecode is not machine code. In Rust the plan is the same; its code size is
not estimated here.

### 6.4 Memory

What BergDB pins sets the memory; the rest is a budget. The pinned objects
are the super root, D (the index nodes dirty since the startup position),
the record being written, and the newest written top node (levels.md,
section 7). D is bounded by the startup distance, loosely: its nodes'
stream bytes reached 1.6 to 2.9 times the startup distance in 005-38's runs,
with 10M and 50M keys at 50 MB to 1000 MB. Everything else is evicted to
the budget, which can be small. The record being written is bounded by the
record limit: 2 GB in Java, but the tests lower it to 100 kB, so a clone
can set it small, and larger transactions are split (005-17).

A target with 256 kB for the database could then use a startup distance of
about 32 kB. D would take up to about 100 kB, if its form in memory is
close to its form in the stream; the cache some tens of kB; the buffer a
flash page. The startup section is small too. It reached at most 2.6 times
the startup distance in 005-38's runs, and the deadline planned in 007-03
bounds it at twice. So a startup after a power loss would read about 80 kB.

The cost is writes. The smaller the startup distance, the sooner and the
more often a dirty index node is written. With uniform random updates of
10M keys, a put of a 24-byte key and an 8-byte value cost 681 bytes of
stream at 50 MB, 373 at 200 MB and 180 at 1000 MB (005-38). At the
distances of a small target nothing is measured. `CoreSame`'s workload,
with 20 kB and only 3,000 keys, wrote 14.7 MB for its 6,000 transactions,
about 2.4 kB each, reclaim and restarts included. That is a first sign, not
a measurement, that index writes would dominate the stream; on flash that
means wear and erase work.

### 6.5 Storage and power loss

The stream suits flash. It is append-only, so pages are programmed in
order. Reclaim cuts the front, so erase blocks would be erased whole, from
the front, as `FileStream` deletes whole files today. With the stream as a
ring of erase blocks, each block would be erased once a round, which levels
the wear without a layer for it; an idea, not tried.

A record starts with its size and ends with a commit byte, and a meta block
of 128 bytes sits at every multiple of 200,000 bytes, so recovery finds the
last whole record without reading the whole stream (`RecoverableStream`).
Java tests this under a fault model of a file system (`PowerLossTest`;
011-07). Raw flash fails in other ways, such as a page half programmed or
an erase cut short, so a clone needs a fault model of its own. The 200,000
bytes and `FileStream`'s files of 200 kB and more were chosen for files. A
clone on raw flash would map stream positions onto blocks, or change the
constants and give up byte equality with Java.

### 6.6 What is Java's and must change

* **Threads.** Four classes start threads: `BufferedStream`'s writer,
  `Eviction`'s evictor, `Db`'s close in the background, and `DbHelper`,
  for a replica. The Core has 184 `synchronized` and 35 `volatile`, in 20
  and 16 files, atomics in 8 classes, and reads without locks, with
  barriers (009-02, section 3.4). A clone with one task needs none of it.
  It writes in the calls or at `sync`, and evicts at transaction ends and
  after loads, where Java already runs eviction (levels.md, section 7).
* **Memory.** In Java, what eviction drops lives on while a reader still
  holds it, and the collector frees it later. In C with one thread,
  eviction between calls can free at once, as no call holds a node or a
  value then. Readers in other threads would need reference counts or
  epochs. The Core uses no weak or
  soft references and, besides `Db.finalize()` (005-55), no finalizer:
  nothing depends on when the collector runs (P8).
* **The JDK.** The Core uses 96 JDK classes, all of `java.base` (jdeps):
  collections (`ArrayList`, `HashMap`, `IdentityHashMap`, `ArrayDeque`, and
  `TreeMap` for a transaction's keys), `CRC32`, files (`FileChannel`,
  `RandomAccessFile`), and, for ids and messages, `SecureRandom`,
  `InetAddress` and dates. In C that is a hash table, an array that grows,
  a sorted map and CRC-32, a few hundred lines; files and entropy come from
  the target.
* **Errors.** 382 `throw` and 85 `catch` become return codes. P7 makes
  that simple: a transaction is checked before its go point, and after it a
  failure stops the database (levels.md, section 3), so a clone needs no
  undo.
* **The clock.** No wall clock is needed. `DbClock` makes each
  transaction's time larger than the last, whatever the clock says, so a
  counter will do; the retain duration is then counted in its units.

### 6.7 What helps a clone

* **A deterministic stream** (P2). The same transactions and times give
  the same bytes. So a clone can be checked byte for byte against Java, on
  every workload of Java's tests and stress programs, as `CoreSame` checks
  two Java builds against each other. `RestartInvariance` already requires
  byte equality across restarts.
* **The model and the checker.** `docs/sis-model.md` and the Lean proofs
  (T1, T2, T3, reclaim, and eviction with handles) are about the algorithm,
  not about Java, and hold for a faithful clone too. The trace checker
  checks a run's trace against the model's steps, and the trace format
  (`docs/trace-format.md`) is text. A clone that writes traces gets the
  conformance checks that Java gets (C-L, C-P, C-H).
* **Small configurations are tested.** The unit tests use startup
  distances from 10 bytes to 2 MB, mostly 2,000 and 10,000 bytes, nodes of
  8, 14, 30 and 62 entries, and a record limit of 100 kB.
* **Principles that suit a small device.** Calm when not used (P3: no CPU,
  I/O or wake-ups when idle, but for the evictor's one wake-up a second,
  005-51), bounded startup (P5), a failed database stops (P7), no global
  state (P9), few settings (P10).
* **Missing: a written stream format.** `stream-format.txt` in
  `core/doc-files` (2015) is partial and names the code as authoritative:
  `StoredTrans`, `StoredKeyNode`, `StoredTopNode`, `StoredValueNode`,
  `MetaBlock` and `RecoverableStream`, about 1,500 code lines.

### 6.8 The verdict, and first steps

Feasible. Size is no obstacle: by the estimate, 35 to 90 kB of code on a
Cortex-M4, and on arm64 LMDB's size to twice it. The design suits a small
device: one append-only stream, bounded startup, recovery after power loss,
eviction to a budget, and calm when idle. What decides it is memory and
writes at small startup distances, which no run has measured. If a clone is
pursued, the first steps:

1. Measure Java at a small target's sizes, 10k to 1M keys with startup
   distances of 8 kB to 1 MB: the stream bytes a put costs, D's bytes, and
   the startup section. This answers memory and wear before any C is
   written.
2. Write the stream format down from the code, as a subitem.
3. A reader in C first: startup and `getOne` on a stream that Java wrote.
   Then the writer, checked byte for byte against Java, and traces for the
   checker.
4. A fault model for raw flash, from 011-07's for files.


## 7. Tools

In [08-core-layer/](08-core-layer/); each script's header says what it
does:

* `core-build.sh`: the Core Layer alone. `deps.py` on its packages, `javac`
  on its sources with an empty class path, `jdeps`, `CoreDemo`, and its
  tests on its jar alone. `sh core-build.sh REPO [unit] [f]`: about 15 s
  with the unit tests, 80 s with both.
* `core-size.sh`: the Core without its tests. `strip.py` on a copy, `javac`
  on the copy and on what `Db` needs, `jdeps`, `CoreDemo`, `CoreSame` on
  both builds, the build of all production code for comparison, and the
  lines. `sh core-size.sh REPO`: about 20 s.
* `c-size.sh`: downloads LMDB, littlefs and SQLite, compiles them with
  `-Os` (littlefs also for a Cortex-M4) and prints the bytes per code line.
  About 15 s.
* `deps.py`: each package's uses of other `bergdb` packages against its
  `package.html`. `python3 -I deps.py java/src core` checks the Core Layer;
  without `core`, all nine packages.
* `strip.py`: removes the test code from a copy of the sources.
* `lines.py`: the lines and code lines of source files.
* `CoreDemo.java`: a user's program that calls `Db` directly.
* `CoreSame.java`: the fixed workload of section 4.
* `CoreUnit.java`: runs the Nano tests of the given packages, as
  `bergdb.dev.Unit` does for all of them.
* `runs/`: the output. `core-build.txt`, `core-size.txt` and
  `closure-lines.txt` are at `c7c6f10`, of 2026-10-27, and `c-size.txt` is
  of the same day. The others are of 2026-10-26: the checks of the change
  in section 4 (`before-commit.txt`, `powerloss-*.txt`, `deps-before.txt`,
  `deps-after.txt`) and the Core Layer's test logs (`core-unit.txt`,
  `core-f.txt`).

P12 has no measure yet (010-01). `core-build.sh`, or `deps.py` with
`core-size.sh`, could be one, as a step in `java/before-commit.sh` (about 15
to 20 s); not added, as the commit gate is Frans's call.
