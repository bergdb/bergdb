BergDB 2026.2
=============

Released 2026-11-04 by Frans Lundberg. As planned in bergdb item 016
([../../items/016-release-2026-2/01-plan.md](../../items/016-release-2026-2/01-plan.md)).

The first release with handles (item 009): eviction in bounded steps,
without a stop-the-world of its own, and reads of resident nodes without a
lock. The first with startup bounded for BergDB's own take (007-07,
007-08). Measured against 2026.1, with both jars run in turns on the same
machines (Baseline, below).

**Every stream differs from what 2026.1 wrote, and databases of 2026.1 are
refused** (005-50): make them again with 2026.2. **Java 17 or later is
required.**


Files
-----

| File                         | What                                                     |
|------------------------------|----------------------------------------------------------|
| `bergdb-2026.2.jar`          | `java/build.sh`'s jar of the release commit (below)      |
| `bergdb-2026.2-src.zip`      | `git archive` of the release commit, in `bergdb-2026.2/` |
| `bergdb-2026.2-javadoc.zip`  | The Pub API's Javadoc, in `bergdb-2026.2-javadoc/`       |
| `baseline.zip`               | The outputs of the gates, the tests and the numbers      |
| `SHA256SUMS`                 | Check with `shasum -a 256 -c SHA256SUMS`                 |

* The jar holds the production code, `src-dev` (Props, the tests, the
  demos) and ICU 50 (as `bergdb.icu50`); class files for Java 17; main
  class `bergdb.dev.Run`.
* The source zip holds the whole tree but `releases/2026.1/`, whose jar
  and zips stay in the repository and its tag (016-09, R-1). License:
  Apache-2.0 (`LICENSE`, `NOTICE`); ICU's in `java/in/ICU-LICENSE.html`.
* The Javadoc is `java/javadoc-pub.sh`'s: `bergdb.pub` and
  `bergdb.pub.util`, with `overview-pub.html`.
* `baseline.zip`: `gates/` (`night.sh`'s report and outputs), `f53/` and
  `s1/` (the tests on the jar, the user's program, StreamDigest's digests,
  the runs in turns), and `tools/` (the scripts).


Identity
--------

* Tag `release-2026.2`, commit `d5b1bda9f77a156ee719b7408116ecc97c0ab7a4` (2026-11-04).
* `BuildInfo`: release 2026.2, release int 262, build 2026.2.261104.0759;
  `java -cp bergdb-2026.2.jar bergdb.core.BuildInfo` prints them.
* Built by `java/build.sh` (`javac --release 17`) with OpenJDK 27 (Homebrew, build 27) on F53,
  Frans's MacBook Pro (MacBookPro18,3, Apple M1 Pro, 10 cores, 32 GB,
  macOS 27.0.1).
* `bergdb-2026.2.jar`: SHA-256 `f22e193877ef178173671c2488805be7de4d23f77c4edca5e4f23523371a008f`.


What it is
----------

An in-process, append-only database for Java: a multiversion ordered map
from (key, time) to value, kept in one append-only stream, with a Lean
model of its algorithm ([README.md](../../README.md)). The levels, as
[docs/levels.md](../../docs/levels.md), section 1 has them at the release
commit:

| Level | Features | Status |
|---|---|---|
| 0 | Multiversion map in memory              | Passes the tests run                              |
| 1 | + restart by replaying the whole stream | Passes the tests run                              |
| 2 | + bounded startup (self-indexed stream) | Passes the tests run, under load and with crashes |
| 3 | + reclaim: cut the front of the stream  | Passes the tests run and a two-hour disk soak     |
| 4 | + eviction: data larger than memory     | Passes the tests run; on by default               |

* Levels 2 to 4 are aligned with the proved Lean model: startup, reclaim,
  and eviction with handles (009-05). Level 3 also passes the power-loss
  ordering checks.
* Level 4 uses handles since 2026-10-26: eviction runs in bounded steps,
  without a stop-the-world of its own; a database six times its memory
  budget runs on disk.
* Replication is in no level: experimental, not for production (Known
  issues).

Defaults that matter:

* A startup distance of 50 MB, which suits up to about 10M keys; from
  about 10M keys, 200 to 1000 MB (`DatabaseBuilder.startupDistanceInMb`,
  or `Database.setStartupDistanceInMb` while the database runs).
* A buffer time of 50 ms (20 ms in 2026.1).
* Infinite retention.
* Eviction on, with handles; the budget is the cache size (the Pub API's
  default a fifth of the JVM's maximum heap; 200 MB in the core API).
* The collector: ZGC (`-XX:+UseZGC`), or Shenandoah without generations.
  With G1, eviction brings pauses of hundreds of milliseconds and full
  collections (Requirements).


Requirements
------------

* **Java 17 or later.** The jar's classes are for Java 17 (`javac
  --release 17`, where 2026.1 had `--release 8`; 009, `bb7e189`). Tested on
  JDK 27 and JDK 17 (Verification).
* **The collector**: ZGC, or Shenandoah in its default mode, without
  generations. With eviction, G1 pauses for hundreds of milliseconds and
  runs full collections, and generational Shenandoah stopped for 821 ms
  in a soak with an 8 GB heap; ZGC paused below 0.1 ms, and Shenandoah in
  its default mode at most 4.1 ms (docs/levels.md, section 7; 004-04,
  009-04). BergDB runs with any collector; its pause target of about 20 ms
  (009) is for its own code, and the collector's pauses come on top.
* **`stop()` or `close()`** for every database started: nothing stops a
  database that the application drops (005-55, below).


Changes since 2026.1
--------------------

Collected in [releases/next.md](../next.md) as they were made, with each
entry's ID; the entries are in [items/005-todo/](../../items/005-todo/readme.md)
and [items/015-todo/](../../items/015-todo/readme.md).

### Requirements

* **Java 17 or later** (009, step 1-0, 2026-10-25, `bb7e189`):
  `java/build.sh` compiles with `javac --release 17`; the jar no longer
  runs on Java 8 to 16.
* **ZGC, or Shenandoah without generations** (004-04, 009-04): see
  Requirements above.

### Reliability

* **A failure fails the database, in more reads.**
  * A corrupt record read by `Connection.transactionInfo()` (`Db.getTrans`)
    fails the database, as every other read does, and keeps the cause;
    before, it threw as it was and the database stayed active (005-82,
    `5672e5a`). How a start handles a damaged tail stays as it is (014-01,
    Known issues).
  * A node whose checksum is right but whose key count, value size, key
    size or pointer count does not fit in it is refused by its parser
    with a `StreamFormatException`, and the read fails the database;
    before, an `ArrayIndexOutOfBoundsException` or a
    `NegativeArraySizeException` escaped the reads' failure handling
    (015-07, `de4b0b2`).
  * Corrupt record and node sizes are refused before anything is
    allocated, instead of looping or exhausting the heap (005-74,
    `2a3af23`); corrupt startup times (record order, the 56-bit range,
    increasing times in key nodes) are refused before replay (005-75,
    `2306213`). Valid streams and the format are unchanged.
* **Close reports storage failures** (005-73, `afc3d20`). `Db.close()` and
  `Database.close()` throw `StreamIoException` when the final flush or the
  storage's close fails, after cleanup; a later `close()` also reports a
  failure of an asynchronous `stop()` or an earlier `close()`; a
  try-with-resources block suppresses the close's failure when the block
  itself throws. Before, these failures were discarded. A get that runs
  while another thread closes the database fails alone, and the close
  does not report it (015-17, `bce685c`).
* **NaN reclaim fractions are refused** (005-73): `Db.setReclaimInternalFraction(double)`
  throws `IllegalArgumentException` for NaN and keeps the setting.
* **A directory whose stream is missing is refused** (015-01, `e7da01b`).
  `created.txt` marks a database whose creation reached the disk: a
  creation through the Pub API is forced before `created.txt` is written.
  `DatabaseBuilder.start()` refuses a directory that has `created.txt` and
  no `*.bergdb` file with a byte, with the new
  `bergdb.pub.util.DatabaseMissingException`, before it opens anything:
  it creates and writes nothing. Before, a directory whose stream files
  were gone, or whose only file was empty, started as a new, empty
  database without a word. A start that reads a stream and finds no
  `created.txt` writes one ("creation date: unknown"). An empty or missing
  directory is still a new database (015-05, Known issues). A start
  refused for its crypto key creates nothing either: no directory, no
  `bergdb.lock`, no empty first stream file (015-06, in part).
* **One database per directory** (005-63, `173544a`). A `FileStream` takes
  an exclusive lock on `bergdb.lock` in its directory before it reads
  anything. A second database on the directory, in the same JVM or in
  another process, is refused at once with a `DirectoryInUseException`
  (`DatabaseBuilder.start()` throws a `StreamIoException` with it as the
  cause); so is one started right after `stop()`, while the first still
  closes: start it after `close()` has returned. Two copies of BergDB in
  one JVM, loaded by two class loaders, refuse each other too, through
  system properties `bergdb.lock.` and a key (015-24, `08a389e`). The
  operating system drops the lock when the process ends, so a crash
  leaves none; the file stays. On a network file system a crashed
  client's lock may stay until the server notices (NFSv4: about 90 s), and
  where the file system supports no locks, a start fails.
* **Interrupts** (005-46, `1165c90`). An interrupt of a thread that calls
  BergDB never fails or hangs the database, as it could before (a commit
  that waited for room in the write buffer or made a cut failed the
  database; an interrupt of the storage thread stopped its writes).
  `sync()`, a job's `join()` and the wait before an rw-transaction's rerun
  end on an interrupt; every other call ignores it until it is done; the
  interrupt flag is always kept. The rule is in `Database`'s class
  Javadoc.
* **STM read sets after a reopening** (005-70, `24a031a`). The Core
  refuses a transaction with a read dependency whose snapshot predates the
  last recovered commit; before, the empty STM history after a start could
  accept it despite a conflicting write before the close.
* **Reclaim spaces its iterations by the live startup distance** (005-61,
  `4085e2e`). Before, it used the builder's value, so a database made with
  a small startup distance and opened with the default builder nearly
  stopped reclaiming.
* **A key node's growth is published safely** (015-12, `e17dfb2`). A key
  node that grew stored its new arrays with plain stores, so a reader on
  another thread could see them before their contents: a search could
  miss a key that was there long before its lookup time, or return the
  value of a later or uncommitted transaction. Rare (8 misses in 477
  million searches in a probe; none seen through a database). The node's
  array fields are now volatile (015-12, 015-14).
* **The fast path reads every pointer with an acquire** (015-14,
  `ca02b5e`), so that a lock-free read is correct by the Java Memory
  Model, not by the hardware's address dependency: a key node or a top
  node reads each pointer with an acquire, paired with the release store
  of each change in place, then its reference with an opaque read. Before,
  the JMM allowed a reader a version older than it needed; HotSpot was not
  seen to give it. The cost is not measured: an estimate of seven more
  load-acquires a hop on AArch64, none on x86 (015-14).
* **A typed primary scan goes on after a page of non-objects** (015-20,
  `e5e1179`). A scan of `usePrimary` ended a page after 100 entries,
  filtered ones included, and took the empty page for the end of the
  range, so it left out every later object, without a word.
* **An index deleted and created again under its name** (015-21, 015-22;
  `68e52ad`, `02e9e79`). A second `deleteIndex` returns the running
  deletion's job, so an old job no longer deletes a new index of the name
  and its entries; a build stops when its index is deleted, and writes
  nothing into a new index of the name, which returned extra objects,
  duplicates and the wrong order. Both lasted after a restart.
* **The last call on a key in a transaction wins** (015-40, `6890ce3`), for
  put and delete in an rw-transaction. Before, a put and then a delete of a
  key committed the put, and of several puts an earlier value could win.
* **`SystemClock` gives strictly increasing times** (005-69, `52ea92c`), as
  its Javadoc said; before, calls within a millisecond, or after the
  system clock was set back, gave equal or earlier times. No harm came of
  it: a database's own clock makes its times strictly increasing.

### API changes

* **`stop()` or `close()` is required** (005-55, `14022ad`).
  `Db.finalize()` is gone, with nothing in its place: nothing stops a
  database that the application drops. A `Db` or `Database` that is not
  stopped keeps its storage threads, its open files, its write buffer and
  its memory until the JVM exits; what it has committed is still written
  within the buffer time, and at the JVM's exit what is buffered and not
  yet written is lost, as in a crash, which the database tolerates.
* **`Db` and `Database` are `AutoCloseable`** (005-59, `7dabc2c`).
  `Database.close()` is new: it stops the database as `stop()` does and
  waits until it is closed; `stop()` still returns at once.
* **`SyncLevel` is in `bergdb.pub.util`** (005-56, `8752cf0`), where it was
  `bergdb.core.SyncLevel`, with the same constants (`NONE`, `ORDINARY`,
  `STRONG`). Code that names it changes its import, and code compiled
  against 2026.1 that uses it must be compiled again.
* **`Database.PRIMARY`** is `Util.identity("primary")` (005-56): the same
  value, but no longer a compile-time constant, so a `case` label with it
  no longer compiles.
* **The builder opens the directories in `start()`** (005-66, `7747325`).
  `DatabaseBuilder.dir()` and `replica()` only record their directories;
  `start()` opens them and closes them again if it fails. A builder that
  is never started holds nothing; a replica given before `dir()` is kept;
  `replica()` no longer throws its `IOException`, and `start()` reports a
  directory that cannot be opened or that another database has. A start
  that is refused closes only the streams it opened (015-56, `1613a45`).
* **The startup distance changes while the database runs** (005-53,
  `decc677`): `Database.setStartupDistanceInMb(int)` and
  `getStartupDistanceInMb()`, clamped as the builder's (5 to 1000 MB); the
  setting is in force when the setter returns, and is written to the
  stream with a small transaction of the database's own (a value of 200
  kB), so that a restart keeps it. A call with the setting in force writes
  nothing. After a decrease, the commits that follow bring the startup
  section down to the new setting, with no commit writing the whole of it
  (007-07).
* **The cache size changes while the database runs** (005-52, `decc677`):
  `Database.setCacheSizeInMb(int)` and `getCacheSizeInMb()`, clamped as
  the builder's (4 to 100,000 MB), for this run only (a restart takes the
  builder's value). After a decrease the database evicts down to the new
  budget in batches that end after 2 ms (`Eviction.BATCH_NANOS`; a limit,
  not a measured bound: 3 to 4 ms on s1, 009-03), also when no other call
  follows, and also when every object was just read (015-10, `f219dc7`).
  The Core's side: `Db.setCacheSizeIndicator(long)` and
  `getCacheSizeIndicator()`. The rule for both setters: a setting that
  changes the stream's bytes, as the startup distance, is kept in the
  stream; one that does not lasts for the run.
* **`DatabaseMissingException`**, new in `bergdb.pub.util` (015-01; see
  Reliability).
* **`Factory` has no public constructor** (`f342bd4`): only the static
  `Factory.database()`.
* **No .NET** (`f342bd4`): `Util.runsIkvm()` is gone, and the Javadoc no
  longer names .NET or C#.
* **Core diagnostics removed** (005-73): `Db.getCachePutSize()`,
  `getDirtyFraction100()` and `getDirtyFraction1000()`, their JMX
  attributes, and JMX's `CachedMemoryValueSpeed` and
  `CachedMemoryValueSpeedM`, which gave a constant or incorrect values.
  The Core's startup info reports the effective startup distance instead
  of −1.
* **The reclaim fraction in units of 2^-16** (005-79, `bb7b6fa`):
  `Db.setReclaimInternalFraction(double)` and JMX's setter keep their
  double and the range 0.001 to 0.90, and use the nearest multiple of
  2^-16, which the getter returns (0.25 exactly, 0.1 as 0.100006).
* Internal only: `PointerLocks` and `Db.Internal.getPointerLocks()` gone;
  `Db.Internal.cacheStats()`, `writersWaiting()` and
  `takeWriteBufferWaits()` new; `bergdb.stream.FileStreamIo` and
  `FileStream(File, FileStreamIo)` public, for the power-loss tester.

### Format

* **The node size is in the stream** (005-50, `c1f1f15`). Every meta block
  holds the maximum node size the database was written with, in 2 bytes
  at offset 44 that were reserved; the meta block's version stays 154. A
  start with another node size is refused with a `StreamFormatException`
  that names both sizes; before, it failed with what looked like a corrupt
  stream, or started and could leave a stream that no start opened. **A
  stream written by 2026.1 or earlier is refused** with a
  `VersioningStreamException`, before anything is written: databases of
  2026.1 must be made again.
* **Every stream differs from what 2026.1 wrote; the format does not**,
  apart from 005-50's two bytes: the paced take (005-49, 007-07, below)
  writes other records, and the Core decides in integers (005-79).
* **The Core decides in integers** (005-79, `bb7b6fa`, `6bc348d`). No
  double or float decides the stream's bytes or the memory: the take's
  share and dither (in units of 2^-16 of a node), reclaim's iteration
  spacing and internal fraction, eviction's low watermark and two buffer
  sizes use 64-bit integers, which every language and target computes
  alike. Doubles stay at the API, converted at once, and in statistics;
  `java/doubles.py` checks it in `before-commit.sh`. Against the double
  rule of the take during 2026.2's development, StreamDigest's decided
  digests changed in 1 of its 12 configurations (one take of 2,158, at a
  tie). The digests of 2026.2 are the new reference (Verification).

### Performance

* **Handles** (009, merged in `98981f8`). A memory pointer holds its
  pointee's handle, and eviction replaces the handle's object, not the
  pointers:
  * eviction without the sweep that stopped the world: CLOCK over the
    node table, in batches that end after 2 ms, and a reader's load over
    the trigger waits up to 2 ms;
  * reads of resident nodes without a lock, each pointer read with an
    acquire (015-14); the pointer locks gone;
  * the node table in 4,096 maps with a lock each, so a resize stops one
    map for 0.23 ms, where it took 11.6 ms; reads no longer synchronize on
    `readSync`;
  * the resident bytes count the handles (015-13, `0b739f3`): each live
    handle with its node-table entry, 79 bytes, and 32 bytes for each
    pointer that holds one, as 009-02, 4.7 says; at a given cache size
    about a third fewer objects stay in memory than in 2026.1. The
    constants are JDK 27's, with compact object headers; on other JVMs
    they are an estimate;
  * an exception in a batch of the eviction thread fails the database
    (015-25, `4d56c2d`), where it ended the thread and eviction with it;
  * measured during the work, against 2026.1 (009-03; docs/levels.md,
    section 7): the longest get from the OS cache at 10M keys under ZGC
    3.45 ms, against 7.3 s; gets in memory from 8 threads 101 and 61
    percent more (G1, ZGC); loads in memory 8 to 20 percent slower. These
    figures are before 015-13 and 015-14; the release's own runs against
    2026.1 are in Baseline. Gets in memory from one thread are 9 and 13
    percent fewer (G1, ZGC) in those runs; 009-03 had 3 and 11.
* **MEM**, heap bytes per KV: 129 to 130 since handles, against 191 in
  2026.1 (`level1.sh`'s limit lowered from 228 to 131).
* **Group commit** (005-48, `d8ed1aa`). A sync that waits has the buffer
  written at once, and transactions that arrive during a force go out
  together: on s1, one thread's durable commits went from 38 to 213 a
  second.
* **The default buffer time is 50 ms** (005-64, `ceef804`), where it was
  20 ms; also for replicas added through the Pub API (the Core's replicas
  keep 2,000 ms). A writer that does not sync gets fewer forces, 11 to 14
  percent on F53 and 18 to 35 on s1, with the same throughput, latency and
  CPU; a rare sync beside a writer that does not sync is up to 22 percent
  slower (s1). For data that is not synced, a power loss or a crash can
  take about twice as much: the writes of about 1.1 to 2 buffer times,
  never more than the 10 MB buffer. What a sync has returned for is never
  lost.
* **A quarter-full write buffer wakes the storage thread** (005-76,
  `9d34ac1`), where it waited for the next timer check; it mattered at
  high write rates and long buffer times.
* **Reads do not wait for the writer** (005-46, `1165c90`): a read of the
  stream's last file no longer waits for the writer's append and its
  force, nor for a new file's force or reclaim's deletes of cut files (a
  thread of their own, `FileStream-cut`); an encrypted database's reads
  no longer wait for each other.
* **Startup without header reads** (005-57, `e773562`). A start finds the
  nodes of the startup section's pointers by their position instead of
  reading a header for each: a cold start of 10M keys on s1 took about 46
  and 51 s at startup distances of 50 and 200 MB in the prototype, where
  it took 214 and 210 s.
* **Index writes in proportion to each commit, and bounded startup**
  (005-49; 007-03, step 3; 007-07; `b8ac8a1`). Each commit writes its
  share of the dirty index nodes, in proportion to its size, so that the
  startup section stays near the startup distance, and a deadline takes
  every transaction that begins twice the startup distance or more before
  the end of the stream. At 10M keys the largest record of a run is 0.34
  to 1.9 MB, against 2.6 to 4.6 MB with the take before; a put costs 24
  and 36 percent more stream at startup distances of 50 and 200 MB, and
  13 percent less at 1000 MB (docs/levels.md, section 5).
* **Calm when idle**: an idle eviction thread waits with no timeout, where
  it woke once a second, and `close()` returns after it has ended (005-51,
  `043a09c`). A reader's load skips the eviction monitor when a request to
  the eviction thread is pending (005-65, `52aeb04`).

### Documentation

* `Database.stop()`'s and `Db.stop()`'s Javadoc corrected (`d9d350d`):
  2026.1's said that the files are not forced and that only
  `sync(STRONG)` forces them. `FileStream` forces every append, so
  `sync()` waits until the data is on the device, and `STRONG` adds the
  replicas.
* `DatabaseBuilder.startupDistanceInMb`'s Javadoc said 5 to 100 MB; the
  code has always clamped to 5 to 1000 MB.
* Replication's Javadoc says that it is experimental, has known faults,
  will change its API, and must not be used in production (016-04).
* `java/javadoc-pub.sh` builds the Pub API's Javadoc with doclint, and
  fails on any warning (`f342bd4`); it is the release's
  `bergdb-2026.2-javadoc.zip`.

### Build and tools

* `before-commit.sh` checks the package dependencies against each
  `package.html` (`java/deps.py`, 005-56) and refuses floating point in
  the Core Layer's decisions (`java/doubles.py`, 005-79).
* `java/stress/core-build.sh` builds the Core Layer alone (005-56).
* `java/stress/PauseProbe.java`, the longest waits of gets and commits
  under eviction (`732e567`), also with the budget lowered in a phase
  (005-52, `4d74c19`); jcstress tests in `java/stress/jcstress/`, among
  them a key node's growth (015-12).


The Lean model and the C clone
------------------------------

Only the Java code is the release (Frans, 2026-11-03); the Lean model and
the C clone are tools of the work.

**The Lean model** ([lean/README.md](../../lean/README.md)) covers, new since
2026.1:

* the model of handles, `SIS/Handle.lean`, and T-CACHE, T-READ, T2-C,
  T-READ with restarts and T-PIN over handles (009); the trace checker's
  C-H compares Java's handle state with the model;
* rule 4 by position, proved to link what rule 4 by node id links, also
  after a cut (005-58, 005-62);
* T9 and T12 over handles, and startup with handles; the model before
  handles is removed (005-62);
* T3 for BergDB's take (007-08).

Where this release's Java is not in the model:

* 005-79's integers: the model's take (`share`, `dither`, and `javaTake`
  in the conformance) keeps the double share and dither of 2026-10-28. On
  its 300 cases the integer take gives the same startup pos; at a tie the
  two can differ by a node (015-03, after the release).
* Concurrency, resource bounds and the Pub API are outside the model, as
  before (Known issues).
* The fixes made for the release (005-69, 005-79's reclaim and eviction
  parts, 005-82, 015-01, 015-07, 015-10, 015-12 to 015-15, 015-17, 015-20
  to 015-22, 015-24, 015-25, 015-40, 015-56) changed Java only. Each is in
  a part that the model leaves out (the parsers, the resident count, the
  memory model, the start of a directory, the Pub API's layers), or, for
  015-10 and 015-25, in the eviction thread's schedule, for which the
  model proves the same records and answers whatever it is; so the
  alignment above stands. The only change to `lean/`
  since `9d34ac1` is a sentence of lean/README.md on the integer take.

**The C clone** (item 012) is not updated: it writes the bytes of the
Java it last ported, before 005-79's take and 005-69's clock, and its
cross tests would differ on the take (015-02, after the release).


Verification
------------

On the release commit, in a clean clone (`baseline.zip`, `gates/`):

`java/night.sh` on `c846c0c`, 2026-11-04 02:10 to 02:48 (`NIGHT OK`, 38
minutes, JDK 27). The release commit differs from it in 015-56's fix
(`1613a45`) and `BuildInfo`, and passed `before-commit.sh` itself
(`BEFORE COMMIT OK (107 s)`, 2026-11-04 07:59 to 08:01):

| Step | Result | Time |
|---|---|---|
| `before-commit.sh`      | BEFORE COMMIT OK | 109 s |
| `stress/core-build.sh`  | CORE BUILD OK    | 45 s  |
| `level1.sh`             | LEVEL 1 OK       | 112 s |
| `level2.sh`             | LEVEL 2 OK       | 553 s |
| `level3.sh`             | LEVEL 3 OK       | 397 s |
| `level4.sh`             | LEVEL 4 OK       | 781 s |
| night tests             | SUCCESS, 8 tests | 136 s |
| `conformance.sh medium` | CONFORMANCE OK   | 144 s |

* Lean: `lake build` of every proof (in the level scripts); the theorems
  that [lean/README.md](../../lean/README.md) lists for `#print axioms`,
  44, each depend on Lean's standard axioms only (`propext`,
  `Classical.choice`, `Quot.sound`, or a part of them; no `sorry`).
* The tests again on the jar itself, with `-ea`, on F53 with JDK 27
  (OpenJDK 27, Homebrew) and JDK 17 (17.0.21): 1,143 unit tests, 79
  f-tests and 8 night tests on each, all passed (142 and 145 s); on s1
  (Linux, 2 cores, 3 GB) with JDK 27 and 17 (17.0.21): the 1,143 unit
  tests and 79 f-tests passed on each; the 8 night tests passed with
  `/tmp` on the disk (171 and 185 s), after a first run failed in
  `BryanIssueNight` with "No space left on device", as s1's `/tmp` is a
  1.9 GB tmpfs that the tests' temporary files fill (015-11, the test
  setup, not BergDB).
* A user's program, compiled against the jar alone from the Javadoc
  (`baseline.zip`, `tools/userprog/`): it creates a database, commits,
  syncs and closes it, then in a new JVM reads it back, writes and closes:
  `USERPROG OK` with JDK 27 and 17, on F53 and on s1.
* StreamDigest: 2026.2's 12 configurations in 3 modes, the modes agree
  (`baseline.zip`, `f53/digests.txt`, the reference for later versions).
  2026.1's jar, run again on the same workloads, gives its release's
  digests, 36 of 36, so the workloads are the same. 2026.1 against 2026.2:
  the decided digests differ in all 36, by design, as the paced take
  (007-07) and the integer take (005-79) change the records; the physical
  cut's fields differ by timing (015-08).

**The search for unknown faults** before the release (016-01, section 6):

* Reviews of what changed since 2026.1 and of the Pub API's promises,
  each by a reviewer that did not write the code (016-06, 016-07): R1
  (handles and the node table), R2 (`FileStream`), R3 (the threads and
  the lifecycle), R7 (`Db` and reclaim), R8 (the Pub API, its lifecycle
  and its promises), S1 (rw-transactions, encryption, JMX), S2 (indexes
  and objects), and a review of the index fixes. R4 (eviction), R5
  (`BufferedStream`, `StorageManager`) and R6 (startup and the take) ended
  on the release's morning, R4 early, after its faults were written; their
  faults are 015-66 to 015-83.
* Each fault found is registered in 015 (from 015-12 on), with whether
  2026.1 has it. Those of R1, R2 and R3 were each verified by a failing
  test or a probe, and, for a race, by its interleaving checked by a
  second reviewer (verify-1, verify-2). Those of S1, S2, R7, R8 and the
  index fixes' review have the reviewer's own test or probe, and no second
  check yet.
* Fixed before the release: from the reviews, 015-12 to 015-15, 015-20 to
  015-22, 015-24, 015-25, 015-40 and 015-56; from the tests, 015-10 and
  015-17 (and 015-09 and 015-16 in the tests). The faults that are new in
  2026.2, or that give a wrong answer in normal use, were fixed; the others
  are known issues, and the release did not wait for them (Frans,
  2026-11-04).
* Left for after the release: `night.sh large` on the release commit
  (015-18).
* Tests beyond the gates (016-08): jcstress in default mode on F53 and s1
  (no forbidden outcome); `before-commit.sh` and the night tests with JDK
  17 on F53, and with JDK 27 and 17 on s1, the first runs on Linux on
  record; the stress programs with fresh seeds, about two hours on F53
  (3,407 runs) and on s1. Their failures were 015-17 (a get during a
  close, on F53 and once on s1, fixed in `bce685c`) and 015-16 (the
  power-loss tester's cleanup). `level1.sh` does not fit s1 (3 GB).
* Every change made for the release was reviewed before its commit by a
  reviewer that did not write it (016-05, section 5), and gated by
  `before-commit.sh`.


Release Props
-------------

As in the log of 2015 (F1-007). Props (`bergdb.dev.props.Props`; lower is
better): MEM, heap bytes per KV; CORE, the four Core tests against cissi's
times of July 2013; SS, stream bytes per user byte.

| Release, machine, date | MEM | CORE (get, get4t, getmany, set) | SS (SS1, SS2, SS3, SS4) |
|---|---|---|---|
| 2015.4, cissi, 2015-07-27 | 161 | 0.78 (0.77, 0.99, 0.85, 0.58) | 1.48 (1.16, 1.26, 1.60, 2.06) |
| 2026.1, F53, 2026-10-25   | 191 | 0.29 (0.26, 0.35, 0.26, 0.32) | 1.50 (1.10, 1.19, 1.62, 2.37) |
| 2026.1, F53, 2026-11-06   | 192 | 0.29 (0.26, 0.32, 0.26, 0.31) | 1.50 (1.10, 1.19, 1.62, 2.37) |
| 2026.2, F53, 2026-11-06   | 129 | 0.24 (0.26, 0.17, 0.25, 0.32) | 1.51 (1.10, 1.20, 1.65, 2.40) |

2015.4 ran on Java 7, 2026.1's first row is its release's, on JDK 27 (the
median of 5 runs). The last two rows are 2026.1 and 2026.2 in turns
(ABBAAB) on F53 with JDK 27, in the quiet block of Baseline (below), each
figure the median of 3 runs (016-10): 2026.2 has a third less heap per KV
(129 against 192), and its gets from 4 threads (get4t) take about half
the time.
MEM and SS do not depend on the machine; CORE does. SS depends on the
startup distance and the take, which 2026.2 changed (005-49).

Lines of code (files in git at the release commit):

| Part | Files | Lines |
|---|---|---|
| `java/src`        | 256 | 74,652 |
| `java/src-dev`    | 122 | 13,914 |
| `java/src-icu`    | 2   | 194    |
| `java/stress`     | 37  | 12,514 |
| `lean`            | 120 | 52,271 |
| `docs` (Markdown) | 7   | 4,683  |

2026.1's, in the same way: 250, 123, 2, 24, 115 and 20 files; 65,958,
13,904, 194, 10,765, 47,347 and 13,712 lines. `docs/` holds only what is
kept up to date since 2026-10-26 (006-07).


Baseline
--------

2026.2 against 2026.1, as planned in 016-10: both jars in turns, on the
same machine and JDK, with each tool compiled once per jar; every
ScaleBench run at a startup distance of 200 MB, with both jars (2026.1's
baseline was at 10 MB, so its published figures are not compared); Props
(Release Props, above), the quick suite (`performance.sh ab`), ScaleBench
at 10M keys on F53 and at 1M and 10M keys on s1, and the pause probe.
Added on 2026-11-07 (Post-release notes). All outputs, GC logs included,
are in `baseline.zip` (`f53/`, `s1/w7/`, and the tables in `tables.md`),
with the scripts (`tools/`).

* **F53**: as in Identity; Homebrew's OpenJDK 27; AC power; a quiet block
  on 2026-11-06 from 22:00 to 23:16, after two checks in a row with a
  1-minute load below 2.5 (1.81 and 1.86), with no other build or test
  and every other Claude session idle. In the runs the other processes
  took 0.12 to 0.32 cores of 10, with short peaks of 0.45 to 0.86 in M's
  ZGC runs.
* **s1**: Frans's VPS (AMD EPYC, 2 virtual CPUs, 3.8 GB, Linux), OpenJDK
  27+35, G1; one run of each on 2026-11-04 from 08:17 to 08:39, the
  morning of the release. 6 of its 10 runs gave figures (below).

**ScaleBench, 10M keys of 24 bytes on F53**, one run each. M: everything
in memory, no eviction, a 6 GB heap. C: the stream in the OS cache, a
cache budget of 665 MB, a 2,660 MB heap, on the databases of M's ZGC
runs. Cells: 2026.1 / 2026.2.

Gets from one thread, uniform keys, a second; latencies from the timed
pass:

| Run           | Gets/s      | p50               | p99               | Longest get       |
|---------------|-------------|-------------------|-------------------|-------------------|
| M, G1         | 722k / 657k | 1.33 µs / 1.46 µs | 1.92 µs / 2.10 µs | 25.6 µs / 30.9 µs |
| M, ZGC        | 610k / 532k | 1.50 µs / 1.71 µs | 2.05 µs / 2.59 µs | 52.1 µs / 50.5 µs |
| C 665 MB, G1  | 177k / 265k | 4.96 µs / 3.29 µs | 11.5 µs / 8.96 µs | 176 ms / 45.6 ms  |
| C 665 MB, ZGC | 166k / 254k | 5.21 µs / 3.55 µs | 12.8 µs / 9.73 µs | 272 µs / 276 µs   |

Gets from 4 and 8 threads, a second; the longest batch of the eviction (a
sweep in 2026.1); the GC:

| Run           | 4 threads       | 8 threads       | Longest batch    | Longest GC pause  |
|---------------|-----------------|-----------------|------------------|-------------------|
| M, G1         | 2.06 M / 2.26 M | 2.14 M / 4.12 M | —                | 721 ms / 394 ms   |
| M, ZGC        | 1.85 M / 1.98 M | 2.15 M / 3.62 M | —                | 0.01 ms / 0.01 ms |
| C 665 MB, G1  | 168k / 740k     | 134k / 610k     | 4.78 s / 45.0 ms | 231 ms / 149 ms   |
| C 665 MB, ZGC | 143k / 612k     | 114k / 609k     | 6.82 s / 21.0 ms | 0.02 ms / 0.03 ms |

* Full GCs with G1: 4 / 4 in M, 53 / 1 in C; none with ZGC.
* The load (M): 41.7 / 45.9 s with G1, 48.8 / 55.8 s with ZGC; heap per
  key 244 / 185 bytes with G1, 315 / 225 with ZGC; on disk 187 / 231
  bytes a key.
* ScaleBench's runs from the OS cache with a 133 MB budget, which 2026.1's
  baseline had, are not here: a 600 MB heap (that baseline's) does not
  start a 10M database at a 200 MB startup distance, in either version
  (out of heap in the start's rerun of the transactions, on F53 and on s1;
  019-45).

**Against 2026.1:**

* In memory (M), 2026.2 has 9.0 and 12.7 percent fewer gets from one
  thread (G1, ZGC), and 92 and 68 percent more from 8 threads. The
  one-thread gap is outside one run's spread (G1's five windows: 711,694
  to 728,344 against 655,185 to 660,784 gets a second), was 7.8 percent
  in the night before (not quiet), and shows in the quick suite's
  one-thread gets (below). 009-03 had 3 and 11 percent (Changes,
  Performance).
* From the OS cache (C), 2026.2 has 50 and 53 percent more gets from one
  thread, 4.4 and 4.3 times as many from 4 threads and 4.6 and 5.3 times
  from 8. 2026.1's longest waits are its sweeps, which stop the readers.
  From 8 threads the longest get was 52.7 ms (G1) and 39.6 ms (ZGC) in
  2026.2, against 4.07 and 6.03 s in 2026.1; from 4 threads with ZGC,
  4.96 ms against 6.00 s (Limits: as many readers as cores).
* Loads in memory are 10 and 14 percent slower (G1, ZGC), and the heap a
  key 24 and 29 percent smaller. The stream is 24 percent larger, 231
  against 187 bytes a key, not yet explained; the take at 200 MB (005-49,
  Changes) is the likely cause.

**The pause probe** (009-03's PauseProbe, 1M keys, values of 100 bytes, a
cache budget of 100 MB, 4 readers, 60 s a phase, a 1,258 MB heap; times
in ms, the longest of the `tsize=1` and `tsize=1000` phases; gets in the
`tsize=1` phase; the longest batch of the eviction over the run, a sweep
in 2026.1):

| Run         | Gets       | Longest get | Longest commit | Longest batch |
|-------------|------------|-------------|----------------|---------------|
| 2026.1, G1  | 7,021,548  | 435.5       | 435.4          | 804           |
| 2026.2, G1  | 29,891,854 | 24.4        | 31.1           | 24.7          |
| 2026.1, ZGC | 6,539,045  | 562.9       | 562.6          | 1,163         |
| 2026.2, ZGC | 29,318,511 | 6.7         | 24.0           | 5.9           |

**The quick suite in turns** (`SUITE=quick performance.sh ab 2026.1
2026.2`, G1 with an 8 GB heap, 3 runs a scenario in ABBA order, medians,
one round; the CV at most 1.9 percent, but 6.4 for 2026.1's
`mix.gets_per_s`; every metric in `tables.md`):

| Scenario, metric                  | 2026.1    | 2026.2    | Change  |
|-----------------------------------|-----------|-----------|---------|
| r-1k-fin, mix.gets_per_s          | 1,972,530 | 2,315,870 | +17.4 % |
| r-1k-fin, mix.commits_per_s       | 49,423.2  | 52,271.4  | +5.8 %  |
| r-1k-fin, startup.sec             | 0.7122    | 0.7084    | −0.5 %  |
| read-1k, get_latest               | 1,318,610 | 1,251,380 | −5.1 %  |
| read-1k, get_historical           | 1,261,980 | 1,217,060 | −3.6 %  |
| read-1k, get_latest_mt4           | 3,552,820 | 4,261,600 | +19.9 % |
| read-1k, get_longkey              | 954,804   | 856,410   | −10.3 % |
| read-1k, scan_fwd.kvs_per_s       | 3,746,100 | 3,816,020 | +1.9 %  |
| read-1k, scan_back.kvs_per_s      | 3,977,370 | 3,983,000 | +0.1 %  |
| read-1k, scan_fwd_hist.kvs_per_s  | 3,491,600 | 3,474,620 | −0.5 %  |
| w-uni-1k-fin, commits_per_s       | 63,318.1  | 64,225.0  | +1.4 %  |
| w-uni-1k-fin, restart.startup_sec | 0.6107    | 0.6191    | +1.4 %  |
| w-uni-1k-inf, commits_per_s       | 102,066.0 | 99,371.1  | −2.6 %  |
| w-uni-1k-inf, restart.startup_sec | 0.6384    | 0.6357    | −0.4 %  |

`get_latest` and `get_longkey` were flagged, worse by more than 5 percent
in every run; with one round, not confirmed. `get_longkey` was flagged in
the night before too.

**ScaleBench on s1** (G1, startup distance 200 MB, keys of 24 bytes, one
run each; 2026.1 / 2026.2; "none" where the run ended with
`OutOfMemoryError` in the database's start). s1's half is the run of
2026-11-04 as it was; its gaps are not redone (016-10).

* Load, 10M keys, a cache budget of 600 MB, a 2,500 MB heap: 337 / 245 s
  (30k / 41k puts a second); longest batch 21.7 s / 208 ms; longest GC
  pause 404 / 207 ms.
* M, 1M keys, a 1 GB heap: load 9 / 4 s (106k / 248k puts a second);
  649k / 642k gets a second from one thread, p50 1.38 / 1.33 µs, longest
  1.23 ms / 76.4 µs; 917k / 1.12 M from 4 threads; longest GC pause 472 /
  261 ms.
* C, 1M keys, a cache budget of 66 MB, a 512 MB heap: 2026.1 none (out of
  heap in the eviction's sweep during the start); 2026.2 540k gets a
  second from one thread, p50 1.47 µs, longest 1.44 ms; 1.09 M from 4
  threads; longest GC pause 173 ms.
* D, as C with the OS cache dropped and the JVM in a cgroup: 2026.1 none
  (as C); 2026.2 a cold start of 6.7 s, then 599k gets a second from one
  thread, p50 1.30 µs, longest 101 µs; 1.20 M from 4 threads; longest GC
  pause 152 ms.
* D, 10M keys, a cache budget of 133 MB, a 600 MB heap: none in either
  version (the 133 MB runs above).


How to compare a later version
------------------------------

Run 2026.2 again beside the later version, in turns, on the same machine
and JDK, rather than compare with the numbers above.

* **One compiled copy of each tool per jar.** Since 2026.1 the tools'
  imports changed (`SyncLevel` moved, 005-56; `PauseProbe` uses
  `FileStreamIo`, 005-46), so a copy compiled against one jar may not run
  on the other. `baseline.zip`'s `tools/` has the scripts that compile
  each tool for each jar (016-10, section 1).
* **Props**: `java -cp JAR bergdb.dev.props.Props`, with each jar in turn;
  Props is in each jar.
* **performance.sh**: in a clone at the tag, `java/stress/performance.sh
  build 2026.2` (a preserved build in `java/build/perf/builds/`); then, in
  the later tree, `SUITE=quick performance.sh ab 2026.2 current`, which
  alternates the two and compares. The harness of the later tree must
  compile against 2026.2's jar.
* **StreamDigest**: its reference is `baseline.zip`, `f53/digests.txt`.
  Compile the later tree's `java/stress/StreamDigest.java` against each
  jar, run each copy on its jar, then `compare`. Its compare also reports
  the physical cut's fields, which depend on timing (015-08); compare the
  decided digests.
* **ScaleBench** (`items/004-indirect-swizzling/02-scale-tests/`): as in
  `tools/`, with 005-65's `prep.sh`, which patches and compiles it per jar.


Known issues and limits
-----------------------

**Replication** (`DatabaseBuilder.replica`, `Database.addReplica`) is
experimental, with known faults; its API will change, and it must not be
used in production (005-11; docs/levels.md, section 9).

**Faults known at the release, not fixed** (each with its entry):

* **Holes in an unforced tail** can refuse a start or fail a later read,
  after a power loss (014-01, found in 005-83). In 2026.1 too.
* **A failed append's transaction was visible**: a get that runs while a
  put's append fails can see the put's values before the failure (015-27;
  docs/levels.md, section 3). The text is corrected; the code is for after
  the release (Frans, 2026-11-04). In 2026.1 too.
* **The retain duration is not kept in the stream** (005-78): a start
  takes the builder's value, though it decides what reclaim writes; a
  database opened with another retain duration than it ran with reclaims
  by the new one.
* **A start on an empty or missing directory creates a database** (015-05;
  015-01's case 3: a volume not mounted, a wrong path). Check that
  `created.txt` exists before `start()` for a database that should be
  there (`DatabaseBuilder.dir()`'s Javadoc).
* **A start refused after the open** (a clock out of range, a bad replica)
  on a directory without a stream file leaves an empty first stream file
  and `bergdb.lock` (015-06, the rest).

**The index and object layers** (indexes, `DbObject`, rw-transactions)
have known faults, found by the reviews before the release, all in 2026.1
too (Frans, 2026-11-04). None is fixed in 2026.2; each has its entry in
[items/015-todo/](../../items/015-todo/readme.md):

* indexes: a write racing an index's creation is never indexed (015-28);
  `deleteIndex(Database.PRIMARY)` throws a `Bug` and leaves the primary
  deleting (015-29); a build step scans past its directory (015-30); an
  interrupted `deleteIndex` leaves the index deleting with no job
  (015-36); an interrupted retry of a build step ends the build for the
  run (015-37); a build's status object reads the worker's changing
  counter (015-39); index work reads the indexes before the read time, so
  a new or deleted index is missed (015-43); a `String` or `byte[]` at an
  object key in an indexed directory breaks the index (015-46); a
  refused deletion leaves the index active and unmaintained (015-23); a
  deletion job that `stop()` ends early reports "Done! Deleted" (015-61);
* objects and rw-transactions: a `String` or bytes and an object, or a
  delete, of one key lose their call order (015-41); `rw()` changes a
  connection's frozen lookup time (015-42); a `byte[]` value is shared
  with the caller, so a change of the array changes the value in memory
  (015-47); `exists()` after `freezeLookupTime()` freezes the read before
  (015-48); `getLookupTime()` of a new connection throws (015-59);
  `Database.connection()` keeps a connection for every thread that called
  it (015-60); `transactionInfo()` after a get that found nothing throws
  (015-62); a key's replace replaces only its last `${transactionTime}`
  (015-64);
* review S2's 27 faults of the indexes and the objects, to be verified and
  split (015-49).

**Other faults found by the reviews, not fixed** (in 2026.1 too, but
015-52):

* storage: a cut at the stream's length throws an internal `Bug` (015-31);
  an unchecked failure during an open leaks handles, and an `Error` keeps
  the lock (015-32); `setMax2G(true)` still allows files over two billion
  bytes (015-33); a storage thread interrupted at its stop skips closing
  its stream (015-34); a failed background write fails the database only
  at a caller's next storage call (015-35); `FileStream.append` with a
  negative length corrupts the stream's length, internal only (015-26);
* the Core and reclaim: a reclaim step that rewrites old values beyond the
  value limit fails the database, at every restart (015-50); a value
  transformation's result is not size-checked (015-51); `execute()` can be
  refused with a `LookupTimeNotAvailableException`, which its Javadoc does
  not list (015-52, likely new in 2026.2, rare); a transaction that runs
  when `stop()` comes is committed, but `execute()` throws (015-53);
  `markSafePositions`'s Javadoc, no harm shown (015-54); a user
  transaction at the last database time makes reclaim's next internal
  transaction fail the database (015-55);
* the Pub API's utilities and the lifecycle: `Time.resolve(TimeZone,
  String)` ignores its time zone (015-57); `TestClock.setTime()` refuses
  the clock's current time (015-58); `Time.toString()` is not safe from
  several threads (015-63); a second `start()` of a `memory()` builder
  whose database runs is not refused (015-65); JMX's monitor thread ends
  on an interrupt (015-38); `cryptoKey(CryptoKey.NULL)` after a key keeps
  the key (015-44); `CryptoKey` has `equals()` and no `hashCode()`
  (015-45).

The faults of reviews R2 and R3 (015-20 to 015-27, 015-31 to 015-39) were
verified by a second reviewer; those of the index fixes' review (015-28 to
015-30), of S1, S2, R7 and R8 (015-40 to 015-64) and 015-65 have the
reviewer's own test or probe, and no second check yet.

**The last reviews' faults** (R4, R5, R6; registered on the release's
morning, with the reviewer's own test or probe):

* startup: a record whose size field is larger than its content is
  accepted, and the records it covers are lost (015-72); a corrupt
  `startupPos` in the last record is accepted, and the transactions before
  it are lost (015-73). A start then accepts a corrupt stream and loses
  committed data; in 2026.1 too. Also: checks of stream data at a start
  that are asserts (015-75), and comments and Javadoc that do not hold
  (015-74, 015-77); `Db.setStartupDistance` clamps to 400,000 to 10^9
  bytes without saying so, Core API and JMX only (015-76, new in 2026.2);
* eviction: a failed eviction batch releases the write lock before the
  database fails, a gap in 015-25's fix (015-66, new in 2026.2); a batch
  goes through a whole map past its handle limit (015-67); startup leaves
  large values in the writer's admission list (015-68, new in 2026.2); a
  test schedule's resync overwrites readers' accounting (015-69); a
  decrease of the budget can settle above it although the pins fit
  (015-70, new in 2026.2); the audit reports a valid cleanup as a bad
  table entry (015-71, new in 2026.2). Memory and the audit only, no data;
* `BufferedStream` and `StorageManager`, all in 2026.1 too: the consumer
  discards the first storage-close `IOException` (015-78); a negative
  append decreases `StorageManager`'s length (015-79); the buffer issues
  concurrent writes to a single-writer stream (015-80); an unchecked close
  error can end the consumer before a failed append is published
  (015-81); a pending cut that arrives during another cut can be left
  unapplied after a close (015-82); a read past the end throws an
  `IOException` instead of the documented `EOFException` (015-83).

**Limits:**

* **Collectors**: G1 pauses and runs full collections under eviction, and
  generational Shenandoah stops; use ZGC, or Shenandoah without
  generations (Requirements).
* **As many readers as cores**: gets of up to 39 ms with 8 readers and
  ZGC's workers on F53's 10 cores (005-65; accepted as a full machine).
* **A decrease of the startup distance at 50M keys**, from 1000 to 100 MB:
  the largest records are 13 to 15 MB (005-77).
* **A small commit after a large transaction** can write that transaction
  whole (007-07, sections 7.1 and 7.2).
* **D's bound is loose**: 1.6 to 2.9 times the startup distance (005-38).
* **The default startup distance** (50 MB) suits up to about 10M keys;
  beyond that, use 200 to 1000 MB (005-38; 010-01, P10).
* **Loads in memory** are 8 to 20 percent slower than before handles
  (docs/levels.md, section 7).
* **Bounded startup**: T3 is proved for the take; T4, and a cold start's
  reads, are not proved (007).
* **The files after a physical cut** depend on timing; the bytes from the
  decided cut do not (005-72).
* **Overload**: there is no admission control, and rw-transactions retry
  with fixed exponential sleeps from 10 ms (005-81).
* **Concurrency** is outside the Lean model, and is checked by tests and
  reviews only (005-07).
* **Power loss**: physical power cycling, other storage and Windows are
  not established (docs/levels.md, section 8); network file systems are
  not tested.
* **JDKs and systems**: tested on JDK 27 and JDK 17, on macOS (F53) and
  Linux (s1); not on Windows.
* **The documentation** is not reviewed for users.


Post-release notes
------------------

A fault found later that affects 2026.2, its numbers or its correctness,
is recorded here. No fault yet.

**Changes of these notes:**

* 2026-11-07: the numbers against 2026.1 that the notes said would follow
  (016-10): Release Props' last two rows and Baseline, from a quiet block
  on F53 on 2026-11-06, and s1's runs of 2026-11-04 with their gaps;
  `baseline.zip` with their outputs, and its line in `SHA256SUMS`. In
  Changes, Performance, the gets in memory from one thread are these runs'
  9 and 13 percent fewer, not 009-03's 3 and 11. The jar, the source zip
  and the Javadoc zip did not change.
