Notes for the next release
==========================

What the release notes of the next release after 2026.1 must say, collected
here as the changes are made, so that the release does not have to find them
again. The release folds them into its `releases/VERSION/readme.md`, as
[2026.1](2026.1/readme.md) has them under "Changes since 2015.4", and
empties this file.


Requirements
------------

* **Java 17 or later** (bergdb 009, step 1-0, 2026-10-25, `b10e072`).
  `java/build.sh` and `performance.sh` compile with `javac --release 17`,
  where 2026.1 had `--release 8`; the jar no longer runs on Java 8 to 16.
  The one incompatible change of the requirements, so it comes first.
* **ZGC, or Shenandoah without generations** (bergdb 004-04, 009-04;
  2026-10-26 and 27; `62ad470`, `3c02f11`, `45c5e43`). With eviction,
  G1 pauses for hundreds of milliseconds and runs full collections, and
  generational Shenandoah stopped for 821 ms in a soak with an 8 GB heap;
  ZGC paused below 0.1 ms, and Shenandoah in its default mode at most 4.1
  ms (docs/levels.md, section 7). BergDB runs with any collector; its
  pause target of about 20 ms (009) is for its own code, and the
  collector's pauses come on top.


Reliability
-----------

* **NaN reclaim fractions are refused** (bergdb 005-73, F4, 2026-11-02,
  `3ad171d`). `Db.setReclaimInternalFraction(double)` throws
  `IllegalArgumentException` for NaN and leaves the setting unchanged. The
  double API and inclusive range 0.001 to 0.90 stay the same.

* **Close reports storage failures** (bergdb 005-73, 2026-11-02, `3ad171d`).
  `Db.close()` and `Database.close()` throw `StreamIoException` when the
  final flush or storage close fails, after cleanup. A later `close()`
  also reports a failure from an asynchronous `stop()` or an earlier
  `close()`. A try-with-resources block suppresses the close failure when
  the block itself throws. Before, these I/O failures were discarded. A get
  that runs while another thread closes the database and reads a file the
  close has closed fails alone, with an `IOException`, and the close does
  not report it (bergdb 015-17, 2026-11-03, `6105d21`; found before the
  release, in the work on it).

* **Corrupt startup times are refused** (bergdb 005-75, 2026-11-02,
  `0e61856`). Startup checks record order, the 56-bit range of record times,
  and increasing times within stored key nodes before replay. Violations
  raise `StreamFormatException` with assertions enabled or disabled. Valid
  stream bytes and the format are unchanged. Core stream appends also check
  the size at the supplied buffer offset.

* **Corrupt sizes are rejected before allocation** (bergdb 005-74, option A,
  2026-11-02, `c229ab2`). Record and node reads check that the declared
  bytes exist, excluding meta blocks, before allocating their buffers. The
  transaction parser refuses negative or undersized nodes and confines nodes
  and the got-dirty list to the declared record, even in a larger reused
  buffer. Malformed sizes raise `StreamFormatException` instead of looping
  or exhausting the heap. Valid stream bytes and the format are unchanged.

* **Node fields are checked** (bergdb 015-07, 2026-11-03, `12610c7`). A
  node whose checksum is right but whose key count, value size, key size
  or pointer count does not fit in the node is refused by its parser with
  a `StreamFormatException`, and the read fails the database, as for
  005-74's sizes. Before, such a node threw an
  `ArrayIndexOutOfBoundsException` or a `NegativeArraySizeException` in a
  load, which escaped the reads' failure handling (`getOne`, `getMany`,
  the reads of a transaction), and the database stayed active.

* **A corrupt record read by `transactionInfo()` fails the database**
  (bergdb 005-82, 2026-11-03, `3e32f02`). `Db.getTrans` parsed the record
  outside its failure handling, so a node's checksum or a malformed record
  made it throw as it was, with the database still active. Now a
  `StreamFormatException`, and any other runtime exception of the parse as
  its cause, fails the database as every other read does, and keeps the
  cause. Only the live read changes: how a start handles a damaged tail
  stays as it is (014-01, a known issue).

* **STM read sets after reopening** (bergdb 005-70, 2026-10-30, `7d967d7`).
  The Core refuses a transaction with a read dependency whose snapshot
  predates the last recovered commit. Before, the empty STM history could
  accept it despite a conflicting write before the close. A snapshot at the
  last recovered commit is covered. The stream format is unchanged.

* **Reclaim spaces its iterations by the live startup distance** (bergdb
  005-61, 2026-10-27, `a175840`). Before, it used the builder's value,
  taken before `start()` read the stream's, so a database made with a
  small startup distance and opened with the default builder nearly
  stopped reclaiming.

* **A key node's growth is published safely** (bergdb 015-12, 2026-11-03,
  `dc42409`). A key node that grew stored its new arrays with plain
  stores, so a reader on another thread could see the new arrays before
  their contents: a search could miss a key that was there long before
  its lookup time, or return the value of a later or uncommitted
  transaction. Rare (8 misses in 477 million searches in a probe; none
  seen through a database), on AArch64. A release fence ordered the
  copies before the stores (`dc42409`); since 015-14 the node's array
  fields are volatile, and the fence is gone.

* **The fast path reads every pointer with an acquire** (bergdb 015-14,
  2026-11-03, `4e10aa2`), so that a lock-free read is correct by the Java
  Memory Model, not by the hardware's address dependency: a key node or a
  top node reads each pointer with an acquire, paired with the release
  store of each change in place, then its reference with an opaque read;
  a key node's array fields and `Handle.writtenPos` are volatile. Before,
  the plain read of a pointer to a handle allowed, by the JMM, a version
  older than the reader needed; HotSpot was not seen to give it. The cost
  on the read path is not measured: an estimate of seven more
  load-acquires a hop on AArch64, none on x86 (015-14).

* **A typed primary scan goes on after a page of non-objects** (bergdb
  015-20, 2026-11-03, `9971100`). A scan of `usePrimary` ended a page
  after 100 entries, filtered ones included, and took the empty page for
  the end of the range, so it left out every later object, without a
  word. In 2026.1 too.

* **An index deleted and created again under its name** (bergdb 015-21
  and 015-22, 2026-11-03, `377fe7d`, `7cd4cdb`). A second `deleteIndex`
  returns the running deletion's job, so an old job can no longer delete
  a new index of the name and its entries; an index build stops when its
  index is deleted, and writes nothing into a new index of the name, which
  returned extra objects, duplicates and the wrong order. Both lasted
  after a restart. In 2026.1 too.

* **The last call on a key in a transaction wins** (bergdb 015-40,
  2026-11-03, `f7974d3`), for put and delete in an rw-transaction. Before,
  every call on a key was kept and the last put won, over a delete
  whatever the order: a put and then a delete of a key committed the put,
  and of several puts an earlier value could win. In an index's own
  operations a put stays over a delete, as before. In 2026.1 too.

* **A directory whose stream is missing is refused** (bergdb 015-01,
  2026-11-03, `ed16384`). `created.txt` now marks a database whose
  creation reached the disk: a creation through the Pub API is forced
  before `created.txt` is written. `DatabaseBuilder.start()` refuses a
  directory that has `created.txt` and no `*.bergdb` file with a byte,
  with the new `bergdb.pub.util.DatabaseMissingException`, before it opens
  the directory: it creates and writes nothing. Before, a directory whose
  stream files were gone, or whose only file was empty, started as a new,
  empty database without a word. A start that reads a stream and finds no
  `created.txt` writes one ("creation date: unknown"). An empty or missing
  directory is still a new database (015-05, a known issue);
  `DatabaseBuilder.dir()`'s Javadoc says how to check for one. A start
  refused for its crypto key now creates nothing either: no directory, no
  `bergdb.lock`, no empty first stream file (015-06, in part).

* **`SystemClock` gives strictly increasing times** (bergdb 005-69,
  2026-11-03, `b281d39`), as its Javadoc said. Before, calls within a
  millisecond, or after the system clock was set back, gave equal or
  earlier times. No harm came of it: a database's own clock makes its
  times strictly increasing with any clock.


API changes
-----------

* **Broken Core diagnostics removed** (bergdb 005-73, 2026-11-02, `3ad171d`).
  `Db.getCachePutSize()`, `getDirtyFraction100()` and
  `getDirtyFraction1000()`, their JMX attributes, and JMX's
  `CachedMemoryValueSpeed` and `CachedMemoryValueSpeedM` are gone; the
  cache size was constant and the dirty fractions were incorrect.
  `Cache3.putSize()` and the unused `GetMany.cache` field are gone too.
  Core startup info now reports the effective startup distance instead
  of −1. Stream bytes and format are unchanged.

* **`stop()` or `close()` is required** (bergdb 005-55, 2026-10-27,
  `cec0032`). `Db.finalize()` is gone, with nothing in its place: nothing
  stops a database that the application drops. Until 2026.1,
  `Database.stop()`'s Javadoc promised that a `Database` that nothing referred
  to was stopped when the collector found it; that promise is gone. A `Db`
  or `Database` that is not stopped keeps its storage threads (one per
  stream), its open files, its write buffer and its memory until the JVM
  exits. What it has committed is still written within the buffer time, as
  after any commit; the storage threads are daemon threads, so they do not
  keep the JVM alive, and at its exit what is buffered and not yet written is
  lost, as in a crash, which the database tolerates. An application that
  stops each database it starts, as an application closes a file, sees no
  change. (Frans: "Typically there is only one database in an application.
  Calling close() is a reasonable requirement. And the database is
  crash-tolerant anyways.")
* **`Db` and `Database` are `AutoCloseable`** (bergdb 005-59, 2026-10-27,
  `f9c3b09`). A `try`-with-resources block closes a database when it ends,
  also when it throws. `Database` has a new method, `close()`: it stops the
  database as `stop()` does and waits until it is closed, as `Db.close()`
  does; `stop()` still returns at once. Every call of 2026.1 works as
  before.
* **Interrupts** (bergdb 005-46, 2026-10-27, `eaec93e`). An interrupt of a
  thread that calls BergDB never fails or hangs the database, as it could
  before (a commit that waited for room in the write buffer or made a cut
  failed the database; an interrupt of the storage thread stopped its
  writes). `sync()`, a job's `join()` and the wait before an
  rw-transaction's rerun end on an interrupt; every other call ignores it
  until it is done; the interrupt flag is always kept. The rule is in
  `Database`'s class Javadoc.
* **One database per directory** (bergdb 005-63, 2026-10-28, `322c5d1`). A
  `FileStream` takes an exclusive lock on a file of its own in the
  directory, `bergdb.lock`, before it reads anything, and releases it when
  it is closed. A second database on the directory, in the same JVM or in
  another process, is refused at once with a `DirectoryInUseException`
  (`DatabaseBuilder.start()` throws a `StreamIoException` with it as the
  cause); so is one started right after `stop()`, while the first is still
  closing: start it after `close()` has returned. Before, nothing refused a
  second database, and one started right after `stop()` could take files
  that the first was still deleting (005-46), and fail. The operating system
  holds the lock and drops it when the process ends, so a crash leaves none;
  the file stays, with a text for people. On a network file system a crashed
  client's lock may stay until the server notices (NFSv4: about 90 s), and
  where the file system supports no locks, a start fails. Two copies of
  BergDB in one JVM, loaded by two class loaders, refuse each other too:
  each copy records the directories it has locked as system properties,
  `bergdb.lock.` and a key, with the holder's token. Before that fix, made
  before the release, a copy's refused start released the other copy's lock
  (015-24, 2026-11-03, `c72a02b`).
* **`SyncLevel` is in `bergdb.pub.util`** (bergdb 005-56, 2026-10-28,
  `04f1546`). It was `bergdb.core.SyncLevel`, a class of the Core Layer in
  the Pub API's signatures (`Database.sync`, `Connection.sync` and
  `Transaction.sync`); now it is `bergdb.pub.util.SyncLevel`, with the same
  constants, `NONE`, `ORDINARY` and `STRONG`. Code that names it changes its
  import, from `bergdb.core.SyncLevel` to `bergdb.pub.util.SyncLevel`, and
  code compiled against 2026.1 that uses it must be compiled again.
* **The builder opens the directories in `start()`** (bergdb 005-66,
  2026-10-28, `83b7ac0`). `DatabaseBuilder.dir()` and `replica()` only
  record their directories; `start()` opens them, the database's first, and
  closes them again if it fails. So a builder that is never started holds
  nothing, where since 005-63 it held the directory's lock until the JVM
  ended, and so did the first of two `dir()` calls and a replica given
  before `dir()`. A replica given before `dir()` is now kept; before,
  `dir()` dropped it. A directory that cannot be opened, or that another
  database has, is reported by `start()`, with the same `StreamIoException`
  that `dir()` threw; `replica()` no longer throws its `IOException`. A
  start that is refused closes only the streams it opened itself: a
  second `start()` of one builder whose database runs, refused as the
  directory is in use, closed that database's stream, which then failed
  and lost its lock (015-56, 2026-11-04, `30e1b61`; a fault of the
  development, never in a release).
* **The startup distance changes while the database runs** (bergdb 005-53,
  2026-10-28, `fd8f513`). `Database.setStartupDistanceInMb(int)` and
  `getStartupDistanceInMb()`: the setter clamps as
  `DatabaseBuilder.startupDistanceInMb` does (5 to 1000 MB), and the new
  setting is in force when it returns, written to the stream with a small
  transaction of the database's own (a value of 200 kB), so that a restart
  keeps it. A call with the setting in force writes nothing, so an
  application may call it after every start; one on a stopped or failed
  database throws as a transaction does and changes nothing. After a
  decrease, the commits that follow bring the startup section down to the
  new setting, with no commit writing the whole of it (007-07). Until now
  only a new database could choose its startup distance through the Pub
  API.
* **The cache size changes while the database runs** (bergdb 005-52,
  2026-10-28, `fd8f513`). `Database.setCacheSizeInMb(int)` and
  `getCacheSizeInMb()`: clamped as `DatabaseBuilder.cacheSizeInMb` (4 to
  100,000 MB), in force when the setter returns, for this run only (a
  restart takes the builder's value). After a decrease the database evicts
  down to the new budget in batches that end after 2 ms
  (`Eviction.BATCH_NANOS`; a limit, not a measured bound: 3 to 4 ms on s1,
  009-03, section 0), also when no other call follows; since 015-10
  (2026-11-03, `24bdae5`), also when every object was just read, as the
  eviction thread goes on until two rounds of its hand free nothing. The
  rule for both setters: a setting that changes the stream's bytes, as the
  startup distance, is kept in the stream; one that does not lasts for the
  run. The Core's side: `Db.setCacheSizeIndicator(long)` and
  `getCacheSizeIndicator()` (`fd8f513`). A race in the setter, found and
  fixed before any release (`988fe1a`), could put back the old budget's
  trigger when a batch ended during the call; a test forces its interleaving
  (005-80, 2026-11-03, `522b645`).
* **`Factory` has no public constructor** (2026-10-29, `216fc8b`). It has
  only the static `Factory.database()`; `new Factory()` no longer compiles.
* **No .NET** (2026-10-29, `216fc8b`). `Util.runsIkvm()` in `bergdb.common`
  is gone, and the Pub API's Javadoc no longer names .NET or C#; BergDB runs
  on Java only.
* **`Database.PRIMARY` is no longer a compile-time constant** (bergdb
  005-56, 2026-10-28, `04f1546`). It is `Util.identity("primary")`, the
  same value as before, but a `case` label with it no longer compiles.
* **`DatabaseMissingException`** (bergdb 015-01, 2026-11-03, `ed16384`),
  new in `bergdb.pub.util`: `DatabaseBuilder.start()` throws it for a
  directory that has `created.txt` and no stream (see Reliability).
* **Internal only**: `PointerLocks` and `Db.Internal.getPointerLocks()` are
  gone (`7831909`); `Db.Internal.cacheStats()`, `writersWaiting()` and
  `takeWriteBufferWaits()` are new (`e23c96e`); `bergdb.stream.FileStreamIo`
  and `FileStream(File, FileStreamIo)` are public, for the power-loss
  tester (`3c807f1`).


Format
------

* **The node size is in the stream** (bergdb 005-50, 2026-10-27, `bf19075`).
  Every meta block holds the maximum node size the database was written
  with, in 2 bytes at offset 44 that were reserved; the meta block's version
  stays 154. A start with another node size is refused with a
  `StreamFormatException` that names both sizes, where it failed before with
  what looked like a corrupt stream, or started and could leave a stream no
  start opened. A stream written before, by 2026.1 or earlier code, is
  refused with a `VersioningStreamException`, before anything is written:
  databases of 2026.1 must be made again. (Frans: "No need to consider
  "today's databases". There are none.")
* **The Core decides in integers** (bergdb 005-79, 2026-11-03, `dde82e8`,
  `f04cefe`). No double or float decides the stream's bytes or the memory:
  the take's share and dither (in units of 2^-16 of a node), reclaim's
  iteration spacing and internal fraction, eviction's low watermark and two
  buffer sizes use 64-bit integers, which every language and target
  computes alike. Doubles stay at the API, converted at once, and in
  statistics; `java/doubles.py` checks it in `before-commit.sh`. The format
  is the same.
  * The paced take (005-49, new in 2026.2) decides in integers. Its choices
    differ in some records from its double rule of 2026-10-28, so the same
    transactions can give other bytes than during 2026.2's development.
    StreamDigest's decided digests change in 1 of its 12 configurations,
    l3-node14, where one take of 2,158 differs, at a tie that the integer
    rule stops at. The digests of 2026.2 are the new reference.
  * `Db.setReclaimInternalFraction(double)` and JMX's setter keep their
    double, the range 0.001 to 0.90 and 005-73's checks. The fraction is
    used as the nearest multiple of 2^-16, and the getter returns that:
    the default 0.25 exactly, 0.1 as 0.100006. So a fraction other than the
    default can make a reclaim step rewrite a few bytes more or less per MB
    of growth than the exact double did.
  * The iteration spacing and the low watermark give what they gave, for
    retain durations below 28 years and budgets below 3 PB; the default
    fraction for streams below 2^53 bytes (9 PB).


Performance
-----------

* **Handles** (bergdb 009, merged in `178a0d4`, 2026-10-26; the branch's tip
  `a04a418`). A memory pointer holds its pointee's handle, and eviction
  replaces the handle's object, not the pointers (`4e66a59`, `c6a4fa2`):
  * eviction without the sweep that stopped the world: CLOCK over the node
    table, in batches that end after 2 ms (`Eviction.BATCH_NANOS`), and a
    reader's load over the trigger waits up to 2 ms (`LOAD_WAIT_NANOS`)
    (`4a1fc5e`, `66c8f3a`, `a04a418`);
  * reads of resident nodes without a lock (`19a8c58`), each pointer read
    with an acquire since 015-14 (`4e10aa2`, above); the pointer locks
    gone (`7831909`);
  * the node table in 4,096 maps with a lock each: a resize stops one map
    for 0.23 ms, where it took 11.6 ms (`be4534a`); reads no longer
    synchronize on `readSync` (`463d6ee`);
  * figures (009-03; docs/levels.md, section 7): the longest get from the
    OS cache at 10M keys under ZGC 3.45 ms, against 7.3 s in 2026.1; gets
    in memory from 8 threads 101 and 61 percent more (G1, ZGC), from one
    thread 3 and 11 percent fewer; loads in memory 8 to 20 percent slower;
    P4's soak: the longest commit 5.1 ms, the longest read 3.6 ms. The
    release notes cite the figures of the release's own runs (016-10),
    with these as context;
  * faults of the development, fixed before the release: a batch
    subtracted values that were never counted, so the resident count could
    drift below the real bytes and the database use more memory than its
    budget (015-15, 2026-11-03, `f82e7e7`); the eviction thread stopped
    after one batch that freed nothing, which left the resident bytes over
    a lowered budget when every object was just read (015-10, 2026-11-03,
    `24bdae5`); an exception in a batch of the eviction thread ended the
    thread and nothing else, so the database went on without eviction,
    where now it fails the database (015-25, 2026-11-03, `fa08db4`).
  * the resident bytes count the handles (015-13, 2026-11-03, `e427a4c`):
    each live handle with its node-table entry, 79 bytes, and 32 bytes for
    each pointer that holds one, as 009-02, 4.7 says. Before, the count
    left them out, and a database used 34 to 49 percent more memory than
    its budget in a probe. At a given cache size about a third fewer
    objects stay in memory than in 2026.1. The constants are JDK 27's,
    with compact object headers; on other JVMs they are an estimate.
* **MEM 129 to 130 bytes per KV** since handles, against 191 in 2026.1;
  `level1.sh`'s limit lowered from 228 to 131 (2026-10-29, `f648f96`).
  `level1.sh`'s SS limits raised after 007-07 (2026-10-29, `f6fc56b`).
* **Group commit** (bergdb 005-48, 2026-10-27, `e611709`). A sync that
  waits has the buffer written at once (`BufferedStream.flushSoon`), and
  transactions that arrive during a force go out together. On s1, one
  thread's durable commits went from 38 to 213 a second (`3950a96`).
* **An idle eviction thread sleeps** (bergdb 005-51, 2026-10-27,
  `c2aab10`). It waits with no timeout, where it woke once a second (1.4
  ms of CPU a minute before, none after, `78a6723`); `close()` returns
  after it has ended, also after `stop()`.
* **A reader's load skips the eviction monitor** when a request to the
  eviction thread is pending (bergdb 005-65, 2026-10-29, `988fe1a`).
* **Reads do not wait for the writer** (bergdb 005-46, 2026-10-27,
  `eaec93e`). A read of the
  stream's last file no longer waits for the writer's append and its force,
  nor for a new file's force or reclaim's deletes of cut files (a thread of
  their own, `FileStream-cut`); an encrypted database's reads no longer wait
  for each other.
* **Startup without header reads** (bergdb 005-57, part 1, 2026-10-27,
  `07b6375`). A start finds the nodes of the startup section's pointers by
  their position instead of reading a header for each: in the prototype a
  cold start of 10M keys on s1 took about 46 and 51 s at startup distances
  of 50 and 200 MB, where it took 214 and 210 s.
* **Index writes in proportion to each commit, and bounded startup** (bergdb
  005-49; 007-03, step 3; 007-07, 2026-10-28, `f89846d`). Each commit writes
  its share of the dirty index nodes, in proportion to its size, so that the
  startup section stays near the startup distance, and a deadline takes
  every transaction that begins twice the startup distance or more before
  the end of the stream, so that a start reruns less than that. At 10M keys
  the largest record of a run is 0.34 to 1.9 MB, against 2.6 to 4.6 MB with
  the take before (docs/levels.md, section 5); a put costs 24 and 36 percent
  more stream at startup distances of 50 and 200 MB, and 13 percent less at
  1000 MB. `Db.setStartupDistance` lowers the distance in one call, with no
  commit that writes the whole startup section; the section comes down as
  transactions are committed. Every stream differs from what 2026.1 wrote;
  the format does not.
* **A quarter-full write buffer wakes the storage thread** (bergdb 005-76,
  2026-11-03, `df6ad50`). An append notifies it once when the buffered bytes
  reach a quarter, and after a flush it writes again without a timer wait if
  a quarter remains. Before, the quarter rule waited for the next timer
  check, reducing throughput at high write rates and long buffer times. The
  stream's bytes and the default buffer time do not change.
* **The default buffer time is 50 ms** (bergdb 005-64, 2026-10-29,
  `27ec238`), where it was 20 ms (`StorageManager.DEFAULT_BUFFER_TIME`, the
  main stream's; also the Pub API's, and that of the replicas added
  through the Pub API; the Core's replicas keep 2,000 ms). A writer that
  does not sync gets fewer forces, 11 to 14 percent on F53 and 18 to 35 on
  s1, so fewer rewrites of the stream's last, partly filled page, with the
  same throughput, latency and CPU. A sync has the buffer written at once
  (005-48), but a rare sync beside a writer that does not sync is up to 22
  percent slower (s1). For data that is not synced, a power loss
  or a crash can take about twice as much: the writes of about 1.1 to 2
  buffer times, about 82 ms of writes on macOS where it was about 40, fewer
  at high rates, where a quarter of the buffer starts a flush, and never more
  than the 10 MB buffer. What a sync has returned for is never lost. The
  stream's bytes do not change.


Documentation
-------------

* **`stop()`'s Javadoc corrected** (2026-10-26, `a515af3`). 2026.1's
  Javadoc of `Database.stop()` and `Db.stop()` said that the files are not
  forced and that only `sync(STRONG)` forces them. `FileStream` forces
  every append, so `sync()` waits until the data is on the device, and
  `STRONG` adds the replicas.
* **`DatabaseBuilder.startupDistanceInMb`'s Javadoc** said 5 to 100 MB; the
  code has always clamped to 5 to 1000 MB (2026-10-28, `fd8f513`).
* **Replication's wording** (bergdb 016-04, 2026-11-03): the Javadoc of
  `DatabaseBuilder.replica`, `Database.addReplica`, `removeReplica` and
  `getStorageInfos` says that replication is experimental, has known
  faults, will change its API, and must not be used in production.


Build and tools
---------------

* `java/javadoc-pub.sh` builds the Pub API's Javadoc, with doclint, and
  fails on any warning (2026-10-29, `216fc8b`).
* `java/deps.py`: `before-commit.sh` checks the package dependencies
  against each `package.html` (bergdb 005-56, 2026-10-28, `04f1546`).
* `java/doubles.py`: `before-commit.sh` refuses floating point in the
  Core Layer's decisions (bergdb 005-79, 2026-11-03, `f04cefe`).
* `java/stress/core-build.sh` builds the Core Layer alone, `night.sh`'s
  step 2 (bergdb 005-56, 2026-10-28, `43e631f`).
* `java/stress/PauseProbe.java`, the longest waits of gets and commits
  under eviction (2026-10-25, `e23c96e`); since 005-52 (2026-11-03,
  `87d1e2c`) it can lower the budget in the middle of a phase (`lower`,
  `lowerAt`).
* jcstress tests in `java/stress/jcstress/` (`19a8c58`, `a04a418`), with a
  key node's growth (015-12, `dc42409`).


The Lean model
--------------

Lean is a tool of the work, not an output of the release (Frans,
2026-11-03).

* The model of handles, `SIS/Handle.lean` (2026-10-25, `74af34c`);
  T-CACHE, T-READ, T2-C, T-READ with restarts and T-PIN over handles
  (2026-10-26, `38586b3`, `059d741`); the checker's C-H compares Java's
  handle state with the model (`851acdf`, `e712874`).
* Rule 4 by position proved to link what rule 4 by node id links (bergdb
  005-58, `7c1ce2f`, `0965377`), also after a cut (`96e371a`, `8ce4f12`).
* T9 and T12 over handles (bergdb 005-62, `bba91dd`, `a506b34`); the model
  before handles removed, and startup with handles proved (005-62,
  2026-10-28, `bee5065`, `7f81169`, `073366a`, `9caa031`).
* T3 for BergDB's take (bergdb 007-08, `db1eca8`, `8b6669f`, `3d21792`,
  `9cf8a82`).
* Not in the model: 005-79's integers. The model's take (`share`,
  `dither`, and `javaTake` in the conformance) keeps the double share and
  dither of 2026-10-28; on its 300 cases the integer take gives the same
  startup pos (015-03 has the change, optional).
