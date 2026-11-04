BergDB 2026.1
=============

Released 2026-10-25 by Frans Lundberg. **Internal: not published, not for
production.** Made by Claude (Opus 5.5, Claude Code) for Frans, as planned
in bergdb item 008 ([../../items/008-release-2026-1/01-plan.md](../../items/008-release-2026-1/01-plan.md)).

The first release since 2015.4 (July 2015); 2017.1 was prepared in 2017 and
never released. 2026.1 is the baseline before the next major change,
handles (item 004) and gradual eviction: the code that later versions are
measured against.


Files
-----

| File | What |
|---|---|
| `bergdb-2026.1.jar` | `java/build.sh`'s jar of the release commit: the production code, `src-dev` (Props, the tests, the demos) and ICU 50 (as `bergdb.icu50`). Class files for Java 8. Main class `bergdb.dev.Run`. |
| `bergdb-2026.1-src.zip` | `git archive` of the release commit, the whole tree, in `bergdb-2026.1/`. License: Apache-2.0 (`LICENSE`, `NOTICE`); ICU's in `java/in/ICU-LICENSE.html`. |
| `baseline.zip` | The outputs of the gates and of the baseline runs (below). |
| `SHA256SUMS` | Check with `shasum -a 256 -c SHA256SUMS`. |


Identity
--------

* Tag `release-2026.1`, commit `a42947c58ee0c984375095cf99bc207d9980c214`
  (2026-10-25).
* `BuildInfo`: release 2026.1, release int 261, build 2026.1.261025.1248;
  `java -cp bergdb-2026.1.jar bergdb.core.BuildInfo` prints them.
* Built by `java/build.sh` (`javac --release 8`) with OpenJDK 27 (Homebrew,
  build 27) on F53, Frans's MacBook Pro (MacBookPro18,3, Apple M1 Pro, 10
  cores, 32 GB, macOS 27.0.1).
* `bergdb-2026.1.jar`: SHA-256
  `4d90eb9237462f28a697620755500043b7880f408ff6469293a63ff951ad5892`.


What it is
----------

An in-process, append-only database for Java: a multiversion ordered map
from (key, time) to value, kept in one append-only stream, with a Lean
model of its algorithm ([README.md](../../README.md)).

| Level | Features | Status |
|---|---|---|
| 0 | Multiversion map in memory | Passes the tests run |
| 1 | + restart by replaying the whole stream | Passes the tests run |
| 2 | + bounded startup (self-indexed stream) | Passes the tests run, under load and with crashes |
| 3 | + reclaim: cut the front of the stream | Passes the tests run, a two-hour disk soak and the power-loss ordering checks; aligned with the proved Lean model of reclaim |
| 4 | + eviction: data larger than memory | Passes the tests run, on by default; a database six times its memory budget runs on disk; aligned with the proved Lean model of eviction |

Defaults that matter: a startup distance of 50 MB; a buffer time of 20 ms;
infinite retention; eviction on, with the cache size indicator as its
budget (200 MB in the core API).


Changes since 2015.4 and since the 2017 import
----------------------------------------------

The details are in [docs/log.md](../../docs/log.md) and in the closed list
of [items/005-todo/readme.md](../../items/005-todo/readme.md).

* **The restart bugs of 2015 to 2017 fixed** (2026-10-12 to 14), ISSUE151111
  very likely among them: deletes of missing long keys, a root replaced twice
  in one transaction, two node tables, Rule R by node id, streams over 2.1
  GB, a crash inside the size bytes, a sync that hid a failed write, and
  more. The stream is byte for byte the same with and without restarts.
* **Levels 2 to 4 work**: bounded startup, reclaim, and eviction (new in
  2026), each aligned with a Lean model with machine-checked proofs.
* **Faults fixed since**, 005-01 to 005-45: M49, a transaction half
  committed when it threw (005-01); M46, the top node ordinal bound (005-02);
  the node table's tree bins (005-08); a race between a
  reader and the sweep (005-09); the overflows of 005-15 to 005-26; a crash
  at a meta block's position (005-27); a read that fails on the storage
  (005-30); a transaction too large for one record (005-31); a failed start
  that left its storage running (005-32); `stop()` and `close()` (005-35);
  a start that wrote before it checked the key and the format (005-40); a
  sync one byte short of the commit byte (005-44); and more.
* **API changes**: `Kv.time()` and `Connection.time()` removed; a failure
  fails the database, which then refuses every transaction and read until
  restarted (005-01, 005-30); `stop()` writes everything in a close of its
  own, and `close()` waits for it (005-35); transaction outputs made
  consistent (005-12); `DatabaseNotCreatedException` for a database whose
  creation did not complete (005-33); `transactionInfo()` gives the user's
  KVs only, and `LookupTimeNotAvailableException` for a value that reclaim
  has rewritten (005-42); replication is documented as experimental
  (005-11).
* **Defaults**: the startup distance 20 MB to 50 MB (2026-10-13); the
  buffer time 100 ms to 20 ms (005-13); an idle database sleeps (005-14).
* **Format**: record format 5 since 2026-10-15 (`topPos` in the header,
  M18). Streams of 2015.4 and 2017 are refused, with a
  `VersioningStreamException` that says whether an older or a newer BergDB
  wrote the stream (005-40).


Verification
------------

On the release commit, in a clean clone (`baseline.zip`, `gates/`):

`java/night.sh` on the release commit, 2026-10-25 12:51 to 13:35 (`NIGHT OK`,
44 minutes, JDK 27):

| Step | Result | Time |
|---|---|---|
| `before-commit.sh` | BEFORE COMMIT OK: 1,024 unit tests, 69 f-tests | 134 s |
| `level1.sh` | LEVEL 1 OK | 132 s |
| `level2.sh` | LEVEL 2 OK | 740 s |
| `level3.sh` | LEVEL 3 OK | 493 s |
| `level4.sh` | LEVEL 4 OK | 863 s |
| night tests | SUCCESS, 7 tests | 161 s |
| `conformance.sh medium` | CONFORMANCE OK | 141 s |

* Lean: `lake build` of every proof (in the level scripts); the 27 theorems
  that [lean/README.md](../../lean/README.md) lists depend on Lean's standard
  axioms only (`propext`, `Classical.choice`, `Quot.sound`; no `sorry`).
* The tests again on the jar itself, with `-ea`: 1,024 unit tests, 69 f-tests and 7 night tests, all passed.
* StreamDigest: the 12 configurations in 3 modes; the modes give the same
  stream (`baseline.zip`, `f53/digests.txt`).


Release Props
-------------

As in the log of 2015 (F1-007). Props (`bergdb.dev.props.Props`; lower is
better): MEM, heap bytes per KV; CORE, the four Core tests against cissi's
times of July 2013; SS, stream bytes per user byte.

| Release, machine | MEM | CORE (get, get4t, getmany, set) | SS (SS1, SS2, SS3, SS4) |
|---|---|---|---|
| 2015.4, cissi, Java 7 (2015-07-27) | 161 | 0.78 (0.77, 0.99, 0.85, 0.58) | 1.48 (1.16, 1.26, 1.60, 2.06) |
| 2026.1, F53, JDK 27 (median of 5 runs) | 191 | 0.29 (0.26, 0.35, 0.26, 0.32) | 1.50 (1.10, 1.19, 1.62, 2.37) |

MEM and SS do not depend on the machine; CORE does (F53 is 2.6 to 2.9 times
faster than cissi for the same code, bergdb 006-02). MEM was 271 in the
2017 import.

Lines of code (Java and Lean files in git):

| Part | Files | Lines |
|---|---|---|
| `java/src` | 250 | 65,958 |
| `java/src-dev` | 123 | 13,904 |
| `java/src-icu` | 2 | 194 |
| `java/stress` | 24 | 10,765 |
| `lean` | 115 | 47,347 |
| `docs` (Markdown) | 20 | 13,712 |


Baseline
--------

The release jar on two machines, with the parameters of 004-02 and 004-04,
2026-10-25. Every value read was checked (`PERF OK`, `SCALEBENCH OK`). All
outputs, GC logs included, are in `baseline.zip`, with the scripts
(`tools/`).

* **F53**: as above; Homebrew's OpenJDK 27; AC power; the timed block
  15:17 to 15:49, after 5 quiet minutes (load 1.4, every other Claude
  session idle; 95.6 percent CPU idle before the quick suite).
* **s1**: Frans's VPS (AMD EPYC, 2 virtual CPUs, 3.8 GB, a virtual disk of
  about 0.45 ms a read), OpenJDK 27+35; 12:52 to 14:00.

**The quick suite** (`performance.sh quick`, G1, `-Xms8g -Xmx8g`, assertions
off, medians of 3 runs; session `a42947c5-20261025T152138-quick-g1-8g-2026.1`):

| Measure | 2026.1 | 2026-10-16 reference |
|---|---|---|
| Warm latest gets, 200k keys of 1,000 bytes, resident | 1.29 M/s | 1.28 M/s |
| Warm historical gets | 1.25 M/s | 1.26 M/s |
| Warm long-key gets (120-byte keys) | 0.95 M/s | 0.95 M/s |
| Gets from 4 threads | 3.10 M/s | 3.42 M/s |
| Forward / backward scans (100 KVs) | 3.78 / 4.03 M KVs/s | 3.70 / 3.88 M KVs/s |
| Updates, infinite retention | 100.9k commits/s | 90.1k commits/s |
| Bytes appended per user byte, infinite / finite | 1.22 / 1.68 | 1.22 / 1.68 |
| Updates, finite retention | 62.9k commits/s | 58.4k commits/s |
| Startup after a restart (50 MB section) | 0.70 s | 0.65 s |
| First 300k gets after a restart, mean; the same again | 2.66 µs; 0.55 µs | 2.69 µs; 0.56 µs |
| Mixed phase (1 writer, 2 readers): commits/s, gets/s | 49.1k, 1.96 M | 47.3k, 1.86 M |

**ScaleBench, 10M keys of 24 bytes on F53** (8-byte values, loaded in
random order, startup distance 10 MB). M: everything in memory, no
eviction; C: the stream in the OS cache, eviction with the budget given.
Gets from one thread, uniform keys; latencies from a timed pass of a
million gets.

| Run | Gets/s | p50 | p99 | Longest get | 4 / 8 threads, gets/s | Longest sweep | Longest GC pause | Full GCs |
|---|---|---|---|---|---|---|---|---|
| M, G1 | 726k | 1.33 µs | 1.96 µs | 45 µs | 1.98 M / 2.00 M | — | 175 ms (during the load) | 0 |
| M, ZGC | 611k | 1.50 µs | 2.46 µs | 120 µs | 1.80 M / 2.21 M | — | 0.013 ms | 0 |
| C 665 MB, G1 | 179k | 5.05 µs | 11.2 µs | 152 ms | 197k / 152k | 5.9 s | 246 ms | 8 |
| C 665 MB, ZGC | 176k | 5.15 µs | 11.2 µs | 0.25 ms | 198k / 139k | 7.4 s | 0.021 ms | 0 |
| C 133 MB, G1 | 58k | 10.4 µs | 18.3 µs | 334 ms | 83k / 65k | 0.6 s | 44 ms | 46 |

* The load (M): 97.7 s, 102k puts a second with G1 (96k with ZGC); 754
  bytes on disk a key; heap per key 243 bytes with G1, 317 with ZGC.
* The longest waits are the sweeps: with 665 MB every sweep took 5 to 7 s,
  and the readers waited for them (4 threads: 41 to 48 percent of the
  samples blocked in `Eviction.afterLoad` on the write lock). In the timed
  passes, a get's tail was a sweep or a G1 pause; with ZGC the GC paused at
  most 0.021 ms.

**ScaleBench on s1** (G1; D: the OS cache dropped, the JVM in a cgroup
that leaves about 300 MB for it):

| Run | Result |
|---|---|
| Load, 10M keys, budget 600 MB | 3,015 s, 3.3k puts a second; longest sweep 24.5 s; longest GC pause 464 ms |
| D, 10M keys, 133 MB | startup with a cold cache 178 s; 1,216 gets a second, p50 0.69 ms, p99 3.1 ms, longest 1.4 s; 1.84 device reads a get; 4 threads 3.3k gets/s |
| M, 1M keys | load 32 s (31k puts/s), 262 bytes of heap a key; 670k gets/s, p50 1.32 µs |
| C, 1M keys, 66 MB | 95k gets/s, p50 4.5 µs, longest 1.1 s (sweeps up to 1.4 s) |
| D, 1M keys, 66 MB | startup with a cold cache 8.3 s; 92k gets/s, p50 5.2 µs, longest 1.1 s |

Beside the earlier runs on older commits (004-02 on `f206e58`, 004-04 on
`7d14f65`), the figures agree within their spread: in memory 726k against
712k to 722k gets a second; the 665 MB sweep 5.9 s against 6.0 s; full
collections at 133 MB 46 against 47 to 49; s1's cold start at 10M 178 s
against 175 to 194 s; s1's 10M load 3,015 s against 3,616 s. Gets from 4
threads in the quick suite (3.10 against 3.42 M/s) are within that test's
known sensitivity to other work (006-02).

StreamDigest's digests of the release are in `baseline.zip`,
`f53/digests.txt`.


How to compare a later version
------------------------------

Run 2026.1 again beside the later version, in turns, on the same machine and
JDK, rather than compare with the numbers above: the machine, the OS and the
JDK change.

* **Props**: `java -cp JAR bergdb.dev.props.Props`, with each jar in turn.
* **performance.sh**: in a clone at the tag, `java/stress/performance.sh
  build 2026.1` (a preserved build in `java/build/perf/builds/`); then, in
  the later tree, `performance.sh ab 2026.1 current`, which alternates the
  two and compares.
* **StreamDigest**: compile `java/stress` of the tag against this jar and
  run that one compiled copy against both jars, then `compare` (see
  `StreamDigest`'s header). The stream does not depend on eviction
  (EvictionInvariance; T-CACHE in Lean), and handles do not change the
  records (004-03, 2.2), so 004 should give the same digests.
* **ScaleBench** (`items/004-indirect-swizzling/02-scale-tests/`, with
  `sb.sh`): the same runs on both jars, in turns, as in `baseline.zip`'s
  `tools/`. It reads internals that handles change (the eviction's figures,
  the resident bytes, the load listener); 004 ports those reads and keeps
  the workload.


Known issues and limits
-----------------------

* The sweep stops the world while it walks every resident object: 0.5 s
  to 266 s in 004-02 (at 100M keys during the load), with G1's full
  collections around it under eviction (004-04). Handles (004) are to end it.
* The read path's pointer lock, stamp and `readSync` cap reads at about 2
  million gets a second, at any size (004-02).
* Writes at scale: the stream grows to about 1.1 KB per key at 100M random
  keys, and loads into an index larger than the budget slow to under 100
  puts a second on a slow disk (005-38).
* A startup with a cold OS cache on a slow disk takes minutes at 10M keys:
  one header read per pointer of D (`DbStarter.linkD`; 004-02, 10.5.8).
* Startup is not yet bounded for BergDB's own startup pos policy: the
  section reached 2.21 times the startup distance in a test (007-01, 4.1);
  the deadline that bounds it (007-03) comes after 2026.1.
* Replication is experimental, with known faults, and not for data that
  matters (005-11).
* `BufferedStream` does not wake its consumer when the buffer is full; it
  matters only at buffer times of about 200 ms or more, set through the core
  API (005-13); the default is 20 ms.
* Power loss on real hardware is not established (see
  [docs/level3-durability.md](../../items/011-docs-archive/07-level3-durability.md)). Tested on
  JDK 27 only, though compiled for Java 8. The documentation has not been
  reviewed for users.


Post-release notes
------------------

A fault found later that affects 2026.1, its numbers or its correctness,
is recorded here. Each was checked against 2026.1's code (`git show
release-2026.1:PATH` of the code its fix changed), on 2026-11-03, for
release 2026.2 (bergdb 016-03, N3).

**Faults of 2026.1 fixed for 2026.2:**

* **An interrupt could fail or stop the database** (005-46, `eaec93e`).
  An append that waited for room in the write buffer threw an
  `IOException` ("Thread interrupted while appending") when its thread was
  interrupted, which failed the database; an interrupt of the storage
  thread threw a `Bug` and stopped its writes; a wait for an index job,
  and an index job's own thread, threw an `Error` when interrupted.
* **A start with another node size** looked like a corrupt stream, or
  started and could leave a stream that no start opened (005-50,
  `bf19075`): 2026.1 does not keep the node size in the stream (offset 44
  of the meta block is reserved). Through the core API only
  (`DbBuilder.maxNodeSize8()` and its kin).
* **Reclaim spaced its iterations by the builder's startup distance**, not
  the stream's (005-61, `a175840`): `Reclaim` took `db.getStartupDistance()`
  in `Db`'s constructor, before `start()` read the stream's. A database
  opened with another startup distance than it was made with, as one made
  with `startupDistanceInMb(5)` and opened with the default 50 MB,
  reclaimed too seldom or too often; in a test at 2,000 bytes against 50
  MB it nearly stopped reclaiming.
* **Nothing refused a second database on one directory** (005-63,
  `322c5d1`), in the same JVM or in another process: 2026.1 takes no lock
  on the directory. The two could write beside each other, and one
  started right after `stop()` could take files that the first was still
  deleting.
* **A read set from before a restart was accepted** (005-70, `7d967d7`):
  after a start the STM's history is empty, and a transaction with a read
  dependency whose snapshot predated the last recovered commit was not
  checked, despite a conflicting write before the close. Through the core
  API only: a Pub API transaction cannot move to a new `Database`.
* **`close()` discarded I/O failures** (005-73, `3ad171d`): a failed final
  flush or storage close, which `closeStorage()` returned, was dropped by
  `close()` and by `stop()`'s thread.
  `Db.setReclaimInternalFraction(Double.NaN)` was accepted (its range check
  is false for NaN). `Db.getCachePutSize()` was constant and
  `getDirtyFraction100()` and `getDirtyFraction1000()` were incorrect, with
  their JMX attributes.
* **Corrupt sizes looped or exhausted the heap** (005-74, `c229ab2`): a
  negative node size moved `StoredTrans.Parser` back for ever, and a
  corrupt record or node size near 2^31 was allocated before its bytes
  were read, giving an `OutOfMemoryError` instead of a format error.
* **Corrupt times and sizes were replayed** (005-75, `0e61856`): startup
  did not check the record order, the 56-bit range of record times or the
  increasing times in key nodes before replay, and a Core append did not
  check the size at the buffer's offset.
* **A node's inner fields were not checked** (015-07, `12610c7`): a node
  whose checksum was right but whose key count, value size, key size or
  pointer count did not fit threw an `ArrayIndexOutOfBoundsException` or a
  `NegativeArraySizeException` in a load, which escaped the reads' failure
  handling, so the database stayed active.
* **`getTrans` on a corrupt record left the database active** (005-82,
  `3e32f02`): `Db.getTrans` parsed the record (`ti.getStoredTrans()`)
  after its `try`, so the parse's exceptions passed its failure handling.
* **A key node's growth was published with plain stores** (015-12,
  `dc42409`): a reader that read the node's size before a growth could see
  the new arrays without their contents, so a search could miss a key
  that was there long before its lookup time, or return the value of a
  later or uncommitted transaction. Rare (8 misses in 477 million searches
  in a probe, none seen through a database); `growCapacity` is the same in
  2026.1.
* **A typed primary scan took a page of non-objects for the end of its
  range** (015-20, `9971100`): a scan of `usePrimary` left out every later
  object when one page of about 100 entries held no object, without a
  word; `UseIndexBuilderImp` is the same in 2026.1.
* **An index deleted and created again under its name** while an old job
  ran (015-21, 015-22; `377fe7d`, `7cd4cdb`): a second `deleteIndex` let
  the first job delete the new index and its entries, and a deleted
  index's build wrote into its replacement, which then returned extra
  objects, duplicates and the wrong order; both lasted after a restart.
  `IndexManager`'s logic is the same in 2026.1 but for 005-46's
  interrupts.
* **The last call on a key in a transaction did not win** (015-40,
  `f7974d3`): `RwEnvironmentImp`'s `MapKey.equals` tested for a `long[]`
  and was never true, so a put and then a delete of a key committed the
  put, and of several puts an earlier value could win.
* **A directory whose stream files were gone, or whose only file was
  empty, started as a new, empty database** without a word (015-01,
  `ed16384`): 2026.1 creates a database for every empty stream, whatever
  `created.txt` says. An empty or missing directory still does, in 2026.2
  too (015-05).
* **A start refused for its crypto key left an empty first stream file**
  (015-06, in part, `ed16384`): in 2026.1, `dir()` opened the directory,
  creating `00000000000000.bergdb`, before `start()` checked the key.
* **`SystemClock` did not give strictly increasing times** (005-69,
  `b281d39`), as its Javadoc said: its last time stayed 0, so calls within
  a millisecond, or after the system clock was set back, gave equal or
  earlier times. No harm: a database's own clock makes its times strictly
  increasing.
* **`BufferedStream` did not wake its consumer when its buffer was a
  quarter full** (005-76, `df6ad50`): 2026.1's known issue of 005-13,
  fixed.

**Faults of 2026.1 not fixed in 2026.2** (known issues of 2026.2):

* **Holes in an unforced tail** after a power loss can refuse a start or
  fail a later read (014-01, found in 005-83). Not fixed.
* **A failed append's transaction was visible** to a read before the
  failure, where 2026.1's documents said that its time never becomes a
  lookup time (015-27): `transactionEnd()` comes before `store()`. The
  text is corrected for 2026.2 (docs/levels.md, section 3); the code is
  the same.
* **`FileStream.append` with a negative length** corrupts the stream's
  length (015-26). Internal: no path from the Pub API gives one.
* **A start on an empty or missing directory creates a database**
  (015-05), as above.
* **The faults that the reviews before release 2026.2 found** in code that
  2026.1 has, each with its entry in `items/015-todo/` and the reviewer's
  check at the tag (bergdb 016-06): in the indexes, the objects and the
  rw-transactions, 015-23, 015-28 to 015-30, 015-36, 015-37, 015-39,
  015-41 to 015-43, 015-46 to 015-48, 015-59 to 015-62, 015-64, and review
  S2's 27 faults (015-49); in the storage, 015-31 to 015-35 and 015-78 to
  015-83; in the Core and reclaim, 015-50, 015-51, 015-53 to 015-55; in
  startup, 015-74, 015-75 and 015-77; in eviction, 015-67 and 015-69;
  elsewhere, 015-38, 015-44, 015-45, 015-57, 015-58, 015-63 and 015-65.
  Release 2026.2's notes, "Known issues and limits", say what each does.
  Those of reviews R2 and R3 (015-23, 015-31 to 015-39) were verified by a
  second reviewer; the others have the reviewer's own test or probe.
* **A start can accept a corrupt stream and lose committed data** (015-72,
  015-73, found by review R6 on 2026-11-04; in 2026.1 too, not fixed): a
  record whose size field is larger than its content is accepted, and the
  records it covers are lost; a corrupt `startupPos` in the last record is
  accepted, and the transactions before it are lost.

**Documentation of 2026.1 that was wrong:**

* The Javadoc of `Database.stop()` and `Db.stop()` said that the files are
  not forced and that only `sync(STRONG)` forces them; `FileStream` forces
  every append, so `sync()` waits until the data is on the device, and
  `STRONG` adds the replicas (`a515af3`).
* `DatabaseBuilder.startupDistanceInMb`'s Javadoc said 5 to 100 MB; the
  code clamps to 5 to 1000 MB (`fd8f513`).

**"How to compare a later version", above, no longer holds as written:**

* One compiled copy of StreamDigest, PauseProbe or `performance.sh`'s
  harness no longer runs on both 2026.1 and later jars: 005-56 (`04f1546`)
  moved `SyncLevel` to `bergdb.pub.util`, and 005-46 (`eaec93e`) made
  `PauseProbe` use `FileStreamIo`, package-private in 2026.1. What runs on
  both: Props, each jar its own; `PauseProbe` as of `e23c96e`;
  StreamDigest and the harness compiled per jar, with the import of
  `SyncLevel` changed for 2026.1; ScaleBench patched and compiled per jar
  (bergdb 016-10, section 1).
* Later versions give other digests than 2026.1, by design: the node size
  in the meta block (005-50), the paced take (007-07) and the take in
  integers (005-79) change the records, though handles alone do not.
