BergDB 2026.5
=============

Released 2026-11-13 by Frans Lundberg. As planned in bergdb item 024
([../../items/024-release-2026-5/readme.md](../../items/024-release-2026-5/readme.md)).

*Theme*: Solid algorithms. 

Result.

* No known bugs. 

* Solid algorithms. 
  - Well tested. Unit tests (nanotests), f-tests, AI user applications.

* Cost proportional to value. 
  - No big writes. No unproportional write size.
  - No stop-the-world. No unproportial time consumption.
  - All maintenance is gradual. Piggy-back to user operations
    or optionally through single maintain() method.

Solid algorithms (024-04; Frans, 2026-11-11): bugs first; operations
proportional to their work; storage proportional to the KVs stored; the
Lean model matching the code. "Cost follows value." 2026.5 changes the
Core's algorithms where 2026.4's measurements at 1M to 10M keys (024-03)
found them out of proportion: a delete now merges underfull key nodes
and a key node holds at most theta dead entries (record format 7, with a
CRC32C node checksum); a reclaim step makes dirty only the paths of its
own puts, not the rest of the index (the last touch, 024-07); the take's
pace is capped after a decrease of the startup distance; the cache's
tables shrink after deletes; and keys, values and transactions have
limits. Count gates at 1M keys check aims 2 and 3 every night (024-30).
The Lean model now has the key tree (024-12, 024-22); the proofs that
hold are in the release, the open ones are named under Known issues.

**Databases of 2026.4 and before do not open in 2026.5.** A start of one
throws a `VersioningStreamException` that names release 2026.4 (format 6;
format 5 of 2026.3 and earlier, as before). Make such a database again,
or read its data with 2026.4 and put it with 2026.5; its history is not
kept. **New limits** (Changes, Limits): a key at most 111 bytes, a value
at most 8 MiB, a transaction at most 500 operations and 32 MiB; a refused
call spoils its builder. **The Pub API** has one new method,
`Database.maintain()`, optional. **Java 17 or later is required.**
BergDB also runs on Android, checked on an emulator.


Files
-----

* `bergdb-2026.5.jar`: the users' jar of the release commit, made by
  `java/build.sh`.
* `bergdb-2026.5-src.zip`: the source of the release commit, made by
  `git archive`, in the directory `bergdb-2026.5/`.
* `bergdb-2026.5-javadoc.zip`: the Pub API's Javadoc, in the directory
  `bergdb-2026.5-javadoc/`.
* `baseline.zip`: the outputs of the gates and the tests.
* `SHA256SUMS`: the files' checksums; check them with
  `shasum -a 256 -c SHA256SUMS`.

* The jar is `build/bergdb-release.jar`, as in 2026.4 (020-10, section
  7): the classes and resources of `java/src` only, for Java 17, with no
  tests, demos or tools (`src-dev`), no ICU and no main class; the
  packages `bergdb.pub` and `bergdb.pubimp` are sealed. The API is
  `bergdb.pub`, `bergdb.pub.util` and the Core's `Db` with the types of
  its signatures; the rest is not API, whatever is public in it.
* The source zip holds the whole tree but the earlier releases'
  directories, `releases/2026.1/` to `releases/2026.4/`, whose files stay
  in the repository and their tags (016-09, R-1). License:
  Apache-2.0 (`LICENSE`, `NOTICE`).
* The Javadoc is `java/javadoc-pub.sh`'s: `bergdb.pub` and
  `bergdb.pub.util`, with `overview-pub.html`. The Core API's Javadoc is
  in the source (`Db`), not published (020-24-15, Q1).
* `baseline.zip`: `gates/` (`night.sh large`'s report and outputs on the
  release commit, its gate, the Lean axioms), `f53/` (StreamDigest's
  digests, jcstress, Android, the performance comparison with 2026.4,
  024-07's queue at 10M keys), `s1/` (the tests on the jars, the user's
  program, OT2's probe, the fuzzing of the deletes) and `tools/` (the
  scripts of the release's night and morning).


Identity
--------

* Tag `release-2026.5`, commit `3611130c5bc98d862655695bd116e7fe2a214574` (2026-11-12).
* `BuildInfo`: release 2026.5, release int 265, build 2026.5.261112.1505;
  `java -cp bergdb-2026.5.jar bergdb.core.BuildInfo` prints them.
* Built by `java/build.sh` (`javac --release 17`) with
  OpenJDK 27.0.1.0.3 (Homebrew) on F53, Frans's MacBook Pro (MacBookPro18,3, Apple M1
  Pro, 10 cores, 32 GB, macOS 27.0.1), in a clean clone of the release
  commit, after its gate.
  The jar is that build's file, the one the tests and the user's program
  below ran on.
* `bergdb-2026.5.jar`: SHA-256 `8535743ded931b8f33faeabcfd2d3ee27d490d32ef257d366025ed95b2f6fc25`.


What it is
----------

An in-process, append-only database for Java
([README.md](../../README.md)). Every transaction is kept in
one append-only stream, and the database answers historic queries: a
read at any available time sees the database as it was at that time,
with every query that the latest time offers, the secondary indexes
included. A start is bounded, whatever the size of the database; reclaim
cuts the front of the stream when a finite retention allows it; and the
data may be larger than memory.

* Startup, reclaim and eviction (with handles, 009-05) are checked
  against a model of the algorithm (`lean/`, work in progress, for
  developers). Since 2026.5 the model also has the key tree
  (024-12): Java's index after each transaction is checked against it by
  traces, merges and theta included, on every gate and on the release
  commit too (Verification).
* A delete removes the index nodes that it empties and merges an
  underfull key node with a sibling, so the index holds at most a fixed
  multiple of a fresh one's key nodes whatever was deleted (024-21; G2).
  A reclaim step makes dirty only the index nodes on the paths of the KVs
  it rewrites (024-07).
* Objects and user indexes, as in 2026.4: a stored object is `DbObject`,
  in format 2, put and got as Data Objects; user indexes of one
  directory, one field a level, with a build's `Job`; the primary scan.
  Their promises are in `bergdb.pub`'s Javadoc.
* The Pub API is the API to use; the Core API, `Db`, is low level, for
  those who need it, and says so at the top of its Javadoc. The Core API
  may damage what the Pub layer builds on it, never the KV store itself
  (010-01, P14; 010-04, R5).
* BergDB has no replication and no encryption, as in 2026.4.

Defaults that matter, as in 2026.4:

* A startup distance of 50 MB, which suits up to about 10M keys; from
  about 10M keys, 200 to 1000 MB (`DatabaseBuilder.startupDistanceInMb`,
  or `Database.setStartupDistanceInMb` while the database runs). A put's
  stream bytes follow the startup distance a key: Known issues.
* A buffer time of 50 ms.
* Infinite retention (`Database.setRetainDuration` sets another, kept in
  the stream). With a finite one, reclaim's internal fraction is 1/4, not
  a setting of the Pub API: Known issues, the stream kept under reclaim.
* The collector: ZGC (`-XX:+UseZGC`), or Shenandoah without generations.
  With G1, eviction brings pauses of hundreds of milliseconds and full
  collections (Requirements).


Requirements
------------

* **Java 17 or later.** The jar's classes are for Java 17 (`javac
  --release 17`). Tested on JDK 27 and JDK 17 (Verification).
* **Android**: the Core from API level 33 (Android 13), objects from API
  level 34 (Android 14); checked on an emulator, not on a phone. R8 needs
  the rules that 2026.4's notes list (Changes, Platforms).
* **The collector**: ZGC, or Shenandoah in its default mode, without
  generations (004-04, 009-04). BergDB runs with any collector; its pause
  target of about 20 ms (009) is for its own code, and the collector's
  pauses come on top.
* **`stop()` or `close()`** for every database started: nothing stops a
  database that the application drops (005-55).
* **Correct storage** (the crash contract, 014-01, section 7): the storage
  under the stream returns the bytes as they were written, and a crash
  leaves a prefix of what was appended, at least up to what was forced.
  `FileStream` relies on a file system that keeps appends in order, as
  common file systems do.
* **A sound environment** (the error model, `Database`'s Javadoc): an
  `Error`, such as `OutOfMemoryError`, fails the database, and the
  application should end its process (`-XX:+ExitOnOutOfMemoryError`).
* **The limits** (Changes, Limits): keys, values, transactions and an
  indexed value's levels; a call over one throws and writes nothing.


Changes since 2026.4
--------------------

Collected in [releases/next.md](../next.md) as they were made, with each
entry's ID; the entries are in [items/024-release-2026-5/](../../items/024-release-2026-5/readme.md)
and [items/021-todo/](../../items/021-todo/readme.md).

### Pub API

* **`Database.maintain()`: the maintenance on request, a new method**
  (bergdb 024-32; Frans, 2026-11-12, 12:10 and 13:52; 023-04, Y10). With a
  finite retain duration, reclaim moves on only at the application's
  commits (010-01, P3), so a database that was emptied and is no longer
  written kept its stream. A call does a bounded part of the maintenance
  in the database's own transactions: at most one reclaim step, one write
  of index nodes by the take, one filler of at most 200 kB that is put and
  deleted at once to reach a meta block, the cut when it is due (after a
  sync, if needed), and a batch of the release from memory of what the cut
  ended; it returns true if more is due now. A call when nothing is due
  writes nothing; with the retain duration forever (the default) it
  returns false. Calling it is optional: the maintenance goes on at the
  commits as before, whether it is called or not. It writes records of
  kinds that exist only: no format, model or trace change (the
  conformance configurations `r-maint` and `e-r-maint` pass). G5 (Tests
  and gates): 1M keys put and deleted, then `maintain()` alone, no writes:
  the stream from 254 MB to 83 kB, at most 75 kB and 5 records a call.
  The Core's `Db.maintain()` is the same.

### Core API

* **Merges at the delete; record format 7** (bergdb 024-21; 024-11, MG).
  A delete now merges an underfull key node with a sibling: after every
  transaction every key node that is not the root of a segment tree
  holds at least m live keys or children (m = 8 at node size 30; 024-11,
  BU1), so the index holds at most S + (n + S - 1) / (m - 1)
  key nodes for n live keys in S segment trees, whatever was deleted and
  with any retain duration. In 2026.4 a node went only when it emptied:
  after scattered deletes the index had 2 to 20 times the key nodes of a
  fresh database with the same keys (15.7 times at 10M keys, every 30th
  key kept; 024-03, section 5), and scans and gets paid for it. Readers
  at earlier times see the nodes as they were (a merge makes new nodes).
  A record of deletes means another tree, so the record format is 7, and
  **a start refuses a database of format 6, written by release 2026.4**,
  with a `VersioningStreamException` that names 2026.4 (format 5 of 2026.3
  and earlier, as before). The thresholds are 024-14's m8 (Frans,
  2026-11-11): at node size 30 m = 8, a merge's cap 17, and a split keeps
  a last version of up to 17 klongs (2026.4: 15), constants of format 7;
  so the put path changes too, at node sizes 30 and 62: about 1 % more
  bytes a put in a random fill at 10M keys and 6 to 13 % fewer key nodes
  (024-14, section 4.3). A transaction of
  deletes counts more index nodes before the go point (`Dag.
  dirtyNodeBound`, 024-11's CB2): at node size 30 and a path of 5 nodes
  about 120,000 deletes fit one transaction, and a larger one is refused
  before it changes anything.
  **One more rule of format 7: at most theta dead klongs a key node**
  (bergdb 024-23; 024-18's option 2, Frans's decision of 2026-11-11). A
  write to a key node that would leave it with more than theta dead
  entries (deleted or overwritten keys and children, which lookups before
  the write still read) replaces the node by its current version with the
  write applied, as a full node is replaced; theta is 7 at node size 30
  (2, 3 and 14 at 8, 14 and 62; at least 2, bergdb 024-19, Q4). In
  2026.4 a node kept up to B such entries until it filled. Counted at 1M keys with a retain duration of
  1 s (bergdb 024-23, section 7; 024-18's probe): under random overwrites
  0.48 dead entries a live one with the merges alone, 0.31 with the rule;
  in a cold database that reclaim rewrites 0.83 down to 0.29; after
  scattered deletes, with a hot range, 0.85 down to 0.31; for -3 % to
  +8.5 % stream bytes, and 13 to 16 % fewer key nodes. Not yet measured:
  10M keys, memory, reads. Each written
  node and each lookup through it carries fewer stale entries; a node
  that is never written again keeps up to theta. A start's rerun applies
  the same rule (no new field).
  **One more change of format 7: the node checksum is CRC32C** (bergdb
  024-25; 024-17, QL9, Frans's decision of 2026-11-11). Every node's
  checksum is a CRC-32C (`java.util.zip.CRC32C`) of 4 bytes in place of
  2026.4's Fletcher-16 of 2 bytes, in a node header of 12 bytes (8 in
  2026.4); the node formats are 3, 3 and 5 (top, key, value and delete
  nodes; 2, 2 and 4 in 2026.4). Key nodes keep their size (the fields
  moved into reserved bytes); a top node is 8 bytes longer, a value or
  delete node 4. The checksum of 8 MiB, a value at the limit L4, takes
  about 1 ms instead of 47 (0.12 ms a MB against 5.6; a key node of 544
  bytes 0.05 us against 3.0): a commit of an 8 MiB value about 2 to 10
  ms instead of 49 to 56, a get of it about 4 ms instead of 53, a
  restart with six such values about 0.2 s instead of 0.5 (rough
  figures, 024-25, section 6). It sees every change of up to 32 adjacent
  bits, so a byte changed between 0x00 and 0xff, which Fletcher-16 did
  not see (019-33), and passes about one random change in 2^32 (65,025
  before). A database written by `main` with format 7 before this change
  (no release wrote one) is refused at the start, for a checksum error.
  The stream grows by those bytes: Props' SS, stream bytes a user byte,
  from 1.51 to 1.53 (SS3, KVs of 100 bytes, from 1.64 to 1.69).
  StreamDigest: the digests of all 12 configurations change, in every
  mode (48 of 48; the digests before and after in 024-25, section 7).

* **A reclaim step makes dirty only the index nodes on the paths of its
  own puts** (bergdb 024-07, option A; on `main` in `36924319`). The last
  step of each reclaim iteration made dirty every index node after its
  scan's last key (`Db.touchRange`, a key range with no end): with keys in
  time order (a queue, a log) the whole index, pinned in memory and then
  written in one record. At 10M keys in time order that was 772,454 nodes,
  a commit of 20.6 to 22.3 s under the write lock, 0.67 to 2.31 GB
  resident against a cache budget of 0.2 GB, and a record of 206 MB; at
  1M keys 1.6 s and 17 MB (024-07, sections 2 and 8). Two faults of 2026.4
  and before are gone with it (024-07, section 3; 2026.4's Known issues):
  * with a small heap the step ended in `OutOfMemoryError` inside a
    user's commit and failed the database (a queue of 1M keys, a heap of
    256 MB): it now runs its 40,000 transactions, the slowest commit 37
    ms;
  * from about 104M keys in time order the step's nodes passed the record
    limit, 2^31 - 9 bytes, the startup position stopped for good, no cut
    was made again, and the stream and the heap grew without end, without
    an exception (reproduced with the limit lowered,
    `Reclaim.Tester.testLastStepWithinRecordLimit`; not run at that
    size).

  Now a step follows the path of each key it puts (`Db.touchPaths`) and
  no key range. At 10M keys in time order the last step makes 5 to 15
  nodes dirty, the largest record is 29 kB, the slowest commit 78 ms, and
  a transaction writes 9.7 % fewer bytes (6 % at 100,000 to 1M keys);
  reclaim's iterations, steps and cuts are as before (024-07, section 8).
  The cut's correctness without the range: 024-07, section 4 (the Lean
  theorems T-COVER and T-LATEST; it rests on a delete's unlink, 023-07,
  section 5.1). The record format is unchanged; the stream's bytes of a
  database with reclaim on change. StreamDigest's configurations that
  change: not isolated (024-07, section 10); every StreamDigest digest
  changes in 2026.5 anyway with record format 7 and CRC32C (all 48,
  024-25, section 7).
* **In a transaction's builder the last call on a key wins, put or
  delete** (bergdb 024-10, R1; Frans, 2026-11-11, 07:08). Of the calls of
  `Trans.Builder` on one key as written, `build()` keeps the one made
  last, a put with its value or a delete; the earlier ones are gone. In
  2026.4 and before a put won over a delete whatever their order (015-40):
  `put(k, 1)` then `delete(k)` kept the put, and now deletes `k`. A
  transaction that names no key twice writes the bytes it wrote before
  (StreamDigest `all`, 48 of 48 digests identical; 024-10, section 8). The
  Pub API's `w()` and `rw()` already kept the last call on a key as
  written (015-40, 015-41).
* **A transaction whose key transformations make two of its keys one key
  is refused** (bergdb 024-16; Frans, 2026-11-11, 09:43: "One transaction
  must not set (put or delete) a value more than once! This is a strict
  rule."). At the commit, when the key transformations (the Core's; a key
  replace such as `${transactionTime}` in the Pub layer) make two
  different keys as written one key, nothing of the transaction is
  written and the caller gets a `DbException` that names both keys as
  written and the key they became; the database goes on. The check is
  made before the go point (`Db.transformKeys`), so every transaction
  that reaches the index holds one operation a key. In 2026.4 and before
  one of the two was kept (the last put in key order, or a delete). A
  transaction without such keys writes the bytes it wrote before.
* **The node size is at most 62** (bergdb 024-19, Q6; 024-27; Frans,
  2026-11-12). The Core API's `DbBuilder` offers 8, 14, 30 and 62, as
  before, and the Pub API 30, the default (024-19, Q1); now the Dag and a
  start refuse a larger size too, a meta block that gives one with a
  clear message (in 2026.4 such a stream named a method that does not
  exist). Theta, the dead klongs a key node may hold, is at least 2:
  2 at node size 8 (was 1; 024-19, Q4).
* **A start checks a time klong's unused bits** (bergdb 024-25, section
  12; `90184540`). A key node whose time klong has any of bits 56 to 61
  set is refused at the start with a `StreamFormatException` ("Bad time
  klong") in place of an `AssertionError` with `-ea` (and a start that
  went on without it). No writer sets those bits, so every database that
  2026.5 writes opens as before. A damaged stream is caught as a best
  effort: BergDB relies on the storage for the integrity of its bytes
  (Frans, 2026-11-12).
* **`Db.getTrans` refuses a position that is not a transaction's**
  (bergdb 021-27; 010-04, R5). A multiple of 8 inside a record, not at
  its start, read the bytes there as a record and failed the database
  (`DbFailedException`; a database in memory was lost). Now any position
  whose bytes are not a committed transaction's record is refused with
  `IllegalArgumentException` (the read's `StreamFormatException` the
  cause), and the database goes on; only an I/O error fails it. A
  position inside a record whose bytes there happen to form a committed
  record still gives that record. The Pub API's `transactionInfo()`,
  whose position is a get's, still takes a bad record there for damage.
  A size over 1 MiB at the caller's position is believed only when a
  walk of the records' sizes from the meta block before it reaches the
  position (Q27-1): bytes inside a record that read as a size of up to
  2 GB are refused before an array of that size is made.
* **The Core refuses a caller's writes at its own keys** (bergdb 024-37;
  010-04, R5; CA3, 022-06-2's U2-8). The key `/#i/-dummy` and reclaim's
  directory `/#i/dreclaim/` with every key under it are written by the
  Core alone, and a start reads them: in 2026.4 seven bytes put through
  `Db` at `/#i/dreclaim/-settings.txt` were taken, and every later start
  failed with `InternalDataException`. Now a put or a delete there is
  refused before anything is written, and the database goes on: by the
  `Trans.Builder` call that takes the key, with
  `IllegalArgumentException` (it spoils the builder, as a key over the
  limit does), and by `Db.execute()` with a `DbException` for a key that
  a key transformation gives and for the internal calls `putLongKey()`
  and `deleteLongKey()`. The Pub API's keys under `/#i/` (its index
  definitions, entries and markers, `/#i/di...`) are written as before;
  reads of the Core's keys are allowed.
* **The take's pace is capped after a decrease of the startup distance**
  (bergdb 024-31; 015-84, 024-05's OP4; Frans, 2026-11-12, 13:09). Each
  record writes its share of the startup section's dirty index nodes (the
  take, 007-07), and the share grew with the section's span over the
  startup distance: right after a decrease from 1000 to 100 MB in one call
  a record took up to 10 times its usual share, and at 50M keys the
  catch-up's records were 13 to 15 MB (2026.4's Known issues, Limits). Now
  the share counts the span of the section's transactions as at most twice
  the startup distance (`TransSeq.SHARE_FACTOR_CAP`, 2). At 10M keys the
  catch-up's largest record from 1000 to 100 MB is 0.99 MB (was 1.90),
  from 200 to 50 MB 2.36 MB (was 4.12); the catch-up is longer: from 1000
  to 100 MB the section is below twice the new distance after 2.88M puts
  and 1,451 MB of stream (was 0.64M and 795 MB), and it shrinks at every
  record meanwhile. With a startup distance that was not lowered the span
  stays below twice it (T3), so the stream is the same, byte for byte
  (StreamDigest 48 of 48 identical before and after). The Lean model's
  pace mirrors it; `T3_take` holds for any pace.
* **`Db.maintain()`**: the Pub API's `Database.maintain()` (above) in the
  Core API (bergdb 024-32).
* **The cache's tables shrink after deletes** (bergdb 024-33, ST6; Frans,
  2026-11-12, 12:10). The node table, 4,096 hash maps, kept its largest
  size after a fill and a mass delete: at 1M keys put and deleted 226,400
  slots against a fresh database's 60,272 (3.76 times). Now a removal that
  leaves a map under 1/8 of its capacity copies it to a capacity of at
  least twice its entries, and at least 16 slots: 63,744 slots, 1.06 times
  (G4). A copy follows at least capacity / 8 removals, so the cost is
  constant a removal, amortized; `performance.sh ab` at 1M keys showed no
  change beyond the runs' spread. No byte of the stream changes. A floor
  is left (Known issues).
* **A reclaim step reads again only the values it may rewrite** (bergdb
  024-34, OP8; Frans, 2026-11-12, 12:10). A step read each live KV of its
  scan again at its time, also one whose value the scan found at pCut or
  later, which it never rewrites. That second read is now skipped: at 1M
  keys the second reads halve (4,208,912 to 2,063,799); with a cache of 20
  MB the loads fall 3.6 %, since the follower caches each version a step.
  The same puts and the same stream bytes (StreamDigest 48 of 48
  identical). The scan still loads every value it passes, as a step's size
  counts the values' lengths; a scan of keys only would change the bytes
  (024-34, Q34-1; not in 2026.5).

### Format

* **StreamDigest: all 48 digests change** (bergdb 018-01, section 2;
  024-38). Against release 2026.4's digests (its `baseline.zip`,
  `baseline/f53/digests.txt`), the decided digests of all 12
  configurations differ, the 8 of `l2-*` and the 4 of `l3-*`, in each of
  the four modes (48 of 48); in each configuration the four modes give the
  same stream. The causes are record format 7, with its merges, theta and
  CRC32C (024-21, 024-23, 024-25), and the last touch (024-07), whose
  configurations are not isolated (024-07, section 10). The take's cap
  (024-31), reclaim's reads (024-34), the cache's tables (024-33) and
  `maintain()` (024-32) change none: 48 of 48 identical before and after
  each. The digests before and after, and their comparison:
  `items/024-release-2026-5/38-release/` (`digests-base.txt`,
  `digests-new.txt`, `compare.txt`).

### Limits

* **Limits on keys, values and transactions** (bergdb 024-17, 024-24),
  fixed for every database; a later release may raise them, never lower
  them. A call over one throws and writes nothing; the database goes on.
  **A refused put or delete spoils its builder** (bergdb 024-26, U26-5,
  024-27; Frans, 2026-11-12): the Pub API's `WBuilder` and the Core's
  `Trans.Builder` then write nothing, and their `execute()` (Core:
  `build()`) and every later call throw `IllegalStateException`, also if
  the caller caught the refusal. In 2026.4 a caller that caught it and
  went on committed the other operations.
  **In an `rw()` action a refused call changes nothing and does not spoil
  the environment** (bergdb 024-27, QR1; Frans, 2026-11-12): an action
  that catches the refusal and returns commits its other writes, as
  before; the action is the application's code, and the database keeps
  its own indexes consistent either way (010-P14; 010-04, R1 and R3;
  `RwEnvironment`'s Javadoc, "Refused calls").
  * **A key is at most 111 bytes**; about 100 characters as a rule of
    thumb: ASCII letters and digits one byte each, each "/" of a Pub key
    two, letters such as å, ä and ö two bytes each (UTF-8). Refused with
    `IllegalArgumentException` by the call that takes the key. Until now a
    key had no limit.
  * **A value is at most 8 MiB** (8,388,608 bytes), refused at the put
    with `IllegalArgumentException`; larger data goes in chunks under keys
    of their own, with a key that lists them written last.
  * **A transaction is at most 500 operations** (the keys it puts or
    deletes; a Pub object put in a directory with k indexes counts up to 1
    + 2k) **and 32 MiB of keys and values**; its keys, its index entries
    among them, at most 56 KiB. Refused at the commit with
    `DbException`. Larger work goes in several transactions, with a key
    written last that readers look at first.
  * **An indexed value's levels are at most 111 bytes**, as a key: a put
    of an object with longer ones for an index of its directory is refused
    with `IllegalArgumentException` (until now it was taken with no entry,
    and the index's scans missed it); index such a value by a hash or a
    prefix. A build over objects put before the index gives them no entry.
  * A value transformation (Core API) whose result passes 8 MiB fails the
    database, as one that throws does (Known issues). A start reads a
    record's header first, and refuses another format before reading the
    record.
  * Gates and tools changed with them: batches of 500 (were 1,000) in
    PayDemo, PayTest and LargerThanMemory, so bytes a put and time a
    commit there are not comparable with earlier runs; `performance.sh`'s
    long keys of 111 bytes (were 120), so its long-key results are not
    comparable with 2026.4's reference.

### Tests and gates

* **Count gates of aims 2 and 3** (bergdb 024-30): `stress/count-gates.sh`,
  a step of `night.sh` after level4 (about 2.5 minutes), at 1M keys and
  on counts, not times: the largest record (G1, at most 1 MB), key nodes
  against a twin built fresh (G2, at most 2 times), the stream kept beyond
  the history within the retain duration (G3, at most 6 times the live
  data) and back to empty (G4: 1M keys put and deleted, then within 2
  times a hello-world database's stream, key nodes, dead klongs, resident
  objects and heap; since 024-33 also the cache's table slots, ST6). Release
  2026.4 fails G1 and G2.
* **G5, back to empty by `maintain()` alone** (bergdb 024-32, section 4),
  in `count-gates.sh` beside G1 to G4: 1M keys put and deleted, then
  20,000 calls of `maintain()` and no writes: the stream kept falls from
  254 MB to 83 kB (the limit: twice a fresh twin's plus 600 kB), quiet
  after call 6,130; resident objects 10 against the twin's 5; the cache's
  slots within the floor of ST6 (Known issues). Two new conformance
  configurations, `r-maint` and `e-r-maint`, trace databases driven by
  `maintain()` (`TraceExport` `maint=K`) and pass the Lean checker.

### Documentation

* **`docs/` moved into item 027** (bergdb 027; Frans, 2026-11-12, 14:17,
  14:27 and 14:32). `levels.md`, `sis-model.md`, `sources/` and the
  readme are 027-01, a snapshot of 2026-11-12, not updated; the trace
  format is 027-02, kept current with the code; `docs/` holds only
  `log.md`, the development log. Code comments, the level scripts and the
  repository's readme cite them by ID. 2026.4's notes link `docs/` at
  their release commit.


The Lean model and the C clone
------------------------------

Only the Java code is the release (Frans, 2026-11-03); the Lean model and
the C clone are tools of the work.

**The Lean model** ([lean/README.md](../../lean/README.md)): 115 of its `.lean` files are new or changed since `release-2026.4`.
New since 2026.4: the key tree (024-12), a model of the index that Java
writes, with its search, its writer and the merges and theta of format 7
(024-22, 024-23); the tie of the model's physical steps to the stream
(024-09); the last touch's cut, T-COVER and T-LATEST (024-07); the take's
cap in the model's pace (024-31); and that the limits' nodes fit a record
(`ReleaseFits`, 024-24). The proofs that hold are in the release, each on
Lean's standard axioms (Verification); those not done are named under
Known issues (aim 4), and Java is checked against the model by
conformance on every night's run. The trace format is 027-02. A Lean
proof of the user indexes' model (020-29) is on a branch, not in the
release.

**The C clone** (item 022) matches release 2026.4, format 6; it does not
write format 7, and 2026.5 refuses its databases. Whether it follows
2026.5 is Frans's decision (022's readme).


Verification
------------

On the release commit, in clean clones (`baseline.zip`, `gates/`):

`java/night.sh large` on `3611130c`, 2026-11-12 15:20 to 2026-11-12 22:20
(`NIGHT OK`, 420 minutes, JDK 27.0.1.0.3). The release commit passed
`before-commit.sh` before the night, in a clean clone
(`BEFORE COMMIT OK (63 s)`).

| Step | Result | Time |
|---|---|---|
| `before-commit.sh`       | BEFORE COMMIT OK                         | 63 s |
| `stress/core-build.sh`   | CORE BUILD OK                            | 55 s |
| `level1.sh`              | LEVEL 1 OK                               | 140 s |
| `level2.sh`              | LEVEL 2 OK                               | 995 s |
| `level3.sh`              | LEVEL 3 OK                               | 441 s |
| `level4.sh`              | LEVEL 4 OK                               | 491 s |
| `count-gates`            | COUNT GATES OK                           | 129 s |
| `stress/lean-tests.sh`   | LEAN TESTS OK                            | 259 s |
| `tree-tests`             | TREE TESTS OK                            | 3179 s |
| night tests              | SUCCESS, 26 tests                        | 816 s |
| `stress/harness-soak.sh` | HARNESS SOAK OK: 10 jobs, 2 rounds       | 119 s |
| `stress/fuzz.sh`         | FUZZ OK                                  | 721 s |
| `unlinkfuzz`             | UNLINKFUZZ OK (3226 rounds, 286 s)       | 286 s |
| `stress/kill-restart.sh` | KILL RESTART OK: 1000 kills and 49 exits | 1433 s |
| `conformance.sh medium`  | CONFORMANCE OK                           | 141 s |
| `conformance.sh large`   | CONFORMANCE OK                           | 15932 s |

* Lean: `lake build` of every proof (in the level scripts); the theorems that
  [lean/README.md](../../lean/README.md) lists for `#print axioms`, 52, each depend on
  Lean's standard axioms only (`propext`, `Classical.choice`, `Quot.sound`, or a part
  of them; no `sorry`).

* jcstress (harness 6.6, 018-08, section 4): the 8 tests of
  `java/stress/jcstress/` in jcstress's default mode on F53 with JDK 27,
  every one OK (`f53/jcstress.txt`).

* The tests again, with `-ea`, on F53, in `night.sh large` with JDK 27:
  1,700 unit tests and 89 f-tests (`before-commit.sh`) and 26 night tests,
  all passed; on s1 (Linux, 2 cores, 3.8 GB) with JDK 27 and 17, from the
  tests' jar of the same build: 1,700 unit tests, 89 f-tests and 26 night
  tests on each, all passed, with `java.io.tmpdir` on the disk (s1's `/tmp`
  is a 1.9 GB tmpfs, 015-11).

* A user's program, compiled from the Javadoc against the release jar alone
  (`bergdb-2026.5.jar`; `baseline.zip`, `tools/userprog/`) by each JDK's
  `javac --release 17`: `open(p)` refuses an empty directory and writes
  nothing; `create(p)` creates a database, commits, syncs and closes it; in
  a new JVM `open(p)` reads it back, writes and closes: `USERPROG OK` with
  JDK 27 and 17, on s1. `java/build.sh` also runs user code with the
  release jar alone (`ReleaseDemo`: the Pub API's values and `Db`, through
  a restart) in every build.

* Android: `java/stress/android.sh` on an Android emulator on F53: the unit
  tests, 1,696 passed and 4 skipped (those that check what only a JVM has),
  and 10 runs of the demos, all OK (`f53/android.txt`).

* StreamDigest: 2026.5's 12 configurations in 4 modes (plain, reads,
  restarts and `restarts-once`), the modes agree (`baseline.zip`,
  `f53/digests.txt`, the reference for later versions). 2026.4's jar, run
  again on the same workloads, gives its release's digests, 48 of 48, so
  the workloads are the same. 2026.5 against 2026.4: the decided digests
  differ in 48 of 48, in 12 configurations, all of them, which
  releases/next.md names (Format: record format 7, with merges, theta and
  CRC32C, and the last touch; 018-01, 024-07, 024-21, 024-23, 024-25,
  024-31, 024-32, 024-33, 024-34, 024-38). 2026.5's digests are those that
  024-38 recorded from the release commit's code (`digests-new.txt` in its
  folder, with 2026.4's as `digests-base.txt`). The physical cut's fields
  differ by timing (015-08).

* UnlinkFuzz, the fuzzer of the deletes' cleanup in the index alone
  (023-09, sections 2 and 5), with `-ea` and JDK 27 on s1, 2026-11-12 16:24
  to 2026-11-13 04:30: 85,700 seeds in 8 configurations, 0 failures, 0
  timeouts (`s1/fuzz/`): the shapes fifo, long, random; the keys of a
  transaction sorted or shuffled, some of them twice (`dup`); up to 200
  operations a transaction and 1,000 keys; node sizes 4, 8, 14, 30. Each
  run checks against a model of every key's history: its gets and scans at
  every time, and the tree's rules after each transaction. The seeds are
  new, from 3,000,001 (2026.4's nights ran from 1,000,001 and 2,000,001);
  by configuration (`s1/fuzz/fuzz.txt` has their properties): a 4,900, b
  16,550, c 4,900, d 16,550, e 4,900, f 16,550, g 4,850, h 16,500.

* OT2's probe (024-36, section 5): `LockWindowProbe` loops
  `FileStreamPowerLossTester`'s three failure tests on s1 (ext4, JDK 17),
  two JVMs at a time, the test fix reverted so that the tests race: with
  OT2's fix (`FileStream.unlockDir`, the same file as in the release) 0
  starts refused as in use in 300,000 tests (10 JVMs of 10,000 rounds); the
  control without the fix, 24 in 60,000 (`s1/ot2/`).

* 024-07's queue in time order at 10,000,000 keys (the last touch's case,
  2026.4's first known issue; 024-07, section 8's method: 13-byte keys,
  values of 100 bytes, 100 puts after every key and 100 deletes of the
  oldest a transaction, a retain duration of 1 s, the builder's defaults,
  G1 and 8 GB): 200,000 transactions, 2 reclaim iterations; the largest
  record 30,832 bytes and 0 records over 1 MB (2026.4: 206,065,600 bytes, a
  commit of 20.6 to 22.3 s); at most 17 index nodes made dirty by a step;
  commits p50 563us, p99.9 2639us, the slowest 68ms; 23,624 bytes written a
  transaction (`f53/queue/`).

**The search for unknown faults** for 2026.5 (024):

* New users' applications against the limits and the refusals (024-26),
  a sweep of what was forgotten before the release (024-35), and the
  reviews of each change (024-21 to 024-25 and later).
* The count gates of aims 2 and 3 at 1M keys (024-30), against a twin
  built fresh: the largest record, the key nodes after deletes, the
  stream kept under reclaim, back to empty, and back to empty by
  `maintain()` alone.
* The key tree's conformance (024-12, 024-22, 024-23): Java's index after
  every transaction of a trace against the Lean model's.
* Every change was gated by `before-commit.sh`, and a change of a level's
  mechanism by that level's script.


Lines of code
-------------

Files in git at the release commit:

| Part | Files | Lines |
|---|---|---|
| `java/src`        | 274 | 133,335 |
| `java/src-dev`    | 124 | 14,026 |
| `java/stress`     | 42  | 14,872 |
| `lean`            | 206 | 70,882 |
| `docs` (Markdown) | 1   | 1,786 |

2026.4's, in the same way: 268, 124, 40, 120 and 7 files; 126,390,
14,008, 13,695, 52,271 and 5,107 lines. `docs` now holds only `log.md`:
the rest of the documentation is 027-01's snapshot (Documentation).


Baseline
--------

A performance comparison of 2026.5 with release 2026.4 before the release,
as 2026.4 had with 2026.3 (020-12): `performance.sh ab` with the quick
suite (`read-1k`, `w-uni-1k-inf`, `w-uni-1k-fin`, `r-1k-fin`; 3 runs each,
the two builds in turns, ABBA), on an F53 that was not quiet (FORCE=1), JDK
27, G1 and an 8 GB heap: no alerts (`f53/perf/compare.txt`). The figures
that it prints:

| Scenario, metric | 2026.4 | 2026.5 | Change |
|---|---|---|---|
| r-1k-fin mix.commits_per_s        | 51,907.7 | 107,048.0 | +106.2% |
| r-1k-fin mix.gets_per_s           | 2,411,100 | 2,314,320 | -4.0% |
| r-1k-fin mix.puts_per_s           | 51,907.7 | 107,048.0 | +106.2% |
| r-1k-fin startup.sec              | 0.7597 | 0.5581 | -26.5% |
| read-1k get_historical.ops_per_s  | 1,211,590 | 1,199,250 | -1.0% |
| read-1k get_latest.ops_per_s      | 1,226,850 | 1,350,620 | +10.1% |
| read-1k get_latest_mt4.ops_per_s  | 4,313,440 | 4,775,960 | +10.7% |
| read-1k get_longkey.ops_per_s     | 896,299.0 | 971,787.0 | +8.4% |
| read-1k scan_back.kvs_per_s       | 3,998,610 | 4,146,300 | +3.7% |
| read-1k scan_back.scans_per_s     | 39,986.1 | 41,463.0 | +3.7% |
| read-1k scan_fwd.kvs_per_s        | 3,793,780 | 3,931,820 | +3.6% |
| read-1k scan_fwd.scans_per_s      | 37,937.8 | 39,318.2 | +3.6% |
| read-1k scan_fwd_hist.kvs_per_s   | 3,477,880 | 3,510,420 | +0.9% |
| read-1k scan_fwd_hist.scans_per_s | 34,778.8 | 35,104.2 | +0.9% |
| w-uni-1k-fin commits_per_s        | 64,060.6 | 140,239.0 | +118.9% |
| w-uni-1k-fin puts_per_s           | 64,060.6 | 140,239.0 | +118.9% |
| w-uni-1k-fin restart.startup_sec  | 0.6860 | 0.4776 | -30.4% |
| w-uni-1k-fin user_mb_per_s        | 64.317 | 140.8 | +118.9% |
| w-uni-1k-inf commits_per_s        | 98,321.4 | 237,997.0 | +142.1% |
| w-uni-1k-inf puts_per_s           | 98,321.4 | 237,997.0 | +142.1% |
| w-uni-1k-inf restart.startup_sec  | 0.7081 | 0.4931 | -30.4% |
| w-uni-1k-inf user_mb_per_s        | 98.715 | 238.9 | +142.1% |

Long keys are of 111 bytes in both runs (024-24), so they compare with each
other, not with 2026.4's own reference.

The main reason for the faster writes and restarts is the node checksum:
CRC32C in place of Fletcher-16 (024-25). Fletcher-16 took about 5.6 ms a
MB, CRC32C about 0.12 ms a MB, and every node written, or read at a
start, is checksummed. Checked on 2026-11-13 with the commits just before
and after that change (e9b9b4cd and 3dd38b23; `w-uni-1k-inf`, one run
each, F53 not quiet): 93,892 against 236,737 commits a second (+152%),
and a restart of 0.705 against 0.463 s (-34%); so the whole gain over
2026.4 comes with that one commit. The durability is the same as in
2026.4: no sync was removed or weakened, and the buffer time and the sync
levels have the same defaults.

StreamDigest's digests (`baseline.zip`, `f53/digests.txt`) are the
reference for the next release.


How to compare a later version
------------------------------

As for 2026.4 (its notes): run 2026.5 again beside the later version, in
turns, on the same machine and JDK, with one compiled copy of each tool per
jar. **StreamDigest**: compile the later tree's
`java/stress/StreamDigest.java` against each jar, run each copy on its jar,
and compare the decided digests (`digest-compare.py` in `tools/`, or
StreamDigest's `compare`); the physical cut's fields depend on timing
(015-08). `tools/checks.sh` does this for 2026.5 against 2026.4.
**Performance**: `java/stress/performance.sh ab` with preserved builds of
both (`tools/perf.sh` did it for 2026.5 against 2026.4). The tools need
the tests' jar or `build/stress` of the same tree; the release jar has no
tools.


Known issues and limits
-----------------------

**No entry of 019 or 021 is open at the release commit** but those named below. Entries listed as open in 019's or 021's table at the release commit that
the known issues below name: 021-27.

**Fixed, found or decided for 2026.5, or a limit** (releases/next.md;
each of 2026.4's known issues is restated there as fixed, changed or still so):

* **Fixed: reclaim with keys in time order** (bergdb 024-07; 2026.4's
  Known issues, its first entry): the heap that ran out in a user's commit
  and the record limit that stopped reclaim at about 104M keys (Core API,
  above).
* **Fixed: on Linux, a new database in a new directory refused as in use**
  (bergdb 024-36, OT2; 2026.4's Known issues): `FileStream` now closes
  `bergdb.lock` and removes the directory from its set of locked
  directories in one step, under the monitor under which a start checks
  that set, so a start in the same JVM right after a close (as a background
  close after `stop()` of a database whose directory was deleted) no longer
  finds a new directory's reused inode still listed. Left: a start in
  another class loader of the same JVM can still, rarely, be refused in
  that moment; a retry works. Test
  `FileStream.testNoStartSeesAClosedLockStillListed`.
* **Fixed: a Core put under the Core's own keys** (CA3; bergdb 024-37;
  024-01, section 5.3): a database that never opened again after a put
  at `/#i/dreclaim/-settings.txt` through `Db` (Core API, above).
* **Fixed: `Db.getTrans` at a position inside a record** (bergdb 021-27;
  2026.4's Known issues, "Open at the release"): it is refused and the
  database goes on (Core API, above).
* **Fixed: a damaged time klong whose unused bits are set** (bergdb
  024-25, section 12; 2026.4's Known issues): a start refuses it (Core
  API, above).

**New in 2026.5:**

* **Aim 4, the model: proved in part, the rest checked by conformance**
  (bergdb 024-04, aim 4; 024-28, section 6; Frans, 2026-11-12, 12:22:
  2026.5 ships with conformance and the proofs that hold, the open ones
  named here). Proved: the tie of the model to the stream (`PhysStep`),
  the last touch's cut (T-COVER, T-LATEST), `T3_take`, the tree's spec
  (TP13, TP17, TP18), TP1 and TP9, the merge's local parts, and that the
  limits' nodes fit a record (`ReleaseFits`). Not proved: TP7 (the tree's
  invariants), TP10 (a get), TP30 (V1 kept, the large part of the
  B-tree's proof; reduced to TP7), TP31 (BU1, the fill of a key node), TP32
  (the merges of a transaction, restated for sorted transactions) and
  TP33 (CB3, a potential);
  TP11 (a scan) is refuted as stated, for keys that Java does not make,
  and its fix is decided: the model's `keyWf` is to say what
  `Keys.toSegments` makes (024-12; Frans, 2026-11-12, 13:38); and T4, the
  records at the startup section's ends, and a cold start's reads (007).
  What is not proved is checked by conformance: Java's traces are run
  against the model at every night's gate (`night.sh`'s level scripts
  and conformance steps; the large set in the release night) and hold on
  every traced state (024-12: 115 traces, with merges 260, with theta
  222).
* **An emptied database keeps the cache's tables at a floor of about
  256 kB** (bergdb 024-32, section 7; ST6 after 024-33). A map of the node
  table that was used keeps at least 16 slots, so a database brought back
  to empty keeps up to 4,096 maps of 16 slots, about 256 kB, whatever its
  size before (3,099 maps after 1M keys; a fresh database uses 5). G4 and
  G5 allow that floor.
* **Moved to 2026.6** (bergdb 024-05; 026): ST8, the 10 MB write buffer
  that every database allocates at its start, whatever its size; P8, the
  lag after a mass delete: an emptied database needs about 4.4 retain
  durations of further writes before its stream comes back near a fresh
  one's (G4: the first cut after the deletes at transaction 4,117, the
  twin's at 1,214; `maintain()` does it without writes).
* **A single put's record of about 0.25 MB now and then** (bergdb
  024-05, OP5, a named allowance; Frans, 2026-10-28; 010-01, P4). The
  take writes whole transactions: with single puts alone at 10M keys a
  record is at most 0.23 to 0.29 MB, the mean under 1 kB; with a batch of
  500 now and then among single puts a put's record reached 209 kB
  against a mean of 576 bytes (sd 1 MB, 20,000 keys; 007-07, section
  7.1). Large as a ratio, small in bytes; it grows with the batch.
* **A value transformation (Core API) that throws or passes 8 MiB fails
  the database** (bergdb 010-04, R5; 024-24, QL6; Limits, above), as
  in 2026.4; a restart has the state before its transaction. To change in
  2026.6 (Frans, 2026-11-12, 14:42: "I don't see it
  as a bug, but something to change anyhow.").
* **A put's stream bytes grow with the keys at a fixed startup distance**
  (bergdb 024-05, QF3, OP3 and BD5; 017-11, section 2.1; Frans,
  2026-11-12, 12:46). A put makes the index nodes on its path dirty, and
  the take writes each dirty node whole about once a startup distance of
  stream, so the puts in between share its write: a put's bytes are a
  function of the startup distance a key, sd / K, for a key shape, a
  value size and a node size. For 32-byte KVs (24-byte keys, 8-byte
  values), uniform updates and retention forever, bytes a put by sd a
  key: about 270 at 50 bytes (1M keys and 50 MB, the model), 190 at 100
  bytes (10M keys and 1000 MB), 524 at 20 bytes (10M keys and 200 MB),
  854 and 867 at 5 bytes (1M keys and 5 MB; 10M keys and 50 MB), 1,244
  at 1 byte (50M keys and 50 MB), about 1,380 at 0.5 bytes (100M keys and
  50 MB, the model); the rest measured, the law within about 15 %. So at
  the default 50 MB each tenfold growth of the keys adds about 400 to 650
  bytes a put, and a startup distance that grows with the keys keeps it
  constant, at the price of a start's time and heap (a warm start 2 to 5
  s at 50 MB, 8 to 20 s at 200 MB, 40 to 100 s at 1000 MB; 017-11,
  section 2.2). Reclaim adds at most about a third; larger values write
  fewer index bytes over the user's bytes. The default stays 50 MB, which
  suits up to about 10M keys; beyond that, 200 to 1000 MB. A default that
  follows the keys is studied in 017-11, not for 2026.5.
* **The stream kept under reclaim: about 4.5 to 6 times the live data
  beyond the history** (bergdb 024-05, QF1, decided by Frans, 2026-11-12,
  14:07; 024-30, G3; 024-29, section 9). With a finite retain duration,
  reclaim may rewrite a quarter of the stream's growth (its internal
  fraction, 1/4 since BergDB's first commit, kept for 2026.5). The stream
  then holds the records within the retain duration, the history, and
  beyond them up to about 6 times a fresh database of the same live keys:
  G3 measures 4.41 at 1M keys under uniform overwrites and fails above 6,
  in every `night.sh`. A larger fraction keeps less for more bytes written
  (at 1M keys 3/8 keeps 8 to 29 % less, for 15 to 27 % more bytes and 23
  % fewer puts a second). The fraction is no Pub API setting; three
  recommended fractions and a default, measured on larger databases, are
  for 2026.6 (026-04).

**From 2026.4's Known issues and limits** (`releases/2026.4/readme.md`),
each as it is in 2026.5:

* **Fixed**: reclaim with keys in time order (024-07), on Linux a new
  directory refused as in use (024-36), `Db.getTrans` inside a record
  (021-27), a damaged time klong (024-25), a Core put under the Core's own
  keys (024-37; part of "Writes through the Core that the rules leave
  undefined"), all above. 2026.4's two fixed entries (021-25's log keyed
  by time, the puts slowed after reclaim passed deleted keys) stay fixed.
* **Changed: a leaf keeps the entries of its deleted keys** (023-08, Q5):
  now underfull key nodes are merged at the delete (024-21), and a key
  node holds at most theta dead entries (024-23), so a node that is
  written keeps few; G2 holds the reachable key nodes within twice a fresh
  twin's (1.30 at 1M keys; 16.0 on 2026.4).
* **Changed: a decrease of the startup distance at 50M keys**, records of
  13 to 15 MB: the take's cap (024-31) halves the catch-up's largest
  records at 10M keys; not measured again at 50M.
* **Changed: a long key's still-dirty loop is quadratic** (021-16, Q1;
  024-05, OP6): a user's key is now at most 111 bytes (L2), so no user's
  key reaches it; the loop is as before for BergDB's own long keys.
* **Changed: other damage that a start does not detect** (019-30, 019-31,
  019-33): CRC32C sees every change of up to 32 adjacent bits (019-33's
  0x00 to 0xff is seen) and a start checks a time klong's unused bits;
  BergDB still assumes correct storage, and its checks are a best effort.
* **Changed: the documentation**: `docs/` is now a snapshot of 2026-11-12
  in item 027-01 (levels.md, sis-model.md, sources/), not kept current;
  the trace format is 027-02, kept current; `docs/` holds `log.md` only
  (Documentation, below).
* **Still so**: after a mass delete, more dirty top nodes for a while
  (023-03, section 10); a lost or cut last stream file (020-24-08, U8-1);
  a transaction larger than the startup distance (020-24-13, U13-7; now at
  most 32 MiB, L5); the user indexes' threads, a job's status that lags
  its index, a fair lock for builds (020-18, O1 and O2; 020-29, section
  7); the Core's other writes that the rules leave undefined (020-22,
  sections 5 and 6); the API's wishes (020-24-13, 020-24-14); a corrupt
  record header (015-73; no checksum covers it in format 7 either); at
  most as many busy readers as the cores less the collector's workers
  (015-86); the collectors; overload; a small commit after a large
  transaction (007-07, sections 7.1 and 7.2); D's loose bound (005-38);
  the default startup distance (above, the put's bytes); loads in memory
  8 to 20 % slower than before handles; bounded startup, T4 and a cold
  start not proved (above, aim 4); the files after a physical cut
  (005-72); concurrency outside the Lean model; power loss; the JDKs and
  systems tested: JDK 27 and 17, macOS and Linux, an Android emulator.


Post-release notes
------------------

A fault found later that affects 2026.5, its numbers or its correctness,
is recorded here. No fault yet.

**Changes since the release:**

* 2026-11-13: 021-27, named as open at the release commit in Known
  issues and limits, was closed on 2026-11-12: fixed by `9dd125f3` and
  `ba7583b9` (`Db.getTrans` at a position inside a record, Core API),
  both before the release commit and in 2026.5; 021's table still listed
  it as open there.
* 2026-11-13: the Lean proof of the user indexes' model (020-29), "on a
  branch, not in the release" (The Lean model and the C clone), is on
  `main` since `868f353f` (Frans, 08:04: "Merge it."): `lake build` 291
  jobs, its 15 theorems on the standard axioms. It is not in the release
  commit or the source zip. The jar, the zips and `SHA256SUMS` did not
  change.
