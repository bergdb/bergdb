BergDB 2026.6
=============

Released 2026-11-24 by Frans Lundberg, as planned in bergdb item 026
([../../items/026-release-2026-6/readme.md](../../items/026-release-2026-6/readme.md)).


Files
-----

The files are on the GitHub release of the tag `release-2026.6`,
<https://github.com/bergdb/bergdb/releases/tag/release-2026.6>:

* `bergdb-2026.6.jar`: the users' jar, `java/build/bergdb-release.jar`
  made by `java/build.sh` from the release commit. SHA-256
  `df394c0ad4356d8c95d68a0bff38ab4828add21436dcf3ffd94fcb681c61602d`.
* `bergdb-2026.6-javadoc.zip`: the Pub API's Javadoc, made by
  `java/javadoc-pub.sh`, in the directory `bergdb-2026.6-javadoc/`.
  SHA-256
  `a04d17e51edfdb9287de76f8b86dc2a458c6e17ae68843409acfdc5fdd8bc618`.

`releases/2026.6/` in the repository holds these notes and `SHA256SUMS`;
check the downloaded files with `shasum -a 256 -c SHA256SUMS`. The
source is GitHub's archive of the tag.


Identity
--------

* Tag `release-2026.6`, commit
  `bbcd802f925d4918eb779d0dbe86c58e339a3758` (2026-11-23 23:12).
* `BuildInfo`: release 2026.6, release int 266, build
  2026.6.261123.2312; `java -cp bergdb-2026.6.jar bergdb.core.BuildInfo`
  prints them.
* Built by `java/build.sh` (`javac --release 17`) with JDK 27.0.1.1, in
  a clean clone of the release commit.


Changes
-------

### The theme

**Proven algorithms** (Frans, 2026-11-19), after 2026.5's solid
algorithms: BergDB's core algorithms are proved, given tested
assumptions. The core algorithms are those of the Core, BergDB's
key-value store of byte arrays: the writer, which applies a transaction
to the index; the reads, at the latest time and at earlier times; crash
recovery and startup; eviction; and reclaim, which cuts the front of the
stream. Each is proved in Lean, a language whose checker verifies every
step of a proof, for a model of BergDB, given a short list of
assumptions that are tested instead, among them that Java does what the
model does, which the tests check transaction by transaction. The Pub
layer, threads and the costs are outside the model.
[bergdb 030-26](../../items/030-proofs/26-core-algorithms-proved.md) states
the claim, what is proved, the model and its limits;
[bergdb 030-38](../../items/030-proofs/38-guarantees.md) gives what a user
gets from it as a closed list of guarantees, G1 to G14, each marked
proved, with its theorem and its conditions, or tested on purpose, with
its check and the script that runs it. An independent review,
[bergdb 030-39](../../items/030-proofs/39-guarantees-review.md), read each
guarantee against its theorem's statement and its check's script; each
place where the list said more than is proved or checked is corrected
there, or accepted with its reason. The conditions are under Known
issues and limits, below.

In short:

* **A new writer, the proved one** (The stream, below): PE, "plan, then
  emit". The proofs are about it; release 2026.5's writer is another and
  is not covered by them.
* **Databases of release 2026.5 and earlier are refused: make them
  again** (The stream, below). There is no upgrade tool.
* **Three released bugs of 2026.5 are fixed**, RB-001 to RB-003
  (Released bugs fixed, below). No bug is known in 2026.6 at its
  release.
* **Speed against 2026.5:** writes with reclaim at work up to 27 %
  faster; writes without reclaim 6 to 10 % slower; reads up to 5 %
  slower, and the gets beside writes 12 % slower (Speed against 2026.5,
  below).
* **Less memory for a small database:** the write buffer grows with use,
  from 64 KiB, instead of 10 MB at every start (Memory, below).
* **The stable stream format waits for a later release**, perhaps more
  than one release later, together with encryption and replication.
* **The files**: the jar and the Pub API's Javadoc are on the GitHub
  release of the tag `release-2026.6` (Files, above).


### Released bugs fixed

The register of released bugs is
[bergdb 033](../../items/033-bugs/readme.md): a fault in the code of a
published release, each with an ID and a severity (S1 data lost or
wrong, S2 the database fails or will not start, S3 a call fails or
refuses wrongly, S4 minor). This release fixes the three that 2026.5
has:

* **RB-001, S2. A value transformation that throws or passes 8 MiB fails
  the database.** A value transformation of the Core API that threw, or
  whose result was over 8 MiB, failed the database instead of refusing
  the transaction; a restart had the state before that transaction.
  Named in 2026.5's Known issues. Now the transaction is refused and the
  database goes on (Core API, below; bergdb 026-06).
* **RB-002, S2. A key transformation that throws fails the database.**
  The same for a key transformation of the Core API that threw a
  `RuntimeException`. Now refused in the same way (bergdb 026-06).
* **RB-003, S4. The Core API's Javadoc did not say that a new database
  is durable only at its first sync.** With the Core API, a crash after
  the creating `Db.start()` returned and before a sync could make the
  next start throw `DatabaseNotCreatedException`. The Javadoc now says
  so (Core API, below; bergdb 028-40); the Pub API syncs the creation in
  its start and was not affected. Nothing committed was lost.


### The stream

* **Databases of release 2026.5 and earlier are refused: make them again**
  (bergdb 028-15, option A; Frans, 2026-11-18, 10:50). The startup
  distance moved out of the meta blocks into a key-value pair of BergDB's
  own, `/#i/-sd`, and the meta block's version is 155 (154 until now). A
  start of an older database throws a
  `VersioningStreamException` whose message names release 2026.5, and
  writes nothing. To keep the data, read it with the release that wrote
  it and put it into a new database with this release, for example with
  two programs, one on each release's jar (the releases' classes have
  the same names); the history is not copied. Release 2026.5 opens a
  database of 2026.5, not one of 2026.4 or earlier: read a database of
  2026.4 with 2026.4, and one of 2026.3 or earlier with the release that
  wrote it (bergdb 028-30). Releases 2026.5 and 2026.4 refuse a database
  of this release by its meta block's version, with the message "Cannot
  read meta block with version 155. Version supported: 154", and write
  nothing. A change of the startup distance
  (`Database.setStartupDistanceInMb`, `Db.setStartupDistance`) now writes
  a small transaction, not one of 200 kB, and a crash inside it starts
  with the old setting. The Core API: every database has that
  key-value pair from its creation on, and a scan of the whole key space
  returns it (Db, "Keys and the layers above"); the creation writes two
  records, so a new database's first transaction has a time one unit
  later than before. The stream's bytes changed for every configuration
  of StreamDigest (a record after the primordial one, and no dummy
  value).
* **A crash while a database is created gives `DatabaseNotCreatedException`,
  also between the creation's two records** (bergdb 028-18, option C;
  Frans, 2026-11-19, 09:53). A creation now writes two records, the empty
  database and the startup distance; a start that finds the first
  without the second refuses the database as not created and writes
  nothing, as for a crash earlier in the creation: remove the files and
  start again (`DatabaseNotCreatedException`'s Javadoc). So a database is
  created whole or not at all. With the Pub API, `created.txt` is written
  after both records are synced, before `start()` returns.
* **The writer is PE, the writer that is proved to meet the writer's
  contract; record format 8** (bergdb 026-25, 030-21; Frans, 2026-11-19,
  09:32). A transaction's keys and values reach the key tree as one
  batch: the writer plans the whole transaction over the tree, decides
  each index node once, and then writes each decided node once ("plan,
  then emit"), where the writer of 2026.5 changed the tree key by key,
  with splits in place, merges at a delete and nodes made and taken back
  within a transaction. It is the writer that bergdb 030-21 proves:
  every history it writes meets the writer's contract, from which the
  reads, recovery, restarts, eviction and reclaim's cuts are proved
  (bergdb 030, the release's theme); the level scripts compare Java,
  node by node, with a copy of it at every traced transaction, and the
  copy with it (030-28). What a program reads is unchanged; the trees
  have other shapes. Each record has the record format 8 (7 until now),
  as the same record makes another tree with this writer: a database
  written with format 7 by a development build of this release is
  refused with a message, and one of release 2026.5 is refused by the
  meta block's version, as above. Speed (bergdb 026-25, section 7): at
  10M keys within a few per cent of 2026.5's writer, the load of
  transactions of 100 or 500 puts 0.90 to 0.97 of its puts a second; a
  small database in memory 11 to 18 % slower in CORE's set; with reclaim
  more cuts, less of the stream kept and about 6 % more bytes written;
  follow-up work is bergdb 028-19. The stream's bytes changed for every
  configuration of StreamDigest, the l2-* and the l3-* ones; the digests
  before and after are in bergdb 030-28, section 6. Tests whose expected
  values changed: a few thresholds of tests that depend on the tree's
  shape, and `StoredTrans.testRefusesFormat6`, which refuses formats 6
  and 7 (026-25).
* **Reclaim charges every index node that its steps make dirty** (bergdb
  028-26). With a finite retain duration (`setRetainDuration`), a
  reclaim step's internal transaction counts toward reclaim's allowance,
  a fraction of the stream's growth, the bytes of the index nodes that
  it makes dirty; since record format 8 and its writer it counted only
  those on its keys' paths, not the nodes that the writer makes (found
  by a review of the writer). It now counts them too, and stores its
  progress again in a small internal transaction of its own after most
  steps, so a restart resumes with the same count. Reclaim so keeps
  closer to its fraction: in a test workload with reclaim the stream
  grew 1.5 to 7.8 % less. The stream's bytes changed for StreamDigest's
  l3-* configurations (reclaim on), not for the l2-* ones; the digests
  before and after are in 028-26.
* **Each reclaim step scans at its own time: a mass delete's space comes
  back sooner** (bergdb 026-05; 024-05, OP9; Frans, 2026-11-12, 12:10).
  With a finite retain duration, a reclaim step scanned the keys that
  were live when its iteration began, so after a mass delete the
  iteration then running walked the deleted keys as well, and the stream
  came back near a fresh database's only after a lag that grew with the
  keys: up to 33,501 transactions at 10M keys. Each step now scans at its
  own time and does not meet the deleted keys: the lag is 1,265 to 1,286
  transactions at 1M, 4M and 10M keys, and a count gate checks it every
  night (bergdb 026-11; 2026.5's Known issues, P8). A cut that is ready
  is now made before a newer one replaces it. Reclaim's records change
  (other steps, and an end key in its row); no record format change. The
  stream's bytes changed for StreamDigest's l3-* configurations
  (reclaim on).
* **A reclaim step does not load the values it does not write again**
  (bergdb 026-09; 024-34, Q34-1, option (b); Frans, 2026-11-13, 09:38,
  and 2026-11-14, 11:35). A step's scan no longer reads from the stream
  the values stored at or after the cut it prepares, which it does not
  write again: at 1M and 10M keys the steps' loads fall by 44 to 60 %
  and the steps by 14 to 20 %, for 1 to 4 % more stream written at 10M
  keys. The stream's bytes changed for StreamDigest's l3-every1, l3-node8
  and l3-node62 (026-09, section 6.5).
* **Two more kinds of damage are refused, not taken for data** (bergdb
  028-09, 028-14). A start refuses a last record that names its own
  position as the startup position, with a `StreamFormatException`;
  before, the start went on and the database lacked committed keys. A
  get that follows a damaged top node's skip pointer back to the same
  node now fails the database; before, it never ended. BergDB still
  assumes correct storage: its checks for damaged bytes are a best
  effort.

### Pub API

* **`DatabaseBuilder.startupDistanceInMb` removed: set the startup distance
  with `Database.setStartupDistanceInMb` after `start()`** (bergdb 028-13;
  Frans, 2026-11-19, 11:06 and 11:10). A new database has 50 MB, as the
  builder's default was; a program that set another calls the setter
  right after `start()`, also the start that creates the database. The
  setter clamps to 5 to 1,000 MB, as the builder's method did, and the
  stream keeps the setting over restarts, as before. The facts of the
  builder's Javadoc (start time, heap, the write buffer) are now the
  setter's. On a new database the call writes a small transaction of the
  database's own after the creation.
* **`bergdb.pub.Limits`: the limits as constants, and a check of a key
  before a call, a new class** (bergdb 026-02, option A; Frans,
  2026-11-13, 09:11, QK1 to QK4). `Limits.MAX_KEY_BYTES` and the other
  limits, L1 to L6, as constants, the Core's `Db`'s by reference;
  `Limits.keyBytes(String key)`, a key's bytes as stored (its UTF-8 and
  one byte more for each '/'), also for a key over the limit, so that a
  program knows how far over it is; `Limits.checkKey(String key)`, which
  throws the very `IllegalArgumentException`, with the same message,
  that a put or a delete throws for the key. Both depend on the key
  alone, not on a database or a connection. A program no longer learns
  of a long key from a refused put, which spoils a `WBuilder` (024-27,
  QR1). A put, a delete and `checkKey` run one check
  (`PubKeys.checkedIkey`), and a property test compares `keyBytes` and
  `checkKey` with a put on a memory database. L6, an object's levels in
  an index entry, has no method: the Javadoc of `Limits` says how to
  count them (QK3). The Core API gets no method: a key fits if its
  bytes are at most `Db.MAX_KEY_BYTES`, as Db's Javadoc now says
  (option E). No stream change; no test's expected value changed.
* **Starts no longer wait for each other** (bergdb 028-07). A start held
  a lock of the whole JVM through its first sync, so one start that
  waited, on a slow disk or after an `OutOfMemoryError`, held up every
  other start and open of the Pub API in the JVM. Starts of different
  databases now run at the same time; two starts of one directory are
  ordered as before, the second refused with `DirectoryInUseException`.
  The date in `created.txt` is now formatted in a thread-safe way.


### Core API

* **`DbBuilder.startupDistance` removed; `Db.setStartupDistance` takes the
  whole range, 10 bytes to 10^9, and returns the value set** (bergdb
  028-13; Frans, 2026-11-19, 11:06 and 11:10). A new database has 50 MB;
  another is set with the setter after `start()`. The setter clamps to 10
  to 10^9 bytes (400,000 to 10^9 until now, a floor that served the
  200 kB dummy value that 028-15 removed), so that tests can use any value
  of the range; it returns the clamped value, the setting in force, which
  `getStartupDistance()` gives too (it returned nothing until now). A
  value below 1 is refused with `IllegalArgumentException` (0 was clamped
  until now). The builder took 10 to 10^9 and refused values outside.
* **A value transformation that throws or passes 8 MiB refuses its
  transaction; the database goes on** (bergdb 026-06; 010-04, R5; Frans,
  2026-11-12, 14:42). A user transaction's value transformations now
  run in `Db.execute()` under the write lock, after the key
  transformations and before the go point, in key order, each with the
  value as given and the key's value before the transaction, as before.
  A `RuntimeException` from one, a result over 8 MiB (L4), or results
  that take the transaction over 32 MiB of keys and values (L5) refuse
  the transaction with a `DbException` (the exception as its cause):
  nothing is written, and the `Trans` is left as it was, its values as
  given, its keys as written, its time given back, so it can be run
  again. In 2026.5 each failed the database (2026.5's Known issues;
  024-24, QL6; 015-51). An `Error` still fails it. **A key
  transformation that throws** a `RuntimeException` is refused in the
  same way (026-06, D9). No stream change. Tests whose expected values
  changed: `DbTesterLimits.testTransformedValueOverL4`,
  `DbTester.testTransformedValueBeyondRecordLimit`, `LimitsTester` (a
  result above the value limit refused, no run ends by the caller's
  fault), and three of `DbTesterFailure` that now fail after the go
  point by a test hook.
* **The node size is 30 for every database; `DbBuilder`'s setters of it
  are gone** (bergdb 026-08; Frans, 2026-11-13, 09:17 and 09:21).
  `DbBuilder.maxNodeSize8()`, `maxNodeSize14()`, `maxNodeSize30()` and
  `maxNodeSize62()` are no longer public: a database made by the Core
  API has the node size 30, as one made by the Pub API always had, and
  the stream format promises that size only (027-03, section 6). A
  program that called `maxNodeSize30()` drops the call; one that made a
  database at 8, 14 or 62 cannot start it with this release, which
  refuses it, as before, with a `StreamFormatException` that writes
  nothing (the meta block's node-size field is kept and checked, a hook
  for a later release that allows other sizes). The other sizes stay for
  BergDB's own tests (`bergdb.core.TestNodeSize`, not API). No stream
  change; no test's expected value changed.
* **`Db.start(StartParams)`, `Db.StartParams` and the start listeners
  removed** (bergdb 028-10, option A; Frans, 2026-11-14, 12:10).
  `Db.start()` is the only start: it takes the startup position and the
  startup distance from the stream. The removed method took a caller's
  values unchecked, and a wrong startup position could start a database
  without committed keys and keep them lost; 2026.5's Javadoc called
  these members internal and for tests. Gone with them:
  `Db.StartListener`, `Db.PrintStartListener` and
  `Db.SYSTEM_OUT_START_LISTENER`.
* **The Javadoc: a new database of the Core API is durable at its first
  sync** (RB-003; bergdb 028-40; Frans, 2026-11-20). `Db.start()` and
  `DatabaseNotCreatedException` say that a crash after the creating
  start returned and before a sync can leave a database that the next
  start refuses as not created; a Core user who needs a new database to
  survive a crash or a restart calls `Db.sync(SyncLevel.ORDINARY)` after
  `Db.start()`. No behaviour change.
* **The Javadoc: a value transformation whose result is null deletes the
  key** (bergdb 028-04), with a test; no behaviour change.
* **`GetMany.valuesBefore`, a new public field, for reclaim's scan**
  (bergdb 026-09, Q4): a scan with it set does not read the values stored
  at that stream position or later. Its Javadoc says what it gives; it is
  for BergDB's own use.


### Memory

* **The write buffer grows with use** (bergdb 026-07; 024-05, ST8;
  2026.5's Known issues). A database allocated a write buffer of 10 MB at
  its start, whatever its size. The buffer now starts at 64 KiB, doubles
  when an append does not fit, up to 10 MB, and goes back to 64 KiB after
  2 seconds with nothing to write: a small database in files holds
  0.67 MB of heap, not 11.1 MB. Write throughput unchanged.
* **An emptied database forgets what it no longer needs** (bergdb
  026-10). A cut forgets the cache of node ids below it and the conflict
  check's key hashes before it, so a database brought back to empty holds
  close to the heap of a new one: 1.08 and 1.47 times in the count gates
  G4 and G5, which check it every night (026-10, section 5).


### The stream's bytes (StreamDigest)

Against release 2026.5, the decided digests of every StreamDigest
configuration changed: the twelve of `java/stress/StreamDigest.java`,
l2-sd100, l2-sd1000-node8, l2-sd10000-node14, l2-sd100000-node62,
l2-every1, l2-idle-1, l2-idle-2, l2-default-100MB, l3-every1, l3-node8,
l3-node14 and l3-node62, in every mode. Every configuration changed by
the startup distance's key-value pair (bergdb 028-15) and by the writer
PE with record format 8 (bergdb 026-25; the digests before and after in
030-28, section 6); the l3-* ones also by reclaim's steps (bergdb 026-05
and 026-09) and its charge (bergdb 028-26). The release's gate compares
the release commit's digests with 2026.5's (bergdb 026-27, step 11).


Verification
------------

The release runs, on commits near the release commit (bergdb 028-23;
026-27, section 1), on F53 (Apple M1 Pro, 10 cores, 32 GB, macOS 27)
with JDK 27.0.1.1:

* `java/night.sh` on `8056d259`, 2026-11-23: NIGHT OK in 181 minutes,
  on `main` after every landing listed below. Its steps:
  `before-commit.sh` (1,738 unit tests and 89 f-tests), the Core's own
  build, Java's commit-time check (TransCheck) in the unit tests and the
  f-tests, the four level scripts with Lean's checkers of the trace,
  the tree, the writer's contract and the proved writer, the count
  gates, the Lean tests, the tree tests, 26 night tests, the index
  harnesses' soak, the fuzzers, 1,000 kills of a writing process with a
  restart after each that checks every transaction, the medium sets of
  conformance and of the contract, the user apps' traces, and the day's
  new seeds (211 conformance traces and 195 contract traces).
* `java/night.sh` on `2bb2b851`, 2026-11-20: NIGHT OK in 206 minutes.
* `java/week.sh` on `2bb2b851`, ended 2026-11-21: WEEK OK in 488
  minutes. The user apps with Java's commit-time check switched on (4.3
  million commits checked in the soak rounds, 31,682 in the kill
  rounds), 2,000 more kills on other seeds, longer fuzzing, the index
  harnesses' soak, the large conformance set, the user apps' traces, and
  the Android tests on an emulator (1,734 unit tests passed and 4
  skipped, 10 runs of the demos).
* `java/timing.sh` on `40cb9ae9`, 2026-11-21, against release 2026.5:
  Speed against 2026.5, below.
* A long run at 10 million keys with reclaim, retention, bounded storage
  and recovery (bergdb 028-43, `java/stress/large.sh`, week.sh's step 10
  since 2026-11-21): its full run passed, 100 million transactions and
  89 physical cuts.
* On the release commit, `bbcd802f`, 2026-11-23: its gate
  (`BEFORE COMMIT OK`, the proofs' `GATE OK`), the eight jcstress tests
  on F53, and the jar's unit tests, f-tests, night tests and user
  programs on Linux (s1, a virtual server) with JDK 27 and with JDK 17:
  all passed.
* **Platforms.** macOS (F53), Linux (s1) and Android (an emulator).
  Earlier releases have also run on Windows; 2026.6 has not been tested
  there.

The Java code that a user runs is the code those runs tested: after
`2bb2b851` it changed by one Javadoc (`TransCheck`, a tool of the
tests), and after `40cb9ae9` by nothing but the version in `BuildInfo`.
Landed after the runs of 2026-11-20, each through its gate (bergdb
026-27, section 1):

* Reclaim keeps the users' values, proved (bergdb 030-35), and the trace
  checker checks on every reclaim step that it writes back the value it
  read and nothing else (030-34); both from an independent review of the
  statements (030-33).
* The dirty-node bound proved for deletes without joins (bergdb 030-36)
  and through the joins of leaves and of the inner nodes just above them
  (030-37); the higher joins stay tested.
* Eight new Pub API apps with their own oracles, 31 runs with 160 forced
  stops of a child JVM: no database fault (bergdb 026-26); its one
  finding, in the build script, fixed (028-41).
* A timing scenario's setting (bergdb 028-42) and the long run at 10M
  keys (028-43), both in the test scripts.
* `Connection.transactionInfo()` kept as it is for 2026.6 (bergdb
  028-34; Frans, 2026-11-22).

Landed after the night of 2026-11-23, outside the Java code:

* The guarantee list (bergdb 030-38) and its independent review
  (030-39); 030-38 and 030-26 corrected after the review.
* The trace checker's C-STEP checks each reclaim step's row at the
  model's key since 2026-11-23 (bergdb 030-39, F1); until then it took
  the row's key from the trace's first step. Gated by
  `lean/contract/gate.sh` (GATE OK, 254 theorems), `level2.sh` (LEVEL 2
  OK) and `level3.sh` (LEVEL 3 OK).


Speed against 2026.5
--------------------

`java/timing.sh` on a quiet F53, on `40cb9ae9` against release 2026.5,
2026-11-21 (bergdb 028-19). CORE times a small database in memory; the
pause probe runs gets and commits with ZGC; `performance.sh ab` runs six
scenarios on both builds in turns, with G1 and an 8 GB heap, at 1M keys
with values of 100 bytes and at 10M keys with values of 8 bytes
(`w10m-*`), with reclaim at work (`*-fin`, a finite retain duration) or
without (`*-inf`).

* CORE: 6 % slower (0.265 against 0.250, smaller is faster).
* The longest get or commit with ZGC: 14.5 ms against 14.4 ms.
* Faster, the writes with reclaim at work: `w10m-fin` +27.4 % commits a
  second (68,936 against 54,104), `r-100-fin`'s mixed phase +27.2 %,
  `w-uni-100-fin` +10.2 %.
* Slower, the writes without reclaim: `w10m-inf` -6.3 %,
  `w-uni-100-inf` -9.7 % (171,837 against 190,254 commits a second).
* The reads: +3 % to -5 % (gets at the latest time, +1.0 %, and from 4
  threads, +2.8 %; at earlier times -4.3 %; scans forward and back -1 %
  to -4 %); `get_longkey` -5.4 %, the run's one alert, unconfirmed (its
  threshold 5 %).

**More than 10 % worse.** The two that the comparison prints:

* `r-100-fin`: the gets beside the commits in its mixed phase, 1,144,980
  against 1,305,590 a second (-12.3 %).
* `w-uni-100-inf`: the restart after the writes, 1.98 s against 1.75 s
  (+12.9 %).

The others among the figures that the same runs record (each build's
median):

* G1's pauses in the write scenarios: the longest 28 to 32 % longer (up
  to 344 ms against 268 ms in `w10m-fin`), and so the slowest commit 28
  to 34 %; the time in pauses 42 to 77 % more. The heap after a
  collection is larger (302 against 143 MB in `w-uni-100-inf`, 394
  against 195 MB in `w10m-inf`) and the resident size 18 to 60 % larger:
  the new writer allocates more (bergdb 028-19). With ZGC, the
  recommended collector, the longest pause is as before (above).
* The latency of reads at their high percentiles in `read-100`: gets,
  p99 and p99.9 10 to 12 % higher (at the latest time 2.26 against 2.05
  µs at p99); scans, p95 to p99.9 11 to 13 % higher, the slowest 11 to
  15 %. `r-100-fin`'s mixed gets: the mean 14.5 % higher, p95 26.5 %,
  p99 16.9 % (6.7 against 5.7 µs) and p99.9 11.0 %.
* After `r-100-fin`'s restart: the first get 122 µs against 83 µs, the
  next 999 14 to 29 % slower on average, and a get of every key at the
  end 0.52 s against 0.38 s (+35 %).
* `w-uni-100-inf`: a commit's append 11 % slower at p50 (4.8 against
  4.3 µs) and 13 % in the mean, and its slowest second 13 % fewer
  commits; the run's last sync 7.2 against 4.8 ms, `w10m-inf`'s 11.6
  against 6.0 ms and `w10m-fin`'s 13.8 against 12.0 ms (single syncs).
* `read-100`'s load of its keys before the reads: 10.6 % fewer puts a
  second (216,959 against 242,610).

Not blocking (bergdb 006-32: only a large loss at 1M or 10M keys
blocks; Frans, 2026-11-23, 026-27's D2). An optimisation round of the
new writer's Java code is bergdb 028-19, open for a later release.


Known issues and limits
-----------------------

**No bug is known at the release.** 028's open entries, none of them a
fault:

* **028-01**: sequential keys fall in few bins of the set that a
  commit's conflict check reads, so a commit that read many sequential
  keys scans more than it needs; a cost, to measure.
* **028-19**: the new writer's speed and reclaim's pace with it (Speed
  against 2026.5, above).
* **028-34**: `Connection.transactionInfo()` (Pub API) is kept as it is
  for 2026.6 (Frans, 2026-11-22); whether it stays, or a walk of a key's
  versions moves into the Core, is for a later release.

**Databases of release 2026.5 and earlier are refused** (The stream,
above): make them again, or read them with the release that wrote them
and put the data into a new database. The C clone (bergdb 012, 022)
writes an older format, which 2026.6 refuses.

**What the proofs do not cover** (bergdb 030-26, sections 2.6 and 4;
030-38). The guarantees hold under conditions, each a premise of a
theorem or a fact tested instead of proved:

* **Java is tested against the model, not proved.** The tests compare
  Java with the model transaction by transaction, on generated traces
  and on the user apps' workloads, every night; a case that no trace
  reaches is covered by the other tests only.
* **A history of fewer than 2^48 - 1 transactions.** A premise of the
  proofs of crashes, restarts, eviction and reclaim, which Java does not
  check: it bounds the top nodes' ordinals instead (bergdb 005-02). At a
  million transactions a second, 2^48 transactions take about 9 years.
  Also premises: the keys within a transaction are distinct (Java's
  writer gets one operation a key), and the top nodes' base level is at
  most 2^62 (1,040,512 at the model's parameters).
* **The writer accepts every transaction that BergDB admits**, proved at
  the model's parameters G = 8,192 and H = 126, which Java does not
  have, and given the writer's fill rules (`FillOk`, five rules: an
  inner root of a segment tree has two live entries, every other key
  node at least m, an inner node's smallest live entry is the empty
  key's, at most theta dead entries a key node, and the tree balanced by
  height). The tree checker tests them on Java's tree after every traced
  transaction. That the writer keeps the first two is proved, by a
  theorem outside the gate's list; that it keeps the other three is not
  (bergdb 030-38, G8).
* **A transaction's index nodes stay within the count that Java checks
  before its go point**: proved for puts and for deletes that join
  leaves and the inner nodes just above them; for deletes that join
  inner nodes at height two and above, tested (bergdb 030-36, 030-37).
  Java's admission check counts otherwise than the theorems in three
  cases: where its cheap estimate fits, it does not call the count; a
  key with a key transformation is counted by that estimate only; and a
  key with a value transformation is counted as a put and as a delete.
  That these counts are enough is argued (bergdb 028-21; 023-11), not
  proved and not tested on purpose (030-38, G9).
* **Values are tokens in the model and 63-bit hashes on the traces.**
  That a value read back has the bytes that were put is tested.
* **The platform**, tested (crash, power-loss and kill tests), not
  proved. With hard sync, the storage's default (`FileStream(dir)`:
  every append is forced to the device before it returns), a synced
  transaction survives a crash of the process, a crash of the operating
  system or a power loss, and a crash leaves at most a torn tail, which a
  start leaves out. With per-append forcing off (`FileStream(dir,
  false)`), a synced transaction survives a crash of the process only: a
  crash of the operating system or a power loss can lose it, and can
  leave a hole in the tail that recovery does not handle (bergdb 014-01),
  so that the database may refuse to start or fail reads (030-38, G12).
  The power-loss test models the storage's persistence boundaries; it is
  not a physical power cycle. That bytes read back are the bytes written
  is tested too; damaged bytes are detected on a best-effort basis only.
* **Threads are not modelled.** One transaction writes at a time;
  readers, eviction and the storage's threads beside it are tested. A
  read that returns gives the answer at its own time. A read beside
  reclaim can instead throw `LookupTimeNotAvailableException` when a cut
  overtakes it, also a read of the latest state or of a time that was
  still available when it began (bergdb 030-38, G14).
* **The Pub layer is not modelled**: objects, user indexes and index
  jobs are built on the Core and tested.
* **Reclaim's arithmetic and Java's steps are tested** at every cut and
  every step of the reclaim traces; C-STEP checks each step's row at the
  model's key since 2026-11-23 (bergdb 030-39, F1).
* **Reclaim's cuts in a running process.** The theorem on reads after
  reclaim's cuts takes a run that starts again from the cut stream at
  every cut, with its memory made anew. Java cuts while it runs and
  keeps its memory: that case is proved for the abstract model of the
  stream (`SIS.T9_handles`), not tied to the proved writer, and tested
  for Java (ReclaimStress, ReclaimReaders, the reclaim traces; bergdb
  030-38, G6).
* **No theorem says that reclaim makes progress or bounds the stream's
  size**: the theorems take reclaim's iterations that end as a premise.
  That the stream stays within a bound is tested: `java/stress/large.sh`
  checks a fixed bound on the kept bytes over a long history at 10
  million keys (in `java/week.sh`; bergdb 028-43).
* **No cost, time or memory statement is proved**, but the bound on a
  transaction's index nodes above: not a start's work, the stream's size,
  the heap or pauses. They are measured and tested (the count gates every
  night, `timing.sh`).

**From 2026.5's Known issues and limits**
([2026.5](../2026.5/readme.md)), as they are in 2026.6:

* **Fixed**: a value transformation that throws or passes 8 MiB (RB-001,
  above); the 10 MB write buffer of every database (Memory, above); the
  lag after a mass delete (The stream, above, bergdb 026-05).
* **Changed: the model.** 2026.5 shipped with the model's proofs in
  part and the rest checked by conformance; 2026.6's claim is 030-26's
  (The theme, above).
* **Still so**: an emptied database keeps the cache's tables at a floor
  of about 256 kB; a single put's record of about 0.25 MB now and then; a
  put's stream bytes grow with the keys at a fixed startup distance (the
  default stays 50 MB, which suits up to about 10M keys; beyond that 200
  to 1,000 MB); the stream kept under reclaim, about 4.5 to 6 times the
  live data beyond the history (the count gate G3 measured 4.73 at 1M
  keys under uniform overwrites on 2026-11-23, and fails above 6), with
  reclaim's fraction 1/4 and no setting of the Pub API (bergdb 026-04,
  open). The rest of 2026.5's list stands as it was.


After the release
-----------------

Added after 2026-11-24; the notes above are as published on that day.

* 2026-11-24. **RB-004, S4**, fixed in this release, registered after it
  (a date in `created.txt`; [bergdb 033](../../items/033-bugs/readme.md)).
* 2026-11-24. Corrected: Verification, `java/week.sh`, reads "2,000 more
  kills on other seeds"; it should read "3,000 more kills on other seeds".
* 2026-11-24. Corrected: Changes, In short, the speed against 2026.5,
  reads "reads up to 5 % slower"; it should read "reads up to 5.4 %
  slower".
* 2026-11-24. Corrected: Changes, The stream, the writer PE, reads "a
  small database in memory 11 to 18 % slower in CORE's set"; it should
  read "a small database in memory 11 to 18 % slower in CORE's set test,
  timed when the writer landed (CORE as a whole 6 % slower in the
  release's timing, Speed against 2026.5, below)".
* 2026-11-24. **RB-005, S4**, found after the release, in 2026.6 and
  2026.5; fixed on main for 2026.7 (bergdb 028-50;
  [bergdb 033](../../items/033-bugs/readme.md)).
* 2026-11-24. **RB-006, S4**, found after the release, in 2026.6 and
  2026.5: `maintain()` could stop beginning reclaim iterations after
  some cuts; fixed on main for 2026.7 (bergdb 028-51;
  [bergdb 033](../../items/033-bugs/readme.md)).
* 2026-11-24. **RB-007, S4**, found after the release, in 2026.6 and
  2026.5: `maintain()` keeps the stream written while a reclaim
  iteration waited for its cut, after some cuts; not yet fixed (bergdb
  028-53; [bergdb 033](../../items/033-bugs/readme.md)).
* 2026-11-25. **RB-008, S3**, found after the release, in 2026.6 and
  2026.5: the Core API's `Db.getTrans` could refuse the position of a
  transaction of over 1 MiB just after a reclaim cut; fixed on main for
  2026.7 (bergdb 028-55; [bergdb 033](../../items/033-bugs/readme.md)).
* 2026-11-25. **RB-009, S3**, found after the release, in 2026.6 and
  2026.5: the Core API's `Db.getTrans` could expire a kept transaction
  of over 1 MiB while reclaim cut the stream; fixed on main for 2026.7
  (bergdb 028-56; [bergdb 033](../../items/033-bugs/readme.md)).
* 2026-11-25. **RB-010, S4**, found after the release, in 2026.6 and
  2026.5: a stop or a crash during `maintain()` can leave its filler,
  up to 200 kB, live; not yet fixed (bergdb 028-59;
  [bergdb 033](../../items/033-bugs/readme.md)).
* 2026-11-25. **RB-011, S4**, found after the release, in 2026.6 and
  2026.5: an emptied file database keeps its last stream file under
  `maintain()`, up to a quarter of the stream kept when that file was
  made; not yet fixed (bergdb 028-61, 028-62;
  [bergdb 033](../../items/033-bugs/readme.md)).
* 2026-11-25. **RB-012, S2**, found after the release, in 2026.6 and
  2026.5: after a kill on macOS, a zeroed tail of the last stream file
  over a meta block stops the start ("Invalid magic bytes"); fixed in
  part on main for 2026.7 (bergdb 028-60;
  [bergdb 033](../../items/033-bugs/readme.md)).
* 2026-11-27. **RB-013, S4**, found after the release, in 2026.6 and
  2026.5: a stop between a transaction's record and reclaim's records
  after it changes the stream's bytes after a restart; fixed on main for
  2026.7 (bergdb 031-06; [bergdb 033](../../items/033-bugs/readme.md)).
