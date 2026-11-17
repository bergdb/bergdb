005-11. The study: replication
==============================

Written 2026-10-22 by Claude (Opus 5.5, Claude Code), at Frans's request
("Do 005-11. Replication: study it, for Frans to decide."). Made on commit
`691794d`, the code as committed; nothing in `java/` or `lean/` was
changed. The options and the proposal are in
[../11-replication.md](../11-replication.md); this file is the study
behind them: what the code does, what the tests cover, what the probes
showed, what the theory says, and what each option takes.

The probes are in [tools/ReplicaProbe.java](tools/ReplicaProbe.java)
(`tools/run.sh PROBE`, `tools/all.sh` for all but P8), their outputs in
[runs/](runs/). F53, macOS 27, OpenJDK 27.


What the code does
==================

The parts
---------

* `storage/StorageManager` holds one main storage and zero or more
  replicas, each an `AppendOnlyStream` behind its own `BufferedStream`.
  It is the `AppendOnlyStream` that the core writes to and reads from.
* `Db.addReplica`, `removeReplica`, `getStorageInfos`; `DbHelper`'s
  `checkReplicaId` and `AddReplicaClass` (the job of an `addReplica`).
* `DbBuilder.stream(name, stream)`: the first stream is the main, every
  other one a replica (by default 20 MB and 2000 ms, the
  `DEFAULT_REPLICA_*` constants); `mainStream` replaces the first.
* The Pub API: `DatabaseBuilder.replica(name, dir)`,
  `Database.addReplica(name, dir)`, `removeReplica`, `getStorageInfos`,
  `sync(SyncLevel.STRONG)`;
  `BadReplicaException` and `StorageInfo` in `pub.util`. A replica of the
  Pub API is a `FileStream` in a directory.

Replication is local: a replica is another stream in the same process,
such as a directory on another disk. Nothing goes over a network.


Writes, reads and the two durability rules
------------------------------------------

* `append` (StorageManager.java:753) appends to the main, then to every
  replica whose status is ACTIVE. The bytes only go into each stream's
  buffer; each `BufferedStream` writes and forces them in its own thread,
  every buffer time (main: 20 ms; a replica: 20 ms by `replica()`, 2000 ms
  by `addReplica()` and `DbBuilder.stream`) or when a quarter of its
  buffer is full.
* `read` (:677) reads the main only. A comment names failover to a
  replica as possible; there is none.
* Two durability rules give the lengths that the syncs wait for
  (`computeRules`, :400, run after every flush of any stream):
  * D1, `MainConfirmedRule`: the main's confirmed (forced) length.
    `sync(pos)`, the ORDINARY level, waits for it. Reclaim's cuts wait
    for it too (`Db.getDurableLength`).
  * D2, `OneActiveReplicaRule`: the smaller of the main's confirmed length
    and the largest confirmed length among the ACTIVE replicas; the
    main's if no replica is ACTIVE. `syncStrong(pos)`, the STRONG level,
    waits for it. So STRONG means "the main and one replica", whichever
    is fastest, and it means ORDINARY when no replica is ACTIVE, also when
    the only one has failed. `setD2` can change the rule (one test does).
* These D1 and D2 are StorageManager's; docs/levels.md uses the same
  names for two decisions of Level 3, which are other things.


Errors and statuses
-------------------

* A storage is INITIALIZING while `addReplica` copies into it, ACTIVE, or
  ERROR (`StorageInfo`; `getStorageInfos` shows them, with a status
  string).
* The error rule, `MainErrorRule`: the storage as a whole has failed only
  if the main has. Then every later append and read throws, and so does a
  sync that has to wait.
* A replica's I/O error (`handleStreamException`, :713): the replica's
  stream is closed, its slot in the array of streams becomes null, its
  storage an `ErrorStorage`, and the rules are computed again. Nothing
  else happens: no exception, no log line; the main goes on.


Startup
-------

`Db.startInner` calls `syncStreams` (Db.java:986) before recovery:

1. `checkStreamIds` (StorageManager.java:194): if the main is not empty,
   every replica that is not empty must have the main's database ID in its
   last valid meta block, or `BadReplicaException`.
2. `syncMainStream` (:249): the longest replica that holds the bytes the
   main lacks (its first position at most the main's length) is copied
   onto the main, from the main's length on. "The longest stream wins."
3. `syncReplicaStreams` (:299): a replica shorter than the main's first
   position is emptied and moved to it (`seekFirstPos`: a `FileStream`
   deletes its files); a replica longer than the main is refused
   (`BadReplicaException`); the others get the main's tail.
4. Then recovery (`RecoverableStream.recover`) through StorageManager, so
   the bytes it appends (the zero fill of a torn last transaction) go to
   every stream.

Only the database ID is checked. That the streams hold the same bytes
where they overlap is assumed.


Adding a replica while the database runs
----------------------------------------

`Db.addReplica(name, stream, bufferSize, bufferTime)` (Db.java:410):

1. `checkReplicaId`: a replica that is not empty must have the database's
   ID.
2. `StorageManager.addReplica` (:504): the name must be new and the
   replica no longer than the main; a replica shorter than the main's first
   position is emptied and moved to it. The replica gets a `BufferedStream`
   and is added as a `SynchingStorage` (INITIALIZING). Its slot in the
   array of streams stays null (:562 to :576).
3. A thread copies the main into it, 50 kB at a time, reading the main
   without the write lock; the last part, under 50 kB, is copied under the
   write lock, and the storage made ACTIVE (`makeActive`, which also fills
   the slot).
4. The thread then executes a dummy transaction (`DUMMY_KEY`) and a STRONG
   sync of it, and the job reports 100 and "Done!". The job's progress
   note on the way says "waiting for syncString" (sic).

A `DbHelper` comment of 2017 says it: "TODO LATER Make sure this class is
tested." `Database.addReplica` (DatabaseImp.java:164) opens a `FileStream`
in the directory and calls it with 20 MB and 2000 ms.


Removing a replica, cuts, stop
------------------------------

* `removeReplica(name)` (:602) takes the replica out of the arrays and
  stops its `BufferedStream`: what it has buffered is not written. Its
  files stay.
* `pretruncate` (:796), reclaim's cut, goes to every stream in the array of
  streams (the main first). A `BufferedStream` keeps a cut past the bytes
  it has flushed and makes it after the flush that reaches it
  (BufferedStream.java:481). Reclaim makes the cut when D1, the main's
  durable length, has passed the stream length at the cut's decision
  (`Reclaim.cutIfDurable`, Reclaim.java:360). The replicas' durable
  lengths are not looked at.
* `close()` flushes every stream; `stop()` does not, for the main or a
  replica. The Pub API has `stop()` only.


The Pub API's details
---------------------

* `replica(name, dir)` adds a stream to the builder, `dir(main)` sets the
  first one. Called in the other order, `replica()` makes the replica the
  first stream and `dir()` then replaces it (DbBuilder.java:264).
* An encryption key wraps the main stream in a `SalsaStream`
  (DatabaseBuilderImp.java:173); a replica of `replica()` or `addReplica()`
  is a plain `FileStream`.
* `replica()` gives a replica a buffer time of 20 ms, `addReplica()` 2000
  ms.
* Nothing checks that a replica's directory is not the main's or another
  replica's.


What is 2017 code
-----------------

By `git blame` on `691794d`: 1,214 of StorageManager's 1,243 lines are
from the 2017 import. The 2026 lines: the durable length for reclaim
(`getDurableLength`), a read below the first position that does not fail
the storage (W1), a fix of `handleStreamException` (it looped forever when
the stream was not found), the listener's `appendFailed`, and the main's
buffer time (005-13). 005-10 removed `setD1` and `setErrorRule`, which
nothing called. The rules, `DbHelper`'s replica code, `Db.addReplica` and
the Pub API's methods are 2017 code that no 2026 work touched.
`BufferedStream`'s 2026 fixes (the pending cut, failures, the idle consumer
of 005-14) apply to replicas as to the main.


What the tests cover
====================

15 tests use replicas, all unit tests, 2017 code; they pass on `691794d`
([runs/existing-tests.txt](runs/existing-tests.txt), with
`StorageManagerTester`'s three other tests):

* `StorageManagerTester`, 13 of its 16 tests: the startup
  sync with two and three `MemoryStream`s and with `FileStream`s
  (`testSync1` to `4`, `testMultipleClose`), `addReplica` with an empty
  replica, one with old data and one with old and current data, after a
  cut of the main, and while appending (`testAddReplica1` to `5`,
  `testAddReplicaWhileAppending`), `removeReplica` (`testRemoveReplica1`,
  `2`). They check lengths and first positions, not the bytes. A note in
  `testAddReplica2` records a failure on 2015-07-23 that was not
  reproduced.
* `DbTester.testBadReplica1`: `Db.addReplica` of another database's stream
  throws `BadReplicaException`.
* `PubTester.testBadStartReplica`: a startup with two databases' streams
  throws `BadReplicaException`.

Not tested: a database with a replica in use (writes, syncs, restarts),
the Pub API's `replica()`, `addReplica()`, `removeReplica()` and
`getStorageInfos()`, the STRONG level with a replica, and every
combination that the entry lists: cuts, a replica added after a cut, a
restart from a replica, a crash in the copy, a replica that fails,
eviction, a slow replica; nor encryption. No stress, level or night test
uses a replica; the STRONG syncs of the tests (most of about 100 uses) run
without one, so they are ORDINARY syncs. docs/levels.md and
docs/level3-durability.md say that replication with cuts is not
established.


The probes
==========

Each probe runs today's code; none changes it. Unless said otherwise, a
database of the reclaim tests' setup (test clock, startup distance 2,000
bytes, nodes of 8, retain 1 s, transactions 50 ms apart, each of 1 to 3
puts and deletes, now and then up to 40, on 300 keys) on `CutStream`s (in
memory; a read below the cut throws, as on disk), or on `FileStream`s in a
temporary directory. A check of a database compares every key at the
latest time and at its first available lookup time, and 300 random
lookups at times from it on, with a model of the transactions.

| | What | Result |
|---|---|---|
| P1 | A replica's bytes; a start from the replica | Works: byte copies. With two replicas, one may hold nothing |
| P2 | Reclaim's cuts: what a crash at each cut leaves on each stream | Fails: replica images shorter than the cut's decision are broken |
| P3 | A replica added after cuts, also during writes | Works; a cut during the copy throws NullPointerException in a user transaction |
| P4 | An empty main and the replica at startup | Works without cuts; refused after cuts |
| P5 | A crash in the middle of `addReplica`'s copy | Works |
| P6 | A replica whose writes fail | The main goes on; then NullPointerException from about half of all transactions, with reclaim |
| P7 | A replica with eviction | Works |
| P8 | Sync times; a slow and a hung replica | STRONG takes 2 s with `addReplica()`; a slow replica stalls the writes, a hung one blocks them |
| P9 | A start without the replica after a crash, then with it | Fails: the main hangs at startup, or the replica holds another history |
| P10 | The Pub API: order, encryption, the main's own directory | Fails: a replica dropped silently; an encrypted database's replica in plain text |
| P11 | (not replication) A crash image that ends at a meta block's position | Fails: the database does not start |


P1. Byte copies
---------------

[runs/p1-identity.txt](runs/p1-identity.txt). 3,000 transactions with a
replica of 10 ms and one of 2000 ms, then `close()`: the replica's 6.3 MB
are the main's, byte for byte, and started alone it is the database (900
lookups right). The Pub API, `dir()` with `replica()`: the same. A second
replica added with `addReplica()` after 2,000 puts: its job ended with
"Done!", it was ACTIVE, a STRONG sync after 2,000 more puts returned in 46
ms, and after `stop()` its directory held 0 bytes. The STRONG syncs, the
job's own too, were met by the other replica, and `stop()` dropped the
added one's 2-second buffer. Started alone, it is an empty database.


P2. Cuts
--------

[runs/p2-*.txt](runs/), `tools/p2-all.sh`. The main and the replica keep a
copy of themselves at each cut (`SnapCutStream`): what a crash at that
moment leaves, since a stream holds what its `BufferedStream` has written,
as a `FileStream` holds what it has forced. Each image is started and
checked against the transactions complete in it, and its length compared
with the stream length at the cut's decision (`Reclaim.Stats`).

| Run | Replica | Setup | Replica images | Shorter than the decision | Of these: not started / lookups failed (at the latest time) | Main images, all right |
|---|---|---|---:|---:|---:|---:|
| a | 10 ms | reclaim tests' | 792 | 414 | 3 / 411 (159) | 792 |
| b | 2000 ms | reclaim tests' | 44 | 26 | 12 / 14 (9) | 786 |
| c | 10 ms, its disk stalls for 500 to 3000 transactions | reclaim tests' | 734 | 367 | 7 / 360 (127) | 790 |
| d | 10 ms | startup distance 200 kB, retain 10 s, values to 200 bytes | 80 | 58 | 0 / 58 (0) | 80 |
| e | 2000 ms | startup distance 1 MB, retain 60 s, 100 ms apart, values to 1 kB | 45 | 30 | 10 / 20 (0) | 61 |
| f | 20 ms (`replica()`) | as e | 61 | 48 | 0 / 48 (0) | 61 |
| | | | 1,756 | 943 | 32 / 911 (295) | 2,570 |

Three seeds each (two for e and f), 12,000 transactions per seed (30,000
for e and f).

* Every replica image shorter than its cut's decision is broken: it does
  not start ("Could not find *any* valid meta block", or a read below the
  cut), or a lookup at a time it says it has fails with a read below the
  cut. With the reclaim tests' small distances, about a third of them
  fail at the latest time. With the larger distances (d, e, f), the latest
  state was right in all that started, and history from the first
  available lookup time on was not: the image lacks the table that marks
  the cut, so it gives the previous first available lookup time. A third of
  e's did not start.
* The other 813 replica images were right but one, which ended exactly at a
  meta block's position (P11). The main's 2,570 images were all right.
* The cause: a replica is cut when the main is durable past the decision,
  and the replica lags behind the main by up to its buffer time. With 2000
  ms, it flushes in large parts and is cut less often (44 images against
  792), but each time it is likely to be short. The window lasts until the
  replica's next flush: about its buffer time after each cut.
* It matters when the main is lost in the same crash, which is what a
  replica is for: started with the main, the replica gets the main's tail
  and is complete again.
* At the end of each run, after `close()`, the main and the replica were
  the same bytes over the range both had.


P3. A replica added after cuts
------------------------------

[runs/p3-addafter.txt](runs/p3-addafter.txt). A main on a `FileStream`
with reclaim, written until its first position is 2 MB; then
`Db.addReplica` of an empty `FileStream` (20 MB, 2000 ms), with nothing
else writing, with a writer of about 1,000 transactions a second, with
that writer and cuts during the copy, and with a writer at full speed and
cuts. In all four the
job ended with "Done!" after 2.0 to 2.5 s (the replica's buffer time), the
replica was ACTIVE, the bytes the same after 2,000 more transactions, and
the replica started alone as the database.

* A cut during the copy throws `NullPointerException` in the transaction
  that makes it (StorageManager.java:806): the copying replica's slot in
  the array of streams is null until it is ACTIVE. The transaction has
  committed; reclaim keeps the cut pending, so the next transactions throw
  too, until the copy ends: 1 in this run, 24 in an earlier one.
* The replica's first position can be below the main's (18,000,000 against
  18,800,000): `FileStream` cuts whole files, and the replica's files begin
  at other positions. It holds more history; harmless.
* A first version of the probe held the write lock from one transaction to
  the next: the copy, which takes the lock for every 50 kB, never ended,
  and the heap ran out (no eviction in that setup). Not a fault of
  replication; a writer that releases the lock lets it through.


P4. Restore an empty main from a replica
----------------------------------------

[runs/p4-restore.txt](runs/p4-restore.txt). A main and a replica, 3,000
transactions; then a startup with a new, empty main directory and the
replica. Without reclaim, the replica is copied onto the main and the
database is right, also when the restored main is started alone. With
reclaim (the replica's first position at 10 MB), startup refuses:
`BadReplicaException: Replica 'r is illegal. It's length is 10648328 while
main stream length is 0.` (sic): `syncMainStream` copies only from a
replica whose first position is within the main, and the empty main is not
moved to the replica's first position. The replica's directory can itself
be started as the main (P1, P3, P5, P7).


P5. A crash in the middle of the copy
-------------------------------------

[runs/p5-crashsync.txt](runs/p5-crashsync.txt). A child process writes 70
MB (20,000 transactions), calls `addReplica` and halts
(`Runtime.halt(0)`) at 52 percent of the copy. The replica then holds the
first 20 MB, byte for byte the main's (two flushes of half its buffer).
Started alone, it is the database after the 6,293 transactions complete
in it. Started with the main, the startup sync copies the rest, and the
two are the same 70 MB. Works.


P6. A replica whose writes fail
-------------------------------

[runs/p6-fail.txt](runs/p6-fail.txt). The replica's stream throws an
`IOException` once it has 100 to 300 kB.

* The main goes on, as `MainErrorRule` says; the replica is ERROR in
  `getStorageInfos`, with the exception's text. Nothing else tells.
* A STRONG sync after the failure returns at once (10 to 12 ms): it is an
  ORDINARY sync now, silently.
* With reclaim, the next cut throws `NullPointerException`
  (StorageManager.java:806: the failed replica's slot is null), after the
  main was cut and the transaction had committed. Reclaim keeps the cut
  pending, so it happens again: of the 5,818 transactions after the
  failure, 2,810 threw, each one committed.
* `removeReplica("r")` of the failed replica throws `NullPointerException`
  too (:646), after it has removed it; then all is well. The database's
  content is right throughout, and after a restart.
* `addReplica` of a stream that fails: the job ends with progress 100 and
  "Done!"; only `getStorageInfos` shows the error.


P7. Eviction
------------

[runs/p7-evict.txt](runs/p7-evict.txt). A cache budget of 2 MB, 5,000
keys with values up to 3 kB, retain 30 s, 20,000 transactions; eviction
released 450,000 objects. Reads, which come from the main, were right; the
replica was the main's bytes over its 30 MB; started alone, with eviction,
it was the database. Works.


P8. Sync times, slow and hung replicas
--------------------------------------

[runs/p8-slow.txt](runs/p8-slow.txt). `FileStream`s on F53's SSD; run
alone, the session idle.

| | sync ORDINARY after each commit, p50 / max | sync STRONG, p50 / max |
|---|---:|---:|
| no replica | 29.0 / 33.4 ms | 29.5 / 35.0 ms |
| a replica of 20 ms (`replica()`) | 29.5 / 43.0 ms | 29.9 / 36.2 ms |
| a replica of 2000 ms (`addReplica()`) | 29.6 / 34.7 ms | 2,022 / 2,030 ms |

* A replica limited to 2 MB/s, puts of 1 kB without syncs: 18,219 in the
  first second, while its 20 MB buffer filled, then none for the next four
  (no replica: 52,000 to 86,000 a second). The writes then go at the
  replica's speed, in bursts of 10 MB.
* A hung replica (its writes block; a 1 MB buffer): 922 puts, then the
  writer waits for good. Reads go on, and a sync of an earlier position
  returns; `Database.sync()`, which syncs the last transaction, waits for
  the write lock that the writer holds, and did not return. `stop()`
  returned at once, the writer stayed blocked until the replica was let
  go.


P9. A restart without the replica
---------------------------------

[runs/p9-diverge.txt](runs/p9-diverge.txt). A main and a replica on
`FileStream`s, the same buffer times, 3,000 transactions, `close()`. Then
a crash in which the replica's disk kept more than the main's: the main's
last 3,000 bytes are cut, as if its storage thread had not written them
when the replica's had (the last two transactions are incomplete in it).
The database is
started on the main alone, which fills the torn transaction with zeros,
and runs 0, 3 or 400 transactions; then it is started with the main and
the replica again. Both have the same database ID, so startup accepts
them, and the bytes differ from position 7,282,616 on.

* 0 transactions: the replica is longer, and its tail (the old last
  transaction) is copied onto the main. The database does not start:
  startup loops for ever in `NodeStream.TransIterator.next`, at 100
  percent of a core; the main alone does the same from then on. The main is
  damaged; the replica, not changed, is the database before the crash.
* 3 transactions: the main is longer; its tail is appended to the
  replica. The main is right. The replica, the same length as the main, is
  the history before the crash: started alone, 9 keys have other values
  than the main's, and the 3 new transactions are not in it. No error.
* 400 transactions: the same, but the replica's latest state happened to
  be the main's; its bytes differ.

The same happens with `addReplica` after each start (as `PayDemo` does):
`StorageManager.addReplica` refuses a replica longer than the main, but
accepts it once the main has grown past it, and appends the main's tail.


P10. The Pub API
----------------

[runs/p10-pubapi.txt](runs/p10-pubapi.txt).

* `replica("r", dir).dir(main)`: the database has the main only; the
  replica is dropped without a word.
* An encrypted database (`cryptoKey`): with a replica of `replica()` or of
  `addReplica()`, the text of a value is in a replica file in plain text,
  and in no file of the main. The replica starts without the key and shows
  the values; with the key it does not start (`BadCryptoKey`).
* `addReplica("self", main's directory)`: accepted ("Done!"); two streams
  then write the same files. After 29,000 more puts and a restart the
  database was right in this run; nothing prevents it.


P11. A crash image at a meta block's position (not replication)
---------------------------------------------------------------

[runs/p11-metaedge.txt](runs/p11-metaedge.txt),
[runs/p11-metaedge-small.txt](runs/p11-metaedge-small.txt). Found by P2,
run a: a replica image of exactly 14,400,000 bytes, longer than its cut's
decision, did not start: `IllegalArgumentException: spos >= streamSize,
14400128, 14400000`. The probe: transactions on a stream without reclaim;
each transaction that ends exactly at a meta block's position (a multiple
of 200,000) is cut there, and the image started.

* 13 such transactions in two runs (30,000 transactions, and 150,000 with
  small values): all 13 images fail to start. Cut 8 bytes before, or after
  the meta block, all 26 start.
* The cause: `RecoverableStream.append` writes the bytes up to a meta
  block's position and the meta block in two appends
  (RecoverableStream.java:408 to 411). A `BufferedStream` flush, and so a crash, can come between
  them; P2's image was made so, by a real flush. Recovery then finds the
  stream ending at the position: `fixMetaBlockIfNeeded` (:297) fills out a
  meta block that is partly written (1 to 127 of its bytes), not one that
  has not begun; `fixLastTransactionIfNeeded` (:150) steps past the meta
  block, beyond the end, and `getRemainingTransBytes` (:285) throws.
* It concerns the main stream as much as a replica: a crash in that
  window leaves a database that does not start. The window is short, and
  few meta block positions have a transaction that ends there (1 of 337
  and 12 of 1,635 here). `CrashTest` cuts at random positions and at
  transaction ends, and is unlikely ever to meet one.
* A fix, likely small: fill out the meta block also when none of it is
  written (a stream whose length is a positive multiple of the distance).
  For an entry of its own.


What the theory says
====================

Is a replica a byte copy of the main stream at every durable point?

* By construction, every ACTIVE replica gets the main's bytes in the main's
  order, and the copies of `addReplica` and of startup copy the main's
  bytes. So a replica holds a prefix of the main's bytes from its first
  position on (P1, P3, P5, P7). Its first position may be lower than the
  main's (P3).
* "At every durable point" holds for STRONG only, and for one replica: D2
  says that one replica holds the bytes up to the sync. Any replica may lag
  behind the main by up to its buffer time (P1, P8), so a crash leaves a
  shorter prefix on it.
* A shorter prefix is fine. A replica is then a crash image of the main,
  and T1 (recovery) says that a prefix of complete records starts as the
  database after its last complete transaction; Java's recovery fills a
  torn last record with zeros, so every byte prefix is such a stream (the
  fault model of docs/level3-durability.md; byte recovery is not modeled).
  P1, P5 and P7 show it.
* Cuts break it. The main is safe after a cut because the cut waits until
  the main is durable past the decision (docs/levels.md, W5c; checked by
  `Reclaim.Tester.testCutIsMadeAfterDecisionIsDurable`). In the model,
  T8 (recovery from a cut stream) needs `CutOK` at the cut for the state
  that the stream holds. Reclaim decides a cut from the state at the
  decision, and the main's wait makes sure that a crash leaves at least
  that state. A replica cut while it holds fewer records than at the
  decision is outside T8, and P2 shows that it fails, every time.
* If each stream were cut only when it is durable past the decision, every
  replica would be a crash image of the main after safe cuts, which is
  what T1, T8 and T12 already cover. The Lean model would need nothing
  new for that.
* What the model does not cover: several streams, the startup sync
  ("the longest wins"), and streams of different histories. It has one
  stream of one run. A statement that every stream of a set is a prefix of
  one run's stream, with its own safe cut, and that the startup sync keeps
  it, could be added; but the Java side needs only a check that two streams
  agree where they overlap (P9), simpler to test than to prove.

On "byte-identical replicas by T2" in docs/prior-art.md: a byte copy is
byte-identical by construction; it needs no theorem. T2 (restart
invariance) adds that a restart from a stream that ends at a record
boundary, the main or a copy, appends exactly the records the run without
the restart would have. So streams that hold whole records stay prefixes of
one stream across restarts. A torn record breaks this: recovery fills it
with zeros, which is not a record of the model, and a stream that has that
record whole differs from that byte on. That is P9. So the sentence holds
for streams that end at a record boundary; a replica after a crash that
tore a record in one of the two does not have it.


What each option takes
======================

Remove
------

What goes, about 1,700 lines, nearly all 2017 code and its tests:

* The Pub API: `Database.addReplica`, `removeReplica`, `getStorageInfos`,
  `DatabaseBuilder.replica`, and their implementations; `BadReplicaException`
  and `StorageInfo` in `pub.util`; `PubTester.testBadStartReplica`.
* The core: `Db.addReplica`, `removeReplica`, `getStorageInfos`, the ID
  check at startup; `DbHelper.checkReplicaId` and `AddReplicaClass` (145
  lines); `DbTester.testBadReplica1`. `DbBuilder.stream` keeps one stream,
  the main (the tests set its buffer with it).
* The storage: StorageManager's replicas (`SynchingStorage`,
  `ErrorStorage`, `checkStreamIds`, `syncMainStream`, `syncReplicaStreams`,
  `addReplica`, `removeReplica`, `getStorageInfo(s)`, `setD2`, the D2
  wait), about 650 of its 1,243 lines; the rules (`DurabilityRule`,
  `MainConfirmedRule`, `OneActiveReplicaRule`, `ErrorRule`,
  `MainErrorRule`, 139 lines), D1 then being the main's confirmed length;
  13 of `StorageManagerTester`'s 16 tests (about 520 lines).
* Kept: `SyncLevel.STRONG`, as the same as ORDINARY, said in its Javadoc
  (about 100 uses, most in tests, and the Pub API's `sync(SyncLevel)`); it
  can go with 005-05's look at the API. `AppendOnlyStream.seekFirstPos`
  ("added to support replication") can stay: `FileStream`'s tests use it
  to make large positions.
* `PayDemo` (`src-dev/frans/`) calls `addReplica`; Frans's demo, his call.
* Documents: docs/levels.md's STRONG ("also a replica, if there is one")
  and the limits that name replication (levels.md,
  level3-durability.md); prior-art.md's sentence, corrected as above.

Size S: about a day, with the four gates; Lean unchanged. StorageManager
is on the path of every write, so the gates matter. Lost: mirroring within
the process to another directory, and the restore of P4 (which works
without cuts only).


Complete it
-----------

The fixes that the probes call for, each with its tests:

| # | Fix | Probe | Size |
|---|---|---|---|
| 1 | Cut each stream only when it is durable past the cut's decision: StorageManager keeps the decision's length with the cut and passes the cut to a stream when that stream's confirmed length has passed it | P2 | M |
| 2 | No null slots: the copying replica has its stream; `pretruncate` and `removeReplica` skip a failed one | P3, P6 | S |
| 3 | Refuse streams of different histories: before one stream is appended from another (startup, `addReplica`), compare their bytes where they overlap, from the shorter one's last meta block to its end | P9 | S to M |
| 4 | The job waits for the added replica itself, and reports a failed copy | P1, P6 | S |
| 5 | Decide what STRONG means with several replicas (one, or all that are ACTIVE) and when one has failed (today: ORDINARY, silently) | P1, P6 | S, and a decision |
| 6 | Encrypt replicas with the database's key and nonce: a `SalsaStream` on each (same positions, same ciphertext) | P10 | S |
| 7 | The Pub API: `replica()` in any order; refuse the main's or another replica's directory; one default buffer time for `replica()` and `addReplica()` | P10, P1, P8 | S |
| 8 | Restore an empty main from a cut replica: move the main to the replica's first position first, or document starting from the replica's directory | P4 | S |
| 9 | A slow or hung replica stalls the database: a time limit after which it is marked failed, or an unbounded buffer | P8 | M, and a decision |
| 10 | Tell the application of a failed replica: a listener, a log line, or an exception at the next STRONG sync | P6 | S, and a decision |

And: the probes as unit and f-tests (P1, P3 to P7, P9, P10); P2's crash
images of a replica as a step of `level3.sh`, and a replica in
`level4.sh`'s eviction runs and in the night run; docs/levels.md on what a
replica and STRONG guarantee. With fix 1, the Lean model needs no change
(see the theory). Size M to L: four to six days with the gates, of which
fixes 9 and 10, and 5, need decisions first.


Change the design
-----------------

* C1. A copy of the stream outside the write path. The database writes
  one stream. A copier, a thread or a separate process, appends the
  main's bytes, in order, to the replica, and cuts the replica only when
  the replica is durable past the cut (the main's cut table says where).
  Every replica is then a crash image of the main at every moment, which
  T1 and T8 cover; the main's writes do not wait for it, and a slow or
  failed replica cannot stall them (P8, P6). A STRONG sync, if wanted,
  waits for the copier. The same copier with a network between is
  replication to another machine: a follower that can take over, by
  starting from what it has (T1). This is where the self-indexed stream
  helps: the stream is the whole database, and any prefix is a database.
  Size: M for a local copier with its checks; L for a network, with
  failover and the question of which copy is the main, a project of its
  own (005-05).
* C2. Leave it to the OS and to the files: mirrored disks (RAID 1, a ZFS
  or btrfs mirror, a mirrored volume) protect against the loss of a disk,
  for every file, with no code in BergDB; a backup copies the directory's
  files. The stream is append-only, so a copy of the files in their order
  should be a prefix, and so a crash image, if no cut deletes a file
  during the copy; not tested here. Size S: a page in the documents and a
  test that a copy made while the database writes starts as the database.
* C3. Failover for reads, from a replica when the main fails
  (`StorageManager.read`): little gain where the OS mirrors; not proposed.


What it is worth
================

* What local replicas give: a second copy on another disk of the same
  machine, kept by the application itself: no administrator, any file
  system (a USB disk, say), and with STRONG a sync that covers both
  disks.
* The same, without code in BergDB: a mirrored disk or volume, which also
  serves reads when a disk fails and rebuilds the copy; on cloud
  machines, block storage that is replicated already. And for backups,
  copying the files of an append-only stream (C2).
* What users of a database mostly mean by replication, a copy on another
  machine, for the loss of a machine and for failover: the code does not
  do it. C1 is the way to it.
* What local replicas cost, as they are: every byte buffered and written
  twice by the JVM, a 20 MB buffer and a thread per replica, writes that
  stall with a slow replica and stop with a hung one (P8), and the faults
  of P2, P6, P9 and P10, where a copy that looks good is not. Few would
  use local replicas, and as they are, those few would get a copy they
  cannot trust.


Found on the way
================

Now entries of their own (2026-10-23): 005-27, 005-28 and 005-29.

* P11: a crash image that ends where a meta block starts does not start.
  A fault of the main stream's recovery (Levels 2 and 3), not of
  replication; for a Fix entry of its own (005-27).
* `NodeStream.TransIterator.next` (NodeStream.java:317) loops for ever when
  the first transaction from the start position is a failed one (last
  byte 0): `transCount` is still 0, so it starts again at the same
  position (:320, :362). In one history the startup position always names
  a committed transaction (`TransSeq.take`), so only a stream made of two
  histories meets it (P9); still, a damaged stream should give an error,
  not a hang. Small (005-28).
* `MemoryStream.assertOk` (MemoryStream.java:75) expects one array too many
  when the length is a multiple of 1,000,000 bytes, so `copy()` fails an
  assertion then (`CutStream.copy` too, which `CrashTest` uses); P2 met it.
  The probes run without assertions in `MemoryStream`. Test code only;
  a one-line fix (005-29; an empty stream fails it too).
* Messages: `BadReplicaException`'s "Replica 'r is illegal. It's length
  is" and the job's "waiting for syncString"; they go with the code, or are
  fixed with it.


Again on 63fa5de, after 005-01
==============================

2026-10-23. 005-01 made a transaction that throws after its go point fail
the database. All probes but P8 ran again on `63fa5de`, with the same
tools ([runs/78cc5f3/](runs/78cc5f3/)); the 15 existing tests pass.

* P1, P4, P5, P7, P10, P11: the same. P9: the same (the stack's line
  numbers moved).
* P2: the same pattern; the counts vary with the timing of the flushes.
  Of 1,730 replica images, all 923 that were shorter than their cut's
  decision were broken (15 did not start, 908 failed lookups), and the
  other 807 were right; the main's 2,571 images were all right.
* P6 and P3 changed. The `NullPointerException` of a cut that meets a null
  stream (a failed replica in P6, one being copied in P3) is thrown in
  reclaim's listener, after the go point of the transaction that makes the
  cut, so it now fails the database: that transaction has committed, and
  every later transaction and read is refused with a `DbFailedException`
  until a restart, after which the database is right. In P6 with reclaim,
  5,812 of the 6,000 transactions threw (on `691794d`, 2,810 of the 5,818
  after the failure), `removeReplica` threw as before, and the database
  stayed failed until the restart. In P3's fourth case, a writer at full
  speed with cuts during the copy, the database failed during the copy, and
  `addReplica`'s job died with it at 99 percent ("Almost done, waiting for
  syncString..."). So the failure of a replica, which `MainErrorRule` means
  the database to survive, now stops the database at the next cut.


Files
=====

* [tools/ReplicaProbe.java](tools/ReplicaProbe.java): the probes P1 to
  P11, in package `bergdb.core`; [tools/run.sh](tools/run.sh) compiles it
  against `java/build/bergdb.jar` and runs one;
  [tools/all.sh](tools/all.sh) runs all but P8, and
  [tools/p2-all.sh](tools/p2-all.sh) P2's six runs.
* [runs/](runs/): the outputs, on `691794d`, and
  [runs/existing-tests.txt](runs/existing-tests.txt), the run of the 15
  existing tests (with `StorageManagerTester`'s three others);
  [runs/78cc5f3/](runs/78cc5f3/), the same again on `63fa5de` (all but
  P8).
