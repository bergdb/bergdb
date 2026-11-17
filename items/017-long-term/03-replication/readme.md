017-03. Replication: ways to implement it
=========================================

Status: open (notes only). Created 2026-11-04 by Claude (Opus 5.5, Claude
Code), at Frans's request, when replication was removed from BergDB
(005-11, "Frans's decision": "A with C2 now").

What this topic holds: the replication design that BergDB had until
2026-11-04, described in full so that it can be reused without the old
code; the open question of durability and waiting for replication, in
Frans's words; and the options for a future design. Nothing here is
planned. The study behind most of it is 005-11 and its report,
[005-11's report](../../005-todo/11-replication/report.md) (cited below as
"the report"), with the probes P1 to P11.


Why it matters
--------------

What users of a database mostly mean by replication is a copy on another
machine, for the loss of a machine and for failover. BergDB never had
that: its replicas were local streams in the same process. Today it has
none, and copies are left to the OS and the file system (005-11, option
C2): a mirrored disk or volume for the loss of a disk, and a copy of the
stream's files for a backup. A future design would decide whether BergDB
should give more than that, and how it shows in the API, where it is linked
to durability.


The open question
-----------------

In Frans's words (2026-10-20, 005-11, "The question"): replication, "we
should either remove it or implement it fully. Not sure where we are with
this."

Frans, 2026-10-23, after the study (005-11, "The question"): "Leave this
todo open. I need to think carefully about this one. Replication is linked
to durability and it affects the public API. As it, perhaps, should.
Important transactions may want to wait for replication before announcing
the transaction completed. I remember thinking about this carefully. And
the solution was features other database do not have. Such as transaction
synch() that can depend on whether data has been replicated." And: "need to
think about it and discuss more with you."

Frans, later the same day: "Perhaps we should be able to wait until
replicated. But, this can be rare and require calling StorageManager (?) or
something special after a transaction. So, we could treat if more as a
special case instead of using synch() method. Just a thought."

Frans, 2026-11-04 (005-11, "Frans's decision"): "A with C2 now". The
removal (A) was proposed as the first step of C1 below: with a special call
instead of a sync level, "A now and C1 later fit without a gap: STRONG goes
with A, and C1 brings the call" (005-11, "Proposal").

The questions that 005-11 ("Durability and the API") put for the
discussion, still open:

1. Which levels should the API offer, and what should each mean: the main;
   one replica; all replicas; a replica on another machine? Or one level,
   and replication waited for by a call of its own (the special case)?
2. Is the level chosen at the sync only, or also by the transaction (2012:
   the stream then flushes at once after it)?
3. When a level cannot be reached (no replica, a failed one, a slow one):
   wait, fail, or fall back to the main's durability, as STRONG did,
   silently (P6)?
4. Should reads be able to see durable states only (Frans's note of
   2013-11-09)?
5. Where do replicas live: in the write path, as they did (B below), so
   that a slow replica slows every write (P8), or outside it (C1), so that
   only the waits that ask for a replica wait for it?


The design that was removed
===========================

As it was on `c739237` (2026-11-04), the last commit before the removal,
and in release 2026.2 (tag `release-2026.2`, `d5b1bda`), whose replication
code is the same. It is 2017 code, from the import (`0257e0b`), which the
2026 work changed only in a few lines (the report, "What is 2017 code"; and
005-32, 005-48, 005-66, 005-67, 015-56, below). To read or run the old code:
`git show c739237:java/src/bergdb/storage/StorageManager.java`, or a
worktree at `c739237`; 005-11's probes
([tools/ReplicaProbe.java](../../005-todo/11-replication/tools/ReplicaProbe.java))
compile against that commit's jar, not against today's.


Where it was
------------

Line numbers are those of `c739237`.

* `java/src/bergdb/storage/StorageManager.java` (1,296 lines): the class
  `StorageManager`, an `AppendOnlyStream` over one main storage and zero or
  more replicas, and its inner classes `Builder`, `Internal` (the state that
  changes, swapped by compare-and-set), `MyStorage` (an active storage),
  `SynchingStorage` (a replica being copied in) and `ErrorStorage` (a
  failed one). About 650 of its lines were replication.
* The rules, in `java/src/bergdb/storage/`: the interfaces `DurabilityRule`
  and `ErrorRule`, and `MainConfirmedRule` (D1), `OneActiveReplicaRule` (D2)
  and `MainErrorRule`, 139 lines.
* `java/src/bergdb/pub/util/StorageInfo.java` (a storage's name, status and
  confirmed length; `STATUS_INITIALIZING`, `STATUS_ACTIVE`, `STATUS_ERROR`)
  and `java/src/bergdb/pub/util/BadReplicaException.java`.
* `java/src/bergdb/core/Db.java`: `addReplica` (:520), `removeReplica`,
  `getStorageInfos`, the startup's `syncStreams` (:1291), and the STRONG case
  of `sync(pos, level)` (:1782).
* `java/src/bergdb/core/DbHelper.java`: `checkReplicaId` and
  `AddReplicaClass`, the job of an `addReplica`, 145 lines.
* `java/src/bergdb/core/DbBuilder.java`: `stream(name, stream)` (:305) and
  `stream(name, stream, bufferSize, bufferTime)` (:331), a list of streams of
  which the first was the main.
* The Pub API: `DatabaseBuilder.replica(name, dir)`, `Database.addReplica(name,
  dir)`, `removeReplica(name)`, `getStorageInfos()`, and `SyncLevel.STRONG`;
  their implementations in `java/src/bergdb/pubimp/DatabaseBuilderImp.java`
  (`replica`, `openDirs`) and `java/src/bergdb/pubimp/DatabaseImp.java`
  (`addReplica`, :210).
* `java/src-dev/frans/PayDemo.java`, Frans's demo, which added a replica in
  `/a/data/pay-demo-replica` after each start.


The mechanism
-------------

Replication was local: a replica was another stream in the same process,
such as a directory on another disk. Nothing went over a network. A
replica of the Pub API was a `FileStream` in a directory of its own, a
directory that a database could start from alone.

* **Streams.** `StorageManager` held an array of `BufferedStream`s, index 0
  the main, and a parallel array of `StorageInfo`s. Each stream had its own
  buffer and its own storage thread, which wrote and forced the buffered
  bytes every buffer time or when a quarter of the buffer was full, and then
  told the manager the stream's new confirmed length (an `AppendListener`).
  The buffers: the main 10 MB and 50 ms (`DEFAULT_BUFFER_SIZE`,
  `DEFAULT_BUFFER_TIME`); a replica of `DatabaseBuilder.replica` 20 MB and 50
  ms (`DEFAULT_REPLICA_BUFFER_SIZE`, and the main's buffer time); a
  replica of `Database.addReplica` or of the Core's `DbBuilder.stream` 20 MB
  and 2,000 ms (`DEFAULT_REPLICA_BUFFER_TIME`).
* **Writes.** `append` (under the database's write lock) appended the bytes
  to the main's buffer, then to the buffer of every replica whose status was
  ACTIVE. So every ACTIVE replica got the main's bytes in the main's order;
  each was a prefix of the main from its first position on, behind the main
  by up to its buffer time. An I/O error of the main failed the storage; one
  of a replica was handled as below and the append went on.
* **Reads** came from the main only (`read`). A comment named failover to a
  replica as possible (C3 below); there was none.
* **Durability rules.** After every flush of any stream, `computeRules`
  evaluated three rules over the array of `StorageInfo`s:
  * the error rule, `MainErrorRule`: the storage as a whole has failed only
    when the main has;
  * D1, `MainConfirmedRule`: the main's confirmed length;
  * D2, `OneActiveReplicaRule`: the smaller of the main's confirmed length
    and the largest confirmed length among the ACTIVE replicas; the main's
    when no replica was ACTIVE. D2 was kept at most D1.
  The rules were objects behind interfaces, so other rules could be set
  (`setD2`; one test set "every stream confirmed"); the Pub API did not show
  them. These D1 and D2 are StorageManager's names; docs/levels.md uses the
  same names for two decisions of Level 3, which are other things.
* **Errors and statuses.** A storage was INITIALIZING while `addReplica`
  copied into it, ACTIVE, or ERROR. A replica's I/O error
  (`handleStreamException`) closed its stream, set its slot in the array of
  streams to null, replaced its `StorageInfo` by an `ErrorStorage` with the
  exception's text, and computed the rules again. Nothing else: no
  exception, no log line; `getStorageInfos` showed it.


The sync levels
---------------

A commit returned before its bytes were durable, as it does today; the
application waited when it wanted to, for the level it wanted:
`Transaction.sync(level)` for that transaction, `Connection.sync(level)`
for the connection's last transaction, `Database.sync(level)` for the last
transaction started; `sync()` was ORDINARY.

* NONE: no wait.
* ORDINARY: `StorageManager.sync(length)` waited until D1 covered the
  transaction's last byte.
* STRONG: `StorageManager.syncStrong(length)` waited until D2 covered it,
  so "the main and one replica", whichever replica was fastest, and the
  same as ORDINARY when no replica was ACTIVE, also when the only one had
  failed. Since 005-48 (group commit) a waiting STRONG sync had every
  stream's buffer written at once, the replicas' too.

`SyncLevel.STRONG` was used in about 130 places, nearly all of them tests
and stress programs that ran without a replica, so as ORDINARY syncs. It was
removed with replication; those calls are ORDINARY now.


Startup's copying
-----------------

`Db.start` called `syncStreams` before recovery, under both of the
database's locks:

1. `checkStreamIds`: when the main was not empty, every replica that was
   not empty had to have the main's database ID in its last valid meta
   block, or `BadReplicaException`.
2. `syncMainStream`: the longest replica that held the bytes the main
   lacked (its first position at most the main's length) was copied onto
   the main, from the main's length on, 50 kB at a time: "the longest stream
   wins".
3. `syncReplicaStreams`: a replica shorter than the main's first position
   was emptied and moved to it (`AppendOnlyStream.seekFirstPos`; a
   `FileStream` deletes its files); a replica longer than the main was
   refused (`BadReplicaException`); the others got the main's tail.
4. Then recovery ran through the manager, so the bytes it appended (the
   zero fill of a torn last transaction) went to every stream.

Only the database ID was checked; that the streams held the same bytes
where they overlapped was assumed (P9 shows where it fails). Since 005-32 a
start that threw closed every stream before the exception left, so the
copies it had made were written, and no storage thread ran on.


addReplica's copy job
---------------------

`Database.addReplica(name, dir)` opened a `FileStream` in the directory and
called `Db.addReplica(name, stream, 20 MB, 2000 ms)`, which returned a
`Job`:

1. `DbHelper.checkReplicaId`: a replica that was not empty had to have the
   database's ID (`BadReplicaException`).
2. `StorageManager.addReplica`: the name had to be new and the replica no
   longer than the main (`BadReplicaException`); a replica shorter than the
   main's first position was emptied and moved to it. The replica got a
   `BufferedStream`, started, and was added as a `SynchingStorage`
   (INITIALIZING), by compare-and-set on the manager's state. Its slot in
   the array of streams stayed null until it was ACTIVE.
3. A thread (`db-addReplica-sync-NAME-ID`, below normal priority) copied
   the main into it, 50 kB at a time, reading the main without the write
   lock; the last part, under 50 kB, under the write lock, after which the
   storage was made ACTIVE (`makeActive`, which also filled the slot). So
   no append was missed: from then on `append` wrote to it.
4. The thread then executed a dummy transaction (`DbConstants.DUMMY_KEY`)
   and a STRONG sync of it, and the job reported 100 and "Done!". On the
   way its progress note said "Almost done, waiting for syncString..."
   (sic).

The job's `join()` waited for the thread; since 005-46 an interrupted
caller's join returned the status with the flag set (it threw an `Error`).
`removeReplica(name)` took the replica out of the arrays and stopped its
`BufferedStream`: what it had buffered was not written, and its files
stayed.

Cuts and stop: reclaim's cut (`pretruncate`) went to every stream in the
array, the main first, once the main's D1 had passed the stream length at
the cut's decision (`Reclaim.cutIfDurable`); a `BufferedStream` kept a cut
past its flushed bytes and made it after the flush that reached it. The
replicas' durable lengths were not looked at (P2). `close()` flushed every
stream; `stop()` did not.


The Pub API
-----------

* `DatabaseBuilder.replica(String name, String dir)`, declared `throws
  IOException` (not thrown since 005-66): records a replica's directory;
  `start()` opened it after the database's own, in the order given (since
  005-66; until then `replica()` opened it, and one given before `dir()` was
  dropped). Each directory was locked by its `FileStream` (005-63).
* `Database.addReplica(String name, String dir)` returning a `Job`;
  `Database.removeReplica(String name)`; `Database.getStorageInfos()`
  returning `StorageInfo[]`.
* `SyncLevel.STRONG`, and `BadReplicaException` from `start()` and
  `addReplica`.
* An encrypted database (`cryptoKey`) wrapped only the main in a
  `SalsaStream`; replicas were written in plain text (P10).
* Release 2026.1 kept it as it was, documented as experimental (Frans,
  2026-10-25); release 2026.2 said it was experimental, with known faults,
  that its API would change, and that it must not be used in production
  (016-01, section 3).


The tests
---------

Removed with the code on 2026-11-04 (005-11, "Frans's decision"):

* `StorageManagerTester`: the startup copying with two and three
  `MemoryStream`s and with `FileStream`s (`testSync1` to `testSync4`),
  `addReplica` with an empty replica, one with old data, one with old and
  current data, after a cut of the main, and while appending
  (`testAddReplica1` to `testAddReplica5`, `testAddReplicaWhileAppending`),
  and `removeReplica` (`testRemoveReplica1`, `testRemoveReplica2`). They
  checked lengths and first positions, not bytes. `testMultipleClose` and
  `testSyncStartsTheFlush` had a replica too; they stay, with the main only.
* `DbTester.testBadReplica1`: `Db.addReplica` of another database's stream
  throws `BadReplicaException`.
* `PubTester.testBadStartReplica`: a start with two databases' streams
  throws `BadReplicaException`.
* `PubTester.testReplicaBeforeDir` (005-66): a replica given before `dir()`
  is kept and written.
* `PubTester.testRefusedStartClosesOnlyItsOwn` (015-56): a refused start
  closes what it opened and nothing of a running database, with a replica's
  directory as the second directory.
* `DbTesterFailure.testFailedStartOfTwoHistories` (005-32): a start with a
  main and a replica of two histories fails after it has copied the
  replica's tail to the main; the copy is written and the streams closed.
* `PubInterruptTester`: its join of `addReplica`'s job by an interrupted
  thread (005-46).

Never tested: a database with a replica in use under the levels' checks,
the Pub API's methods together, STRONG with a replica, cuts, crashes,
failures, eviction or encryption with a replica; no level, stress or night
test had a replica (the report, "What the tests cover"). The probes of
005-11 covered those once, by hand.


The faults found
----------------

From 005-11's study (the report, "The probes"; on `691794d` and again on
`63fa5de`) and after it:

* **Cuts (P2).** A replica was cut when the main, not the replica, was
  durable past the cut's decision. Of 1,756 replica images that a crash at a
  cut would leave, 943 were shorter than the decision, and all 943 were
  broken: 32 did not start, 911 failed lookups at times they claimed to
  have. All 2,570 of the main's were right.
* **A restart without the replica (P9).** After a crash that left the
  replica ahead of the main, a start without it, then with it, mixed two
  histories of the same database ID: the main hung at startup for good
  (005-28 then made that an error), or the replica silently held another
  history than the main.
* **A failing replica (P6).** It was dropped without a word, and a STRONG
  sync then returned as an ORDINARY one. With reclaim, the next cut threw
  `NullPointerException` on the failed replica's null slot; since 005-01 that
  came after the transaction's go point and failed the database. A cut
  during `addReplica`'s copy did the same (P3).
* **STRONG and the job (P1, P6, P8).** With two replicas the faster met
  STRONG; an added replica held 0 bytes after `stop()` though its job said
  "Done!"; the job said "Done!" also when the copy failed; with
  `addReplica`'s 2 s buffer every STRONG sync took 2 s.
* **Encryption (P10).** Replicas were written in plain text and opened
  without the key. `SalsaStream.seekFirstPos` left its keystream at the old
  length (016-06, S1), so an encrypted replica moved by it would have been
  wrong too.
* **More (P4, P8, P10).** A slow replica stalled every write once its
  buffer was full, a hung one blocked the writes and `Database.sync()`;
  `addReplica` of the main's own directory was accepted; an empty main could
  not be restored from a replica that had been cut (P4).
* **Leaks.** A manager closed while a replica was still being copied in
  never closed that replica's stream (its slot was null): its thread stayed
  and, since 005-63, its directory stayed locked until the JVM ended
  (005-67's probe, noted in 005-11). `removeReplica` stopped the replica's
  `BufferedStream` and nothing closed it later, so a stop that met an
  interrupt of the storage thread leaked the stream and its lock (016-06,
  verify-2).
* Messages: "Replica 'r is illegal. It's length is" and "waiting for
  syncString" (sic).

What worked (P1, P3, P5, P7): a replica was a byte copy of the main and
started alone as the database; one could be added while the database
wrote, also after cuts; a crash in the middle of its copy left an older but
valid database, and the next start completed it; eviction made no
difference.


What the theory says
--------------------

From the report, "What the theory says". A replica is meant to be a crash
image of the main, a prefix of its bytes. T1 (recovery) then makes it a
database, and with cuts T8 does, if the replica is cut only when it is
durable past the cut's decision. Then the Lean model needs nothing new: a
copy that is always a prefix of the main, cut by the main's own rule, is
what T1, T8 and T12 cover. The startup's copying between streams, and
streams of different histories, are outside the model, which has one stream
of one run. "Byte-identical replicas by T2" holds for streams that end at a
record boundary; a torn record, which recovery fills with zeros, is where
two streams part (P9).


Options for a future design
===========================

From 005-11, "The options", where each is described in full with what it
takes, and the report, "What each option takes". All keep the commit that
does not wait and the sync per transaction; they differ in whether a wait
can cover a copy elsewhere, and how. A (remove) and C2 (the OS and the
files) are what BergDB does now.


B. Complete the removed design
------------------------------

Replicas as streams in the write path, as above, made correct and tested.
The fixes the probes call for (005-11, "B"):

1. Cut each stream only when it is durable past the cut's decision: keep the
   decision's length with the cut and pass the cut to a stream when that
   stream's confirmed length has passed it (P2). M.
2. No null streams: the copying replica has its stream; cuts and removal
   skip a failed one (P3, P6). S.
3. Refuse streams of different histories: before one stream is appended
   from another (startup, `addReplica`), compare their bytes where they
   overlap, from the shorter one's last meta block to its end (P9). S to M.
4. The job waits for the added replica itself, and reports a failed copy
   (P1, P6). S.
5. Decide what STRONG means with several replicas (one, all ACTIVE, a
   number) and with a failed one (P1, P6). S, and a decision.
6. Encrypt replicas with the database's key and nonce: a `SalsaStream` on
   each, the same positions giving the same ciphertext (P10). S.
7. The Pub API: `replica()` in any order (done in 005-66); refuse the main's
   or another replica's directory; one default buffer time (P10, P1, P8). S.
8. Restore an empty main from a cut replica, or document starting from the
   replica's directory (P4). S.
9. A slow or hung replica: a time limit after which it is failed, or a
   larger buffer (P8). M, and a decision.
10. Tell the application of a failed replica: a listener, a log line, or an
    exception at the next STRONG sync (P6). S, and a decision.

Then the probes as tests, P2's crash images of a replica in `level3.sh`, a
replica in `level4.sh` and the night run. Size M to L. It can grow towards
the 2012 design (D3, rules by name in the Pub API, a network replica written
as a stream), but each replica stays in the write path: once its buffer is
full every write waits for it, so a slow or remote replica slows the whole
database, and the main's buffer and thread are repeated per replica.


C1. Copy the stream outside the write path
------------------------------------------

The database writes one stream, as now. A copier (a thread, a separate
process or a backup command) appends the main's durable bytes, in order,
to a replica, and cuts the replica only when the replica is durable past
the cut (the main's cut table says where).

* The copier knows its replica's durable length. A STRONG sync, or a call
  of its own as in Frans's special case, waits until that length covers the
  transaction, as the 2013 backlog's network replica that "confirms". The
  main's writes never wait for a replica; only the waits that ask for one
  do. A replica that falls behind delays only those waits, so a limit is
  needed: how far behind before such a wait fails.
* A copy of durable bytes only can never be ahead of the main, so two
  histories cannot meet (P9) as long as the main stays the main; a failover
  to a replica needs P9's check. A replica is cut by the main's own rule
  (P2), and its failure or slowness cannot touch the main's writes (P6, P8).
* Local first, size M: the copier, its rule for cuts, adding and removing
  copies, the tests (P1 to P7 and P2's crash images, for copies). Over a
  network, with a follower that can take over, size L: a project of its
  own, with 017-01 (what to do with BergDB).
* Replicas on other machines fit the same API (the 2012 D3: two places),
  and so do the 2013 active replicas: a follower starts from its prefix (T1)
  and applies the records as they come.

005-11's view (its "Proposal"): if BergDB should have replication, the
self-indexed stream is well suited to C1: any prefix of the stream is a
database, so a copy that only appends the main's bytes is always one. Put
otherwise (a note here, not 005-11's words): the stream is the whole
database, index included, so the copier needs to know positions only, not
records or transactions: the main's durable length, and the cut table for
where a replica may be cut. And with Frans's
special call, A now and C1 later fit without a gap: nothing in the API had
to stay meanwhile.

A sketch of the special call (005-11, "A special case, not a sync level";
the names are to be found): the syncs keep one meaning, the main's
durability; the replication part of the Pub API, not the transaction, has
a call that, given a transaction (its last position) or everything so far,
waits until a replica (or the replicas named) holds those bytes durably,
with a time limit, such as
`database.replication().waitUntilReplicated(transaction)`; beside it, an
answer without a wait, as the `isDurable(level)` idea of 2026-10-13 in
`Transaction` and `Connection` ("commit now, ask later"). A transaction
that must always be replicated calls it every time, which is fine if such
transactions are rare.


C3. Failover for reads
----------------------

Reads from a replica when the main fails (the old `StorageManager.read`
named it as possible). Little gain where the OS mirrors; not proposed on its
own. It could come with B or C1: with C1, a replica is a prefix of the main,
so a read below its length is right.


Other ways, worth a look
------------------------

Not in 005-11's options; added here as notes, not studied:

* **A backup command (C1 as a tool).** A call or a program that copies the
  stream's durable prefix to a directory while the database runs: the
  stream's files in order, up to the durable length, with the cut table's
  rule for the first file. It gives C2's backups with a guarantee instead
  of an expectation, and is the local copier of C1 without a thread in the
  database. C2's own test, that a copy of the files made while the database
  writes starts as the database, is not made yet (005-11, "C2").
* **Shipping the stream to a follower.** C1 over a network: the follower
  receives the stream's bytes from a position on, appends them, and reports
  its durable length; it can serve reads at times it has (the 2013 active
  replicas) and take over by starting from its prefix. The questions are
  those of any primary and follower: which copy is the main after a
  failover, and how an old main that comes back is refused (P9's check, the
  database ID and the bytes where they overlap). PostgreSQL's
  `synchronous_commit` levels, from `local` to `remote_apply`, are the
  nearest model elsewhere (005-11, "Durability and the API").
* **Durable reads.** A connection that reads only states that are durable,
  or durable on a replica (Frans, 2013-11-09: "Normal durability and
  'strong' durability"; MongoDB's read concern "majority"). With C1 it is a
  lookup time no later than the last transaction that the replica holds
  durably.
* **Several mains.** Frans's 2012 stream manager (F1-007,
  `2012/2012-stream-manager.txt`): child streams of several kinds (files,
  FTP, SCP, cloud), most write-only, failure rules, and "ensure durable"
  requests at levels D1 "survives process", D2 "survives OS", D3 "highest
  available durability achieved", defined by replaceable rules. The removed
  code had the levels ORDINARY and STRONG, the sync per transaction, the
  rules behind an interface and local replicas of it; not D3, network
  replicas, the rules in the Pub API, a check of the synced streams,
  warnings, active replicas or durable reads (005-11, "Durability and the
  API").


Log
===

2026-11-04. Created, at Frans's request, when replication was removed
(005-11: "A with C2 now"): the removed design, the open question, the
options.
