005-11. Replication: study it, for Frans to decide
=================================================

Status: done (2026-11-04; Frans decided "A with C2 now": replication
removed, copies left to the OS and the file system; see "Frans's
decision"). Kind: decide. Created 2026-10-20.


The question
------------

In Frans's words (2026-10-20): replication, "we should either remove it
or implement it fully. Not sure where we are with this." The work is to
study the existing implementation and its tests, and to give Frans the
material to decide. Likely options: remove the feature; make sure it works
and that its testing is complete; change its design.

Found in 005-10, where the Pub API's replication methods came up as
unused (G1): nothing in the repository calls `Database.addReplica`,
`removeReplica`, `getStorageInfos` or `DatabaseBuilder.replica`. They stay
until Frans decides here.

In Frans's words (2026-10-23), after the study: "Leave this todo open. I
need to think carefully about this one. Replication is linked to
durability and it affects the public API. As it, perhaps, should.
Important transactions may want to wait for replication before announcing
the transaction completed. I remember thinking about this carefully. And
the solution was features other database do not have. Such as transaction
synch() that can depend on whether data has been replicated." And: "need
to think about it and discuss more with you." "Durability and the API"
below collects the material for that; "The options" describes each option
in full, with what it means for the syncs.

Frans, later the same day: "Perhaps we should be able to wait until
replicated. But, this can be rare and require calling StorageManager (?)
or something special after a transaction. So, we could treat if more as a
special case instead of using synch() method. Just a thought." See "A
special case, not a sync level" below.


The study, in short
-------------------

By Claude (Opus 5.5, Claude Code), 2026-10-22, on commit `cbeb9bd`; no
change to `java/` or `lean/`. The full study, which follows the six
questions of this entry's definition, is in
[11-replication/report.md](11-replication/report.md); the probes P1 to
P11, small programs that run today's code, are in
[11-replication/tools/](11-replication/tools/), their outputs in
[11-replication/runs/](11-replication/runs/). Run again on `78cc5f3`
(2026-10-23, after 005-01), in
[11-replication/runs/78cc5f3/](11-replication/runs/78cc5f3/): the same,
but for P3 and P6, below.

* What it is. A replica is a second stream in the same process (a
  directory on another disk, say), written with every append behind its
  own buffer; reads come from the main only. ORDINARY syncs wait for the
  main, STRONG ones for the main and one replica. At startup the longest
  stream is copied onto the others; `addReplica` copies the main into a
  new replica while the database runs. It is 2017 code that no 2026 work
  changed but for a few lines.
* What is tested. 15 unit tests of 2017: 13 of the storage manager, which
  check lengths, not bytes, and 2 of the error of a replica of another
  database. Nothing with a database in use, the Pub API's methods, cuts,
  crashes, failures, eviction or encryption; no level, stress or night
  test has a replica.
* What works (probes P1, P3, P5, P7). A replica is a byte copy of the
  main and starts alone as the database; one can be added while the
  database writes, also after cuts; a crash in the middle of its copy
  leaves an older but valid database, and the next start completes it;
  eviction makes no difference.
* What does not, each found by a probe:
  * Cuts (P2). A replica is cut when the main, not the replica, is durable
    past the cut's decision. Of 1,756 replica images that a crash at a cut
    would leave, 943 were shorter than the decision, and all 943 were
    broken: 32 did not start, 911 failed lookups at times they claim to
    have (295 at the latest time). The main's 2,570 images were all right.
    On `78cc5f3`, the same: all 923 short replica images were broken, and
    none of the main's 2,571.
  * A restart without the replica (P9). After a crash that left the
    replica ahead of the main, a start without it, then with it, mixes two
    histories of the same database ID: the main then hung at startup for
    good, or the replica silently held another history than the main.
  * A failing replica (P6). It is dropped without a word, and a STRONG
    sync then returns as an ORDINARY one. With reclaim, the next cut throws
    `NullPointerException` (the failed replica's stream is null). On
    `cbeb9bd`, about half of all later transactions threw it after they had
    committed, until `removeReplica`, which throws too. Since 005-01
    (`78cc5f3`), the exception comes after the transaction's go point and
    fails the database: every later transaction and read is refused until a
    restart. A replica's disk that fails takes the database down. A cut
    during `addReplica`'s copy does the same (P3: the copying replica's
    stream is null too).
  * STRONG and the job (P1, P6, P8). With two replicas, STRONG is met by
    the faster one; an added replica held 0 bytes after `stop()` though
    its job said "Done!". The job says "Done!" also when the copy failed.
    With `addReplica`'s buffer time of 2 s, every STRONG sync takes 2 s.
  * Encryption (P10). An encrypted database writes its replicas in plain
    text; they open without the key.
  * More (P4, P8, P10): `replica()` before `dir()` drops the replica
    silently; a slow replica stalls every write, a hung one blocks the
    writes and `Database.sync()`; an empty main cannot be restored from a
    replica that has been cut.
* What the theory says. A replica is meant to be a crash image of the
  main, a prefix of its bytes; T1 (recovery) then makes it a database, and
  with cuts T8 does, if the replica is cut only when it is durable past
  the cut's decision. Then the Lean model needs nothing new. The startup's
  copying between streams, and streams of different histories, are
  outside the model. docs/prior-art.md's "byte-identical replicas by T2"
  holds for streams that end at a record boundary; a torn record, which
  recovery fills with zeros, is where two streams part (P9).
* What it is worth. A copy on a second local disk, kept by the
  application. A mirrored disk or volume does the same for every file,
  with no code here, and a copy of an append-only stream's files is a
  backup. What users of a database mostly want from replication, a copy
  on another machine, the code does not do.


Durability and the API
----------------------

Material for the discussion, 2026-10-23.

**Today**, on `78cc5f3`:

* A commit returns before its bytes are durable. The application waits
  when it wants to, for the level it wants: `Transaction.sync(level)` for
  that transaction, `Connection.sync(level)` for the connection's last
  transaction, `Database.sync(level)` for the last transaction started;
  `sync()` is ORDINARY. The levels (`SyncLevel`): NONE; ORDINARY, the main
  storage's forced length (StorageManager's rule D1); STRONG, the main and
  one replica (D2), which is ORDINARY when no replica is ACTIVE.
* The transactions of many threads share one forced write: the storage
  thread forces about every 20 ms, and a sync waits for that (005-13: one
  thread that syncs every commit gets 29 a second, 64 threads 1,800).
* The levels are rules over the set of storages, objects behind an
  interface (`DurabilityRule`, `StorageManager.setD2`); the Pub API does
  not show them.
* An idea of 2026-10-13, a comment in `Transaction` and `Connection`:
  `isDurable(level)`, answered at once: "commit now, ask later".

**Frans's earlier design**, in F1-007 (the f1 repository,
`a/007-bergdb-261012/bergdb/doc/`):

* 2012, `2012/2012-stream-manager.txt`: a stream manager over child
  streams: files, and replicas on FTP, SCP, Google App Engine, Google Drive,
  even e-mail, most of them write-only. Reads spread over them, failure
  rules (which streams may fail), and "ensure durable" requests at levels:
  D1 "survives process", D2 "survives OS", D3 "highest available durability
  achieved", such as "to replicate to at least two remote locations". The
  levels are defined by replaceable rules, and the client uses them by
  name.
  "Possibly, the transactions themselves could carry a durability
  parameter", so that the stream flushes at once after such a
  transaction.
* 2013-01, `2013/2013-01-notes.txt`: a Pub API sketch with a file replica
  and an FTP replica and `d2(DurabilityRule.ONE_REPLICA)`. The startup sync
  "results in identical streams. This should be verified partially" (not
  done: P9). A failed replica as a warning (not done: P6).
* 2013-02, `2013/2013-02-notes.txt`: rules by name in the Pub API,
  `Database.setD1(Durability.MAIN_STORAGE)`,
  `Database.setD2(Durability.TWO_STORAGES_IF_AVAILABLE)`.
* 2013 to 2014, `2013/2013-backlog.txt`, `2014/2014-ideas.txt`: a network
  replica that sends "confirm" messages back ("More secure D2 durability
  can be attained"); active replicas that serve queries, kept from the
  stream (`2013/2013-active-replica.txt`, `2013/2013-q4-notes.txt`, which
  also weighs a stream of KVs as the format); and reading only durable
  state, 2013-11-09: "a Connection for reading that uses not the absolutely
  latest possible lookup time, but the latest *durable* lookup time. Normal
  durability and 'strong' durability." 2014: "Advanced replication has to
  wait till 2015.1."
* Of this, the code has the levels ORDINARY and STRONG, the sync per
  transaction, the rules D1 and D2 behind an interface, and local
  replicas. Not: D3, network replicas, the rules in the Pub API, a check of
  the synced streams, warnings, active replicas, durable reads.

**Elsewhere**, a first look:

* PostgreSQL: `synchronous_commit`, which can be set per transaction
  (`SET LOCAL`), from `off` (the commit does not wait for its flush)
  through `local` and `remote_write` to `on` (a synchronous standby has
  flushed it) and `remote_apply` (applied there, visible to its queries):
  "It is therefore possible, and useful, to have some transactions commit
  synchronously and others asynchronously"
  ([documentation](https://www.postgresql.org/docs/current/runtime-config-wal.html)).
  The level is chosen before the commit, which waits for it.
* SQL Server: delayed durability per transaction (`COMMIT ... WITH
  (DELAYED_DURABILITY = ON)`), and `sys.sp_flush_log`, which later makes all
  earlier delayed transactions durable
  ([documentation](https://learn.microsoft.com/en-us/sql/relational-databases/system-stored-procedures/sys-sp-flush-log-transact-sql)):
  commit now, durable later, on the local log.
* MongoDB: a write concern per operation or per transaction (`w: 1`,
  `w: "majority"`), and the read concern `"majority"`, which reads only data
  acknowledged by a majority, "durable and guaranteed to not roll back"
  ([write concern](https://www.mongodb.com/docs/manual/reference/write-concern/),
  [read concern](https://www.mongodb.com/docs/manual/reference/read-concern-majority/)):
  reads of durable state.
* So the parts exist elsewhere, each on its own. What BergDB's design has
  in one place, embedded and on one stream: the commit never waits; the
  wait is a call of its own, for one transaction or for all up to a point,
  at a level chosen afterwards; the levels are rules over the set of
  storages; and, as ideas, an answer without a wait (`isDurable`) and
  reads of durable states only.

**A special case, not a sync level** (Frans's thought of 2026-10-23,
above): the syncs mean the main's durability only, and a transaction that
must be replicated before it is announced waits by a call of its own, made
after it. A first look at what that would mean, by Claude:

* The syncs that every application uses get one meaning, the main's forced
  length: `sync()`, `Transaction.sync()`, `Connection.sync()`.
  `SyncLevel` could keep NONE and ORDINARY, or go.
* The special call belongs to the replication part, not to the
  transaction. Frans names StorageManager, which is internal; in the Pub
  API it would be the replication's own object. Given a transaction (its
  last position), or everything so far, it waits until a replica (or the
  replicas named) holds those bytes durably, with a time limit; beside it,
  an answer without a wait, as `isDurable`. Something like
  `database.replication().waitUntilReplicated(transaction)`; the names are
  to be found.
* With C1 it is natural: the copier knows its replica's durable length,
  and the call waits until that covers the position. With B it waits for
  D2, or for named replicas. With A there is no such call until C1 comes;
  as `sync()` would never have waited for a replica, nothing in the API has
  to come back meanwhile, so A now and C1 later fit without keeping
  `SyncLevel.STRONG`.
* What it leaves out: a transaction that must always be replicated calls
  it every time, which is fine if such transactions are rare; and the 2012
  D3 as a level of a sync.
* It is one answer to questions 1 and 2: one level for the syncs, and
  replication waited for apart from them.

**Questions** for the discussion:

1. Which levels should the API offer, and what should each mean: the
   main; one replica; all replicas; a replica on another machine? Or one
   level, and replication waited for by a call of its own (the special
   case above)?
2. Is the level chosen at the sync only, as today, or also by the
   transaction (2012: the stream then flushes at once after it)?
3. When a level cannot be reached (no replica, a failed one, a slow one):
   wait, fail, or fall back to ORDINARY, as STRONG does today, silently
   (P6)?
4. Should reads be able to see durable states only (2013-11-09)?
5. Where do replicas live: in the write path, as now (B below), so that a
   slow replica slows every write (P8), or outside it (C1), so that only
   the syncs that ask for a replica wait for it?


The options
-----------

All five keep the commit that does not wait and the sync per
transaction; they differ in whether a sync can wait for a copy elsewhere,
and how. More detail, with the lists of what changes, in the report's
"What each option takes".

**A. Remove replication.** The database has one stream, the main.

* What it takes. The Pub API's `Database.addReplica`, `removeReplica`,
  `getStorageInfos` and `DatabaseBuilder.replica`, with their
  implementations, `BadReplicaException` and `StorageInfo`; `Db`'s and
  `DbHelper`'s replica code and the ID check at startup; StorageManager's
  replica code (the copying and failed storages, the startup sync, add and
  remove, the rules), about 650 of its 1,243 lines, and the five rule
  classes; 15 tests; `PayDemo`'s call of `addReplica` (Frans's demo, his
  call); the documents' STRONG and the limits that name replication. About
  1,700 lines, nearly all 2017 code and tests. Size S: about a day, with
  the four gates; Lean unchanged.
* Durability and the API. One level is left: ORDINARY, the main's forced
  length. `SyncLevel.STRONG` stays, the same as ORDINARY (most of its about
  100 uses are tests), or goes. `Transaction.sync(STRONG)` no longer waits
  for a replica: the sync that depends on replication goes. A wait for a
  copy can come back with C1, as a level or as a call of its own (the
  special case above).
* Gives: no faulty code in the write path, a StorageManager of about half
  its size; the faults of P2, P3, P6, P9 and P10 gone. Costs: the
  replicated sync; mirroring within the process (C2 gives it otherwise);
  restoring an empty main from a replica (P4, which works only without
  cuts).

**B. Complete it.** Keep today's design, replicas as streams in the write
path, and make it correct and tested.

* What it takes. Ten fixes, from the probes:

  | # | Fix | Probe | Size |
  |---|---|---|---|
  | 1 | Cut each stream only when it is durable past the cut's decision: StorageManager keeps the decision's length with the cut and passes the cut to a stream when that stream's confirmed length has passed it | P2 | M |
  | 2 | No null streams: the copying replica has its stream; `pretruncate` and `removeReplica` skip a failed one (today a replica's failure fails the database at the next cut) | P3, P6 | S |
  | 3 | Refuse streams of different histories: before one stream is appended from another (startup, `addReplica`), compare their bytes where they overlap, from the shorter one's last meta block to its end | P9 | S to M |
  | 4 | The job waits for the added replica itself, and reports a failed copy | P1, P6 | S |
  | 5 | Decide what STRONG means with several replicas (one, all that are ACTIVE, a number) and when one has failed (today: ORDINARY, silently) | P1, P6 | S, and a decision |
  | 6 | Encrypt replicas with the database's key and nonce: a `SalsaStream` on each (the same positions give the same ciphertext) | P10 | S |
  | 7 | The Pub API: `replica()` in any order; refuse the main's or another replica's directory; one default buffer time for `replica()` and `addReplica()` | P10, P1, P8 | S |
  | 8 | Restore an empty main from a cut replica: move the main to the replica's first position first, or document starting from the replica's directory | P4 | S |
  | 9 | A slow or hung replica stalls the database: a time limit after which it is marked failed, or a larger buffer | P8 | M, and a decision |
  | 10 | Tell the application of a failed replica: a listener, a log line, or an exception at the next STRONG sync | P6 | S, and a decision |

  Then the probes as unit and f-tests; unit tests of `addReplica` itself,
  its copy, its job and the STRONG sync at its end, of which only the ID
  check has one today (a TODO of 2014 in `DbHelper` said so; gone since
  2026-10-25, 006-05); P2's crash images of a replica as a step of
  `level3.sh`; a replica in `level4.sh`'s eviction runs and in the night
  run; and the documents. Lean unchanged. Size M to L: four to six days
  with the gates, and decisions on 5, 9 and 10 first.
* Durability and the API. Today's model stays and becomes true:
  `Transaction.sync(STRONG)` waits until the transaction is on the main and
  on the replicas that fix 5 says. It can grow towards the 2012 design: D3,
  rules by name in the Pub API (2013-02), a network replica written as a
  stream (2012: FTP, SCP; 2013: a replica that confirms). But each replica
  stays in the write path: once its buffer is full, every write waits for
  it (P8), so a slow or remote replica slows the whole database, unless fix
  9 drops it; and the main's buffer and thread are repeated per replica.
* Gives: the replicated sync, local mirroring kept by the application, and
  the 2013 design finished (the check of the synced streams, the
  warnings). Costs: the most work for a local feature; the complexity stays
  in the write path; replication to another machine is not part of it.

**C1. Copy the stream outside the write path.** The database writes one
stream. A copier, a thread or a separate process or a backup command,
appends the main's durable bytes, in order, to a replica, and cuts the
replica only when the replica is durable past the cut (the cut table says
where).

* What it takes. The copier, its rule for cuts, adding and removing
  copies (the Pub API's methods can keep their names), the tests (P1 to P7
  and P2's crash images, for copies), the documents. Size M for a local
  copier. L for one over a network, with a follower that can take over: a
  project of its own, with 005-05.
* Durability and the API. The same levels, kept by another mechanism: the
  copier reports its replica's durable length, and a STRONG sync, or a
  call of its own as in the special case above, waits until that covers
  the transaction, as the 2013 backlog's network replica "confirms". The
  main's writes never wait for a replica; only the waits that ask for one
  do. A replica that falls behind delays only those waits, so a limit is
  needed (how far behind before such a wait fails).
  Replicas on other machines fit the same API (D3: two places), and so do
  the 2013 active replicas: a follower starts from its prefix (T1) and
  applies the records as they come.
* Gives: the replicated sync, local and later remote, with replicas that
  are crash images of the main at every moment, which T1 and T8 cover as
  they cover the main's own. A copy of durable bytes only can never be
  ahead of the main, so two histories cannot meet (P9) as long as the main
  stays the main (a failover to a replica needs P9's check); a replica is
  cut by the main's own rule, once it is durable past the decision (P2); and
  a replica's failure or slowness cannot touch the main's writes (P6, P8).
  The write path is simpler than today's. Costs: a
  new design; a STRONG sync waits for the copy after the main's force,
  where B forces both at once; the network part is large.

**C2. Leave it to the OS and to the files.** No replication in BergDB
(with A). Mirrored disks (RAID 1, a ZFS or btrfs mirror, a mirrored
volume) for the loss of a disk; a backup by copying the stream's files.

* What it takes. A page in the documents, and a test that a copy of the
  files made while the database writes starts as the database: an
  append-only stream copied in file order should be a prefix, if no cut
  deletes a file during the copy (not tested). Size S.
* Durability and the API. One level, ORDINARY. On a mirror, a forced write
  is on both disks before it returns, for every transaction, with no
  choice and no code here. No sync waits for a copy elsewhere.
* Gives: the least code. Costs: no replicated sync in the API, nothing for
  a second machine.

**C3. Failover for reads.** Reads from a replica when the main fails
(`StorageManager.read`, whose comment names it as possible). Little gain
where the OS mirrors; not proposed on its own. It could come later with B
or C1.


Proposal
--------

Claude, 2026-10-22: A with C2, now, before 005-05's decision on
publishing, since the Pub API offers replication. The code is not a
working feature to keep or extend: it leaves copies that look good and are
not (P2, P9), it writes in plain text what the database encrypts (P10),
and a replica's failure breaks the database (P6; since 005-01 it fails the
database). Completing it (B) costs more than removing it and gives a
feature that the OS gives better. If BergDB should have replication, the
self-indexed stream is well suited to C1: any prefix of the stream is a
database, so a copy that only appends the main's bytes is always one.

Added 2026-10-23, after Frans's words above: if the sync that waits for
replication is to stay in the API, A alone is not enough, and the choice
is between B and C1. C1 then, as it keeps the levels and the sync per
transaction, makes replicas crash images by construction, keeps a replica
out of the main's writes, and leads to replicas on other machines; A's
removal of today's mechanism is its first step, and `SyncLevel.STRONG` can
stay in the API meanwhile. B only if replicas in the write path are
wanted. With Frans's later thought, a special call instead of a sync level,
A now and C1 later fit without a gap: STRONG goes with A, and C1 brings the
call.


For release 2026.1
------------------

Asked, before release 2026.1 (008), what the release should do with it
(remove it, A; pull it from the Pub API only; complete it, B; or keep it,
documented as experimental), Frans, 2026-10-25: "Keep it, document as
experimental". No code change. Done the same day, by Claude (Opus 5.5,
Claude Code): the Javadoc of `DatabaseBuilder.replica` and
`Database.addReplica` says that replication is experimental, not for data
that matters, and lists the faults that a user meets (P1 to P3, P6, P8 to
P10); `removeReplica`, `getStorageInfos` and `SyncLevel.STRONG` point
there; README.md and docs/levels.md say so. The decision on the design
below stays open.


Next
----

Frans thinks it over, and it is discussed ("Durability and the API" has
the questions). His decision is recorded here; carrying it out is a
following entry, as this one's definition says.


Frans's decision
----------------

2026-11-04. Frans: "A with C2 now". Replication is removed from BergDB
(option A), and copies are left to the OS and the file system (option C2).
Carried out the same day, in this entry rather than in a following one, by
Claude (Opus 5.5, Claude Code), on `19e9409`; release 2026.2
(`release-2026.2`, `95bde62`) still has replication.

* **Removed from `java/`.** The Pub API's `DatabaseBuilder.replica`,
  `Database.addReplica`, `removeReplica`, `getStorageInfos` and
  `SyncLevel.STRONG`, with their implementations; `BadReplicaException` and
  `StorageInfo` in `pub.util`; `Db.addReplica`, `removeReplica`,
  `getStorageInfos` and the startup's `syncStreams`;
  `DbHelper.checkReplicaId` and `AddReplicaClass`; in `StorageManager`, the
  replicas, the startup's copying (`checkStreamIds`, `syncMainStream`,
  `syncReplicaStreams`), `addReplica`, `syncReplica`, `removeReplica`,
  `getStorageInfo(s)`, `setD2`, `syncStrong`, and the classes `Internal`,
  `MyStorage`, `SynchingStorage` and `ErrorStorage` (1,296 lines to 446);
  the rules `DurabilityRule`,
  `ErrorRule`, `MainConfirmedRule`, `OneActiveReplicaRule` and `MainErrorRule`.
  `StorageManager` now holds one stream, the main, with rule D1 (its
  confirmed length) and its error; `start()` takes the place of the
  startup's copying. `DbBuilder` holds one stream: a `stream()` of another
  name than the stream set, until now a replica, throws an
  `IllegalStateException` (`DbTester.testSecondStreamRefused`).
  `PayDemo`'s `addReplica` (Frans's demo, `src-dev/frans/`) is removed, as
  the build compiles it. About 2,000 lines in all.
* **The tests removed**, 17: in `StorageManagerTester`, `testSync1` to
  `testSync4`, `testAddReplica1` to `testAddReplica5`,
  `testAddReplicaWhileAppending`, `testRemoveReplica1` and
  `testRemoveReplica2`; `DbTester.testBadReplica1`;
  `PubTester.testBadStartReplica`, `testReplicaBeforeDir` (005-66) and
  `testRefusedStartClosesOnlyItsOwn` (015-56, whose second directory was a
  replica's; `testSecondStartOfOneBuilder` keeps 015-56's regression);
  `DbTesterFailure.testFailedStartOfTwoHistories` (005-32). Changed:
  `testMultipleClose` and `testSyncStartsTheFlush` without their replica,
  and `PubInterruptTester` without the join of `addReplica`'s job
  (`testDirByInterruptedThread`). `doubles.py` lost its allowance for the
  copy's progress percentage.
* **`SyncLevel.STRONG` goes.** "Proposal" says so: with Frans's thought of
  a special call instead of a sync level, "STRONG goes with A, and C1 brings
  the call". Kept as the same as ORDINARY, it would be a level that names a
  copy elsewhere and waits for none, the silent fallback that P6 found; and a
  future design may want the wait as a call of its own, not as this level
  (017-03). `SyncLevel` keeps NONE and ORDINARY; its about 130 uses of STRONG,
  nearly all in tests and stress programs that ran without a replica, so
  already ORDINARY syncs, are ORDINARY. `RestartStress` still draws the
  random choice it used for it, so that its seeds run as before.
* **The stream is unchanged.** Nothing in the stream records replicas: the
  meta block holds the magic bytes, the version, the time, the last
  transaction's position, the database ID, the startup distance and the
  node size, and the records hold transactions. A replica was a stream of
  its own, linked to the main only by the database ID in its meta blocks,
  which the startup and `addReplica` compared. So a database without
  replicas writes the same bytes as before (the C clone's cross tests,
  012). An old database that had replicas: its directory starts as before,
  alone, and nothing copies between streams at startup. A replica's
  directory is a database of its own, with the same database ID, a copy of
  the main up to where it was last written (with the faults of P2 and P9
  possible), which nothing writes any more. Bytes that only a replica held,
  past the main's end after a crash, are no longer copied onto the main;
  no sync promised them, as D2 was never above D1. An application that
  calls the removed methods or `STRONG` no longer compiles.
* **Lean.** `lean/` has nothing on replicas (its "replicate" is
  `List.replicate`); the model has one stream. Unchanged.
* **C2.** No code. docs/levels.md, section 9, and README.md say what is
  true now. C2's test, that a copy of the files made while the database
  writes starts as the database, is not made.
* **Checked.** `java/before-commit.sh`: BEFORE COMMIT OK, unit tests
  1,127 and f-tests 79 (before, on the same commit: 1,143 and 79; 17 tests
  removed, 1 added). `java/stress/core-build.sh`: CORE BUILD OK. The level
  scripts were not run: for a database without replicas the removal
  changes none of the levels' mechanisms (the main stream's append, sync,
  cut and recovery are as before), and no level check had a replica.
* **The design for later.** The removed design, in full, with Frans's
  question and the options B, C1 and C3 for a future replication:
  [017-03](../017-long-term/03-replication/readme.md).
* This entry's probes (`11-replication/tools/`) compile against `19e9409`
  or earlier, not against today's `java/`. The leak of "Found on the way"
  below (a replica being copied in at a close) went with the code.


Found on the way
----------------

Outside replication, now entries of their own (2026-10-23, at Frans's
request):

* [005-27](27-fix-meta-block-edge.md): a crash that ends the stream
  exactly at a meta block's position, after a transaction that ends there,
  leaves a database that does not start (P11; 13 of 13 such images). The
  main stream's recovery, Levels 2 and 3.
* [005-28](28-fix-trans-iterator-loop.md): startup loops for ever when the
  transaction at its start position is a failed one; P9's mixed stream hung
  the database so.
* [005-29](29-fix-memory-stream-assert.md): `MemoryStream.copy` fails an
  assertion when the stream is empty or its length a multiple of 1,000,000
  bytes (test code; P2 met it).

A leak, found by 005-67's probe (2026-10-29, noted as Frans decided on
006-10's point 7: "as recommended"; to be fixed with this entry's
decision): if the manager is closed while a replica is still being copied
in (`addReplica`), the replica's stream is never closed. Its slot in the
manager's array of streams is null until `makeActive`, as in P3, so
`close()` does not close the replica's `BufferedStream`: its thread stays
alive, and since 005-63 its directory stays locked (`bergdb.lock`), until
the JVM ends; another start on that directory in the same JVM gets a
`DirectoryInUseException`. With `close()` after the copy, both threads end
and the directory is free
([005-67](67-fix-test-add-replica2.md), "Found on the way, for 005-11";
`67-fix-test-add-replica2/probe/CloseDuringSync67.java`,
`67-fix-test-add-replica2/runs/close-during-sync.txt`).


Done when
---------

The report is written (done, 2026-10-22: what the code does, what the
tests cover, what the probes showed, the options with their cost and
value). Then Frans's decision is recorded here; carrying it out is a
following entry.


Size and order
--------------

M: reading and probes, some machine time. Independent of the other
entries; before 005-05's decision on publishing, as the API offers it.


Files
-----

* [11-replication/report.md](11-replication/report.md): the study.
* [11-replication/tools/](11-replication/tools/): `ReplicaProbe.java`, the
  probes P1 to P11; `run.sh` runs one, `all.sh` all but P8, `p2-all.sh` P2's
  six runs.
* [11-replication/runs/](11-replication/runs/): their outputs on
  `cbeb9bd`, and the existing tests' run; in
  [runs/78cc5f3/](11-replication/runs/78cc5f3/), the same run again on
  `78cc5f3`, after 005-01 (all but P8).
* [017-03](../017-long-term/03-replication/readme.md): the removed design,
  Frans's question and the options for a future replication.
