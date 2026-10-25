005-33. Decide: a database whose creation crashed
================================================

Status: done (2026-10-25). Frans decided A, one clear error, on
2026-10-25, and it is implemented ("Frans, 2026-10-25" and "Outcome"
below). Kind: decide. Created 2026-10-23.

Found on 2026-10-23 in 005-28, by Claude (Opus 5.5, Claude Code). Frans:
"I don't know what to do with this. Make a new 005 entry for this. Study
the options and propose something in the entry. Do not implement
anything." The probe is in [33-crashed-creation/](33-crashed-creation/).
No change to `java/` for the study.


The question
------------

A crash while a database is created can leave its stream with part of
the first meta block, the whole meta block, or the meta block and part of
the first transaction (the primordial one): with no committed
transaction. Such a database never starts: every start throws, until
someone removes its files. Should a start create it again, as it does for
an empty stream? Should the creation be made so that a crash cannot leave
it half done? Or should it stay an error, a clearer one?

Frans's design, 2012-08-20 (the f1 repository's F1-007,
`a/007-bergdb-261012/bergdb/doc/log-old/2012-log.txt`): "I decided that a
DB stream is only valid after primordial transaction has run, before that
it is not recoverable. This simplifies programming. We differentiate
between creating a database (creating stream, writing a metablock and
primordial transaction), and the startup of an existing one. A database
cannot be recovered (started) unless the primordial transaction ran
successfully." The code follows it. What it leaves open is what a start
does with a stream that is not valid in this sense: today it fails, with
one of three messages.


What a crash in the creation leaves
-----------------------------------

`CreationCrashProbe`, on `e2c0dc0`, Java 27
([runs/](33-crashed-creation/runs/)).

A creation writes 264 bytes to the stream: the first meta block (128
bytes, with the database's ID; it names no transaction) and the
primordial transaction (136 bytes: the super root and the first key
node). The same with and without a crypto key. The Pub API also writes
`created.txt` beside the stream's file, at once and on its own.

A start on the stream cut at each length L (`cuts`: the core API, every L
from 0 to 264; `pub`: the Pub API in a directory, with and without a key,
at L = 0, 1, 64, 127, 128, 129, 132, 133, 200, 263 and 264, with the same
outcomes):

| L | The start | The stream after it |
|---|---|---|
| 0, or no stream file | creates the database | a new database |
| 1 to 127 | `StreamFormatException`: "Cannot recover stream without complete first meta block, length: L" | unchanged |
| 128 | `StreamFormatException`: "No transactions in startup transaction set." | unchanged |
| 129 to 263 | `StreamFormatException`: "Transaction at start pos 128 is not committed (its last byte is 0)." (until 005-28, the start hung) | 264 bytes: recovery has zero-filled the transaction |
| 264 | starts | |
| 128 or 264 zero bytes | `BadCryptoKey`: "Likely, the wrong crypto key was used. Invalid magic bytes in stream.", also without a key | unchanged |

None of the messages says what happened or what to do. The last row is
what a file system would leave if a power loss kept a file's new length
but not its bytes; its message names a key also when none is used.

How the creation reaches the disk (`flushes`, `kill`):

* 500 creations through the Pub API (its buffer: 10 MB, 20 ms): each
  time, the creation's 264 bytes reached the stream in one append, 1.6 to
  36 ms after `start()` returned (median 27). `FileStream` writes each
  append and forces it to the disk.
* 300 JVMs killed (`SIGKILL`) at random moments, 0 to 400 ms after they
  began to create a database through the Pub API: 29 left no stream file
  (killed 0 to 42 ms after), 28 an empty one (37 to 160 ms), and 243 the
  whole creation (80 to 400 ms); none a part of it. Each next start
  created the database or started it.

So a crash of the process does not leave a half-done creation: the
creation is one write, before which the stream is empty. What leaves one
is a power loss, or a crash of the operating system, during the first
write and force of a new database's file, or damage to that file; this
machine cannot test those. The window is short, but it is there on a
device that loses power and creates its database at its first start. No
data is lost, as nothing was committed; the cost is a database that does
not start until someone removes its files.


How LevelDB does it
-------------------

LevelDB writes the file that makes a directory a database last.
`DBImpl::NewDB` writes and syncs the first manifest; then `SetCurrentFile`
writes the file `CURRENT` under a temporary name, syncs it and renames it.
At open, a directory without `CURRENT` is no database, and with
`create_if_missing` it is created
([db_impl.cc](https://github.com/google/leveldb/blob/main/db/db_impl.cc),
`DBImpl::Recover` and `NewDB`;
[filename.cc](https://github.com/google/leveldb/blob/main/db/filename.cc),
`SetCurrentFile`). A crash in the creation thus leaves no database, and
the next open creates it.


The options
-----------

All keep the 2012 rule: a stream without a committed primordial
transaction is not a database. They differ in what a start does with
one, or in whether one can come about.

**A. One clear error.** The start recognizes a stream that holds no
committed transaction and throws one exception for it, which says what
happened and what to do; the files stay as they are. The application, or
a person, removes them and starts again.

* What it takes. A check in `Db.startInner`, after `syncStreams()` (a
  replica with the whole creation is copied to the main first, as today)
  and before recovery: the stream holds BergDB's magic as far as it goes,
  and either ends inside or right after the first meta block, or its
  transaction at 128 is cut or failed and nothing follows it. Then a new
  exception, say `DatabaseNotCreatedException extends
  StreamFormatException`, with a message such as "The database was not
  completely created (a crash while it was created?); it holds no data.
  Remove its files and start it again." Recovery appends nothing then (it
  zero-fills today). On the way: without a key, a first meta block whose
  magic is wrong is not called a wrong key. The remedy in the Javadoc of
  `DatabaseBuilder.start()`. Tests: every cut of a creation gives the
  exception and leaves the files as they were. 005-32 first, so that the
  files are closed when the exception arrives (on Windows they cannot be
  removed while open). Size S.
* For the API: one new exception, for the application to catch.
* Gives: the database never removes anything on its own, and the 2012 rule
  stays as it is, with a message that says what to do. Costs: every
  application must handle it, or a device that lost power while it created
  its database fails at every start until someone removes its files.

**B. Create it again at start.** A stream that A's check finds is not a
database yet: the start removes its bytes and creates the database, as in
an empty directory.

* What it takes. A's check and exception, and one of:
  * B1, in the core: a new stream operation that empties a stream, for
    `FileStream` (remove its files, force the directory), `MemoryStream`,
    `SalsaStream`, `BufferedStream` and `StorageManager`; `ReadOnlyStream`
    refuses it, and a read-only database gets A's error. Then
    `handleEmptyStream()` as today. Size M: an interface change in about
    eight classes.
  * B2, in the Pub API: `DatabaseBuilderImp.start()` catches A's exception,
    removes the stream's files (`*.bergdb`) and `created.txt` from the
    directory (005-32 has closed them), opens the directory again and
    starts a new `Db`, which creates the database. With replicas (until
    005-11 decides), A's error instead. The core API keeps A's error. Size
    S, after A.

  Tests: a start creates a working database after every cut of a creation
  from 1 to 263 bytes; a stream with a committed transaction is never
  removed (the cut at 264, longer streams, a failed first transaction with
  a committed one after it).
* For the API: none. `start()` creates the database as in an empty
  directory, with a new ID (or the builder's) and a new `created.txt`.
* Gives: a crash in the creation acts as a crash before it, as in
  LevelDB; no code in the application, no manual step. A's check finds
  only streams without a committed transaction, so nothing that holds data
  is removed. Costs: the database removes a stream's bytes on its own,
  which it does nowhere else (reclaim's cuts aside); B1 changes the stream
  interface. A stream of zero bytes stays an error: with a key, it cannot
  be told from a wrong key (a new, empty database opened with a wrong key
  would be removed); without a key, it could be taken as not created
  too.

**C. Create it whole or not at all.** A new database's stream reaches its
directory only complete. The Pub API creates it under a temporary name
(the first file, or the whole database in a subdirectory), forces it and
renames it into place, then forces the directory. A crash before the
rename leaves no stream, and the next start creates the database (a
left-over temporary file is removed); after it, a whole one. As LevelDB's
`CURRENT`.

* What it takes. In `FileStream` or the Pub API: the creation written and
  forced under a temporary name, the rename, a force of the directory
  (`FileStream` forces directories already, when it creates and removes
  files), the removal of a left-over. Tests: a kill at every moment of a
  creation, and a `FileStreamIo` that fails between the write, the force
  and the rename, as `FileStreamPowerLossTester` does. The core API with
  other streams keeps A's error, or today's. Size M.
* For the API: none.
* Gives: a half-done creation cannot come about, nothing is removed at a
  start, and no stream's beginning needs to be judged. Costs: the most
  code; one more protocol of renames and forces per platform to get
  right; `FileStream` only.

**D. No change.** Today's three errors, and the zeros' `BadCryptoKey`.
Size 0. Costs: as A, with messages that do not say what happened.


Proposal
--------

Claude, 2026-10-23: A, then B2, after 005-32.

* A gives the core one clear error for a database whose creation did not
  finish, in place of three that do not say what happened, and keeps the
  2012 rule as it is: such a stream cannot be started.
* B2 lets the Pub API, which owns the directory, treat such a database as
  no database, as LevelDB treats a directory without `CURRENT`, and create
  it. An application never sees it, and no one has to remove files on a
  device in the field. Nothing that holds data is removed: A's check
  matches only streams without a committed transaction.
* B1 is not needed for the Pub API, and changes the stream interface for
  the core's own users, which are tests and tools. C prevents what B2
  repairs, at more cost and for `FileStream` only; worth it only if Frans
  wants the database never to remove a stream's bytes.

If Frans prefers that the database never removes anything on its own: A
alone, with the remedy in `DatabaseBuilder.start()`'s Javadoc.


Questions for Frans
-------------------

1. A, B (B1 or B2), C or D?
2. With B: should the application learn that a creation was done again
   (`StartupInfo`, a log line)? It would have seen an empty directory
   otherwise, so it may not matter.
3. With B and no key: should a stream of only zero bytes, no longer than a
   creation, count as not created too?


Frans, 2026-10-24
-----------------

"Let's wait with implementation. I like the proposals. Just one thing.
BergDB must work with truly append-only storage, I guess we are making
exceptions if we delete the stream. It may or may not be ok."

B1 and B2 remove a stream's bytes; A and D leave the stream as it is; C
needs a rename at the creation, which truly append-only storage may not
offer either. To study when this is taken up: whether such a stream can
be repaired by appending only, with the rest of the first meta block, a
new primordial transaction after the failed one, and a startup that steps
over failed transactions before the first committed one.


Frans, 2026-10-25
-----------------

"bergdb 005-33. Decision: A. Note the decision in the readme. Implement
it. Then commit if successful."

So option A, one clear error: the database never removes a stream's bytes
and writes nothing to such a stream, which also suits truly append-only
storage (his note of 2026-10-24). B and C are not done. Questions 2 and 3
were for B; with A they fall away. The repair by appending only, above,
is not needed for A.


Done when
---------

Frans's decision is recorded here; carrying it out is this entry's or a
following one's work, as he says.


Size and order
--------------

The study is done (2026-10-23). A is S, A with B2 S to M, C M. After
005-32 for A and B2; independent of 005-11, but B2 waits for its decision
for replicas.


Outcome
-------

2026-10-25, by Claude (Opus 5.5, Claude Code), option A as Frans decided.

* The check. `Db.startInner` calls `refuseIncompleteCreation()` after
  `syncStreams()` and `handleEmptyStream()`, before recovery. It asks
  `RecoverableStream.isIncompleteCreation()`, through `NodeStream`, which
  only reads: the stream is not empty and no longer than a creation,
  `Db.CREATION_LENGTH`, 264 bytes (`writePrimordialTransaction()` asserts
  it); its bytes begin as a meta block of this version as far as they go,
  the magic bytes and the version (`MetaBlock.beginsAsBlock`), and a
  complete block is valid and names no transaction; and the transaction at
  128, if begun, is cut by the end of the stream, or failed (its last byte
  0) and ends the stream. The bound on the length makes it safe: a stream
  no longer than a creation holds no data, whatever the size field of its
  first transaction says. Without the bound, a damaged size field that
  claims more bytes than there are would make a longer stream, with data
  after it, look cut.
* The exception, `bergdb.pub.util.DatabaseNotCreatedException`, a
  `DbException`: "The database was not completely created (a crash or a
  power loss while it was created?): its stream, of length L, holds an
  incomplete creation, and no data. Remove its files and start it again;
  the start then creates it (bergdb 005-33)." It is in the Pub API's
  package, beside `BadCryptoKey`, as the application is to catch it; so it
  is not the `StreamFormatException` that option A's sketch named, since
  `bergdb.pub.util` depends on `bergdb.common` only (its package.html).
  The start writes nothing: recovery's zero fill does not run, and the
  failed start closes the files before the exception leaves (005-32). The
  remedy is in the Javadoc of `DatabaseBuilder.start()`, of `Db.start()`
  and of the exception.
* No key, no wrong key. Without a crypto key (the main stream is not a
  `SalsaStream`), a stream whose magic bytes are wrong still gives a
  `BadCryptoKey`, as the Pub API documents for an encrypted database
  started without its key, but its message no longer says that the wrong
  key was used: "Invalid magic bytes in stream, and no crypto key was used:
  likely, the database is encrypted and needs its key; else the stream is
  not a BergDB stream, or it is damaged." With a key, as before.
* Tests. New: `RecoverableStream.Tester.testIsIncompleteCreation`, every
  cut of a creation and the creation with its transaction failed, and what
  is not one (longer streams, also a first transaction whose size claims
  more than the stream has, zero bytes, another version, an invalid block,
  a block that names a transaction, a short first transaction with more
  bytes after it), each stream left as it was;
  `DbTester.testCrash8InCreation`, an f-test, as its 264 starts take about
  110 ms: every cut from 1 to 263 and the creation with its transaction
  failed give the exception, the stream unchanged byte for byte, and the
  whole creation starts; `PubTester.testCrashInCreation`, through the Pub
  API with and without a key: eight cuts, and a stream of zero bytes, whose
  message names a key only when one is used. Changed: 005-28's
  `NodeStreamTester.testCrashInPrimordialTrans` and 005-32's
  `PubTester.testFailedStartsDirectoryRemoved` expect the new exception
  and the stream as it was; 005-32's
  `DbTesterFailure.testFailedStartClosesStorage` needs a start that
  appends and then throws, and a cut creation is no longer zero-filled, so
  it now starts on a damaged stream, a failed first transaction with a cut
  one after it (recovery zero-fills the cut one, and startup throws at the
  failed one).
* The probe again, on the change ([runs/](33-crashed-creation/runs/)
  `after-cuts.txt`, `after-pub.txt`): every cut from 1 to 263 bytes, and
  the creation with its transaction failed, give the exception, and the
  stream is as it was; 0 and 264 start. Through the Pub API in
  directories, with and without a key, the same, and the files are as they
  were; streams of zero bytes give a `BadCryptoKey`, with the new message
  without a key. The probe now also starts on the creation with its
  transaction failed (on `ec44d19`, before the change: "Transaction at
  start pos 128 is not committed (its last byte is 0).",
  `cuts-ec44d19.txt`), and writes the length in the new message as L.
  `flushes` and `kill` were not run again: they measure the creation,
  which has not changed.
* Found on the way, for 005-11: with a replica, a main stream or a
  replica that ends inside its first meta block fails the start before the
  check, in `StorageManager.checkStreamIds`, with a `StreamIoException`
  ("Cannot read 128 bytes at position 0, stream size is 100."), as before;
  also when the other stream holds the whole creation, which
  `syncStreams()` would copy. "A replica with the whole creation is copied
  to the main first", above, holds only when both have their first meta
  block. The probe's new case `replicas`, the core API with one replica
  (`after-replicas.txt`): a main of 200 bytes and a replica of 264 start,
  as the copy makes the creation whole, and so do the reverse; both of 200
  give the exception.
* `java/before-commit.sh`: BEFORE COMMIT OK (1020 unit tests, 69
  f-tests). Also `java/stress/level2.sh quick`, as the change is in the
  start: LEVEL 2 OK.
