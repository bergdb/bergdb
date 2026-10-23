005-33. Decide: a database whose creation crashed
================================================

Status: open; studied, for Frans to decide. Kind: decide. Created
2026-10-23.

Found on 2026-10-23 in 005-28, by Claude (Opus 5.5, Claude Code). Frans:
"I don't know what to do with this. Make a new 005 entry for this. Study
the options and propose something in the entry. Do not implement
anything." The probe is in [33-crashed-creation/](33-crashed-creation/).
No change to `java/`.


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


Done when
---------

Frans's decision is recorded here; carrying it out is this entry's or a
following one's work, as he says.


Size and order
--------------

The study is done (2026-10-23). A is S, A with B2 S to M, C M. After
005-32 for A and B2; independent of 005-11, but B2 waits for its decision
for replicas.
