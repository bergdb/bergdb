005-30. Fix: a read that fails on the storage fails the database
================================================================

Status: open. Kind: fix. Created 2026-10-23.

From 005-01's follow-up, 2026-10-23, by Claude (Opus 5.5, Claude Code),
at Frans's request ("Write it up in a new entry. I like your proposal.").
Frans, before: "Perhaps the safest approach is to make it fail the whole
database. If we detect this actually happening when it should not, we
could redesign."


The issue
---------

Since 005-01 a transaction that throws after its go point fails the
database (`DbState.FAILED`): every later transaction and read is refused
with a `DbFailedException` until a restart. A read that fails on the
storage does not: `getOne`, `getMany`, `getTrans`, the warm-up of a
transaction and `sync()` throw a `StreamIoException` or a
`StreamFormatException`, and the database stays `ACTIVE`.

The storage below has stopped already. A real I/O error is remembered by
`FileStream` (its `ioException`, `checkIOException`), which then refuses
every read and append, and by `StorageManager` (`handleStreamException`
closes the main stream, and `hasError` refuses all later I/O). So after
the first one the database is half dead: reads of nodes in memory still
answer, reads that need the stream fail, and writes fail until one gets
past its go point and fails the database in `store()`. The application
gets answers for some keys and errors for others, with no clear signal
that the database is gone.

A read that fails changes nothing in memory (a load that fails registers
nothing), so this is not a correctness fault as M49 was. It is Frans's
rule from 005-01: if the storage, the JVM or memory fails, the database
cannot function and is restarted.


When a read fails
-----------------

Not faults, and they must stay as they are:

* A read during or after `stop()` or `close()`: `StorageManager.closeInner`
  sets the error "Storage is closing.", so reads still running get an
  `IOException`. The background threads of the index jobs expect it
  (`IndexBuilderImp.createInThread`, `DatabaseImp`).
* A read that a cut has overtaken: `ReadBelowFirstPosException`, which
  `Db.expiredIfReadBelowCut` turns into a `LookupTimeNotAvailableException`
  (docs/levels.md, W1).

Faults, rare on a healthy local disk, which fits that Frans has never seen
one:

* A write failure seen by a later read: a failed flush (a full disk, a
  write error) fails the `BufferedStream`, and reads get "Cannot read from
  the failed stream".
* The device or the files: read errors of a failing disk; a volume that
  goes away (an external drive unplugged, a network share dropped); files
  deleted, truncated or made unreadable by another program (a cleanup
  script, a sync tool such as iCloud evicting files); on Windows, files
  locked by antivirus or backup programs.
* A bug or a lost write: "No file found for reading", or an `EOFException`
  when a file is shorter than expected (005-24).
* Corrupt data: a checksum or format error (`StreamChecksumException`,
  `StreamFormatException`); the storage itself stays healthy.

`FileStream` reads with `RandomAccessFile`, not `FileChannel`, so an
interrupted reader thread cannot close the files for every thread (as
`ClosedByInterruptException` does with NIO).


The fix, proposed
-----------------

A read that fails on the storage fails the database, as a transaction
does after its go point:

* Where: the read paths of `Db`. `getOneInternal`, which `getOne` and the
  warm-up use; `getMany`; `getTrans` (the Pub API's `transactionInfo()`);
  and `sync()`, whose failure is the same failure of the storage. The
  writer's loads in a transaction are covered by 005-01 already; reclaim's
  reads go through `getOne` and `getMany`.
* What: a `StreamIoException` or a `StreamFormatException` (with
  `StreamChecksumException`) sets `FAILED`, keeps the first failure, and
  the call throws a `DbFailedException` with it as the cause. The two
  exceptions above stay: a read below the cut whose time has expired is
  still a `LookupTimeNotAvailableException`, and while the database is
  stopping the exception is thrown as it is, as in `Db.fail()`.
* Corrupt data fails the database too, as proposed and liked by Frans: it
  means lost data or a bug, and a database that serves around the damage
  is worse than one that stops. The cost: after a restart, the next read
  of that node fails the database again, until the stream is repaired or
  restored.
* The state's change: today `Db.fail()` runs under the write lock only; a
  reader fails the database without it. Make the change from `ACTIVE` to
  `FAILED` one step under a lock both use (`readSync` will do: readers
  take it at the start of every read already), so that the first failure
  is the one kept. A transaction that runs at the time ends as it would
  anyway: committed or failed, as after a crash at that point.
* A gap of 005-01 to close on the way: `getTrans` does not check the
  state, so `Connection.transactionInfo()` still reads after a failure.
* `InternalDataException` is not part of it: it comes from parsing
  internal data above `Db` (the Pub API's index data, `Data`), or from
  reclaim's table in the writer, where 005-01 fails the database already.


Performance
-----------

No change expected. On the path of a read that does not fail, nothing is
added: `getOne` and `getMany` already check the state (a plain field) and
already catch `StreamIoException`; catching more classes costs nothing when
nothing is thrown, and the lock is taken only after a failure. `getTrans`
gets the state check, one field read, beside a read of the stream. The
streams do not change: the write path is not touched. As this is the read
path, the hottest one, check it with Props in ABBA order (`java/props.sh`,
CORE's `get` and `get4t`), run in the background with the session idle.


Done when
---------

* Unit tests: a `getOne`, and a `getMany`, that meets a read error fail the
  database, and every later transaction and read is refused with that
  cause; the same with a corrupt node; a warm-up's read error fails it; a
  sync that fails fails it; a read below the cut that has expired is
  still a `LookupTimeNotAvailableException` and the database goes on
  (`ReclaimReaderTester` covers it today); a read during `stop()` does not
  fail the database; `transactionInfo()` is refused after a failure. 005-01's
  `FaultStream` (`DbTesterFailure`) can make the errors.
* The tests that meet a storage failure today still pass, or are changed on
  purpose: `DbTester.testSyncAfterStreamFailure`,
  `DbTesterStream.testReadOnlyStream2`, `ReclaimReaderTester`,
  `EvictionReaderTester`.
* `java/before-commit.sh` prints `BEFORE COMMIT OK`; StreamDigest
  identical; Props ABBA as above; `level3.sh` and `level4.sh`, as readers
  and cuts meet there.
* Docs: `DbFailedException`, `DbException` (a stream error in a read then
  fails the database), `Database` and `Connection` in the Pub API, and
  docs/levels.md ("A transaction that fails", which becomes about reads
  too).


First step
----------

List every read path of `Db` and what it catches today, and every test
that expects a read to fail and the database to go on after it.


Size and order
--------------

S: about 40 lines in `Db`; the tests are most of it. Any time; best not
while a timing campaign runs, as it touches the read path.
