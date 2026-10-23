005-30. Fix: a read that fails on the storage fails the database
================================================================

Status: done (2026-10-23; see Outcome). Kind: fix. Created 2026-10-23.

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


Outcome
-------

2026-10-23, by Claude (Opus 5.5, Claude Code), at Frans's request ("Fix
bergdb 005-30. As proposed. Commit when done."): as proposed, with the
details below that the work found. The evidence is in
[30-fix-read-failure/](30-fix-read-failure/).

**The first step.** The read paths of `Db`, before the change and now:

| Read | Before | Now |
|---|---|---|
| `getOne`, through `getOneInternal` | the state checked; a `StreamIoException` below the cut whose time has expired became a `LookupTimeNotAvailableException`, any other was thrown as it is, and so was a `StreamFormatException` | a `StreamException` (`StreamIoException`, `StreamFormatException`): expired as before, or it fails the database |
| the warm-up of a transaction, through `getOneInternal` | as `getOne` (`execute` checks the state) | as `getOne` |
| `getMany` | as `getOne` | as `getOne` |
| `getTrans` (`transactionInfo()`) | no state check; all thrown as it is | the state checked; an I/O error fails the database; below the cut, a `LookupTimeNotAvailableException`; a format error thrown as it is (below) |
| `sync()` | an `IOException` of the storage became a `StreamIoException` | a failure of the storage fails the database; an interrupt is a `StreamIoException`, as before |
| the writer's loads, reclaim's reads | after a go point: they fail the database (005-01) | the same; a read through `getOne` or `getMany` fails it first, and its `DbFailedException` passes `fail()` as it is |

The tests that expected a read or a sync to fail with the database going
on: `DbTester.testSyncAfterStreamFailure`,
`DbTesterStream.testReadOnlyStream2` and
`DbTesterFailure.testAppendErrorInStore` (a sync after a failed flush threw
a `StreamIoException`; changed on purpose, below). `ReclaimReaderTester`
(expiry, and the database goes on), `EvictionReaderTester` (no failures),
and the stress tests `ReclaimReaders` and `Soak` (the model or an expiry)
pass unchanged. The background threads of the index jobs
(`IndexBuilderImp.createInThread`, `DatabaseImp.deleteIndexInternal`)
already end on a `DbFailedException`, and on the `StreamIoException` of a
read while the database stops.

**The change**, in `java/src/bergdb/`:

* `core/Db.java`. `getOneInternal` and `getMany` catch `StreamException`,
  the base of `StreamIoException` and `StreamFormatException` (with
  `StreamChecksumException`), and `readFailed()` decides: a read that a cut
  has overtaken expires (`expiredIfReadBelowCut()`, as before), anything
  else goes to `failOnStorage()`. That sets `FAILED` with the first failure
  (`setFailed()`) and returns a `DbFailedException` with the exception as
  the cause; while the database is stopping, or before it has started, the
  exception as it is. `setFailed()` makes the change from `ACTIVE` to
  `FAILED` one step under `readSync`, and `fail()` (005-01) uses it too.
  `getTrans` checks the state. `sync()` fails the database when the storage
  has failed. `assertDbStateIsActive`'s refusal no longer says "in a
  transaction". The Javadoc of `getOne`, `getMany`, `getTrans`, `sync`,
  `start`, `execute` and of the failure's fields and methods.
* `storage/StorageManager.java`: a sync whose thread is interrupted throws
  an `InterruptedIOException` (it was an `IOException`), so that `Db.sync`
  can tell it from a failure of the storage.
* Javadoc: `core/DbState.java`, `pub/util/DbFailedException.java`,
  `pub/util/DbException.java`, the Pub API's `Database` (the rule, and
  `sync`) and `Connection` (`exists`, `get`, `transactionInfo`, `sync`).
* docs/levels.md: the section "A transaction that fails" is now "A
  transaction or a read that fails", with the reads; and W1's note.
  docs/level4-alignment.md, row M49: the section's name.

**The details that the work found:**

* `getTrans`: a format error is thrown as it is, and the database goes on,
  unlike the other reads. Its position is the caller's, and the Pub API's
  is wrong for a value after a meta block in its record: a fault of its
  own, found here, now [005-34](34-fix-transaction-info-position.md).
  `transactionInfo()` then reads the middle of a record. With the format
  errors failing the database, as proposed, a call for about one value in
  40, with records of 10 KB, could have failed it for a fault that is not
  the storage's. An I/O error in `getTrans` fails the database as for the
  other reads. On the code before, one such call that read past the end
  had left the database half dead (005-34's probe).
* `getTrans` of a transaction that reclaim has removed (a read below the
  first position) throws a `LookupTimeNotAvailableException`, as a read
  that a cut has overtaken; it was a `StreamIoException`. Such a
  transaction is older than the first available lookup time, so the time of
  the get has expired.
* `sync()`: `StorageManager` throws an `IOException` when the storage has
  failed or is closing, and also when the waiting thread is interrupted. An
  interrupt is not a failure of the storage, so it now throws an
  `InterruptedIOException`, and `Db.sync` throws it as a
  `StreamIoException`, as before.
* `stop()` and `close()` set `STOPPING` under `readSync` too (they wrote
  the state without it), so that a failure cannot overwrite `STOPPING`
  after a stop: `DbState` allows `ACTIVE -> FAILED -> STOPPING` only.
* `start()`: its last step reads reclaim's table with `getOne`, after the
  state is `ACTIVE`; a failure there now fails the database, and `start()`
  throws a `DbFailedException` with the failure as the cause.

**Tests**, in `core/DbTesterFailure` (ten new, all unit tests but one; the
whole class takes about 0.6 s):

* `testReadErrorInGetOne`, `testReadErrorInGetMany`,
  `testCorruptNodeInGetOne`, `testCorruptNodeInGetMany`: a get, and a scan,
  that loads an index node that eviction has released (005-01's setup:
  node size 8, a startup distance of 1,000 bytes, every evictable object
  evicted after every transaction, 2,000 keys) meets a read error of
  `FaultStream` (the storage then fails), or a corrupt node (a checksum
  error; the storage stays healthy). The read throws a `DbFailedException`
  with the read's exception as the cause; every later transaction, get,
  scan and `getTrans` is refused with that cause; nothing more is
  appended; a restart, with the audit on, gives every key and takes a
  transaction.
* `testReadErrorInWarmup`: the same in a transaction's warm-up, before its
  go point; the lookup time stays.
* `testSyncFails`, an f-test (a sync after a failed flush waits for
  StorageManager's 500 ms poll): the sync throws a `DbFailedException` with
  the `StreamIoException` as the cause, and the database refuses the rest.
* `testInterruptedSync`: a sync that waits (`FaultStream` holds the flush)
  and is interrupted throws a `StreamIoException` with an
  `InterruptedIOException` as the cause, and the database goes on.
* `testReadDuringStop`: a scan that stops the database after its first KV
  and then loads a node gets the `StreamIoException` of the closing
  storage, as before, and the database is stopping, not failed.
* `testGetTrans`: a format error (a corrupt read) is thrown as it is and
  the database goes on; a read error fails it; then `getTrans` is refused.
* `testGetTransBelowTheCut`: `getTrans` of a transaction below a cut (a
  `CutStream` cut directly) throws a `LookupTimeNotAvailableException`, and
  the database goes on.
* Changed on purpose: `testAppendErrorInStore` waits for the failed flush
  (the storage's status) instead of syncing, as the sync would now fail the
  database first; it became a unit test. `assertRefused` also checks
  `getTrans`. `DbTester.testSyncAfterStreamFailure` and
  `DbTesterStream.testReadOnlyStream2`: the sync throws a
  `DbFailedException` with the `StreamIoException` as the cause, and the
  next transaction is refused with it (it failed in `store()` before).

Each part of the change has a test that fails without it
([mutations.txt](30-fix-read-failure/mutations.txt), made with
[mutations.sh](30-fix-read-failure/mutations.sh) and
[mutate.py](30-fix-read-failure/mutate.py)): A, reads as before: the four
read tests and the warm-up's; B, no state check in `getTrans`: every test
with `assertRefused`; C, a sync as before: `testSyncFails`,
`testSyncAfterStreamFailure`, `testReadOnlyStream2`; D, an interrupt as a
failure: `testInterruptedSync`; E, no exception for a stopping database:
`testReadDuringStop`; F and G, `getTrans` failing the database on a format
error and below the cut: `testGetTrans`, `testGetTransBelowTheCut`. The
order of the state's change under `readSync` (a race) has no test.

**Evidence.**

* StreamDigest `all` against the build before the change, on `ad09b2e`:
  `DIGESTS IDENTICAL (36 of 36)`, as on `948ec00` and `f6bc3ce` before
  ([digest-compare.txt](30-fix-read-failure/digest-compare.txt)). No record
  changes.
* `before-commit.sh`: BEFORE COMMIT OK (987 unit tests, 63 f-tests) on
  `948ec00` with the fix, and BEFORE COMMIT OK (990 unit tests, 63
  f-tests) on `ad09b2e` with it, the commit it is on.
* `level3.sh` and `level4.sh`, full, one after the other, with `nice`, on
  `948ec00` with the fix ([gates.txt](30-fix-read-failure/gates.txt)):
  `LEVEL 3 OK` (533 s; 25 of 25 traces with cuts `TRACECHECK OK`,
  `POWERLOSS OK`) and `LEVEL 4 OK` (874 s; 33 of 33 traces, C-P on 7,917
  transactions). In their `ReclaimReaders` steps, 6 and 442 reads that a
  cut overtook expired (with forced eviction schedules in `level4.sh`, many
  more loads come from the stream), and none failed the database: 0
  failures, the writer went on.
* Props in ABBA order, four runs each, on `ad09b2e` without and with the
  fix, in a quiet window ([props-ab.txt](30-fix-read-failure/props-ab.txt)):
  CORE 0.28 to 0.29 for both, `get` 0.24 to 0.26 and `get4t` 0.32 to 0.33
  without, 0.24 to 0.26 and 0.32 with it; MEM 191 to 192 and SS 1.50 for
  both. No change, as expected: nothing is added on the path of a get or
  a scan that does not fail.

**Done when**, point by point:

* The unit tests: above; the read below the cut whose time has expired is
  `ReclaimReaderTester`'s, which passes unchanged (and `getTrans`'s case,
  `testGetTransBelowTheCut`); `transactionInfo()` is refused after a
  failure: `Db.getTrans`, which it calls, in `assertRefused`.
* The tests that met a storage failure: changed on purpose or passing, as
  above.
* `before-commit.sh`, StreamDigest, Props, `level3.sh` and `level4.sh`:
  above.
* Docs: `DbFailedException`, `DbException`, `Database`, `Connection`, and
  docs/levels.md, "A transaction or a read that fails". Also docs/log.md.
