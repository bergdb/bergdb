005-32. Fix: a start that throws leaves its storage running
==========================================================

Status: done (2026-10-24). Kind: fix. Created 2026-10-23.

Found on 2026-10-23 in 005-28, by Claude (Opus 5.5, Claude Code). Added
at Frans's request ("Yes, make a new 005 entry."). The probe is in
[32-fix-failed-start-storage/](32-fix-failed-start-storage/).


The issue
---------

`Db`'s constructor creates the storage: a `StorageManager` with a
`BufferedStream` for each stream, each with a thread of its own and a
buffer (10 MB for the main stream by default), and the streams' files open
(`FileStream`). `Db.start` runs `startInner`; when that throws, nothing
stops the storage. The threads run on, the files stay open, and what the
start appended before it threw is written later by the left-over thread,
at its own time: recovery's zero fill, and the copies between the main
stream and its replicas (`StorageManager.syncStreams`). A caller of
`Db.start` holds the object and can call `stop()`; a caller of
`DbBuilder.start()` or of the Pub API's `DatabaseBuilder.start()` gets
only the exception.

A start throws for a stream that does not start (005-28; a creation that
crashed, 005-33), a wrong crypto key (`BadCryptoKey`), a replica of
another database (`BadReplicaException`), a read error, an
`OutOfMemoryError` in the startup's reruns, and for anything that throws
after `startInner` has set the state to `ACTIVE` (reclaim's `initFromDb`,
eviction, the audit). The Pub API has two more such places:
`DatabaseImp.createAndStart` leaves a database that runs when the index
manager's initialization throws after `db.start()`, and
`DatabaseBuilderImp.start` leaves the `FileStream` that `dir()` opened when
it throws before the `Db` is built (a key of an unknown algorithm).

The leak ends when the garbage collector finalizes the `Db` (`Db.finalize`
calls `stop()`), which the Pub API's `Database.stop()` relies on ("the
Database will be stopped automatically when garbage collected"). Java
deprecated finalization for removal in Java 18; with it disabled
(`--finalization=disabled`), the leak is for good.


What the probe found
--------------------

`FailedStartProbe`, on `a10ebf9`, Java 27
([runs/](32-fix-failed-start-storage/runs/)):

* Ten starts through the Pub API with a wrong key, then one with the
  right key: after the ten, 5 of their threads and 5 open files were left
  (collections during the starts had finalized the other five: each start
  allocates a buffer of 10 MB); the right key then started and read.
  After `System.gc()` and `System.runFinalization()`, none were left. With
  finalization disabled, all 10 threads and 10 files were left, also after
  the collection.
* Ten starts of a directory whose creation crashed (its stream cut at 200
  bytes, 005-33): 1 thread and 1 open file left after them; the first
  start's zero fill was written by its left-over thread.
* Twenty times, 005-11's P9 in small, with files: a start with a main and
  a replica of two histories fails (005-28), having copied the replica's
  last transaction into the main's buffer. At once the main alone starts,
  writes a transaction and syncs it (STRONG), while the failed start's
  thread writes that copy to the same file:

  | Then | Assertions on | Assertions off |
  |---|---|---|
  | The main alone's write came first and was synced; the failed start's write was then refused by `FileStream`'s check; a restart of the main finds the transaction | 9 | 7 |
  | The failed start's write came first; the main alone's write failed (`StreamIoException`: the file "is not of expected length"); the main does not start any more, as it now holds the replica's transaction (005-28's exception) | 9 | 9 |
  | Both wrote at the same position. With assertions on, the main alone's writer thread died of an `AssertionError` and its sync waited for ever; with them off, its sync returned, and the main does not start any more | 2 | 4 |

  `FileStream.append` compares the file's length with its own before each
  write. That stops a second writer that writes later (`twice`: two
  databases started on one directory, writing in turn; the second one's
  first write fails, and a restart finds all of the first one's). It does
  not stop two writers that check before either has written: both write
  at the same position. With assertions on, the check after the write
  (`FileStream.DbFile.append`, "864 != 1048") kills the writer's thread;
  with assertions off, nothing notices, and a transaction whose sync has
  returned is lost.
* `BufferedStream.close()` with bytes in the buffer, when the flush fails:
  still waiting after 3 s. `close()` waits until the buffer is empty, but
  after a failed flush the thread stops (2026-10-13, `stopAfterFailure`)
  and the buffer never empties. So `Db.close()` hangs when the disk fails
  at the last flush, and so would a fix that closes the storage of a start
  that failed on the storage. Also: an `Error` in a flush (such as the
  assertion above) is not caught (`flushToStream` catches `IOException`
  only), so the thread dies without telling the listener, and every sync
  after it waits for ever.


The fix, proposed
-----------------

1. `Db.start`: when `startInner` throws, close the storage before the
   exception leaves, outside the locks: what the start appended is
   written (recovery's zero fill and the copies between streams are what
   any start writes, so writing them is safe, and the result is the same
   every time), the streams are closed and their threads stopped, and the
   `Db` is stopped (`DbState.STOPPING`), so later calls are refused as
   after `stop()`. If the close fails too, its exception is added to the
   start's as suppressed. The same for an `Error`, which is then thrown as
   it is.
2. The Pub API: `DatabaseImp.createAndStart` closes the `Db` when anything
   after `db.start()` throws; `DatabaseBuilderImp.start` closes the
   streams that the builder opened when it throws before the `Db` is
   built.
3. `BufferedStream`: `close()` returns when the thread has stopped, also
   after a failed flush, and throws that failure; a flush that throws
   anything, not only an `IOException`, stops the stream and tells the
   listener, so syncs fail instead of waiting.

Not part of this entry: a lock on the database's directory, so that two
databases cannot write it at once. After this fix, a failed start no
longer leaves a second writer; an application that opens one directory
twice still can, and two that write at the same moment are not stopped
by `FileStream`'s check. A separate entry if wanted.


Done when
---------

* Unit tests:
  * A start that throws (005-28's crashed creation; a stream of two
    histories) leaves no thread of its storage and its streams closed,
    and what it appended is written; a later call on the `Db` is refused.
  * The Pub API: ten starts with a wrong key leave no thread and no open
    file, counted at once, without a garbage collection; then the right
    key starts. A directory whose start failed can be removed and created
    again at once.
  * An exception after `db.start()` in `DatabaseImp.createAndStart` (a test
    hook) closes the `Db`.
  * `BufferedStream.close()` returns, and throws the failure, when the last
    flush fails; an `Error` in a flush makes a sync fail instead of wait.
  * While replication is in the code (005-11): the race above, after which
    the main alone writes, syncs and finds its transaction after a
    restart, 20 times of 20, with assertions on and off.
* `java/before-commit.sh` prints `BEFORE COMMIT OK`.


First step
----------

List every place where a start can throw, in `Db`, `DbBuilder` and the
Pub API, and what each has opened by then; check that `StorageManager`'s
close needs neither the write lock nor `readSync`.


Size and order
--------------

S: about 40 lines in `Db`, `DatabaseImp`, `DatabaseBuilderImp` and
`BufferedStream`; the tests are most of it. Any time; before 005-33's
change, whose options A and B need the files of a failed start closed.
Independent of 005-11; the race test goes with replication.


Outcome
-------

2026-10-24, by Claude (Opus 5.5, Claude Code), as proposed, at Frans's
request ("fix all todo items of type Fix", "do what is proposed").

The first step, where a start can throw and what it has opened by then:

* `Db`'s constructor makes the storage: a `StorageManager` with a
  `BufferedStream` and its running thread for each stream. After that, a
  null clock (`DbClock`) or a step reserve below 1
  (`Reclaim.setStepReserve`) threw, and nothing closed the storage. Now the
  clock is made before the storage, and `DbBuilder.reclaimStepReserve`
  refuses the value itself.
* `Db.start`, also through `DbBuilder.start()`: anything in `startInner`,
  from `syncStreams` (a `BadReplicaException`, the copies between the
  streams), the creation, recovery (`BadCryptoKey`), the reading of the
  startup section (005-28) and the reruns, to reclaim's `initFromDb` after
  the state is `ACTIVE` (005-30). The streams are open, their threads run,
  and the buffers hold what the start appended.
* The Pub API: `DatabaseBuilderImp.start` before the `Db` is built
  (`handleCryptoKeyAndCreatedTxt`: a key of an unknown algorithm, a
  `SalsaStream` that cannot be made), with the `FileStream` of `dir()` and
  those of `replica()` open; and `DatabaseImp.createAndStart` after
  `db.start()` (the index manager's initialization and its jobs), with the
  database running.
* `StorageManager`'s close needs neither `writeLock` nor `readSync`: it
  swaps its `Internal` with a compare-and-set and closes each
  `BufferedStream`, which synchronizes on itself.

The fix:

1. `Db.start`: when `startInner` throws, the state becomes `STOPPING`
   under both locks, so no call sees what the start left, and outside them
   the storage is closed (`StorageManager.closeAndThrow`, new: as
   `close()`, and it throws the first failure of a stream's close). What
   the start appended is written, the streams are closed, and their
   threads have ended when the exception leaves; a failure of the close is
   added to it as suppressed. A second `start()`, or one after `stop()`,
   closes nothing, as the state is checked before.
2. The Pub API: `DatabaseImp.createAndStart` closes the `Db` when anything
   throws, after `db.start()` too (a test hook, `testHookAfterStart`, can
   throw there); `DatabaseBuilderImp.start` closes the builder's streams
   (`DbBuilder.closeStreams`, new) when it throws before the `Db` is built.
   `DatabaseBuilder.start()`'s Javadoc says so.
3. `BufferedStream`: `close()` waits until all is written or the thread has
   stopped, then until the thread has ended, and throws the failure of a
   flush (a new field, `failure`). It does not wait for the thread from the
   thread itself: `StorageManager.handleStreamException`, the listener of a
   failed flush, closes the stream there. After `stop()` too it now waits
   for the thread; it returned at once (005-35's second issue, below the
   database). A flush that throws a `RuntimeException` or an `Error` stops
   the stream as an `IOException` does and tells the listener, so syncs
   fail instead of waiting for ever.
4. Found on the way: `Db.newGetData()` and `newGetMany()` of a database
   without a Dag (not started, or a start that threw) threw a
   `NullPointerException`; now they are refused as a read is: a
   `DbStoppingException` after a failed start.

Tests:

* `DbTesterFailure.testFailedStartClosesStorage`: a creation cut at 200
  bytes (005-33): the start throws; the zero fill is written (264 bytes);
  no thread of the storage runs; the stream is closed; a transaction and a
  read are refused.
* `DbTesterFailure.testFailedStartOfTwoHistories`: 005-11's P9 in small,
  with `MemoryStream`s: the start with a main and a replica of two
  histories throws (005-28), after it copied the replica's last
  transaction to the main; the copy is written (the main as long as the
  replica), both streams are closed, no thread runs.
* `DbTesterFailure.testErrorInFlushFailsSync`: an `AssertionError` in an
  append (`FaultStream.errorInAppends`, new): the sync fails the database
  (005-30) instead of waiting, and `close()` returns.
* `BufferedStream.testCloseAfterFailedFlush`: an `IOException` and an
  `Error` in the last flush: `close()` returns, throws the failure, the
  listener is told, the thread has ended.
* `PubTester.testFailedStartsLeaveNothing`: ten starts with a wrong key
  leave no thread and no open file, counted at once; then the right key
  starts and reads. `PubTester.testFailedStartsDirectoryRemoved`: a
  directory whose creation crashed, after the failed start, is removed and
  created again at once. `PubTester.testExceptionAfterStartClosesDb`: the
  test hook throws after `db.start()`; the `Db` is closed, its stream too,
  and a transaction is refused. `PubTester.testUnknownCryptoAlgorithmClosesFile`:
  three starts with a key of an unknown algorithm leave no open file.

Each of them fails without its part of the fix, undone for the check.

The probe again, on the fixed build
([runs/after-*.txt](32-fix-failed-start-storage/runs/)):

* `pub`: ten starts of a directory whose creation crashed: 0 threads and 8
  open files after them, as before them (1 and 9 before the fix).
* `key`: ten starts with a wrong key: 0 threads and 8 open files, also with
  finalization disabled (5 and 13 before the fix; 10 and 10 without
  finalization); the right key starts.
* `closehang`: `close()` returned; before, still waiting after 3 s.
* `race`, 20 times, assertions on and off: the same every time, the start
  with both fails (005-28), and then the main alone fails to start too, as
  does a later start of the main (`StreamFormatException`). No synced
  transaction is lost, no writer thread dies and nothing hangs: the failed
  start's thread no longer writes later. But this is not what "Done when"
  expects, that the main alone then writes, syncs and finds its
  transaction 20 times of 20. By point 1, the start with both writes the
  replica's last transaction to the main (`syncStreams`'s copy), as any
  start with both would; the main then holds two histories, which 005-28
  refuses. Before the fix the main ended so 9 and 9 times of 20 (the failed
  start's write came first), and 2 and 4 times both wrote at the same
  position. To drop the buffer of a failed start instead would keep the
  main as it was only if the copy had not been flushed yet, so not every
  time. Two histories are 005-11's matter, replication, which waits for
  Frans.
* `twice`: unchanged, two databases on one directory: the second one's
  first write is refused, and a restart finds all of the first one's (the
  lock on the directory is not part of this entry).

`before-commit.sh`: BEFORE COMMIT OK (1004 unit tests, 63 f-tests).

2026-11-05 (015-19): `tools/FailedStartProbe.java` is kept for the code of its time, not
changed: it calls `DatabaseBuilder.dir` (removed by 015-05) and `SyncLevel`
as it was before 005-56. It compiles against a jar of its time, not against
release 2026.2's or main's.
