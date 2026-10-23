005-32. Fix: a start that throws leaves its storage running
==========================================================

Status: open. Kind: fix. Created 2026-10-23.

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

`FailedStartProbe`, on `e2c0dc0`, Java 27
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
