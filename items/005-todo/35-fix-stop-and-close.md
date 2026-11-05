005-35. Fix: stop() loses what is buffered, and close() does not always wait
===========================================================================

Status: done (2026-10-24). Kind: fix. Created 2026-10-24.

Found on 2026-10-24 by Claude (Opus 5.5, Claude Code), from Frans's note in
`Db.close()` ("26102424-BUG1-close") and a finding of 005-27's work; added
at Frans's request ("Investigate this further, then write this down as a
fix item in 005."). The probes, the survey of the calls and their runs are
in [35-fix-stop-and-close/](35-fix-stop-and-close/).


What stop() and close() are for
-------------------------------

Frans, 2026-10-24: "None of the stop() and close() methods are meant to be
crash semantics. Both stop() and close() are for properly closing the
database. stop() returns faster ("immediately") while close() waits for
resources (storage) to be closed before it returns. I believe stop() is
useful for testing." And: "Let's follow the Javadoc spec of stop(). No
waiting there, good to have."

`Db.stop()`'s Javadoc: it "returns quickly, it does not wait for threads to
finish, storage streams to flush and files to be closed. It only request a
release of such resources in the near future", typically within a second;
"When this method returns, it is guaranteed that no write operation is
running or will be started". `Db.close()`: "Stops the database, flushes the
storage streams and releases resources ... and waits until its done before
it returns." The Pub API has only `Database.stop()`, which calls
`Db.stop()`; its Javadoc says to call `sync()` before it "when appropriate",
and that a database no longer referenced is stopped when garbage collected
(`Db.finalize` calls `stop()`).

How they are used ([runs/survey.txt](35-fix-stop-and-close/runs/survey.txt),
one line per call in [runs/calls.txt](35-fix-stop-and-close/runs/calls.txt)):
338 calls of `stop()`, 213 on a `Db` and 125 on a `Database`, almost all in
tests, 83 of them with a sync in the five lines before; and 37 of
`Db.close()`, in `DbTesterFailure`, `Perf`, `LoadTest`, `Soak`,
`ReclaimCost` and a few more. Most tests stop an in-memory database at
their end; those I read that restart from the stream sync first, as stop()
would otherwise lose their last transactions (issue 1).


The issues
----------

The probes are `tools/StopCloseProbe.java`, on `685e895`; a slow stream is
an in-memory stream whose appends take 300 ms.

1. **stop() loses the transactions that are still in the write buffer.**
   `BufferedStream.stop()` sets `stop`, and the storage thread leaves its
   loop without writing what is buffered (`runConsumer`, the `break A` at
   lines 153 and 185), then closes the stream. Only a flush that had begun
   completes. The same in the 2017 code. Probe `stop`
   ([runs/stop.txt](35-fix-stop-and-close/runs/stop.txt)): 2,000 puts
   without a sync, with the default buffer (10 MB, 20 ms), then stop(); 2 s
   later the files hold 0 to 115,536 of the 303,784 bytes, and a restart
   finds 0 to 825 of the 2,000 keys. In two of three runs nothing was
   written, not even the database's creation, so the restart created a new
   database. With close(), all 2,000, every time. The Pub API's
   `Database.stop()` the same: 0, 0 and 0 here (1,859 in an earlier run).
   Probe `exit` ([runs/exit.txt](35-fix-stop-and-close/runs/exit.txt)): a
   program that puts 2,000 keys, calls `Database.stop()` and returns from
   `main` leaves 490 to 699 of them.
2. **close() returns at once after stop(), or while another close() runs**
   (Frans's note). Both of its checks of `DbState.STOPPING` return without
   waiting. Below it, `BufferedStream.close()` returns at once when `stop`
   is set (line 542). Probe `stopclose`
   ([runs/stopclose.txt](35-fix-stop-and-close/runs/stopclose.txt)), on a
   slow stream: close() after stop() returned after 0.0 ms, with the storage
   thread alive and the stream open; the thread closed it within the
   second, with 2,640 of the 14,216 bytes written, the rest lost by stop().
   Probe `twoclose` ([runs/twoclose.txt](35-fix-stop-and-close/runs/twoclose.txt)):
   thread B's close(), 50 ms after thread A's, returned after 0.0 ms with
   264 of the 14,216 bytes written and the stream open; A's returned after
   603 ms with all of them.
3. **A transaction that waits for room in the buffer waits for ever when
   the stream stops or fails.** `BufferedStream.append` waits in a loop
   (line 439) that does not look at `stop` or at the failure: the thread
   that would make room has ended. Probe `running`
   ([runs/running.txt](35-fix-stop-and-close/runs/running.txt)): a put of
   1 MB into a buffer of 100 KB on a slow stream; stop() returned after
   0.7 ms, and the put was still waiting 3 s later. Probe `fullfail`
   ([runs/fullfail.txt](35-fix-stop-and-close/runs/fullfail.txt)): the
   same with a stream whose appends fail (a failing disk): the put waits
   for ever, holding the write lock, and the next transaction waits for the
   lock for ever. The database hangs instead of failing, which 005-30 made
   a failed sync or read do. With the default buffer, a transaction waits
   for room only when more than 9 MB are buffered: bulk loads and large
   values.
4. **stop()'s guarantee that "no write operation is running" does not
   hold.** stop() does not take the write lock (nor did it in 2017); a
   running transaction goes on and meets a stopped stream (005-01's
   outcome: "stop() closes the storage without the write lock, so a running
   transaction's append can fail"), or waits for ever (issue 3).
5. **A process that ends right after stop() does not wait for the storage
   threads.** They are daemon threads (`consumer.setDaemon(true)`, line
   121), so the JVM exits without them. Today that adds nothing to issue
   1; with a stop() that writes in the background, it would still lose the
   last transactions of a program that returns from `main` after stop().

Also seen, not part of the fix: a sync that waits when close() begins
throws ("Storage is closing."), although close() then writes its bytes;
neither stop() nor close() forces the files to the device, which
`sync(SyncLevel.STRONG)` does, as with ordinary files; and some tests start
a new database on the same stream right after stop() (`DbTester.testCrash2`
reuses `mstream`), while the old storage thread closes that stream at a
time of its own.


The fix, proposed
-----------------

1. **One way of closing, which stop() starts and close() waits for.**
   `Db.stop()` sets `STOPPING`, so that no operation starts, as now, and
   starts the close in a thread of its own, then returns at once. That
   thread takes the write lock, so that a running transaction completes
   and is written, and closes the storage as `close()` does now: it writes
   what is buffered, closes the streams and ends the storage threads.
   `Db.close()` starts the same close if none has begun, and waits until it
   is done, also when stop() or another close() began it. The closing
   thread is not a daemon, so a program that returns from `main` after
   stop() still writes all it had. `finalize()` keeps calling stop().
2. **BufferedStream.** `close()` returns when its thread has ended and the
   stream is closed, also when stop() came first; a writer that waits for
   room in the buffer gets an `IOException` when the stream stops or
   fails, instead of waiting for ever. A transaction then fails the
   database, with the failure as the cause (005-01), or is refused as the
   database stops. With 005-32's third point, which changes the same
   methods.
3. **Javadoc.** stop() and close() write every transaction that has
   returned; stop() returns at once, close() when the streams are closed;
   neither forces the files to the device. stop()'s guarantee becomes: no
   operation starts after it; a write that runs completes and is written.
   The Pub API's `Database.stop()` the same, with its advice on sync()
   made precise.

Questions for Frans, answered on 2026-10-24:

* Should the Pub API get a `close()` too, `Database.close()` (and
  `Closeable`, for try-with-resources), for a program that must know that
  its files are closed? Frans: "Not now."
* A transaction that runs when stop() is called: complete it and write it
  (proposed), or refuse it? Frans: "As you propose."


Done when
---------

* Unit tests, on a slow stream as in the probes:
  * after stop(), once the closing thread has ended, the stream holds every
    transaction that returned, for `Db` and for the Pub API, also with a
    transaction running at stop();
  * close() after stop(), and two close() at once: each returns only when
    the stream is closed and holds everything;
  * a writer that waits for room in the buffer: after stop(), it completes
    or is refused, and does not hang; after a failed flush, it throws, the
    database fails, and the next transaction is refused.
* An f-test: a JVM that returns from `main` after stop() leaves all its
  transactions.
* The probes again: `stop` and `exit` find all the keys; `stopclose`,
  `twoclose`, `running` and `fullfail` as the unit tests.
* The tests that use a stream after stop() still pass (with close() where
  they need it closed); StreamDigest unchanged; `java/before-commit.sh`
  prints `BEFORE COMMIT OK`, and the level scripts, which stop every
  database they make, print their OK.


First step
----------

From [runs/calls.txt](35-fix-stop-and-close/runs/calls.txt), the tests
that read or reuse a stream after stop(), as they meet a stop() that writes
in the background.


Size and order
--------------

M: `Db.stop` and `close`, `StorageManager`'s close and `BufferedStream`'s
`close`, `stop` and `append`, about 60 lines; the tests are most of the
work. With 005-32 or after it, as both change `BufferedStream.close()`;
before 005-33's change.


Outcome
-------

2026-10-24, by Claude (Opus 5.5, Claude Code), as proposed, with Frans's
answers (no `Database.close()`; a transaction that runs at `stop()`
completes and is written), at his request ("fix all todo items of type
Fix", "do what is proposed"). After 005-32, which changed
`BufferedStream.close()` first.

1. One close, `Db.closeStorage()`, for `stop()`, `close()` and a start
   that throws (005-32): it takes the write lock, so that a transaction
   that runs completes and is written (none starts after it: the state is
   `STOPPING`, and `executeInner` checks it again under the lock), then
   closes the storage (`StorageManager.closeAndThrow`), which writes what
   is buffered, closes the streams and ends their threads. It runs once
   (`closeLock`, `closeBegun`, `closeDone`).
   * `stop()` sets `STOPPING` and starts the close in a thread of its own,
     `Db-close-N`, which is not a daemon, and returns at once.
   * `close()` sets `STOPPING` and runs the close itself if none has
     begun; else it waits, without being interrupted, until the close
     that `stop()` or another `close()` began is done. Within a
     transaction (an action or a listener, which hold the write lock), a
     close that another call began waits for that lock, so `close()`
     closes the storage at once there, as it did before.
   * `finalize()` still calls `stop()`. `StorageManager.stop()` (which
     drops the buffer) is no longer called by `Db`; tests use it.
   * Frans's note in `close()` ("26102424-BUG1-close") is gone with the
     fault it named; the Javadoc refers to it.
2. `BufferedStream`: `close()` returns when its thread has ended, also
   after `stop()` (since 005-32). A writer that waits for room in the
   buffer gets an `IOException` once the thread has stopped, after
   `stop()` or a failed flush, with the failure as the cause; the
   transaction then fails the database (005-01), or, while it stops, it
   throws as before.
3. Javadoc: `Db.stop()`, `Db.close()` and the Pub API's `Database.stop()`
   say that every transaction that has returned is written, that `stop()`
   returns at once and `close()` when the streams are closed, that a
   running transaction completes, that neither forces the files to the
   device, and when to call `sync()` first.

Tests (each fails on the code before the change, `Db` and
`BufferedStream` undone):

* `DbTester.testStopWritesAll`: 300 transactions without a sync, then
  `stop()`: once its close has ended, the stream holds them all and is
  closed, and a restart reads them (before: 26,752 of 27,784 bytes).
* `PubTester.testStopWritesAll`: the same through the Pub API (before,
  the value of `/k192` was not there).
* `DbTester.testStopWithRunningTransaction` (f): a put of 400 KB that waits
  for room in a 100 KB buffer on a slow stream (20 ms an append), and
  `stop()` meanwhile: `stop()` returns at once, the transaction completes,
  and a restart reads it (before: the transaction still ran after 30 s).
* `DbTester.testCloseWaits` (f): on a slow stream (100 ms an append),
  `close()` after `stop()`, and two `close()` 20 ms apart: each returns
  when the stream is closed and holds every byte (before: 264 of 9,416
  bytes).
* `DbTester.testWriterWaitingForRoomAfterFailedFlush`: a put of 1 MB that
  waits for room when the flushes fail: it fails the database, and the
  next transaction is refused (before: it still waited after 10 s).
* `PubTester.testStopThenReturnFromMain` (f): a child JVM puts 2,000 keys,
  calls `Database.stop()` and returns from `main`; a restart finds all of
  them (before: 866).

The probes again, on the fixed build
([runs/after-*.txt](35-fix-stop-and-close/runs/)): `stop`, 2,000 puts
without a sync: 2,000 of 2,000 keys after `Db.stop()`, `Db.close()` and
`Database.stop()`, three times each; `exit`: 2,000 of 2,000, three times;
`stopclose`: `close()` after `stop()` returned after 571 ms with the
stream closed and all 14,216 bytes written, and no storage thread left;
`twoclose`: both returned after 604 and 550 ms, with the stream closed and
all bytes written; `running`: `stop()` returned after 1.5 ms, and the put
of 1 MB returned normally 8.5 s later (20 flushes of 50 KB at 300 ms);
`fullfail`: the put of 1 MB failed the database, and the next was refused.
Two changes to the probe: the child of `exit` returns from `main` instead
of calling `System.exit()`, which does not wait for any thread; and
`running` waits 30 s instead of 3, as its put now completes.

The tests that read or reuse a stream after `stop()`: all pass. A scan
of the calls for a start on the stream of a database stopped without a
sync after its last write, in the same method, found none (the survey's
tests sync first, or start on a copy).

The level scripts, which stop every database they make, on the change
([runs/gates.txt](35-fix-stop-and-close/runs/gates.txt)): LEVEL 1 OK,
LEVEL 2 OK (70 traces, TRACECHECK OK), LEVEL 3 OK (25 traces, no failing
CUT line), LEVEL 4 OK.

`before-commit.sh`: BEFORE COMMIT OK (1007 unit tests, 66 f-tests).

2026-11-05 (015-19): `tools/StopCloseProbe.java` is kept for the code of its time, not
changed: it calls `DatabaseBuilder.dir` (removed by 015-05) and
`AppendOnlyStream.seekFirstPos` (removed by 019-04). It compiles against
release 2026.2's jar, not against main's.
