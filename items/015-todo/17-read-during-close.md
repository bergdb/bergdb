015-17. Investigate: a read during close fails with "File closed", and close reports it
=======================================================================================

Status: done. Kind: Investigate. Created 2026-11-03 by Frans Lundberg.

For release 2026.2, if it is a fault.

What: in 016-08's F3 (F53, main at `c8e2f1e`), `InterruptStress` failed
after 485 s of a 600 s run: "a worker failed", `StreamIoException: File
closed, .../00000000022200.bergdb` at `Db.close` (1307), from a worker's
close (`InterruptStress$1.once`, 167); its cause, the `IOException` "File
closed" at `FileStream$DbFile.reopenChannel` (1254), from a read of
another worker's get (`InterruptStress$2.once`, 186: `DbUtil.get`,
`Db.getOne`, `NodeCollection.followValuePointer`, `NodeStream.readNode`,
`RecoverableStream.read`, `StorageManager.read`, `BufferedStream.read`,
`FileStream.read`). So a get that ran while the database closed read a
file that the close had closed; the read failed as an I/O failure, and
the close reported it. InterruptStress takes no seed (its interleavings
come from timing), so a rerun need not repeat it.

Questions: what does BergDB promise for a get that runs while another
thread closes the database (Db.close's and the Pub API's Javadoc;
005-46, 005-55, 005-63)? Should the get get a "closed" refusal, and the
close not fail? Is the read's failure recorded as the database's
failure, and does a later start see anything of it (it should not)?

Done when: the interleaving is written out against the code and checked;
a fault is fixed with a test that forces it, or the behaviour is shown to
be the promised one and InterruptStress's check is corrected.

First step: the interleaving, from the stack traces in
`/Users/f/fl/bench/016/h4-stress/f3/interrupt-111110000.txt`.

Found 2026-11-03 by 016-08's F3.


State
-----

2026-11-03, 17:32: done. A fault (Log): close() reported a get's "File
closed" as a failed close. Fixed in `FileStream` with two tests, reviewed
by the coordinator and committed after the combined gate.


Log
---

2026-11-03. Registered by the coordinator of release 2026.2 (016-02).

2026-11-03, 17:07 to 17:26, by agent J (016-05), in
`/Users/f/fl/bench/016/015-17/repo` from `main` at `60b7074` (the code
of the run, `c8e2f1e`, differs in none of the classes below but `Db`'s
line numbers):

* **The promise.** For the get: a read while the database stops throws
  as it did (docs/levels.md, section 3; `Db.getOne`'s Javadoc: a
  `StreamIoException` "while the database is stopping"; 005-30: reads
  still running during a close get an `IOException`; 005-46, change 3: a
  read of a closed file fails "as today"). For the close: it throws
  `StreamIoException` only for "a failed final flush or storage close"
  (`Db.close`, the Pub API's `Database.close`; 005-73, F5). Here nothing
  of the close failed: the get's read failed, and close() reported it.
  A fault, of 2026.2 only: `release-2026.1`'s `Db.close` dropped
  `closeStorage`'s failure (F5 came in `afc3d20`).
* **The interleaving**, from the trace in
  `/Users/f/fl/bench/016/h4-stress/f3/interrupt-111110000.txt` (W, the
  writer worker in its restart, `InterruptStress` line 167; R, a reader
  worker's get, line 186; C, the `BufferedStream` consumer thread):
  1. R: `Db.getOne` reads the volatile state `ACTIVE`; down to
     `StorageManager.read` (`hasError` false) and `BufferedStream.read`,
     whose check under the stream's monitor passes (`exception` null,
     the bytes in the stream part); it leaves the monitor before
     `FileStream.read`, and stalls (F53 at a load of about 33).
  2. W: `Db.close` sets `STOPPING` under `readSync`; `closeStorage`
     takes and leaves the write lock, ends eviction's thread;
     `StorageManager.closeInner` sets "Storage is closing.";
     `BufferedStream.close` sets `flushAndClose` and `exception`, waits
     until the buffer is written, `stop()`, then `consumer.join()`.
  3. C: leaves its loop on `stop` and closes the stream, the first
     `FileStream.close()` (`BufferedStream` line 206): `failure =
     ioException` (null), each `DbFile.close()` sets `isClosed` under
     `channelLock` and closes the channel; `unlockDir`; no failure; C
     ends.
  4. R: `DbFile.read` (its `isClosed` check passed before 3): the
     channel read throws `ClosedChannelException`; `reopenChannel`
     finds `isClosed` under `channelLock` and sets the stream's failure,
     `ioException = new IOException("File closed, ...")`, and throws it
     (`FileStream` 1254, the trace's line; a read that begins after 3
     does the same at 1182). Up through `StorageManager.read` (whose
     `handleStreamException` closes the `BufferedStream` again from R)
     to `Db.readFailed`: not below a cut; `failOnStorage`'s
     `setFailed` finds `STOPPING`, records nothing, and the
     `StreamIoException` is thrown as it is. R's check sees the
     database inactive and goes on. All as promised.
  5. W: `consumer.join()` returns; `BufferedStream.close` closes the
     stream again (line 671), the second `FileStream.close()`: `failure
     = ioException`, now R's exception; every file is closed already;
     `throw failure`. `closeInner` keeps it, `closeStorage` sets
     `closeFailure`, and `Db.close` throws `StreamIoException(closeFailure)`
     (`Db` 1307 at `c8e2f1e`), with R's `IOException` as the cause: the
     trace exactly.
* **Not the database's failure, nothing for a later start.** W's write
  of `STOPPING` (under `readSync`) comes before its `BufferedStream.close`
  (the stream's monitor), C's read of `stop` under that monitor before
  C's write of the volatile `isClosed` under `channelLock`, and that
  before R's read of it there: R's `setFailed` under `readSync` comes
  after `STOPPING` and cannot see `ACTIVE`. The close wrote every
  buffered byte before `stop()` (FileStream forces each append); the read
  writes nothing. Only the closed instances' memory holds the read's
  exception (`ioException`, R's `ErrorStorage`). The new test restarts
  and reads every key.
* **The fix**, `stream/FileStream.java`: a read of a closed file, in
  `DbFile.read`'s check and in `reopenChannel`'s, throws a new
  `IOException` ("File closed, ...", `closedException()`) without
  keeping it as the stream's failure, as a read of a deleted file fails
  alone. The other failures stay the stream's (a failed delete, close or
  append; an append after close keeps its `ioException`). `close()`'s
  Javadoc says that a read of a closed file is not a failure of the
  stream. `InterruptStress`'s check is right and is not changed.
* **The tests.** `FileStream.testReadOfClosedFileFailsAlone`: a read
  after `close()`, and a read held by a `HeldReadIo` channel after its
  checks while `close()` closes the channel (the `reopenChannel` path);
  each read fails with "File closed", and a second `close()` returns.
  `DbTesterFailure.testGetDuringClose`, the stress run's interleaving on
  a `FileStream` with eviction (`startEvicting`): `CloseRaceStream`
  holds R's first read, once begun, until the first `close()` (C's) has
  closed the `FileStream`, and that close until the read is done; then
  `db.close()` returns, the get throws `StreamIoException`, the database
  is stopping, not failed, and a restart reads all 2,000 keys. On the
  base both fail (the second `close()` throws the read's exception;
  `Db.close` throws `StreamIoException: File closed`, the trace's cause).
  Mutations (`/Users/f/fl/bench/016/015-17/mut/mutate.py`): M1, the old
  `read()` check: both tests fail; M2, the old `reopenChannel()` check:
  `testReadOfClosedFileFailsAlone` fails at the `reopenChannel` line,
  `testGetDuringClose` passes (its read takes the other check).
* **The smoke**: `InterruptStress 180` on the fix, 17:19 to 17:22 (F53
  at a load of about 33): `INTERRUPT STRESS OK`, 47,050,490 calls, 19
  restarts. (The fault needs a stalled read; 1 in 485 s of F3.)
* **The gate**: the clone rebased on `main` at `4948ec6` (015-01's
  change to `FileStream`, elsewhere in the file); `java/before-commit.sh`,
  17:22 to 17:24: `BEFORE COMMIT OK (134 s)`, 1,121 unit tests and 78
  f-tests.
* Not changed: the stream format, the Pub API, `InterruptStress`,
  `docs/levels.md` (section 3 says already that a read while the
  database stops throws as it did).
* A doubt, not changed: during a close, `StorageManager.read`'s
  `handleStreamException` takes a get's failed read for a failure of the
  stream and closes the `BufferedStream` again from the reader's thread.
  Harmless here: the stream is closing, the second close finds it
  closed, and `failOnStorage` records nothing while the state is
  `STOPPING`.

2026-11-03, 17:31, by the coordinator (016-05, H5): the review found no
faults. The combined gate on `main` at `f070403` with the patch:
`BEFORE COMMIT OK (130 s)`, 17:27 to 17:30.
