016-06/verify-2. Verification of R2's and R3's other findings
=============================================================

Created 2026-11-03 by Frans Lundberg. Base: b1651a5. Started 20:46, ended 20:56 (from date).

The code is a clone of b1651a5 in `/Users/f/fl/bench/016/verify-2/repo`, built with
`sh java/build.sh`. Each probe and patch was copied to `/Users/f/fl/bench/016/verify-2/`
(`R2/`, `r3/`) and run there, one JVM at a time; outputs are in its `out/`. The two R3
patches (tests only) were applied for their Nano tests and then reverted; every probe's
output is from a clean build of b1651a5 (the R3 probes were run on both, with the same
output). Commands below run from `/Users/f/fl/bench/016/verify-2` with
`JAR=repo/java/build/bergdb.jar`. "Main" is ca02b5e, checked by reading the code, not by a
run.


## R2-F2 (confirmed)

`FileStream.pretruncate(pos)` with `pos == getLength()` throws `Bug("Unexpected newSize: 0")`.

* Reasons. The loop at lines 426-433 selects every file with `spos + fileLength - 1 < pos`;
  `fileLength` is the file's current length (line 1097), so at `pos == length` the last
  file qualifies too, also the empty first file (`0 + 0 - 1 < 0`). `newSize` is 0 and lines
  437-438 throw. The contract, `AppendOnlyStream.pretruncate` Javadoc, refuses only "a
  position greater than the length of the stream", so a cut at the length is legal. The
  probe uses only `FileStream`'s public constructor, `append`, `pretruncate`, `read` and
  `close`, as the contract allows. At b1651a5 the check comes before any file is taken off,
  so the stream stays usable (the probe appends and reads after it).
* Reach. Internal classes only. `bergdb.pub` exposes no stream. `BufferedStream` passes a
  cut at its flushed length straight on (lines 570-577), and `applyPendingCut` passes a
  pending cut equal to the flushed length (line 587), and the consumer's catch (lines
  286-288) turns that `Bug` into a failure of the storage (`stopAfterFailure`).
  Db's reclaim cuts at a transaction's position after it has written its table transaction
  behind it, and only when the stream is durable past that table (`Reclaim`, lines
  381-401, 669), so the stream is longer than the cut; no Pub path was found that cuts at
  exactly the length.
* Effect class. A legal call fails with an internal error. No data lost or invented at
  b1651a5, no wrong answer, no hang.
* 2026.1: yes, and worse: its `pretruncate` deletes the selected files, the last one
  included, before the same `newSize` check throws, so there such a cut would remove the
  stream's bytes (not reached through Pub there either).
* Still on main: yes; `pretruncate` at ca02b5e has the same loop and check (lines 442-457).
* Commands:

  ```sh
  javac --release 17 -cp $JAR -d classes R2/CutEndProbe.java
  java -ea -cp classes:$JAR bergdb.core.CutEndProbe out
  # cut at length 0: bergdb.common.Bug: Unexpected newSize: 0. pos=0, kfiles.length=1
  # cut at length 3: bergdb.common.Bug: Unexpected newSize: 0. pos=3, kfiles.length=1
  # Stream remains usable: length=4, last=7
  git show release-2026.1:java/src/bergdb/stream/FileStream.java   # lines 257-294
  git -C /Users/f/fl/repos/bergdb show HEAD:java/src/bergdb/stream/FileStream.java
  ```


## R2-F3 (confirmed)

An unchecked exception in the open of a new file leaks its handle; an `Error` in the
constructor also leaves the directory in `LOCKED_DIRS`, so the next open is refused.

* Reasons. `openForRw()` (lines 1032-1049) closes `k.rfile` only in `catch (IOException)`;
  a `RuntimeException` or `Error` from `k.force()`, `forceDirectory` or `io.openRead`
  leaves it open, and `k` is not yet in `dbFiles`, so `closeAfterFailedOpen()` (lines
  218-227) cannot close it. The constructor (lines 205-213) catches `IOException` and
  `RuntimeException` only; an `Error` skips `closeAfterFailedOpen()`, hence `unlockDir()`,
  and the key added at line 587 stays in the static `LOCKED_DIRS`. Nothing else removes it:
  no `FileStream` is returned to close. The cited texts ask for the cleanup: 005-63, "The
  lock file", point 5 ("A failed open (`closeAfterFailedOpen`) releases it too"), and
  011-07, "Production changes" ("Failed construction also releases already opened
  files"). The probe injects the failures with `FileStreamIo`, the public test boundary of
  the power-loss tests, at `forceFile` of the first new file, and uses the constructor
  `FileStream(File, FileStreamIo)` documented "Internal, for testing"; that is a fair way
  to drive the control flow, not a misuse. The output matches the finding.
* Reach. Through Pub in principle: `DatabaseBuilderImp` opens each directory with
  `new FileStream(dir)` (line 277), and a failure there propagates to the caller's start.
  In normal use it needs an unchecked exception or an `Error` (such as `OutOfMemoryError`)
  thrown inside the open of a file; the production `FileStreamIo` throws only
  `IOException` on its own, so this is rare and the probe needs the internal boundary to
  force it.
* Effect class. A leaked file descriptor, and after an `Error` a refused reopen
  (`DirectoryInUseException`) of that directory until the JVM ends. No data lost or
  invented, no wrong answer, no hang.
* 2026.1: yes for the handle leak (same catch coverage in its constructor and
  `openForRw()`); no for the stranded lock, as 2026.1 has no `LOCKED_DIRS` (005-63 came
  after).
* Still on main: yes; at ca02b5e the constructor (lines 212-233) still catches only
  `IOException` and `RuntimeException`, and `openForRw()` (lines 1062-1085) still closes
  only on `IOException`.
* Commands:

  ```sh
  javac --release 17 -cp $JAR -d classes R2/FailedOpenProbe.java
  java -ea -cp classes:$JAR bergdb.core.FailedOpenProbe out
  # IOException: IOException / data handle still valid: false / reopen: succeeded
  # RuntimeException: IllegalStateException / data handle still valid: true / reopen: succeeded
  # Error: AssertionError / data handle still valid: true / reopen: DirectoryInUseException
  git show release-2026.1:java/src/bergdb/stream/FileStream.java   # lines 92-121, 722-744
  ```


## R2-F4 (confirmed)

With `setMax2G(true)`, a reopen that picks a small file size from the last two files lets
the next rotation jump to 10 GB.

* Reasons. `determineFileSizeIndexFromFiles()` (lines 738-758) sets the index from the
  lengths of the last two files only: 100 MB files give index 4. At the next new file,
  `determineFileSizeIndex()` (lines 953-990) with a 40 GB stream finds `size` = 10 GB,
  `foundIndex` 7; `isMaxIndex` tests the old index (`4 >= INDEX_2G` is false); the
  stream length is a multiple of the one-up size (500 MB), so `result = 7`; the clamp at
  line 987 again tests the old index (`4 > 6` is false). The new file gets a 10 GB
  capacity, against `setMax2G` Javadoc (lines 366-370): "never use stream files larger
  than 2e9 bytes". The probe's sparse `FileStreamIo` only skips writing and forcing
  zeros; the file selection, rotation and accounting are production code, and it calls
  `setMax2G(true)` on every stream it opens. The output matches the finding (a 2,001,000,000
  byte file).
* Reach. Internal classes only. No code in `java/src` calls `setMax2G` outside
  `FileStream` itself, and Pub has no setting for it, so a database opened through Pub
  never sets the cap.
* Effect class. The documented cap is exceeded; on a file system with a file-size limit
  an append would fail and fail the stream. No data lost or invented, no wrong answer,
  no hang.
* 2026.1: yes; the same selection and clamp (its lines 425-445, 650-681).
* Still on main: yes; the same code at ca02b5e (lines 769-790, 995-1022).
* Commands (about 2 s; sparse files, removed by the probe):

  ```sh
  javac --release 17 -cp $JAR -d classes R2/Max2GProbe.java
  java -ea -cp classes:$JAR bergdb.core.Max2GProbe out
  # After 400 public-API write/reopen rounds: files=460; largest=100000000; length=40000000000
  # After setMax2G(true): largest=2001000000; files=461
  # Cap respected: false
  grep -rn setMax2G repo/java/src | grep -v stream/FileStream.java   # nothing
  ```


## R3-F6 (confirmed)

A storage thread that an interrupt takes out of its `wait` after `stop()` returns from
`runConsumer` without closing its underlying stream.

* Reasons. In `runConsumer` (lines 144-209) the `catch (InterruptedException)` at line 168
  returns when `stop` is set (lines 169-170); the only `stream.close()` of the thread is
  after the loop (lines 205-209), reached by `break A` and by the loop's end, not by that
  return. `stop()` (lines 687-694) only sets `stop` and notifies. The interleaving: the
  consumer waits in `wait()` or `wait(waitTime)` holding nothing; an interrupt removes it
  from the wait set; it must take the monitor of the `BufferedStream` again before the
  catch runs; `stop()` takes that monitor, sets `stop = true` and releases it; the
  consumer then gets the monitor, and the release of the monitor by `stop()` happens before
  its acquisition by the consumer, so the consumer reads `stop == true` and returns. The
  probe and the test force it by holding the monitor themselves until `stop()` has run,
  which is exactly the window `stop()` opens on its own when it takes the monitor while
  the consumer is blocked. That is against `stop()`'s Javadoc ("Eventually stops thread
  and closes stream") and 005-46, "Interrupts", change (g) (the storage thread goes on).
  The reflection in the probe only fetches the thread to interrupt it, as an interrupt
  from outside (`ThreadGroup.interrupt()`, 005-46's example) would.
* Reach. Through Pub only via the experimental `Database.removeReplica(name)`, whose
  `StorageManager.removeReplica` calls `b.stop()` on the replica's `BufferedStream`
  (line 699) and nothing closes it later; the replica's storage thread must get an
  interrupt from outside just as the stop comes. `Db.stop()` and `Db.close()` use
  `StorageManager.closeAndThrow()`, whose `BufferedStream.close()` joins the thread and
  then calls `stream.close()` itself (lines 653-671), which repairs the omission; a failed
  stream is closed by `handleStreamException`. `StorageManager.stop()` has no caller in
  `core` or `pubimp`.
* Effect class. A leaked stream: its file handles and its directory lock stay until the
  JVM ends, so a later open of that directory in the JVM is refused. Nothing was buffered
  that a stop promises to write (`stop()` does not write the buffer). No data lost or
  invented, no wrong answer, no hang.
* 2026.1: yes; its catch returns too when `stop` is set (and throws a `Bug` when not).
* Still on main: yes; at ca02b5e the catch (lines 168-176) still returns.
* Commands:

  ```sh
  javac --release 17 -cp $JAR -d classes r3/ConsumerStopInterruptProbe.java
  java -ea -cp classes:$JAR bergdb.core.ConsumerStopInterruptProbe out/tmp
  # consumer terminated after stop+interrupt: true
  # FAULT: terminated consumer left directory locked
  cd repo && git apply ../r3/r3-f6.patch && sh java/build.sh && cd java
  java -ea -cp build/bergdb.jar bergdb.dev.Unit -c bergdb.storage.BufferedStream \
      -m testStopAndInterruptClosesUnderlying
  # AssertionError: stop plus interrupt must close the underlying stream, expected true,
  # but was false.  FAILURE, total: 2, failed: 1.
  ```


## R3-F10 (confirmed)

A main stream whose storage thread fails a write does not fail the `Db`; cached reads go on
until a later append, sync or load meets the failure.

* Reasons. On a failed flush the consumer calls `stopAfterFailure` (lines 326-333), which
  reports to the append listener; `MyStorage.appendFailed` (lines 1053-1054) calls only
  `StorageManager.handleStreamException` (lines 765-799), which closes the stream, puts an
  `ErrorStorage` in its place in the `AtomicReference` and recomputes the rules. No code in
  `bergdb.storage` refers to `Db` (its own note: "No dependencies on Db"), so nothing sets
  `DbState.FAILED`. `getOne` and `getMany` admit a read by `assertDbStateIsActive` only
  (lines 1512, 1674), which reads `Db.state`, still `ACTIVE`; a get served from memory
  never touches the storage. The probe's run: after the consumer has ended (joined, so its
  failure handling is complete) the `Db` is active and a get returns `new`, the value of
  the transaction whose write failed; the next `execute` throws `DbFailedException`. That
  is against 010-01, P7 ("A database whose environment has failed (an I/O error ...) does
  not run on. It fails: the call throws, and so does every later transaction and read").
  docs/levels.md, section 3 lists the failures that fail the database by the call that
  meets them (a transaction after its go point, a read or sync that fails on the
  storage) and does not name a failure on the storage thread, so the gap is between P7's
  rule and the triggers that implement it. The probe uses `Db.builder().testSetup(stream)`
  with a `MemoryStream` that fails `append`, the same injection the failure tests use; the
  Pub equivalent is a disk that fails a background write.
* Reach. Through Pub in normal use, on an I/O error (disk full, a device error) in the
  background write of a database on a directory, followed by a workload of reads that hit
  memory: they go on for as long as no transaction, `sync()` or cache miss comes.
* Effect class. The database runs on after a known failure; reads answer from memory,
  including the transaction whose record the failure kept off the disk and that a restart
  will not have. No further data lost or invented, no hang. Whether that is a wrong answer
  depends on reading P7 strictly; by P7, the read should have thrown.
* 2026.1: yes; its `appendFailed` also calls only `handleStreamException` (its line 1028),
  and its reads check `Db`'s own state.
* Still on main: yes; `BufferedStream.java`, `StorageManager.java` and `Db.java` are
  unchanged from b1651a5 to ca02b5e (`git diff --stat b1651a5 ca02b5e -- java/src`).
* Commands:

  ```sh
  javac --release 17 -cp $JAR -d classes r3/BackgroundFlushFailureProbe.java
  java -ea -cp classes:$JAR bergdb.core.BackgroundFlushFailureProbe
  # failed consumer terminated: true
  # database active after consumer join: true
  # cached read accepted after storage failure: new
  # database fails only on next append: true
  ```


## R3-F11 (confirmed)

`deleteIndex` by an interrupted thread commits the deleting state and then throws from its
interruptible sync, before it starts the deletion's thread.

* Reasons. `deleteIndexInternal` (lines 303-337) calls `ensureDeletingState`, which commits
  the index's deleting state, then `sync(SyncLevel.ORDINARY)` (line 311), and only after
  that makes and starts the thread. `Db.sync` (lines 1801-1814) turns the
  `InterruptedIOException` of `storageManager.sync` into a `StreamIoException`, by design
  for a public sync (005-30). So an interrupt before or during that wait ends
  `deleteIndex` with an exception: no `Job` returned, no thread started, the index left
  deleting and its name taken. `Database`'s class Javadoc (lines 37-43) names three calls
  that an interrupt ends, `sync()`, `Job.join()` and a transaction's wait to rerun, and
  says "Every other call ignores an interrupt until it is done"; `deleteIndex` is not one
  of the three, and its Javadoc says it "Starts and returns a Job". Same in 005-46,
  "Interrupts", the rule. The probe holds the stream's append on a latch so the sync
  really waits, and calls the Pub `deleteIndex` from a thread with its flag set, as a
  `Future.cancel(true)` or `shutdownNow()` can leave it; it releases the latch and joins
  the resumed job. Output as the finding.
* Reach. Through Pub in normal use: `Database.deleteIndex(name)` on a thread that is
  interrupted before or during the call (an executor's cancel or shutdown).
* Effect class. A call that throws after it has accepted the work: the index stays in its
  deleting state and its name taken, with no deletion running, until a restart (which
  resumes it, as the probe shows) or another `deleteIndex`. No data lost or invented, no
  wrong answer from reads, no hang.
* 2026.1: yes; the same order (its lines 273-281) and the same interruptible sync (its
  `Db` lines 1576-1580).
* Still on main: yes; at ca02b5e `deleteIndexInternal` still calls
  `sync(SyncLevel.ORDINARY)` (line 318) after `ensureDeletingState` and before it makes and
  starts the thread; `Db.java` is unchanged.
* Commands:

  ```sh
  javac --release 17 -cp $JAR -d classes r3/DeleteCallerInterruptProbe.java
  java -ea -cp classes:$JAR bergdb.core.DeleteCallerInterruptProbe
  # deleteIndex threw: InterruptedIOException
  # caller interrupt retained: true
  # database still active: true
  # delete workers started: 0
  # index name still occupied after interrupted deletion: true
  # restart resumes delete jobs: 1
  ```


## R3-F5 (confirmed)

An index build whose step meets an STM conflict with its thread's interrupt flag set dies
with a `DbException`; the index stays creating for the rest of the run.

* Reasons. The build's step runs `connection.rw(action)` (`createStep`, line 438), so a
  conflict goes through `RwTransaction.executeRw`'s rerun loop (lines 118-140), whose
  `Thread.sleep` throws at once when the flag is set, and the catch throws a `DbException`
  ("The transaction was not run ..."), as 005-46, change (f) wants for an application's
  call. The worker in `createInThread` (lines 311-325) catches only `StreamIoException`,
  `DbStoppingException` and `DbFailedException`; `createStep` catches only
  `DbStoppingException` around the `rw`. So the `DbException` ends the thread as uncaught,
  `createState.isDone` stays false, and nothing restarts the build until the database
  restarts. The flag can be set during a step: an interrupt that arrives while the worker
  works (not in a wait) stays pending, and the pause between steps
  (`sleepFiftyPercentOfDuration`, lines 349-367) clears it only if it arrives there. That
  is against 005-46, "Interrupts", change (g) ("the index jobs' threads" go on when
  interrupted) and `IndexBuilder.start()`'s Javadoc (the index is CREATING "until the job
  finishes and the index state becomes ACTIVE"; it continues after a restart only if the
  database is stopped). The probe's `Db.getMany` override only pauses the worker after
  its scan, so that an application's put conflicts with it, and sets the flag there, as
  `ThreadGroup.interrupt()` could; the conflict and the refusal are the production code's.
* Reach. Through Pub in normal use: `IndexBuilder.start()` while the application writes
  objects of the indexed directory, and an interrupt from outside reaches the build's
  thread during a step (for example `ThreadGroup.interrupt()` on a group that holds it;
  the build's thread is made by the caller's thread, in its group).
* Effect class. A stalled job: the index stays CREATING and cannot be used until a
  restart, `Job.join()` returns at once with progress -1, and no error is exposed. No data
  lost or invented, no wrong answer, no hang of a call (an application that waits for the
  index to become active waits until it restarts the database).
* 2026.1: yes; its retry sleep threw a `RuntimeException` (its `RwTransaction`, lines
  128-130), which the same three catches did not catch either.
* Still on main: yes; at ca02b5e `createInThread` (lines 319-337) has the same three
  catches, `createStep` (lines 462-475) adds only `IndexDeletedException`, and
  `RwTransaction.java` is unchanged.
* Commands:

  ```sh
  javac --release 17 -cp $JAR -d classes r3/BuildInterruptProbe.java
  java -ea -cp classes:$JAR bergdb.core.BuildInterruptProbe
  # build worker terminated: true
  # uncaught failure: bergdb.pub.util.DbException: The transaction was not run: the thread
  #   was interrupted while it waited to run it again after a conflict.
  # job progress after join: -1
  # database active: true
  ```


## R3-F4 (confirmed)

`Jmx.Speed`'s monitor thread ends on an interrupt, `registerAndStart` then does not start
it again, and an interrupted `stop` returns before the thread ends and clears the flag.

* Reasons. `Speed.run` (lines 323-342) does `break A` on an `InterruptedException` from its
  `Thread.sleep(1000)`, with `stop` false, and leaves `thread` set. `registerAndStart`
  (lines 293-307) returns at once when `thread != null` ("already running"), so it does not
  start a new thread. `stop` (lines 310-320) catches the `InterruptedException` of
  `thread.join()` with an empty block: the caller's flag is cleared, and it unregisters the
  bean and sets `thread = null` while the old thread may still run. Against 005-46,
  "Interrupts", the rule ("BergDB never swallows an interrupt. BergDB's own threads go on
  when something interrupts them"); the eviction thread is the one named exception. The
  probe interrupts the monitor in its sleep, then (with a `Db` whose
  `getTransactionCount` pauses on the monitor's thread) calls `stop()` with the caller's
  flag set; reflection only reads the `thread` field. Output as the finding.
* Reach. Internal classes only. No code in `java/src` other than `Jmx.java` makes a
  `Jmx.Speed` or calls `registerAndStart` (`DbTester` and `CapacityTester` use
  `Jmx.DbMonitor` only), and neither Pub nor `Db` starts it; an application that starts
  `bergdb.core.Jmx.Speed` itself meets it.
* Effect class. Monitoring only: the bean's speeds stay at their last values (a stale
  value of a monitoring bean, not a wrong answer of the database), a stop may leave the
  thread running a little longer, and the caller's interrupt is lost. No data lost or
  invented, no hang.
* 2026.1: yes; the same `run` break, `registerAndStart` check and empty catch in `stop`
  (its lines 314-341, 361-363).
* Still on main: yes; `Jmx.java` is unchanged from b1651a5 to ca02b5e.
* Commands:

  ```sh
  javac --release 17 -cp $JAR -d classes r3/JmxInterruptProbe.java
  java -ea -cp classes:$JAR bergdb.core.JmxInterruptProbe
  # monitor died on interrupt while stop=false: true
  # registerAndStart retained dead thread: true
  # interrupted stop lost caller flag: true
  # stop returned with monitor alive: true
  grep -rn "Jmx.Speed\|registerAndStart" repo/java/src | grep -v core/Jmx.java   # nothing
  ```


## R3-F7 (confirmed)

The `JobStatus` of an index build reads the build's counter when `note()` is called, so one
status object changes its text as the build goes on.

* Reasons. `IndexCreateState.getJobStatus` (lines 512-531) captures `progress` in a final
  local under the state's monitor, but the anonymous status's `note()` reads the outer
  field `processedEntries` (a plain `public long`, line 482) at each call, outside the
  monitor; the worker sets it in `update` (lines 507-510) under the monitor. The
  `JobStatus` contract (its class Javadoc, line 4): "implementations must be immutable".
  The test and the probe hold the worker on its start event
  (`createInThreadWaitEvent`, a test hook of `IndexBuilderImp`, used only to order the
  steps), take a status, let the build finish and join it, and read the same status
  again: `Working, processed 0 ...` becomes `Working, processed 2 ...`, with `progress()`
  still -1. The join gives the second read a happens-before edge, so the observation is
  deterministic; while the job runs, the read has no edge to the worker's write, so it
  may also see an older value (and, by JLS 17.7, a non-volatile `long` may be read torn).
* Reach. Through Pub in normal use: `IndexBuilder.start()` returns a `Job`; a status from
  `Job.getStatus()` that the application keeps and reads later (a log line, a progress
  display) shows newer counts than its `progress()`.
* Effect class. A wrong answer of a status object (its note), monitoring text only; the
  index and its data are right. No data lost or invented, no hang.
* 2026.1: yes; the same anonymous status reads the outer counter (its lines 511-532).
* Still on main: yes; at ca02b5e `getJobStatus` (lines 564-586) captures `progress` and a
  new `stopped`, and `note()` still reads `processedEntries` at the call.
* Commands (the patch adds the test only; built with it applied, as for R3-F6):

  ```sh
  cd repo && git apply ../r3/r3-f7.patch && sh java/build.sh && cd java
  java -ea -cp build/bergdb.jar bergdb.dev.Unit -c bergdb.pubimp.PubTesterIndex \
      -m testBuildJobStatusIsImmutable
  # AssertionError: JobStatus.note must be immutable, expected 'Working, processed 0
  # entries for index: amount.', got 'Working, processed 2 entries for index: amount.'.
  # FAILURE, total: 2, failed: 1.
  cd ../.. && javac --release 17 -cp $JAR -d classes r3/JobStatusProbe.java
  java -ea -cp classes:$JAR bergdb.core.JobStatusProbe
  # same JobStatus note before: Working, processed 0 entries for index: amount.
  # same JobStatus note after:  Working, processed 2 entries for index: amount.
  # FAULT: immutable status changed: true
  # old status progress remains: -1
  ```
