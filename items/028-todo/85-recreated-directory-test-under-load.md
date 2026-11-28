028-85. Fix: PubTesterJavadocNewUsers.testNewDatabaseWhereAStoppedOneWasDeleted fails under load
================================================================================================

Status: done (2026-11-28): the test deletes the directory after
`close()`, as `stop()`'s Javadoc says; the window in a test of its own.
Kind: Fix. Frans: none.
Created 2026-11-28 by Frans Lundberg.

What: `java/stress/level3.sh` failed once on 2026-11-28, under a load
average of about 20 on F53, in its unit tests:
`PubTesterJavadocNewUsers.testNewDatabaseWhereAStoppedOneWasDeleted`
threw "Could not find *any* valid meta block ... The stream begins at
200000 ... first file ... 00000000000002.bergdb". The rerun passed, and
the test passed 40 times of 40 alone (an agent of lead-1127, on the
branch of 028-81 and 028-82, which do not touch the window below).

The test (020-24-10's U10 case, 021-20): a database puts 1 MB, which is
still in its write buffer, and `stop()`s; the test deletes the
database's directory at once, while the old database still writes in
the background, starts a new database at the same path (retried while
the old one holds it), puts and syncs, and checks the new database's
value after a restart.

Why, by reading: the window that 021-20 and 021-24 left open.
021-20 refuses a start at the path while the old database is open, and
makes the old database fail at its next stream file instead of making
it in the directory now at the path; 021-24 moved `FileStream`'s check
of the directory after the force before a new file, and checks again
after the step. Left, as 021-24 ("Left") states: a replacement of the
directory in the short window between the check and the step, usually
microseconds, longer when the thread is paused, as by a GC or a
preempted thread on a loaded machine. Then the old database's step is
done in the new directory before the check after it fails the stream: a
new, empty stream file there, or at a cut the new directory's file of
that name deleted. The failure's "The stream begins at 200000 ... first
file 00000000000002.bergdb" fits the second: the old database's cut,
after its records, deleted the new database's first file. Not proved:
the failure was not reproduced.

Frans: none. 021-24 put two later changes on his list in 2026-11:
`SecureDirectoryStream` (opens and deletes relative to an open
directory, which closes the window) and clearer refusals beside such a
file.

Done when: the failure reproduced (a hook that holds the old database
between `checkDirectory()` and its step, as 021-24's
`DirectorySwitchProbe` held the force) and one of: the window closed in
the code; or the test made to test what the documents promise, which
`Database.stop()`'s Javadoc states with its "Otherwise" (a directory
deleted before the close is done may get the old database's step), so
that it waits for `close()` before it deletes the directory, with the
window kept in a test of its own that expects the documented outcome;
and the test passing under load (`level3.sh` with other heavy runs
beside it).

First step: the test, 021-24's section "Left" and `Database.stop()`'s
Javadoc; whether the cut's delete is in the window as the step is.


Log
---

2026-11-28. Registered by lead-1127 from `level3.sh`'s failure on the
branch of 028-81 and 028-82.

2026-11-28. Done by an agent of lead-1127 (branch `028-85`, on main's
`d75dec96`).

* The cause, shown: 021-24's window, its first case, not the cut. A
  probe ran the test's steps with the old database on a `FileStream`
  whose `FileStreamIo.open()` of a new stream file, after
  `checkDirectory()` and before the file is made, sleeps a while (a
  delay at the window's point). The old database's writer, still
  writing the 1 MB after `stop()`, passes the check before its second
  file, `00000000000002.bergdb` at 200000; the test deletes the
  directory, and its start at the path, refused as in use, makes it
  again; the old database then makes its file there, empty, and fails
  at the check after. Once the old database has closed, the retried
  start finds that empty file alone and throws the failure of
  `level3.sh`: `StreamFormatException`, "Could not find *any* valid
  meta block ... The stream begins at 200000 ... The stream's first
  file in ... is 00000000000002.bergdb"; the directory holds
  `00000000000002.bergdb` (0 bytes) and `bergdb.lock`. A cut cannot
  meet a new database's file in this test: the new database starts
  only after the old one has closed.
* The documents: `Database.stop()` says to delete the directory only
  after `close()` has returned, and states this outcome for a
  replacement in the window ("leaves an empty stream file in the new
  directory ... a start there is refused until the empty file is
  removed"); `close()` waits for the close that `stop()` began. The
  test deleted the directory right after `stop()` and expected the
  start to be taken, which the documents do not promise. No product
  finding: the code does what the Javadoc states.
* Fix, in the test only, `PubTesterJavadocNewUsers`:
  * `testNewDatabaseWhereAStoppedOneWasDeleted` follows `stop()`'s
    Javadoc: it calls `close()`, which waits, before it deletes the
    directory; `startRetried()` is gone.
  * `testDirectoryReplacedInTheWindowAfterStop`, new, keeps the case
    with the documented outcome, made on purpose: the old database's
    writer is held by a `FileStreamIo` in the window, at its first new
    file after the start, until the directory is deleted after
    `stop()` and the start at the path is refused as in use (and has
    made the directory). Released, the old close throws
    `StreamIoException` ("is no longer"); the new directory has one
    stream file, that one, of 0 bytes; a start throws
    `StreamFormatException` ("valid meta block") until it is removed,
    and then keeps its value, with nothing of the old database. No
    timing decides it (latches; 60 s hang guards).
  * The window itself is not closed: `SecureDirectoryStream` stays on
    Frans's list (021-24).
* Repetitions, the probe, 200 each (load average 13 to 24 from other
  runs on F53): the old steps with no delay 200 of 200 passed (the
  window is too short to meet without a pause), with a delay of 2 ms
  60 failed, of 30 ms 49 failed, each with the message above; the new
  steps (`close()` before the delete) with the same delays, 0 failed
  of 200 each. The tests in one JVM, 300 times each (load average 13
  to 15): `testNewDatabaseWhereAStoppedOneWasDeleted`,
  `testDirectoryReplacedInTheWindowAfterStop` and
  `testDirectoryDeletedWhileTheDatabaseRuns`, 300 of 300 passed each.
