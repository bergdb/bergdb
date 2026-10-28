005-63. Decide: one database per directory, also while one closes
================================================================

Status: done (2026-10-28; see Outcome). Kind: decide. Created 2026-10-27.
Updated 2026-10-28 with Frans: option B worked out as a lock file,
`bergdb.lock`.

Found on 2026-10-27 by Claude (Opus 5.5, Claude Code) in 006-09, when
`level2.sh`'s step 6 (`BryanRepro`) failed on `main` from `eaec93e`
(005-46) on; registered by the session for Frans to decide. The cause, the
evidence and the test's fix are in
[006-09's note](../006-2026-q4/09-unattended-27-28-october/bryanrepro.md).
Decided by Frans on 2026-10-28 (Decision), and made as decided (Outcome).


Decision
--------

2026-10-28, 08:13, Frans: "Implement and commit bergdb 005-63; as
proposed, Option C. Add a comment to the Javadoc for the FileStream class
with a note about Network File Systems."

Two answers while it was made, about 08:30:

* Within the JVM (a hole in point 6, found when it was made; Outcome): a
  set of the directories that the JVM's `FileStream`s hold, checked before
  the lock file is opened, as recommended, though it is global state
  (010-P9).
* The exception (the question left open below): "Search for other
  exceptions. I think there is something like a DatabaseStreamException or
  similar. More specific than IOException. Use a subclass of that if you
  find it suitable. Otherwise, use DirectoryInUseException as proposed."


The issue
---------

`stop()` returns before the database is closed (005-35): a thread of its
own writes what is buffered and closes the streams. Since 005-46, a cut's
files are also deleted afterwards, by the `FileStream-cut` thread, and the
close waits for it. A program that starts a database on the same directory
right after `stop()` therefore has two databases on one directory for a
while. In `BryanRepro`, cycle 39's start listed the directory while cycle
38's cut was still deleting 60 files, took the 52 left as its own, cut 46
of them again at start (`Reclaim.initFromDb`), and its first delete failed,
as the old thread had deleted that file; the next read then failed the
database (010-P7). No data was at risk: every deleted file lay below the
cut, which is durable before any cut (`cutIfDurable`). The test now ends
each cycle with `close()`, which waits (`b0661ba`).

The same holds before 005-46 for what `stop()` still writes: a second
database that opens the directory before the first has written its buffer
reads a stream that is still growing.

Today nothing refuses a second `FileStream` on a directory. The only check
is in `DbFile.append()`: an append compares the file's length with the
expected one ("Alternative to lock file", Frans, 2013-08-18), which finds
another writer only after it has written.


The lock file
-------------

`FileStream` holds an operating-system lock on a file of its own in its
directory, for as long as it is open. A second `FileStream` on the
directory fails at once, with a clear message, before it reads anything.

1. **The file.** `bergdb.lock`, in the stream's directory, beside the
   `.bergdb` files and `created.txt`. It does not end with `.bergdb`, so
   the stream's listing (`getSortedDbFiles()`) ignores it. It is a
   separate file because the `.bergdb` files are deleted by cuts, and
   `created.txt` is written later, by `Db`, and only for a new database.

2. **Its text.** Written once, when `FileStream` creates the file, and
   never changed:

       This directory contains a BergDB database. BergDB locks this file
       while a database has the directory open. The lock is held by the
       operating system and ends with the process. Do not delete this file
       while a database is open.

   No process ID, no time: after a crash they would be stale, and a lock
   that cannot be stale is the point. The text is for people; the lock
   does not depend on it.

3. **Never deleted.** Neither `close()` nor `seekFirstPos()` deletes it.
   Deleting a lock file is itself a race: if one instance deletes it while
   another holds its lock, a third creates a new file of the same name and
   locks that, and two instances hold "the" lock. Whether the file exists
   means nothing; only its lock does.

4. **The lock.** An exclusive lock on one byte far beyond the end of the
   file: `channel.tryLock(LOCK_POS, 1, false)` with `LOCK_POS = 2^62`.
   Java and the operating systems allow a lock on bytes that do not exist.
   On Windows a lock is mandatory: no other program can read the locked
   bytes, so a lock on byte 0 would hide the text while the database is
   open. Beyond the end, the text stays readable everywhere. On macOS and
   Linux Java uses `fcntl` locks, on Windows `LockFileEx`.

5. **The order.** The constructor creates the directory if needed (as
   today), opens or creates `bergdb.lock`, writes the text if the file is
   new, takes the lock, and only then lists the `.bergdb` files. `close()`
   releases the lock last: after the cut's thread has deleted its files
   and after the stream's files are closed. A failed open
   (`closeAfterFailedOpen`) releases it too. The lock file is not forced:
   if a power loss loses it, the next start creates it again.

6. **Refused.** If `tryLock` returns null (another process holds the
   lock) or throws `OverlappingFileLockException` (another `FileStream`
   in the same JVM holds it), the constructor closes the channel and
   throws an `IOException`: "Directory X is in use by another BergDB
   database (bergdb.lock is locked)." The start fails at once; nothing in
   the directory has been read or changed. Changed when made (Outcome):
   closing that channel released the first's lock for other processes,
   so a set of the JVM's locked directories refuses first, without
   opening the file, and the exception is `DirectoryInUseException`.

7. **Crashes.** The lock lives in the kernel's memory, never on disk.
   When a process ends, however (`kill -9`, a JVM crash), the kernel
   closes its files and drops its locks; after a machine crash or a power
   loss no lock exists. The next start takes the lock at once, with no
   cleanup. A process that hangs but does not end keeps the lock, which
   is right: it may still write.

8. **Network file systems.** On NFS or SMB the server holds the lock; a
   client that crashes may keep it until the server notices (NFSv4: a
   lease, typically 90 s), and some setups do not support locks at all.
   BergDB's databases belong on local disks anyway, for the hard sync.

9. **Existing databases.** A directory from 2026.1 has no `bergdb.lock`;
   the first open creates it. Nothing else in the format changes.

10. **For `BryanRepro`'s case.** A start right after `stop()` fails at
    once with the message of 6, instead of failing the database later at
    a delete or a read. To start again, a program waits for `close()`, as
    the test does since `b0661ba`. A start that waits for the lock could
    come later, if a program needs it.

Several instances on one directory (one writer, read-only readers) are not
considered now (Frans, 2026-10-28).

**Tests.**

* A second `FileStream` on the directory in the same JVM is refused, with
  the message; after the first's `close()`, a new one opens.
* A `FileStream` in a child JVM holds the directory: the parent's open is
  refused; after the child is killed (`destroyForcibly`, as `kill -9`),
  the parent's open succeeds.
* `bergdb.lock` is not taken for a stream file, and its text is the same
  after a close and a new open.
* A directory without `bergdb.lock` (as from 2026.1) opens, and gets one.
* `Database`: a start on a directory whose database is stopping fails
  with the message, and starts after `close()`.


Options
-------

A. **Say it.** `Db.stop()`'s and `Database.stop()`'s Javadoc: start another
   database on the same directory only after this one is closed (`close()`
   returned).
B. **Refuse it.** The lock file above.
C. **Both.**
D. **Nothing.**

Recommended: C. B turns a race that can fail a database into an
immediate, clear error, at the cost of one file in the directory, a small
change to `FileStream` and the tests above. A is one sentence, and tells a
program what to do when B refuses it.

Open, for Frans, with C or B: whether the refusal gets an exception class
of its own (a subclass of `IOException`, such as
`DirectoryInUseException`) so that a program can tell it from other
failures to start, or a plain `IOException` with the message. Decided:
`DirectoryInUseException` (Decision, Outcome).


Done when
---------

Frans has decided; with B or C, the lock file in `FileStream` with the
tests above, `releases/next.md` updated, and `before-commit.sh` and
`level3.sh` pass.


First step
----------

Frans's decision.


Outcome
-------

2026-10-28, by Claude (Opus 5.5, Claude Code), as decided; in a clone on
`fadefe3` with the main tree's uncommitted edits of this entry and of
`FileStream`'s class Javadoc, the code in commit `322c5d1` (java/ and
releases/next.md).

* **The lock.** `FileStream`'s constructor calls `lockDir()` after
  `createDirIfNeeded()` and before it lists the `.bergdb` files: it
  creates `bergdb.lock` with the text of point 2 if it does not exist,
  opens it and takes `tryLock(2^62, 1, false)`. `close()` releases it
  last, after the cut's thread and the files; so does a failed open
  (`closeAfterFailedOpen`). Points 1 to 5, 7 and 9 as written.
* **A hole in point 6, and the set.** A probe on F53 (macOS, JDK 27),
  before the code: a second channel's `tryLock` in the same JVM throws
  `OverlappingFileLockException`, as expected, but closing that channel
  released the first channel's lock in the operating system (POSIX
  record locks belong to the process and the file; `FileLock`'s Javadoc,
  "Platform dependencies"), and a child JVM then took the lock while the
  first `FileStream` still held it. So a refusal in the same JVM, as
  point 6 had it, opened the directory to other processes. Frans chose a
  set of the JVM's locked directories (`LOCKED_DIRS`, static), filled
  before the lock file is opened: a second `FileStream` in the JVM is
  refused without touching the file. Its key is the directory's file key
  (device and inode on macOS and Linux), so that another path to the
  directory finds it, or the real path where there is none (Windows,
  where closing a handle releases only that handle's locks). Lucene's
  `NativeFSLockFactory` and SQLite do the same. It is global state, a
  deviation from 010-P9, which `FileStream`'s Javadoc states, and 010-01's
  list of where BergDB stands on P9 (added the same day). A lock that
  other code in the JVM holds (`OverlappingFileLockException`) is refused
  too.
* **The exception.** The class Frans remembered is `StreamException`
  (`bergdb.storage`; a `DbException`, so unchecked; subclasses
  `StreamFormatException` and `StreamIoException`). Not suitable:
  `bergdb.stream` depends only on common, nanotest and pub.util (its
  `package.html`, 005-56), and `FileStream` reports its failures as
  `IOException`s, as `BadDirStateException` does. So
  `bergdb.stream.DirectoryInUseException extends IOException`, beside
  `BadDirStateException`, as proposed. A Pub program gets it as the cause
  of the `StreamIoException` that `DatabaseBuilder.dir()` throws, as for
  any failed open; `DatabaseBuilder.replica()` and
  `Database.addReplica()` throw it as it is. The messages: "Directory X
  is in use by another BergDB database in this JVM (bergdb.lock is
  locked)." and "... (bergdb.lock is locked by another process)."
* **Interrupts.** `lockDir()` is not interruptible, as the rest of the
  class: it clears the thread's flag and sets it again after, writes the
  text with `java.io`, and takes the lock again if an interrupt during
  `tryLock()` closed the channel. `testCutAndOpenByInterruptedThread` and
  `InterruptTester` open streams with the flag set.
* **Javadoc (A).** `FileStream`'s class Javadoc: one stream per
  directory, and network file systems, at Frans's request (the server
  holds the lock; a crashed client's may stay until the server notices,
  NFSv4's lease, typically 90 s; where the file system has no locks the
  constructor fails, and with NFS's `nolock` the lock refuses only
  streams on the same machine; use a local disk). `Db.stop()` and
  `Database.stop()`: start another database on the directory only after
  `close()` has returned. `DatabaseBuilder.dir()`: the refusal and its
  cause.
* **Tests.** In `FileStream`: `testSecondStreamRefused` (also by the path
  `dir/.`; the first stream goes on; a new one opens after its close),
  `testLockFile` (the text; not a stream file; the same after appends, a
  cut, a close, a new open and `seekFirstPos()`; a directory without it
  opens and gets one), `testLockAcrossProcesses` (an f-test: a child JVM
  holds the directory and the open here is refused, then opens after
  `destroyForcibly()`; a child is refused while this JVM holds the
  directory, also after a refusal here), and `testRestartMissingFile`
  (a failed open releases the lock). With the set disabled,
  `testLockAcrossProcesses` fails: "Expected 'refused', got 'opened'".
  In `PubTester`: `testStartWhileStoppingRefused`, a start right after
  `stop()`, with the close held on a force, is refused with the cause
  `DirectoryInUseException`, and starts after `close()`.
* **Tests that restarted right after `stop()`** on the same directory now
  call `close()`, as `BryanRepro` has since `b0661ba`:
  `FileStreamPowerLossTester.verify` and `ReclaimReaderTester` (both
  refused in the f-tests), `RestartStress` (level 2; with `-Dfile` it
  always stops before a restart), `ReclaimReaders` (level 3, `-Ddisk`),
  `LargerThanMemory` (level 4) and `BryanIssue` (`BryanIssueNight`, a
  night test). `StorageManagerTester.testSync4` counted every file in the
  directory; now the `.bergdb` files.
* Left as it is: a `DatabaseBuilder` whose `dir()` succeeded and that is
  never started keeps the directory until the JVM ends, as it kept its
  open file before; a failed `start()` closes its streams (005-32).
* Gates, in the clone: `java/before-commit.sh` (unit 1055 tests, f 74,
  `BEFORE COMMIT OK (90 s)`, also on the final tree), `level3.sh` full
  (`LEVEL 3 OK`, 8 minutes), `level2.sh` full (`LEVEL 2 OK`, 12 minutes;
  `RestartStress` on files and `BryanRepro` among its steps) and
  `level4.sh quick` (`LEVEL 4 OK`, 3 minutes; `LargerThanMemory` among
  its steps).
