021-20. Fix: a deleted directory's database writes into a new one at its path
============================================================================

Status: done. Kind: Fix. Frans: none.
Created 2026-11-09 by Frans Lundberg.

What: a database's directory deleted after `stop()`, while the database
still writes in the background, or while it runs, and a new database
created at the path at once. The start at the path is taken, and the old
database creates its next stream files by name in the new directory: the
new database fails to start (`StreamFormatException`), or loses its synced
data, with no error to either (U10-1, high). Found by a new-user
application, 020-24-10; the reproduction `ProbeRecreate.java` (cases `b2`
and `c`) in `/Users/f/fl/bench/2026-11-09/app-u10/app/src/`. With it, the
other findings of 020-24-10 asked for by coord-1109: the bugs U10-3, U10-5
and U10-6, and the Javadoc of U10-2, U10-4, U10-7 and U10-9 (020-24's
commits).

Why: deleting a closed document's database and making a new document of
the same name is ordinary for an application with one database per
document, and `stop()`'s Javadoc says that a start there is refused until
the close is done. A database must not damage another one silently.

Frans: none. U10-8 (in use told by a class outside the API; the Core's
words in messages) is on his list, not here.

Done when: ProbeRecreate's two cases as unit tests that fail before; a fix
within today's stream format and without new API so that neither case
writes into the new directory; the Javadoc says when a database's
directory may be deleted; `BEFORE COMMIT OK`, `JAVADOC PUB OK` and
`java/stress/level1.sh` under the gate lock; lines in `releases/next.md`.

First step: what keys the lock in the JVM, and what FileStream opens by
name.


Log
---

2026-11-09. Registered by coord-1109 from 020-24-10's U10-1 (and U10-2 to
U10-7, U10-9), and taken by its agent l20 (clone `clone-l20`, on main's
595418e).

2026-11-09. Done by l20: commits 3a18e8f (021-20, U10-1), 0ad6fe1
(020-24, U10-3), 1b2c363 (U10-5), b47b33a (U10-6) and 4824aa3 (U10-2,
U10-4, U10-7, U10-9, Javadoc only) in `clone-l20`, on main's 595418e, to
land. In 2026.1 to 2026.3 (005-63 made the lock).

* Why it happened. The lock is `bergdb.lock` in the directory and, in the
  JVM, `FileStream`'s set `LOCKED_DIRS` keyed by the directory's file key
  (device and inode); a new directory at the path is another directory,
  so neither refuses the start. `FileStream` makes each new stream file as
  `new File(dir, name)`, deletes a cut's files and opens a file again
  after an interrupt by name too, so the old stream wrote into, or would
  delete from, whatever directory is at the path.
* Fix, two parts, both in `FileStream`. (1) The lock in the JVM holds the
  directory's real path beside its file key (`pathKey()`, "path " and
  `toRealPath()`), in `LOCKED_DIRS` and in the system properties of
  015-24: a start at the path is refused as in use (cause
  `DirectoryInUseException`, "one started on the directory that was at
  this path, deleted, moved or replaced since, is still open or closing")
  until the stream that opened the directory there has closed. That keeps
  `stop()`'s promise for a deleted directory too; a refused start has made
  the directory if it was missing, and nothing else. (2)
  `checkDirectory()`, before each new stream file, each delete of a cut
  and each reopen of a file after an interrupt: if the path's file key is
  not the one locked, the stream fails ("Directory P is no longer the
  database's directory: it was deleted, moved or replaced while the
  database had it open. Nothing more is written there."), and the
  database with it (`DbFailedException`), or the background close after
  `stop()` (a `StreamIoException` of `close()`). Part 1 alone left the
  old database writing into a directory that the refused start, or the
  application, made at the path; part 2 alone let the new start in while
  the old one ran. Not caught: a replacement between the check and the
  step (microseconds); another process at the path (it sees only
  `bergdb.lock`, as before); on Windows the key is the path, but a
  directory with open files cannot be deleted there. Until its next
  stream file, a database whose directory was deleted writes into its
  open, unlinked file, and its `sync()` returns: that data is in the
  deleted directory, gone with it.
* Javadoc: `Database.stop()` says to delete, move or replace the
  directory only after `close()` has returned, and what happens
  otherwise; `DatabaseBuilder.start()` that a start at such a path is
  refused.
* Tests, each failing before: `FileStream`'s
  `testNoNewFileInAReplacedDirectory` (a second stream at the path, then
  the next file) and `testNoDeleteInAReplacedDirectory` (a cut deleted the
  new directory's file of the same name); `PubTesterJavadocNewUsers`'s
  `testNewDatabaseWhereAStoppedOneWasDeleted` (ProbeRecreate `b2`; threw
  "Could not find *any* valid meta block") and
  `testDirectoryDeletedWhileTheDatabaseRuns` (ProbeRecreate `c`; the start
  was taken).
* ProbeRecreate on the fixed build: `b2`, the start at the path is taken
  once the old close is done, and the reopened database has `/new.txt`;
  `c`, the start at the path is refused as in use while the old database
  is open.
* The other findings of 020-24-10, one commit each:
  * U10-3 (bug, medium): `BufferedStream`'s ring buffer, 10 MB, is
    released when its thread ends, after the close of the underlying
    stream, and by `close()` of a stream whose thread never ran; the
    thread ends only after stop, and every way to stop sets the stream's
    exception first, so later appends and reads throw before using it.
    ProbeRetain, 30 closed databases kept: 16 MB of heap after GC, 0.54
    MB each (331 MB before); memory databases 1.6 MB each (their data;
    362 MB before). Tests `BufferedStream.testBufferReleasedAtTheEnd`,
    `PubTesterJavadocNewUsers.testClosedDatabasesHoldLittleHeap` (10
    kept: 135 MB before; below 30 MB required).
  * U10-5 (bug, low): `createDirIfNeeded()` throws "could not be
    created" only if `mkdirs()` returned false and the directory is not
    there; the lock then refuses the losers as in use. ProbeMkdirs: 30
    taken, 210 refused as in use, no other exception (159 before). Test
    `FileStream.testConcurrentOpensOfANewDirectory`.
  * U10-6 (bug, low): `StorageManager`'s close, when the main stream's
    close worked, sets the durable length to the stream's confirmed
    length; the close sets the storage's error first, and its own flushes
    were ignored. `sync()` after `close()`, or after `stop()` once the
    close is done, returns; during the background close it throws for a
    transaction not yet durable, as before (U3-3). ProbeSync: all five
    cases return. Test `PubTesterJavadocNewUsers.testSyncAfterClose`.
    Returning is right by design: the Javadoc said so, and close() has
    forced every transaction.
  * Javadoc: U10-2 (the write buffer, 10 MB of heap per started
    database, whatever its data; no setting in 2026.4), U10-4 (`stop()`
    then `System.exit()`, or in a shutdown hook, can lose returned
    transactions: call `close()` there), U10-9 (the write buffer and the
    buffer time, 50 ms), U10-7 (what `getStartupDuration()` includes and
    leaves out), in `Database`, `DatabaseBuilder.startupDistanceInMb()`,
    `StartupInfo` and the package's "Good to know".
* For Frans's list (API wishes, not done): a setting of the write buffer,
  or a buffer that grows with use (U10-2); U10-8.
* `releases/next.md`: Pub API (021-20, U10-3, U10-5, U10-6) and
  Documentation (U10-2, U10-4, U10-7, U10-9).

Runs, under the gate lock (2026-11-09, 16:25 to 16:49), on the tree of
the last commit: `BEFORE COMMIT OK (152 s)` (unit 1588, f 86, demos);
`JAVADOC PUB OK`; `LEVEL 1 OK` (MEM 129, SS 1.51).
Rebased onto main's 907f543 as branch `try-rebase` in `clone-l20`
(f22a964, 331c77d, fb41e43, 5dbd09e, 9c3936d; only `releases/next.md`
met main's new entries, both kept): `BEFORE COMMIT OK (230 s)` (unit
1596, f 86, demos) and `JAVADOC PUB OK` under the gate lock (16:51 to
17:09).
