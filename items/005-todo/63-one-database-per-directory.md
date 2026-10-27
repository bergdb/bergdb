005-63. Decide: one database per directory, also while one closes
================================================================

Status: open. Kind: decide. Created 2026-10-27.

Found on 2026-10-27 by Claude (Opus 5.5, Claude Code) in 006-09, when
`level2.sh`'s step 6 (`BryanRepro`) failed on `main` from `eaec93e`
(005-46) on; registered by the session for Frans to decide. The cause, the
evidence and the test's fix are in
[006-09's note](../006-2026-q4/09-unattended-27-28-october/bryanrepro.md).


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


Options
-------

A. **Say it.** `Db.stop()`'s and `Database.stop()`'s Javadoc: start another
   database on the same directory only after this one is closed (`close()`
   returned).
B. **Refuse it.** `FileStream` takes a lock on a file in its directory
   (`FileChannel.tryLock`) for as long as it is open, and a second
   `FileStream` on the directory fails at once with a clear message. The
   operating system releases the lock when the process ends, so a crash
   leaves nothing stale; in the same JVM, Java refuses an overlapping lock
   too (`OverlappingFileLockException`), with no registry of BergDB's own
   (010-P9).
C. **Both.**
D. **Nothing.**

Recommended: C. A is one sentence; B turns a race that can fail a
database into an immediate, clear error, at the cost of one lock file, a
small change to `FileStream` and tests (a second open in the same JVM and
in another process).


Done when
---------

Frans has decided; with B, the lock in `FileStream` with tests, and
`before-commit.sh` and `level3.sh` pass.


First step
----------

Frans's decision.
