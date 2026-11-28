028-85. Fix: PubTesterJavadocNewUsers.testNewDatabaseWhereAStoppedOneWasDeleted fails under load
================================================================================================

Status: open. Kind: Fix. Frans: none.
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
