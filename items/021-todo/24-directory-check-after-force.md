021-24. Fix: a directory replaced during the force before a new stream file
============================================================================

Status: done. Kind: Fix. Frans: none.
Created 2026-11-09 by Frans Lundberg.

What: a hole in 021-20's fix. `FileStream.newFile()` called
`checkDirectory()` and then forced the last file (`Force.SWITCH`), which
can take seconds, and closed its writer, and only then made the next
stream file by its name. A directory moved away and another database's
directory moved to the path during that force got the old database's
next stream file: the old database's `sync()` and `close()` returned, and
the replacement no longer started ("Bad size of file
.../00000000000000.bergdb"), its synced data lost to the reader. Found by
a Codex review (round 4) of 021-20, its W1 (high), with the probe
`DirectorySwitchProbe.java` in
`/Users/f/fl/bench/2026-11-09/clone-codex4/probes/` (a Core `Db` on
`FileStream(dir, io, false)`, its SWITCH force held by the `FileStreamIo`
hook). It also said that `Database.stop()`'s Javadoc promised that the old
database writes nothing into the replacement. With it, V5-1 of reviewer
v2 (020-23, section 5): a comment at `checkDirectory()` with the
invariant that the check relies on.

Why: misuse must end in an exception, never in wrong data or a failed
database; and a Javadoc must not promise more than the code gives.

Frans: none. The rest of the window is for his list (below), not a
decision for 2026.4.

Done when: the probe as a unit test that fails before; the check after
every step that waits, right before each make, delete and reopen by
name; what is left said in the code, the Javadoc and here; V5-1's
comment; `BEFORE COMMIT OK`, `JAVADOC PUB OK` and `LEVEL 1 OK` under the
gate lock; a line in `releases/next.md`.

First step: list every wait between `checkDirectory()` and the file
step.


Log
---

2026-11-09. Registered by coord-1109 from the Codex review's W1 and
reviewer v2's V5-1, and taken by its agent d24 (clone `clone-d24`, on
main's 48d2b00).

2026-11-09. Done by d24: commit 4ebd063 in `clone-d24`, on main's 48d2b00,
to land. In 2026.4's 021-20 only (main's 2557286).

* The paths that make, delete or open a stream file by its name, and
  what came between 021-20's check and the step:
  * `newFile()`: the SWITCH force of the last file (with per-append
    forcing off, a Core option; a database of the Pub API forces each
    append, so its force there finds nothing to do) and the close of the
    last file's writer. The window of seconds.
  * a cut's delete (`DbFile.delete()`, the cut's thread, after its CUT
    force): `close()` of the file, whose channel's close waits for the
    reads in progress on it.
  * the reopen of a read channel after an interrupt (`reopenChannel()`)
    and of the writer's handle (`force()`): nothing; the check was right
    before the open.
  * the start: the earlier files are opened for reads, then the last one
    for appends (`openForRw()`), with no check (021-20 checked only
    later steps).
* Fix, in `FileStream`: the check moved out of `newFile()` into
  `openForRw()`, right before `io.open()`, after the force and the close
  of the writer; in `delete()` right before the delete, after `close()`.
  Each of these steps, and both reopens after an interrupt, are checked
  again after the step: `openForRw()` after the file's force, the
  directory's force and the read channel's open (an open handle is
  closed when it throws); `reopenChannel()` publishes the new channel
  only after its second check, so no read uses a channel of a
  replacement. The start's last file goes through `openForRw()`, so the
  start is checked too, after its opens of the earlier files. Nothing
  else of 021-20 changed: the two lock keys, the messages, the failure.
* Left: a replacement in the short window between the check and the
  step, usually microseconds, longer if the thread is paused, as by a GC
  or a preempted thread on a loaded machine (reviewer v2), as Java's
  `RandomAccessFile` and `File.delete()` take a path, not a directory
  that is open. The check after the step then fails the stream before it
  writes a byte there, but the step is done: a new, empty stream file in
  the replacement, or, at a cut, the replacement's file of that name
  deleted. A database's start there is refused until the empty file is
  removed, with an exception that depends on what else is in the
  directory: `BadDirStateException` (in a `StreamIoException`) beside
  stream files of its own, as `testReplacedRightBeforeTheOpen` shows; in
  a directory without others (a fresh `mkdir`, or the directory a
  refused `create()` made), reviewer v2's EmptyFileProbe
  (`/Users/f/fl/bench/2026-11-09/v2/probe6`): `create()` throws
  `StreamFormatException` ("Could not find *any* valid meta block"),
  `open()` with `created.txt` `DatabaseMissingException`, whose message
  advises a restore from a backup. A directory replaced and put back
  between the two checks is not seen. `checkDirectory()`'s comment,
  the class comment and `Database.stop()` say so; `stop()`'s sentence
  "writes nothing into the directory that is then at the path" now
  comes after what is left, as "Otherwise". Another process at the path,
  and Windows, as in 021-20.
* For Frans's list, after the release: in a directory without other
  stream files, `open()`'s `DatabaseMissingException` beside such an
  empty stream file advises a restore from a backup where removing the
  file is enough, and `create()`'s `StreamFormatException` says only that
  no valid meta block was found (reviewer v2); a clearer refusal is a
  code change, not made tonight.
* For Frans's list, after the release: `SecureDirectoryStream`, which
  the JDK gives on macOS (checked: `UnixSecureDirectoryStream` on F53's
  JDK 27) and Linux, opens and deletes relative to an open directory
  (`openat`, `unlinkat`) and would close the window; `FileStream` and
  `FileStreamIo` would open their files through it, not by path, a
  larger change than one for today.
* V5-1: `checkDirectory()`'s comment says that the check relies on
  `bergdb.lock` being open from `lockDir()` until `unlockDir()`, after the
  stream's last file step: while it is open, the old directory's inode
  cannot be reused (s1, ext4: `rm -rf` then `mkdir` gave the same inode
  50 of 50 times with nothing open, 0 of 30 with a file open), so the
  lock file must not be closed earlier.
* Tests, in `FileStream`, each failing before:
  * `testNoNewFileWhenReplacedDuringTheSwitch`, the probe: a stream with
    per-append forcing off, its SWITCH force held by a `FileStreamIo`;
    meanwhile the directory is moved away and another stream's directory
    (1,000 bytes) moved to the path. Before: "a new file in the
    replacement" (file 02 made there). Now the append and `close()`
    throw "no longer", and the replacement opens with its 1,000 bytes.
  * `testReplacedRightBeforeTheOpen`, what is left: the replacement made
    inside `FileStreamIo.open()`, after the check. Before: the stream
    went on, and `close()` returned. Now the append and `close()` throw;
    the empty file 02 is in the replacement, which a stream refuses
    (`BadDirStateException`) and opens with its 1,000 bytes once the
    file is removed.
  * About 0.25 s each; the 021-20 tests and the other FileStream tests
    pass unchanged.
* The probe on the fixed build (its `sync()` and `close()` in a try):
  "Old sync threw: bergdb.pub.util.DbFailedException: A sync failed on
  the storage" (cause "Directory .../live is no longer the database's
  directory"); the replacement holds only its own files and starts, with
  its value "synced replacement data".
* `releases/next.md`, Pub API, after 021-20's entry.

Runs, under the gate lock (2026-11-09, 17:58 to 18:08), on the tree of
4ebd063: `BEFORE COMMIT OK (323 s)` (unit 1614, f 86, demos);
`JAVADOC PUB OK`; `LEVEL 1 OK` (MEM 129, SS 1.51).

2026-11-09. Reviewer v2 (020-23) found 4ebd063 sound, with two low
points of wording, done by d24 in one commit on top (comments, Javadoc,
`releases/next.md` and this item; no change of code): the window is
"usually microseconds, longer if the thread is paused, as by a GC", not
a bound; and the empty file left by it is refused with an exception that
depends on what else is in the directory, not always
`BadDirStateException` (reviewer v2's EmptyFileProbe; above, "Left").
Under the gate lock (18:37 to 18:42), on the tree of that commit:
`BEFORE COMMIT OK (260 s)` (unit 1614, f 86, demos); `JAVADOC PUB OK`.
