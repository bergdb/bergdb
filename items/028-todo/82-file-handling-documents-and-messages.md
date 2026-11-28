028-82. Fix: a user's handling of the files: the backup of a running database, the files of a decided cut, the open's refusals
==============================================================================================================================

Status: done (2026-11-28): on `main` (`710ae35e`, `49f3838c`,
`cc848794`).
Kind: Fix. Frans: none.
Created 2026-11-28 by Frans Lundberg.

What: 031-08, part B (`items/031-release-2026-7/08-user-apps/`,
`apps-b.md`, section 4), the findings on documents and messages:

* **UB-1.** The same actions give the same stream, not the same files:
  a closed or idle database keeps the files of a cut that reclaim has
  decided until the next start, commit or `maintain()` call
  (`Reclaim.cutIfDurable`, `Reclaim.initFromDb`), so the files on disk
  differ between runs of the same actions while the stream is the same;
  `FileStream`'s "The files and the disk" and `Database.getStreamSize()`
  do not say so. Part A of 031-08 found the same, UA-1 (`apps-a.md`; its
  probe `CutFilesStay`): a `sync()` does not make the cut either.
* **UB-5.** (a) A start needs write access to the last stream file, and
  no sentence says so: every stream file read-only is refused with the
  system's message alone, ".../00000000000320.bergdb (Permission
  denied)". (b) The directory read-only: "StreamIoException: Permission
  denied", no file named (it is the lock file, `bergdb.lock`). (c) A file
  but the last cut or an older copy put back, "Bad size of file F, should
  have been a multiple of 100000, but was 199999.", and a file under a
  name inside the file before it, "... has a filename with an index value
  that does not match the previous file sizes ...": no way out. (d) The
  first file missing: "The start needs bytes of the stream before its
  first position, 200000: ..." names no file and no way out. (e)
  `FileStream`'s sentence on a run of zeros longer than 8 MB, "as a cut
  tail where its zeros begin inside the last record", leaves out that
  they must end in it. (f) A stray file after the last is refused with
  "Bad size of file" naming the database's own last file, not the stray
  one.
* **UB-6.** The Pub API does not say how to back up a running database;
  `FileStream`'s Javadoc ("A backup by a copy of the files") does, and
  031-08's `LiveCopy` found its procedure sound.

Checked on `main` at `4d2cb284` (2026-11-28, after 028-70 and 028-80):
f4 `FileHandling` seeds 7, 8 (with a database of release 2026.6) and 14
give the messages of (a) to (d) and (f) unchanged; the mechanism of UB-1
is as the record says (`Reclaim.applyCut` moves the first available
position at the decision, `cutIfDurable` cuts after a record or in
`maintain()`, `close()` makes no cut).

Why: a user who meets the files of a decided cut, a refusal or a backup
needs the document and the message to say what happened and what to do.

Frans: none.

Done when: the Javadoc and the messages say the above, each message
keeping its existing parts; tests of the new messages, failing before;
`java/before-commit.sh` prints `BEFORE COMMIT OK`; 027-11 and 027-14
agree with the code.

First step: `FileStream`'s checks of the directory (`checkDbFiles`,
`lockDir`, `openForRw`), `Db.refusalOfMissingBytes`, `Reclaim.initFromDb`.

Found by: 031-08, part B (UB-1, UB-5, UB-6), 2026-11-28.

Not in this entry: UB-2, the README's sentence on one stream, which is
Frans's text.


Result
------

On the branch `028-81-82` (2026-11-28). Javadoc and messages only; no
check, no stream byte and no API method changed.

* **UB-1.** `FileStream`'s "The files and the disk": the database makes a
  decided cut only once the stream is durable past its record, at a later
  commit or `maintain()` call or the next start, and `close()` makes
  none, nor does `sync()`; so a stopped or idle database keeps that
  cut's files, which commit makes the cut follows the write buffer's
  timing, and the files
  can differ between runs of the same actions while the stream is the
  same; the split into files can differ too after starts.
  `Database.getStreamSize()` says the same. `close()` is not changed.
* **UB-5 (a), (b).** `DatabaseBuilder.open()` and `start()`, and
  `FileStream(File)`: the open needs write access to the directory (to
  make `bergdb.lock`), to `bergdb.lock` and to the last stream file, also
  for a database that is only read. The messages: "The lock file
  bergdb.lock in the stream's directory D could not be made: Permission
  denied. The open needs write access to the directory, to make
  bergdb.lock if it is not there, to bergdb.lock, which it locks, and to
  the last stream file, also for a stream that is only read (bergdb
  028-82). Give the write access back, or copy the stream files
  (*.bergdb) to a directory where they can be written; no stream file has
  been opened." (also "could not be opened for writing", for
  `bergdb.lock` itself); and "The stream file 00000000000170.bergdb in D
  could not be opened for appends: D/00000000000170.bergdb (Permission
  denied). The open needs write access to the last stream file, also for
  a stream that is only read (bergdb 028-82). Give the write access back,
  or copy the stream files (*.bergdb) to a directory where they can be
  written."
* **UB-5 (c), (f).** A file but the last whose length is not a multiple
  of 100,000: the open cannot tell a file that was cut, or replaced by an
  older copy, from a file put after the database's last file, whose
  length is any (`checkDbFiles` reads names and lengths only, and a stray
  file's name can be the next file's), so the message names both: "Bad
  size of file D/00000000000170.bergdb, should have been a multiple of
  100000, but was 402384. Every stream file but the last is a multiple of
  100000 bytes long, and 00000000000170.bergdb is not the last: the file
  00000000000175.bergdb is after it. Either 00000000000170.bergdb was
  cut, or replaced by an older copy of it, or that file is not the
  database's, as a file put after the database's last stream file; the
  open cannot tell which. The open has changed no stream file (bergdb
  028-82). If 00000000000170.bergdb was cut or replaced, restore it from
  a backup, or the database's stream files (*.bergdb) all together, and
  start again; if it is the database's last stream file and the file
  after it was put there, move that file out of the directory, and keep
  it." (with several files after it: "16 files are after it, from X to
  Y", "those files"). A file whose name begins inside the file before
  it: "... currentSpos: 10600000, fileSpos: 10000000. The file
  00000000000100.bergdb begins at 10000000 by its name, before the end of
  the file before it, 00000000000096.bergdb, at 10600000: one of the two
  is not the database's, as a copy of a stream file put under another
  name, or was replaced by another file. The open has changed no stream
  file (bergdb 028-82). Move the file that was put in the directory out
  of it, and keep it; or restore the database's stream files (*.bergdb)
  from a backup, all together, and start again." A name that is not a
  stream file's: "Bad name of bergdb file: D/00000000000000 copy.bergdb.
  A stream file's name is a 14-digit number and ".bergdb", as
  00000000000000.bergdb; a file of another name that ends in .bergdb, as
  a copy that a file manager made, is not a stream file. Move it out of
  the directory, and keep it; the open has changed no stream file (bergdb
  028-82)."
* **UB-5 (d).** `FileStream`'s read below the first position, where no
  gap is, names the first file: "Cannot read at spos 199999, below the
  first position, 200000. The stream's first file in D is
  00000000000002.bergdb, which begins there."; `Db.refusalOfMissingBytes`
  and `Reclaim.initFromDb`'s refusal end with the way out: "The start has
  written nothing either (bergdb 028-70). To start the database, put its
  missing stream files back from a backup, or restore its files all
  together, the stream files and created.txt; a copy of a running
  database's files that missed some is taken again (bergdb 028-82)."
* **UB-5 (e).** `FileStream`'s "A tail of zeros": a longer run is a cut
  tail "where its zeros begin inside the last record and end in it, the
  record's size, read before them, reaching to or past the stream's end;
  else, where they begin at a record's start or reach past the end of the
  record they begin in, refused" (027-11, 1.3; `walkTail`). Its sentence
  that a start's recovery may append before a later check refuses the
  start says now that since 028-70 a refused start writes nothing.
* **UB-6.** `Database`'s new paragraph "A backup of a running database":
  `FileStream`'s procedure in the Pub API's words (after a transaction
  and a `sync()` since the start, list the `*.bergdb` files, copy them in
  the order of their names, the last one last, with `created.txt`), what
  the copy holds, and what a start does with a copy that misses a file
  that reclaim deleted (takes it, or refuses it and writes nothing, as
  since 028-70; take the copy again). `DatabaseBuilder.start()`: a start
  refused by a check writes nothing (028-70).

Tests, each failing before (2026-11-28):

* `FileStream.testOpenRefusalsNameTheFiles`: a stray empty file after the
  last, a file but the last cut, a name inside the file before it, a copy
  as a file manager names it, the first file missing (a read below the
  first position), a read-only directory without `bergdb.lock` and a
  read-only last file: each message with its files and its way out.
  Before: "Bad size of file .../00000000000004.bergdb, should have been a
  multiple of 100000, but was 50000., expected true, but was false."
* `PubTesterJavadocNewUsers.testStartWithTheFirstFileDeleted`: the
  message also names the first file and the way out.

The apps: f4 `FileHandling` matches no message text that this entry
changed (only "records end at", 028-67's); its expectations of the cases
whose refusals changed are any refusal.


Gates
-----

On F53 beside other sessions' runs (load averages near 20), 2026-11-28,
on the branch `028-81-82` rebased on `main` at `ead07411` (031-08's part
B landed), at 028-82's commit, which holds 028-81's:

* `java/before-commit.sh`: BEFORE COMMIT OK (130 s; unit 1,767 tests, f
  96).
* `java/stress/level3.sh`: LEVEL 3 OK on the second run (its power-loss
  stage: POWERLOSS OK, 8 seeds, 488 cold recoveries). The first run
  failed at its unit tests, at
  `PubTesterJavadocNewUsers.testNewDatabaseWhereAStoppedOneWasDeleted`
  ("Could not find *any* valid meta block ... The stream begins at
  200000 ... The stream's first file in .../doc is
  00000000000002.bergdb"), the failure of 021-20's case: the old
  database's background close makes its next stream file in the
  directory made again at the path, in the window between
  `FileStream.checkDirectory()` and the step that 021-20 and 021-24
  leave open. Not reproduced: the test passed in both runs of
  `before-commit.sh`, in level3's second run, and 40 times of 40 alone
  on the branch.
* `java/stress/apps.sh quick`: APPS OK (every app compiled, 031-08's f1
  to f5 among them).
* f4 `FileHandling`, seeds 7, 8 (with a database of release 2026.6) and
  14, as 031-08's section 3 runs it, before (on `main` at `4d2cb284`) and
  after: OK in each; before 46, 41 and 52 accepted, after 45, 40 and 51,
  the one case of each seed that changed being "B's stream files with
  A's created.txt", now refused by 028-81 (f4 expects either); every
  refused start changed no file, and every directory whose cause was
  removed started with every transaction. f4 matches no message text
  that 028-82 changed.
* `PowerLossTest 1001 12 3000 3`: POWERLOSS OK, 12 seeds, 732 cold
  recoveries, without per-append forces 744; negative controls caught.
* After these, 028-82's commit took a Javadoc-only addition, part A's
  UA-1 of the same finding and that `sync()` makes no cut, on `main` at
  `32b7e6f1` (031-08's part A landed: apps and probes only):
  `java/before-commit.sh`, BEFORE COMMIT OK (86 s; unit 1,767 tests, f
  96).


Log
---

2026-11-28. Registered by lead-1127 from 031-08's UB-1, UB-5 and UB-6;
taken by an agent of lead-1127, on the branch `028-81-82`.

2026-11-28. Built: the Javadoc and the messages; the two tests.

2026-11-28. The gates passed (above), on the branch rebased on `main` at
`ead07411`, and before-commit.sh again on `32b7e6f1`; to land.

2026-11-28. Landed on `main` by lead-1127 (`710ae35e`, `49f3838c`,
`cc848794`): the branch's head passed `java/before-commit.sh` on `main`
at `32b7e6f1`, and between the tree that `level3.sh` passed and the head
only the Javadoc changed. Done.
