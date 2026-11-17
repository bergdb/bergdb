# 020-24-08 An append-heavy log store where the file system misbehaves

Created 2026-11-09 by Frans Lundberg.

An application written as a new user of 2026.4 would write it (u8, for coord-1109, by the
common brief of 020-24, round 3): only the release jar on the class path, and only what a
user reads (README.md, `java/src/overview-pub.html`, the Javadoc of `bergdb.pub` and
`bergdb.pub.util`, `releases/next.md`). The jar was built from a clone of main at
`4338cda`. The implementation was read only afterwards, to explain U8-2 and U8-3, and
`javap` showed the classes of the exceptions met.


## 1. The application

An append-only log of records, run on a file system that fills up, turns read-only,
loses files or goes away, as a user would meet it. To fill a disk without sudo, the
database lives on a volume of its own: a 50 MB APFS disk image
(`hdiutil create -size 50m -fs APFS -volname bergdbfull`), attached at
`/Volumes/bergdbfull`, filled to a chosen free space by a filler file. hdiutil needed
nothing that a user cannot do: create, attach, attach `-readonly`, and `detach -force`
for a volume that goes away under the writer. The image was detached at the end.

The files are in `/Users/f/fl/bench/2026-11-09/app-u8/app/`: `LogStore.java` (the log),
`LogEvent.java` (a record as a Data Object, for an index by level), `Child.java` (each
step of an application as a JVM of its own), `App.java` (arranges the file system between
the steps and checks what each saw against the Javadoc) and `run.sh`, which builds and
runs every case in about 4 minutes and prints `APP OK` or `APP FAILED`; the output of the
last run is `run.txt`, each step's own output is in `../work/`. 1,600 lines of Java. The
minimal reproductions are in `/Users/f/fl/bench/2026-11-09/app-u8/probe/`.

How it uses BergDB:

* Record seq is a `byte[]` of 1,000 bytes at `/log/SEQ.bin` (12 digits), holding its seq,
  a payload made from it and a CRC32, so that a reader checks each record alone. The
  writer syncs every 50 or 100 appends (a group commit) and writes the last acknowledged
  seq, the one a `sync()` returned for, to a file on the main disk.
* The check after each failure: a start by `open()`, every record read by `get()` and
  checked, a primary scan of `/log/` that must count the same (the records are a prefix
  of the appends, no hole, nothing after it), the prefix at least to the last
  acknowledged seq and at most to the last seq put; then more appends, a restart and the
  same checks again.
* After the first failure, what the application meets next: a put, a get, a sync of the
  connection and of the database, two `close()` calls, each under a time limit of 30 s (a
  hang prints the threads' stacks).
* Variants: Data Objects with a user index by level (a build on a full disk); a ring of
  10,000 records with a retain duration of 1 s, so that reclaim cuts (a log with
  retention on a small disk).

The cases, each a part of `App`:

* `full`: the disk fills while the log appends; a start on the full disk; appends there;
  a start after space is freed.
* `syncfull`: puts past the free space without a sync, then `sync()`, as fast as the
  puts go and paced at 0.5 ms.
* `idle`: puts past the free space, then no call for 3 s while the storage thread fails,
  then `close()`.
* `createfull`: `create()` on a full disk, then after space is freed.
* `bigput`: one put of 12 MB on a volume with 6 MB free.
* `ring`: the ring with retention outgrows the volume; two restarts on the full disk; the
  database copied to a larger disk.
* `sweep`: the disk fills at 21 points (2.0 to 6.0 MB free), so that the failing write is
  in a record, an index node, a meta block or a new stream file; every other run the
  process halts at the failure without `close()`; a start on the full disk; a start
  after space is freed.
* `rorun`: the directory made read-only (r-x) while the log appends.
* `robefore`: before a start, the directory r-x, the files r--, the directory not
  readable, the volume attached read-only.
* `damage`: a stopped database of 24,000 records (31 MB, 39 stream files), every record
  acknowledged; each of 20 damages to a fresh copy, then a start and a read of every
  record: a file deleted (the last, the one before, a middle one, an early one, the
  first), cut (by 1,000 bytes or half, the last or another), emptied, 4 kB zeroed (in an
  early, a middle, the before-last and the last file, at the last file's end), 8 kB of
  zeros or of random bytes appended, `created.txt` deleted (started by `open()` and by
  `create()`), `bergdb.lock` deleted.
* `readerr`: an early stream file cut, zeroed or deleted under a running database with a
  cache of 4 MB, then every record read; a restart.
* `index`: an index build on a disk that fills during the build; the build after space
  is freed.
* `twoproc`: a second process's `create()` and `open()` while a first holds the
  directory; `bergdb.lock` deleted under the holder; a holder killed with SIGKILL; two
  processes that create one new database at the same instant, 6 times.
* `twowriters`: `bergdb.lock` deleted while process 1 appends, and process 2 starts and
  appends too.
* `notadb`: `open()` of an empty directory, a directory of other files, a regular file,
  a database's parent; `create()` on a regular file, a random `00000000000000.bergdb`, a
  text file named `backup.bergdb`, a database's first file under a later name, an emptied
  stream with `created.txt`.
* `vanish`: the volume force-detached while the log appends, then attached again.

The last run: 16 cases, about 160 JVMs, 4 minutes; every check passes but the four of
U8-1, so it ends with `APP FAILED`; no call hung.


## 2. The findings

Most severe first. A reproduction names a file in `probe/`, or a case of `App`.

| ID    | Kind | Severity | What                                                     | Reproduction      |
|-------|------|----------|----------------------------------------------------------|-------------------|
| U8-1  | API | medium | a lost or cut last file: synced records dropped silently | LastFileLost      |
| U8-2  | API | low    | a start on a full disk: DbFailedException "getOne()"     | StartTrace, sweep |
| U8-3  | doc | low    | a tail of zeros is refused, with no way out given        | LastFileLost      |
| U8-4  | doc | low    | a full disk has no way out from inside the database      | ring              |
| U8-5  | API | low    | no read-only start: read-only volume or files refused    | robefore          |
| U8-6  | API | low    | a start's refusals are classes outside the API           | twoproc, damage   |
| U8-7  | API | low    | a failure's cause is three or four causes deep           | full              |
| U8-8  | doc | low    | create(): "without created.txt ... new, empty database"  | damage            |
| U8-9  | doc | low    | bergdb.lock deleted: a second process starts             | twoproc           |
| U8-10 | doc | low    | an index build's join() gives ACTIVE before durable      | index             |
| U8-11 | API | low    | create() on a regular file: "Not a directory", no path   | notadb            |

No hang, no wrong record, and no acknowledged record lost in any case where the files
were not touched: the storage's error paths held. U8-1 is the one loss, of damage done
to a stopped database's files.

### U8-1. A lost or cut last stream file: synced records dropped silently (API, medium)

A database of 24,000 records, each acknowledged by a `sync()` that returned, stopped by
`close()`. Then one change to its files, as a backup tool, a sync client, a cleanup
script or a hand may make, and a start by `open()`:

| Change to the files                     | Start   | Records after |
|-----------------------------------------|---------|---------------|
| the last file deleted (1.1 MB)          | OK      | 23,167 |
| the last file emptied                   | OK      | 23,167 |
| the last file cut to half               | OK      | 23,584 |
| the last file cut by 1,000 bytes        | OK      | 23,999 |
| the file before the last deleted        | refused |        |
| a middle, an early or the first deleted | refused |        |
| a middle or an early file cut to half   | refused |        |

The start succeeds with no sign that the stream is shorter than the one the last
`close()` left: `StartupInfo` has only the duration, and nothing is logged. Up to 833
acknowledged records are gone. The next write lands where the cut is, so the deleted
file can no longer be put back. Every other damage of the files was refused at the start
or failed a read with `DbFailedException` (section 3).

Reproduction, `probe/LastFileLost.java`, on the main disk (`java LastFileLost DIR
delete`, or `cut`): 24,000 puts of 1,000 bytes with a sync every 100, `close()`, the last
`*.bergdb` deleted, a start: "start OK: 23167 of 24000 synced records"; with `cut`, the
last file cut by 1,000 bytes: "start OK: 23999 of 24000 synced records". The same on the
50 MB volume and on the Mac's own disk.

What the Javadoc says: Database, "Errors": "Only a cut tail, as after a crash or a power
loss, is recovered", and "BergDB does not try to recover when the environment fails; the
database fails instead". A user reads the first as the unsynced end that a crash may
lose, and the second as the rule for anything else; `Database.sync()` says the
transaction "has been stored durably". A cut deeper than the last append cannot come
from a crash with the default forcing (each append forced before it returns), but the
start cannot tell, as nothing outside the stream records how long it was. The stream's
files grow with it (200 kB up to 4 MB of stream, 1 MB up to 20 MB, then 5 MB), so the
loss grows with the database.

What would help, for Frans to choose: say it in the Javadoc of `Database` ("Errors") and
`sync()`, that a lost or cut end of the stream's files is taken as a crash and loses
synced transactions without an error; or record the stream's length at `close()` outside
the stream (in `bergdb.lock` or a file of its own) and refuse a start that finds less; or
report the length that recovery cut in `StartupInfo`, so that an application that knows
its last acknowledged record, as this one does, can stop.

### U8-2. A start on a full disk throws DbFailedException "Cannot call getOne()" (API, low)

A start on a full disk, after the database failed there, sometimes works (16 and 18 of
21 sweep runs, in two runs: it reads, and even a small put and sync fit in the last
block) and sometimes is refused. The refusal is one of:

* `DbFailedException`: "Cannot call getOne(): the database failed (the cause) and must
  be restarted." <- `StreamIoException`: "No space left on device" (or the next stream
  file's name and "(No space left on device)"), in 5 and 3 of 21 sweep runs, when the
  start's own write needed a new block or a new stream file;
* `StreamIoException`: "Main storage not active: the main stream failed (the cause)."
  <- "No space left on device" (case `ring`, a restart);
* `StreamIoException`: "Cannot read from the failed stream, fail exception message:
  .../00000000001300.bergdb (No space left on device)" (case `ring`, the next restart).

And with the first stream file deleted (case `damage`), a start threw `DbFailedException`:
"A read failed on the storage (the cause). The database takes no more transactions or
reads and must be restarted."

The stack trace of the first (`/Users/f/fl/bench/2026-11-09/app-u8/work/starttrace.txt`,
from `probe/StartTrace.java`):
`DatabaseBuilderImp.start` -> `Db.start` -> `Reclaim.initFromDb` -> `Db.getOne` ->
`assertDbStateIsActive`, with the storage thread's failed write as the cause: the start
writes, its write fails in the background, and its next read refuses. The start has
cleaned up: a start after space is freed works, with every acknowledged record.

Why it matters: `DatabaseBuilder.start()` lists DbException, "If a functioning database
could not be started", and names StreamIoException and others, not DbFailedException,
whose Javadoc is about a running database. The message names a call the user did not
make and says to restart, which fails again the same way. That a start writes, and so
needs free space, is not said; nor that a start on a full disk may work.

### U8-3. A tail of zeros or garbage is refused, with no way out given (doc, low)

Zeros at the end of the last file, 8 kB appended or the last 4 kB overwritten, as a power
loss leaves on a file system that writes a file's size before its data, and 8 kB of
random bytes, as a disk that reorders writes may leave: the start is refused with
`StreamFormatException`, "Bad transaction size in db stream, 0, spos 31110648. Stream
length: 31118840" (random bytes: size -1156638823). Reproduction: `java LastFileLost DIR
zeros`.

That is the decided contract (014-01, section 7: the storage provider ensures that only
a truncated tail is left; FileStream's Javadoc names the known limit, 005-83). But the
user-facing Javadoc says "Only a cut tail, as after a crash or a power loss, is
recovered", and of the storage only "correct storage, which returns the bytes written to
it": a user does not learn that a power loss must leave a cut tail and never zeros, nor
on which file systems that holds. The message gives no way out. One exists: cutting the
last file at the given spos made the start work, with every record for the 8 kB
appended (here `00000000000300.bergdb` cut to 1,110,648 bytes: the spos, 31,110,648,
less the file's start, its name times 100,000). A sentence in Database's "Errors" and in
the message would do.

### U8-4. A full disk has no way out from inside the database (doc, low)

The ring (10,000 records of 1,000 bytes, 10 MB live, retain 1 s, startup distance 5 MB)
grew to 49 MB and filled the 50 MB volume: `DbFailedException` at a sync. Two restarts on
the full disk: each was refused or failed at its first sync, and each added to the
stream (46 to 48 MB in an earlier run). Nothing inside the database frees space on a full
disk: a delete writes, and reclaim rewrites live values before it cuts. The way out was
to copy the stopped database's files to a larger disk, where it ran on (stream 70 MB for
10 MB live).

The Javadoc says what a failure does, not what to do on a full disk: free space outside
the database, or move the files, and leave room, as a database with a finite retain
duration keeps several times its live data (here 5 to 8 times; U6-2 asks for the
sizes).

### U8-5. No read-only start (API, low)

A start on a volume attached read-only is refused (`StreamIoException`, "Read-only file
system"), and so is one with read-only files (`StreamIoException`, ".../bergdb.lock
(Permission denied)"). A start on a full disk may be refused (U8-2). So an archived log
on a read-only medium, a mounted backup image or snapshot, or a database on a full disk
cannot be read without copying it. A start in a read-only directory (r-x, files rw) does
work: its reads, a put and a sync work, until the stream needs a new file (case `rorun`:
`DbFailedException` <- "00000000000012.bergdb (Permission denied)", 100 records after the
change).

### U8-6. A start's refusals are classes outside the API (API, low)

To tell "another process has the directory" (wait and retry) from damage (call a human),
an application must look at classes of `bergdb.storage` and `bergdb.stream`, which the
README says are not API: `StreamIoException` with a `DirectoryInUseException` cause,
`StreamIoException` with a `BadDirStateException` cause (a file missing or of a wrong
size), `StreamFormatException` (a damaged tail), `StreamIoException` with a
`ReadBelowFirstPosException` cause (a first file missing). The API's classes that a start
also threw do not tell the cases either: `DbFailedException` (U8-2), and `BadCryptoKey`
for a stream of random bytes. The Javadoc names "StreamIoException" without its package
(`DatabaseBuilder.start()`, `Database.close()`), and `DbException` names
StreamFormatException and InternalDataException. A `DatabaseInUseException` in
`bergdb.pub.util`, as `DatabaseMissingException` is, would serve the first case.

### U8-7. The cause of a failure is three or four causes deep (API, low)

On a full disk the writer gets `DbFailedException`: "A sync failed on the storage (the
cause). The database takes no more transactions or reads and must be restarted." <-
`StreamIoException`: "StorageManager has error: Main storage not active: the main stream
failed (the cause)." <- `IOException` with the same message <- `IOException`: "No space
left on device". A log line of `e.getMessage()`, or of the exception and its first
cause, does not say that the disk is full; "StorageManager" and "main stream" are
internal names. The message of the failing call could end with the root cause's,
"(No space left on device)".

### U8-8. create(): "without created.txt ... a new, empty database" (doc, low)

`DatabaseBuilder.create()`: "A directory without created.txt, also an empty or a missing
one, gets a new, empty database". A directory with its stream files and without
`created.txt` opens its database: `create()` and `open()` both started with all 24,000
records, and the start wrote `created.txt` again. Read alone, the sentence says the
opposite; the first paragraph has the rule (no stream file with a byte). "A directory
without created.txt and without a stream byte" would do.

### U8-9. bergdb.lock deleted: a second process starts (doc, low)

With `bergdb.lock` deleted while process 1 holds the database, process 2's start works
(case `twoproc`; its put and sync too). With process 1 appending (case `twowriters`),
process 2 was stopped by the stream's own checks, in three runs three ways: at its first
new file, "File .../00000000000012.bergdb is not of expected length (173768),but 200000
bytes. Was is modified by someone else?" (sic: "Was is", no space after the comma), or
"File .../00000000000014.bergdb already exists and has length 200000.", or at its start,
"Cannot read 8 bytes at spos 1400000, the end of the stream."; process 1's acknowledged
records all survived each time. Process 2's own puts before its first sync were lost,
and with an idle process 1 nothing stopped process 2. The lock file's own text says not
to delete it; the Javadoc (`DatabaseBuilder.start()`, "One database at a time has the
directory") does not.

### U8-10. An index build's join() gives ACTIVE before it is durable (doc, low)

On a disk with room for the objects but not for the index, the build's `join()` returned
ACTIVE ("its build read 20000 values in this process"), a get and a put worked, and the
next `sync()` threw `DbFailedException` (No space left on device). After space was freed,
the next start's `indexJob().join()` gave ACTIVE, and the index gave all 5,000 ERROR
events. Right, as a crash before a sync may undo a transaction; but `Job.join()` does not
say that ACTIVE is not durable, where `IndexBuilder.start()` says it of the creation.

### U8-11. create() on a regular file: "Not a directory", no path (API, low)

`create()` of a path that is a regular file throws `StreamIoException`: "Not a directory"
<- `IOException`: "Not a directory", without the path; `open()` of it says "No database in
/Volumes/bergdbfull/t/file: it is not a directory. ...", a model message.


## 3. What went well

* The disk full, at about 30 points in each run (21 in the sweep, the others in `full`,
  `syncfull`, `idle`, `bigput`, `ring`, `index`): each time the failing put or sync threw
  `DbFailedException` with "No space left on device" at the root, every later put, get
  and sync threw `DbFailedException`, `close()` returned, as Database's "Errors" says.
  After space was freed every start worked, every acknowledged record was there and right,
  the records were a prefix of the appends, and appends went on. Also with the process
  halted at the failure without `close()`.
* `sync()` after puts that the full disk could not take threw `DbFailedException`; puts
  paced at 0.5 ms saw the failure at the next put. A 12 MB put returned and its sync
  failed; the log before it was intact.
* `close()` after a failure that no call had reported threw `StreamIoException` ("No
  space left on device"), and so did a second `close()`, as `Database.close()` says
  (019-09).
* `create()` on a full disk was refused with `StreamIoException` and left the directory
  empty; `open()` of it then gave `DatabaseMissingException`; after space was freed
  `create()` worked.
* A volume force-detached under the writer: `DbFailedException` ("Bad file descriptor"),
  every acknowledged record there after it was attached again.
* A file deleted, cut or of a wrong size anywhere but at the end: the start refused,
  naming the file ("File .../00000000000040.bergdb has a filename with an index value that
  does not match the previous file sizes", "Bad size of file ..."). Zeros in the startup
  section: refused. Zeros in older parts: the start worked and the read that met them
  threw `DbFailedException` (a checksum or a node type), never a wrong or a missing record:
  0 wrong records in every run. A stream file deleted under a running database: the reads
  went on (the OS keeps the file), and the next start refused.
* Two processes: `create()` and `open()` refused with a clear message ("Directory ... is
  in use by another BergDB database (bergdb.lock is locked by another process)"),
  nothing changed; a holder killed with SIGKILL released the directory; 6 of 6 races to
  create one new database had exactly one winner, and the database started after.
* Paths that hold no database: `open()` gave `DatabaseMissingException` with messages that
  say what to check, and wrote nothing; a random stream file, a text file named
  `backup.bergdb` and a first file under a later name were refused and left unchanged; an
  emptied stream with `created.txt` gave `DatabaseMissingException`, as documented.
* `bergdb.lock` and `created.txt` explain themselves in plain text; a deleted
  `bergdb.lock` or `created.txt` is made again at the next start.
* Read-only cases are refused at the start or fail cleanly with the file named
  ("00000000000012.bergdb (Permission denied)"), and the database starts after the
  permissions are back, with every acknowledged record.
* The Javadoc of failures (Database, "Errors"; DbFailedException; Database.close();
  DatabaseMissingException) matched what happened in every case but those above.


## 4. Fixes

Made 2026-11-09 for coord-1109, in `clone-x26`, by the rule for 2026.4: no
change of the stream's format; a plain bug fixed with a failing test
first; elsewhere the Javadoc made true where the code is as designed; no
new API and no change of meaning. The tests are in
`PubTesterJavadocNewUsers`. The three commits, on main at `f2dbcc7`, gated
on one tree under the gate lock: BEFORE COMMIT OK (149 s, unit 1580, f 86,
demos), JAVADOC PUB OK, and LEVEL 1 OK for the change of `FileStream`.

* **U8-1** (`bf903c3`): not changed in behaviour. `Database`'s Javadoc has a new
  part, "The files": a start recovers a cut tail and cannot tell it from a
  lost or cut last stream file, so such damage while the database is
  stopped loses synced transactions without an error; leave the files
  alone, and copy, move or restore them all together. `sync()` points
  there; `docs/levels.md`, section 8, the crash contract, says it too.
  The options to detect it, for Frans:
  * (a) The stream's length recorded outside the stream at each clean
    `close()`, in a small file of the directory written and forced last
    (or in `created.txt`), and checked at the start: a stream shorter than
    the record is refused. No change of the stream's format; a new file in
    the directory, and a new refusal, a change of meaning (which
    exception, and how a user who means it, after restoring an older
    backup, gets past it). It covers damage after a clean stop only: after
    a crash the record is the last clean stop's, below the stream's end. A
    copy without the file is not checked, as one without `created.txt`.
    Variant: the record also at each sync, which costs a second force per
    sync, or at each new stream file.
  * (b) `StartupInfo` gives the stream's end, the time of its last
    transaction and whether recovery completed a torn tail, so that an
    application that knows its last acknowledged write (this one did) can
    stop. New API, no change of format, no check by BergDB.
  * (c) A record of a clean stop in the stream (a last record, or a flag
    in the meta block), so that a start knows whether the last stop was
    clean; a lost last file after a clean stop then looks like a crash,
    which a start could report but not refuse. A change of the stream's
    format: not for 2026.4.
* **U8-2** (`90ee5a8`, tests failing first): a start that fails on the storage
  throws the storage's exception, a `StreamIoException` (or
  `StreamFormatException`), and closes what it opened, as before
  (`DatabaseImp.createAndStart`). It threw `DbFailedException` when a read
  of the start's last steps (reclaim's settings in `Db.start`, the index
  manager's scans) failed, as with the first stream file deleted ("A read
  failed on the storage ..."), or met a failure of the storage in the
  background, as the start's own write on a full disk ("Cannot call
  getOne(): ... must be restarted."). A user now sees, on a full disk,
  `StreamIoException` "No space left on device" (or "Main storage not
  active: ..." or "Cannot read from the failed stream ...", as before),
  and with the first file deleted `StreamIoException` "Cannot read at spos
  176320, below the first position, 200000." with a
  `ReadBelowFirstPosException` cause. `DatabaseBuilder.start()` says so,
  and that a start may write (a cut tail, `created.txt`), so that a full
  disk may refuse it or the database fails at its first write. Tests
  `testStartWithTheFirstFileDeleted` (a real directory) and
  `testStartOnAFailedStorage` (a stream whose appends fail, failed by a
  hook after the Db's start). The Core's `Db.start()` is unchanged: it
  still throws `DbFailedException` for a failed read of reclaim's
  settings, as its Javadoc says (005-30).
* **U8-3** (`bf903c3`): "The files" says that a power loss must leave a cut
  tail (014-01, section 7; 005-83), that a tail of zeros or other bytes is
  refused with `StreamFormatException` "Bad transaction size ..., spos P",
  and how to start: keep a copy, cut the stream file that holds P to P
  less its first position (its name's number times 100,000) and remove
  later stream files. The message is unchanged.
* **U8-4** (`bf903c3`): `Database`'s Javadoc says that nothing inside the
  database frees space on a full disk, to free space outside it or copy
  the stopped database's files to a larger disk, that a start may write,
  and to leave room for the retained stream.
* **U8-5, U8-6, U8-7**: API questions, for Frans's list; not changed. U8-5,
  a read-only start (a read-only volume, a backup image, a full disk).
  U8-6, an API class for "another process has the directory"
  (`DatabaseInUseException`), and the Javadoc's "StreamIoException"
  without its package. U8-7, the root cause's message ("No space left on
  device") in the message of the failing call.
* **U8-8** (`bf903c3`): `DatabaseBuilder.create()` says that a directory without
  `created.txt` and without a stream byte gets a new database, and that
  one with stream files and without `created.txt` is opened, the start
  writing `created.txt` again.
* **U8-9** (`bf903c3`): `DatabaseBuilder.start()` says what `bergdb.lock` is (the
  operating system's lock, released at the process's end, never stale) and
  that deleting it lets a start in another process take the same files,
  which can lose writes and damage the stream. The message's "Was is
  modified by someone else?" is now "Was it ...", with the missing space
  after the comma.
* **U8-10** (`bf903c3`): `Job.join()` says that ACTIVE is committed, not
  durable: a crash or a failure before a sync can undo the build, and the
  next start takes it again.
* **U8-11** (`bf8e9ac`, a plain bug, test failing first): `create()` of a path
  that is a regular file throws `StreamIoException` "Directory P could
  not be opened: it exists and is not a directory." (`FileStream`), where
  it said "Not a directory" without the path. Test
  `testCreateOnAFileNamesThePath`.
