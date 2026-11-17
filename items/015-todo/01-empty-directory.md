015-01. Fix: a database directory without its stream starts as a new, empty database
==================================================================================

Status: done (2026.2): A with A+ (see Outcome). Kind: Fix. Created 2026-11-03 by
Frans Lundberg. Closed 2026-11-03.

To be fixed before release 2026.2. Frans, 2026-11-03, 15:27, on 016-01's
question Q4 (a Decide entry for after the release, or a fix before it):
"Q4. Fix before. You decide how to." So the coordinator (013-02) chooses
the design from the options below; the recommendation is at the end. The
plan of the release's fixes is 016-05. Found in 016-01's review (its
section 4.2), from 005-33 (the first row of its table) and 012-14,
section 6.4. With D7 (016-01, section 10): Java only; the C clone does
not follow.


The issue
---------

A start through the Pub API, `Factory.database().dir(D).start()`, on a
directory D whose stream files (`*.bergdb`) are gone, or whose only stream
file is empty, creates a new, empty database there, and says nothing. The
application then runs on an empty database as if it were its own.

How it comes about, read at `9d34ac1`:

* `DatabaseBuilderImp.start()` opens D (`openDirs`, `new FileStream(D)`).
  `FileStream`'s constructor creates D if it is missing (`mkdirs`, with
  every missing ancestor), takes `bergdb.lock`, and, if D holds no
  `*.bergdb` file, creates an empty `00000000000000.bergdb`
  (`createDbFileObjects`, `newFile()`).
* `Db.startInner` calls `handleEmptyStream()` after `syncStreams()`: if
  the stream's length is 0, it writes the first meta block and the
  primordial transaction (264 bytes, `CREATION_LENGTH`) and then
  `created.txt` (`writeCreatedTxt`, through `Util.bytesToFile`, not
  forced). A length of 0 is both "no file" and "one empty file named
  `00000000000000.bergdb`". An empty first file with another name (after
  reclaim's cuts) has a length above 0 and is refused today.
* This is the 2012 rule (005-33, the first row of its table: "0, or no
  stream file: creates the database"). It is right for a new database and
  for a creation that crashed before its first write. It is wrong when a
  database was there.

Where it matters:

1. **A restore or a copy that missed the stream files**, or files removed
   by hand or by a cleaner of `*.bergdb`; `created.txt` and `bergdb.lock`
   are still there.
2. **The only stream file emptied**: a file system that kept the file but
   not its bytes, a restore that made an empty file. A database of one
   file is one below 200 kB of stream (`FileStream`'s smallest file), or
   any database before its first new file.
3. **A volume that is not mounted, or a wrong path**: D is empty or
   missing. The start creates D (and its missing parents) on another
   volume, and a database in it.

012-14, section 6.4 met case 2 in its corrupt variants (Gen 703 and 904,
"a database of one file, with that file emptied or removed"): Java's start
made a new database, C's `bergdb-dump` refused (C does not create
databases).

Not affected: the core API's users (tests, tools, the C clone's harness),
which choose their stream themselves; and `memory()` databases.


What a fix must keep
--------------------

* **The stream format** (016-01, section 3). No byte of a stream changes,
  and nothing that a start reads from the stream changes. A change of what
  a start reads from the stream needs Frans's explicit approval.
* **005-33's decision A**: a stream that holds a part of a creation (1 to
  263 bytes) is refused with `DatabaseNotCreatedException`, and the start
  writes nothing to it. A creation that crashed before its first write
  (no stream byte, nothing committed) is created again at the next start,
  as today.
* **Truly append-only storage** (Frans, 2026-10-24, in 005-33): the
  database never removes a stream's bytes.
* **A refused start writes nothing and creates nothing**, so that the
  person can restore the files in place and start again (005-32: the
  start closes what it opened). An empty `00000000000000.bergdb` left by a
  refused start would break the restore of a database whose first file
  has another name: `FileStream`'s check of the files' positions refuses
  the gap.
* **010-01**: no new setting if it can be avoided (P10); no global state
  (P9); simple first (P11); a failed or refused start says what happened
  and what to do (P7's spirit, 005-33's message).


The options
-----------

**A. created.txt as the mark of a database.** A database's directory
holds `created.txt` from the moment its creation is durable. A start
through the Pub API refuses a directory that has `created.txt` and no
stream byte.

* What it changes:
  * The creation's order, in `Db.handleEmptyStream`: the creation's 264
    bytes are forced (`storageManager.sync(CREATION_LENGTH)`, rule D1:
    the main stream's write and force, as `Db.sync(ORDINARY)` does)
    before `created.txt` is written. Today `created.txt` is written at
    once, and the creation reaches the stream's file with the buffer's
    first write, 1.6 to 36 ms after `start()` returns (005-33), so a kill
    in between can leave `created.txt` beside an empty stream (005-33's
    kills left an empty stream in 28 of 300 runs; whether `created.txt`
    was there is not recorded), which A would then refuse as a lost
    database. With the force first, `created.txt` present means that the
    creation reached the disk.
  * The check, in `DatabaseBuilderImp.start()`, before `openDirs()` opens
    D: if `D/created.txt` is a file and no `*.bergdb` file in D has a
    byte (none, or all of length 0), the start throws a new
    `bergdb.pub.util.DatabaseMissingException` (extends `DbException`),
    and opens, creates and writes nothing. The test of the files is a
    static method of `FileStream` (`hasStreamBytes(File dir)`), so that
    the suffix stays in one class. Before the lock, and safe without it:
    a running database always has a stream file with bytes (the creation
    is forced before `created.txt` exists; a cut never removes the file of
    the startup position).
  * The message: the directory held a database (`created.txt`), its
    stream files are missing or empty; the start wrote nothing; restore
    the `*.bergdb` files from a backup, or, to create a new database
    there, remove `created.txt` and the `*.bergdb` files; bergdb 015-01.
  * Optional, A+: a start of a database that holds data and has no
    `created.txt` writes it, with "creation date: unknown (written at a
    start on DATE)", so that a database whose `created.txt` was lost, or
    whose creation crashed between the force and `created.txt` (a window
    of a few milliseconds), is marked from its next start on.
* The Pub API: one new exception class; `DatabaseBuilder.start()` and
  `dir()` get a paragraph each (the refusal; the recipe for an
  application that must never create a database: check that
  `created.txt` exists before `start()`); `created.txt`'s first line
  already says "This directory contains a BergDB database." No method
  changes.
* The stream format: unchanged. `created.txt` gets a meaning at the start,
  a part of the directory's contract, not of the stream; the release
  notes say it.
* Tests: see the recommendation.
* The C clone: nothing. C does not create databases, and its open refuses
  an empty stream already (012-09).
* Covers cases 1 and 2. Not case 3: an empty or missing directory is a new
  database, as before; the Javadoc's recipe lets an application refuse it
  in one line.
* Size: S, about half a day with the tests and the gates.

**B. An explicit wish to create.** The application says when a start may
create a database.

* B1: `start()` refuses a directory with no stream byte unless the
  builder was told `createIfMissing()` (LevelDB's and RocksDB's
  `create_if_missing`, false by default). Covers cases 1 to 3. Changes the
  Pub API's behaviour: every program that creates a database must call
  the new method; in the repository, about 40 builder calls with
  `dir(` (tests, tools, benchmarks), the Javadoc's examples and README.
  P10: a new setting, and a step that BergDB's "start() creates or opens"
  (since 2012) did not need.
* B2: the opposite default: `start()` creates as today, and a new
  `mustExist()` makes it refuse. Compatible, but protects only the
  programs that call it; A's recipe gives the same with no new method.
* The stream format: unchanged. The C clone: nothing.
* Size: B1 M (the call sites and examples), B2 S.

**C. A marker file of its own**, such as `bergdb.id` with the database's
ID, written after the creation is forced; a start refuses a directory
that has it and no stream byte, and could also refuse a stream whose ID
differs. As A, with one more file in the directory and in the
documentation, and the ID check as a feature that no fault asks for.
Size S to M. A uses the file that is already there.

**D. bergdb.lock as the mark.** Not possible as it is: `FileStream`
creates `bergdb.lock` at the first open, before the creation, so a
creation that crashed before its first write leaves it, and would be
refused. Making the lock file later changes 005-63's protocol.

**E. Create only the last directory.** `FileStream` creates D but not its
missing parents (`mkdir`, not `mkdirs`). Covers a part of case 3, where
the mount point is missing (macOS's `/Volumes/X`), not where it is an
empty directory (Linux's `/mnt/x`). Changes `dir()`'s promise ("creates it
if it does not exist") and breaks programs and tests that give a new
nested path. Size S, with unknown churn in the tests.

**F. Tell, do not refuse.** `StartupInfo` gets `isCreated()`, or the start
logs a line. The application learns it after the fact, when the new
database's files are already written on the wrong volume. Adds a method
to an interface. Size S.

**G. Nothing**, and the case in the release notes' known issues. Size 0.


Recommendation
--------------

**A, with A+**, for 2026.2. It closes cases 1 and 2, the ones where BergDB
can know that a database was there, with no new setting, no method
change, no stream byte and no removal of anything; it keeps "start()
creates or opens"; and it makes `created.txt` a reliable mark, which an
application can check itself for case 3. Case 3 (an empty or missing
directory) stays as it is, in the notes' known issues with the recipe, and
B1 goes to Frans as a question for after the release (a change of the Pub
API's usage that the coordinator should not make alone).

The steps, by the implementing agent, in its clone
`/Users/f/fl/bench/016/015-01/repo` (a clone of `main`):

1. **The order** (`java/src/bergdb/core/Db.java`, `handleEmptyStream`):
   force the creation before `writeCreatedTxt()`; on a failed force the
   start fails as a failed sync does, and no `created.txt` is written.
   Check first that `storageManager.sync` works at that point of the
   start (`x.endOfLastTrans` is set for it; the sync has the
   `BufferedStream` flush at once, 005-48); if it does not, move
   `writeCreatedTxt()` to the end of `startInner`, after a sync. 0.4
   agent-hours.
2. **A+** (`Db.java`): if `createdTxtDir` is set, the stream was not
   empty and `created.txt` is missing, write it after the start, with
   "creation date: unknown". A failure to write it fails the start as
   today's `writeCreatedTxt` does. 0.3 agent-hours.
3. **The check** (`java/src/bergdb/pubimp/DatabaseBuilderImp.java`,
   before `openDirs()`; `java/src/bergdb/stream/FileStream.java`, the
   static `hasStreamBytes(File)`; new
   `java/src/bergdb/pub/util/DatabaseMissingException.java`). Also when
   replicas are given (replication is experimental; 016-01, section 3).
   0.5 agent-hours.
4. **The Javadoc**: `DatabaseBuilder.start()` (`@throws
   DatabaseMissingException`), `DatabaseBuilder.dir()` (the recipe), the
   new class (what happened and what to do), `DatabaseNotCreatedException`
   unchanged. `java/javadoc-pub.sh` builds without new warnings. 0.3
   agent-hours.
5. **The tests** (1.2 agent-hours), in `PubTester` beside
   `testCreatedTxt1` (unit, each in a temp directory, each stops its
   databases):
   * `testStreamFilesRemoved`: create, put, stop; remove the `*.bergdb`
     files; `start()` throws `DatabaseMissingException`; the directory's
     listing and `created.txt`'s bytes are unchanged (no new stream file).
   * `testOnlyFileEmptied`: as before, with the one stream file truncated
     to 0 bytes.
   * `testRemedy`: as the first, then `created.txt` removed: `start()`
     creates a new, empty database.
   * `testCrashedCreationBeforeFirstWrite`: a directory with an empty
     `00000000000000.bergdb` and `bergdb.lock`, no `created.txt` (005-33,
     row 0): `start()` creates the database.
   * `testCreatedTxtAfterForce`: a creation whose force fails (a
     `FileStreamIo` that fails `force`, as `FileStreamPowerLossTester`
     does; through the core API with `createdTxt(dir, null)`, as
     `DbTesterStream`'s test of `created.txt` does) leaves no
     `created.txt`.
   * `testCreatedTxtWrittenAtStart` (A+): a database whose `created.txt`
     was removed gets one at its next start, with "unknown".
   * Each new test fails on `main` before the change, except the remedy
     and row 0, which pass on both (they keep today's behaviour); the
     agent records this in the Log.
6. **The gate**, in the clone: `java/before-commit.sh` (`BEFORE COMMIT
   OK`, about 2 minutes), the only one required (Frans, 2026-11-03, 15:40:
   "you only need before-commit.sh to be successful to commit your
   work"); if it fits, `java/stress/level1.sh quick` and
   `java/stress/level2.sh quick` (the start, restarts on disk; about 4
   minutes). StreamDigest does not cover it (its streams are in memory)
   and need not run.
7. **The review** (016-05, section 5; 0.75 agent-hours of another agent),
   the answers here (0.4), then the hand-off to the coordinator (016-05,
   section 4; 0.1).

In all about 4 agent-hours, by agent F5 (016-05), from the coordinator's
choice. It depends on nothing else of W4.

Stops for Frans: none, if the coordinator takes A. B1, or any change
that makes the start read something new from the stream, is a stop.


Done when
---------

* `main` has A (and A+, if taken), with the tests of step 5, the Javadoc,
  and `BEFORE COMMIT OK` on the combined tree.
* The review's findings are answered in this entry's Log.
* The release notes (016-03) have the change, and case 3 with the recipe
  in "Known issues and limits".
* Case 3's question (B1) is registered by the coordinator for Frans, for
  after the release.


State
-----

2026-11-03, 15:56: **decided by the coordinator: A, with A+** (016-02,
section 6). Case 3 is 015-05, for Frans after the release; the empty
`00000000000000.bergdb` left by a refused start is 015-06, fixed with this
entry. Before that, at 15:55: the options and the recommendation were
written. Nothing was decided or made: the coordinator chooses (016-02 records it), then an
agent makes steps 1 to 6 in its clone. The code was read at `9d34ac1`:
`Db.handleEmptyStream`, `writeCreatedTxt`, `refuseIncompleteCreation`,
`DatabaseBuilderImp.start`, `openDirs`, `handleCryptoKeyAndCreatedTxt`,
`FileStream`'s constructor, `createDirIfNeeded`, `lockDir`,
`handleExistingFiles`, `createDbFileObjects`. Not yet checked: whether
`storageManager.sync` can run inside `handleEmptyStream` (step 1's
first check).

2026-11-03, 17:13, F1: done; the final hand-off is
`/Users/f/fl/bench/016/015-01/handoff/` (with `review.txt`, one patch with
015-06), for the coordinator's combined gate and commit. Case 3 stays
015-05's.



Outcome
-------

2026-11-03, by F1 (016-05), in `/Users/f/fl/bench/016/015-01/repo` from
`main` at `9d0f33c`: A with A+, as the coordinator decided.

* **The order**: a creation through the Pub API (`DbBuilder.createdTxt`)
  is made durable, rule D1, before `created.txt` is written
  (`Db.syncCreation`, which ignores interrupts as a start must, 005-46);
  a failed sync fails the start, and no `created.txt` is written. So
  `created.txt` marks a directory whose creation reached the disk. The
  core API's streams without `created.txt` are as before.
* **A+**: a start that has read a stream with data and finds no
  `created.txt` writes one, "creation date: unknown (created.txt written
  at a start on DATE)", with the stream's database ID.
* **The check**: `DatabaseBuilder.start()` refuses a `dir()` that has
  `created.txt` and no `*.bergdb` file with a byte
  (`FileStream.hasStreamBytes`), with the new
  `bergdb.pub.util.DatabaseMissingException`, before it opens the
  directory: it opens, creates and writes nothing. Its message and Javadoc
  say what to do (restore the files; or, for a new database, remove
  `created.txt` and the `*.bergdb` files). Cases 1 and 2 are closed.
* **Case 3** (an empty or missing directory) is a new database, as before;
  `DatabaseBuilder.dir()`'s Javadoc gives the recipe (check that
  `created.txt` exists before `start()`); B1 is 015-05, for Frans after
  the release. For the release notes: the refusal, the new exception (the
  only Pub API addition of W4), `created.txt`'s meaning, and case 3 with
  the recipe in "Known issues and limits".
* **Tests** (`PubTester`, unit): seven with 015-06's; all fail on the code
  as it was except the crashed creation before its first write (005-33's
  row 0), which keeps today's behaviour.
* **Gates**: `BEFORE COMMIT OK (94 s)` on `9d0f33c`; `LEVEL 1 OK` and
  `LEVEL 2 OK` (quick); `JAVADOC PUB OK`. No stream byte changes.
* Reviewed by the coordinator: no faults; one doubt noted (the Log).

Log
---

2026-11-03. Created, from 016-01's question Q4 and Frans's answer ("Fix
before. You decide how to."), with options A to G and the recommendation
A with A+.

2026-11-03, 15:56. The coordinator chose A with A+, as recommended, under
Frans's "You decide how to": it closes cases 1 and 2 with no stream byte,
no setting and no method change, and keeps "start() creates or opens".
Case 3 needs a change of the Pub API's usage (B1), which is Frans's to
decide: 015-05.

2026-11-03, 16:40 to 16:56, by F1 (016-05; the coordinator gave this
entry to F1, with 015-06), in `/Users/f/fl/bench/016/015-01/repo`, steps 1
to 5:

* **Step 1, the order** (`Db.handleEmptyStream`): with `createdTxtDir` set
  (the Pub API's directories), the creation is made durable by
  `storageManager.sync(CREATION_LENGTH)` (rule D1, the main stream's write
  and force, as `Db.sync(ORDINARY)` waits for) before
  `writeCreatedTxt`. The check of step 1: the sync works there, as
  `writePrimordialTransaction` sets `x.endOfLastTrans` and the storage
  runs since `syncStreams()`; `sync` has the main stream flush at once
  (005-48). A failed sync throws a `StreamIoException`, the start fails
  (`start()` closes the storage, 005-32), and no `created.txt` is written
  (`testNoCreatedTxtWithoutForce`). Without `createdTxtDir` (the core
  API's streams, the tests) nothing changes: no sync. The cost: one
  force at a creation.
* **Step 2, A+** (`Db.writeCreatedTxtIfMissing`, called in `startInner`
  after the stream is read and checked, before the state becomes
  `ACTIVE`): with `createdTxtDir` set and no `created.txt`, it writes one,
  "creation date: unknown (created.txt written at a start on DATE)", with
  the database ID of the stream's meta block. A failure to write it fails
  the start, as before. `writeCreatedTxt` takes the date's text and the
  ID.
* **Step 3, the check** (`DatabaseBuilderImp.start()`, before `openDirs()`,
  `refuseMissingStream`): `created.txt` a file in `dir()` and
  `FileStream.hasStreamBytes(dir)` false (a new static method: a `*.bergdb`
  file with a byte; false for a missing directory) gives the new
  `bergdb.pub.util.DatabaseMissingException` (extends `DbException`), and
  the start opens, creates and writes nothing. Also with replicas (the
  main directory's check; replicas' directories have no `created.txt`).
  015-06's change is in the same place: `checkCryptoKey()`, before
  `openDirs()` too.
* **Step 4, the Javadoc**: `DatabaseBuilder.dir()` (what `created.txt`
  means, the refusal, case 3 and the recipe: check that `created.txt`
  exists before `start()`); `start()`'s `@throws DatabaseMissingException`;
  the new class (what happened and what to do).
  `DatabaseNotCreatedException` unchanged. `java/javadoc-pub.sh`: `JAVADOC
  PUB OK`.
* **Step 5, the tests**, `PubTester` (unit, each in a temporary
  directory, each closing its databases), with helpers `createdWithData`,
  `streamFiles`, `listing` and `assertMissing`:
  `testStreamFilesRemoved`, `testOnlyStreamFileEmptied` (truncated to 0),
  `testMissingStreamRemedy` (refused, then `created.txt` removed: a new,
  empty database, and a new `created.txt`),
  `testCrashedCreationBeforeFirstWrite` (`bergdb.lock` and an empty
  `00000000000000.bergdb`, made by a `FileStream` opened and closed: the
  start creates the database, and it starts again with its value),
  `testNoCreatedTxtWithoutForce` (core API, a `FileStreamIo` whose
  `forceFile` fails once armed after the open: the start throws a
  `StreamIoException`, no `created.txt`; about 0.5 s, the sync's wait of
  500 ms before it sees the storage's error), `testCreatedTxtWrittenAtStart`
  (A+: "creation date: unknown", the same database ID line). In
  `PubTester` too, not in `DbTesterStream`, so that the tests of 015-01
  are together.
* **On the code as it was** (`Db.java`, `DatabaseBuilderImp.java` and
  `FileStream.java` of `17270d1`, the tests and the new class kept): five
  of the six fail: `testStreamFilesRemoved`, `testOnlyStreamFileEmptied`
  and `testMissingStreamRemedy` ("a new database started in ..."),
  `testNoCreatedTxtWithoutForce` ("no created.txt, expected true"),
  `testCreatedTxtWrittenAtStart` ("created.txt written, expected true");
  `testCrashedCreationBeforeFirstWrite` passes on both, as it keeps
  today's behaviour. The remedy's test fails before only at its first
  part, the refusal; its second part is today's behaviour.
* **The gate**, first run, 16:55 to 16:57: `BEFORE COMMIT FAILED: unit
  tests`, one: `PubInterruptTester.testDirAndJobJoinByInterruptedThread`,
  "StreamIoException: Thread was interrupted while waiting for D1 size
  264": a start by an interrupted thread now waits for the creation's
  sync, and `StorageManager.sync` ends on an interrupt, against 005-46's
  rule (a start ignores an interrupt until it is done, and keeps the
  flag). Fixed: `Db.syncCreation()` waits as `waitUntilClosed()` does: on
  an `InterruptedIOException` it clears the flag and waits again, and
  sets the flag at the end. `PubInterruptTester`, `InterruptTester` and
  `PubTester` pass.
* **The gate** again, 16:59 to 17:01: `BEFORE COMMIT OK (98 s)`, 1,108 unit
  tests and 78 f-tests.
* **On `9d0f33c`** (015-07 in `main`, `Db.java` and the node parsers): the
  change applies unchanged; gated again there (below).
* **The gate on `9d0f33c`**, 17:05 to 17:07: `BEFORE COMMIT OK (94 s)`,
  1,115 unit tests and 78 f-tests. `level1.sh quick` and `level2.sh quick`
  run after it.
* **`level1.sh quick`**, 17:07 to 17:09: `LEVEL 1 OK`; **`level2.sh
  quick`**, 17:09 to 17:12: `LEVEL 2 OK` (its crash and restart checks on
  disk, the conformance traces: `TRACECHECK OK: 14`).

2026-11-03. Reviewed 2026-11-03 by the coordinator (H5, 016-05, section
5), with 015-06: no faults. Checked: the creation is forced before
`created.txt`, so `created.txt` means durable; `refuseMissingStream` runs
before `openDirs()` and takes no lock; the 2012 rule for a creation that
crashed before its first write still holds (no `created.txt` then); A+
writes only for a started database that read the stream and has none; the
crypto check moved before the open with the same messages; encrypted
streams keep the `.bergdb` suffix. One doubt, noted, no change: with
replicas given, a main directory with `created.txt` and no stream is now
refused too; replication is experimental (016-01, section 3), and refusing
is the safer side. Closed: Outcome and Status above.
