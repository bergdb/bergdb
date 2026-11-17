015-56. Fix: a refused second start() of one builder closes the running database's stream, and the database fails
=================================================================================================================

Status: done. Kind: Fix. Created
2026-11-04 by Frans Lundberg.

For 2026.2: new in this release (2026.1 refused the second start another way).

What: review R8's finding R8-F10 (items/016-release-2026-2/06-reviews/R8.md,
section R8-F10: where, intended, actual, effect, a proposed fix), shown by a
test or probe in 06-reviews/R8/. In 2026.1: no, not this way: there `dir()` opened the `FileStream` and a second `start()`

Done when: a test that fails on the code before the fix passes, and the
fix is in `main` after `before-commit.sh`.

First step: the test of R8-F10, in a tester of the area.


State
-----

2026-11-04, 07:52: the fix, its two tests, two mutations and
`before-commit.sh` done in the clone `/Users/f/fl/bench/016/015-56/repo`
(`main` at `abe7785`); handed off for review in
`/Users/f/fl/bench/016/015-56/handoff/`. Open: the review (016-05,
section 5), the combined gate, the commit in `main`.


The cause and the fix
---------------------

**The cause**: `DatabaseBuilderImp.start()` closed every stream of its
`DbBuilder` when anything in `openDirs()`, `handleCryptoKeyAndCreatedTxt()`
or `build()` threw (`DbBuilder.closeStreams`, 005-32). Until 005-66 those
were the streams that `dir()` and `replica()` had opened for this start.
Since 005-66 the start opens them, and the `DbBuilder` keeps them after a
successful start, as the running database's: a second `start()` of the
builder opens the directory, the open is refused (005-63, the
`DirectoryInUseException` of `FileStream.lockDir`, before the lock file is
opened), and the catch closed the first database's `FileStream` and its
replicas' streams. That database's next flush failed, its next `sync()`
failed it (`DbFailedException`, "Main storage not active"), and what it had
not flushed was lost; the close released its lock, so a start on the
directory by another builder succeeded while the first `Database` was open.
A start of a second builder on the directory was refused without harm, as
its `DbBuilder` holds nothing then.

**The fix** (`DatabaseBuilderImp`): `openDirs()` adds each `FileStream` to
a list of the start's own, as it opens it and before it gives it to the
`DbBuilder`; a start that throws closes that list's streams and no other.
The streams of an earlier start stay in the `DbBuilder`, untouched by a
later start that fails; a later start that opens its directories replaces
them there, as before. `DbBuilder.closeStreams` had no other caller and is
removed. Javadoc: `DatabaseBuilder.dir()`'s paragraph of 005-63 names the
database "that this builder started" among those that have the directory,
and adds "the database that has it runs on as before (bergdb 015-56)". No
stream byte and no Pub API signature changes.

One change of behaviour besides the fault: a stream that the start did not
open, from `memory()` or from `mainStream()` and `stream()` (not Pub API),
is no longer closed by a start that throws before the `Db` is built. A
`MemoryStream` holds no file; the core API's caller makes its stream and
owns it until the start (005-66, "Not changed"). A start that throws after
the `Db` is built closes the `Db` and its streams, as before
(`DatabaseImp.createAndStart`, `testExceptionAfterStartClosesDb`).

**Tests** (`PubTester`, after 005-66's `testBuilderOpensInStart` and
`testReplicaBeforeDir`):

* `testSecondStartOfOneBuilder` (R8-F10's case; its test is not in
  06-reviews/R8/R8-tests.diff, so it is written after the finding's
  evidence): one builder with `dir()`, start, put `/a`, sync; a second
  start of the builder is refused (`StreamIoException`, the cause
  `DirectoryInUseException`), the directory's files and lengths are as
  before; put `/b` and `sync()` on the first database; a start of another
  builder on the directory is refused (the lock is held); after `close()`
  the builder starts again and reads `/a` and `/b`. 32 ms.
* `testRefusedStartClosesOnlyItsOwn`: a builder with `dir()` and a
  replica, started; its second start, and a start on the replica's
  directory, are refused; given a new directory, the builder's start opens
  it and is refused at the replica's (the running database has it); the
  replica's directory is still refused, and the new directory is free (a
  database starts there); the first database puts and syncs, and after
  its `close()` the replica holds the put. 99 ms.


Log
---

2026-11-04. Registered by the coordinator of release 2026.2 (016-02).

2026-11-04, 07:41 to 07:52, by an agent of 016-05, in
`/Users/f/fl/bench/016/015-56/repo` (a clone of `main` at `abe7785`):

* **Read**: R8-F10 (016-06, R8), 005-66, 005-63's Javadoc in
  `DatabaseBuilder` (`dir()`, `start()`) and `Database.stop()`,
  `DatabaseBuilderImp.start` and `openDirs`, `DbBuilder.closeStreams` and
  `mainStream`, `FileStream`'s constructor, `lockDir` (a refusal by
  `LOCKED_DIRS` or the system property opens no file, so the running
  database's lock is not dropped by a second channel) and
  `closeAfterFailedOpen`, `DatabaseImp.createAndStart`, `Db(DbBuilder)`,
  005-32's tests in `PubTester`.
* **The tests first, on `main`'s code**: `testSecondStartOfOneBuilder`
  fails with R8-F10's failure: the first database's `sync()` after the
  refused start throws `DbFailedException` ("A sync failed on the storage
  ... StorageManager has error: Main storage not active. ... The flush
  failed"). `testRefusedStartClosesOnlyItsOwn` fails with "started, the
  replica's directory": the refused second start closed the running
  database's replica stream and released its lock. With the fix both pass,
  as do `PubTester` and `DatabaseBuilderImp` (94 tests, 1.3 s).
* **Mutations** (built and run, then the fixed file put back): M1 is
  `main`'s code (above). M2, the catch closes nothing:
  `testRefusedStartClosesOnlyItsOwn` fails (the new directory "is in use
  by another BergDB database in this JVM", held by the refused start's
  unclosed stream); no other test of a failed start fails
  (`testFailedStartsLeaveNothing`, `testFailedStartsDirectoryRemoved`,
  `testUnknownCryptoAlgorithmClosesFile`, `testBuilderOpensInStart`), as
  their failures come before `openDirs()` (015-06) or after `build()`; so
  the new test is the one that checks that a refused start closes what it
  opened.
* **The gate**: `java/before-commit.sh`, 07:49:08 to 07:50:55: `BEFORE
  COMMIT OK (107 s)`, 1,143 unit tests, 79 f-tests. Not run: the level
  scripts (no level's mechanism changed).
* **A finding outside the entry**, for the coordinator (not fixed): a
  second `start()` of a `memory()` builder whose database runs is not
  refused; it gives the same `MemoryStream` to a second database, and both
  append to it (a probe: the second start returns, sees `/a` of the
  first, and each then misses the other's puts). The same with
  `mainStream()`; with a crypto key, the second start wraps the first's
  `SalsaStream` again (`handleCryptoKeyAndCreatedTxt`). As in 2026.1;
  `memory()`'s Javadoc promises nothing on it.

2026-11-04, 07:55, by the coordinator (016-05, H5): reviewed, no fault. A
start that throws closes only the FileStreams it opened itself; a refused
open (`lockDir`) throws before its stream is added to the list or to the
DbBuilder, so the running database's streams stay. The finding outside the
entry, a second start() of a memory() builder not refused, is 015-65.
Committed after the combined gate.
