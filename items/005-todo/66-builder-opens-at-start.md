005-66. Implement: the Pub API's builder opens the directories in `start()`
==========================================================================

Status: done (2026-10-28; see Outcome). Kind: implement. Created
2026-10-28.

Registered at Frans's request (2026-10-28, 09:43: "Register this as a new
005 "Implement" entry. Then implement it and commit if successful."), by
Claude (Opus 5.5, Claude Code), from 005-63's outcome (a builder that is
never started) and the proposal made after it in the same session.


The issue
---------

`DatabaseBuilder.dir()` opens the directory's `FileStream` at once, and
`replica()` opens the replica's (`DatabaseBuilderImp`). Since 005-63 a
`FileStream` holds its directory's lock until it is closed, and a builder
has no `close()`. So a directory stays held, and refuses every other
database on it, in the JVM and in other processes, until the JVM ends,
when:

1. a builder whose `dir()` succeeded is never started, or a builder call
   after `dir()` throws;
2. `dir()` is called twice: the first `FileStream` is replaced
   (`DbBuilder.mainStream`) and never closed;
3. `replica()` is called before `dir()`: `dir()` replaces the replica, as
   `replica()`'s Javadoc warns ("Call dir() first: a replica added before
   it is dropped"), and the replica's directory stays held.

Before 005-63 the same cases left open files only. A failed `start()`
already closes what the builder opened (005-32).


The change
----------

* `dir()` and `replica()` record the directories; `start()` opens them,
  the database's first, then the replicas in the order given, inside the
  `try` that closes the streams when the start fails (005-32).
  `memory()` and `mainStream()` (not Pub API) drop a recorded `dir()`: the
  last of `dir()`, `memory()` and `mainStream()` decides the main stream.
* So a builder holds nothing until `start()`; the last `dir()` wins; a
  replica given before `dir()` is kept, and the rule "call dir() first"
  goes.
* A bad directory, and since 005-63 one in use (`DirectoryInUseException`),
  is reported by `start()`, as the `StreamIoException` that `dir()` threw,
  with the same cause. `replica()` keeps `throws IOException` in its
  signature, so that callers still compile, and no longer throws it.
* A start without a stream throws `IllegalStateException`, as today,
  before anything is opened.
* Javadoc: `DatabaseBuilder`'s `dir()`, `replica()` and `start()`;
  `Database.stop()`'s sentence from 005-63 ("DatabaseBuilder.dir()
  throws") names `start()`. `releases/next.md`: 005-63's line names
  `start()`; a line for this change.
* Not changed: `Database.addReplica()` opens its directory at once (it is
  not a builder); the core API, where the caller makes the stream and owns
  it until the start.

**Tests** (`PubTester`):

* `dir()` on a directory that a running database holds returns; `start()`
  is refused (`StreamIoException`, the cause `DirectoryInUseException`).
* A builder with `dir()` that is dropped holds nothing: a database starts
  on its directory; `dir()` of a new directory creates nothing before
  `start()`.
* `dir()` twice: the database is in the second directory, and the first
  is free.
* `replica()` before `dir()`: the replica is kept and written, and after
  `close()` a database starts on the replica's directory and reads the
  data.
* The tests of a failed start (005-32) pass as they are.


Done when
---------

The change with the tests above, `releases/next.md` updated,
`java/before-commit.sh` passes, and it is committed.


First step
----------

The change in `DatabaseBuilderImp`.


Outcome
-------

2026-10-28, by Claude (Opus 5.5, Claude Code), as registered; in a clone
on `9697502`, the code in commit `7747325` (java/ and
releases/next.md).

* `DatabaseBuilderImp`: `dir()` records the directory, and `replica()`
  the replica's by name (a `LinkedHashMap`: the same name replaces, as in
  `DbBuilder.stream()`); `memory()` and `mainStream()` drop a recorded
  `dir()`. `start()` first checks that there is a stream
  (`IllegalStateException`, nothing opened), then `openDirs()` opens the
  database's directory and then the replicas', inside the `try` that
  closes the builder's streams when the start fails (005-32). A null name
  or directory is refused at once, as before.
* Javadoc: `DatabaseBuilder.dir()` (`start()` opens the directory,
  creates it and reports its errors; 005-63's paragraph names `start()`),
  `replica()` (opened by `start()` after the database's own; "call dir()
  first" gone; `throws IOException` kept, no longer thrown), `start()`
  (the `StreamIoException`, `DirectoryInUseException` as its cause);
  `Database.stop()`: `DatabaseBuilder.start()` throws.
  `releases/next.md`: 005-63's line names `start()`, and a line for this
  change.
* Tests in `PubTester`: `testBuilderOpensInStart` (the first three cases
  above) and `testReplicaBeforeDir`. With the `DatabaseBuilderImp` before
  this change both fail: `dir()` of a held directory throws where it now
  returns, and the dropped replica's directory stays held, so the start
  on it is refused. The 005-32 tests pass as they are.
* Gates, in the clone: `java/before-commit.sh` (deps: 9 packages, as
  `package.html` allows; unit 1058 tests, f 74; `BEFORE COMMIT OK
  (94 s)`) and `level2.sh quick` (`LEVEL 2 OK`; its `BryanRepro` starts
  through the builder).
