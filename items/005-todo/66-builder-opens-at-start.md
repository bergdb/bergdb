005-66. Implement: the Pub API's builder opens the directories in `start()`
==========================================================================

Status: open. Kind: implement. Created 2026-10-28.

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
