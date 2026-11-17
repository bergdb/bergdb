028-07. Investigate: one start's sync blocks every start of the JVM
===================================================================

Status: done. Kind: Investigate. Frans: none.
Created 2026-11-13 by Frans Lundberg.

What: a Pub start holds the lock of the class `DatabaseImp` through
`Db.syncCreation`.

Why: a sync that waits (after an `OutOfMemoryError`, or on a slow disk)
blocks every other start and open in the JVM (`tools/jstack2.txt`).

Frans: none.

Done when: the lock is not held across the sync, or
`DatabaseBuilder.start()`'s Javadoc says that starts wait for each other.

First step: why the start holds the class lock.


Findings
--------

* **Where.** `DatabaseImp.createAndStart(Db)`, which
  `DatabaseBuilderImp.start()` calls after it has opened the directories and
  built the `Db`, was `static synchronized`: the lock of the class
  `DatabaseImp` through `new DatabaseImp`, `db.start()` (with
  `Db.handleEmptyStream` and `syncCreation` for a new directory) and the
  index manager's start.
* **Why.** No reason is written anywhere. The method is
  `public static synchronized` in the 2017 source imported on 2026-10-14
  (`0257e0ba`), with no comment; no other code takes the lock (no
  `synchronized (DatabaseImp.class)`, no other static synchronized method
  in the class). It reads as a defensive lock of 2017, not a design rule.
* **What it could have guarded**, each checked:
  - *One database per directory.* `FileStream`'s lock (005-63):
    `LOCKED_DIRS` under its own lock, the `bergdb.lock.` system properties
    by `putIfAbsent`, and the operating system's file lock. It is taken in
    `DatabaseBuilderImp.openDirs()`, before `createAndStart()` and so
    outside the class lock: the class lock never ordered it.
  - *One database per stream of `memory()`* (015-65):
    `refuseStreamInUse()`, also before `createAndStart()`, also outside the
    class lock. A builder is not thread-safe; that is unchanged.
  - *A second start of one `Db`.* `Db.start()` checks the state ZERO under
    the `Db`'s `writeLock` and `readSync`, and refuses a second start with
    `IllegalDbStateException`. `DatabaseBuilderImp` builds a new `Db` for
    each start, so the Pub API never starts one `Db` twice.
  - *The new database's own state* (`DatabaseImp`'s fields, its
    `IndexManager`, `StartInfoImp`): made by this start, seen by no other
    thread until `createAndStart()` returns.
  - *Static state in the start's path.* A search for static fields that are
    not final in `src/bergdb`: test hooks (volatile, read once:
    `DatabaseImp.testHookAfterStart`, `StorageManager.testHookSync`,
    `Db.testHooks`, `Util.testHookStart` and others), statistics
    (`Dag.stat*`, volatile), `Eviction`'s process totals and `Audit`'s
    counters (each under its own class's lock), and one unguarded:
    `Util.today()`'s static `SimpleDateFormat`, which `Db` calls for
    created.txt when it creates a database (or writes a missing one). A
    `SimpleDateFormat` is not thread-safe (019-08): threads that format at
    once share its calendar. The class lock ordered the Pub starts' calls;
    the Core starts' calls were never ordered. With every thread formatting
    the same day, the race gives a wrong date only at midnight (a check of
    8 threads with 5,000 calls each gave no wrong string), so it was never
    seen; it is fixed anyway (below).
* **So** the lock guarded only the `SimpleDateFormat`, by chance, and
  blocked every start of the JVM behind one start's sync: after an
  `OutOfMemoryError` (026-13, U13-3) or on a slow disk, also behind a start
  that reads a long stream.


What was done
-------------

Commit `72e8de5d` (2026-11-16):

* `DatabaseImp.createAndStart()` is `static`, not `static synchronized`;
  its comment says why the lock is not needed.
* `Util.today()` and `Util.dateAndTime()` format with immutable,
  thread-safe `DateTimeFormatter`s instead of static `SimpleDateFormat`s;
  the unused `compactDateFormat` is gone.
* Tests in `PubTester`:
  - `testStartDoesNotWaitForAnotherStart`: a test hook
    (`StorageManager.testHookSync`) holds the first sync of the start of
    directory a on a latch (at most 20 s). Meanwhile a start of directory
    b (with a put and a sync) and one of `memory()` run to the end, and a
    start of a is refused at once (`DirectoryInUseException`); then a's
    start ends, and a works and has created.txt. With the old lock put
    back, the test fails (b's start waits for the hook's time limit).
  - `testStartsOfOneDirectoryAtOnce`: 4 threads start one new directory at
    the same time, 3 rounds: exactly one database starts, each other start
    is refused with `DirectoryInUseException`, and the database holds the
    one's write after a restart.
* No Javadoc change: starts of different databases do not wait for each
  other now, and `DatabaseBuilder.start()` said nothing about it.
* Gates: `java/before-commit.sh` BEFORE COMMIT OK (101 s);
  `java/stress/level1.sh` LEVEL 1 OK.

Every interleaving the lock prevented, and why the new form keeps what
matters:

* Two starts of different directories: they share no state but
  `Util.today()`, now thread-safe; they now run at the same time, which is
  the point of the change.
* Two starts of one directory: ordered by `FileStream`'s lock before and
  after the change (the class lock was taken later); the second test checks
  it.
* Two starts of one `memory()` builder: unchanged, refused before
  `createAndStart()`.
* Two `createAndStart()` calls on one `Db` (only BergDB's own tests can
  make them; the method is package-private): `Db.start()` orders them by
  the `Db`'s locks and refuses the second. One difference, of no Pub API
  use: before, the second waited for the whole first `createAndStart()`
  and then, refused, closed the `Db` in its catch; now it waits only for
  the first's `db.start()`, and its catch may close the `Db` while the
  first's index manager starts. In both forms the refused call closes the
  database that the other call started, against `Db.start()`'s Javadoc
  ("nothing is closed then"). A possible small todo, not done here.
* A start beside a running database's calls (`stop()`, transactions):
  those never took the class lock; unchanged.


Log
---

2026-11-13. Registered by coord-1113, from 026-13, section 5 (U13-3).

2026-11-16. Taken by an agent of coord-1116 (in progress), in a clone on
branch 028-07-start-lock.

2026-11-16. Done: the class lock removed, `Util`'s date formats made
thread-safe, two tests; BEFORE COMMIT OK, LEVEL 1 OK; by an agent of
coord-1116 (Claude, Opus 5.5).
