005-55. Fix: the deprecated API in the build; finalize() goes
=============================================================

Status: open; decided 2026-10-27, no safety net. Kind: fix. Created
2026-10-26.

Found on 2026-10-26 by Claude (Opus 5.5, Claude Code), from the note that
every build prints (Frans: "Why the warning?"); registered at Frans's
request (2026-10-26: "Add a Fix item to 005. I want a real fix for this,
not SuppressWarnings. finalize() need to go. In the item, propose a
solution, but do not implement it."). The probes and their output are in
[55-fix-finalize/](55-fix-finalize/).


Decision
--------

2026-10-27, Frans: "Db.finalize() is the big question here. I think no
safety net is reasonable. For the end user it makes sense. Typically there
is only one database in an application. Calling close() is a reasonable
requirement. And the database is crash-tolerant anyways."

So question 1 is decided, for the alternative of 2026-10-26:
`finalize()` goes with nothing in its place, and the Pub API's promise
goes with it. "The fix" below is the fix as decided; the `Cleaner`
proposed on 2026-10-26 is kept, not chosen, under "Not chosen: a
`Cleaner`".

The issue
---------

`java/build.sh`, and so `java/before-commit.sh`, prints this on every
build:

    Note: Some input files use or override a deprecated API.
    Note: Recompile with -Xlint:deprecation for details.

`build.sh` compiles with `-nowarn`, which hides the warnings but not this
note: javac always prints it. `-Xlint:-deprecation` does not hide it
either. With `-Xlint:deprecation` (`--release 17`, javac 27) the build
has eight uses of deprecated API, all in the main compile; `stress/` has
none:

| Where | Deprecated | What it does |
|---|---|---|
| `Db.java:1242`, `:1244` | `Object.finalize()` | `Db.finalize()` calls `stop()` when the collector finds a `Db` that was not stopped |
| `CcDbTest.java:145` (src-dev, manual) | `Object.finalize()` | the test object's `finalize()` stops its database |
| `CcDbNightTest.java:168` (src-dev, night) | `Object.finalize()` | the same, in a night test (`bergdb.dev.Night`, which `night.sh` runs) |
| `ValueNodeTotalMem.java:87`, `:89` (src-dev, manual) | `Object.finalize()` | an experiment: a running estimate of the memory of value nodes, from their finalization |
| `OptionalIcuCollatorFactory.java:37` | `Class.newInstance()` | makes the ICU collator factory, which it finds by name |
| `TestRunner.java:118` (nanotest) | `Class.newInstance()` | makes the object of a JUnit test; there are none, as JUnit is not on the class path |

Java deprecated finalization in Java 9, and for removal in Java 18
(JEP 421): `--finalization=disabled` turns it off, a later release is to
turn it off by default, and one after that to remove it. In Java 27 it is
still on by default (the probe below). `Class.newInstance()` is
deprecated since Java 9, as it passes on any exception of the
constructor, checked ones too, without wrapping it.

Only `Db.finalize()` does anything that matters; the rest are small
(the fix, points 3 and 4).


What Db.finalize() is for
-------------------------

A promise, in two places:

* `Db`'s class Javadoc, "Db shutdown": the resources of a `Db` (open
  files, running threads) "are guaranteed to be *eventually released*
  without any action from the Db user as the Db object is garbage
  collected. The finalize() method makes sure that the resources are
  released."
* The Pub API, `Database.stop()`: "It is not a requirement that stop() is
  called once the Database is not longer used. If there are no references
  to this Database object or to any Connection or Transaction object
  created with this Database, the Database will be stopped automatically
  when garbage collected."

The storage cannot keep it by itself. Its consumer threads, one per
stream, hold it, and a thread is a root for the collector (Frans's notes
in `BufferedStream`, of 2012-12, and in `StorageManager`). The `Db` can,
as long as nothing that a thread holds refers to it. The note at the end
of `Db.java`: "There must be no reference (direct or indirect) to a Db
object from a thread started by the database. Otherwise, the Db object
will never be available for garbage collection."

`finalize()` calls `stop()`, which since 005-35 starts the one close of the
database in a thread `Db-close-N`: it writes what is buffered, closes the
streams and their files, and ends their threads.


What the probes found
---------------------

On `356c058`, the main branch of today, with Java 27 on F53:
[55-fix-finalize/run.sh](55-fix-finalize/run.sh), its output in
[55-fix-finalize/out/](55-fix-finalize/out/).

`FinalizeProbe` starts a database through the Pub API, uses it, and drops
it without `stop()`; then `System.gc()` runs, up to 50 times 100 ms
apart, until the storage thread has ended:

| Case | Finalization on (the default) | `--finalization=disabled` |
|---|---|---|
| `mem`: in memory, 100 puts | after 1 collection the `Db` is gone and its storage thread has ended | after 50 collections the thread is still there |
| `file`: a directory, 100 puts | after 1 collection the thread has ended and the stream's file is closed (open files 10, then 9) | after 50, the thread and the file are still there |
| `evict`: in memory, a 4 MB cache, 400,000 keys, then gets of them all | after 50, the `Database` is gone but not its `Db`: the storage thread and the eviction thread are still there | the same |

So finalization is what closes a database that is not stopped, and with
it disabled nothing does. And a database whose eviction thread has
started is never collected, finalization or not. The eviction thread,
`bergdb-evictor` (009, decision T5a; since 009's step 3b, `4a1fc5e`,
2026-10-25), holds the `Db` (`Eviction.EvictorRun.db`, and `Db.Internal
in` on its stack, an inner class that holds the `Db`), and when idle it
waits a second at a time for as long as the database is active, that is
until `stop()` (005-51). Such a database keeps its storage threads, its
open files and its write buffer, and also its cache and all else it
holds, until the JVM exits. Against the note in `Db.java`. Nothing else
holds it: in a scratch clone where the eviction thread ends when it has
nothing to do (one line, not kept;
[out/check-evictor-ends.txt](55-fix-finalize/out/check-evictor-ends.txt)),
the `Db` of `evict` is collected, and finalization closes it as in `mem`.

`SuiteThreads` runs the unit tests or the f-tests in one JVM, as
`before-commit.sh` does, then collects garbage and counts BergDB's
threads:

| Suite | After collection, finalization on | After collection, `--finalization=disabled` |
|---|---|---|
| unit | no storage thread; 7 MB of heap in use | 211 storage threads; 1,083 MB |
| f | 1 storage thread and 1 eviction thread; 11 MB | 101 storage threads and 1 eviction thread; 716 MB |

With finalization disabled, every database that a test did not stop is
left, and its storage threads (one per stream) count it.

Both suites pass with finalization disabled: no test needs `finalize()`
for its result, only for the cleanup. The f-tests have one database of
the eviction case: it stays, with finalization on too.


The fix
-------

As decided on 2026-10-27: `finalize()` goes with nothing in its place. An
application calls `stop()` or `close()` when it is done with a database,
as it closes a file or a socket. For it: 010-P8, nothing depends on the
collector; 010-P3 and P9, no cleaner thread and nothing shared by the
databases of a JVM; 010-P11, less code. Against it: the Pub API's
promise goes, a change of the API (2026.1 is internal, so no user outside
is affected), and the tests must stop their databases (point 4).

1. **`Db`: no `finalize()`.** The class Javadoc ("Db shutdown") says that
   `stop()` or `close()` is required, and what a database that is not
   stopped keeps until the JVM exits: its storage threads (one per
   stream, parked, no wake-ups since 005-14), its open files, its write
   buffer (10 MB by default), its cache, and with a memory storage its
   whole stream. What it has committed is still written: its consumer
   thread writes the buffer within the buffer time, as after any commit.
   The storage threads are daemon threads, so they do not keep the JVM
   alive; at exit, what the buffer holds and has not written is lost as
   in a crash, which the database tolerates: the next start finds it as
   of an earlier commit. Finalizers do not run at exit either, so that
   part is as today. The note at the end of `Db.java`, that no thread of
   the database may refer to the `Db`, goes: nothing depends on the `Db`
   being collected.
2. **The Pub API.** In `Database.stop()`'s Javadoc, the paragraph "It is
   not a requirement that stop() is called ..." becomes the requirement,
   with what a database that is not stopped keeps (point 1). Noted for
   the release (item 008) as a change of the API.
3. **The eviction thread: unchanged here (recommended, question 3).**
   The `Cleaner` proposal changed the eviction thread so that a dropped
   `Db` can be collected. With no safety net, a dropped database keeps its threads,
   files and write buffer whether its `Db` is collected or not;
   collecting it would free the cache, and with a memory storage not even
   most of what it holds. Not worth a `WeakReference` in `EvictorRun`.
   The eviction thread already ends within a second of `stop()` (it
   checks `in.isActive()` once a second); 005-51 makes it end at once.
   This corrects the entry of 2026-10-26, which said that no safety net
   needs that change too.
4. **The tests stop their databases.** Every unit test and f-test that
   starts a database stops it, in a `finally` (or `close()`, which waits
   for the close). Today, with finalization disabled, the unit tests leave
   211 storage threads and 1,083 MB of heap, the f-tests 101 and 716 MB
   ("What the probes found"). `CcDbTest` and `CcDbNightTest` stop their
   database at the end of `go()`, in a `finally`.
5. **A check that they keep doing so (question 5).** At the end of
   `bergdb.dev.Unit` and `bergdb.dev.F`, the suite counts the threads
   `BufferedStream-consumer-*` and `bergdb-evictor`, after a bounded wait
   (a few seconds) for the closes that `stop()` started (005-35); any
   left is a database that a test did not stop, and the suite fails.
   Without the check nothing notices a new test that forgets: no
   finalizer cleans up after it, and the suites slowly grow in threads
   and memory.
6. **`ValueNodeTotalMem`** registers each node with a `Cleaner` whose
   action reports the node's size (it holds the listener and the size,
   not the node): the same experiment by the current means (005-10's C1:
   the manual tests are kept). A measurement in a manual experiment, not
   a safety net.
7. **`Class.newInstance()`** becomes
   `getDeclaredConstructor().newInstance()`, which wraps a constructor's
   exception in an `InvocationTargetException`: in
   `OptionalIcuCollatorFactory`, with one
   `catch (ReflectiveOperationException e)` that throws the `Bug` as now,
   with the exception; in `TestRunner`, nothing more, as `ConsoleUI`
   already unwraps an `InvocationTargetException`.

No `@SuppressWarnings` and no new flag in `build.sh`. After the fix
javac prints no note, and a new use of deprecated API brings it back.


Not chosen: a `Cleaner`
-----------------------

Proposed on 2026-10-26: a `java.lang.ref.Cleaner` in `Db` in place of
`finalize()`, which would keep the Pub API's promise by closing a dropped
`Db`'s storage, with an eviction thread that lets go of the `Db` while it
waits. Not chosen on 2026-10-27 (the decision).


Questions
---------

1. Keep the Pub API's promise, or drop it? Decided 2026-10-27: drop it,
   no safety net (the decision).
2. The `Cleaner`'s thread and its wake-up once a minute. Moot: no
   `Cleaner` in `Db`. The one in `ValueNodeTotalMem` (the fix, point 6)
   is in a manual experiment.
3. The eviction thread's `WeakReference` (in the `Cleaner` proposal), with
   005-51 or before it? Recommended now: not at all (the fix, point 3).
   005-55 then does not touch the eviction thread and is independent of
   005-51.
4. Beyond this entry: at `--release 27`, javac 27 finds 15 more uses:
   `Thread.getId()` (6), `new Long(long)` in src-dev's memory experiments
   (6), and `setPerformancePreferences` of `Socket` and `ServerSocket` in
   `NetworkRoundTrip` (3, for removal)
   ([out/lint-release27.txt](55-fix-finalize/out/lint-release27.txt), from
   [lint.sh](55-fix-finalize/lint.sh)). For a move to a later release,
   not for this entry. At both releases javac also finds one `@deprecated`
   in Javadoc without `@Deprecated` (`StoredTrans.getValueNode(long[])`,
   which only its own test calls); `-nowarn` hides it, and it is not part
   of the note.
5. The suites' check for databases not stopped (the fix, point 5)?
   Recommended: yes; it is a few lines, and it is what keeps point 4
   true.
6. Beyond this entry: should `Db` and `Database` implement
   `AutoCloseable`, for try-with-resources and for the warnings of IDEs
   about a resource not closed? `Db` has `close()` already; `Database`
   has only `stop()` and would get a `close()`, the same as `stop()` or
   one that waits as `Db.close()` does. Not needed for this entry.


Done when
---------

* No `finalize()` and no `Class.newInstance()` in `java/`; `build.sh`
  prints no note, and `lint.sh` finds no use of deprecated API at
  `--release 17` (eight today,
  [out/lint-release17.txt](55-fix-finalize/out/lint-release17.txt)).
* `Db`'s class Javadoc and `Database.stop()`'s say that `stop()` or
  `close()` is required, and what a database that is not stopped keeps;
  no Javadoc in `java/src` promises a stop by the collector.
* The unit tests and the f-tests stop every database they start: the
  probe `SuiteThreads`, with finalization on and with
  `--finalization=disabled`, finds no storage or eviction thread at the
  end of either suite; with question 5 accepted, the suites check this
  themselves.
* `stop()`, `close()` and a start that throws close once, as before (the
  tests of 005-32 and 005-35).
* `java/before-commit.sh` prints `BEFORE COMMIT OK`.


First step
----------

Find the tests that leave a database: run the suites with
`--finalization=disabled` and count, after each test, the storage threads
still alive, so each leak is tied to its test. Look also for tests that
drop a database on purpose, to model a crash; such a test closes the
storage some other way (a test hook), as no finalizer does it for them.


Size and order
--------------

S to M: a few lines in `Db`, `Database` and the two `newInstance` calls;
most of the work is in the tests that leave the 211 storage threads (one
per stream, so fewer databases), and the suites' check. Independent of
005-51 with question 3 as recommended, and of the rest.
