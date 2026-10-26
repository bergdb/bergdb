005-55. Fix: the deprecated API in the build; finalize() goes
=============================================================

Status: open. Kind: fix. Created 2026-10-26.

Found on 2026-10-26 by Claude (Opus 5.5, Claude Code), from the note that
every build prints (Frans: "Why the warning?"); registered at Frans's
request (2026-10-26: "Add a Fix item to 005. I want a real fix for this,
not SuppressWarnings. finalize() need to go. In the item, propose a
solution, but do not implement it."). The probes and their output are in
[55-fix-finalize/](55-fix-finalize/).


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


The fix, proposed
-----------------

1. **`Db`: a `Cleaner` instead of `finalize()`.** `java.lang.ref.Cleaner`
   (Java 9) is the replacement that JEP 421 points to: an action that
   runs once the collector has found an object unreachable, in the
   Cleaner's own thread, without the object.
   * The action, a static nested class of `Db`, holds the
     `StorageManager` and the `Eviction`, never the `Db`; a lambda that
     reads a field of the `Db` would hold the `Db`, which would then never
     be collected. It closes the storage as `closeStorage()` does, without
     the write lock (no transaction runs in a `Db` that nothing reaches),
     and ends the eviction thread (point 2).
   * The `Db` registers it in its constructor, right after the storage is
     made (`createStorageManager`, which starts the storage threads), with
     one `Cleaner` for BergDB: a static final field, made with the first
     `Db`, whose daemon thread is named `bergdb-cleaner`. So the storage of
     a `Db` whose constructor throws after that point is closed as well,
     as `finalize()` closes it today.
   * `closeStorage()`, the close of `stop()`, `close()` and a start that
     throws (005-32, 005-35), closes through the `Cleanable`: `clean()`
     runs the action at most once and unregisters it, so a close by the
     application and one by the cleaner are the same close, run once. The
     action keeps the close's `IOException` for `closeStorage()` to return.
   * `finalize()` goes. The class Javadoc ("Db shutdown") and the note on
     garbage collection at the end of `Db.java` say what holds instead.
   * As with `finalize()` today, the collector may find a `Db`
     unreachable while a call on it still runs, the last call before the
     application drops it (JLS 12.6.1); the storage could then close under
     that call, which fails. `Reference.reachabilityFence` in the API's
     methods is the JDK's remedy. Not proposed: it takes a collection
     during that last call, and it has not been seen.
2. **The eviction thread lets go of the `Db` while it waits.** It holds
   the `Db` only while it runs batches: `EvictorRun` keeps a
   `WeakReference<Db>`, takes the `Db` from it for each round of batches,
   and holds neither the `Db` nor a `Db.Internal` while it waits; it ends
   when the reference is empty. A close ends it at once, by a new
   `Eviction.stop()` that sets a flag and notifies `evictorLock`, called
   by the action of point 1, instead of after up to a second, as 005-51
   also asks. 005-51's question 1 offers another way, a thread that ends
   when it has nothing to do; that lets go of the `Db` too, but starts a
   new thread for every burst of loads over the trigger.
3. **Test code.** `CcDbTest` and `CcDbNightTest` stop their database at
   the end of `go()`, in a `finally`. `ValueNodeTotalMem` registers each
   node with a `Cleaner` whose action reports the node's size (it holds
   the listener and the size, not the node): the same experiment by the
   current means (005-10's C1: the manual tests are kept).
4. **`Class.newInstance()`** becomes
   `getDeclaredConstructor().newInstance()`, which wraps a constructor's
   exception in an `InvocationTargetException`: in
   `OptionalIcuCollatorFactory`, with one
   `catch (ReflectiveOperationException e)` that throws the `Bug` as now,
   with the exception; in `TestRunner`, nothing more, as `ConsoleUI`
   already unwraps an `InvocationTargetException`.
5. **The Pub API's promise stays.** `Database.stop()`'s Javadoc says what
   "stopped automatically" means: the storage is closed some time after
   the collector finds the database unreachable, when the JVM chooses;
   an index job holds the database until it is done.

No `@SuppressWarnings` and no new flag in `build.sh`. After the fix
javac prints no note, and a new use of deprecated API brings it back.


The alternative: no safety net
------------------------------

`finalize()` goes with nothing in its place: an application must call
`stop()` or `close()`, as it closes a file or a socket.

* A database that is not stopped keeps its storage threads (parked, no
  wake-ups since 005-14), its open files and its write buffer (10 MB by
  default) until the JVM exits. What it has committed is still written:
  its consumer thread writes the buffer within the buffer time, as after
  any commit. Its cache and the rest of its memory go, once point 2 is
  done, which this alternative needs too.
* For it: 010-P8, nothing depends on the collector; 010-P3 and P9, no
  cleaner thread and nothing shared by the databases of a JVM; 010-P11,
  less code.
* Against it: the promise of the Pub API goes, a change of the API (2026.1
  is internal, so no user outside is affected); and the tests, whose
  databases that are not stopped would hold 1,083 MB of heap after the
  unit tests and 716 MB after the f-tests, with 211 and 101 storage
  threads. Each such test would then stop its database, or the suites
  hold that memory until they end.


Questions
---------

1. Keep the Pub API's promise, the proposal, or drop it, the alternative?
2. The JDK's `Cleaner` thread waits with a timeout of 60 seconds
   (`jdk.internal.ref.CleanerImpl.run`, Java 27) for as long as its
   `Cleaner` is reachable: BergDB's one cleaner thread would wake once a
   minute, from the first `Db` until the JVM exits. A departure from
   010-P3, small beside the JVM's own (its `Common-Cleaner` does the same;
   the JVM alone woke about 25 times a second in 005-14); and one thread
   that the databases of a JVM share, for their closes only (P9). Accept
   it and record it under P3 in 010-01, or use a thread of BergDB's own
   that waits on a `ReferenceQueue` of `PhantomReference`s without a
   timeout, about 20 lines more than the `Cleaner`?
3. Point 2 with 005-51, which changes the same wait, or before it?
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


Done when
---------

* No `finalize()` and no `Class.newInstance()` in `java/`; `build.sh`
  prints no note, and `lint.sh` finds no use of deprecated API at
  `--release 17` (eight today,
  [out/lint-release17.txt](55-fix-finalize/out/lint-release17.txt)).
* A `Db` that is dropped without `stop()` or `close()` has its storage
  closed once the collector finds it: its threads end and its files
  close; also when its eviction thread had started, and that thread ends
  too. Unit tests for both, through the core and the Pub API, each with a
  bounded wait (`System.gc()`, at most a few seconds).
* The probes, `run.sh`, also with `--finalization=disabled`: in the three
  cases the `Db` is collected, its threads end and its file is closed;
  the unit and f-tests leave no storage or eviction thread after
  collection.
* `stop()`, `close()` and a start that throws close once, as before (the
  tests of 005-32 and 005-35).
* `java/before-commit.sh` prints `BEFORE COMMIT OK`; `level4.sh` passes,
  as a change to Level 4's mechanism (the eviction thread).


First step
----------

Look for anything else that holds a `Db` from a thread or a static field
(`Jmx.DbMonitor`, which some tests register with the platform MBean
server; the Pub API's index jobs, while they run; `Db.testHooks`), and
write the unit test of the eviction case first: it fails today, with
finalization on.


Size and order
--------------

S: about 40 lines in `Db` and `Eviction`, 30 in the test code and the two
`newInstance` calls, and the tests. With or after 005-51 (question 3);
independent of the rest.
