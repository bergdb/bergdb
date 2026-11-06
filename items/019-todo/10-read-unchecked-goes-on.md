019-10. Fix: an unchecked exception or Error from a read of the storage leaves the database going on
================================================================================================

Status: done 2026-11-06. Kind: Fix. Frans: decision (2026-11-06, 10:18 and
10:31: the error model; section "The error model, done").
Created 2026-11-06 by Frans Lundberg.

What: when the stream under the storage throws an unchecked exception or
an `Error` from `read()`, the read's call (a get, or a transaction's
warm-up before its go point) throws it as it is, and the database goes
on: the next transaction or get returns. An `IOException` from the same
read fails the database (`DbFailedException`, 005-30). The read paths in
`Db` (`getOneInternal`, `getMany`, `checkDirtyNodes`'s `dirtyNodeBound`,
the warm-up) catch only `StreamException`, which `RecoverableStream`
and `StorageManager` make of an `IOException`; anything else passes
through them.

Why: docs/levels.md, section 3: "a database whose environment has failed,
or that has a bug, does not run on", and "a read that fails on the
storage fails the database in the same way" (005-30); 010-01, P7. An
unchecked exception from a stream breaks `AppendOnlyStream`'s contract (a
bug of the stream, `StrictStream`'s kind UNCHECKED), and an `Error` (an
`OutOfMemoryError` in a read) is a failed environment; after either, the
stream's state is unknown. Nothing was found wrong in the data after
such a run (the harness's restart check passed), but the database ran on
past a failure it had met. Found by harness 6.2 (018-03), check "met":
on `main` (4d7a1bb), STREAM UNCHECKED and ERROR at a READ of the
workload's thread, 43 of 1,548 runs (every 13th N), new and reopened, for
example:

    STREAM UNCHECKED at 29: get 1 threw InjectedException: injected unchecked
    exception at STREAM call 29, READ, in thread StorageFaultTester-runner,
    and the database went on: execute 3 returned

Not in the IO layer: `FileStream` reads through an open channel, not
through `FileStreamIo`. Older than the night: in 2026.2 and 2026.1 by
reading (the catch of `StreamException` only is from 005-30).

Frans: none at first (the night's fix followed docs/levels.md, section 3);
then R5's F1 and F2, and e1's study, for Frans. Decided 2026-11-06, 10:18
and 10:31: an `Error` in any call, or on BergDB's own threads, fails the
database and is thrown as it is; the application ends its process (the
section "The error model, done", below).

Done when: a regression test (a stream whose read throws an unchecked
exception, and one whose read throws an `Error`: a get and a
transaction's warm-up fail the database, every later call throws
`DbFailedException`) fails before the fix and passes after; harness
6.2's skip list (`StorageFaultTester.SKIP`) no longer has 019-10, and its
night tests pass; `BEFORE COMMIT OK`.

First step: the test, in `DbTesterFailure` (its `FaultStream` gets a
flag for an unchecked read). The likely fix: `StorageManager.read()`
turns an unchecked exception of the stream below into a
`StreamIoException` (the storage failed), and the read sites of `Db` that
catch `StreamException` also fail the database on an `Error`, then
throw it as it is.


Fix
---

`StorageManager.read()` catches an unchecked exception or an `Error` of
the main stream's read as it catches an `IOException`: the storage fails
(`handleStreamException`, its error set and the stream closed), and it
throws an `IOException` with the exception as the cause. `RecoverableStream`
makes it a `StreamIoException`, and `Db`'s read sites fail the database
as for an I/O error (`readFailed()`, `DbFailedException`). The `Error` is
not thrown as it is: the cause chain keeps it. A read below the first
position stays as it was (`ReadBelowFirstPosException`, an `IOException`).

Test: `DbTesterFailure.testUncheckedReadFailsTheDatabase`, an unchecked
exception and an `Error` from `FaultStream`'s read, in a get and in a
transaction's warm-up: the call throws `DbFailedException` with a
`StreamIoException` as the cause, every later call is refused with it,
nothing is appended, and a restart has the key. Before the fix: "an
unchecked exception in a get fails the database:
java.lang.IllegalStateException: FaultStream: an unchecked read error, as
set". Harness 6.2: the line `"019-10",` left `StorageFaultTester.SKIP`,
and its sweeps (the IO layer at every N, the STREAM layer at every 13th)
find nothing but 015-80's OVERLAP. docs/levels.md, section 3, and
`releases/next.md` (Reliability) say so.


For Frans (R5 F1, F2)
---------------------

Review R5 of the night 006-12 (`/Users/f/fl/bench/006-12/review-r5.md`,
F1 and F2): since this fix, an `Error` of the stream's read reaches the
caller wrapped (`DbFailedException` → `StreamIoException` → `IOException`
→ the `Error`), in a get, a warm-up, a transaction's own reads (`fail()`
gets the `StreamIoException`) and a start, where docs/levels.md, section
3, says that an `Error` is thrown as it is (005-32, `Db.fail()`). And an
`OutOfMemoryError` fails the database only when it is thrown below
`StorageManager` (in `SalsaStream`'s or `FileChannel`'s buffer), not one
frame up (`NodeStream`'s `new byte[size]`, the parse), which still passes
through and leaves the database going on. The behaviour is left as it is
until Frans decides; levels.md's sentence on Errors is unchanged.

* (a) Keep the wrap and document it: levels.md's transaction bullet and
  `Db.fail()`'s Javadoc say that an `Error` of the stream's read is the
  cause of the `DbFailedException`, not thrown as it is. No code change.
  An `OutOfMemoryError` above the stream stays as it is today.
* (b) Rethrow the `Error` as it is after failing the storage:
  `StorageManager.read()` fails the storage (its error and the stream's
  close, before it builds any message) and rethrows the `Error`; `Db`'s
  read sites (`getOneInternal`, `getMany`, `dirtyNodeBound`, `getTrans`)
  catch an `Error` too, fail the database, and rethrow it, as a
  transaction does after its go point. One rule for every `Error` of a
  read, wherever it is thrown (R5's F2), and levels.md stays true.

Recommendation: (b). It keeps the one rule that the rest of the Core
follows (an `Error` is thrown as it is, and the database fails), and it
closes F2's gap: an `OutOfMemoryError` in `NodeStream` or the parse
fails the database too. It is a few lines at four read sites and in
`StorageManager.read()`, with `testUncheckedReadFailsTheDatabase`
extended (the `Error` case expects the `Error` itself, then refusals).


Can the database go on after an Error in a read? (2026-11-06)
-------------------------------------------------------------

By agent e1 of coord-1106, for Frans's direction of 2026-11-06, 09:38: "If
we can really ensure the database as a whole is still in a good state
after an OOM in a get, we should allow the database to go on. At least if
this does not become too complex to implement and understand. KISS is an
important principle. Important that the database user understands the
error model. That is part of the interface." Read on main at 1cce631 (its
Java as at 8df56fc), and one probe in a scratch clone; nothing else
changed.

In short: for an `OutOfMemoryError`, Frans's case, it can be ensured, with
two fixes of a few lines (`Eviction.wake`, and the order of
`StorageManager.handleStreamException`; below). For every `Error`
anywhere it cannot: a `StackOverflowError` can come between two steps that
allocate nothing, and the JVM's own errors change the JVM. What holds for
every `Error` is the data: a read changes no data, so an `Error` in it
cannot make a later read wrong or lose a commit.

**The read paths.** Every read of the storage on a caller's thread loads
through `NodeCollection.followPointer` (index nodes and values), except
`getTrans`, which reads its record into a `TransIterator` of its own. No
read registers with reclaim: a read admitted before a cut expires instead
(011-04, W1, D1 = A; `Reclaim.java:489`), so there is no reader count that
a failed read could leave behind.

| Path                               | Thread, lock                | Besides the follow       |
|------------------------------------|-----------------------------|--------------------------|
| `getOne` (`Db.java:1646`)          | caller's, none              | a counter, after it      |
| `getMany` (`Db.java:1701`)         | caller's, none              | the caller's `GetMany`   |
| `getTrans` (`Db.java:1575`)        | caller's, none              | none: all local          |
| warm-up (`Db.java:2423`)           | caller's, before write lock | none                     |
| `checkDirtyNodes` (`Db.java:2254`) | caller's, write lock        | none: its maps are local |
| `sync()` (`Db.java:1820`)          | reads nothing               | -                        |

**The follow** (`followStreamPointer`, `NodeCollection.java:389`, and
`followValuePointer`, `:581`), step by step; each changes state that later
follows use:

1. `raiseRef` (`:429`), before the read: Rule R's newer reference, or a
   dead handle's written position, into the predecessor's pointer, under
   its monitor, never lowered. It is the value every later follow writes
   there, so harmless when the read then fails.
2. `liveOrNewHandle` (`:435`; `Cache3.java:140`), before the read: an
   empty live handle in the node table if the node had none (`new
   Handle`, a `HashMap` put under the map's lock). Left after a failed
   read, it is a state the table has anyway: the next follow loads into
   it, and a CLOCK step drops it (`Cache3.java:419`). An OOM inside the
   put leaves the `HashMap` consistent (a resize raises its threshold,
   then allocates), but for a tree bin's split, which Cache3's hashing
   keeps away (005-08).
3. The handle's LOADING state (`:463`), set back to LIVE in a `finally`
   (`:482`), under the handle's monitor. An `Error` in the read or the
   install leaves it LIVE. Only an `Error` of that `finally` itself, a
   `StackOverflowError` at the call of `casState` (which allocates
   nothing, so never an OOM), leaves it LOADING: then every later load of
   the node spins at `:463-465`, which takes a failed compare-and-set for
   "evicted meanwhile", the writer's load too, and eviction skips it.
4. The read (`readVersion`, `:548`; `NodeStream.readNode`,
   `NodeStream.java:179`): its buffers (`new byte[1024]`, `new
   byte[size]` at `:193`), the checksum and the parse are local; then two
   atomic counters (`tickAccessClock`, `loads`). Nothing shared.
5. `install` (`:476`; `Cache3.java:264`), under the handle's monitor: the
   new object's handle, its count (`Residents.added`,
   `Residents.java:141`), the handle's object, the old object's release.
   No allocation; a `StackOverflowError` between the steps leaves one
   object's count off (accounting, not data).
6. `dropIfEmpty` (`:495`), and the swizzle (`:510-521`, under the
   predecessor's monitor: one release store, then `handleIn`'s 32 bytes,
   `Residents.java:194`); for a value, `setPointee` and `valueIn`
   (`:597-603`, `Residents.java:205`). No allocation; as 5.
7. The CLOCK bit (`touch`); a reader's pointer listener does nothing.
8. After a load, the load listener (`:227`): `Eviction.afterLoad`
   (`Eviction.java:442`), which may `wake` the eviction thread
   (`Eviction.java:508-519`). `wake` sets `wanted` before it makes and
   starts the thread. An `OutOfMemoryError` there (the heap at `new
   Thread`, or "unable to create native thread" at `start()`) leaves
   `wanted` set, and after `start()` also `evictor`, a thread that never
   runs. Every later `wake` returns at its first line, so the eviction
   thread never runs again: the writer's batch at each transaction's end
   goes on (`afterTransaction`, `Eviction.java:330-339`), but a read-only
   workload has no eviction, and a reader under pressure parks 2 ms at
   every load (`Eviction.java:450`). It can happen only when the thread
   is made: the first wake, or one after an interrupt ended the thread.
   This is the one half-done state an OOM of a read can leave; it is in
   main today, where the `Error` passes through the get and the database
   goes on.

**Below `StorageManager`.** `RecoverableStream.read`
(`RecoverableStream.java:450`) keeps no state. `BufferedStream.read`
(`BufferedStream.java:455`) writes no field. `FileStream.read`
(`FileStream.java:293`, `DbFile.read` at `:1342`) takes no lock, sets the
interrupt flag again in a `finally` (`:1401`), and reopens a channel that
an interrupt closed, which heals itself. `SalsaStream.read`
(`SalsaStream.java:95`) allocates first, and sets the block counter and
position before it decrypts (`Salsa.java:196`). `CutStream`,
`ReadOnlyStream` and `OneFileStream` (a seek before each read) keep none.
`FileChannel`'s temporary direct buffer is taken before the I/O. So an
`Error` of the stream's read leaves BergDB's streams as they were, as the
coordinator found. A stream of the application's (`DbBuilder.mainStream`)
is bound by `AppendOnlyStream`'s contract only, which says nothing of it.
One step of `StorageManager` itself: `handleStreamException`
(`StorageManager.java:324-329`) sets `mainFailing`, then builds a message
before it sets the error and `mainFailure`; an OOM in that message, after
an I/O error, loses the storage's failure for good (every later call of
it returns at its first line), with the stream open. Today and under (c)
alike; R5's F2 found the same in 019-10's new catch.

**An `Error` before a transaction's go point, today.** All that comes
before the go point (`Db.java:2066`) is outside the `try`: an `Error` in
`checkSize`, the warm-up, `checkDirtyNodes`, `x.begin` (`Db.java:2778`;
what it sets, the next begin sets again, as after a `RerunException`),
`stmCheckConflicts` or the clock leaves `execute` as it is, the
transaction is not run, and the database goes on. The write lock is a
monitor, which the JVM releases. Since b45b2fa, one exception: an `Error`
of the stream's read, in the warm-up or `dirtyNodeBound`, fails the
database, wrapped. After the go point, `fail()` (`Db.java:2151`) fails
the database and throws an `Error` as it is, but, since b45b2fa, not one
of the stream's read, which it gets wrapped (R5's F1).

**What else an `Error` of a read can leave.**

* Index jobs (Pub API): the job's thread (`IndexBuilderImp.java:313-345`)
  catches `StreamIoException`, `DbStoppingException` and
  `DbFailedException` only. Any other `Throwable` of its reads (today an
  `Error` above the stream; under (c) every `Error`) ends the thread with
  the database going on: the index creation stops until a restart, its
  `join()` reports it working, and a restart's job whose thread has died
  reports it done (`IndexManager.java:197-199`). BergDB's other threads
  fail the database on an `Error` (the eviction thread, 015-25; the
  storage thread, 015-35), as there is no caller to tell.
* A corrupt node size (`NodeStream.java:183-193`): `checkReadSize` bounds
  it by the stream's length, not by the heap, so a corrupt size can give
  an `OutOfMemoryError` at `new byte[size]` before the checksum is seen.
  Under (c) each read of that node then throws it, and the database
  serves around the node (005-30: worse than one that stops) until the
  heap allows the read, whose checksum then fails the database. Rare: the
  4-byte size of one node, corrupted to more than the free heap.
* The JVM: an OOM in a class's static initializer leaves the class
  unusable for good (`NoClassDefFoundError`), and metaspace, native
  threads and `InternalError` are the JVM's state. No Java code can check
  them.
* The caller's own objects: after a get that threw, a connection's
  `transactionInfo()` gives the transaction of the get before
  (`GetData.tpos` is set only when a value is found), and a `GetMany`
  holds a partial result. Connection-local, as after any exception of a
  get.

**Probe.** `E1Probe` in the clone `/Users/f/fl/bench/006-13/e1` (not for
commit), with `StorageManager.read` changed to throw an `Error` as it is,
the storage not failed (option c). A `MemoryStream` under a stream that
throws, 2,000 keys, node size 8, eviction EVERY 1, the audit every 20
transactions, the record limit 300 kB (so that a transaction of 50 puts
walks `dirtyNodeBound`, by the arithmetic of its cheap test; not
instrumented). A workload of gets, a get and its
`getTrans`, scans (`DbUtil.checksum`), and transactions of 5 and 50 puts.
An `OutOfMemoryError` thrown once, at the n-th call of one site: the
stream's read; the first-touch hook (after an install and before the
swizzle; for a value, before `setPointee`); the load listener (after a
load, before `afterLoad`). n from 1 to 1,200, every 5th. Then: the
database active, `Audit.check` and `Residents.misCounted` clean, no
handle LOADING, every key right, a commit taken, and a restart with every
key and the same checksum. 720 runs, 63 s:

| Site          | Runs | Thrown as itself | Went on | Failed (after the go point) | Findings |
|---------------|------|------------------|---------|-----------------------------|----------|
| stream read   | 240 | 240 | 233 | 7 | 0 |
| first touch   | 240 | 240 | 240 | 0 | 0 |
| load listener | 240 | 240 | 240 | 0 | 0 |

The stream's `Error` went on in 37 gets, 6 gets with their `getTrans`, 10
scans, 21 transactions of 5 puts and 159 of 50 (the warm-up or
`dirtyNodeBound`); the hooks' mostly in scans (157 each) and transactions
of 50 puts (59).
The probe cannot reach `wake`'s thread start, `handleStreamException`'s
message or a `StackOverflowError` in a `finally`; those are by reading.

**Verdict.**

* "An `OutOfMemoryError` in a read leaves the database as it was" can be
  ensured, after the fix of `Eviction.wake` (and of
  `handleStreamException`'s order, for an OOM that comes with an I/O
  error). On every path above, the allocations are local (buffers, the
  parse, the walk's maps, a scan's results) or come before the shared
  changes (step 2's handle, harmless when left), and the shared changes
  after the read allocate nothing. The argument can be checked: the
  follow is one method of 140 lines, and the probe tests its sites.
* For every `Error` anywhere it cannot: a `StackOverflowError` at the
  `finally` of step 3 hangs one node's loads, the writer's too, and one
  between the steps of 5 or 6 leaves a count off; the JVM's own errors
  are outside BergDB. They keep the data: a read changes no data (not the
  stream, a canonical object, D, the clock or the transaction sequence),
  only what memory holds of the stream (versions, handles, memory
  pointers, values in pointers), references that Rule R raises, CLOCK
  bits and counts. So no later read is wrong, and no commit is lost.
* An unchecked non-`Error` exception of the stream's read is a bug of the
  stream (a breach of `AppendOnlyStream`'s contract, `StrictStream`'s
  UNCHECKED): 019-10's fix, which fails the storage and the database,
  stays. That is the simplest rule: anything the stream throws but an
  `Error` fails the database.

**Draft error model**, for docs/levels.md, section 3 (one bullet in place
of the read bullet and of the transaction bullet's parenthesis), and
`Db`'s class Javadoc, with `@throws Error` on `getOne`, `getMany`,
`getTrans` and `execute`:

> A failure of the storage (an I/O error, corrupt data, or an exception of
> the stream) fails the database, in a read as in a transaction: the call
> throws a `DbFailedException`, and so does every later call until the
> database is restarted (005-30). An `Error`, such as an
> `OutOfMemoryError`, is always thrown as it is. After a transaction's go
> point it fails the database too, as nothing there is undone. Anywhere
> else, in a get, a scan, `transactionInfo()` or a transaction before its
> go point, it fails only that call, and the database goes on: a read
> changes no data, only what memory holds of the stream. An `Error` on one
> of BergDB's own threads (the storage thread, eviction, an index job)
> fails the database, as there is no call to throw it to.

The one rule for the user: the go point decides; an `Error` fails the
database only after it, or where no caller can be told. And for
`AppendOnlyStream.read`: "An `Error` thrown by read() leaves the stream as
it was; BergDB goes on after it."

**The change for (c), and its size.**

1. `StorageManager.read` (`StorageManager.java:308`): an `Error` is thrown
   as it is, the storage not failed; an unchecked exception as now. About
   4 lines, and its Javadoc, `hasFailed()`'s and `getFailure()`'s. It
   also closes R5's F1 (a transaction's `fail()` gets the `Error` itself,
   and so does a start) and F2 (an `Error` above and below `StorageManager`
   take the same way).
2. `Eviction.wake` (`Eviction.java:508-519`): make and start the thread,
   then set `evictor` and `wanted`, so that an `Error` changes nothing and
   the next load tries again. The new thread first takes `evictorLock`,
   which `wake` holds, so it finds `wanted` set. About 4 lines.
3. `StorageManager.handleStreamException` (`:324-329`): `mainFailure` and
   a fixed error before any message is built. About 2 lines.
4. Index jobs (`IndexBuilderImp.java:322-336`): any other `Throwable`
   fails the database, as the eviction thread's does (015-25;
   `Db.Internal.failByEviction` is that call, at most renamed). About 5
   lines.
5. Words: docs/levels.md section 3 (above), `Db`'s Javadoc,
   `AppendOnlyStream.read`'s sentence, releases/next.md (019-10's line).
6. Tests: `DbTesterFailure.testUncheckedReadFailsTheDatabase` keeps its
   unchecked cases; its `Error` cases expect the `Error` itself, the
   database active, then the get right, a commit and a restart; with
   `getMany`, `getTrans`, a transaction of 50 puts (`dirtyNodeBound`,
   the record limit lowered) and a put's load after the go point (the
   `Error` itself, the database failed), which R5 found missing. A test of
   the probe's shape with a sample of n, about 2 s (the first-touch hook
   and the load listener throw). A test of `wake` with a test hook that
   throws at the thread's start. Harness 6.2 (018-01, section 6.2): its
   "met" check takes an ERROR at a READ before a go point as going on by
   the rule, and after one as a failure; its night set run.

Production code about 15 lines, words about 30, tests about 150: one
agent, half a day with BEFORE COMMIT OK and harness 6.2's night set. No
change to the stream's bytes or to Lean.

Not proposed (KISS): a self-heal of a handle left LOADING (a thread that
holds the handle's monitor and finds LOADING knows that its loader died;
one line at `NodeCollection.java:463`). It would close step 3's hang, but
only for a `StackOverflowError` at one call, and no test reaches it.

**(b) for comparison.** Fail the database on every `Error` of a read and
throw it as it is: the same line in `StorageManager.read` (fail, then
rethrow), and a catch of `Error` in `getOneInternal`, `getMany`,
`getTrans` and `dirtyNodeBound`, about 16 lines. It needs no argument
about the follow, but: `getMany` runs the caller's `StopCondition`
(`Dag.java:578`; Core API), whose own `Error` would then fail the database
unless told apart; the model gets two rules before the go point (an
`Error` in a read fails the database, any other refuses the transaction);
and an OOM of one get, for one large value, say, stops every connection
until a restart, which at 10M keys takes tens of seconds (005-57).
`wake`, `handleStreamException` and the index jobs want their fixes
either way.

**Recommendation: (c)**, with changes 1 to 6. It is what Frans asked
for; it can be ensured for an `OutOfMemoryError` by a short argument that
can be checked, and by the probe; its model is one rule that the user
already has, the go point; and it takes the wrap of 019-10's fix away
rather than adding catches. What it does not promise, the state after a
`StackOverflowError` at one exact call or after the JVM's own errors, no
Java library can; the data is safe in both.

**Left.** An unchecked exception above the stream in `getOne`, `getMany`
or `dirtyNodeBound` (a bug in the parse or the Dag) passes through with
the database going on; `getTrans` wraps its parse's (005-82,
`Db.java:1634`). Wrapping the node parse's in `NodeStream.bytesToNode` in
the same way would make every read fail the database on a malformed node:
a separate entry, if Frans wants it. A connection's `transactionInfo()`
after a get that threw (above): a Pub API detail.


The error model, done (2026-11-06)
----------------------------------

Frans, 10:18, on e1's study: "The complexity cost is too high. Mainly in
future maintenance. I never before tried to handle OOM or StackOverflow
in Java. In general, this is considered a bad idea. So, keep the error
model even simpler. I think this is the original error model. If the
environment is faulty (storage, memory, stack), then the database cannot
be garanteed to work. Flag this, throw exception is called. The user
application should close the process." 10:31, on coord-1106's draft of the
model and the proposal: "Good. Document this and implement it. Ensure the
Javadoc is clear about this." 10:42 (019-30, 019-31, 019-33): "BergDB
assumes correct storage. Which makes sense. Ensure this is documented in
the relevant Javadoc comments." Done by agent i10 of coord-1106 (clone
`/Users/f/fl/bench/006-13/i10`, branch `i10`).

**The model**, in docs/levels.md, section 3 ("Errors"), `Db`'s class
Javadoc, `Database`'s (the Pub API), `DbFailedException`'s, a pointer in
`Connection`'s and `DbException`'s, and `AppendOnlyStream`'s (correct
storage assumed; what an unexpected exception of `read()` does). The
approved words with three changes for accuracy: "during a call to the
database" became "during a read, a transaction or a sync, also in the
application's code that it runs" (getters, `newGetData()` and the like do
not fail the database, nor does the Pub API's conversion of a read value
to the application's object, below); "Every later call" became "Every
later read and transaction", and "`stop()` and `close()` still work, and so
does `sync()` while the storage does" (a sync after a failure works for
the transactions before it, as before); and correct storage with the
checksums as a best effort (Frans, 10:42).

**The code.**

* The edge catch: `Db.failed(Error)` (`Db.java:2271`): `setFailed()`
  first, which allocates nothing, then returns the `Error` for the call to
  throw. At `getOne` (`:1591`), `getTrans` (`:1621`), `getMany` (`:1767`,
  also its `StopCondition`), `sync` (`:1914`, at the storage's sync, the
  call's one step that waits or reads), `execute` (`:2030`, before the go
  point too; after it `fail()` was first) and `setCacheSizeIndicator`
  (`:443`: it may start the eviction thread, and an `OutOfMemoryError` in
  `Eviction.wake` left the thread wanted and never started, e1's first
  ordering fault). `start()` already caught everything (`:642`): the
  database is stopped and its storage closed (005-32). Not `stop()` and
  `close()`: they set the state to STOPPING first, so no later call does
  work, and their `Error` is thrown as it is. Not the getters and the
  setters that commit through `execute()` (`setStartupDistance`,
  `setRetainDuration`, `setReclaimInternalFraction`), whose own steps
  before it change nothing.
* The Pub API: a transaction (`RwTransaction.executeRw`,
  `RwTransaction.java:113`, through `ConnectionImp.failed`, `:226`): the
  application's `Action` runs there before the Core's `execute()`. Not the
  conversion of a read value to the application's object
  (`KvToObjectImp.createObject`): `BlankConstructorFactory` turns any
  exception of the application's constructor into a `Bug`, an `Error`, so
  a catch there would fail the database on an application's
  `RuntimeException`. An `Error` of the Core reaches a Pub caller as it
  is: no Pub class catches one but the start's, which closes and rethrows
  (`DatabaseBuilderImp`, `DatabaseImp`'s constructor); tested.
* `StorageManager.read`: an `Error` passes through as it is, and the
  storage goes on (the edge fails the database); an unchecked exception
  stays a storage failure (`:314`). R5's F1 and F2 close by the one rule.
* `StorageManager.handleStreamException` (`:340`): the failure first, then
  a fixed error text, before anything is allocated; e1's second ordering
  fault: an `OutOfMemoryError` in the message, on the storage thread, lost
  the storage's failure for good, and the database went on, with syncs
  waiting for ever. The detail is now the cause of what `read()`,
  `append()` and `sync()` throw after it.
* BergDB's threads, each listed:
  * the storage thread (`BufferedStream.runConsumer`, `:173`): anything
    that ends it outside a flush fails the stream as a failed flush does
    (new; before, the thread ended with nothing failed);
  * eviction (`Eviction.EvictorRun`, `:644`, `:669`): already did (015-25);
    `failByEviction` renamed `Db.Internal.fail` (`Db.java:2787`);
  * the cut's file deletion (`FileStream.runCuts`, `:595`): already did
    (the stream's failure);
  * an index build (`IndexBuilderImp`, `:342`): new, anything else fails
    the database; the restart's build job (`IndexManager`, `:203`) reports
    the build's status, not "done" when its thread has ended;
  * an index deletion (`DatabaseImp.deleteIndexInternal`, `:316`): new;
  * `Db-close-` (stop()'s close): left, the database is stopping;
  * `DBMonitor.MThread` (`Jmx`, tests only): left, it reads counters.
* Not done (Frans's model, coord-1106's proposal, point 4): a guarantee of
  the cache's state after an `Error`, probe tests, the LOADING spin after a
  `StackOverflowError`.

**Tests**, each failing on 33a8713 with only the test files changed, and
passing after:

* `DbTesterFailure.testUncheckedReadFailsTheDatabase`: an unchecked
  exception and an `Error` of the stream's read in a get, a scan, `getTrans`
  and a warm-up; the `Error` is thrown as it is (the same instance), then
  every later transaction and read is refused with it as the cause.
  Before: "an Error in a get is thrown as it is: DbFailedException".
* `DbTesterFailure.testErrorInStopConditionFailsTheDatabase`. Before:
  "refused, 0".
* `PubTester.testErrorFailsTheDatabase`: an `Error` of an `Action`, and
  one of a read of the storage reaching a Pub `get` as it is. Before:
  "refused, 0: null".
* `PubTesterIndexJobs.testErrorInBuildFailsTheDatabase`: an `Error` in a
  build's `Action` and after its step's transaction. Before: "action, the
  database failed: null".
* `DbTesterFailure.testErrorInFlushFailsSync`: the flush's failure is now
  looked for in the cause chain.
* Harness 6.2 (018-03): the fault's `Error` thrown as it is counts as a
  failure (P7: every later transaction and read refused); `close()`'s
  check after a reported failure counts it too.

**Left.** The Pub API's own steps around a Core call (key parsing, the
conversion of a value to the application's object, `transactionInfo()`'s
list) do not fail the database on an `Error`; the application ends its
process anyway. The storage thread and the cut's thread allocate one
`IOException` before they record their failure. Found while gating, older
than this change (on 33a8713 too): `BufferedStream.closeStream` calls
`failure.addSuppressed(failed)` when the stream's close throws the flush's
own `IOException` (harness 6.2, IO `IO_EXCEPTION` at 79), and the storage
thread ends with "IllegalArgumentException: Self-suppression not
permitted"; the close's failure is kept before it. For a new entry.


Log
---

2026-11-06. Registered by harness 6.2's agent of the night 006-12: found
by the harness (018-03, section 5); in its skip list until fixed.

2026-11-06. Fixed in the night 006-12 by the same agent (the simplest fix
by the entry's First step; no decision needed, docs/levels.md's rule).

2026-11-06, 03:10. R5's F1 and F2 written up for Frans's decision (above);
its F3 (words: docs/levels.md's reflow, `StorageManager.hasFailed()` and
`getFailure()`) fixed with 018-03's follow-up.

2026-11-06, 09:57. Agent e1 of coord-1106: the section "Can the database
go on after an Error in a read?" (the read paths traced, and a probe in a
scratch clone, 720 runs, no finding): an `OutOfMemoryError` in a read can
be ensured to leave the database as it was after two small fixes
(`Eviction.wake`, the order of `StorageManager.handleStreamException`),
not every `Error`; recommended (c), with a draft error model. For Frans.

2026-11-06, 10:18 and 10:31. Frans: "The complexity cost is too high.
[...] So, keep the error model even simpler. [...] If the environment is
faulty (storage, memory, stack), then the database cannot be garanteed to
work. Flag this, throw exception is called. The user application should
close the process."; then, on the drafted model: "Good. Document this and
implement it. Ensure the Javadoc is clear about this." Status in
progress, agent i10 of coord-1106.

2026-11-06. Done by agent i10 (section "The error model, done"): an
`Error` in a read, a transaction, a sync or on BergDB's own threads fails
the database and is thrown as it is; the model in docs/levels.md, section
3, and the Javadoc; four new or changed tests that fail before; harness
6.2's "met" check follows the rule. BEFORE COMMIT OK.
