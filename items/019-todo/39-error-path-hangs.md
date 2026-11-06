019-39. Fix: hangs in the error path: a thread that cannot start, and a second Error while a thread records its failure
=======================================================================================================================

Status: done. Kind: Fix. Frans: none.
Created 2026-11-06 by Frans Lundberg.

What: two ways in which an `OutOfMemoryError`, the case of the error model
(docs/levels.md, section 3, "Errors"), ends in a hang instead of a failed
database whose `stop()` and `close()` work:

* **B2, a thread that cannot start** (older than 019-10). `Db.stop()`
  (about lines 1371 to 1380) sets `closeBegun` and then makes and starts
  the closer thread; if that throws, a later `close()` waits in
  `waitUntilClosed()` for ever. `FileStream.pretruncate` (about lines 549
  to 556) assigns `cutThread` before `start()`; if the start throws,
  `awaitCutThread()`, which `close()` calls, never returns.
* **B3, a second Error while a thread records its failure.**
  `BufferedStream`'s storage thread (the catch at about line 179, and
  334 and 396; `flushFailure` at 433) and `FileStream.runCuts` (about
  596) allocate an `IOException` before they record anything. If that
  allocation fails too, the thread dies silently: syncs, a commit waiting
  for room in the buffer, and `close()` wait for ever.

Why: review R6 of 006-13 (`/Users/f/fl/bench/006-13/review-r6.md`, B2 and
B3; read, not run). The model promises "`stop()` and `close()` still
work", so that the application can end its process; a hang hides the
failure. 019-10's change fixed the same order in
`StorageManager.handleStreamException`, not on these paths.

Frans: none. The simplest fixes, KISS (010-P13): no recovery, only that
the failure is recorded before anything is allocated and that no waiter
waits for a thread that never ran.

Done when: `stop()` sets `closeBegun` back on a `Throwable` from the
closer's making or start (so that `close()` closes on its own thread), and
rethrows; `pretruncate` assigns `cutThread` after `start()` returned; the
storage thread and the cut's thread record their failure (a field set
first, no allocation before it) and wake their waiters (`cutThread = null;
notifyAll()` in a `finally`) before they build an exception; tests with a
hook that throws at a thread's start, and one that throws at the wrapping;
`BEFORE COMMIT OK`.

First step: R6's B2 and B3.

Limit: while the heap stays full, BergDB cannot promise even to fail
cleanly, as the JVM itself may need memory to record the failure; a
`sync()` or `close()` may then wait. `-XX:+ExitOnOutOfMemoryError` ends
the process at the first `OutOfMemoryError`, and that is the model's
advice (docs/levels.md, section 3, "Errors"). An example, after this
entry's fixes: R7's `R7OomProbe` with the sync made before any later
append (`-Xmx48m`, the heap kept full until the stream's close). The
storage thread records the failure and wakes its waiters, but
`StorageManager.handleStreamException`'s first
`AtomicBoolean.compareAndSet` in that JVM links its call site, which
allocates, and throws a second `OutOfMemoryError`: the storage does not
fail, and the sync waits (1 of 1 runs; with the call site linked first,
2 of 2 fail cleanly). Not chased further (coord-1106, from Frans's
"The complexity cost is too high", 2026-11-06, 10:18).


Log
---

2026-11-06. Registered by coord-1106 from review R6.

2026-11-06. Done by coord-1106's agent i39, as the "Done when" says,
with two changes, both simpler: `stop()` closes on its own thread
when its closer cannot be made or started (`closeStorage(false)`), and
then rethrows, instead of setting `closeBegun` back: a `close()` that
began waiting meanwhile is woken too. And the failure that the storage
thread and the cut's thread record is an `IOException` made with the
stream (`BufferedStream.flushFailure`, `FileStream.cutFailure`), given
the `Error` as its cause (`initCause` allocates nothing), so the
wrapping cannot throw; R6 and R7 both proposed it. The rest of each
thread's failure path is as before: `stopAfterFailure` sets the fields
and wakes the waiters, and tells the listener. `pretruncate` sets
`cutThread` after `start()`; `runCuts` clears it in a `finally` too.
A test hook, `Util.testHookStart`, runs before `Util.start(t)`, which
`Db.stop()` and `pretruncate` use. Tests, each failing with its fix
taken out: `DbTesterFailure.testStopWhoseCloserCannotStart` (close()
HUNG), `FileStream.testCutThreadThatCannotStart` (close() still waits),
`FileStream.testCutErrorRecordedAsMadeBefore` and
`BufferedStream.testFlushFailureMadeBefore` (a new IOException each
time). Review R7 of 006-13 confirmed B3 by runs (its B1, R7OomProbe and
R7CutOomProbe, `/Users/f/fl/bench/006-13/r7-runs/probe/`); with this
entry's fixes, 3 of 3 runs of each: the storage thread's failure is
recorded (a later append throws it, the sync throws, close() returns),
and the cut's close() returns with the cut's failure. The limit above,
also in docs/levels.md, section 3.
