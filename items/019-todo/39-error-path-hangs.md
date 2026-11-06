019-39. Fix: hangs in the error path: a thread that cannot start, and a second Error while a thread records its failure
=======================================================================================================================

Status: open. Kind: Fix. Frans: none.
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


Log
---

2026-11-06. Registered by coord-1106 from review R6.
