019-41. Fix: review R7's C findings: a test that misses a hot loop, a sync not woken, an interrupted eviction thread spinning
==========================================================================================================================

Status: open. Kind: Fix. Frans: none.
Created 2026-11-06 by Frans Lundberg.

What: review R7 of 006-13 (`/Users/f/fl/bench/006-13/review-r7.md`), a
second look at the night 006-12's concurrency fixes (015-66, 67, 70, 82,
80: all OK, no A finding), found, beside its B1 (019-39) and C5 (019-40,
R6's C1):

* C1: 015-70's test does not pin two of its three parts. With the
  sweep's end of a decrease taken out (`Eviction`, about line 851) the
  test still passes, while the eviction thread runs 17.5 million empty
  batches in about a second, each taking the write lock (010-P1, P3); with
  `goal()` reverted it passes too (run).
* C2: `testWriterCutBesideThreadsCutAndClose` waits a fixed 400 ms and can
  pass without checking the overlap it is for.
* C3: 015-80's entry says the close holds the write lock; it does not.
* C6: a sync is not woken by a failure or a close (`StorageManager`,
  `d1Lock.wait(500)`, about line 234; the error is set at about 338 and
  137 with no notify): it sees the failure up to 500 ms late (P7, "at
  once"), and a sync during a close throws up to 500 ms later instead of
  returning. Older than the night.
* C7: the eviction thread spins while writers wait if it was interrupted
  (`Eviction`, about lines 631 to 633: `parkNanos` returns at once while
  the flag is set). Older than the night.

Why: C6 and C7 are faults (small; P7's "at once", 005-46's interrupts);
C1 leaves a regression to a hot loop unseen by `before-commit.sh`; C2 and
C3 are a test and words.

Frans: none. Each as R7 suggests, the simplest way (KISS, 010-P13).

Done when: C1, the test asserts that the thread goes idle after the
decrease and that the sweeps since are few, and fails with the clause at
851 taken out (for `goal()`, a fixture with a writer waiting, or a line
in 015-70 that it has no failing test); C2, the test checks the overlap
instead of a fixed wait; C3, 015-80's words; C6, `d1Lock.notifyAll()`
after the error is set (no allocation), with a test that a waiting sync
fails within, say, 50 ms of a failure; C7, `Thread.interrupted()` before
the park loop, with a test; `BEFORE COMMIT OK`, and `level4.sh` (the
eviction mechanism).

First step: R7's C1, C2, C3, C6, C7 and its probes
(`/Users/f/fl/bench/006-13/r7-runs/probe/`).


Log
---

2026-11-06. Registered by coord-1106 from review R7.
