019-36. Fix: Reclaim's cut waits for the storage thread's append, holding the write lock
=========================================================================================

Status: open. Kind: Fix. Frans: none.
Created 2026-11-06 by Frans Lundberg.

What: since 015-80's fix (night 006-12), every call that `BufferedStream`
makes to the stream below, but a read, holds its fair lock `ioLock`. Reclaim's
cut (`Reclaim.cutIfDurable`, in `transactionCompleted`, under the
database's write lock) goes through `BufferedStream.pretruncate`, so when
the storage thread is appending, the cut waits for that append and its
force. The other writers wait with it; readers do not. An append is up to
half the buffer, 5 MB by default. On F53 an append of 2.5 MB with its
force took 17 ms on average and 144 ms at the longest (005-46); on s1 a
force can take seconds. Under steady writes the thread appends most of
the time, so most reclaim cuts may wait. Nobody has measured how often a
cut waits, or how long.

Why: 010-P1, a worst case of about 20 ms for a commit. Review R4 of night
006-12 (`/Users/f/fl/bench/006-12/review-r4.md`, C1) found the wait; it is
not the device's limit that P1 allows (a writer that fills the buffer):
this writer fills nothing, it waits for a lock. 015-80, section "The
cost". Frans, 2026-11-06, 09:47, on 006-12, section 8, point 2: "As
recommended." (a line under P1 in 010-01 now, which is there; this entry
to measure, then R4's fix if the waits are real).

Frans: none. KISS (010-P13): the simplest fix that removes the wait.

The fix, R4's: the cut tries the lock (`tryLock`; it does not wait for
fairness), and when the thread holds it, Reclaim keeps the cut and tries
again at its next commit. The writer still makes every cut itself, so
`BufferedStream`'s kept first position stays exact. A cut is never
urgent: putting it off keeps some bytes in the stream a little longer.
R4 adds a fall-back to the plain lock after some growth, so that a stream
whose thread never lets go is still cut; add it only if the measurement
shows such a stream (a cut put off for more than a few commits in a row).

Done when:

1. Measured, on F53 and on s1, with the default buffer and a steady write
   load with reclaim on: how many reclaim cuts wait for `ioLock`, and the
   longest and the mean wait (a counter and a timer around the cut's lock,
   in a probe or a test, not in `main`). The numbers go into this entry
   and into 010-01's P1 line.
2. If a wait is over 20 ms on either machine: the fix above, with a test
   that fails before it (a cut made while the thread holds the lock in an
   append that a test stream holds back: the commit returns at once, and
   the cut is made at a later commit), the stream's bytes unchanged
   (`StreamDigest`), level 3's script (`java/stress/level3.sh`, reclaim)
   and `BEFORE COMMIT OK`; 010-01's P1 line says it is fixed. If no wait
   is over 20 ms: 010-01's P1 line gets the numbers, and the entry closes
   without a change of the code.

First step: read 015-80 ("The cost", "Locks and their order") and R4's
C1, then the probe for step 1.


Log
---

2026-11-06. Registered by coord-1106 from 006-12, section 8, point 2, at
Frans's word (09:47).
