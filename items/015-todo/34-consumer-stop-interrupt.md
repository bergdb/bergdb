015-34. Fix: a storage thread interrupted at its stop skips closing its stream
==============================================================================

Status: done 2026-11-05, night 006-12. Kind: Fix. Created 2026-11-03 by Frans Lundberg.

After release 2026.2 (a known issue of it); in 2026.1 too.

What: `BufferedStream`'s consumer, interrupted while it stops, returns before it closes the stream below: its files and the directory lock stay open. Reached through the Pub API only by the experimental `removeReplica` with an outside interrupt; `Db.stop`/`close` repair it.

Source: review R3, R3-F6 (items/016-release-2026-2/07-concurrency/r3.md),
confirmed by verify-2 (items/016-release-2026-2/06-reviews/verify-2.md,
section R3-F6), with its probe, the reach and the effect.

Done when: a test that fails on the code before the fix passes, and the
fix is in `main` after `before-commit.sh`.

First step: the probe of R3-F6, made a test.


Log
---

2026-11-03. Registered by the coordinator of release 2026.2 (016-02).

2026-11-04. Review R5 found the same, or its counterpart in StorageManager (R5-F2, items/016-release-2026-2/06-reviews/R5.md).

2026-11-05. Done in night 006-12, with 015-78. R5's form of the probe
(R5/R5-F2.diff: the test holds the buffer's monitor, interrupts the idle
consumer and calls `stop()`), made
`BufferedStream.testStopWhileInterruptedClosesStream`: before the fix "the
consumer closed the stream, expected 1, got 0".

* Fix: `BufferedStream.runConsumer` closes the stream in a `finally`
  around the consumer's loop (now `consume()`), so every way the thread
  ends closes it: the interrupt's `return` at a stop, the loop's end, and
  an unchecked exception.
* Reach today: `BufferedStream.stop()` and `StorageManager.stop()` only;
  `removeReplica`, the Pub API's way in, went with replication (005-11),
  and `Db.stop()` and `close()` close through `BufferedStream.close()`.
* 010-01: no setting, thread or format change; the stream's bytes are
  unchanged.
