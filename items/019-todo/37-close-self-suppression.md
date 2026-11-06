019-37. Fix: a failed flush and the close's same IOException: "Self-suppression not permitted"
=============================================================================================

Status: open. Kind: Fix. Frans: none.
Created 2026-11-06 by Frans Lundberg.

What: `BufferedStream.closeStream` keeps a failed close of the stream
below with a failed flush's failure, `failure.addSuppressed(failed)`
(015-81, night 006-12). When the stream's close throws the very
`IOException` that the flush failed with (a stream that keeps its
failure and throws it again), `failed` and `failure` are the same object,
and `addSuppressed` throws `IllegalArgumentException("Self-suppression
not permitted")`; the storage thread ends with it. The close's failure is
kept (`closeFailure`) before that.

Why: found by agent i10 of 006-13 while it implemented 019-10's error
model; older than that change (also on 33a8713, before it). Shown by
harness 6.2 (018-03), IO layer, `IO_EXCEPTION` at call 79. Since 019-10's
change the storage thread's top catch fails the database with what
escapes, so an unexpected exception there is not harmless noise.

Frans: none.

Done when: a test (a stream whose close throws the failed flush's own
`IOException`) fails before the fix and passes after, with `close()`
throwing the flush's failure and the storage thread ending without
another exception; `before-commit.sh`. The likely fix: `if (failure !=
null && failure != failed)` before `addSuppressed`.

First step: the test, in `BufferedStream`'s tester or `DbTesterFailure`.


Log
---

2026-11-06. Registered by coord-1106 from agent i10's report (019-10).
