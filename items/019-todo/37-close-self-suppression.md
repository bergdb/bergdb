019-37. Fix: a failed flush and the close's same IOException: "Self-suppression not permitted"
=============================================================================================

Status: done 2026-11-06. Kind: Fix. Frans: none.
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
model; older than that change (also on de1b026, before it). Shown by
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

2026-11-06. Taken and done by coord-1106's agent f32 (clone f32, branch
f32). `BufferedStream.closeStream` keeps the close's failure as
suppressed on the flush's only when it is another object (`failure !=
failed`). A real stream reaches it: `FileStream.close()` throws its kept
`ioException`, which can be the very `IOException` an append threw. Test
`BufferedStream.testCloseThrowsFlushFailureAgain`: a stream whose append
throws an `IOException` and whose close throws the same one, (i = 0)
with the default listener and (i = 1) with a listener that closes the
stream from the thread, as `StorageManager.handleStreamException` does.
Before the fix: (0) "nothing escapes the thread, 0:
java.lang.IllegalArgumentException: Self-suppression not permitted",
(1) "the listener's close throws the flush's failure:
java.lang.IllegalArgumentException: Self-suppression not permitted".
After: `close()` throws the flush's failure, with nothing suppressed,
and the thread ends without an exception. The stream's bytes are
unchanged. A line in `releases/next.md`, Reliability. BEFORE COMMIT OK.
