019-10. Fix: an unchecked exception or Error from a read of the storage leaves the database going on
================================================================================================

Status: done 2026-11-06, night 006-12; R5's F1 and F2 wait for Frans (below). Kind:
Fix. Frans: decision.
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

Frans: none. The fix follows section 3's rule; an `Error` is thrown as it
is, as after the go point (`Db.execute`'s Javadoc).

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


Log
---

2026-11-06. Registered by harness 6.2's agent of the night 006-12: found
by the harness (018-03, section 5); in its skip list until fixed.

2026-11-06. Fixed in the night 006-12 by the same agent (the simplest fix
by the entry's First step; no decision needed, docs/levels.md's rule).

2026-11-06, 03:10. R5's F1 and F2 written up for Frans's decision (above);
its F3 (words: docs/levels.md's reflow, `StorageManager.hasFailed()` and
`getFailure()`) fixed with 018-03's follow-up.
