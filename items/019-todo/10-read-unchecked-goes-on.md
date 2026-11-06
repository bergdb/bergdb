019-10. Fix: an unchecked exception or Error from a read of the storage leaves the database going on
================================================================================================

Status: open. Kind: Fix. Frans: none.
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


Log
---

2026-11-06. Registered by harness 6.2's agent of the night 006-12: found
by the harness (018-03, section 5); in its skip list until fixed.
