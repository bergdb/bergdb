005-45. Fix: two faults found on the way in 005-40 and 005-41
=============================================================

Status: done. Kind: fix. Created 2026-10-25.

Two small faults that 005-40 and 005-41 found on the way and left: "Not
fixed". Registered and fixed by Claude (Opus 5.5, Claude Code) before
release 2026.1 (008), at Frans's request: "Are there any known bugs in
BergDB? If so, we should fix them before the release."


The faults
----------

**`SalsaStream.getLength()`** (005-40). It gave the underlying stream's
length when the `SalsaStream` was made, and did not count what it
appended: after appends of 150 bytes it said 0. `AppendOnlyStream` says
that the length is "the total number of bytes ever appended". BergDB's own
stack did not meet it: a `BufferedStream` is always above it, and reads its
length only before its first append. A test or a tool that writes through a
`SalsaStream` directly got wrong positions, as the first version of
`RecoverableStream.testRecoverWithWrongKeyWritesNothing` did.

**`WTransaction.sync(SyncLevel)`** (005-41, and 005-44's outcome). It
waited for the database's last transaction (`Db.sync(level)`, position 0),
not for its own, as its `sync()` and an rw-transaction's `sync(level)` do.
It waited longer than it needed to, never too short: while a later
transaction of another thread was being written, the sync of an earlier,
durable one waited for it.


The fix
-------

* `SalsaStream.getLength()` gives the underlying stream's length, which
  counts its appends: the encryption keeps every byte's position, so the
  two lengths are the same. The field `length` is gone; the constructor
  reads the length once, as before.
* `WTransaction.sync(SyncLevel)` calls `Db.sync(trans.lastPos, level)`, as
  `sync()` does.

Not changed: `SalsaStream.seekFirstPos`, for replication only (005-11),
leaves the keystream at the old length. No `SalsaStream` is under a replica
today (005-11, P10: replicas are not encrypted).


Outcome
-------

2026-10-25, by Claude (Opus 5.5, Claude Code), on `f641780`, with 005-42:

* `SalsaStream.testLengthCountsAppends`: 150 after appends of 100 and 50
  bytes, and 160 after 10 more through a new `SalsaStream` on the same
  stream. Before the fix: "Expected 150, got 0."
* `PubTester.testWSyncLevelWaitsForItsOwn`: a stream that holds back the
  appends of a later transaction; the first one's `sync(ORDINARY)` must
  return, as it is durable. Before the fix it waited until the 5 s limit:
  "sync(ORDINARY) waited for a later transaction". After it, 31 ms.
* `before-commit.sh` passes, with 005-42's change.
