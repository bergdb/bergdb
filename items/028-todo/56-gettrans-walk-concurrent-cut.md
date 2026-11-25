028-56. Fix: getTrans's walk refuses a kept transaction when a cut comes during it
===================================================================================

Status: done: a fault of BergDB since 2026.5, S3; fixed on the branch
`028-56`. Kind: Fix. Frans: none.
Created 2026-11-25 by Frans Lundberg.

What: `Db.getTrans(tpos)` of a transaction of over 1 MiB walks the
records' sizes from a record's start that a meta block names
(`RecoverableStream.getRecordStartBefore`, `NodeStream.recordHolding`;
021-27, Q27-1; 028-55). The stream's first position is read before the
meta block; a cut made by another thread during the walk can remove the
named record, which is below reclaim's cut though `tpos` is not, and
the walk's read below the first position makes `getTrans` throw
`LookupTimeNotAvailableException` for a transaction that is kept. A
retry succeeds. Found by Codex's review of 028-55 (2026-11-25), with a
probe that holds the cut with latches (`DbCutRaceProbe`: a get gave
`tpos` 1,102,264, the cut stayed at 1,101,912, the first position
became 1,000,000, the walk's named start was 512); the same on `main`
before 028-55, so since 2026.5 (`2858ed36`).

Why: a call refused wrongly (033: S3, a race), in the Core API only;
`Connection.transactionInfo()` does not walk.

Frans: none.

Done when: the race reproduced on `main` with a probe or a unit test
that fails before the fix; the fix (Codex's lead: no named start below
the cut read at the walk's start, and a new start when a cut removes
what the walk reads while `tpos` is still kept); `java/before-commit.sh`
printing `BEFORE COMMIT OK`; whether 2026.5 and 2026.6 have it, and if
so an RB entry drafted for 033.

First step: 028-55's entry and fix; `RecoverableStream.getRecordStartBefore`
and `NodeStream.recordHolding`; Reclaim's cut and BufferedStream's
first position.


Result
------

Done 2026-11-25 by an agent of lead-1125, in a clone of `main` at
`c041ac79`, on the branch `028-56`. A fault of BergDB: `Db.getTrans`
(Core API) of a committed transaction over 1 MiB throws
`LookupTimeNotAvailableException` for a transaction that is kept, when
another thread cuts the stream during the walk to its position. S3. In
releases 2026.5 and 2026.6. The Pub API is not affected.

### 1. Reproduced

* On `main` at `c041ac79`, with the review's probe (`DbCutRaceProbe`): a
  stream that holds its cuts back while reclaim's cut moves on, and a
  reader that stops, by latches, at its read of the meta block before
  `tpos` until the stream is cut at reclaim's cut. `Db.getTrans(1102264)`,
  a position that a get gave, threw `LookupTimeNotAvailableException`;
  the cut was 1,101,912, the first position 1,000,000, and the walk read
  the record at 512, which the meta block names. Deterministic, with no
  timing. A retry read the transaction.
* On release 2026.6 (the tag `release-2026.6`, `bbcd802f`, built in a
  separate worktree): the same, the same numbers. On 2026.5
  (`release-2026.5`, `3611130c`): the same at `tpos` 1,302,240, the cut
  1,301,912. In both, a retry at this position is refused too, by RB-008
(028-55).

### 2. The cause

The walk (021-27, Q27-1; 028-55) reads records before `tpos`, and the
stream before reclaim's cut may be removed at any time
(`Db.getFirstAvailablePos()`), by a cut that another thread makes. Two
ways such a cut removed a record that the walk reads while `tpos` stays
at or after the cut:

* `RecoverableStream.getRecordStartBefore` took the record that the meta
  block before `tpos` names if it was at or after the stream's first
  position, which it read before the meta block; a named record below
  reclaim's cut was taken too. A cut between the two reads removed it
  (the probe's case).
* A cut that moves reclaim's cut during the walk, past the record the
  walk started from and not past `tpos`, removes the records that the
  walk reads next.

The walk's read below the first position throws `StreamIoException`
with `ReadBelowFirstPosException`, which `Db.getTrans` turns into
`LookupTimeNotAvailableException`, as for a transaction that reclaim
removed.

### 3. The reach

* **API:** the Core API's `Db.getTrans(tpos)` only. The Pub API's
  `Connection.transactionInfo()` reads with `Internal.getTrans`
  (`ConnectionImp`, in 2026.6 too), which reads the record at `tpos`
  with no walk; a read there that fails below the first position is a
  real expiry, as the stream is cut only before reclaim's cut.
* **When:** a record over 1 MiB at `tpos`; a cut of the stream by
  reclaim during the call, between its read of the first position and
  the walk's read of the named record, or while the walk reads the
  records after it. The window is a few reads. Not seen outside the
  probe.
* **Streams:** `FileStream` and `MemoryStream`, which reclaim cuts; not
  `OneFileStream`.
* **What a user sees:** `LookupTimeNotAvailableException` from
  `Db.getTrans` for a position that a get gave, whose transaction is
  kept. Nothing is written; the database goes on.
* **Since:** `2858ed36` (021-27, Q27-1, 2026-11-12), the walk; in
  releases 2026.5 and 2026.6.
* **Severity:** S3, a call refused wrongly with no damage (033).

### 4. The fix

* `RecoverableStream.getRecordStartBefore(spos, cut)`: the record that a
  meta block names is taken only if it is at or after both the first
  position and reclaim's cut; otherwise the walk starts at the cut, or
  at the first position after its meta block, as before. The meta blocks
  at or before the later of the two are not read, as the records they
  name are before it; so every read of the walk is at or after the cut
  it began with. A position before the cut expires before any read,
  also when a named record before it is still in the stream: such a
  transaction is no longer available (`Db.getFirstAvailablePos()`). A
  record of at most 1 MiB is read with no walk, as before.
* `NodeStream.recordHolding`: a read below the first position, when
  reclaim's cut has moved since the walk began and not past `tpos`,
  starts the walk again, from the new cut or a record after it that a
  meta block names. The stream is cut only before reclaim's cut, so
  such a read follows a move of the cut. Each walk reads as before, and
  there is at most one more walk than moves of the cut during the call.
* A position that a cut passed expires as before: a cut past `tpos`, or
  a read below the first position with the cut not moved, is thrown,
  and `Db.getTrans` throws `LookupTimeNotAvailableException`.
* `Db.isReadBelowCut` is package-private, for `recordHolding`; the
  Javadoc of the three methods and of `Db.getTrans` says so. The stream
  format is unchanged; `readAValidMetaBlock`'s other callers search as
  before.

Tests (unit, in `before-commit.sh`):

* `DbTesterFailure.testGetTransCutDuringTheWalk`, about 0.1 s: the
  probe's case in a `Db`, with `CutHeldStream`; the reader stops at the
  walk's first read, which was the meta block's. Before the fix it fails:
  `LookupTimeNotAvailableException` at 1,102,264, caused by "Cannot read
  from position 512, first valid position is 1000000".
* `NodeStreamTester.testRecordHoldingCutDuringTheWalk`, about 0.01 s:
  `recordHolding` on a `MemoryStream`, with reclaim's cut moved at the
  read of the meta block before `tpos` and the stream cut to 1,000,000.
  With the cut moved to a record before `tpos` the walk starts again and
  finds `tpos`; before the fix it fails: "Cannot read from position 128,
  first valid position is 1000000". With the cut moved past `tpos`, or
  not moved, the read is thrown, with `ReadBelowFirstPosException` as
  the cause.

### 5. Gates

* `java/before-commit.sh`: `Unit: SUCCESS, 1752 successful tests`,
  `F:    SUCCESS, 89 successful tests`, `BEFORE COMMIT OK (176 s)`.
* The review's probe, `DbCutRaceProbe`, with its reader stopped at the
  walk's first read (on `main` and in the releases the read of the meta
  block before `tpos`; the fix reads no meta block before the cut): on
  the branch, `Db.getTrans(1102264)` reads the transaction (tt
  20000000), the stream cut to 1,000,000 during the walk; on 2026.5 and
  2026.6 it reproduces as in section 1.
* The Churn command of 028-55 on the branch's release jar:
  `OK Churn seed 2078207 node 30 keys 30: 300 transactions, 738
  operations, 1 restarts, 1030 checks, old reads 9 ok and 19 cut, chain
  steps 10, max live stream 292456392, max ratio 6.162`.
* `java/stress/apps.sh quick` (the fix is in the walk of the stream):
  `APPS OK`, 28 apps' OK lines.


Log
---

2026-11-25. Registered by lead-1125, from Codex's review of 028-55.

2026-11-25. Done by an agent of lead-1125 on the branch `028-56`:
reproduced on `main`, 2026.5 and 2026.6 with latches; the walk takes no
named record below reclaim's cut, and starts again after a cut that
removes what it reads while `tpos` is kept. S3, in 2026.5 and 2026.6: a
released bug (033).
