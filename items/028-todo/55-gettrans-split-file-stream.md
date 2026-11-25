028-55. Investigate: getTrans fails in week.sh's Churn soak, seed 2078207, node size 30
=====================================================================================

Status: done: a fault of BergDB since 2026.5, S3; fixed on the branch
`028-55`. Kind: Investigate. Frans: none.
Created 2026-11-25 by Frans Lundberg.

What: `week.sh` on `main` at `09bf9efb` (2026-11-25, step apps-soak-cc):
the app Churn (a2, 024-26), `Churn 2078207 30 30 300 DIR 1000 500 0.25
0 400000 big`, failed after 50 transactions with no restart. Its
`verifyChains` called `Db.getTrans(167171320)`, a position that
`getOne` had given in `GetData.tpos`, and got "Not a position of a
transaction, 167171320: the bytes there are not a committed
transaction's record", caused by `StreamFormatException: Bad
transaction size, -1594286241, transPos=160000128, stream size:
340100968` (`NodeStream.readRecordHeader`, from `recordHolding` and
`TransIterator.next`). The stream is in files of 20,000,000 bytes; the
first kept file begins at 160,000,000, and the walk began at
160,000,128. The other 20 apps of the soak passed, and the same app
passed in earlier week runs with other seeds.

Why: a read of a committed transaction refused, or the walk to it
misreading the stream; through the Pub API, `Connection.transactionInfo()`
reads with the same walk, and a record that is not a committed
transaction fails the database there (021-27). A wrong refusal is S3, a
failed database S2 (033's rules); in 2026.6 too, a released bug.

Frans: none.

Done when: the failure reproduced from the seed (and from the kept
data, if it helps); its cause named; release 2026.6 checked; a fix with
a unit test that fails before it, `java/before-commit.sh` printing
`BEFORE COMMIT OK`, and the RB entry in 033 if 2026.6 has it.

First step: run the command above on `main`'s release jar; read
`NodeStream.recordHolding`, `TransIterator` and where the walk begins
for a position in the first kept file of a split file stream.


Result
------

Done 2026-11-25 by an agent of lead-1125, in a clone of `main` at
`c94c2e14`, on the branch `028-55`. A fault of BergDB, not of the app:
`Db.getTrans` (Core API) refuses the position of a committed transaction
over 1 MiB just after a reclaim cut, when a record reaches over the
first position that the storage keeps. S3. In releases 2026.5 and
2026.6. The Pub API is not affected.

### 1. Reproduced

* The command, on the clone's release jar: fails after 50 transactions,
  in 5 s, with the same exception, position, size and walk start as in
  `week.sh`'s run (`Bad transaction size, -1594286241,
  transPos=160000128`). Deterministic.
* On release 2026.6 (the tag `release-2026.6`, `bbcd802f`, built in a
  separate worktree): the same failure, the same numbers.
* The database that the failure left, opened again by a probe (a
  restart): `Db.getTrans(167171320)` refused the same way;
  `Db.getFirstAvailablePos()` is 167,168,744.
* The stream there: the first kept file begins at 160,000,000. The meta
  blocks from 160,000,000 to 167,000,000 all name the record at
  158,106,616, the last one completed before them: a record of the
  app's large values that begins in the file before and ends in this
  one, before 167,000,000. The block at 167,200,000 names 167,168,744,
  the record at reclaim's cut. The record at 167,171,320 is over 1 MiB.

### 2. The cause

* `Db.getTrans(tpos)` at a caller's position walks the records' sizes to
  `tpos` before it believes a size over 1 MiB there (021-27, Q27-1;
  `NodeStream.recordHolding`). The walk starts at
  `RecoverableStream.getRecordStartBefore(tpos)`: the record that the
  last valid meta block at or before `tpos` names, if it is at or after
  the stream's first position; otherwise the first position, after its
  meta block, taken for a record's start because reclaim cuts at one.
* The stream's first position is not reclaim's cut: `FileStream` drops
  whole files, so its first position is the first kept file's start,
  and `MemoryStream` whole arrays of 1 MB (027-03, section 4, for the
  files); only `CutStream`, a test stream, cuts exactly. A record that
  reaches over that start makes the first position a place inside a
  record.
* Here every meta block from the file's start to `tpos` names the record
  at 158,106,616, before the first position, so the walk began at
  160,000,128, inside it, read four bytes of a value as a size, and threw
  `StreamFormatException`, which `getTrans` turns into
  `IllegalArgumentException` (021-27). The registration's guess was
  right.

### 3. The reach

* **API:** the Core API's `Db.getTrans(tpos)` only. The Pub API's
  `Connection.transactionInfo()` reads with `Internal.getTrans`, the
  database's own position, which reads the record at `tpos` with no
  walk; on the kept database it read the transaction at 167,171,320
  (tt 17780000040540000, 12 nodes), before and after the fix. So 021-27's
  path that fails the database is not reached: not S2.
* **When:** a record over 1 MiB at `tpos`, after reclaim has cut the
  stream, and the last valid meta block at or before `tpos` names a
  record below the first position, the one that reaches over it: `tpos`
  is the record that follows that one, or a record that begins after
  the follower's end and before the next meta block (200 kB apart); at
  or after the cut, as a get gives. Records of at most 1 MiB are read
  with no walk and are not affected.
* **Streams:** `FileStream` (every file database, Pub and Core) and
  `MemoryStream`, after a cut that a record reaches over; not
  `OneFileStream`, which never cuts.
* **What a user sees:** `IllegalArgumentException`, "Not a position of a
  transaction", for a position that a get gave. Nothing is written; the
  database goes on.
* **Since:** `2858ed36` (021-27, Q27-1, 2026-11-12), the walk; in
  releases 2026.5 and 2026.6, not in 2026.4, which has no walk.
* **Severity:** S3, a call refused wrongly with no damage (033).

### 4. The fix

* `RecoverableStream.getRecordStartBefore(spos, cut)`: when no valid meta
  block at or before `spos` names a record at or after the first
  position, the walk starts at reclaim's cut (`Db.getFirstAvailablePos()`,
  a record's start), or at the first position if that is later (a stream
  not cut, or one cut exactly by a test), after its meta block, as
  before. `cut` is read after the first position: reclaim sets it before
  it cuts the stream, so it is never left below the first position by a
  cut between the two reads.
* A position after the first position and before the cut, with no
  record's start named before it, has no start to walk from; it is
  before the cut, so its transaction is no longer available
  (`Db.getFirstAvailablePos()`'s Javadoc): `getTrans` throws
  `LookupTimeNotAvailableException`, as for a read below the first
  position. Before, it was walked from inside a record and refused with
  `IllegalArgumentException`.
* `Db.getTransInner` passes `reclaim::getFirstAvailablePos` through
  `NodeStream.createTransIteratorAtCallersPos` and `recordHolding`; the
  Javadoc of the three and of `Db.getTrans` say so. Nothing else reads
  the walk's start; the stream format is unchanged.

Tests (unit, in `before-commit.sh`):

* `DbTesterFailure.testGetTransAfterACutInsideARecord`, about 0.1 s: a
  `MemoryStream`, values of 1.1 MB, so that each record reaches over an
  array's start; reclaim cuts at 1,101,912, the first position is
  1,000,000. Every record from the cut on is read at its position by
  `Db.getTrans` and by `Internal.getTrans`. Before the fix it fails:
  "Not a position of a transaction, 1102264", caused by "Bad transaction
  size, 0, transPos=1000128".
* `RecoverableStream.Tester.testRecordStartBeforeAfterCut`: in a stream
  cut at a 1 MB array with a cut after it, the start is the cut up to
  the next meta block and the named record after it; a position before
  the cut throws with `ReadBelowFirstPosException` as the cause; with no
  cut, the first position after its meta block, as before.

### 5. Gates

* `java/before-commit.sh`: `Unit: SUCCESS, 1750 successful tests`,
  `F:    SUCCESS, 89 successful tests`, `BEFORE COMMIT OK (207 s)`.
* The Churn command on the branch's release jar:
  `OK Churn seed 2078207 node 30 keys 30: 300 transactions, 738
  operations, 1 restarts, 1030 checks, old reads 9 ok and 19 cut, chain
  steps 10, max live stream 292456392, max ratio 6.162, 20080 ms`.
* `java/stress/apps.sh quick` (the fix is in the walk of the stream):
  `APPS OK`, 28 apps' OK lines.
* The kept database, opened by the probe on the branch's jar:
  `Db.getTrans(167171320)` reads the transaction (tt 17780000040540000,
  12 nodes), as `Internal.getTrans` does.


Log
---

2026-11-25. Registered by lead-1125, from `week.sh`'s report
(2026-11-25-1409).

2026-11-25. Done by an agent of lead-1125 on the branch `028-55`:
reproduced on `main` and on 2026.6; the walk of `Db.getTrans` began at
the first kept file's start, inside a record; it starts at reclaim's cut
now. S3, in 2026.5 and 2026.6: a released bug (033).
