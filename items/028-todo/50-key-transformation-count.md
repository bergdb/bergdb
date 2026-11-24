028-50. Fix: the dirty-node count of a key with a key transformation, after it
==============================================================================

Status: done. Kind: Fix. Frans: decided (A, 2026-11-24, 12:26).
Created 2026-11-24 by Frans Lundberg.

What: `Db.checkDirtyNodes` (`java/src/bergdb/core/Db.java`; 027-08,
section 4.2; 005-31) counts a key with a key transformation by the cheap
estimate with the segments of the key as given, as it runs before the
key transformations. A key transformed to a key of more segments can mark
more key nodes than counted: 46 for 39 in 028-45's test at node size 8
(028-45, Result, "The fault"). Released bug RB-005 (033), S4.

Why: a count below the key nodes a transaction marks lets through a
transaction whose index nodes could pass a record's room after its go
point; such a transaction would never be taken into a record, and
startup would grow without end (005-31; RB-005). Within `execute()`'s
limits, L1 to L5, a separate bound (TP26, stated, not proved) keeps the
case out of reach; the fix makes the count itself cover it.

Frans: decided, option A of 028-45 (2026-11-24, 12:26): count a key with
a key transformation after the transformation, by a second check right
after `Db.transformKeys`, under the write lock and before the go point,
where a refusal already gives the keys back (024-16), walking the keys as
transformed with `Dag.dirtyNodeBound`.

Done when:

* Db counts a user transaction with a key transformation after its key
  transformations, with the keys they gave: the cheap estimate, and
  `Dag.dirtyNodeBound` where the estimate does not fit; one over the limit
  is refused with a `DbException` before the go point, its keys as
  written, write hashes and time given back, nothing written, and the
  database goes on. What Db refuses for a transaction without key
  transformations is unchanged (`DbTester.testTooManyDirtyNodes`,
  `DbTesterLimits`, `LimitsTester` pass as before).
* 028-45's `testKnownFaultKeyTransformationDeeperThanCount` turned around:
  the transaction counted at least its marks, or refused where the count
  does not fit; `DbTesterDirtyCount.testCountsCoverMarkedKeyNodes` with
  the counts after the transformations; a test of a transaction refused
  by the new check, the record limit lowered as `DbTesterDirtyCount`
  does.
* The texts: 033's RB-005 (the fix, its commit, "fixed on main for
  2026.7"); 030-26, 2.7 and section 5, item 14, and 027-08, section 4.2,
  where they say the estimate is short; 030-38 unchanged (the record of
  2026.6).
* Gates: `java/before-commit.sh` BEFORE COMMIT OK; `java/stress/level2.sh`
  LEVEL 2 OK; StreamDigest `quick` identical to main's (028-01's run),
  as its workloads have no key transformations.

First step: read 028-45 (Result) and `Db.executeInner`, `checkDirtyNodes`
and `transformKeys`.


Result
------

Made on 2026-11-24 by an agent of lead-1124, on the branch `028-50`
(`33193b20`, and `a63cc559` for a test's Javadoc), rebased on `main`
(`cdf75b0e`).

* **The check after the key transformations.**
  `Db.checkDirtyNodesAfterKeyTransformations`, called in `executeInner`
  right after `transformKeys` for a user transaction with a key
  transformation (`before.keys != null`), under the write lock and
  before `transformValues` and the go point. It counts the transaction
  as `checkDirtyNodes` counts one without key transformations, with the
  keys they gave: the cheap estimate, and `Dag.dirtyNodeBound` where the
  estimate does not fit; a key with a value transformation as a put and
  as a delete, as before. A refusal gives back the keys as written,
  their write hashes and the time (`giveBack`, as `transformKeys`'
  refusals), with the message of 005-31 and "after its key
  transformations"; anything the count throws fails the database, as a
  read of `transformValues` does.
* **Decided on the way:** `checkDirtyNodes` leaves a transaction with a
  key transformation wholly to the new check, rather than counting its
  other keys first. The whole transaction is walked once: the count is
  not a sum over parts of a transaction (a node's overflows count the
  klongs of all the keys below it together), so the new check must walk
  every key anyway, and an earlier walk of a part would refuse nothing
  more and cost a second walk. A transaction with a key transformation
  is then refused exactly when the same transaction written with its
  keys as transformed would be. What Db refuses for a transaction
  without key transformations is unchanged: the same count, the same
  comparison, the same message.
* **For the tests:** `countDirtyNodes(Trans, Kv[], boolean)` counts
  given KVs; the counts go to the test hooks
  (`TestHooks.dirtyNodesCounted`, default methods), and
  `TestHooks.walkDirtyNodes` makes the check walk also where the
  estimate fits. `DirtyNodeCounts.refused()` (the estimate and the walk
  over the limit) keeps that walk from refusing anything. The method
  `countDirtyNodes(Trans)`, which counted before the transformations,
  is gone.
* **The tests** (`DbTesterDirtyCount`, unit, in `before-commit.sh`):
  * `testCountsCoverMarkedKeyNodes` takes the counts from the hook, after
    executing: each transaction counted once, after its key
    transformations if it has one. Node size 8: 85 transactions, 67
    estimates within the limit, 18 walked, none refused, 54 counted after
    key transformations; node size 30: 124, 78, 46, none refused, 55.
    (028-45's run, with the count before the transformations, refused 9
    at node size 30.)
  * `testKeyTransformationToDeeperKey`, the known-fault test turned
    around: 028-45's case marks 46 key nodes, counted 579 by the
    estimate and 153 by the walk (39 until 028-50).
  * `testRefusedAfterKeyTransformations`: the record limit lowered to
    10,400 bytes, a record 42 index nodes. The same transaction is
    refused (579 and 153 over 42; until 028-50 counted 39 and taken), its
    key as written, write hash and `t.tt` given back, nothing appended,
    no transaction; a put of a key of 16 segments transformed to "h" is
    taken (39 within 42; until 028-50 counted 579 and refused); with the
    limit restored the refused transaction, run again, is taken and
    marks 46 key nodes, more than the 42 of the lowered record.
* **Review rev24, R3's case** (a probe, not committed): node size 62, a
  stream of 265 kB, 500 KVs of 111-byte keys with identity key and value
  transformations. Main before the fix refuses it ("up to 2241500", over
  1,906,500 nodes); with the fix it is counted after the key
  transformations, 2,241,500 by the estimate and 7,540 by the walk, and
  taken.
* **Texts:** `Db`'s class Javadoc ("Limits"), `execute`'s `@throws`,
  `checkDirtyNodes` and `KeyTransformation`; 027-08, 4.2 and 6; 030-26,
  2.7 and section 5, item 14; 033, RB-005 fixed on `main` for 2026.7;
  `releases/next.md`, RB-005 under "Released bugs fixed". 030-38 is
  unchanged (the record of 2026.6).

Gates, in the clone, on the branch rebased on `main`:
`java/before-commit.sh` printed `BEFORE COMMIT OK (61 s)` (before the
rebase `BEFORE COMMIT OK (63 s)`); `java/stress/level2.sh` (full, at
nice 10) printed `LEVEL 2 OK`; StreamDigest `quick`, the stress classes
of main's build (`7290967f`) run against that build's jar and against
the branch's, printed `DIGESTS IDENTICAL (44 of 44; of the identical,
the physical cut differs in 0)`: its workloads have no key
transformations.


Log
---

2026-11-24. Registered by an agent of lead-1124: Frans chose 028-45's
option A (12:26); RB-005.

2026-11-24. In progress: taken by an agent of lead-1124, on the branch
`028-50`.

2026-11-24. Done by an agent of lead-1124 on the branch `028-50`: a
transaction with a key transformation is counted after its key
transformations; the known-fault test turned around, a test of the new
refusal; RB-005 fixed on `main` for 2026.7. Gates: BEFORE COMMIT OK,
LEVEL 2 OK, StreamDigest identical. Moved to Closed.
