028-50. Fix: the dirty-node count of a key with a key transformation, after it
==============================================================================

Status: in progress. Kind: Fix. Frans: decided (A, 2026-11-24, 12:26).
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


Log
---

2026-11-24. Registered by an agent of lead-1124: Frans chose 028-45's
option A (12:26); RB-005.

2026-11-24. In progress: taken by an agent of lead-1124, on the branch
`028-50`.
