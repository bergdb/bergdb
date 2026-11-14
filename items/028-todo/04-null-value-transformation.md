028-04. Fix: what a null result of a value transformation does
==============================================================

Status: done (2026-11-14). Kind: Fix. Frans: decision (A).
Created 2026-11-13 by Frans Lundberg.

What: `ValueTransformation.transform()`'s Javadoc says nothing of a null
result, and says that the result "is checked as a value given directly",
which for null is a refusal.

Why: the null result deletes the key (B2's probe), which a user cannot
know.

Frans: decision (A: document the delete, recommended, no behaviour change;
B: refuse it with a `DbException` as 026-06's other refusals, with a
test).

Done when: the Javadoc says what a null result does, and for B the test.

First step: B2's probe as a unit test of the delete.


Log
---

2026-11-13. Registered by coord-1113, from 026-13, section 5 (U13-2).

2026-11-14, 11:43. Frans: "'I recommend A'. Yes, sounds good. Do it."
Option A: document the delete, no behaviour change.

2026-11-14. Done by an agent of coord-1114, in the commit "028-04: a
null result of a value transformation deletes the key (Javadoc and a
test, no behaviour change)" on branch 028-04-null-transform:
`ValueTransformation.transform()`'s Javadoc now says that a null result
deletes the key, as a delete of the key in the same transaction would,
and is not refused, though a null value given directly to
`Trans.Builder.put()` is: the transaction commits, the key has no value
at its time, and `Db.getTrans()` lists the delete; for a key without a
previous value the delete stores nothing, the transaction commits and
`getTrans()` does not list the key. Its sentence "Its result is checked
as a value given directly" now reads "A non-null result is checked as a
value given directly", and `@return` says "or null to delete the key".
B2's probe is the unit test `DbTester.testValueTransformationNullDeletes`
(a key with a value and one without, in one transaction; the values at
the transaction's time and one unit before, `getTrans()`'s list, and a
restart). `java/before-commit.sh` printed `BEFORE COMMIT OK`.
