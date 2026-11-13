028-04. Fix: what a null result of a value transformation does
==============================================================

Status: open. Kind: Fix. Frans: decision.
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
