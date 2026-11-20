028-38. Fix: Dag.freshTreeBound does not end at node sizes of 4 or less
========================================================================

Status: open. Kind: Fix. Frans: none.
Created 2026-11-20 by Frans Lundberg.

What: the loop over splits in `Dag.freshTreeBound`
(java/src/bergdb/dag/Dag.java) never ends at a node size of 4 or less.
Only Dag's own tests use such node sizes; a user's database has node
size 30 (026-08), BergDB's tests also 8, 14 and 62. Found by 030-29 while
modelling `dirtyNodeBound` in Lean.

Why: a method that does not end for some of its inputs is a fault even
where no caller reaches it; a test with a small node size would hang.

Frans: none.

Done when: freshTreeBound ends for every node size it accepts, or refuses
the sizes it cannot bound; a unit test for a node size of 4 or less;
030-29's Lean model of the bound (Contract/DirtyBound.lean) still matches
it; `java/before-commit.sh` BEFORE COMMIT OK.

First step: 030-29, section 1, where the bound is compared with Dag.java
line by line.


Log
---

2026-11-20. Registered by coord-1120, from 030-29's report.
