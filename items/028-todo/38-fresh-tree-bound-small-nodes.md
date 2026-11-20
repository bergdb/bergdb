028-38. Fix: Dag.freshTreeBound does not end at node sizes of 4 or less
========================================================================

Status: done. Kind: Fix. Frans: decided (2026-11-20).
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


Result
------

Frans decided (2026-11-20): the Dag takes a node size of 8 at least, in
place of a `freshTreeBound` made to end at 4 or less. A database has node
size 8, 14, 30 or 62 already (`DbBuilder`), and a start refuses a meta
block whose node size is not the start's (`Db.refuseOtherNodeSize`), so
no stream reaches a smaller one.

* `Dag.MIN_NODE_SIZE` = 8. `checkNodeSize`, which both constructors call
  (`Dag.createEmpty`, and `new Dag(TopNode, int)`, which `DbStarter`
  uses), refuses a size below it with an `IllegalArgumentException` that
  names 8, as it refuses one above 62.
* Dead code removed: `minFill`'s branch below 8 (m = 1), `theta`'s (0,
  off), the constant `MERGE_MIN_NODE_SIZE`, `checkFill`'s guards `m >= 2`
  and `theta > 0` and its text for m < 2, and `dirtyNodeBound`'s sentence
  on m < 2. `splitAbove`, `mergeCap` and `cutSize` had no branch.
* Kept, with a comment: `PeWriter.merges` (`m >= 2`, now always true),
  as PeWriter follows the Lean model's `Cfg.merges`
  (lean/contract/Contract/PeWriter.lean, lean/SIS/Tree/Pe.lean); and the
  `theta > 0` of `Dag.overflows`, as the model of the count
  (Contract/DirtyBound.lean, `overflowsD`) has it.
* `freshTreeBound` is unchanged. Its loop of the splits ends at every size
  it now gets: from node size 5, `overflows(ov, 1, false)` is below ov
  (room b - 3 >= 2 and q >= 2: 0 for ov = 1, at most 1 + (ov - 2) / 2
  after), checked by arithmetic for every size from 5 to 62 and ov up to
  200,000.
* Tests moved to 8 (`DagTester`): `testSplit0` (node size 6 to 8, ten
  keys in place of six, to pass the node), `testTimeSplit1a` (6 to 8),
  `testNoKlongNamesATakenBackNode` (4 to 8 became 8 to 12),
  `testDeleteEveryKeyAfterTheRootSplit` (4 and 8 became 8 and 14),
  `testDirtyNodeBoundOfDeletes` (6 dropped from 6, 8, 14, 30; its cases
  (2) and (2b), chains of single children that need m = 1, dropped, as no
  such chain forms from 8), `testDirtyNodeBoundSumsCollapsesOverTrees`
  (rebuilt at 8: two segment trees, each a root of two leaves, whose
  roots collapse in one transaction; the space root's count is at least
  the collapses and two klongs a delete). `MergeTester.testThresholds`
  and `DeadKlongTester.testTheta` no longer check values below 8.
* New: `DagTester.testNodeSizeBelow8Refused`: sizes 7, 6, 4, 1, 0 and -1
  refused by both constructors, with a message that names 8; 8 taken.
* `java/stress/unlinkfuzz.sh`: the configuration `drain-b6` (node size 6)
  is `drain-60` at node size 8, the same keys, deletes and rounds.
  `UnlinkFuzz`'s header: theta 2 at node size 8 (it said 1, stale since
  2026-11-12).
* Texts: 027-08, section on B (sizes below 8 refused), 027-02 (the trace
  header's theta), 030-29, section 1 (the difference at 4 and less gone).

No other use of a size below 8: the stress tests' `maxnode` is 8, 14, 30
or 62 in every script but `drain-b6`; the Lean trace tests and the
conformance sets export traces at 8 and above.

The Lean model of the bound (Contract/DirtyBound.lean; 030-29, section
1) still matches Java at node sizes 8, 14, 30 and 62, and at every size
from 8: `freshTreeBound`, `overflows`, `cutPartsBound`, `rootsAbove` and
`dirtyNodeBound` are unchanged, and `minFill` and `theta` give the same
values from 8. The model's `minFill` and `theta` keep their `b < 8`
branches, and the PE model its `Cfg.merges`; they differ from Java only
below 8, which Java refuses. No Lean file changed.


Gates
-----

On the change of this entry (the branch `028-fx1` on main c0b9683b):

* `java/before-commit.sh`: BEFORE COMMIT OK (124 s).
* `java/stress/unlinkfuzz.sh 20261120`: UNLINKFUZZ OK (3226 rounds,
  413 s), `drain-60` ok on both blocks.


Log
---

2026-11-20. Registered by coord-1120, from 030-29's report.

2026-11-20. In progress: fx1 of coord-1120, on the branch `028-fx1`.

2026-11-20. Frans decided: a minimum node size of 8 in the Dag, in place
of a fix of `freshTreeBound` at 4 or less (to coord-1120, 14:02).

2026-11-20. Done by fx1 of coord-1120: node sizes below 8 refused, their
code and tests removed or moved to 8.
