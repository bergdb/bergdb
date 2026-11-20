028-39. Fix: dirtyNodeBound's Javadoc repeats a false step about joins
======================================================================

Status: done. Kind: Fix. Frans: none.
Created 2026-11-20 by Frans Lundberg.

What: 028-21's argument on paper for deletes, and the Javadoc of
`Dag.dirtyNodeBound`, have a false step: a node joined from a small and a
non-small node can end small and be joined again. The bound still covers
it by far (030-29: 8 against 2,279 in its example), and 421,000 random
model transactions (about 128,000 with deletes) found none above the
bound. 030-29 proved the bound for transactions of puts only; the delete
case is open (030-29).

Why: 027 and the comments document what the code does (027-04); a false
step in an argument misleads the proof of the delete case.

Frans: none.

Done when: the Javadoc and 028-21 state the argument without the false
step, or say what is proved (puts, 030-29) and what is tested (deletes);
`java/before-commit.sh` BEFORE COMMIT OK (comments only).

First step: 030-29's report on the join step.


Result
------

The false step, as 030-29, section 4, shows it: 028-21's argument held
that a joined group is its small children and at most one other node, so
a delete's joins make at most three nodes a level. A join of two inner
nodes rebalances the joined list one level down, where cut parts can
merge again; a node joined from a small and a non-small node can then end
with fewer than m entries and be joined again, with a second node that is
not small.

* `Dag.dirtyNodeBound`'s Javadoc: the joins' item keeps what holds (a
  child is joined only if it is small; in a transaction of puts none is,
  proved by 030-29; with deletes a child is small only with a delete
  below it; the count's four nodes a level and four klongs a node of a
  delete's path for the joins), names 028-21's step as false with
  030-29's example, and says that for deletes the count is tested. Its
  last paragraph says what is proved (puts: 030-29,
  `Contract.PE.pe_dirtyNodeBound_puts`, at every node size from 8, given
  the fill rules that C-T6 checks) and what is tested (deletes:
  DagTester's tests, C-T8, 030-29's 421,000 random model transactions,
  about 128,000 with deletes). Comments only.
* 028-21: a dated correction after its argument for PE, the same
  content; its text is kept as the record.
* 027-03, section 8.3: the sentence on joins says the argument had a
  false step and that the count for deletes is tested, not proved. 027-08,
  section 4.2, says so already ("for transactions with deletes argued ...
  and tested"); a clause added on the false step.


Gates
-----

On the branch `028-fx1` after 028-38's commit, with this entry's and
028-37's changes: `java/before-commit.sh` BEFORE COMMIT OK (67 s).
Comments and item text only.


Log
---

2026-11-20. Registered by coord-1120, from 030-29's report.

2026-11-20. In progress: fx1 of coord-1120, on the branch `028-fx1`.

2026-11-20. Done by fx1 of coord-1120: the Javadoc, 028-21, 027-03 and
027-08 say what is proved (puts) and what is tested (deletes).
