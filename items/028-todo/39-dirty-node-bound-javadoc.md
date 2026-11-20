028-39. Fix: dirtyNodeBound's Javadoc repeats a false step about joins
======================================================================

Status: open. Kind: Fix. Frans: none.
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


Log
---

2026-11-20. Registered by coord-1120, from 030-29's report.
