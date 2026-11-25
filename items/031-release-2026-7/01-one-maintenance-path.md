# 031-01. One maintenance path: back to empty, quiet when done

Created 2026-11-25 by Frans Lundberg. Status: open.

The design of BergDB's maintenance as one step for a commit and for
`maintain()` (026-03), together with the fix of RB-007 and of the
rewriting of live values in a database that is not written to (028-53).
A design only: nothing of it lands without Frans.


## 1. The request

Frans, 2026-11-25, 13:03: design 026-03 and 028-53's fix together,
rather than choosing between 028-53's options A, B and C on their own.
`maintain()` in the public API is not an absolute requirement; the
database's return to empty is wanted; one way into the maintenance work
would be the simpler design.

What the design is to give:

* one maintenance step that both a commit and `maintain()` call, or the
  reasons that keep two paths;
* back to empty: a database that has been emptied returns to about the
  stream of a fresh one under the calls (024-30's G5);
* quiet when done: a database not written to, with live values, stops
  writing under the calls once nothing is left to give back (028-53,
  sections 1 and 2);
* RB-007 fixed (028-53, section 3; 033);
* the stream deterministic (010-01, P2), and bounded startup (027-11).
* the effect on the Lean proofs (Frans, 13:04): which theorems, the
  model's scope (027-13, section 5; 030-25) and the contract and trace
  checkers change or stay, what new proofs the design needs or makes
  possible, and what a single step makes simpler to prove.

Sources: 026-03 (the question, the simple form with filler, the sync
inside `maintain()`, the tests to keep); 028-53 (the faults, the
options, A's design in section 8, its prototype on the branch
`028-53-a`); 024-32 (`maintain()` as built); 027-13, section 1.10 (M1);
010-01 (P2, P3, P4, P11, P13).


## 2. State

2026-11-25: registered; the design is taken by an agent of lead-1125.


Log
===

2026-11-25. Created (Frans's decision of 13:03, 006-35).
