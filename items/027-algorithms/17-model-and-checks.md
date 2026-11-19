# 027-17. The model and its checks: the index

Created 2026-11-13 by Frans Lundberg. Status: stub.

Part 13 of 027's outline (027-04, section 2.3; levels: all). How an
implementation is tied to the model: the trusted part of the Lean model
(the definitions and the statements); the assumptions (A2 to A5, TREE, A6,
A-COPY, `LiveAppend`); what the proofs leave out (concurrency, bytes, torn
records, resource bounds); the mapping from Java's state to the model's
and its registers (011-11, 001-07, 001-08, 009-05); the checkers and their
sets (`conformance.sh`, `treeconf.sh`, `TakeCheck`, `A2A3Check2`; 027-02's
format); since record format 8 the tree checker's writer is PE
(lean/SIS/Tree/Pe.lean), shown to give the trees of the proved writer,
`Contract.PE.peTx` (030-21), on Java's traces by `pecmp`, a step of
`level2.sh` since 030-28 (first 026-25's), and the
contract checker (`lean/contract/check.sh`); the pins of the statements,
checked by `gate.sh` and, without a build, by `level2.sh` (030-15,
030-28); a table of every theorem with its part.

Not written yet: the outline's order of writing is 027-04, section 5.1.
Each part follows the template of 027-04, section 2.2.


Log
===

2026-11-13. Created as a stub (Frans, 11:09, 027-04's Q3: "as
recommended").

2026-11-19. The checks of the writer PE (026-25, 030-21). By an agent of
coord-1118, on the branch `027-pe`.

2026-11-19. 030-28: pecmp and the pins' check in level2.sh.
