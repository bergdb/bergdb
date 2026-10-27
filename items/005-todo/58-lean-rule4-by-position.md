005-58. Investigate a Lean theorem for rule 4 by position
=========================================================

Status: open. Kind: investigate. Created 2026-10-27.

Registered at Frans's request, as his answer to question 4 of 005-57's
report ("A Lean theorem for the claim?"), 2026-10-27: "Yes, but in a
separate work item in 005."


The issue
---------

Since 005-57, Java's rule 4 (`DbStarter.linkD`, `NodeCollection.
linkToCanonical`) finds the node that a pointer of D names by the
pointer's position, without reading the stream: by the startup section's
ids (`posToId`: each index node version in the section, and the version
before each key node version there), or among the canonical objects by the
positions of their versions. A pointer whose position is in neither is left
as it is. 005-57's report, section 2, argues that this links every pointer
that rule 4 by node id links: every write of a node after the version that
a node of D names is in the startup section (001-08, 5.4, case 5). The
argument is checked at every startup of the tests, where rule 4 by node id
runs beside it with assertions on, and it found no difference. It is not a
theorem.

The Lean model's rule 4 (`Mem.linkD` in `lean/SIS/Evict.lean`,
`HMem.linkD` in `lean/SIS/Handle.lean`) finds the canonical object by node
id. In the model a slot names its node, so that costs nothing; the
positions that Java has to work with are not in it.


Questions
---------

1. The statement. On every state that the model's startup reaches
   (`handleStartup`, after the rerun), for a pointer that holds no handle,
   of a pinned object, to a node y that has a canonical object o: the
   pointer's record is in the startup section, or is the record of y's
   version just before y's first version in the section, or is the record
   that o's version came from (o's position, `sectionPos`). And the
   converse that makes the two rules equal: a pointer whose record is
   neither names no node with a canonical object.
2. What the model needs for it: "the version before", a node's previous
   version in the stream, as Java's `prevPos` (the model has the records,
   `newest` and `sectionPos`, not a version chain); top nodes, whose
   versions have no `prevPos` in Java (011-03, G3), so the statement
   excludes the root's children or the model gives them none either.
3. Which lemmas it rests on: the record rule (INV-SLOT, `T2_cache`),
   D closed upward and Rule A (TREE, A6'), the take's invariant
   (every node of D has its got-dirty index after s); which of them the
   model has as theorems today, and which are assumptions of `EvictStep`.
4. Then: state Java's rule 4 by position in the model (a `linkDPos` beside
   `HMem.linkD`) and prove that they are equal on reachable states, so that
   the checker's C-H covers the Java code as it is.


Done when
---------

The theorem in `lean/`, with `lake build` clean and no `sorry`; 005-57's
report and `docs/levels.md` cite it; the check under assertions in
`NodeCollection.linkToCanonical` may then stay or go, for Frans to decide.


First step
----------

Read `HMem.linkD` and `handleStartup` with their lemmas
(`lean/SIS/Proof/HandleInit.lean`, `EvictInit.lean`), and write the
statement of question 1 in the model's terms, with what it needs (question
2), before any proof.


Size and order
--------------

M, at a guess. Independent of the code; it can go any time.
