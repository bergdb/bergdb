005-04. The A6 failures: is anything to be done?
================================================

Status: open. Kind: decide. Created 2026-10-19.


Background
----------

A6 ("no adoption") is an assumption that item 001's plan made about Java's
runs: a pointee of a node that is not its live child is a data node or not
reachable. It fails in 5 of 68,901 Java-tier transactions. All five are one
kind: a transaction creates the root of the next key segment's tree and
splits it in place (`Dag.spaceSplitInPlace`), so the segment leaf's earlier
klong of the same transaction, to the split node, becomes a dead pointer to
a node that is still below the leaf.

The proofs never used A6. They use a weaker form, A6', which allows exactly
this case, and A-COPY. Both hold in every Java transaction checked, and
Frans accepted this at K1 (2026-10-17). See
[03-k1-review.md](../001-lean-model-levels-3-4/03-k1-review.md), sections 1
and 3, and [level4-alignment.md](../../docs/level4-alignment.md), section 4.

So nothing is broken. The question is whether to leave it, or tidy up.


Options
-------

1. **Leave it.** A6 is the plan's word for a stronger property than needed;
   A6' is what the proofs need, and it holds. Only record that A6 is no
   longer a target (perhaps drop it from the Java tier's report, so "A6
   fails" stops looking like a failure).
2. **Change Java so A6 holds**: make the in-place split not leave a dead
   pointer in the same transaction (for instance split before the leaf's
   klong is written, or rewrite that klong). Then the model could assume the
   simpler A6. Cost: the records of such transactions change (the format
   stays, but StreamDigest differs from R8's), and Level 2's alignment and
   the conformance sets must be rerun; gain: a simpler assumption.
3. **Prove the assumptions for Java's algorithm.** TREE, A6' and A-COPY are
   checked on Java's runs, not proved. The model has `javaTest`, Java's
   algorithm with marking; proving that its runs meet TREE, A6' and A-COPY
   would turn three checked assumptions into theorems. This is the
   substantive version of the question, and it is more work than 1 or 2.
4. **Look for more kinds.** Only one kind of A6 failure has been seen. A
   short look at whether any other code path can adopt (with larger node
   sizes, reclaim's rewrites, eviction's reloads) would make option 1 safer.


Proposal
--------

Option 1 with option 4's short look now; option 3 as a candidate for later,
together with T-SCHEME (item 001's R6, also checked, not proved), if proving
the remaining checked assumptions becomes a goal (it would matter for a
publication, 005-06). Option 2 is not worth changing the records.


Done when
---------

Frans decides; the decision is recorded here and, if it changes anything,
in `level4-alignment.md`.


First step
----------

Read section 4 of level4-alignment.md and the Java tier's A6 output, and
search the code for other places where a node can gain a dead pointer to a
node still below it.


Size
----

S for options 1 and 4. Option 3 is M to L.
