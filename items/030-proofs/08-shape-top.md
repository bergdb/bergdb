# 030-08. The tree's shape and its top in the contract

Created 2026-11-17 by Frans Lundberg. Status: open.

Step 4b of 030-04: the two simplifications that 030-05 and 030-06 name,
and the shape clauses of 030-06's finding F3. TREE (no node is reached
twice) as a clause of the contract; Java's top nodes and skip pointers in
the contract's tree, with the readers' top search as Java does it
(`TopDs.findSuperRootAtTime`); the reads' theorems restated over the tree
with its top. Written by an agent of coord-1117, "I" below, on the branch
`030-08-top`.


# 1. The result

Work in progress; see the Log and the State note.

- **TREE is a clause** (work list item 1, done). `MeetsShape`
  (`Contract/ShapeStatement.lean`): a history that meets the writer's
  contract, in which the start tree and the tree after each transaction,
  at its time, meet TREE: the walk from the space root through the live
  klongs reaches no node twice, values included (`TreeOk`,
  `Contract/Reach.lean`). Proved: such a history meets the contract
  (`MeetsShape.meets`), so `inv_right`, `get_right` and `scan_right` hold
  for it unchanged; and TREE holds at every time of it, the earlier ones
  too (`tree_right`). The DAG of 030-06 does not meet it
  (`ExampleDag.not_tree`); Example3's three transactions do
  (`Example3.meetsShape`, not vacuous). Tested: the checker's C4
  (`treeOkB`, proved to give `TreeOk`) on the 180 traces of the level 2
  sets, 21,000 transactions, no failure; a trace with a value node made
  shared fails C4.


# 2. Decisions

- **TREE as "no node reached twice"** (`(reach s).Nodup`), not the
  abstract model's form (every reached node but the root has exactly one
  reached parent among the distinct parents, `treeAt`). Mine is a little
  stronger (it also rules out one node naming the same child by two live
  klongs) and much simpler to state and to compute; Java met it on every
  trace. The bridge (030-07) derives `treeAt` from it.
- **Only at the transaction's own time in the clause;** the earlier times
  follow from the frame (`Frame.treeOk`), as the invariants do.
- **Values count.** A value node is a node of the abstract model; two keys
  must not share one.
- **The checker computes it by sorting** (`treeOkB`: the list sorted,
  strictly increasing), O(n log n) a transaction, with a proof that it
  gives `TreeOk`; `List.Nodup`'s own decision is quadratic.
- **New files, the shared ones in small hunks** (common rules):
  `Reach.lean`, `ShapeStatement.lean`, `CheckShape.lean`,
  `Proof/Reach.lean`, `TheoremsShape.lean`, `ExampleShape.lean`; in
  `ContractCheck.lean` the C4 lines; `Contract.lean` and `Axioms.lean`
  lines added at their ends.


# State

2026-11-17, 15:30. Started. Branch `030-08-top` in the clone
`/Users/f/fl/bench/2026-11-17/night/s4b/clone`, from `main` fc183148.


# Log

2026-11-17, 15:09. Started from the brief of coord-1117.
2026-11-17, 15:55. TREE as a clause: `MeetsShape`, `tree_right`, C4 on
the small and drain sets (180 traces, no failure).
GATED 1a1a441b: TREE as a clause of the contract (`MeetsShape`, `tree_right`), C4 on the traces.
