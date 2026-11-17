/-
The contract package (bergdb 030-08): the clauses of the tree's shape, added
to the writer's contract (Statement.lean) by conjunction. To read and to
trust, with Reach.lean.

English. A history that meets the contract with TREE (`MeetsShape`): a
history that meets the writer's contract (`Meets`), in which the start tree
at time 0, and the tree after each transaction at its time, meet TREE (no
node reached twice, Reach.lean).

The theorems on reads hold as before, since such a history meets the
contract (`MeetsShape.meets`, TheoremsShape.lean); and TREE then holds at
every time of the history, the earlier ones too (`tree_right`).

A history that meets the contract with TREE and the top (`MeetsTop`): the
state is the tree and its top (Top.lean). It meets `MeetsShape`; the start
top and each transaction's top meet the top's clauses (`TopStart`,
`TopStep`: at most one new top node a transaction, the old ones fixed, the
skip pointers as `TopDs.newSuperRoot` makes them); and the tree's space roots
are the top nodes' root pointers (`rootsOf`). Then Java's search through the
skip pointers finds the space root of every time (`top_right`,
TheoremsTop.lean), and the readers that start from it, as Java's do, give
what the plain map gives (`jget_right`, `jscan_right`).
-/
import Contract.Top

namespace Contract

/-- A history that meets the writer's contract and TREE: from a start tree
that meets TREE, the transactions txs in order, the j-th at time j, each
meeting the writer's contract and ending in a tree that meets TREE at its
time. -/
inductive MeetsShape (p : Params) : List (List Op) → Tree → Prop where
  | start (s : Tree) : Start p s → TreeOk (s.at 0) → MeetsShape p [] s
  | step (txs : List (List Op)) (s : Tree) (ops : List Op) (D : List NodeId) (s' : Tree) :
      MeetsShape p txs s → Contract p (txs.length + 1) s ops D s' →
      TreeOk (s'.at (txs.length + 1)) → MeetsShape p (txs ++ [ops]) s'

/-- A history that meets the writer's contract, TREE and the top's clauses:
from a start tree and a start top whose root pointer is the tree's space
root, the transactions txs in order, the j-th at time j, each meeting the
writer's contract, ending in a tree that meets TREE at its time, with a top
that meets the top's clauses and whose root pointers are the tree's space
roots. -/
inductive MeetsTop (p : Params) : List (List Op) → Tree → Top → Prop where
  | start (s : Tree) (tp : Top) : Start p s → TreeOk (s.at 0) → TopStart tp →
      s.roots = rootsOf tp → MeetsTop p [] s tp
  | step (txs : List (List Op)) (s : Tree) (tp : Top) (ops : List Op) (D : List NodeId)
      (s' : Tree) (tp' : Top) :
      MeetsTop p txs s tp → Contract p (txs.length + 1) s ops D s' →
      TreeOk (s'.at (txs.length + 1)) → TopStep (txs.length + 1) tp tp' →
      s'.roots = rootsOf tp' → MeetsTop p (txs ++ [ops]) s' tp'

end Contract
