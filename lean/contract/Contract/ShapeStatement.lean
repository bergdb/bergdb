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
-/
import Contract.Reach

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

end Contract
