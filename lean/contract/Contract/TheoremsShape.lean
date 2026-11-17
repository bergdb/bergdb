/-
The contract package (bergdb 030-08): the theorems of the shape clauses.

For any history that meets the writer's contract with TREE (`MeetsShape`,
ShapeStatement.lean): it meets the writer's contract, so the theorems on
reads (Theorems.lean) hold for it; and at every time of the history, the
latest and every earlier one, the tree meets TREE.
-/
import Contract.Theorems
import Contract.ShapeStatement
import Contract.Proof.Reach

namespace Contract

/-- A history that meets the contract with TREE meets the contract. -/
theorem MeetsShape.meets {p : Params} {txs : List (List Op)} {s : Tree}
    (h : MeetsShape p txs s) : Meets p txs s := by
  induction h with
  | start s hs _ => exact Meets.start s hs
  | step txs s ops D s' _ hc _ ih => exact Meets.step txs s ops D s' ih hc

/-- TREE at every time t of a history that meets the contract with TREE: no
node is reached twice from the space root of time t. -/
theorem tree_right {p : Params} {txs : List (List Op)} {s : Tree} (h : MeetsShape p txs s)
    (t : Time) (ht : t ≤ txs.length) : TreeOk (s.at t) := by
  induction h generalizing t with
  | start s _ htr =>
    obtain rfl : t = 0 := by simpa using ht
    exact htr
  | step txs s ops D s' hm hc htr ih =>
    simp only [List.length_append, List.length_singleton] at ht
    by_cases hlt : t ≤ txs.length
    · exact hc.2.treeOk (Nat.lt_succ_of_le hlt) (inv_right hm.meets t hlt) (ih t hlt)
    · obtain rfl : t = txs.length + 1 := Nat.le_antisymm ht (Nat.lt_of_not_le hlt)
      exact htr

end Contract
