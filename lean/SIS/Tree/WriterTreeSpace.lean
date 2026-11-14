/-
The writer's tree kept by a space split (bergdb 024-22, `OpTreeOK`): a segment
leaf L that existed before the transaction, with a klong put into it, is split
into two new leaves, the halves of its last version with the klong
(`halves`); its inner parent q, with room, gets its klong of L pointed to the
first and a klong of the divider for the second; L keeps its klongs before the
transaction (`SpaceSplitAfter`). The tree is kept (`treeOK_spaceSplitAfter`, by
`treeOK_transfer_gone`: a klong of L goes to the first half below the divider,
to the second from it).
-/
import SIS.Tree.WriterTreeOps
import SIS.Tree.GetSplit
import SIS.Tree.SpaceSplitMap
import SIS.Tree.WalkComplete

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-! ## Nodes -/

/-- A node of one time's klongs: its live klongs are among its pairs. -/
theorem liveAt_newKlongs_mem (leaf : Bool) (t t' : Time) (pairs : List (Nat × NodeId)) (c : Nat)
    (z : NodeId) (h : (c, z) ∈ ({ leaf := leaf, ks := newKlongs t pairs } : KNode).liveAt t') :
    (c, z) ∈ pairs := by
  have hk := KNode.liveAt_key_mem _ t' c z h
  simp only [newKlongs, List.mem_cons, reduceCtorEq, false_or, List.mem_map] at hk
  obtain ⟨q, hq, he⟩ := hk
  rcases q with ⟨a, b⟩
  simp only [Klong.key.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  exact hq

/-! ## The state after a space split, and its tree -/

/-! ## The writer's space split -/

/-! ## The space split of the space root -/

end SIS.Tree
