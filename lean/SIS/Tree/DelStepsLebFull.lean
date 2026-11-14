/-
LE-b's full branch at the upward delete's stop node, the merges on (bergdb
024-12, case (4)'s delete steps): the stop node's last version with the empty key in
the next klong's place splits. The tree with that last version is the walk's
tree with the empty key's child gone and the next child under the empty key
(`treeOK_up_tr`, `rangeOrder_up_leb`) and reads as the delete's
(`getFromR_up_leb`); at the space root by `writerWP_handleFull_rootVReach` and
`writerWP_rootSplit_rangeL`.
-/
import SIS.Tree.DelStepsCascRoot
import SIS.Tree.TakeDeadUp
import SIS.Tree.TakeUpCasc
import SIS.Tree.RangeDelChainGV

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- What a node with its links relabeled reaches, the tree before reaches. -/
theorem tReach_updN_relabel (N : NodeId → Option KNode) (t : Time) (r x : NodeId) (m m' : KNode)
    (hNx : N x = some m) (hsub : ∀ c z, (c, z) ∈ m'.liveAt t → ∃ c0, (c0, z) ∈ m.liveAt t) :
    ∀ z, TReach (updN N x m') t r z → TReach N t r z := by
  intro z h
  induction h with
  | root => exact TReach.root
  | link _ hl ih =>
    rename_i u c y _
    obtain ⟨mm, hm, hc⟩ := hl
    by_cases hu : u = x
    · subst hu
      rw [updN_self] at hm
      cases hm
      obtain ⟨c0, h0⟩ := hsub c y hc
      exact TReach.link ih ⟨m, hNx, h0⟩
    · rw [updN_ne _ _ _ _ hu] at hm
      exact TReach.link ih ⟨mm, hm, hc⟩

end SIS.Tree
