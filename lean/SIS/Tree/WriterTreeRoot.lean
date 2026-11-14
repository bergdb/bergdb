/-
The writer's tree kept by a put that splits the space root (bergdb 024-22,
`OpTreeOK`), on prover latest's writer states of GetRootSplit.lean: the space
split under a new root (`writerWP_put_rootSpaceSplit_tree`, from
`treeOK_rootSplit`).
-/
import SIS.Tree.WriterTreePut
import SIS.Tree.GetRootSplit

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- What the tree from a new root above the root x reaches: the new root and
what x reached. -/
theorem tReach_newRootAbove (N N' : NodeId → Option KNode) (t : Time) (x R : NodeId) (m : KNode)
    (hT : TreeOK N t x) (hfR : N R = none)
    (hfresh : ∀ u c', TReach N t x u → ¬ TLink N t u c' R)
    (hNR : N' R = some m) (hm : ∀ c z, (c, z) ∈ m.liveAt t → c = 0 ∧ z = x)
    (hother : ∀ z, z ≠ R → N' z = N z) : ∀ y, TReach N' t R y → y = R ∨ TReach N t x y := by
  have hRR : ¬ TReach N t x R := not_reach_fresh N t x R hT hfR hfresh
  intro y hy
  induction hy with
  | root => exact Or.inl rfl
  | @link u c z _ hl ih =>
    obtain ⟨mm, hmm, hc⟩ := hl
    rcases ih with h | h
    · rw [h, hNR] at hmm
      simp only [Option.some.injEq] at hmm
      subst hmm
      rw [(hm c z hc).2]
      exact Or.inr TReach.root
    · have huR : u ≠ R := fun he => hRR (he ▸ h)
      rw [hother u huR] at hmm
      exact Or.inr (TReach.link h ⟨mm, hmm, hc⟩)

/-- A new root R above the root x, with x its only live child: the tree is
from R. -/
theorem treeOK_newRootAbove (N N' : NodeId → Option KNode) (t : Time) (x R : NodeId) (m : KNode)
    (hT : TreeOK N t x) (hfR : N R = none)
    (hfresh : ∀ u c', TReach N t x u → ¬ TLink N t u c' R)
    (hNR : N' R = some m) (hm : ∀ c z, (c, z) ∈ m.liveAt t → c = 0 ∧ z = x)
    (hother : ∀ z, z ≠ R → N' z = N z) : TreeOK N' t R := by
  have hRR : ¬ TReach N t x R := not_reach_fresh N t x R hT hfR hfresh
  have hb := tReach_newRootAbove N N' t x R m hT hfR hfresh hNR hm hother
  -- a link of N' from a reached node
  have hl' : ∀ y c z, (y = R ∨ TReach N t x y) → TLink N' t y c z →
      (y = R ∧ c = 0 ∧ z = x) ∨ (y ≠ R ∧ TLink N t y c z) := by
    intro y c z hy hl
    obtain ⟨mm, hmm, hc⟩ := hl
    by_cases hyR : y = R
    · rw [hyR, hNR] at hmm
      simp only [Option.some.injEq] at hmm
      subst hmm
      exact Or.inl ⟨hyR, hm c z hc⟩
    · rw [hother y hyR] at hmm
      exact Or.inr ⟨hyR, mm, hmm, hc⟩
  refine ⟨⟨m, hNR⟩, ?_, ?_⟩
  · intro y c hy hl
    rcases hl' y c R (hb y hy) hl with ⟨_, _, h⟩ | ⟨hyR, hlk⟩
    · obtain ⟨_, hk⟩ := hT.rootKey; rw [← h, hfR] at hk; cases hk
    · rcases hb y hy with h | h
      · exact hyR h
      · exact hfresh y c h hlk
  · intro y1 c1 y2 c2 z hy1 hy2 hl1 hl2
    rcases hl' y1 c1 z (hb y1 hy1) hl1 with ⟨h1, h1c, h1z⟩ | ⟨h1R, hlk1⟩ <;>
      rcases hl' y2 c2 z (hb y2 hy2) hl2 with ⟨h2, h2c, h2z⟩ | ⟨h2R, hlk2⟩
    · exact ⟨h1.trans h2.symm, h1c.trans h2c.symm⟩
    · have hy2' : TReach N t x y2 := (hb y2 hy2).resolve_left h2R
      rw [h1z] at hlk2
      exact absurd hlk2 (hT.rootFree y2 c2 hy2')
    · have hy1' : TReach N t x y1 := (hb y1 hy1).resolve_left h1R
      rw [h2z] at hlk1
      exact absurd hlk1 (hT.rootFree y1 c1 hy1')
    · exact hT.oneLink y1 c1 y2 c2 z ((hb y1 hy1).resolve_left h1R)
        ((hb y2 hy2).resolve_left h2R) hlk1 hlk2

end SIS.Tree
