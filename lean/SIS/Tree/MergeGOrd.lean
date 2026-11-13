import SIS.Tree.WriterTreeMerge
import SIS.Tree.MergeProps

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-! The merge's second node's compare value (bergdb 024-12, case (4)): where it
comes from in the merged klongs, for the full parent's ranges and order. -/

/-- `MergeGOK` with the order of the second node's compare value g: g is
positive, and when it is a live compare value of the left node, another one of
the left node is below it. -/
def MergeGOrd (ln rn : KNode) (cR : Nat) (m2 : Option (NodeId × Nat)) (t : Time) : Prop :=
  ∀ y g, m2 = some (y, g) → 0 < g ∧ (g = cR ∨ (∃ z, (g, z) ∈ rn.liveAt t) ∨
    ((∃ z, (g, z) ∈ ln.liveAt t) ∧ ∃ c0 z0, (c0, z0) ∈ ln.liveAt t ∧ c0 < g))


/-- `MergeGOrd` for the merge's two nodes: g heads the second half of the
sorted merged klongs (`mrg_splitMerged_two`), so the first merged klong is below
it. -/
theorem mergeGOrd_two (inner : Bool) (ln rn : KNode) (t : Time) (cR h g : Nat) (yg m : NodeId)
    (hlt : ∀ s, Klong.time s ∈ ln.ks → s ≤ t) (hrt : ∀ s, Klong.time s ∈ rn.ks → s ≤ t)
    (hs : CvSorted (mergeList inner cR ln.live rn.live)) (hh : 1 ≤ h)
    (hgs : ((mergeList inner cR ln.live rn.live).drop h).head? = some (g, yg)) :
    MergeGOrd ln rn cR (some (m, g)) t := by
  intro y g' hyg
  simp only [Option.some.injEq, Prod.mk.injEq] at hyg
  obtain ⟨_, hgg⟩ := hyg
  rw [← hgg]
  have hmemD : (g, yg) ∈ (mergeList inner cR ln.live rn.live).drop h := List.mem_of_mem_head? hgs
  have hmem : (g, yg) ∈ mergeList inner cR ln.live rn.live := List.mem_of_mem_drop hmemD
  -- the first merged klong is below g
  obtain ⟨a, rest, hal⟩ : ∃ a rest, mergeList inner cR ln.live rn.live = a :: rest := by
    cases hm : mergeList inner cR ln.live rn.live with
    | nil => rw [hm] at hmem; cases hmem
    | cons a rest => exact ⟨a, rest, rfl⟩
  have hag : a.1 < g := by
    rw [hal] at hs hmemD
    obtain ⟨h', rfl⟩ : ∃ h', h = h' + 1 := ⟨h - 1, by omega⟩
    simp only [List.drop_succ_cons] at hmemD
    exact (List.pairwise_cons.mp hs).1 _ (List.mem_of_mem_drop hmemD)
  refine ⟨by omega, ?_⟩
  rcases mem_mergeList inner cR ln.live rn.live g yg hmem with h1 | h1 | ⟨c0, h0, hc0⟩
  · refine Or.inr (Or.inr ⟨⟨yg, by rw [KNode.liveAt_of_times ln t hlt]; exact h1⟩, ?_⟩)
    have ha : a ∈ ln.live := by
      cases hl : ln.live with
      | nil => rw [hl] at h1; cases h1
      | cons b bs =>
        unfold mergeList at hal
        rw [hl] at hal
        simp only [List.cons_append, List.cons.injEq] at hal
        rw [← hal.1]; exact List.mem_cons_self
    exact ⟨a.1, a.2, by rw [KNode.liveAt_of_times ln t hlt]; exact ha, hag⟩
  · exact Or.inr (Or.inl ⟨yg, by
      rw [KNode.liveAt_of_times rn t hrt]; exact List.mem_of_mem_tail h1⟩)
  · cases inner
    · simp only [Bool.false_eq_true, ↓reduceIte] at hc0
      exact Or.inr (Or.inl ⟨yg, by
        rw [KNode.liveAt_of_times rn t hrt, hc0]; exact List.mem_of_mem_head? h0⟩)
    · simp only [↓reduceIte] at hc0
      exact Or.inl hc0

end SIS.Tree
