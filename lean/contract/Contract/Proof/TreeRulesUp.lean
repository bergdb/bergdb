/-
The contract package (bergdb 030-16): a rule of the delete as statements
about two trees, A before and B after, as TreeRules.lean has the put's.

* `Sound.collapse`: root collapse. An inner space root with one live klong is
  replaced by the node that klong names: the tree from that node is sound and
  holds the same keys, and the old root is not reached from it.
-/
import Contract.Proof.TreeRulesDel

namespace Contract

/-- Root collapse: the space root r, an inner node with the one live klong
(c, y), is replaced by y. -/
theorem Sound.collapse {M : Nat} {A : Tree} {r y : NodeId} {C : List (Key × Nat)} {nr : KNode}
    {c : Nat} (h : Sound M none A r C) (hAr : A.obj r = some (.key nr)) (hrl : nr.leaf = false)
    (hlive : live nr.ks = [(c, y)]) :
    Sound M none A y C ∧ r ∉ reachAt A (A.fuel y) y ∧
      ∀ z ∈ reachAt A (A.fuel y) y, z ∈ reachAt A (A.fuel r) r := by
  have hfr : A.fuel r = nr.level + 1 := by simp [Tree.fuel, hAr]
  have hm : (c, y) ∈ live nr.ks := by rw [hlive]; simp
  have hG := h.good
  have hkeq := hG.tc_kid_eq hAr hm
  have hsub : ∀ z ∈ reachAt A (A.fuel y) y, z ∈ reachAt A (A.fuel r) r := by
    intro z hz
    rw [hfr]
    exact tc_kid hAr hm (hkeq ▸ hz)
  obtain ⟨m, hm1, -, hm3⟩ : ∃ m, A.obj y = some (.key m) ∧ m.level < nr.level ∧
      live m.ks ≠ [] := by
    rcases hG.kind hAr hm with ⟨hl, _, _⟩ | ⟨_, m, _, _, hm1, hm2, hm3, _⟩
    · rw [hrl] at hl
      cases hl
    · exact ⟨m, hm1, hm2, hm3⟩
  have hGy : Good A y 0 none := by
    cases hG with
    | mk _ _ _ n' hobj' _ _ _ _ _ _ hkid =>
      rw [hAr] at hobj'
      obtain rfl : nr = n' := by injection hobj' with h1; injection h1
      exact (hkid hrl [] c y [] (by rw [hlive]; rfl)).widen (Nat.zero_le _) (fun _ h => h)
  refine ⟨⟨⟨m, hm1, Or.inr hm3⟩, hGy, ?_, ?_, ?_⟩, hG.not_below hAr hm _, hsub⟩
  · intro z hz m' hm'
    simpa using h.nodes z (hsub z hz) m' hm'
  · rw [← h.holds, hG.L_eq hAr, hlive]
    simp [klongList, hrl]
  · have ht := h.tree
    rw [hfr, tc_key hAr, hlive] at ht
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil] at ht
    rw [← hkeq]
    exact (List.nodup_cons.mp ht).2

end Contract
