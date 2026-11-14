/-
The reading after the merge with a full parent (bergdb 024-22): a node's split
with a last version given as a virtual node and the cascade above it reads as
the tree with the node's content replaced by that version (latest's level
lemmas, `getFromR_timeLevel`, `getFromR_spaceLevel`, with the cascade above
it).
-/
import SIS.Tree.WriterTreeMergeFull
import SIS.Tree.GetCascadeChainG
import SIS.Tree.GetFuel

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- The live klongs of `mergeFullLast` as the merge's reading lemmas take them
(`getFromR_mergeOne`, `getFromR_mergeTwo`). -/
theorem mergeFullLast_iff (pn : KNode) (t : Time) (cL : Nat) (m1 : NodeId) (cR : Nat)
    (m2 : Option (NodeId × Nat)) (last : KNode) (h : mergeFullLast pn t cL m1 cR m2 = some last)
    (hpt : ∀ s, Klong.time s ∈ pn.ks → s ≤ t) :
    (m2 = none → ∀ cc z, (cc, z) ∈ last.liveAt t ↔
      (cc = cL ∧ z = m1) ∨ ((cc, z) ∈ pn.liveAt t ∧ cc ≠ cL ∧ cc ≠ cR)) ∧
    (∀ y g, m2 = some (y, g) → ∀ cc z, (cc, z) ∈ last.liveAt t ↔
      (cc = g ∧ z = y) ∨ (cc ≠ g ∧ cc = cL ∧ z = m1) ∨
        (cc ≠ g ∧ cc ≠ cL ∧ cc ≠ cR ∧ (cc, z) ∈ pn.liveAt t)) := by
  obtain ⟨pairs, hks⟩ := mergeFullLast_ks pn t cL m1 cR m2 last h
  have htl : ∀ s, Klong.time s ∈ last.ks → s ≤ t := by rw [hks]; exact newKlongs_times t pairs
  obtain ⟨_, hnone, hsome⟩ := mergeFullLast_lookup pn t cL m1 cR m2 last h
  have hl : ∀ cc z, (cc, z) ∈ last.liveAt t ↔ last.live.lookup cc = some z := by
    intro cc z
    rw [KNode.liveAt_of_times last t htl]
    exact ⟨lookup_of_mem_nodup _ (KNode.live_keys_nodup last) cc z, mem_of_lookup_nodup _ cc z⟩
  have hp : ∀ cc z, (cc, z) ∈ pn.liveAt t ↔ pn.live.lookup cc = some z := by
    intro cc z
    rw [KNode.liveAt_of_times pn t hpt]
    exact ⟨lookup_of_mem_nodup _ (KNode.live_keys_nodup pn) cc z, mem_of_lookup_nodup _ cc z⟩
  refine ⟨fun h0 cc z => ?_, fun y g hy cc z => ?_⟩
  · rw [hl, hnone h0 cc, hp]
    by_cases h1 : cc = cL
    · rw [ite_eq_left_of_eq_true _ _ (eq_true h1)]
      constructor
      · intro he; exact Or.inl ⟨h1, (Option.some.inj he).symm⟩
      · rintro (⟨_, rfl⟩ | ⟨_, h2, _⟩)
        · rfl
        · exact absurd h1 h2
    · rw [ite_eq_right_of_eq_false _ _ (eq_false h1)]
      by_cases h2 : cc = cR
      · rw [ite_eq_left_of_eq_true _ _ (eq_true h2)]
        constructor
        · intro he; cases he
        · rintro (⟨h, _⟩ | ⟨_, _, h⟩)
          · exact absurd h h1
          · exact absurd h2 h
      · rw [ite_eq_right_of_eq_false _ _ (eq_false h2)]
        constructor
        · intro he; exact Or.inr ⟨he, h1, h2⟩
        · rintro (⟨h, _⟩ | ⟨he, _, _⟩)
          · exact absurd h h1
          · exact he
  · rw [hl, hsome y g hy cc, hp]
    by_cases h0 : cc = g
    · rw [ite_eq_left_of_eq_true _ _ (eq_true h0)]
      constructor
      · intro he; exact Or.inl ⟨h0, (Option.some.inj he).symm⟩
      · rintro (⟨_, rfl⟩ | ⟨h, _⟩ | ⟨h, _⟩)
        · rfl
        · exact absurd h0 h
        · exact absurd h0 h
    · rw [ite_eq_right_of_eq_false _ _ (eq_false h0)]
      by_cases h1 : cc = cL
      · rw [ite_eq_left_of_eq_true _ _ (eq_true h1)]
        constructor
        · intro he; exact Or.inr (Or.inl ⟨h0, h1, (Option.some.inj he).symm⟩)
        · rintro (⟨h, _⟩ | ⟨_, _, rfl⟩ | ⟨_, h, _⟩)
          · exact absurd h h0
          · rfl
          · exact absurd h1 h
      · rw [ite_eq_right_of_eq_false _ _ (eq_false h1)]
        by_cases h2 : cc = cR
        · rw [ite_eq_left_of_eq_true _ _ (eq_true h2)]
          constructor
          · intro he; cases he
          · rintro (⟨h, _⟩ | ⟨_, h, _⟩ | ⟨_, _, h, _⟩)
            · exact absurd h h0
            · exact absurd h h1
            · exact absurd h2 h
        · rw [ite_eq_right_of_eq_false _ _ (eq_false h2)]
          constructor
          · intro he; exact Or.inr (Or.inr ⟨h0, h1, h2, he⟩)
          · rintro (⟨h, _⟩ | ⟨_, h, _⟩ | ⟨_, _, _, he⟩)
            · exact absurd h h0
            · exact absurd h h1
            · exact he

end SIS.Tree
