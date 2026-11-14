import SIS.Tree.GetSpaceSplit

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-! A put into a full leaf that the transaction made (bergdb 024-12, TP10;
`OpGetOK`'s rules): with at most h klongs in its last version, or full by its
dead klongs only, a time split in place: the leaf becomes its last version with
the put's klong, and the parent is not changed. -/

/-! ## A space split in place below an inner parent with room -/

theorem KNode.searchLte_congr (n1 n2 : KNode) (t : Time) (h1 : ∀ s, Klong.time s ∈ n1.ks → s ≤ t)
    (h2 : ∀ s, Klong.time s ∈ n2.ks → s ≤ t) (hl : ∀ c', n1.live.lookup c' = n2.live.lookup c')
    (c : Int) : (n1.searchLte t c).map (·.y) = (n2.searchLte t c).map (·.y) := by
  have hmem : ∀ a y, (a, y) ∈ n1.live ↔ (a, y) ∈ n2.live := by
    intro a y
    rw [mem_iff_lookup _ (KNode.live_keys_nodup n1), mem_iff_lookup _ (KNode.live_keys_nodup n2), hl]
  have hs1 := n1.searchLte_spec t c
  unfold NodeSearchSpec at hs1
  rw [KNode.liveAt_of_times n1 t h1] at hs1
  cases hf : n1.searchLte t c with
  | none =>
    have hall := hs1.2.mp hf
    rw [KNode.searchLte_none_of n2 t h2 c (fun q hq => by
      have := hall q ((hmem q.1 q.2).mpr hq)
      simp only [decide_eq_false_iff_not] at this
      omega)]
  | some f =>
    obtain ⟨hfm, hfa, hfmax⟩ := hs1.1 f hf
    simp only [decide_eq_true_eq] at hfa
    rw [KNode.searchLte_of_max n2 t h2 c f.c f.y ((hmem _ _).mp hfm) hfa (fun q hq hqc => by
      have := hfmax q ((hmem q.1 q.2).mpr hq) (by simpa using hqc)
      simpa using this)]
    rfl

/-- The parent after a space split in place of its child L: a klong at sc names
the second half S. A search that found its klong k1 to L finds L below sc and S
from sc on; any other search finds what it found. -/
theorem KNode.splitParentInPlace_searchLte (n : KNode) (t : Time) (k1 sc : Nat) (L S : NodeId)
    (hw : klongsWf n.ks = true) (ht : ∀ s, Klong.time s ∈ n.ks → s ≤ t)
    (hk1 : (k1, L) ∈ n.live) (hle : k1 ≤ sc)
    (hgap : ∀ c' z, (c', z) ∈ n.live → c' ≤ k1 ∨ sc < c') (c : Int) :
    ((n.add t (.key sc S)).searchLte t c).map (·.y) =
      (n.searchLte t c).map (fun fd => if fd.c = k1 then (if c < sc then L else S) else fd.y) := by
  rw [← KNode.splitParent_searchLte n t k1 sc L L S hw ht hk1 hle hgap c]
  have hw1 := KNode.add_key_wf n t k1 L hw
  have ht1 := KNode.add_times n t (.key k1 L) (fun s h => by cases h) ht
  apply KNode.searchLte_congr _ _ t (KNode.add_times n t (.key sc S) (fun s h => by cases h) ht)
    (KNode.add_times _ t (.key sc S) (fun s h => by cases h) ht1)
  intro c'
  rw [KNode.add_key_live_lookup_of_wf n t sc c' S hw, KNode.add_key_live_lookup_of_wf _ t sc c' S hw1,
    KNode.add_key_live_lookup_of_wf n t k1 c' L hw]
  by_cases h1 : sc = c'
  · simp [h1]
  · have h1' : (sc == c') = false := by simpa using h1
    simp only [h1', Bool.false_eq_true, ↓reduceIte]
    by_cases h2 : k1 = c'
    · subst h2
      simp only [beq_self_eq_true, ↓reduceIte]
      exact lookup_some_of_mem (KNode.live_keys_nodup n) hk1
    · have h2' : (k1 == c') = false := by simpa using h2
      simp only [h2', Bool.false_eq_true, ↓reduceIte]

end SIS.Tree
