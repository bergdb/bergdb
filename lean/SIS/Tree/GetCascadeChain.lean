import SIS.Tree.GetCascadeGen
import SIS.Tree.WriterTreeCascadeGen2

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-! Splits of any depth (bergdb 024-12, TP10): the reading after
`appendKlongs` along a chain of the access path, as cost's
`writerWP_appendKlongs_chain` states the tree after it: the writer's state
reads as the state with the klongs put in the chain's node (the virtual map). -/

/-- The halves of a leaf's last version with klongs put on one side of its
divider find, below the divider and from it on, what the leaf with the klongs
found. -/
theorem halves_leaf_searchEq_ins (n Q : KNode) (t : Time) (ins : List (Nat × NodeId))
    (hnl : n.leaf = true)
    (r : Nat × NodeId) (hr : (n.live.drop (n.live.length / 2)).head? = some r)
    (hside : (∀ q ∈ ins, r.1 ≤ q.1) ∨ (∀ q ∈ ins, q.1 < r.1))
    (hQwf : klongsWf Q.ks = true) (hQt : ∀ s, Klong.time s ∈ Q.ks → s ≤ t)
    (hQlook : ∀ c, Q.live.lookup c = ins.foldl (pairLookupStep c) (n.live.lookup c)) :
    let out := halves n.leaf t (n.lastVersion t) ins
    out.2.2 = r.1 ∧ out.1.leaf = true ∧ out.2.1.leaf = true ∧
      klongsWf out.1.ks = true ∧ klongsWf out.2.1.ks = true ∧
      (∀ s, Klong.time s ∈ out.1.ks → s ≤ t) ∧ (∀ s, Klong.time s ∈ out.2.1.ks → s ≤ t) ∧
      (∀ c : Nat, c < r.1 → (out.1.searchEq t c).map (·.y) = (Q.searchEq t c).map (·.y)) ∧
      (∀ c : Nat, r.1 ≤ c → (out.2.1.searchEq t c).map (·.y) = (Q.searchEq t c).map (·.y)) := by
  intro out
  have hlv := KNode.lastVersion_eq_newKlongs n t
  rw [hnl] at hlv
  have hout : out = halves true t ⟨true, newKlongs t n.live⟩ ins := by
    simp only [out, hnl, hlv]
  have hs : CvSorted n.live := n.live_order
  have hside' : ∀ q ∈ ins, decide (r.1 ≤ q.1) =
      (match ins.head? with | some a => decide (r.1 ≤ a.1) | none => false) := by
    intro q hq
    cases hins : ins with
    | nil => rw [hins] at hq; cases hq
    | cons a rest =>
      rw [hins] at hq hside
      simp only [List.head?_cons]
      rcases hside with h | h
      · simp [h q hq, h a List.mem_cons_self]
      · have h1 := h q hq
        have h2 := h a List.mem_cons_self
        simp only [decide_eq_decide]
        omega
  have hlook := halves_leaf_lookup t n.live ins hs r hr hside'
  have hshape := halves_leaf_shape t n.live ins r hr
  rw [← hout] at hshape hlook
  simp only at hlook
  have hwfh := halves_newKlongs_wf true t n.live ins
  rw [← hout] at hwfh
  have hbasic : out.2.2 = r.1 ∧ out.1.leaf = true ∧ out.2.1.leaf = true ∧
      (∀ s, Klong.time s ∈ out.1.ks → s ≤ t) ∧ (∀ s, Klong.time s ∈ out.2.1.ks → s ≤ t) := by
    rw [hshape]
    split <;> (try split) <;> exact ⟨rfl, rfl, rfl, newKlongs_times t _, newKlongs_times t _⟩
  obtain ⟨hsc, hl1, hl2, ht1, ht2⟩ := hbasic
  refine ⟨hsc, hl1, hl2, hwfh.1, hwfh.2, ht1, ht2, ?_, ?_⟩
  · intro c hc
    have h := hlook c
    rw [hsc] at h
    simp only [hc, ↓reduceIte] at h
    rw [KNode.searchEq_live _ t hwfh.1 ht1, KNode.searchEq_live _ t hQwf hQt, h, hQlook]
  · intro c hc
    have h := hlook c
    rw [hsc] at h
    simp only [show ¬ c < r.1 by omega, ↓reduceIte] at h
    rw [KNode.searchEq_live _ t hwfh.2 ht2, KNode.searchEq_live _ t hQwf hQt, h, hQlook]

theorem KNode.addKeys_leaf (t : Time) :
    ∀ (ins : List (Nat × NodeId)) (n : KNode),
      (ins.foldl (fun n (cv, y) => n.add t (.key cv y)) n).leaf = n.leaf := by
  intro ins
  induction ins with
  | nil => intro n; rfl
  | cons a rest ih =>
    intro n
    simp only [List.foldl_cons]
    rw [ih, KNode.add_leaf]

/-- `getFromR_updN_unreach` with cost's `updN`. -/
theorem getFromR_updN_unreach' (M : NodeId → Option KNode) (V : NodeId → Option Nat) (t : Time)
    (fuel : Nat) (r x : NodeId) (m : KNode)
    (hwf : ∀ z zn, ReachS M t r z → M z = some zn → klongsWf zn.ks = true)
    (hx : ¬ ReachS M t r x) :
    ∀ key, getFromR (updN M x m) V t fuel key r = getFromR M V t fuel key r :=
  getFromR_updN_unreach M V t fuel r x m hwf hx

end SIS.Tree
