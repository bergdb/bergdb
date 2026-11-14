/-
The cascade of splits keeps `LiveEdges` (bergdb 024-12, TP7, toward `QLive` of
the put into a full leaf): the counts the steps of `LiveSteps.lean` need, from
the writer's nodes. Here: the helper facts. A node keeps its kind and gains no
fewer live klongs when klongs are put in (`addKeys_liveAt_length`). A time
split's last version has the live klongs of the node with the klongs put
(`timeSplit_liveAt_length`). A space split's halves are `HalfOK`
(`halves_halfOK`). A new root has two live klongs (`newRoot_liveAt_two`). A
repointed klong keeps the count (`repoint_liveAt_length`).
-/
import SIS.Tree.LiveSteps
import SIS.Tree.SplitLiveFill

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

theorem addKeys_leaf (t : Time) : ∀ (ins : List (Nat × NodeId)) (n : KNode),
    (ins.foldl (fun n (cv, y) => n.add t (.key cv y)) n).leaf = n.leaf := by
  intro ins
  induction ins with
  | nil => intro n; rfl
  | cons q rest ih =>
    intro n
    simp only [List.foldl_cons]
    rw [ih, KNode.add_leaf]

/-- No fewer live klongs at t in B than in A, when every live compare value of A
is live in B. -/
theorem liveAt_length_le (A B : KNode) (t : Time)
    (h : ∀ c z, (c, z) ∈ A.liveAt t → ∃ z', (c, z') ∈ B.liveAt t) :
    (A.liveAt t).length ≤ (B.liveAt t).length := by
  have hsub : ∀ c ∈ (A.liveAt t).map Prod.fst, c ∈ (B.liveAt t).map Prod.fst := by
    intro c hc
    obtain ⟨⟨c', z⟩, hm, hcc⟩ := List.mem_map.mp hc
    simp only at hcc
    subst hcc
    obtain ⟨z', hz'⟩ := h c' z hm
    exact List.mem_map.mpr ⟨(c', z'), hz', rfl⟩
  have := (KNode.liveAt_keys_nodup A t).length_le_of_subset hsub
  simpa using this

theorem pairLookupFold_some (c : Nat) : ∀ (ins : List (Nat × NodeId)) (z : NodeId),
    ∃ z', ins.foldl (pairLookupStep c) (some z) = some z' := by
  intro ins
  induction ins with
  | nil => intro z; exact ⟨z, rfl⟩
  | cons q rest ih =>
    intro z
    simp only [List.foldl_cons, pairLookupStep]
    split
    · exact ih _
    · exact ih z

/-- Klongs put in at t lose no live klong. -/
theorem addKeys_liveAt_length (t : Time) (ins : List (Nat × NodeId)) (n : KNode)
    (hw : klongsWf n.ks = true) (ht : ∀ s, Klong.time s ∈ n.ks → s ≤ t) :
    (n.liveAt t).length ≤ ((ins.foldl (fun n (cv, y) => n.add t (.key cv y)) n).liveAt t).length := by
  apply liveAt_length_le
  intro c z hc
  have hl : n.live.lookup c = some z := by
    rw [KNode.liveAt_of_times n t ht] at hc
    exact lookup_of_mem_nodup _ (KNode.live_keys_nodup n) c z hc
  obtain ⟨z', hz'⟩ := pairLookupFold_some c ins z
  rw [← hl] at hz'
  exact ⟨z', KNode.addKeys_liveAt_of_fold t ins n hw ht c z' hz'⟩

/-- A time split's last version l (its live lookups those of the node with the
klongs put) has the live klongs of the node with the klongs put. -/
theorem timeSplit_liveAt_length (t : Time) (ins : List (Nat × NodeId)) (n l : KNode) (leaf : Bool)
    (hw : klongsWf n.ks = true) (ht : ∀ s, Klong.time s ∈ n.ks → s ≤ t)
    (hl_times : ∀ s, Klong.time s ∈ l.ks → s ≤ t)
    (hl_look : ∀ q, l.live.lookup q = ins.foldl (pairLookupStep q) (n.live.lookup q)) :
    ((ins.foldl (fun n (cv, y) => n.add t (.key cv y)) n).liveAt t).length ≤
      ((⟨leaf, l.ks⟩ : KNode).liveAt t).length := by
  apply liveAt_length_le
  intro c z hc
  have hf := KNode.addKeys_liveAt_fold t ins n hw ht c z hc
  rw [← hl_look c] at hf
  refine ⟨z, ?_⟩
  rw [KNode.liveAt_of_times (⟨leaf, l.ks⟩ : KNode) t hl_times]
  exact lookup_some_mem hf

/-- A space split's halves have m live klongs and more, so they are `HalfOK`
with the merges' thresholds. -/
theorem halves_halfOK (p : Params) (hp : MergeParamsOK p) (n : KNode) (t : Time)
    (ins : List (Nat × NodeId)) (hfull : p.splitAbove < (n.lastVersion t).size) :
    HalfOK p t (halves n.leaf t (n.lastVersion t) ins).1 ∧
      HalfOK p t (halves n.leaf t (n.lastVersion t) ins).2.1 := by
  obtain ⟨h1, h2⟩ := halves_lastVersionGivenDel_live_fill p hp n t n.lastBitmap ins hfull
  obtain ⟨ht1, ht2⟩ := halves_times n.leaf n t ins
  have hm : 2 ≤ p.mergeBelow := hp.1
  have hc1 : p.mergeBelow ≤ ((halves n.leaf t (n.lastVersion t) ins).1.liveAt t).length := by
    rw [KNode.liveAt_of_times _ t ht1]; exact h1
  have hc2 : p.mergeBelow ≤ ((halves n.leaf t (n.lastVersion t) ins).2.1.liveAt t).length := by
    rw [KNode.liveAt_of_times _ t ht2]; exact h2
  refine ⟨⟨fun hE => ?_, by omega, fun _ => hc1⟩, ⟨fun hE => ?_, by omega, fun _ => hc2⟩⟩
  · rw [hE] at hc1; simp at hc1; omega
  · rw [hE] at hc2; simp at hc2; omega

/-- Two different members make a list of two at least. -/
theorem two_le_length_of_mem {α : Type} (l : List α) (a b : α) (ha : a ∈ l) (hb : b ∈ l)
    (hab : a ≠ b) : 2 ≤ l.length := by
  match l, ha, hb with
  | [], ha, _ => cases ha
  | [x], ha, hb =>
    simp only [List.mem_singleton] at ha hb
    exact absurd (ha.trans hb.symm) hab
  | _ :: _ :: _, _, _ => simp

/-- A new root over two nodes has two live klongs. -/
theorem newRoot_liveAt_two (t : Time) (a b : NodeId) (sc : Nat) (hsc : 0 < sc) :
    2 ≤ ((⟨false, [.time t, .key 0 a, .key sc b]⟩ : KNode).liveAt t).length := by
  have hnd : ([(0, a), (sc, b)].map Prod.fst).Nodup := by
    simp only [List.map_cons, List.map_nil, List.nodup_cons, List.mem_cons,
      List.not_mem_nil, or_false, List.nodup_nil, and_true, not_false_eq_true]
    omega
  have h1 := (mrg_newKlongs_liveAt_iff false t [(0, a), (sc, b)] hnd 0 a).mpr (by simp)
  have h2 := (mrg_newKlongs_liveAt_iff false t [(0, a), (sc, b)] hnd sc b).mpr (by simp)
  exact two_le_length_of_mem _ _ _ h1 h2 (by intro h; simp only [Prod.mk.injEq] at h; omega)

theorem liveAt_repoint_new (n : KNode) (x y : NodeId) (k j : Nat) (t : Time)
    (hj : n.linkIndex x k = some j) (ht : ∀ s, Klong.time s ∈ n.ks → s ≤ t) :
    (k, y) ∈ (n.repoint j y).liveAt t := by
  rw [KNode.liveAt_of_times _ t (KNode.repoint_times n j y t ht)]
  apply bk_mem_of_lookup
  rw [KNode.repoint_live_lookup n x y k j hj k]
  simp

theorem liveAt_repoint_keep (n : KNode) (x y : NodeId) (k j : Nat) (t : Time)
    (hj : n.linkIndex x k = some j) (ht : ∀ s, Klong.time s ∈ n.ks → s ≤ t) (c : Nat) (z : NodeId)
    (hz : (c, z) ∈ n.liveAt t) (hck : c ≠ k) : (c, z) ∈ (n.repoint j y).liveAt t := by
  rw [KNode.liveAt_of_times _ t (KNode.repoint_times n j y t ht)]
  rw [KNode.liveAt_of_times n t ht] at hz
  apply bk_mem_of_lookup
  rw [KNode.repoint_live_lookup n x y k j hj c]
  have hb : (k == c) = false := by simpa using Ne.symm hck
  simp only [hb, Bool.false_eq_true, ↓reduceIte]
  exact lookup_of_mem_nodup _ (KNode.live_keys_nodup n) c z hz

/-- A repointed klong keeps the live klongs' count. -/
theorem repoint_liveAt_length (n : KNode) (x y : NodeId) (k j : Nat) (t : Time)
    (hj : n.linkIndex x k = some j) (ht : ∀ s, Klong.time s ∈ n.ks → s ≤ t) :
    (n.liveAt t).length ≤ ((n.repoint j y).liveAt t).length := by
  apply liveAt_length_le
  intro c z hc
  by_cases hck : c = k
  · subst hck; exact ⟨y, liveAt_repoint_new n x y c j t hj ht⟩
  · exact ⟨z, liveAt_repoint_keep n x y k j t hj ht c z hc hck⟩

end SIS.Tree
