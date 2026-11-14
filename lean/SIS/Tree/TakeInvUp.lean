/-
The upward delete with the take-back keeps the take-back's (B) (bergdb 024-12,
TP4; `TtReachedN`, TakeInvTree.lean). Prover cost's
`writerWP_deleteUpward_upT_get`, here with what becomes of the chain below the
stop node (`writerWP_deleteUpward_upT_getF`): each of its nodes is taken back or
keeps no klong of the transaction's time (`ChainFate`).
-/
import SIS.Tree.TakeInvCollapse
import SIS.Tree.WriterGetUpTake
import SIS.Tree.WriterKindsRules

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- A node of the chain after the upward delete: taken back, or without a klong
of time t. -/
def ChainFate (t : Time) (v : W) (y : NodeId) : Prop :=
  v.taken.contains y = true ∨ ∃ S0, v.nodes.lookup y = some S0 ∧ Klong.time t ∉ S0.ks

theorem chainFate_frame (t : Time) (v v' : W) (y : NodeId) (h : ChainFate t v y)
    (ht : v'.taken = v.taken) (hl : v'.nodes.lookup y = v.nodes.lookup y) : ChainFate t v' y := by
  rcases h with h | ⟨S0, h1, h2⟩
  · left; rw [ht]; exact h
  · right; exact ⟨S0, by rw [hl]; exact h1, h2⟩

theorem retargetOr_wf_times (n S : KNode) (y : NodeId) (t : Time)
    (hS : S = n ∨ ∃ ti dst, S = { n with ks := retargetKlongs n.ks ti y dst })
    (hw : klongsWf n.ks = true) (ht : ∀ s, Klong.time s ∈ n.ks → s ≤ t) :
    klongsWf S.ks = true ∧ ∀ s, Klong.time s ∈ S.ks → s ≤ t := by
  rcases hS with rfl | ⟨ti, dst, rfl⟩
  · exact ⟨hw, ht⟩
  · exact ⟨by rw [klongsWf_retargetKlongs]; exact hw, KNode.retarget_times _ _ _ _ _ ht⟩

/-! ## At node-map level -/

/-- The upward delete at node-map level: a node reached before is reached after,
or is of the chain below the stop node, or no node (a value of the emptied
leaf). The stop node keeps every live klong but the one to the chain, perhaps
moved to another compare value. -/
theorem reach_up (N1 N2 : NodeId → Option KNode) (t : Time) (r : NodeId) (X : Nat → NodeId)
    (Nn : Nat → KNode) (stop depth : Nat) (hsD : stop < depth)
    (hN : ∀ i, stop ≤ i → i ≤ depth → N1 (X i) = some (Nn i))
    (hone : ∀ i, stop < i → i < depth → ∀ c z, (c, z) ∈ (Nn i).liveAt t → z = X (i + 1))
    (hkids : ∀ c z, (c, z) ∈ (Nn depth).liveAt t → N1 z = none)
    (sn' : KNode) (hsn : N2 (X stop) = some sn')
    (hkeep : ∀ c z, (c, z) ∈ (Nn stop).liveAt t → z ≠ X (stop + 1) → ∃ c', (c', z) ∈ sn'.liveAt t)
    (hagree : ∀ u, u ≠ X stop → (∀ k, stop < k → k ≤ depth → u ≠ X k) → N2 u = N1 u) :
    ∀ u, TReach N1 t r u →
      TReach N2 t r u ∨ (∃ k, stop < k ∧ k ≤ depth ∧ u = X k) ∨ N1 u = none := by
  intro u hu
  induction hu with
  | root => exact Or.inl TReach.root
  | @link a c u ha hl ih =>
    obtain ⟨an, han, hau⟩ := hl
    by_cases hac : ∃ k, stop < k ∧ k ≤ depth ∧ a = X k
    · obtain ⟨k, hk1, hk2, hka⟩ := hac
      rw [hka, hN k (by omega) hk2] at han
      cases han
      rcases Nat.lt_or_ge k depth with hkd | hkd
      · exact Or.inr (Or.inl ⟨k + 1, by omega, by omega, hone k hk1 hkd c u hau⟩)
      · have hkd' : k = depth := by omega
        rw [hkd'] at hau
        exact Or.inr (Or.inr (hkids c u hau))
    · have haR : TReach N2 t r a := by
        rcases ih with h | h | h
        · exact h
        · exact absurd h hac
        · rw [han] at h; cases h
      have hnc : ∀ k, stop < k → k ≤ depth → a ≠ X k := fun k h1 h2 he => hac ⟨k, h1, h2, he⟩
      by_cases has : a = X stop
      · rw [has, hN stop (Nat.le_refl _) (by omega)] at han
        cases han
        by_cases hux : u = X (stop + 1)
        · exact Or.inr (Or.inl ⟨stop + 1, by omega, by omega, hux⟩)
        · obtain ⟨c', hc'⟩ := hkeep c u hau hux
          rw [has] at haR
          exact Or.inl (TReach.link haR ⟨sn', hsn, hc'⟩)
      · exact Or.inl (TReach.link haR ⟨an, by rw [hagree a has hnc]; exact han, hau⟩)

/-- (B) after the upward delete, before root collapse: every node of the chain
taken back or without a klong of time t. -/
theorem ttReachedN_up (N1 N2 : NodeId → Option KNode) (t : Time) (r : NodeId) (X : Nat → NodeId)
    (Nn : Nat → KNode) (stop depth : Nat) (hsD : stop < depth)
    (hN : ∀ i, stop ≤ i → i ≤ depth → N1 (X i) = some (Nn i))
    (hone : ∀ i, stop < i → i < depth → ∀ c z, (c, z) ∈ (Nn i).liveAt t → z = X (i + 1))
    (hkids : ∀ c z, (c, z) ∈ (Nn depth).liveAt t → N1 z = none)
    (sn' : KNode) (hsn : N2 (X stop) = some sn')
    (hkeep : ∀ c z, (c, z) ∈ (Nn stop).liveAt t → z ≠ X (stop + 1) → ∃ c', (c', z) ∈ sn'.liveAt t)
    (hagree : ∀ u, u ≠ X stop → (∀ k, stop < k → k ≤ depth → u ≠ X k) → N2 u = N1 u)
    (hXs : ∀ k, stop < k → k ≤ depth → X stop ≠ X k)
    (hstopR : TReach N1 t r (X stop))
    (hfate : ∀ k, stop < k → k ≤ depth → ∀ un, N2 (X k) = some un → Klong.time t ∉ un.ks)
    (hL : TtReachedN N1 t r) : TtReachedN N2 t r := by
  have hR := reach_up N1 N2 t r X Nn stop depth hsD hN hone hkids sn' hsn hkeep hagree
  intro u un hu hm
  by_cases huc : ∃ k, stop < k ∧ k ≤ depth ∧ u = X k
  · obtain ⟨k, h1, h2, hk⟩ := huc
    rw [hk] at hu
    exact absurd hm (hfate k h1 h2 un hu)
  · have hnc : ∀ k, stop < k → k ≤ depth → u ≠ X k := fun k h1 h2 he => huc ⟨k, h1, h2, he⟩
    by_cases hus : u = X stop
    · rw [hus]
      rcases hR (X stop) hstopR with h | h | h
      · exact h
      · obtain ⟨k, h1, h2, he⟩ := h
        exact absurd he (hXs k h1 h2)
      · rw [hN stop (Nat.le_refl _) (by omega)] at h; cases h
    · rw [hagree u hus hnc] at hu
      rcases hR u (hL u un hu hm) with h | h | h
      · exact h
      · exact absurd h huc
      · rw [hu] at h; cases h

/-! ## The upward delete with the take-back -/

/-! ## The emptied leaf's live klongs name values, by the kinds -/

theorem segLen_last_of_keyWf (pre : List Nat) (cv : Nat) (h : keyWf (pre ++ [cv]) = true) :
    segLen cv ≠ 7 := by
  induction pre with
  | nil =>
    simp only [List.nil_append, keyWf, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
    exact h.2
  | cons a pre ih =>
    apply ih
    cases pre with
    | nil =>
      simp only [List.cons_append, List.nil_append, keyWf, Bool.and_eq_true] at h
      simpa [keyWf] using h.2
    | cons b pre' =>
      simp only [List.cons_append, keyWf, Bool.and_eq_true] at h
      simpa [keyWf] using h.2

/-- A value of the kinds is no node of the writer's tree: no cached node is a
value (the books' tags, `ViewKinds`), and the base has none. -/
theorem wNode_val_none (K0 : KindOracle) (B : NodeId) (c : Ctx) (base : View BVal) (w : W)
    (hvk : ViewKinds K0 B c) (hvals : ∀ q ∈ w.vals, B ≤ q.1 ∧ q.1 < w.next ∧ q.1 ∉ w.gh.map (·.1))
    (hb : Book B c w) (hbaseNew : ∀ z, B ≤ z → knodeOf c.p base z = none)
    (hbaseVal : ∀ z, K0.val z → knodeOf c.p base z = none) (z : NodeId) (hz : IsValId K0 w z) :
    wNode c.p base w z = none := by
  have hnot : z ∉ w.nodes.map (·.1) := by
    rw [hb.ids, List.mem_reverse]
    intro hm
    rcases hz with ⟨hh, hzv⟩ | hzv
    · exact (hvals _ hzv).2.2 hm
    · obtain ⟨⟨z', g, h⟩, hq, hz'⟩ := List.mem_map.mp hm
      simp only at hz'
      subst hz'
      rcases hb.tag z' g h hq with ⟨nd, hnd, hd, hl, _, _⟩ | ⟨hBz, _, _⟩
      · exact hvk.notBoth z' _ (hvk.node z' nd hnd hd hl) hzv
      · have := hvk.oldVal z' hzv
        omega
  have hlk : w.nodes.lookup z = none := by
    rw [List.lookup_eq_none_iff]
    intro q hq
    simp only [bne_iff_ne, ne_eq]
    intro hqz
    apply hnot
    exact List.mem_map.mpr ⟨q, hq, hqz.symm⟩
  unfold wNode
  split
  · rfl
  · rw [hlk]
    rcases hz with ⟨hh, hzv⟩ | hzv
    · exact hbaseNew z (hvals _ hzv).1
    · exact hbaseVal z hzv

end SIS.Tree
