/-
The take-back's (C) and node facts through a cascade, against latest's shape of
every node after it (bergdb 024-12; `CascadeNodeShape`, ChainShape.lean): a
chain node unchanged, left behind, a node of time t whose shadowed klongs name
old nodes or values, or the node where the cascade ends, at any level j (key
klongs added, or a segment leaf's klong to a segment root made by the
transaction repointed). `CascadeShapeJ2` is that shape in the form (C) needs,
`j2rest_cascade2` the node-map lemma.
-/
import SIS.Tree.TakeDeadAssembly2
import SIS.Tree.ChainShape

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- A node changed or made by a cascade along X s .. X D, in the form (C)
needs. -/
def CascadeShapeJ2 (N : NodeId → Option KNode) (t : Time) (B : NodeId) (vals : List NodeId)
    (X : Nat → NodeId) (Nn : Nat → KNode) (s D : Nat) (z : NodeId) (zn : KNode) : Prop :=
  (∃ i, s ≤ i ∧ i ≤ D ∧ z = X i ∧ zn = Nn i) ∨
  (∃ i, s ≤ i ∧ i ≤ D ∧ z = X i ∧ (Nn i).firstTime ≠ some t ∧ zn = (Nn i).toPrev (t - 1)) ∨
  (ShadowShaped t B vals zn ∧ B ≤ z) ∨
  (∃ j, s ≤ j ∧ j ≤ D ∧ z = X j ∧
    ((∃ ins : List (Nat × NodeId),
      zn = ins.foldl (fun n (cv, y) => n.add t (.key cv y)) (Nn j) ∧ (ins.map Prod.fst).Nodup ∧
      (∀ q ∈ ins, ∀ z', (q.1, z') ∈ (Nn j).liveAt t → z' < B ∨ z' ∈ vals)) ∨
    (∃ (idx k : Nat) (x y : NodeId) (xn : KNode), (Nn j).linkIndex x k = some idx ∧
      (k, x) ∈ (Nn j).liveAt t ∧ B ≤ x ∧ N x = some xn ∧ (Nn j).leaf = true ∧
      zn = (Nn j).repoint idx y)))

/-- (C) and the node facts after a cascade whose changed and made nodes have
`CascadeShapeJ2`, the others below nx as before. -/
theorem j2rest_cascade2 (N N' : NodeId → Option KNode) (t : Time) (r B : NodeId)
    (vals : List NodeId) (X : Nat → NodeId) (Nn : Nat → KNode) (s D : Nat) (nx : NodeId)
    (hpos : 0 < t) (hT : TreeOK N t r) (hD : DeadLiveN N t B vals) (hO : OldBelowN N t B)
    (hS : OldStartN N t B) (hM : MadeStartN N t B) (hV : ValsNoNodeN N vals)
    (hN : ∀ i, s ≤ i → i ≤ D → N (X i) = some (Nn i))
    (hwf : ∀ i, s ≤ i → i ≤ D → klongsWf (Nn i).ks = true)
    (hts : ∀ i, s ≤ i → i ≤ D → ∀ u, Klong.time u ∈ (Nn i).ks → u ≤ t)
    (hR : ∀ i, s ≤ i → i ≤ D → TReach N t r (X i)) (hvnx : ∀ y ∈ vals, y < nx)
    (hother : ∀ z, z < nx → (∀ i, s ≤ i → i ≤ D → z ≠ X i) → N' z = N z)
    (hshape : ∀ z zn, N' z = some zn → (nx ≤ z ∨ ∃ i, s ≤ i ∧ i ≤ D ∧ z = X i) →
      CascadeShapeJ2 N t B vals X Nn s D z zn) :
    DeadLiveN N' t B vals ∧ OldBelowN N' t B ∧ OldStartN N' t B ∧ MadeStartN N' t B ∧
      ValsNoNodeN N' vals := by
  have hold : ∀ u un, N u = some un →
      DeadLiveK un t B vals ∧ (∀ cv y, Klong.key cv y ∈ prefixAt un.ks (t - 1) → y < B) ∧
      (u < B → ∃ s', s' < t ∧ un.firstTime = some s') ∧ (B ≤ u → un.firstTime = some t) :=
    fun u un hu => ⟨deadLiveK_of_N N t B vals hD _ _ hu, fun cv y hk => hO _ _ hu cv y hk,
      fun h => hS _ _ hu h, fun h => hM _ _ hu h⟩
  have hnode : ∀ u un, N' u = some un →
      DeadLiveK un t B vals ∧ (∀ cv y, Klong.key cv y ∈ prefixAt un.ks (t - 1) → y < B) ∧
      (u < B → ∃ s', s' < t ∧ un.firstTime = some s') ∧ (B ≤ u → un.firstTime = some t) := by
    intro u un hu
    by_cases hc : nx ≤ u ∨ ∃ i, s ≤ i ∧ i ≤ D ∧ u = X i
    · rcases hshape u un hu hc with ⟨i, h1, h2, rfl, rfl⟩ | ⟨i, h1, h2, rfl, hf, rfl⟩ | ⟨hls, hBu⟩ |
          ⟨j, h1, h2, rfl, hadd | hrep⟩
      · exact hold _ _ (hN i h1 h2)
      · have hNi := hN i h1 h2
        have hiB := lt_of_firstTime_ne N t B hM _ _ hNi hf
        refine ⟨fun i' cv y hi hB _ => ?_, fun cv y hk => ?_, fun _ => ?_, fun h => absurd h (by omega)⟩
        · have hm : Klong.key cv y ∈ prefixAt (Nn i).ks (t - 1) := List.mem_of_getElem? hi
          have := hO _ _ hNi cv y hm
          omega
        · simp only [KNode.toPrev] at hk
          rw [prefixAt_idem] at hk
          exact hO _ _ hNi cv y hk
        · obtain ⟨s', hs', hf'⟩ := hS _ _ hNi hiB
          exact ⟨s', hs', KNode.firstTime_toPrev _ _ s' hf' (by omega)⟩
      · obtain ⟨hDK, hpre, hft⟩ := shadowShaped_facts t B vals un hls hpos
        refine ⟨hDK, fun cv y hk => (by rw [hpre] at hk; cases hk), fun h => absurd h (by omega),
          fun _ => hft⟩
      · have hNj := hN j h1 h2
        have hDj : DeadLiveK (Nn j) t B vals := deadLiveK_of_N N t B vals hD _ _ hNj
        obtain ⟨ins, rfl, hnd, hins⟩ := hadd
        obtain ⟨hDK, hpre, hft⟩ := addKeys_facts t B vals hpos ins (Nn j) (hwf j h1 h2) (hts j h1 h2)
          hDj hnd hins
        refine ⟨hDK, fun cv y hk => by rw [hpre] at hk; exact hO _ _ hNj cv y hk, fun h => ?_,
          fun h => hft t (hM _ _ hNj h)⟩
        obtain ⟨s', hs', hf'⟩ := hS _ _ hNj h
        exact ⟨s', hs', hft s' hf'⟩
      · have hNj := hN j h1 h2
        have hDj : DeadLiveK (Nn j) t B vals := deadLiveK_of_N N t B vals hD _ _ hNj
        obtain ⟨idx, k, x, y, xn, hj, hk, hBx, hxn, hleaf, rfl⟩ := hrep
        have hxv : x ∉ vals := fun h => by rw [hV x h] at hxn; cases hxn
        have hDK := deadLiveK_repoint N t r B vals (X j) x y (Nn j) k idx hT hDj (hR j h1 h2) hNj hleaf
          (hts j h1 h2) hj hk hBx hxv
        have hjk : (Nn j).ks[idx]? = some (.key k x) := kd_linkIndex_some (Nn j) x k idx hj
        have hjp : (prefixAt (Nn j).ks (t - 1)).length ≤ idx := by
          rcases Nat.lt_or_ge idx (prefixAt (Nn j).ks (t - 1)).length with h | h
          · have hm := mem_prefixAt_of_lt (Nn j).ks (t - 1) idx _ h hjk
            have := hO _ _ hNj k x hm
            omega
          · exact h
        have hpre : prefixAt ((Nn j).repoint idx y).ks (t - 1) = prefixAt (Nn j).ks (t - 1) := by
          unfold KNode.repoint
          rw [hjk]
          exact prefixAt_set_late (Nn j).ks (t - 1) idx k y hjp (fun k0 hk0 => by
            rw [hjk] at hk0; cases hk0; exact ⟨k, x, rfl⟩)
        refine ⟨hDK, fun cv y' hk' => by rw [hpre] at hk'; exact hO _ _ hNj cv y' hk', fun h => ?_,
          fun h => by rw [KNode.firstTime_repoint]; exact hM _ _ hNj h⟩
        obtain ⟨s', hs', hf'⟩ := hS _ _ hNj h
        exact ⟨s', hs', by rw [KNode.firstTime_repoint]; exact hf'⟩
    · have hlt : u < nx := by
        rcases Nat.lt_or_ge u nx with h | h
        · exact h
        · exact absurd (Or.inl h) hc
      rw [hother u hlt (fun i h1 h2 he => hc (Or.inr ⟨i, h1, h2, he⟩))] at hu
      exact hold u un hu
  refine ⟨fun u un hu => (hnode u un hu).1, fun u un hu => (hnode u un hu).2.1,
    fun u un hu h => (hnode u un hu).2.2.1 h, fun u un hu h => (hnode u un hu).2.2.2 h, ?_⟩
  intro y hy
  have hyn := hvnx y hy
  by_cases hc : ∃ i, s ≤ i ∧ i ≤ D ∧ y = X i
  · obtain ⟨i, h1, h2, rfl⟩ := hc
    have := hV _ hy
    rw [hN i h1 h2] at this; cases this
  · rw [hother y hyn (fun i h1 h2 he => hc ⟨i, h1, h2, he⟩)]
    exact hV y hy

/-- The klong that `linkIndex` finds is live. -/
theorem liveAt_of_linkIndex (n : KNode) (t : Time) (x : NodeId) (k j : Nat)
    (hj : n.linkIndex x k = some j) (ht : ∀ s, Klong.time s ∈ n.ks → s ≤ t) :
    (k, x) ∈ n.liveAt t := by
  obtain ⟨pre, post, hks, hlen, hpost, hdel⟩ := KNode.linkIndex_split n x k j hj
  have hjk : n.ks[j]? = some (.key k x) := by
    rw [hks, List.getElem?_append_right (by omega), hlen, Nat.sub_self]; rfl
  apply liveAt_of_lastLive n t ht j k x hjk
  refine ⟨⟨x, hjk⟩, by simpa using hdel, fun j' y' hjj hj' => ?_⟩
  exfalso
  rw [hks, List.getElem?_append_right (by omega)] at hj'
  have h1 : j' - pre.length ≠ 0 := by omega
  obtain ⟨m, hm⟩ : ∃ m, j' - pre.length = m + 1 := ⟨j' - pre.length - 1, by omega⟩
  rw [hm, List.getElem?_cons_succ] at hj'
  exact hpost _ (List.mem_of_getElem? hj') y' rfl

/-- latest's shape of a node after a cascade in the form (C) needs, given that a
chain node left behind is not one the transaction made and a repointed top is a
segment leaf. -/
theorem cascadeShapeJ2_of (c : Ctx) (N : NodeId → Option KNode) (B : NodeId) (vals : List NodeId)
    (X : Nat → NodeId) (K : Nat → Nat) (Nn : Nat → KNode) (s D : Nat) (ins : List (Nat × NodeId))
    (nx : NodeId) (hS : OldStartN N c.i B) (hM : MadeStartN N c.i B)
    (hN : ∀ i, s ≤ i → i ≤ D → N (X i) = some (Nn i))
    (hts : ∀ i, s ≤ i → i ≤ D → ∀ u, Klong.time u ∈ (Nn i).ks → u ≤ c.i)
    (hBnx : B ≤ nx) (hinsN : (ins.map Prod.fst).Nodup)
    (hins : ∀ q ∈ ins, ∀ y, (q.1, y) ∈ (Nn D).liveAt c.i → y < B ∨ y ∈ vals)
    (z : NodeId) (zn : KNode) (hz : nx ≤ z ∨ ∃ i, s ≤ i ∧ i ≤ D ∧ z = X i)
    (hprev : ∀ i, s ≤ i → i ≤ D → z = X i → zn = (Nn i).toPrev (c.i - 1) →
      (Nn i).firstTime ≠ some c.i)
    (hleaf : ∀ j, s ≤ j → j < D → z = X j → ∀ k1 idx r, (Nn j).linkIndex (X (j + 1)) k1 = some idx →
      zn = (Nn j).repoint idx r → (Nn j).leaf = true)
    (h : CascadeNodeShape c X K Nn s D ins z zn) : CascadeShapeJ2 N c.i B vals X Nn s D z zn := by
  rcases h with ⟨i, h1, h2, h3, h4⟩ | ⟨i, h1, h2, h3, h4⟩ | ⟨hsh, hft⟩ | ⟨j, h1, h2, h3, htop⟩
  · exact Or.inl ⟨i, h1, h2, h3, h4⟩
  · exact Or.inr (Or.inl ⟨i, h1, h2, h3, hprev i h1 h2 h3 h4, h4⟩)
  · refine Or.inr (Or.inr (Or.inl ⟨⟨hsh.1, fun a b cv y y' hab ha hb => ?_⟩, ?_⟩))
    · rcases hsh.2 a b cv y y' hab ha hb with ⟨i, a1, a2, a3, a4⟩ | ⟨c0, a1, a2⟩
      · left
        rw [a3]
        exact lt_of_firstTime_ne N c.i B hM _ _ (hN (i + 1) (by omega) (by omega)) a4
      · obtain ⟨q, hq, hq1⟩ := List.mem_map.mp a2
        exact hins q hq y (by rw [hq1]; exact a1)
    · rcases hz with hz | ⟨i, h1, h2, rfl⟩
      · omega
      · exact ge_of_firstTime2 N c.i B hS _ _ (hN i h1 h2) (hft i h1 h2 rfl)
  · refine Or.inr (Or.inr (Or.inr ⟨j, h1, h2, h3, ?_⟩))
    rcases htop with ⟨hj, hz'⟩ | ⟨hj, ins', hz', hnd, hq⟩ | ⟨hj, k1, idx, r, hl, hz', hf⟩
    · subst hj
      exact Or.inl ⟨ins, hz', hinsN, hins⟩
    · refine Or.inl ⟨ins', hz', hnd, fun q hq' y hy => Or.inl ?_⟩
      obtain ⟨_, hyx, hnf⟩ := hq q hq' y hy
      rw [hyx]
      exact lt_of_firstTime_ne N c.i B hM _ _ (hN (j + 1) (by omega) (by omega)) hnf
    · exact Or.inr ⟨idx, k1, X (j + 1), r, Nn (j + 1), hl,
        liveAt_of_linkIndex (Nn j) c.i (X (j + 1)) k1 idx hl (hts j h1 (by omega)),
        ge_of_firstTime2 N c.i B hS _ _ (hN (j + 1) (by omega) (by omega)) hf,
        hN (j + 1) (by omega) (by omega), hleaf j h1 hj h3 k1 idx r hl hz', hz'⟩

end SIS.Tree
