/-
The upward delete in full at the writer's level (bergdb 024-22): the stop node's
bitmap or LE-b, or a stop at a segment leaf; the tree and the reading
together.
-/
import SIS.Tree.WriterGetUpLeb

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- With the stop node relinked by f (LE-b): the tree after the upward delete at
tree level, the stop node X s's klong K (s + 1) to the chain X (s + 1) .. X D
deleted (N' agrees with N but at X s and the chain): a tree from the same root,
which reaches only what N reached but the chain. -/
theorem treeOK_up_tr (N N' : NodeId → Option KNode) (t : Time) (r : NodeId) (X : Nat → NodeId)
    (Nn : Nat → KNode) (K : Nat → Nat) (s D : Nat) (hsD : s < D)
    (hT : TreeOK N t r) (hXs : TReach N t r (X s))
    (hN : ∀ i, s ≤ i → i ≤ D → N (X i) = some (Nn i))
    (hlinkK : ∀ i, s < i → i ≤ D → (K i, X i) ∈ (Nn (i - 1)).liveAt t)
    (hdist : ∀ i i', s ≤ i → i ≤ D → s ≤ i' → i' ≤ D → X i = X i' → i = i')
    (hagree : ∀ u, u ≠ X s → (∀ i, s < i → i ≤ D → u ≠ X i) → N' u = N u)
    (sn' : KNode) (hsn' : N' (X s) = some sn') (f : Nat → Nat)
    (hlive' : ∀ c z, (c, z) ∈ sn'.liveAt t → ∃ c0, (c0, z) ∈ (Nn s).liveAt t ∧ c0 ≠ K (s + 1) ∧ f c0 = c) :
    TreeOK N' t r := by
  have hreach : ∀ k, s + k ≤ D → TReach N t r (X (s + k)) := by
    intro k
    induction k with
    | zero => intro _; simpa using hXs
    | succ k ih =>
      intro hk
      have hl := hlinkK (s + (k + 1)) (by omega) hk
      rw [show s + (k + 1) - 1 = s + k by omega] at hl
      exact TReach.link (ih (by omega)) ⟨Nn (s + k), hN (s + k) (by omega) (by omega), hl⟩
  have hXi : ∀ i, s ≤ i → i ≤ D → TReach N t r (X i) := by
    intro i h1 h2
    have := hreach (i - s) (by omega)
    rwa [show s + (i - s) = i by omega] at this
  have hlk : ∀ i, s < i → i ≤ D → TLink N t (X (i - 1)) (K i) (X i) := fun i h1 h2 =>
    ⟨Nn (i - 1), hN (i - 1) (by omega) (by omega), hlinkK i h1 h2⟩
  apply treeOK_dropSubtree_tr N N' t r (X s) (X (s + 1)) (K (s + 1)) (Nn s) sn'
    (fun g => ∃ k, s < k ∧ k ≤ D ∧ g = X k) f hT hXs (hN s (Nat.le_refl _) (by omega))
    (by have := hlinkK (s + 1) (by omega) (by omega); simpa using this) hsn' hlive'
  · rintro ⟨k, h1, h2, he⟩
    have := hdist s k (Nat.le_refl _) (by omega) (by omega) h2 he; omega
  · rintro ⟨k, h1, h2, he⟩
    exact hT.rootFree (X (k - 1)) (K k) (hXi (k - 1) (by omega) (by omega)) (by rw [he]; exact hlk k h1 h2)
  · rintro g ⟨k, h1, h2, rfl⟩
    by_cases hk : k = s + 1
    · left; rw [hk]
    · right
      intro u c hu hl
      have he := (hT.oneLink u c (X (k - 1)) (K k) (X k) hu (hXi (k - 1) (by omega) (by omega)) hl
        (hlk k h1 h2)).1
      exact ⟨k - 1, by omega, by omega, he⟩
  · intro x hxs hxG
    exact hagree x hxs (fun i h1 h2 he => hxG ⟨i, h1, h2, he⟩)

/-- With the stop node relinked: after the upward delete at tree level, what N'
reaches N reached, and it is no node of the chain; a link of a node N' reaches is
one of N. -/
theorem tReach_up_sub_tr (N N' : NodeId → Option KNode) (t : Time) (r : NodeId) (X : Nat → NodeId)
    (Nn : Nat → KNode) (K : Nat → Nat) (s D : Nat) (hsD : s < D)
    (hT : TreeOK N t r) (hXs : TReach N t r (X s))
    (hN : ∀ i, s ≤ i → i ≤ D → N (X i) = some (Nn i))
    (hlinkK : ∀ i, s < i → i ≤ D → (K i, X i) ∈ (Nn (i - 1)).liveAt t)
    (hdist : ∀ i i', s ≤ i → i ≤ D → s ≤ i' → i' ≤ D → X i = X i' → i = i')
    (hagree : ∀ u, u ≠ X s → (∀ i, s < i → i ≤ D → u ≠ X i) → N' u = N u)
    (sn' : KNode) (hsn' : N' (X s) = some sn')
    (hlive' : ∀ c z, (c, z) ∈ sn'.liveAt t → ∃ c0, (c0, z) ∈ (Nn s).liveAt t ∧ c0 ≠ K (s + 1)) :
    ∀ y, TReach N' t r y → TReach N t r y ∧ ∀ k, s < k → k ≤ D → y ≠ X k := by
  have hreach : ∀ k, s + k ≤ D → TReach N t r (X (s + k)) := by
    intro k
    induction k with
    | zero => intro _; simpa using hXs
    | succ k ih =>
      intro hk
      have hl := hlinkK (s + (k + 1)) (by omega) hk
      rw [show s + (k + 1) - 1 = s + k by omega] at hl
      exact TReach.link (ih (by omega)) ⟨Nn (s + k), hN (s + k) (by omega) (by omega), hl⟩
  have hXi : ∀ i, s ≤ i → i ≤ D → TReach N t r (X i) := by
    intro i h1 h2
    have := hreach (i - s) (by omega)
    rwa [show s + (i - s) = i by omega] at this
  have hlk : ∀ i, s < i → i ≤ D → TLink N t (X (i - 1)) (K i) (X i) := fun i h1 h2 =>
    ⟨Nn (i - 1), hN (i - 1) (by omega) (by omega), hlinkK i h1 h2⟩
  -- a link of N into the chain is the chain's own link
  have hinto : ∀ x c k, TReach N t r x → TLink N t x c (X k) → s < k → k ≤ D →
      x = X (k - 1) ∧ c = K k := by
    intro x c k hx hl h1 h2
    exact hT.oneLink x c (X (k - 1)) (K k) (X k) hx (hXi (k - 1) (by omega) (by omega)) hl (hlk k h1 h2)
  intro y hy
  induction hy with
  | root =>
    refine ⟨TReach.root, fun k h1 h2 he => ?_⟩
    exact hT.rootFree (X (k - 1)) (K k) (hXi (k - 1) (by omega) (by omega)) (by rw [he]; exact hlk k h1 h2)
  | @link x c z hx hl ih =>
    obtain ⟨hxN, hxc⟩ := ih
    obtain ⟨m, hm, hcm⟩ := hl
    by_cases hxs : x = X s
    · rw [hxs, hsn'] at hm
      simp only [Option.some.injEq] at hm
      subst hm
      obtain ⟨c0, hcm', hc⟩ := hlive' c z hcm
      have hlN : TLink N t x c0 z := ⟨Nn s, by rw [hxs]; exact hN s (Nat.le_refl _) (by omega), hcm'⟩
      refine ⟨TReach.link hxN hlN, fun k h1 h2 he => ?_⟩
      rw [he] at hlN
      obtain ⟨hx1, hc1⟩ := hinto x c0 k hxN hlN h1 h2
      rw [hxs] at hx1
      have := hdist s (k - 1) (Nat.le_refl _) (by omega) (by omega) (by omega) hx1
      have hk : k = s + 1 := by omega
      subst hk
      exact hc hc1
    · rw [hagree x hxs hxc] at hm
      have hlN : TLink N t x c z := ⟨m, hm, hcm⟩
      refine ⟨TReach.link hxN hlN, fun k h1 h2 he => ?_⟩
      rw [he] at hlN
      obtain ⟨hx1, _⟩ := hinto x c k hxN hlN h1 h2
      rcases Nat.lt_or_ge s (k - 1) with h | h
      · exact hxc (k - 1) h (by omega) hx1
      · have : k - 1 = s := by omega
        rw [this] at hx1
        exact hxs hx1

/-- A link of a node N' reaches, after the upward delete at tree level with the stop node relinked, is
one of N, up to its compare value. -/
theorem tLink_up_sub_tr (N N' : NodeId → Option KNode) (t : Time) (r : NodeId) (X : Nat → NodeId)
    (Nn : Nat → KNode) (K : Nat → Nat) (s D : Nat) (hsD : s < D)
    (hT : TreeOK N t r) (hXs : TReach N t r (X s))
    (hN : ∀ i, s ≤ i → i ≤ D → N (X i) = some (Nn i))
    (hlinkK : ∀ i, s < i → i ≤ D → (K i, X i) ∈ (Nn (i - 1)).liveAt t)
    (hdist : ∀ i i', s ≤ i → i ≤ D → s ≤ i' → i' ≤ D → X i = X i' → i = i')
    (hagree : ∀ u, u ≠ X s → (∀ i, s < i → i ≤ D → u ≠ X i) → N' u = N u)
    (sn' : KNode) (hsn' : N' (X s) = some sn')
    (hlive' : ∀ c z, (c, z) ∈ sn'.liveAt t → ∃ c0, (c0, z) ∈ (Nn s).liveAt t ∧ c0 ≠ K (s + 1)) :
    ∀ x c y, TReach N' t r x → TLink N' t x c y → ∃ c0, TLink N t x c0 y := by
  intro x c y hx hl
  obtain ⟨m, hm, hcm⟩ := hl
  by_cases hxs : x = X s
  · rw [hxs, hsn'] at hm
    simp only [Option.some.injEq] at hm
    subst hm
    obtain ⟨c0, h0, _⟩ := hlive' c y hcm
    exact ⟨c0, Nn s, by rw [hxs]; exact hN s (Nat.le_refl _) (by omega), h0⟩
  · have hxc := (tReach_up_sub_tr N N' t r X Nn K s D hsD hT hXs hN hlinkK hdist hagree sn' hsn' hlive' x hx).2
    rw [hagree x hxs hxc] at hm
    exact ⟨c, m, hm, hcm⟩

/-- LE-b's node's live klongs from its lookups. -/
theorem liveAt_iff_of_leb_lookup (n n' : KNode) (t : Time) (jcv : Nat) (jy : NodeId)
    (hn : ∀ s, Klong.time s ∈ n.ks → s ≤ t) (hn' : ∀ s, Klong.time s ∈ n'.ks → s ≤ t)
    (hl : ∀ c, n'.live.lookup c = if c = 0 then some jy else if c = jcv then none else n.live.lookup c) :
    ∀ c z, (c, z) ∈ n'.liveAt t ↔ (c = 0 ∧ z = jy) ∨ ((c, z) ∈ n.liveAt t ∧ c ≠ 0 ∧ c ≠ jcv) := by
  intro c z
  rw [KNode.liveAt_of_times n' t hn', KNode.liveAt_of_times n t hn,
    mem_iff_lookup _ (KNode.live_keys_nodup n'), mem_iff_lookup _ (KNode.live_keys_nodup n), hl c]
  by_cases h0 : c = 0
  · rw [ite_eq_left_of_eq_true _ _ (eq_true h0)]
    constructor
    · intro h; exact Or.inl ⟨h0, (Option.some.inj h).symm⟩
    · rintro (⟨_, h⟩ | ⟨_, h, _⟩)
      · rw [h]
      · exact absurd h0 h
  · rw [ite_eq_right_of_eq_false _ _ (eq_false h0)]
    by_cases hj : c = jcv
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hj)]
      constructor
      · intro h; cases h
      · rintro (⟨h1, _⟩ | ⟨_, _, h2⟩)
        · exact absurd h1 h0
        · exact absurd hj h2
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hj)]
      constructor
      · intro h; exact Or.inr ⟨h, h0, hj⟩
      · rintro (⟨h1, _⟩ | ⟨h, _, _⟩)
        · exact absurd h1 h0
        · exact h

end SIS.Tree
