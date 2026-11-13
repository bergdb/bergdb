import SIS.Tree.RangeSim

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-! The walk's ranges after the splits that `rangeOrder_timeStep` and
`rangeOrder_spaceStep` leave out (bergdb 024-12, TP10; `RangeOrder`): of a
segment root below its segment leaf, of the space root, and in place. -/

/-- `rangeOrder_timeStep` below a segment leaf q: the segment root x's time
split, q's klong k1 naming the new node y. -/
theorem rangeOrder_segTimeStep (N1 N2 : NodeId → Option KNode) (t : Time) (r : NodeId)
    (hR : RangeOrder N1 t r) (hT : TreeOK N1 t r)
    (q x y : NodeId) (qn xn yn qn2 : KNode) (k1 : Nat)
    (hq : TReach N1 t r q) (hqn : N1 q = some qn) (hql : qn.leaf = true)
    (hk1 : (k1, x) ∈ qn.liveAt t) (hxn : N1 x = some xn)
    (hy1 : N1 y = none) (hyfree : ∀ u c, TReach N1 t r u → ¬ TLink N1 t u c y)
    (hN2q : N2 q = some qn2) (hq2l : qn2.leaf = true)
    (hq2 : ∀ c z, (c, z) ∈ qn2.liveAt t → (c = k1 ∧ z = y) ∨ (c ≠ k1 ∧ (c, z) ∈ qn.liveAt t))
    (hN2y : N2 y = some yn) (hyl : yn.leaf = xn.leaf)
    (hylive : ∀ c z, (c, z) ∈ yn.liveAt t → (c, z) ∈ xn.liveAt t)
    (hN2 : ∀ z, z ≠ q → z ≠ y → z ≠ x → N2 z = N1 z) :
    RangeOrder N2 t r := by
  have hxR : TReach N1 t r x := TReach.link hq ⟨qn, hqn, hk1⟩
  have hyq : y ≠ q := by intro h; rw [h, hqn] at hy1; cases hy1
  have hyx : y ≠ x := by intro h; rw [h, hxn] at hy1; cases hy1
  have hqx : q ≠ x := by
    intro h
    exact hT.no_self_link x k1 hxR ⟨qn, by rw [← h]; exact hqn, hk1⟩
  have hrx : r ≠ x := by
    intro h; exact hT.rootFree q k1 hq ⟨qn, hqn, h ▸ hk1⟩
  have hry : r ≠ y := by
    intro h; obtain ⟨m, hm⟩ := hT.rootKey; rw [h, hy1] at hm; cases hm
  -- the only link to x is q's k1
  have honly : ∀ u c, TReach N1 t r u → TLink N1 t u c x → u = q ∧ c = k1 := fun u c hu hl =>
    hT.oneLink u c q k1 x hu hq hl ⟨qn, hqn, hk1⟩
  let φ : NodeId → NodeId := fun z => if z = y then x else z
  have hφy : φ y = x := by simp [φ]
  have hφ : ∀ z, z ≠ y → φ z = z := fun z hz => by simp [φ, hz]
  -- the node of z after, from the node of φ z before
  have hnode : ∀ z m, z ≠ q → z ≠ x → N2 z = some m →
      ∃ m0, N1 (φ z) = some m0 ∧ m.leaf = m0.leaf ∧
        ∀ c z', (c, z') ∈ m.liveAt t → (c, z') ∈ m0.liveAt t := by
    intro z m hzq hzx hm
    by_cases hzy : z = y
    · subst hzy; rw [hN2y] at hm; cases hm; rw [hφy]; exact ⟨xn, hxn, hyl, hylive⟩
    · rw [hN2 z hzq hzy hzx] at hm; rw [hφ z hzy]; exact ⟨m, hm, rfl, fun _ _ h => h⟩
  let G : NodeId → Nat → Option Nat → Prop := fun z lo hi =>
    z ≠ x ∧ ∃ lo0 hi0, ReachR N1 t r (φ z) lo0 hi0 ∧ lo ≤ lo0 ∧ HiLE hi0 hi
  -- a child after of a node reached before: not x but from q's k1, not y but from q's k1
  have hchild : ∀ u c z, TReach N1 t r u → TLink N1 t u c z → u ≠ q → z ≠ x ∧ z ≠ y := by
    intro u c z hu hl huq
    refine ⟨fun h => huq (honly u c hu (h ▸ hl)).1, fun h => hyfree u c hu (h ▸ hl)⟩
  apply rangeOrder_of_good N2 t r G
  · refine ⟨hrx, 0, none, ?_, Nat.le_refl _, HiLE.refl _⟩
    rw [hφ r hry]; exact ReachR.root
  · intro z lo hi m c z' b _ hG hm hml hb
    obtain ⟨hzx, lo0, hi0, hz0, hlo, hhi⟩ := hG
    have hcz := childBounds_fst _ _ _ _ hb
    have hms := KNode.liveAt_order m t
    by_cases hzq : z = q
    · subst hzq
      rw [hN2q] at hm; cases hm; rw [hq2l] at hml; cases hml
    · obtain ⟨m0, hm0, hlf, hlv⟩ := hnode z m hzq hzx hm
      have hu := reachR_tReach N1 t r (φ z) lo0 hi0 hz0
      have hcz0 : (c, z') ∈ m0.liveAt t := hlv c z' hcz
      have hφq : φ z ≠ q := by
        by_cases hzy : z = y
        · rw [hzy, hφy]; exact hqx.symm
        · rw [hφ z hzy]; exact hzq
      obtain ⟨hz'x, hz'y⟩ := hchild (φ z) c z' hu ⟨m0, hm0, hcz0⟩ hφq
      obtain ⟨lo1, hi1, h3, h4, h5⟩ := old_child_step N1 t r hR (φ z) m0 lo0 lo hi0 hi hz0 hm0
        (by rw [← hlf]; exact hml) hlo hhi _ hms c z' z' b hcz0 hb
        (fun r' hr' hlt => ⟨r', hlv r'.1 r'.2 hr', hlt, Nat.le_refl _⟩)
      exact ⟨hz'x, lo1, hi1, by rw [hφ z' hz'y]; exact h3, h4, h5⟩
  · intro z lo hi m c z' _ hG hm hml hcz
    obtain ⟨hzx, lo0, hi0, hz0, _, _⟩ := hG
    by_cases hzq : z = q
    · subst hzq
      rw [hN2q] at hm; cases hm
      rw [hφ z hyq.symm] at hz0
      rcases hq2 c z' hcz with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h2]
        exact ⟨hyx, 0, none, by rw [hφy]; exact ReachR.seg z qn lo0 hi0 k1 x hz0 hqn hql hk1,
          Nat.le_refl _, HiLE.refl _⟩
      · have hz'x : z' ≠ x := fun h => h1 (honly z c hq ⟨qn, hqn, h ▸ h2⟩).2
        have hz'y : z' ≠ y := fun h => hyfree z c hq ⟨qn, hqn, h ▸ h2⟩
        exact ⟨hz'x, 0, none, by rw [hφ z' hz'y]; exact ReachR.seg z qn lo0 hi0 c z' hz0 hqn hql h2,
          Nat.le_refl _, HiLE.refl _⟩
    obtain ⟨m0, hm0, hlf, hlv⟩ := hnode z m hzq hzx hm
    have hu := reachR_tReach N1 t r (φ z) lo0 hi0 hz0
    have hcz0 : (c, z') ∈ m0.liveAt t := hlv c z' hcz
    have hφq : φ z ≠ q := by
      by_cases hzy : z = y
      · rw [hzy, hφy]; exact hqx.symm
      · rw [hφ z hzy]; exact hzq
    obtain ⟨hz'x, hz'y⟩ := hchild (φ z) c z' hu ⟨m0, hm0, hcz0⟩ hφq
    refine ⟨hz'x, 0, none, ?_, Nat.le_refl _, HiLE.refl _⟩
    rw [hφ z' hz'y]
    exact ReachR.seg (φ z) m0 lo0 hi0 c z' hz0 hm0 (by rw [← hlf]; exact hml) hcz0
  · intro z lo hi m _ hG hm
    obtain ⟨hzx, lo0, hi0, hz0, hlo, hhi⟩ := hG
    by_cases hzq : z = q
    · subst hzq
      rw [hN2q] at hm; cases hm
      rw [hφ z hyq.symm] at hz0
      refine nodeRange_sub qn qn2 t lo0 lo hi0 hi (hR z lo0 hi0 qn hz0 hqn) (by rw [hq2l, hql]) ?_ hlo hhi
      intro q' hq'
      rcases hq2 q'.1 q'.2 hq' with ⟨h1, _⟩ | ⟨_, h2⟩
      · exact ⟨(k1, x), hk1, h1.symm⟩
      · exact ⟨q', h2, rfl⟩
    · obtain ⟨m0, hm0, hlf, hlv⟩ := hnode z m hzq hzx hm
      exact nodeRange_sub m0 m t lo0 lo hi0 hi (hR _ lo0 hi0 m0 hz0 hm0) hlf
        (fun q' hq' => ⟨q', hlv q'.1 q'.2 hq', rfl⟩) hlo hhi

/-- `rangeOrder_timeStep` below a parent of either kind (prover cost's
`treeOK_timeSplit_gen`). -/
theorem rangeOrder_timeStepAny (N1 N2 : NodeId → Option KNode) (t : Time) (r : NodeId)
    (hR : RangeOrder N1 t r) (hT : TreeOK N1 t r)
    (q x y : NodeId) (qn xn yn qn2 : KNode) (k1 : Nat)
    (hq : TReach N1 t r q) (hqn : N1 q = some qn)
    (hk1 : (k1, x) ∈ qn.liveAt t) (hxn : N1 x = some xn)
    (hy1 : N1 y = none) (hyfree : ∀ u c, TReach N1 t r u → ¬ TLink N1 t u c y)
    (hN2q : N2 q = some qn2) (hq2l : qn2.leaf = qn.leaf)
    (hq2 : ∀ c z, (c, z) ∈ qn2.liveAt t → (c = k1 ∧ z = y) ∨ (c ≠ k1 ∧ (c, z) ∈ qn.liveAt t))
    (hN2y : N2 y = some yn) (hyl : yn.leaf = xn.leaf)
    (hylive : ∀ c z, (c, z) ∈ yn.liveAt t → (c, z) ∈ xn.liveAt t)
    (hN2 : ∀ z, z ≠ q → z ≠ y → z ≠ x → N2 z = N1 z) :
    RangeOrder N2 t r := by
  cases hql : qn.leaf with
  | false =>
    exact rangeOrder_timeStep N1 N2 t r hR hT q x y qn xn yn qn2 k1 hq hqn hql hk1 hxn hy1 hyfree
      hN2q (by rw [hq2l, hql]) hq2 hN2y hyl hylive hN2
  | true =>
    exact rangeOrder_segTimeStep N1 N2 t r hR hT q x y qn xn yn qn2 k1 hq hqn hql hk1 hxn hy1 hyfree
      hN2q (by rw [hq2l, hql]) hq2 hN2y hyl hylive hN2

/-- The walk's ranges after a time split of the space root x (the root of N1, x
with its klongs to put): the new node y, with x's live klongs, is the root. -/
theorem rangeOrder_rootTimeStep (N1 N2 : NodeId → Option KNode) (t : Time) (x y : NodeId)
    (xn yn : KNode) (hR : RangeOrder N1 t x) (hT : TreeOK N1 t x) (hxn : N1 x = some xn)
    (hy1 : N1 y = none) (hyfree : ∀ u c, TReach N1 t x u → ¬ TLink N1 t u c y)
    (hN2y : N2 y = some yn) (hyl : yn.leaf = xn.leaf)
    (hylive : ∀ c z, (c, z) ∈ yn.liveAt t → (c, z) ∈ xn.liveAt t)
    (hN2 : ∀ z, z ≠ y → z ≠ x → N2 z = N1 z) :
    RangeOrder N2 t y := by
  have hyx : y ≠ x := by intro h; rw [h, hxn] at hy1; cases hy1
  let φ : NodeId → NodeId := fun z => if z = y then x else z
  have hφy : φ y = x := by simp [φ]
  have hφ : ∀ z, z ≠ y → φ z = z := fun z hz => by simp [φ, hz]
  have hnode : ∀ z m, z ≠ x → N2 z = some m →
      ∃ m0, N1 (φ z) = some m0 ∧ m.leaf = m0.leaf ∧
        ∀ c z', (c, z') ∈ m.liveAt t → (c, z') ∈ m0.liveAt t := by
    intro z m hzx hm
    by_cases hzy : z = y
    · subst hzy; rw [hN2y] at hm; cases hm; rw [hφy]; exact ⟨xn, hxn, hyl, hylive⟩
    · rw [hN2 z hzy hzx] at hm; rw [hφ z hzy]; exact ⟨m, hm, rfl, fun _ _ h => h⟩
  have hchild : ∀ u c z, TReach N1 t x u → TLink N1 t u c z → z ≠ x ∧ z ≠ y := by
    intro u c z hu hl
    exact ⟨fun h => hT.rootFree u c hu (h ▸ hl), fun h => hyfree u c hu (h ▸ hl)⟩
  let G : NodeId → Nat → Option Nat → Prop := fun z lo hi =>
    z ≠ x ∧ ∃ lo0 hi0, ReachR N1 t x (φ z) lo0 hi0 ∧ lo ≤ lo0 ∧ HiLE hi0 hi
  apply rangeOrder_of_good N2 t y G
  · exact ⟨hyx, 0, none, by rw [hφy]; exact ReachR.root, Nat.le_refl _, HiLE.refl _⟩
  · intro z lo hi m c z' b _ hG hm hml hb
    obtain ⟨hzx, lo0, hi0, hz0, hlo, hhi⟩ := hG
    have hcz := childBounds_fst _ _ _ _ hb
    obtain ⟨m0, hm0, hlf, hlv⟩ := hnode z m hzx hm
    have hcz0 : (c, z') ∈ m0.liveAt t := hlv c z' hcz
    obtain ⟨hz'x, hz'y⟩ := hchild (φ z) c z' (reachR_tReach N1 t x (φ z) lo0 hi0 hz0)
      ⟨m0, hm0, hcz0⟩
    obtain ⟨lo1, hi1, h3, h4, h5⟩ := old_child_step N1 t x hR (φ z) m0 lo0 lo hi0 hi hz0 hm0
      (by rw [← hlf]; exact hml) hlo hhi _ (KNode.liveAt_order m t) c z' z' b hcz0 hb
      (fun r' hr' hlt => ⟨r', hlv r'.1 r'.2 hr', hlt, Nat.le_refl _⟩)
    exact ⟨hz'x, lo1, hi1, by rw [hφ z' hz'y]; exact h3, h4, h5⟩
  · intro z lo hi m c z' _ hG hm hml hcz
    obtain ⟨hzx, lo0, hi0, hz0, _, _⟩ := hG
    obtain ⟨m0, hm0, hlf, hlv⟩ := hnode z m hzx hm
    have hcz0 : (c, z') ∈ m0.liveAt t := hlv c z' hcz
    obtain ⟨hz'x, hz'y⟩ := hchild (φ z) c z' (reachR_tReach N1 t x (φ z) lo0 hi0 hz0)
      ⟨m0, hm0, hcz0⟩
    refine ⟨hz'x, 0, none, ?_, Nat.le_refl _, HiLE.refl _⟩
    rw [hφ z' hz'y]
    exact ReachR.seg (φ z) m0 lo0 hi0 c z' hz0 hm0 (by rw [← hlf]; exact hml) hcz0
  · intro z lo hi m _ hG hm
    obtain ⟨hzx, lo0, hi0, hz0, hlo, hhi⟩ := hG
    obtain ⟨m0, hm0, hlf, hlv⟩ := hnode z m hzx hm
    exact nodeRange_sub m0 m t lo0 lo hi0 hi (hR _ lo0 hi0 m0 hz0 hm0) hlf
      (fun q' hq' => ⟨q', hlv q'.1 q'.2 hq', rfl⟩) hlo hhi

/-- `rangeOrder_spaceStep` in place: x, made by the transaction, keeps the first
half; the second half S is new and q's klong sc names it, q's klong k1 still
names x. -/
theorem rangeOrder_spaceInPlaceStep (N1 N2 : NodeId → Option KNode) (t : Time) (r : NodeId)
    (hR : RangeOrder N1 t r) (hT : TreeOK N1 t r)
    (q x S : NodeId) (qn xn fn sn qn2 : KNode) (k1 sc : Nat)
    (hq : TReach N1 t r q) (hqn : N1 q = some qn) (hql : qn.leaf = false)
    (hk1 : (k1, x) ∈ qn.liveAt t) (hxn : N1 x = some xn)
    (hS1 : N1 S = none)
    (hSfree : ∀ u c, TReach N1 t r u → ¬ TLink N1 t u c S)
    (hsc : ∃ zs, (sc, zs) ∈ xn.liveAt t) (hlow : ∃ c0 z0, (c0, z0) ∈ xn.liveAt t ∧ c0 < sc)
    (hN2q : N2 q = some qn2) (hq2l : qn2.leaf = false)
    (hq2 : ∀ c z, (c, z) ∈ qn2.liveAt t →
      (c = sc ∧ z = S) ∨ (c ≠ sc ∧ (c, z) ∈ qn.liveAt t))
    (hq2sc : (sc, S) ∈ qn2.liveAt t)
    (hN2x : N2 x = some fn) (hfl : fn.leaf = xn.leaf)
    (hf : ∀ c z, (c, z) ∈ fn.liveAt t → (c, z) ∈ xn.liveAt t ∧ c < sc)
    (hN2S : N2 S = some sn) (hsl : sn.leaf = xn.leaf)
    (hs : ∀ c z, (c, z) ∈ sn.liveAt t → ∃ c0, sc ≤ c0 ∧ (c0, z) ∈ xn.liveAt t ∧
      c = (if c0 = sc ∧ xn.leaf = false then 0 else c0))
    (hN2 : ∀ z, z ≠ q → z ≠ x → z ≠ S → N2 z = N1 z) :
    RangeOrder N2 t r := by
  have hxR : TReach N1 t r x := TReach.link hq ⟨qn, hqn, hk1⟩
  have hSq : S ≠ q := by intro h; rw [h, hqn] at hS1; cases hS1
  have hSx : S ≠ x := by intro h; rw [h, hxn] at hS1; cases hS1
  have hqx : q ≠ x := by
    intro h
    exact hT.no_self_link x k1 hxR ⟨qn, by rw [← h]; exact hqn, hk1⟩
  have hrx : r ≠ x := by
    intro h; exact hT.rootFree q k1 hq ⟨qn, hqn, h ▸ hk1⟩
  have hrS : r ≠ S := by
    intro h; obtain ⟨m, hm⟩ := hT.rootKey; rw [h, hS1] at hm; cases hm
  have honly : ∀ u c, TReach N1 t r u → TLink N1 t u c x → u = q ∧ c = k1 := fun u c hu hl =>
    hT.oneLink u c q k1 x hu hq hl ⟨qn, hqn, hk1⟩
  have hchild : ∀ u c z, TReach N1 t r u → TLink N1 t u c z → u ≠ q → z ≠ x ∧ z ≠ S := by
    intro u c z hu hl huq
    exact ⟨fun h => huq (honly u c hu (h ▸ hl)).1, fun h => hSfree u c hu (h ▸ hl)⟩
  have hk1u : ∀ z', (k1, z') ∈ qn.liveAt t → z' = x := by
    intro z' h
    have h1 := lookup_of_mem_nodup _ (KNode.liveAt_keys_nodup qn t) k1 z' h
    have h2 := lookup_of_mem_nodup _ (KNode.liveAt_keys_nodup qn t) k1 x hk1
    rw [h1] at h2; exact Option.some.inj h2
  have hxchild : ∀ c z, (c, z) ∈ xn.liveAt t → z ≠ x ∧ z ≠ S := by
    intro c z hz
    refine hchild x c z hxR ⟨xn, hxn, hz⟩ hqx.symm
  obtain ⟨c0, z0, hz0, hc0⟩ := hlow
  have hsc0 : 0 < sc := by omega
  -- the facts of x's range below a range of q
  have hxrange : ∀ lo0 hi0, ReachR N1 t r q lo0 hi0 → ∀ b0,
      ((k1, x), b0) ∈ childBounds (qn.liveAt t) hi0 →
      k1 < sc ∧ lo0 < sc ∧ UpperBound b0 sc ∧ UpperBound hi0 sc := by
    intro lo0 hi0 hq0 b0 hb0
    have hx0 := ReachR.inner q qn lo0 hi0 k1 x b0 hq0 hqn hql hb0
    have hxr := hR x _ b0 xn hx0 hxn
    have hqr := hR q lo0 hi0 qn hq0 hqn
    obtain ⟨zs, hzs⟩ := hsc
    obtain ⟨hscl, hscu⟩ := hxr (sc, zs) hzs
    obtain ⟨hc0l, _⟩ := hxr (c0, z0) hz0
    obtain ⟨hk1l, hk1u⟩ := hqr (k1, x) hk1
    simp only [hql, Bool.false_eq_true, ↓reduceIte] at hk1l
    have hb0u : UpperBound hi0 sc := by
      rcases (childBounds_isNext _ hi0 (KNode.liveAt_order qn t) _ _ hb0).2 with
        ⟨hb, _⟩ | ⟨r', hr', hb, _, _⟩
      · rw [hb] at hscu; exact hscu
      · rw [hb] at hscu
        have := (hqr r' hr').2
        cases hi0 with
        | none => trivial
        | some h0 => simp only [UpperBound] at this hscu ⊢; omega
    cases hxl : xn.leaf with
    | true =>
      simp only [hxl, ↓reduceIte] at hscl hc0l
      by_cases hk : k1 = 0
      · subst hk
        simp only [beq_self_eq_true, ↓reduceIte] at hscl hc0l
        exact ⟨hsc0, by omega, hscu, hb0u⟩
      · rw [ite_zero_eq k1 lo0 hk] at hscl hc0l
        exact ⟨by omega, by omega, hscu, hb0u⟩
    | false =>
      simp only [hxl, Bool.false_eq_true, ↓reduceIte] at hscl
      by_cases hk : k1 = 0
      · subst hk
        simp only [beq_self_eq_true, ↓reduceIte] at hscl
        exact ⟨hsc0, by omega, hscu, hb0u⟩
      · rw [ite_zero_eq k1 lo0 hk] at hscl
        exact ⟨by omega, by omega, hscu, hb0u⟩
  let G : NodeId → Nat → Option Nat → Prop := fun z lo hi =>
    (z ≠ x ∧ z ≠ S ∧ ∃ lo0 hi0, ReachR N1 t r z lo0 hi0 ∧ lo ≤ lo0 ∧ HiLE hi0 hi) ∨
    (z = x ∧ hi = some sc ∧ ∃ lo0 hi0, ReachR N1 t r x lo0 hi0 ∧ lo ≤ lo0) ∨
    (z = S ∧ lo = sc ∧ ∃ lo0 hi0, ReachR N1 t r x lo0 hi0 ∧ HiLE hi0 hi)
  apply rangeOrder_of_good N2 t r G
  · exact Or.inl ⟨hrx, hrS, 0, none, ReachR.root, Nat.le_refl _, HiLE.refl _⟩
  · intro z lo hi m c z' b _ hG hm hml hb
    have hcz := childBounds_fst _ _ _ _ hb
    have hms := KNode.liveAt_order m t
    rcases hG with ⟨hzx, hzS, lo0, hi0, hz0, hlo, hhi⟩ | ⟨hzF, hhs, lo0, hi0, hx0, hlo⟩ |
      ⟨hzS, hls, lo0, hi0, hx0, hhi⟩
    · by_cases hzq : z = q
      · subst hzq
        rw [hN2q] at hm; cases hm
        obtain ⟨b0, hb0⟩ := childBounds_exists (qn.liveAt t) hi0 (k1, x) hk1
        obtain ⟨hk1sc, _, hscb0, _⟩ := hxrange lo0 hi0 hz0 b0 hb0
        have hx0 := ReachR.inner z qn lo0 hi0 k1 x b0 hz0 hqn hql hb0
        have hnb0 := (childBounds_isNext _ hi0 (KNode.liveAt_order qn t) _ _ hb0).2
        have hqold : ∀ r' ∈ qn.liveAt t, UpperBound hi0 r'.1 := fun r' hr' =>
          (hR z lo0 hi0 qn hz0 hqn r' hr').2
        -- a compare value of q after k1 is above sc
        have habove : ∀ r' ∈ qn.liveAt t, k1 < r'.1 → sc < r'.1 := by
          intro r' hr' hlt
          rcases hnb0 with ⟨_, hall⟩ | ⟨nx, hnx, hbn, _, hmin⟩
          · have := hall r' hr'; omega
          · rw [hbn] at hscb0; simp only [UpperBound] at hscb0
            have := hmin r' hr' hlt; omega
        rcases hq2 c z' hcz with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · rw [h1, h2] at hb ⊢
          refine Or.inr (Or.inr ⟨rfl, ite_zero_eq sc lo (by omega), _, b0, hx0, ?_⟩)
          refine isNext_hiLE2 _ _ hi0 hi k1 sc b0 b hnb0
            (childBounds_isNext _ hi hms _ _ hb).2 (Or.inl hhi) hqold ?_
          intro r' hr' hlt
          rcases hq2 r'.1 r'.2 hr' with ⟨h3, _⟩ | ⟨_, h3⟩
          · omega
          · exact ⟨r', h3, by omega, Nat.le_refl _⟩
        · by_cases hck : c = k1
          · have hz'x := hk1u z' (hck ▸ h2)
            rw [hck, hz'x] at hb ⊢
            have hbF : b = some sc := by
              refine isNext_unique _ hi k1 b (some sc) (childBounds_isNext _ hi hms _ _ hb).2 ?_
              right
              refine ⟨(sc, S), hq2sc, rfl, hk1sc, ?_⟩
              intro r' hr' hlt
              rcases hq2 r'.1 r'.2 hr' with ⟨h3, _⟩ | ⟨_, h3⟩
              · simp only; omega
              · have := habove r' h3 hlt; simp only; omega
            refine Or.inr (Or.inl ⟨rfl, hbF, _, b0, hx0, ?_⟩)
            by_cases hk : k1 = 0
            · rw [hk]; simp only [beq_self_eq_true, ↓reduceIte]; exact hlo
            · have e1 := ite_zero_eq k1 lo hk; have e2 := ite_zero_eq k1 lo0 hk; omega
          · have hz'x : z' ≠ x := fun h => hck (honly z c hq ⟨qn, hqn, h ▸ h2⟩).2
            have hz'S : z' ≠ S := fun h => hSfree z c hq ⟨qn, hqn, h ▸ h2⟩
            have hlater : ∀ r' ∈ qn2.liveAt t, c < r'.1 →
                ∃ r0 ∈ qn.liveAt t, c < r0.1 ∧ r0.1 ≤ r'.1 := by
              intro r' hr' hlt
              rcases hq2 r'.1 r'.2 hr' with ⟨h3, _⟩ | ⟨_, h3⟩
              · have hck' : c < k1 := by
                  rcases Nat.lt_or_ge c k1 with hck' | hck'
                  · exact hck'
                  · have := habove (c, z') h2 (by simp only; omega); simp only at this; omega
                exact ⟨(k1, x), hk1, hck', by simp only; omega⟩
              · exact ⟨r', h3, hlt, Nat.le_refl _⟩
            obtain ⟨lo1, hi1, h3, h4, h5⟩ := old_child_step N1 t r hR z qn lo0 lo hi0 hi hz0 hqn hql
              hlo hhi _ hms c z' z' b h2 hb hlater
            exact Or.inl ⟨hz'x, hz'S, lo1, hi1, h3, h4, h5⟩
      · have hm0 : N1 z = some m := by rw [← hN2 z hzq hzx hzS]; exact hm
        have hu := reachR_tReach N1 t r z lo0 hi0 hz0
        obtain ⟨hz'x, hz'S⟩ := hchild z c z' hu ⟨m, hm0, hcz⟩ hzq
        obtain ⟨lo1, hi1, h3, h4, h5⟩ := old_child_step N1 t r hR z m lo0 lo hi0 hi hz0 hm0 hml
          hlo hhi _ hms c z' z' b hcz hb (fun r' hr' hlt => ⟨r', hr', hlt, Nat.le_refl _⟩)
        exact Or.inl ⟨hz'x, hz'S, lo1, hi1, h3, h4, h5⟩
    · subst hhs
      rw [hzF, hN2x] at hm; cases hm
      obtain ⟨hc1, hc2⟩ := hf c z' hcz
      have hxl : xn.leaf = false := by rw [← hfl]; exact hml
      obtain ⟨b0, hb0⟩ := childBounds_exists (xn.liveAt t) hi0 (c, z') hc1
      have hz'0 := ReachR.inner x xn lo0 hi0 c z' b0 hx0 hxn hxl hb0
      obtain ⟨hz'x, hz'S⟩ := hxchild c z' hc1
      refine Or.inl ⟨hz'x, hz'S, _, b0, hz'0, ?_, ?_⟩
      · by_cases hk : c = 0
        · subst hk; simp only [beq_self_eq_true, ↓reduceIte]; exact hlo
        · have e1 := ite_zero_eq c lo hk; have e2 := ite_zero_eq c lo0 hk; omega
      · obtain ⟨zs, hzs⟩ := hsc
        exact isNext_hiLE2 _ _ hi0 (some sc) c c b0 b
          (childBounds_isNext _ hi0 (KNode.liveAt_order xn t) _ _ hb0).2
          (childBounds_isNext _ _ hms _ _ hb).2 (Or.inr ⟨(sc, zs), hzs, hc2, HiLE.refl _⟩)
          (fun r' hr' => (hR x lo0 hi0 xn hx0 hxn r' hr').2)
          (fun r' hr' hlt => ⟨r', (hf r'.1 r'.2 hr').1, hlt, Nat.le_refl _⟩)
    · subst hzS
      rw [hls]
      rw [hN2S] at hm; cases hm
      have hxl : xn.leaf = false := by rw [← hsl]; exact hml
      obtain ⟨c0', hc0', hc1, hceq⟩ := hs c z' hcz
      simp only [hxl, and_true] at hceq
      obtain ⟨b0, hb0⟩ := childBounds_exists (xn.liveAt t) hi0 (c0', z') hc1
      have hz'0 := ReachR.inner x xn lo0 hi0 c0' z' b0 hx0 hxn hxl hb0
      obtain ⟨hz'x, hz'S⟩ := hxchild c0' z' hc1
      refine Or.inl ⟨hz'x, hz'S, _, b0, hz'0, ?_, ?_⟩
      · rw [ite_zero_eq c0' lo0 (by omega)]
        by_cases hcs : c0' = sc
        · simp only [hcs, ↓reduceIte] at hceq
          subst hceq
          simp only [beq_self_eq_true, ↓reduceIte]
          omega
        · simp only [hcs, ↓reduceIte] at hceq
          rw [hceq, ite_zero_eq c0' sc (by omega)]
          exact Nat.le_refl _
      · refine isNext_hiLE2 _ _ hi0 hi c0' c b0 b
          (childBounds_isNext _ hi0 (KNode.liveAt_order xn t) _ _ hb0).2
          (childBounds_isNext _ _ hms _ _ hb).2 (Or.inl hhi)
          (fun r' hr' => (hR x lo0 hi0 xn hx0 hxn r' hr').2) ?_
        intro r' hr' hlt
        obtain ⟨c0'', hc0'', hc1', hceq'⟩ := hs r'.1 r'.2 hr'
        simp only [hxl, and_true] at hceq'
        by_cases hcs' : c0'' = sc
        · simp only [hcs', ↓reduceIte] at hceq'; omega
        · simp only [hcs', ↓reduceIte] at hceq'
          refine ⟨(c0'', r'.2), hc1', ?_, by simp only; omega⟩
          simp only
          by_cases hcs : c0' = sc
          · omega
          · simp only [hcs, ↓reduceIte] at hceq; omega
  · intro z lo hi m c z' _ hG hm hml hcz
    rcases hG with ⟨hzx, hzS, lo0, hi0, hz0, _, _⟩ | ⟨hzF, _, lo0, hi0, hx0, _⟩ |
      ⟨hzS, _, lo0, hi0, hx0, _⟩
    · have hzq : z ≠ q := by intro h; rw [h, hN2q] at hm; cases hm; rw [hq2l] at hml; cases hml
      have hm0 : N1 z = some m := by rw [← hN2 z hzq hzx hzS]; exact hm
      obtain ⟨hz'x, hz'S⟩ := hchild z c z' (reachR_tReach N1 t r z lo0 hi0 hz0)
        ⟨m, hm0, hcz⟩ hzq
      exact Or.inl ⟨hz'x, hz'S, 0, none, ReachR.seg z m lo0 hi0 c z' hz0 hm0 hml hcz,
        Nat.le_refl _, HiLE.refl _⟩
    · subst hzF
      rw [hN2x] at hm; cases hm
      have hc1 := (hf c z' hcz).1
      obtain ⟨hz'x, hz'S⟩ := hxchild c z' hc1
      exact Or.inl ⟨hz'x, hz'S, 0, none,
        ReachR.seg z xn lo0 hi0 c z' hx0 hxn (by rw [← hfl]; exact hml) hc1, Nat.le_refl _,
        HiLE.refl _⟩
    · subst hzS
      rw [hN2S] at hm; cases hm
      obtain ⟨c0', _, hc1, _⟩ := hs c z' hcz
      obtain ⟨hz'x, hz'S⟩ := hxchild c0' z' hc1
      exact Or.inl ⟨hz'x, hz'S, 0, none,
        ReachR.seg x xn lo0 hi0 c0' z' hx0 hxn (by rw [← hsl]; exact hml) hc1, Nat.le_refl _,
        HiLE.refl _⟩
  · intro z lo hi m _ hG hm
    rcases hG with ⟨hzx, hzS, lo0, hi0, hz0, hlo, hhi⟩ | ⟨hzF, hhs, lo0, hi0, hx0, hlo⟩ |
      ⟨hzS, hls, lo0, hi0, hx0, hhi⟩
    · by_cases hzq : z = q
      · subst hzq
        rw [hN2q] at hm; cases hm
        obtain ⟨b0, hb0⟩ := childBounds_exists (qn.liveAt t) hi0 (k1, x) hk1
        obtain ⟨_, hlosc, _, hhisc⟩ := hxrange lo0 hi0 hz0 b0 hb0
        have hqr := hR z lo0 hi0 qn hz0 hqn
        intro q' hq'
        simp only [hq2l, Bool.false_eq_true, ↓reduceIte]
        rcases hq2 q'.1 q'.2 hq' with ⟨h1, _⟩ | ⟨_, h3⟩
        · rw [h1]
          exact ⟨Or.inr (by omega), upperBound_of_hiLE hi0 hi sc hhi hhisc⟩
        · obtain ⟨h4, h5⟩ := hqr q' h3
          simp only [hql, Bool.false_eq_true, ↓reduceIte] at h4
          exact ⟨by omega, upperBound_of_hiLE hi0 hi q'.1 hhi h5⟩
      · have hm0 : N1 z = some m := by rw [← hN2 z hzq hzx hzS]; exact hm
        exact nodeRange_wider m t lo0 lo hi0 hi (hR z lo0 hi0 m hz0 hm0) hlo hhi
    · subst hhs
      rw [hzF, hN2x] at hm; cases hm
      have hxr := hR x lo0 hi0 xn hx0 hxn
      intro q' hq'
      obtain ⟨h1, h2⟩ := hf q'.1 q'.2 hq'
      obtain ⟨h3, _⟩ := hxr q' h1
      refine ⟨?_, by simp only [UpperBound]; exact h2⟩
      rw [hfl]
      cases hxl : xn.leaf with
      | true => simp only [hxl, ↓reduceIte] at h3 ⊢; omega
      | false => simp only [hxl, Bool.false_eq_true, ↓reduceIte] at h3 ⊢; omega
    · subst hzS
      rw [hls]
      rw [hN2S] at hm; cases hm
      have hxr := hR x lo0 hi0 xn hx0 hxn
      intro q' hq'
      obtain ⟨c0', hc0', hc1, hceq⟩ := hs q'.1 q'.2 hq'
      obtain ⟨_, h4⟩ := hxr _ hc1
      have hup : UpperBound hi q'.1 := by
        have := upperBound_of_hiLE hi0 hi c0' hhi h4
        cases hi with
        | none => trivial
        | some h => simp only [UpperBound] at this ⊢; by_cases hcs : c0' = sc ∧ xn.leaf = false
                    · simp only [hcs, and_self, ↓reduceIte] at hceq; omega
                    · simp only [hcs, ↓reduceIte] at hceq; omega
      refine ⟨?_, hup⟩
      rw [hsl]
      cases hxl : xn.leaf with
      | true => simp only [hxl, ↓reduceIte, Bool.true_eq_false, and_false] at hceq ⊢; omega
      | false =>
        simp only [hxl, Bool.false_eq_true, ↓reduceIte, and_true] at hceq ⊢
        by_cases hcs : c0' = sc
        · simp only [hcs, ↓reduceIte] at hceq; exact Or.inl hceq
        · simp only [hcs, ↓reduceIte] at hceq; right; omega

end SIS.Tree
