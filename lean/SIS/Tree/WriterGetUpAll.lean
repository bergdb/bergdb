/-
The upward delete in full at the writer's level (bergdb 024-22): the stop node's
bitmap or LE-b, or a stop at a segment leaf; the tree and the reading together
(`writerWP_deleteUpward_up`).
-/
import SIS.Tree.WriterGetUpLeb

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- `treeOK_up_inner` with the stop node relinked by f (LE-b): the tree after the upward delete at tree level, the stop node X s's klong
K (s + 1) to the chain X (s + 1) .. X D deleted (N' agrees with N but at X s and
the chain): a tree from the same root, which reaches only what N reached but the
chain. -/
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

/-- `tReach_up_sub` with the stop node relinked: after the upward delete at tree level, what N' reaches N reached, and it is
no node of the chain; a link of a node N' reaches is one of N. -/
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

/-- The state after the upward delete's stop node, before root collapse: a tree
with what root collapse keeps (`CollGetInv`), from the facts of the state before
and the frame of the stop node's change (its live klongs name what it named, by a
compare value map f). -/
theorem collGetInv_after_up (c : Ctx) (base : View BVal) (X : Nat → NodeId) (Nn : Nat → KNode)
    (K : Nat → Nat) (depth : Nat) (w : W)
    (hlk : ∀ i, i ≤ depth → w.nodes.lookup (X i) = some (Nn i))
    (htk : ∀ i, i ≤ depth → w.taken.contains (X i) = false)
    (hdist : ∀ i i', i ≤ depth → i' ≤ depth → X i = X i' → i = i')
    (hT : TreeOK (wNode c.p base w) c.i w.top.rootKey)
    (hwf : ∀ x xn, TReach (wNode c.p base w) c.i w.top.rootKey x → wNode c.p base w x = some xn →
      klongsWf xn.ks = true)
    (hRt : ∀ y, TReach (wNode c.p base w) c.i w.top.rootKey y → w.taken.contains y = false)
    (hTimesR : ∀ y yn, TReach (wNode c.p base w) c.i w.top.rootKey y → wNode c.p base w y = some yn →
      ∀ s, Klong.time s ∈ yn.ks → s ≤ c.i)
    (hICE : InnerChildrenExist (wNode c.p base w) c.i w.top.rootKey)
    (hfit : PathsFit (wNode c.p base w) c.i w.top.rootKey c.p.fuel)
    (hnovalAll : ∀ y yn, wNode c.p base w y = some yn → wValue base w y = none)
    (hreach : ∀ i, i ≤ depth → TReach (wNode c.p base w) c.i w.top.rootKey (X i))
    (hlinkK : ∀ i, 0 < i → i ≤ depth → (K i, X i) ∈ (Nn (i - 1)).liveAt c.i)
    (stop : Nat) (w' : W) (sn' : KNode) (f : Nat → Nat) (hsD : stop < depth)
    (ht : w'.taken = w.taken) (htop : w'.top = w.top) (hv : w'.vals = w.vals)
    (hnodes : ∀ y, y ≠ X stop → (∀ k, stop < k → k ≤ depth → y ≠ X k) →
      w'.nodes.lookup y = w.nodes.lookup y)
    (hsn' : w'.nodes.lookup (X stop) = some sn') (hsl' : sn'.leaf = (Nn stop).leaf)
    (hsw' : klongsWf sn'.ks = true) (hst' : ∀ s, Klong.time s ∈ sn'.ks → s ≤ c.i)
    (hlive' : ∀ c' z, (c', z) ∈ sn'.liveAt c.i →
      ∃ c0, (c0, z) ∈ (Nn stop).liveAt c.i ∧ c0 ≠ K (stop + 1) ∧ f c0 = c') :
    CollGetInv c base w' w' := by
  have hN : ∀ i, i ≤ depth → wNode c.p base w (X i) = some (Nn i) := fun i hi => by
    simp only [wNode, htk i hi, Bool.false_eq_true, ↓reduceIte, hlk i hi]
  -- the tree after, at tree level
  have hagree : ∀ u, u ≠ X stop → (∀ i, stop < i → i ≤ depth → u ≠ X i) →
      wNode c.p base w' u = wNode c.p base w u := by
    intro u hus hnc
    simp only [wNode, ht, hnodes u hus hnc]
  have hsnw : wNode c.p base w' (X stop) = some sn' := by
    simp only [wNode, ht, htk stop (by omega), Bool.false_eq_true, ↓reduceIte, hsn']
  have hlive1 : ∀ c' z, (c', z) ∈ sn'.liveAt c.i → ∃ c0, (c0, z) ∈ (Nn stop).liveAt c.i ∧ c0 ≠ K (stop + 1) :=
    fun c' z h => by obtain ⟨c0, h1, h2, _⟩ := hlive' c' z h; exact ⟨c0, h1, h2⟩
  have hdist' : ∀ i i', stop ≤ i → i ≤ depth → stop ≤ i' → i' ≤ depth → X i = X i' → i = i' :=
    fun i i' _ h2 _ h4 he => hdist i i' h2 h4 he
  have hNs : ∀ i, stop ≤ i → i ≤ depth → wNode c.p base w (X i) = some (Nn i) := fun i _ h2 => hN i h2
  have hlinks : ∀ i, stop < i → i ≤ depth → (K i, X i) ∈ (Nn (i - 1)).liveAt c.i :=
    fun i h1 h2 => hlinkK i (by omega) h2
  rw [← htop] at hT hwf hRt hTimesR hICE hfit hreach
  have hT' := treeOK_up_tr (wNode c.p base w) (wNode c.p base w') c.i w'.top.rootKey X Nn K stop depth
    hsD hT (hreach stop (by omega)) hNs hlinks hdist' hagree sn' hsnw f hlive'
  have hsub := tReach_up_sub_tr (wNode c.p base w) (wNode c.p base w') c.i w'.top.rootKey X Nn K stop depth
    hsD hT (hreach stop (by omega)) hNs hlinks hdist' hagree sn' hsnw hlive1
  have hlsub := tLink_up_sub_tr (wNode c.p base w) (wNode c.p base w') c.i w'.top.rootKey X Nn K stop depth
    hsD hT (hreach stop (by omega)) hNs hlinks hdist' hagree sn' hsnw hlive1
  have hV : wValue base w' = wValue base w := wValue_congr' base w' w ht hv
  -- a reached node's node after: the stop node's, or the one before
  have hnode : ∀ y yn, TReach (wNode c.p base w') c.i w'.top.rootKey y → wNode c.p base w' y = some yn →
      (y = X stop ∧ yn = sn') ∨ wNode c.p base w y = some yn := by
    intro y yn hy hyn
    by_cases hys : y = X stop
    · left; rw [hys, hsnw] at hyn; exact ⟨hys, (Option.some.inj hyn).symm⟩
    · right; rw [← hagree y hys (hsub y hy).2]; exact hyn
  show CollGetInv c base w' w'
  refine ⟨⟨hT', fun y hy => by rw [ht]; exact hRt y (hsub y hy).1, ?_, ?_⟩, fun _ => rfl, ?_, ?_, ?_⟩
  · intro y yn hy hyn
    rcases hnode y yn hy hyn with ⟨_, rfl⟩ | h
    · exact hst'
    · exact hTimesR y yn (hsub y hy).1 h
  · intro y yn cc z hy hyn hyl hcz
    have hzR : TReach (wNode c.p base w') c.i w'.top.rootKey z := TReach.link hy ⟨yn, hyn, hcz⟩
    obtain ⟨cc0, hl⟩ := hlsub y cc z hy ⟨yn, hyn, hcz⟩
    obtain ⟨m0, hm0, hcm0⟩ := hl
    by_cases hzs : z = X stop
    · exact ⟨sn', by rw [hzs]; exact hsnw⟩
    · rw [hagree z hzs (hsub z hzR).2]
      have hyN := (hsub y hy).1
      have hm0l : m0.leaf = false := by
        rcases hnode y yn hy hyn with ⟨hys, rfl⟩ | h
        · rw [hys, hN stop (by omega)] at hm0
          cases hm0
          rw [← hsl']; exact hyl
        · rw [h] at hm0; cases hm0; exact hyl
      exact hICE y m0 cc0 z hyN hm0 hm0l hcm0
  · intro z k hz
    apply hfit z k
    induction hz with
    | root => exact PathLen.root
    | link hx hl ih => obtain ⟨c0, h0⟩ := hlsub _ _ _ hx.reach hl; exact PathLen.link ih h0
  · intro y yn hy hyn
    rcases hnode y yn hy hyn with ⟨_, rfl⟩ | h
    · exact hsw'
    · exact hwf y yn (hsub y hy).1 h
  · intro y yn hy hyn
    rw [hV]
    rcases hnode y yn hy hyn with ⟨hys, _⟩ | h
    · rw [hys]; exact hnovalAll _ _ (hN stop (by omega))
    · exact hnovalAll y yn h


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

set_option linter.unusedSimpArgs false in
/-- `writerWP_deleteUpward_inner_get` with LE-b too: the climb stops at a segment
leaf, at an inner node whose klong to the chain is not the empty key's (a bitmap,
with room), or at an inner node whose empty key's klong names the chain (LE-b,
with room); `hcoll`, `hleafQ` and `hcollLeb` give what follows. -/
theorem writerWP_deleteUpward_up_get (c : Ctx) (base : View BVal) (X : Nat → NodeId)
    (Nn : Nat → KNode) (K : Nat → Nat) (depth cv : Nat) (pre : List Nat) (rk : NodeId)
    (w : W) (Q : W → Prop) (hdepth : 0 < depth) (hfuel : 1 ≤ c.p.fuel)
    (hp : ∀ i, i ≤ depth → (w.path[i]?).map (·.2) = some (X i))
    (hk : ∀ i, 0 < i → i ≤ depth → w.path[i]? = some (some (K i), X i))
    (hlk : ∀ i, i ≤ depth → w.nodes.lookup (X i) = some (Nn i))
    (htk : ∀ i, i ≤ depth → w.taken.contains (X i) = false)
    (htimes : ∀ i, i ≤ depth → ∀ s, Klong.time s ∈ (Nn i).ks → s ≤ c.i)
    (hdist : ∀ i i', i ≤ depth → i' ≤ depth → X i = X i' → i = i')
    (hne : bitsUnion (Nn depth).lastBitmap ((Nn depth).bitsOf cv) ≠ (Nn depth).lastBitmap)
    (hall : (Nn depth).allKeysIn (bitsUnion (Nn depth).lastBitmap ((Nn depth).bitsOf cv)) = true)
    (hleaf : (Nn depth).leaf = true)
    (hT : TreeOK (wNode c.p base w) c.i w.top.rootKey)
    (hR : RangeOrder (wNode c.p base w) c.i w.top.rootKey)
    (hwf : ∀ x xn, TReach (wNode c.p base w) c.i w.top.rootKey x → wNode c.p base w x = some xn →
      klongsWf xn.ks = true)
    (hreach : ∀ i, i ≤ depth → TReach (wNode c.p base w) c.i w.top.rootKey (X i))
    (hlinkK : ∀ i, 0 < i → i ≤ depth → (K i, X i) ∈ (Nn (i - 1)).liveAt c.i)
    (hnoval : ∀ i, i ≤ depth → wValue base w (X i) = none)
    (hrk : segRootR (wNode c.p base w) c.i c.p.fuel pre w.top.rootKey = some rk) (hcv : cv ∉ pre)
    (hvisL : (X depth, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk)
    (huniq : ∀ key' x m, keyWf key' = true →
      (x, cv) ∈ fromVisits (wNode c.p base w) c.i c.p.fuel key' w.top.rootKey →
      (x, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk → wNode c.p base w x = some m →
      m.leaf = true → key' = pre ++ [cv])
    (hstopOK : ∀ s, s < depth → (∀ i, s < i → i < depth →
        (Nn i).allKeysIn (bitsUnion (Nn i).lastBitmap ((Nn i).bitsOf (K (i + 1)))) = true) →
      (∀ k, s < k → k ≤ depth → (Nn k).firstTime ≠ some c.i) ∧
      (((Nn s).leaf = true ∨ K (s + 1) ≠ 0) → (Nn s).size + 1 < c.p.M ∧
        deadOver c.p ((Nn s).setAt ((Nn s).size - 1)
          (.del (bitsUnion (Nn s).lastBitmap ((Nn s).bitsOf (K (s + 1)))))) = false ∧
        deadOver c.p ((Nn s).add c.i (.del (bitsUnion (Nn s).lastBitmap ((Nn s).bitsOf (K (s + 1)))))) =
          false) ∧
      ((Nn s).leaf = false → K (s + 1) = 0 → (Nn s).size + 3 ≤ c.p.M ∧
        ∀ b1 b2 e jcv jy, deadOver c.p (lebNode (Nn s) c.i b1 b2 e jcv jy) = false))
    (hmerges : c.p.merges = false)
    (hcoll : ∀ (seg stop : Nat) (w' : W) (sn' : KNode), stop < depth →
      (∀ i, stop < i → i < depth →
        (Nn i).allKeysIn (bitsUnion (Nn i).lastBitmap ((Nn i).bitsOf (K (i + 1)))) = true) →
      w'.taken = w.taken → w'.top = w.top → w'.vals = w.vals →
      (∀ y, y ≠ X stop → (∀ k, stop < k → k ≤ depth → y ≠ X k) → w'.nodes.lookup y = w.nodes.lookup y) →
      w'.nodes.lookup (X stop) = some sn' → sn'.leaf = (Nn stop).leaf → klongsWf sn'.ks = true →
      (∀ s, Klong.time s ∈ sn'.ks → s ≤ c.i) →
      (∀ c' z, (c', z) ∈ sn'.liveAt c.i ↔ (c', z) ∈ (Nn stop).liveAt c.i ∧ c' ≠ K (stop + 1)) →
      (∀ key', keyWf key' = true →
        wGet c.p c.i base w' key' = if pre ++ [cv] == key' then none else wGet c.p c.i base w key') →
      WriterWP (collapseRoot (pre ++ [cv]) seg c.p.fuel) c w' (fun _ w'' => Q w''))
    (hleafQ : ∀ (stop : Nat) (w' : W) (sn' : KNode), stop < depth →
      (∀ i, stop < i → i < depth →
        (Nn i).allKeysIn (bitsUnion (Nn i).lastBitmap ((Nn i).bitsOf (K (i + 1)))) = true) →
      w'.taken = w.taken → w'.top = w.top → w'.vals = w.vals →
      (∀ y, y ≠ X stop → (∀ k, stop < k → k ≤ depth → y ≠ X k) → w'.nodes.lookup y = w.nodes.lookup y) →
      w'.nodes.lookup (X stop) = some sn' → sn'.leaf = (Nn stop).leaf → klongsWf sn'.ks = true →
      (∀ s, Klong.time s ∈ sn'.ks → s ≤ c.i) →
      (∀ c' z, (c', z) ∈ sn'.liveAt c.i ↔ (c', z) ∈ (Nn stop).liveAt c.i ∧ c' ≠ K (stop + 1)) →
      (∀ key', keyWf key' = true →
        wGet c.p c.i base w' key' = if pre ++ [cv] == key' then none else wGet c.p c.i base w key') →
      Q w')
    (hcollLeb : ∀ (seg stop : Nat) (w' : W) (sn' : KNode) (jcv : Nat) (jy : NodeId), stop < depth →
      (∀ i, stop < i → i < depth →
        (Nn i).allKeysIn (bitsUnion (Nn i).lastBitmap ((Nn i).bitsOf (K (i + 1)))) = true) →
      w'.taken = w.taken → w'.top = w.top → w'.vals = w.vals →
      (∀ y, y ≠ X stop → (∀ k, stop < k → k ≤ depth → y ≠ X k) → w'.nodes.lookup y = w.nodes.lookup y) →
      w'.nodes.lookup (X stop) = some sn' → sn'.leaf = (Nn stop).leaf → klongsWf sn'.ks = true →
      (∀ s, Klong.time s ∈ sn'.ks → s ≤ c.i) → K (stop + 1) = 0 →
      (jcv, jy) ∈ (Nn stop).liveAt c.i → 0 < jcv →
      (∀ c' z, (c', z) ∈ sn'.liveAt c.i ↔
        (c' = 0 ∧ z = jy) ∨ ((c', z) ∈ (Nn stop).liveAt c.i ∧ c' ≠ 0 ∧ c' ≠ jcv)) →
      (∀ key', keyWf key' = true →
        wGet c.p c.i base w' key' = if pre ++ [cv] == key' then none else wGet c.p c.i base w key') →
      WriterWP (collapseRoot (pre ++ [cv]) seg c.p.fuel) c w' (fun _ w'' => Q w'')) :
    WriterWP (deleteUpward (X depth) depth cv (pre ++ [cv])) c w (fun _ w' => Q w') := by
  unfold deleteUpward
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_getNode_known _ _ c w (hlk depth (Nat.le_refl _))]
  have hne' : (bitsUnion (Nn depth).lastBitmap ((Nn depth).bitsOf cv) == (Nn depth).lastBitmap) = false := by
    simpa using hne
  simp only [hne', hall, Bool.false_eq_true, ↓reduceIte, Bool.not_true]
  rw [writerWP_bind]
  refine writerWP_mono (writerWP_climb c X Nn K depth w hp hk hlk) ?_
  rintro stop w1 ⟨hw1, hst, hbetween, hmadeOK, hstopNode, hself⟩
  have hw1' := hw1.symm
  subst hw1'
  have hsd : stop ≠ depth := fun h => by have := (hself h).1; omega
  have hsd' : (stop == depth) = false := by simpa using hsd
  simp only [hsd', Bool.false_eq_true, ↓reduceIte]
  have hsD : stop < depth := by omega
  obtain ⟨hnone, hbitRoom, hlebRoom⟩ := hstopOK stop hsD hbetween
  rw [writerWP_bind]
  refine (writerWP_note_iff _ c w _).mpr ?_
  generalize hw0 : ({ w with trail := "up.climb" :: w.trail } : W) = w0
  have h0n : w0.nodes = w.nodes := by rw [← hw0]
  have h0p : w0.path = w.path := by rw [← hw0]
  have h0t : w0.taken = w.taken := by rw [← hw0]
  have h0top : w0.top = w.top := by rw [← hw0]
  have h0v : w0.vals = w.vals := by rw [← hw0]
  rw [writerWP_bind, writerWP_get, writerWP_bind]
  refine writerWP_mono (writerWP_foldlM_getNode c (fun s n => if n.leaf = true then s + 1 else s)
    (List.take stop w0.path) 0 w0 ?_) ?_
  · intro e he
    obtain ⟨i, hie⟩ := List.mem_iff_getElem?.mp he
    rw [List.getElem?_take] at hie
    split at hie
    · rename_i hi
      have h1 := hp i (by omega)
      rw [← h0p, hie] at h1
      simp only [Option.map_some, Option.some.injEq] at h1
      rw [h1, h0n]
      exact ⟨_, hlk i (by omega)⟩
    · cases hie
  rintro seg w0' hw0'
  have hw0'' := hw0'.symm
  subst hw0''
  -- the loop: the chain's nodes unlinked
  let I : List Nat → W → Prop := fun rem v =>
    v.taken = w0.taken ∧ v.top = w0.top ∧ v.vals = w0.vals ∧ v.path = w0.path ∧
    (∀ y, (∀ k, stop < k → k ≤ depth → y ≠ X k) → v.nodes.lookup y = w0.nodes.lookup y) ∧
    (∀ j ∈ rem, j < depth - stop ∧ v.nodes.lookup (X (depth - j)) = some (Nn (depth - j))) ∧
    rem.Nodup
  rw [writerWP_bind]
  refine writerWP_mono (writerWP_forIn_inv c I _ ?_ (List.range (depth - stop)) w0
    ⟨rfl, rfl, rfl, rfl, fun _ _ => rfl, fun j hj => ⟨List.mem_range.mp hj, by
      rw [h0n]; exact hlk _ (by omega)⟩, List.nodup_range⟩) ?_
  · intro a rest v ⟨hvt, hvtop, hvv, hvp, hvn, hvrem, hnd⟩
    obtain ⟨ha, hva⟩ := hvrem a List.mem_cons_self
    simp only [writerWP_bind]
    refine writerWP_pathNode_known (depth - a) (X (depth - a)) c v
      (by rw [hvp, h0p]; exact hp _ (by omega)) _ ?_
    rw [writerWP_getNode_known _ _ c v hva]
    have hnm : ((Nn (depth - a)).firstTime == some c.i) = false := by
      simpa using hnone (depth - a) (by omega) (by omega)
    simp only [hnm, Bool.false_eq_true, ↓reduceIte, writerWP_bind]
    refine (writerWP_note_iff _ c v _).mpr ?_
    refine writerWP_mono (writerWP_unlink_frameP _ _ c _ hva) ?_
    rintro _ v2 ⟨h2t, h2top, _, h2v, h2p, _, h2l⟩
    simp only [writerWP_pure]
    refine ⟨by first | rfl | trivial, h2t.trans hvt, h2top.trans hvtop, h2v.trans hvv, h2p.trans hvp, fun y hy => ?_,
      fun j hj => ?_, (List.nodup_cons.mp hnd).2⟩
    · rw [h2l y (hy (depth - a) (by omega) (by omega)), hvn y hy]
    · obtain ⟨hj1, hj2⟩ := hvrem j (List.mem_cons_of_mem _ hj)
      refine ⟨hj1, ?_⟩
      have hja : j ≠ a := fun he => (List.nodup_cons.mp hnd).1 (he ▸ hj)
      rw [h2l _ (fun he => hja (by have := hdist _ _ (by omega) (by omega) he; omega))]
      exact hj2
  rintro _ w2 ⟨h2t, h2top, h2v, h2p, h2n, _, _⟩
  simp only [writerWP_bind]
  refine writerWP_pathNode_known stop (X stop) c w2 (by rw [h2p, h0p]; exact hp stop (by omega)) _ ?_
  refine writerWP_klongAt_known (stop + 1) (K (stop + 1)) (X (stop + 1)) c w2
    (by rw [h2p, h0p]; exact hk _ (by omega) (by omega)) _ ?_
  have hls2 : w2.nodes.lookup (X stop) = some (Nn stop) := by
    rw [h2n _ (fun k h1 h2 he => by have := hdist _ _ (by omega) (by omega) he; omega), h0n]
    exact hlk stop (by omega)
  rw [writerWP_getNode_known _ _ c w2 hls2]
  refine writerWP_ghOf_cached _ _ c w2 hls2 _ (fun gh => ?_)
  have hst_t : ∀ s', Klong.time s' ∈ (Nn stop).ks → s' ≤ c.i := htimes stop (by omega)
  have hsx : (K (stop + 1), X (stop + 1)) ∈ (Nn stop).liveAt c.i := by
    have := hlinkK (stop + 1) (by omega) (by omega); simpa using this
  have hneS : bitsUnion (Nn stop).lastBitmap ((Nn stop).bitsOf (K (stop + 1))) ≠ (Nn stop).lastBitmap := by
    apply KNode.delete_bitmap_changes_of_live
    rw [KNode.liveAt_of_times _ c.i hst_t] at hsx
    exact List.mem_map.mpr ⟨_, hsx, rfl⟩
  have hswf : klongsWf (Nn stop).ks = true := by
    have := hwf (X stop) (Nn stop) (hreach stop (by omega))
      (by simp only [wNode, htk stop (by omega), Bool.false_eq_true, ↓reduceIte, hlk stop (by omega)])
    exact this
  -- the chain's facts
  have hone : ∀ i, stop < i → i < depth → ∀ c' z, (c', z) ∈ (Nn i).liveAt c.i → z = X (i + 1) := by
    intro i h1 h2 c' z hm
    have ht := htimes i (by omega)
    have hm' : (c', z) ∈ (Nn i).live := by rw [← KNode.liveAt_of_times _ c.i ht]; exact hm
    have hc := allKeysIn_live_cv (Nn i) (K (i + 1)) (hbetween i h1 h2) c' z hm'
    have hl := hlinkK (i + 1) (by omega) (by omega)
    rw [show i + 1 - 1 = i by omega] at hl
    rw [KNode.liveAt_of_times _ c.i ht] at hl
    have hnd := KNode.live_keys_nodup (Nn i)
    have e1 := lookup_some_of_mem hnd hm'
    have e2 := lookup_some_of_mem hnd hl
    rw [hc] at e1
    rw [e1] at e2
    exact Option.some.inj e2
  have honly : ∀ c' z, (c', z) ∈ (Nn depth).liveAt c.i → c' = cv := by
    intro c' z hm
    have hm' : (c', z) ∈ (Nn depth).live := by
      rw [← KNode.liveAt_of_times _ c.i (htimes depth (Nat.le_refl _))]; exact hm
    exact allKeysIn_live_cv (Nn depth) cv hall c' z hm'
  -- the bitmap at the stop node, from any state with w2's nodes
  have hbit : ((Nn stop).leaf = true ∨ K (stop + 1) ≠ 0) →
      ∀ (v : W), v.nodes = w2.nodes → v.taken = w2.taken → v.top = w2.top → v.vals = w2.vals →
      ∀ (post : W → Prop), (∀ w3 n', w3.taken = w.taken → w3.top = w.top → w3.vals = w.vals →
        (∀ y, y ≠ X stop → (∀ k, stop < k → k ≤ depth → y ≠ X k) →
          w3.nodes.lookup y = w.nodes.lookup y) →
        w3.nodes.lookup (X stop) = some n' → n'.leaf = (Nn stop).leaf → klongsWf n'.ks = true →
        (∀ s, Klong.time s ∈ n'.ks → s ≤ c.i) →
        (∀ c' z, (c', z) ∈ n'.liveAt c.i ↔ (c', z) ∈ (Nn stop).liveAt c.i ∧ c' ≠ K (stop + 1)) →
        (∀ key', keyWf key' = true → wGet c.p c.i base w3 key' =
          if pre ++ [cv] == key' then none else wGet c.p c.i base w key') → post w3) →
      WriterWP (appendDeleteKlong (X stop) stop (K (stop + 1))) c v (fun _ w3 => post w3) := by
    intro hkind v hvn hvt hvtop hvv post hpost
    obtain ⟨hroom, hd1, hd2⟩ := hbitRoom hkind
    refine writerWP_mono (writerWP_appendDeleteKlong_room_frame (X stop) stop (K (stop + 1)) (Nn stop)
      c v (by rw [hvn]; exact hls2) hst_t hswf hneS hroom hd1 hd2) ?_
    rintro _ w3 ⟨h3t, h3top, h3v, _, _, _, n', h3n, hn'l, hn'w, hn't, hn'lk⟩
    have h3tw : w3.taken = w.taken := by rw [h3t, hvt, h2t, h0t]
    have h3top' : w3.top = w.top := by rw [h3top, hvtop, h2top, h0top]
    have h3v' : w3.vals = w.vals := by rw [h3v, hvv, h2v, h0v]
    have hfr : ∀ y, y ≠ X stop → (∀ k, stop < k → k ≤ depth → y ≠ X k) →
        w3.nodes.lookup y = w.nodes.lookup y := by
      intro y hys hnc
      rw [h3n, lookup_upsert]
      simp only [hys, ↓reduceIte]
      rw [hvn, h2n y hnc, h0n]
    have hsn3 : w3.nodes.lookup (X stop) = some n' := by rw [h3n, lookup_upsert]; simp
    have hlive' := liveAt_iff_of_delete_lookup (Nn stop) n' c.i (K (stop + 1)) hst_t hn't hn'lk
    refine hpost w3 n' h3tw h3top' h3v' hfr hsn3 hn'l hn'w hn't hlive' ?_
    intro key' hkw
    have hV3 : wValue base w3 = wValue base w := wValue_congr' base w3 w h3tw h3v'
    have hagree : ∀ u, TReach (wNode c.p base w) c.i w.top.rootKey u → u ≠ X stop →
        (∀ i, stop < i → i ≤ depth → u ≠ X i) → wNode c.p base w3 u = wNode c.p base w u := by
      intro u _ hus hnc
      simp only [wNode, h3tw, hfr u hus hnc]
    have hsnw : wNode c.p base w3 (X stop) = some n' := by
      simp only [wNode, h3tw, htk stop (by omega), Bool.false_eq_true, ↓reduceIte, hsn3]
    unfold wGet
    rw [hV3, h3top']
    cases hl : (Nn stop).leaf with
    | false =>
      have hK0 : K (stop + 1) ≠ 0 := by
        rcases hkind with h | h
        · rw [hl] at h; cases h
        · exact h
      exact getFromR_up_inner (wNode c.p base w) (wNode c.p base w3) (wValue base w) c.i c.p.fuel hfuel
        w.top.rootKey X Nn K stop depth hsD pre cv rk hT hR hwf (hreach stop (by omega))
        (fun i h1 h2 => by simp only [wNode, htk i h2, Bool.false_eq_true, ↓reduceIte, hlk i h2])
        (fun i h1 h2 => hlinkK i (by omega) h2) hone hleaf honly (fun i h1 h2 => hnoval i h2)
        (fun i h1 h2 he => by have := hdist i depth (by omega) (Nat.le_refl _) he; omega)
        hrk hcv hvisL huniq hagree n' hl hsnw (by rw [hn'l]; exact hl) hlive' key' hkw
    | true =>
      exact getFromR_up_leaf (wNode c.p base w) (wNode c.p base w3) (wValue base w) c.i c.p.fuel hfuel
        w.top.rootKey X Nn K stop depth hsD pre cv rk hT hR hwf (hreach stop (by omega))
        (fun i h1 h2 => by simp only [wNode, htk i h2, Bool.false_eq_true, ↓reduceIte, hlk i h2])
        (fun i h1 h2 => hlinkK i (by omega) h2) hone hleaf honly (fun i h1 h2 => hnoval i h2)
        (fun i h1 h2 he => by have := hdist i depth (by omega) (Nat.le_refl _) he; omega)
        hrk hcv hvisL huniq hagree n' hl hsnw (by rw [hn'l]; exact hl) hn'w hlive' key' hkw
  cases hsl : (Nn stop).leaf with
  | true =>
    simp only [↓reduceIte, writerWP_bind]
    refine (writerWP_note_iff _ c w2 _).mpr ?_
    refine hbit (Or.inl hsl) _ ?_ ?_ ?_ ?_ _ ?_
    rotate_left 4
    · intro w3 n' h3t h3top h3v hfr hsn3 hn'l hn'w hn't hlive' hread
      unfold afterDelete
      simp only [writerWP_bind, writerWP_read, hmerges, Bool.false_eq_true, ↓reduceIte, writerWP_pure]
      exact hleafQ stop w3 n' hsD hbetween h3t h3top h3v hfr hsn3 hn'l hn'w hn't hlive' hread
    all_goals rfl
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    split
    · simp only [writerWP_bind]; exact writerWP_throw _ _ _ _
    by_cases hK0 : K (stop + 1) = 0
    · -- LE-b
      have hK0' : (K (stop + 1) != 0) = false := by simp [hK0]
      simp only [hK0', Bool.false_eq_true, ↓reduceIte, writerWP_bind, hmerges]
      obtain ⟨hroomL, hdeadL⟩ := hlebRoom hsl hK0
      refine writerWP_mono (writerWP_emptyKeyNext_room_frame (X stop) stop (Nn stop) c w2 hls2 hswf hst_t
        hroomL hdeadL) ?_
      rintro _ w3 ⟨h3t, h3top, h3v, _, _, _, n', jcv, jy, h3n, hn'l, hn'w, hn't, hj, hj0, hmin, hn'lk⟩
      have h3tw : w3.taken = w.taken := by rw [h3t, h2t, h0t]
      have h3top' : w3.top = w.top := by rw [h3top, h2top, h0top]
      have h3v' : w3.vals = w.vals := by rw [h3v, h2v, h0v]
      have hfr : ∀ y, y ≠ X stop → (∀ k, stop < k → k ≤ depth → y ≠ X k) →
          w3.nodes.lookup y = w.nodes.lookup y := by
        intro y hys hnc
        rw [h3n, lookup_upsert]
        simp only [hys, ↓reduceIte]
        rw [h2n y hnc, h0n]
      have hsn3 : w3.nodes.lookup (X stop) = some n' := by rw [h3n, lookup_upsert]; simp
      have hlive' := liveAt_iff_of_leb_lookup (Nn stop) n' c.i jcv jy hst_t hn't hn'lk
      have hmin' : ∀ c' z, (c', z) ∈ (Nn stop).liveAt c.i → c' = 0 ∨ jcv ≤ c' := by
        intro c' z hm
        by_cases hc : c' = 0
        · exact Or.inl hc
        · right
          rw [KNode.liveAt_of_times _ c.i hst_t] at hm
          exact hmin c' z hm hc
      refine writerWP_mono (hcollLeb seg stop w3 n' jcv jy hsD hbetween h3tw h3top' h3v' hfr hsn3 hn'l hn'w
        hn't hK0 hj hj0 hlive' ?_) ?_
      · intro key' hkw
        have hV3 : wValue base w3 = wValue base w := wValue_congr' base w3 w h3tw h3v'
        have hagree : ∀ u, TReach (wNode c.p base w) c.i w.top.rootKey u → u ≠ X stop →
            (∀ i, stop < i → i ≤ depth → u ≠ X i) → wNode c.p base w3 u = wNode c.p base w u := by
          intro u _ hus hnc
          simp only [wNode, h3tw, hfr u hus hnc]
        have hsnw : wNode c.p base w3 (X stop) = some n' := by
          simp only [wNode, h3tw, htk stop (by omega), Bool.false_eq_true, ↓reduceIte, hsn3]
        unfold wGet
        rw [hV3, h3top']
        exact getFromR_up_leb (wNode c.p base w) (wNode c.p base w3) (wValue base w) c.i c.p.fuel hfuel
          w.top.rootKey X Nn K stop depth hsD pre cv rk hT hR hwf (hreach stop (by omega))
          (fun i h1 h2 => by simp only [wNode, htk i h2, Bool.false_eq_true, ↓reduceIte, hlk i h2])
          (fun i h1 h2 => hlinkK i (by omega) h2) hone hleaf honly (fun i h1 h2 => hnoval i h2)
          (fun i h1 h2 he => by have := hdist i depth (by omega) (Nat.le_refl _) he; omega)
          hrk hcv hvisL huniq hagree n' jy jcv hK0 hsl hj hj0 hmin' hsnw (by rw [hn'l]; exact hsl)
          hlive' key' hkw
      · intro _ w4 h4
        simp only [writerWP_pure]
        exact h4
    have hK0' : (K (stop + 1) != 0) = true := by simpa using hK0
    simp only [hK0', ↓reduceIte, writerWP_bind, hmerges, Bool.false_eq_true]
    refine hbit (Or.inr hK0) _ ?_ ?_ ?_ ?_ _ ?_
    rotate_left 4
    · intro w3 n' h3t h3top h3v hfr hsn3 hn'l hn'w hn't hlive' hread
      refine writerWP_mono (hcoll seg stop w3 n' hsD hbetween h3t h3top h3v hfr hsn3 hn'l hn'w hn't
        hlive' hread) ?_
      intro _ w4 h4
      simp only [writerWP_pure]
      exact h4
    all_goals rfl

/-- The upward delete at the writer's level, the tree and the reading: the stop
node a segment leaf or an inner node, its klong to the chain deleted by a bitmap
with room or, the empty key's, by LE-b with room; no node of the chain made by
the transaction; the merges off. The writer's tree after is a tree,
the key reads nothing and every other key as before; at the space root's segment
root collapse is part of it, at another segment `hcollSeg` gives it. -/
theorem writerWP_deleteUpward_up (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base)
    (X : Nat → NodeId) (Nn : Nat → KNode) (K : Nat → Nat) (depth cv : Nat) (pre : List Nat)
    (rk : NodeId) (w : W) (hdepth : 0 < depth) (hfuel : 1 ≤ c.p.fuel)
    (hp : ∀ i, i ≤ depth → (w.path[i]?).map (·.2) = some (X i))
    (hk : ∀ i, 0 < i → i ≤ depth → w.path[i]? = some (some (K i), X i))
    (hlk : ∀ i, i ≤ depth → w.nodes.lookup (X i) = some (Nn i))
    (htk : ∀ i, i ≤ depth → w.taken.contains (X i) = false)
    (htimes : ∀ i, i ≤ depth → ∀ s, Klong.time s ∈ (Nn i).ks → s ≤ c.i)
    (hdist : ∀ i i', i ≤ depth → i' ≤ depth → X i = X i' → i = i')
    (hne : bitsUnion (Nn depth).lastBitmap ((Nn depth).bitsOf cv) ≠ (Nn depth).lastBitmap)
    (hall : (Nn depth).allKeysIn (bitsUnion (Nn depth).lastBitmap ((Nn depth).bitsOf cv)) = true)
    (hleaf : (Nn depth).leaf = true)
    (hT : TreeOK (wNode c.p base w) c.i w.top.rootKey)
    (hR : RangeOrder (wNode c.p base w) c.i w.top.rootKey)
    (hwf : ∀ x xn, TReach (wNode c.p base w) c.i w.top.rootKey x → wNode c.p base w x = some xn →
      klongsWf xn.ks = true)
    (hRt : ∀ y, TReach (wNode c.p base w) c.i w.top.rootKey y → w.taken.contains y = false)
    (hTimesR : ∀ y yn, TReach (wNode c.p base w) c.i w.top.rootKey y → wNode c.p base w y = some yn →
      ∀ s, Klong.time s ∈ yn.ks → s ≤ c.i)
    (hICE : InnerChildrenExist (wNode c.p base w) c.i w.top.rootKey)
    (hfit : PathsFit (wNode c.p base w) c.i w.top.rootKey c.p.fuel)
    (hnovalAll : ∀ y yn, wNode c.p base w y = some yn → wValue base w y = none)
    (hreach : ∀ i, i ≤ depth → TReach (wNode c.p base w) c.i w.top.rootKey (X i))
    (hlinkK : ∀ i, 0 < i → i ≤ depth → (K i, X i) ∈ (Nn (i - 1)).liveAt c.i)
    (hrk : segRootR (wNode c.p base w) c.i c.p.fuel pre w.top.rootKey = some rk) (hcv : cv ∉ pre)
    (hvisL : (X depth, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk)
    (huniq : ∀ key' x m, keyWf key' = true →
      (x, cv) ∈ fromVisits (wNode c.p base w) c.i c.p.fuel key' w.top.rootKey →
      (x, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk → wNode c.p base w x = some m →
      m.leaf = true → key' = pre ++ [cv])
    (hstopOK : ∀ s, s < depth → (∀ i, s < i → i < depth →
        (Nn i).allKeysIn (bitsUnion (Nn i).lastBitmap ((Nn i).bitsOf (K (i + 1)))) = true) →
      (∀ k, s < k → k ≤ depth → (Nn k).firstTime ≠ some c.i) ∧
      (((Nn s).leaf = true ∨ K (s + 1) ≠ 0) → (Nn s).size + 1 < c.p.M ∧
        deadOver c.p ((Nn s).setAt ((Nn s).size - 1)
          (.del (bitsUnion (Nn s).lastBitmap ((Nn s).bitsOf (K (s + 1)))))) = false ∧
        deadOver c.p ((Nn s).add c.i (.del (bitsUnion (Nn s).lastBitmap ((Nn s).bitsOf (K (s + 1)))))) =
          false) ∧
      ((Nn s).leaf = false → K (s + 1) = 0 → (Nn s).size + 3 ≤ c.p.M ∧
        ∀ b1 b2 e jcv jy, deadOver c.p (lebNode (Nn s) c.i b1 b2 e jcv jy) = false))
    (hmerges : c.p.merges = false)
    (hcollSeg : ∀ seg, 0 < seg → ∀ w', CollGetInv c base w' w' →
      (∀ key', keyWf key' = true →
        wGet c.p c.i base w' key' = if pre ++ [cv] == key' then none else wGet c.p c.i base w key') →
      WriterWP (collapseRoot (pre ++ [cv]) seg c.p.fuel) c w' (fun _ w'' =>
        TreeOK (wNode c.p base w'') c.i w''.top.rootKey ∧ ∀ key', keyWf key' = true →
          wGet c.p c.i base w'' key' = if pre ++ [cv] == key' then none else wGet c.p c.i base w key')) :
    WriterWP (deleteUpward (X depth) depth cv (pre ++ [cv])) c w (fun _ w' =>
      TreeOK (wNode c.p base w') c.i w'.top.rootKey ∧ ∀ key', keyWf key' = true →
        wGet c.p c.i base w' key' = if pre ++ [cv] == key' then none else wGet c.p c.i base w key') := by
  have hN : ∀ i, i ≤ depth → wNode c.p base w (X i) = some (Nn i) := fun i hi => by
    simp only [wNode, htk i hi, Bool.false_eq_true, ↓reduceIte, hlk i hi]
  have hpost := collGetInv_after_up c base X Nn K depth w hlk htk hdist hT hwf hRt hTimesR hICE hfit
    hnovalAll hreach hlinkK
  have hcollAny : ∀ seg w', CollGetInv c base w' w' → (∀ key', keyWf key' = true →
      wGet c.p c.i base w' key' = if pre ++ [cv] == key' then none else wGet c.p c.i base w key') →
      WriterWP (collapseRoot (pre ++ [cv]) seg c.p.fuel) c w' (fun _ w'' =>
        TreeOK (wNode c.p base w'') c.i w''.top.rootKey ∧ ∀ key', keyWf key' = true →
          wGet c.p c.i base w'' key' = if pre ++ [cv] == key' then none else wGet c.p c.i base w key') := by
    intro seg w' hI hread
    by_cases hseg : seg = 0
    · subst hseg
      refine writerWP_mono (writerWP_collapseRoot_space_get (pre ++ [cv]) c base hvc w' c.p.fuel w' hI) ?_
      intro _ w'' h
      exact ⟨h.1.1, fun key' hkw => by rw [h.2.1 key']; exact hread key' hkw⟩
    · exact hcollSeg seg (by omega) w' hI hread
  apply writerWP_deleteUpward_up_get c base X Nn K depth cv pre rk w _ hdepth hfuel hp hk hlk htk
    htimes hdist hne hall hleaf hT hR hwf hreach hlinkK (fun i hi => hnovalAll _ _ (hN i hi))
    hrk hcv hvisL huniq hstopOK hmerges
  · intro seg stop w' sn' hsD _ ht htop hv hnodes hsn' hsl' hsw' hst' hlive' hread
    exact hcollAny seg w' (hpost stop w' sn' id hsD ht htop hv hnodes hsn' hsl' hsw' hst'
      (fun c' z h => ⟨c', ((hlive' c' z).mp h).1, ((hlive' c' z).mp h).2, rfl⟩)) hread
  · intro stop w' sn' hsD _ ht htop hv hnodes hsn' hsl' hsw' hst' hlive' hread
    exact ⟨(hpost stop w' sn' id hsD ht htop hv hnodes hsn' hsl' hsw' hst'
      (fun c' z h => ⟨c', ((hlive' c' z).mp h).1, ((hlive' c' z).mp h).2, rfl⟩)).1.1, hread⟩
  · intro seg stop w' sn' jcv jy hsD _ ht htop hv hnodes hsn' hsl' hsw' hst' hK0 hj hj0 hlive' hread
    refine hcollAny seg w' (hpost stop w' sn' (fun c' => if c' = jcv then 0 else c') hsD ht htop hv
      hnodes hsn' hsl' hsw' hst' ?_) hread
    intro c' z h
    rcases (hlive' c' z).mp h with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩
    · refine ⟨jcv, by rw [h2]; exact hj, by omega, ?_⟩
      simp [h1]
    · exact ⟨c', h1, by omega, by simp [h3]⟩

end SIS.Tree
