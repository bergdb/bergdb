/-
The upward delete keeps the writer's tree (bergdb 024-22, `OpTreeOK`): the
stop node's klong to the emptied chain deleted, the chain left out
(`treeOK_up_inner`).
-/
import SIS.Tree.WriterGetUpW

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- The tree after the upward delete at tree level, the stop node X s's klong
K (s + 1) to the chain X (s + 1) .. X D deleted (N' agrees with N but at X s and
the chain): a tree from the same root, which reaches only what N reached but the
chain. -/
theorem treeOK_up_inner (N N' : NodeId → Option KNode) (t : Time) (r : NodeId) (X : Nat → NodeId)
    (Nn : Nat → KNode) (K : Nat → Nat) (s D : Nat) (hsD : s < D)
    (hT : TreeOK N t r) (hXs : TReach N t r (X s))
    (hN : ∀ i, s ≤ i → i ≤ D → N (X i) = some (Nn i))
    (hlinkK : ∀ i, s < i → i ≤ D → (K i, X i) ∈ (Nn (i - 1)).liveAt t)
    (hdist : ∀ i i', s ≤ i → i ≤ D → s ≤ i' → i' ≤ D → X i = X i' → i = i')
    (hagree : ∀ u, u ≠ X s → (∀ i, s < i → i ≤ D → u ≠ X i) → N' u = N u)
    (sn' : KNode) (hsn' : N' (X s) = some sn')
    (hlive' : ∀ c z, (c, z) ∈ sn'.liveAt t → (c, z) ∈ (Nn s).liveAt t ∧ c ≠ K (s + 1)) :
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
  apply treeOK_dropSubtree N N' t r (X s) (X (s + 1)) (K (s + 1)) (Nn s) sn'
    (fun g => ∃ k, s < k ∧ k ≤ D ∧ g = X k) hT hXs (hN s (Nat.le_refl _) (by omega))
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

/-- After the upward delete at tree level, what N' reaches N reached, and it is
no node of the chain; a link of a node N' reaches is one of N. -/
theorem tReach_up_sub (N N' : NodeId → Option KNode) (t : Time) (r : NodeId) (X : Nat → NodeId)
    (Nn : Nat → KNode) (K : Nat → Nat) (s D : Nat) (hsD : s < D)
    (hT : TreeOK N t r) (hXs : TReach N t r (X s))
    (hN : ∀ i, s ≤ i → i ≤ D → N (X i) = some (Nn i))
    (hlinkK : ∀ i, s < i → i ≤ D → (K i, X i) ∈ (Nn (i - 1)).liveAt t)
    (hdist : ∀ i i', s ≤ i → i ≤ D → s ≤ i' → i' ≤ D → X i = X i' → i = i')
    (hagree : ∀ u, u ≠ X s → (∀ i, s < i → i ≤ D → u ≠ X i) → N' u = N u)
    (sn' : KNode) (hsn' : N' (X s) = some sn')
    (hlive' : ∀ c z, (c, z) ∈ sn'.liveAt t → (c, z) ∈ (Nn s).liveAt t ∧ c ≠ K (s + 1)) :
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
      obtain ⟨hcm', hc⟩ := hlive' c z hcm
      have hlN : TLink N t x c z := ⟨Nn s, by rw [hxs]; exact hN s (Nat.le_refl _) (by omega), hcm'⟩
      refine ⟨TReach.link hxN hlN, fun k h1 h2 he => ?_⟩
      rw [he] at hlN
      obtain ⟨hx1, hc1⟩ := hinto x c k hxN hlN h1 h2
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

/-- A link of a node N' reaches, after the upward delete at tree level, is one of N. -/
theorem tLink_up_sub (N N' : NodeId → Option KNode) (t : Time) (r : NodeId) (X : Nat → NodeId)
    (Nn : Nat → KNode) (K : Nat → Nat) (s D : Nat) (hsD : s < D)
    (hT : TreeOK N t r) (hXs : TReach N t r (X s))
    (hN : ∀ i, s ≤ i → i ≤ D → N (X i) = some (Nn i))
    (hlinkK : ∀ i, s < i → i ≤ D → (K i, X i) ∈ (Nn (i - 1)).liveAt t)
    (hdist : ∀ i i', s ≤ i → i ≤ D → s ≤ i' → i' ≤ D → X i = X i' → i = i')
    (hagree : ∀ u, u ≠ X s → (∀ i, s < i → i ≤ D → u ≠ X i) → N' u = N u)
    (sn' : KNode) (hsn' : N' (X s) = some sn')
    (hlive' : ∀ c z, (c, z) ∈ sn'.liveAt t → (c, z) ∈ (Nn s).liveAt t ∧ c ≠ K (s + 1)) :
    ∀ x c y, TReach N' t r x → TLink N' t x c y → TLink N t x c y := by
  intro x c y hx hl
  obtain ⟨m, hm, hcm⟩ := hl
  by_cases hxs : x = X s
  · rw [hxs, hsn'] at hm
    simp only [Option.some.injEq] at hm
    subst hm
    exact ⟨Nn s, by rw [hxs]; exact hN s (Nat.le_refl _) (by omega), (hlive' c y hcm).1⟩
  · have hxc := (tReach_up_sub N N' t r X Nn K s D hsD hT hXs hN hlinkK hdist hagree sn' hsn' hlive' x hx).2
    rw [hagree x hxs hxc] at hm
    exact ⟨m, hm, hcm⟩

/-- The upward delete at the writer's level, the tree and the reading: the stop
node with room, a segment leaf or an inner node whose klong to the chain is not
the empty key's, no node of the chain made by the transaction, the merges off. The writer's tree after is a tree,
the key reads nothing and every other key as before; at the space root's segment
root collapse is part of it, at another segment `hcollSeg` gives it. -/
theorem writerWP_deleteUpward_inner (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base)
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
    (hfit : SegFits (wNode c.p base w) c.i (c.p.fuel - 1) w.top.rootKey)
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
      ((Nn s).leaf = true ∨ K (s + 1) ≠ 0) ∧ (Nn s).size + 1 < c.p.M ∧
      deadOver c.p ((Nn s).setAt ((Nn s).size - 1)
        (.del (bitsUnion (Nn s).lastBitmap ((Nn s).bitsOf (K (s + 1)))))) = false ∧
      deadOver c.p ((Nn s).add c.i (.del (bitsUnion (Nn s).lastBitmap ((Nn s).bitsOf (K (s + 1)))))) =
        false ∧
      ∀ k, s < k → k ≤ depth → (Nn k).firstTime ≠ some c.i)
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
  have hpost : ∀ (stop : Nat) (w' : W) (sn' : KNode), stop < depth →
      w'.taken = w.taken → w'.top = w.top → w'.vals = w.vals →
      (∀ y, y ≠ X stop → (∀ k, stop < k → k ≤ depth → y ≠ X k) → w'.nodes.lookup y = w.nodes.lookup y) →
      w'.nodes.lookup (X stop) = some sn' → sn'.leaf = (Nn stop).leaf → klongsWf sn'.ks = true →
      (∀ s, Klong.time s ∈ sn'.ks → s ≤ c.i) →
      (∀ c' z, (c', z) ∈ sn'.liveAt c.i ↔ (c', z) ∈ (Nn stop).liveAt c.i ∧ c' ≠ K (stop + 1)) →
      CollGetInv c base w' w' := by
    intro stop w' sn' hsD ht htop hv hnodes hsn' hsl' hsw' hst' hlive'
    -- the tree after, at tree level
    have hagree : ∀ u, u ≠ X stop → (∀ i, stop < i → i ≤ depth → u ≠ X i) →
        wNode c.p base w' u = wNode c.p base w u := by
      intro u hus hnc
      simp only [wNode, ht, hnodes u hus hnc]
    have hsnw : wNode c.p base w' (X stop) = some sn' := by
      simp only [wNode, ht, htk stop (by omega), Bool.false_eq_true, ↓reduceIte, hsn']
    have hlive1 : ∀ c' z, (c', z) ∈ sn'.liveAt c.i → (c', z) ∈ (Nn stop).liveAt c.i ∧ c' ≠ K (stop + 1) :=
      fun c' z h => (hlive' c' z).mp h
    have hdist' : ∀ i i', stop ≤ i → i ≤ depth → stop ≤ i' → i' ≤ depth → X i = X i' → i = i' :=
      fun i i' _ h2 _ h4 he => hdist i i' h2 h4 he
    have hNs : ∀ i, stop ≤ i → i ≤ depth → wNode c.p base w (X i) = some (Nn i) := fun i _ h2 => hN i h2
    have hlinks : ∀ i, stop < i → i ≤ depth → (K i, X i) ∈ (Nn (i - 1)).liveAt c.i :=
      fun i h1 h2 => hlinkK i (by omega) h2
    rw [← htop] at hT hR hwf hRt hTimesR hICE hfit hreach hrk huniq
    have hT' := treeOK_up_inner (wNode c.p base w) (wNode c.p base w') c.i w'.top.rootKey X Nn K stop depth
      hsD hT (hreach stop (by omega)) hNs hlinks hdist' hagree sn' hsnw hlive1
    have hsub := tReach_up_sub (wNode c.p base w) (wNode c.p base w') c.i w'.top.rootKey X Nn K stop depth
      hsD hT (hreach stop (by omega)) hNs hlinks hdist' hagree sn' hsnw hlive1
    have hlsub := tLink_up_sub (wNode c.p base w) (wNode c.p base w') c.i w'.top.rootKey X Nn K stop depth
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
      have hl := hlsub y cc z hy ⟨yn, hyn, hcz⟩
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
        exact hICE y m0 cc z hyN hm0 hm0l hcm0
    · refine segFits_transfer _ _ c.i _ _ _ hfit
        (fun u hu => tReach_reachS _ _ _ _ (hsub u (reachS_tReach _ _ _ _ hu)).1)
        (fun u un' hu hun' hl => ?_)
      rcases hnode u un' (reachS_tReach _ _ _ _ hu) hun' with ⟨hus, rfl⟩ | h
      · refine ⟨Nn stop, by rw [hus]; exact hN stop (by omega), by rw [← hsl']; exact hl,
          fun c' y' hy' => ⟨c', ((hlive' c' y').mp hy').1⟩⟩
      · exact ⟨un', h, hl, fun c' y' hy' => ⟨c', hy'⟩⟩
    · intro y yn hy hyn
      rcases hnode y yn hy hyn with ⟨_, rfl⟩ | h
      · exact hsw'
      · exact hwf y yn (hsub y hy).1 h
    · intro y yn hy hyn
      rw [hV]
      rcases hnode y yn hy hyn with ⟨hys, _⟩ | h
      · rw [hys]; exact hnovalAll _ _ (hN stop (by omega))
      · exact hnovalAll y yn h
  apply writerWP_deleteUpward_inner_get c base X Nn K depth cv pre rk w _ hdepth hfuel hp hk hlk htk
    htimes hdist hne hall hleaf hT hR hwf hreach hlinkK (fun i hi => hnovalAll _ _ (hN i hi))
    hrk hcv hvisL huniq hstopOK hmerges
  · intro seg stop w' sn' hsD _ ht htop hv hnodes hsn' hsl' hsw' hst' hlive' hread
    have hI := hpost stop w' sn' hsD ht htop hv hnodes hsn' hsl' hsw' hst' hlive'
    by_cases hseg : seg = 0
    · subst hseg
      refine writerWP_mono (writerWP_collapseRoot_space_get (pre ++ [cv]) c base hvc w' c.p.fuel w' hI) ?_
      intro _ w'' h
      exact ⟨h.1.1, fun key' hkw => by rw [h.2.1 key']; exact hread key' hkw⟩
    · exact hcollSeg seg (by omega) w' hI hread
  · intro stop w' sn' hsD _ ht htop hv hnodes hsn' hsl' hsw' hst' hlive' hread
    exact ⟨(hpost stop w' sn' hsD ht htop hv hnodes hsn' hsl' hsw' hst' hlive').1.1, hread⟩

end SIS.Tree
