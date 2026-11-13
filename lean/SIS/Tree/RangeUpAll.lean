/-
The upward delete keeps the walk's ranges (bergdb 024-12, TP10; `RangeOrder`):
prover cost's `writerWP_deleteUpward_up_get` with the ranges as its
postcondition. At tree level the stop node loses its klong to the emptied chain
(`rangeOrder_up_bitmap`) or, the empty key's, moves its next klong to the empty
key (`rangeOrder_up_leb`); root collapse at the space root keeps `CollInv` and
the ranges (`writerWP_collapseRoot_spaceRO`).
-/
import SIS.Tree.WriterGetUpAll
import SIS.Tree.RangeLeb
import SIS.Tree.RangeCollapse
import SIS.Tree.RangeChainG

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- What root collapse keeps for the walk's ranges: `CollInv` and `RangeOrder`. -/
def CollInvRO (c : Ctx) (base : View BVal) (w : W) : Prop :=
  CollInv c base w ∧ RangeOrder (wNode c.p base w) c.i w.top.rootKey

theorem collInvRO_of_readsAs (c : Ctx) (base : View BVal) (w v : W) (hr : ReadsAs c.p base w v)
    (h : CollInvRO c base w) : CollInvRO c base v := by
  refine ⟨collInv_of_readsAs c base w v hr h.1, ?_⟩
  rw [hr.1, hr.2.1]
  exact h.2

/-- Root collapse at the space root keeps `CollInv` and the walk's ranges. -/
theorem writerWP_collapseRoot_spaceRO (key : Key) (c : Ctx) (base : View BVal)
    (hvc : ViewCoherent c base) :
    ∀ (fuel : Nat) (w : W), CollInvRO c base w →
      WriterWP (collapseRoot key 0 fuel) c w (fun _ w' => CollInvRO c base w') := by
  intro fuel
  induction fuel with
  | zero => intro w _; exact writerWP_throw _ _ _ _
  | succ f ih =>
    intro w hI
    unfold collapseRoot descendToSegmentRoot pathClear findRoot pathAdd
    simp only [writerWP_bind, writerWP_read, writerWP_modify, writerWP_get, List.take_zero,
      List.foldlM_nil, writerWP_pure]
    generalize hw1 : ({ ({ w with path := [] } : W) with
      path := ([] : List (Option Nat × NodeId)) ++ [(none, w.top.rootKey)] } : W) = w1
    have hr01 : ReadsAs c.p base w w1 := by subst hw1; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
    have hp1 : w1.path = [(none, w.top.rootKey)] := by subst hw1; rfl
    have hI1 := collInvRO_of_readsAs c base w w1 hr01 hI
    refine writerWP_mono (writerWP_and (writerWP_getNode_all _ c w1 base hvc)
      (writerWP_getNode_cache w.top.rootKey c w1)) ?_
    intro n w2 ⟨⟨hr12, hlk2, hwn2, _, _⟩, ⟨_, _, hp2⟩⟩
    have hr02 := ReadsAs.trans _ _ _ _ _ hr01 hr12
    have hI2 := collInvRO_of_readsAs c base w w2 hr02 hI
    have htop2 : w2.top.rootKey = w.top.rootKey := by rw [hr02.2.1]
    have htop1 : w1.top.rootKey = w.top.rootKey := by rw [hr01.2.1]
    have hroot0 : wNode c.p base w2 w.top.rootKey = some n := by
      rw [hr12.1]
      exact hwn2 (by have := hI1.1.2.1 _ TReach.root; rw [htop1] at this; exact this)
    have hroot : wNode c.p base w2 w2.top.rootKey = some n := by rw [htop2]; exact hroot0
    by_cases hleaf : n.leaf = true
    · simp only [hleaf, ↓reduceIte, writerWP_pure]; exact hI2
    · have hleaf' : n.leaf = false := by simpa using hleaf
      simp only [hleaf', Bool.false_eq_true, ↓reduceIte]
      unfold replacedBy
      simp only [writerWP_bind, writerWP_get, writerWP_pure]
      split
      · simp only [writerWP_pure]; exact hI2
      · split
        · simp only [writerWP_pure]; exact hI2
        · rename_i only honly
          split
          · simp only [writerWP_bind]; exact writerWP_throw _ _ _ _
          · rename_i hcvc
            have hcv : n.cv? only = some 0 := by simpa using hcvc
            unfold pathSize
            simp only [writerWP_bind, writerWP_get, writerWP_pure, hp2, hp1, List.length_singleton]
            -- the step's facts
            have hstep : ∀ child, n.ptr? only = some child → ∀ w3 : W, w3.top.rootKey = child →
                (∀ z, z ≠ w.top.rootKey → w3.taken.contains z = w2.taken.contains z) →
                (∀ z, z ≠ w.top.rootKey → w3.nodes.lookup z = w2.nodes.lookup z) →
                CollInvRO c base w3 := by
              intro child hptr w3 h3top h3t h3n
              have hnt := hI2.1.2.2.1 _ n TReach.root hroot
              obtain ⟨cc, hcc⟩ := onlyLiveKlong_link n c.i only child hnt honly hptr
              refine ⟨collInv_step c base w2 w3 child cc hI2.1 ⟨n, hroot, hcc⟩
                (fun m hm => by rw [hroot] at hm; cases hm; exact hleaf') h3top
                (fun z hz => by rw [htop2] at hz; exact h3t z hz)
                (fun z hz => by rw [htop2] at hz; exact h3n z hz), ?_⟩
              obtain ⟨hy, honlyy⟩ := onlyLiveKlong_liveAt n c.i only child hnt honly hptr hcv
              rw [h3top]
              refine rangeOrder_collapseRoot (wNode c.p base w2) (wNode c.p base w3) c.i
                w2.top.rootKey child n hI2.2 hI2.1.1 hroot hleaf' hy honlyy ?_
              intro z hz
              rw [htop2] at hz
              simp only [wNode, h3t z hz, h3n z hz]
            simp only [Nat.sub_self]
            split
            · cases hp : n.ptr? only with
              | none =>
                rw [writerWP_bind]
                unfold takeBackRoot
                simp only [writerWP_bind, writerWP_read]
                rw [writerWP_getNode_known _ n c w2 hlk2, hp]
                exact writerWP_throw _ _ _ _
              | some child =>
                rw [writerWP_bind]
                refine writerWP_mono (writerWP_takeBackRoot_space _ only n child c w2 hlk2 hp) ?_
                intro _ w3 ⟨h3top, h3t, h3n⟩
                apply ih
                apply hstep child hp w3 h3top
                · intro z hz
                  rw [h3t, List.contains_cons]
                  have : (z == w.top.rootKey) = false := by simpa using hz
                  simp [this]
                · intro z _; rw [h3n]
            · cases hp : n.ptr? only with
              | none =>
                rw [writerWP_bind]
                unfold replaceRoot
                simp only [writerWP_bind, writerWP_read]
                rw [writerWP_getNode_known _ n c w2 hlk2, hp]
                exact writerWP_throw _ _ _ _
              | some child =>
                rw [writerWP_bind]
                refine writerWP_mono (writerWP_replaceRoot_space _ only n child c w2 hlk2 hp) ?_
                intro _ w3 ⟨h3top, h3t, h3n⟩
                apply ih
                apply hstep child hp w3 h3top
                · intro z _; rw [h3t]
                · intro z hz; exact h3n z hz



/-- A node in place of itself: the lookup unchanged. -/
theorem updN_self_eq (N : NodeId → Option KNode) (x : NodeId) (n : KNode) (hx : N x = some n) :
    updN N x n = N := by
  funext z
  by_cases hz : z = x
  · rw [hz, updN_self, hx]
  · exact updN_ne _ _ _ _ hz

/-- The walk's ranges after the upward delete at tree level, the stop node X s
losing its klong K (s + 1) to the chain X (s + 1) .. X D (a bitmap), the chain
left out (as `treeOK_up_tr`). -/
theorem rangeOrder_up_bitmap (N N' : NodeId → Option KNode) (t : Time) (r : NodeId)
    (X : Nat → NodeId) (Nn : Nat → KNode) (K : Nat → Nat) (s D : Nat) (hsD : s < D)
    (hR : RangeOrder N t r) (hT : TreeOK N t r) (hXs : TReach N t r (X s))
    (hN : ∀ i, s ≤ i → i ≤ D → N (X i) = some (Nn i))
    (hlinkK : ∀ i, s < i → i ≤ D → (K i, X i) ∈ (Nn (i - 1)).liveAt t)
    (hdist : ∀ i i', s ≤ i → i ≤ D → s ≤ i' → i' ≤ D → X i = X i' → i = i')
    (hagree : ∀ u, u ≠ X s → (∀ i, s < i → i ≤ D → u ≠ X i) → N' u = N u)
    (sn' : KNode) (hsn' : N' (X s) = some sn') (hleaf' : sn'.leaf = (Nn s).leaf)
    (hlive' : ∀ c z, (c, z) ∈ sn'.liveAt t → (c, z) ∈ (Nn s).liveAt t ∧ c ≠ K (s + 1)) :
    RangeOrder N' t r := by
  have hNs := hN s (Nat.le_refl _) (by omega)
  have hR1 : RangeOrder (updN N (X s) sn') t r :=
    rangeOrder_updN_sub N t r (X s) (Nn s) sn' (by rw [updN_self_eq N (X s) (Nn s) hNs]; exact hR)
      hleaf' (fun c z h => (hlive' c z h).1)
  refine rangeOrder_agree _ N' t r hR1 ?_
  intro z hz
  have hsub := tReach_up_sub_tr N (updN N (X s) sn') t r X Nn K s D hsD hT hXs hN hlinkK hdist
    (fun u hu _ => updN_ne _ _ _ _ hu) sn' (updN_self _ _ _)
    (fun c z h => ⟨c, (hlive' c z h).1, (hlive' c z h).2⟩) z hz
  by_cases hzs : z = X s
  · rw [hzs, hsn', updN_self]
  · rw [hagree z hzs hsub.2, updN_ne _ _ _ _ hzs]

/-- The walk's ranges after the upward delete at tree level whose stop node X s,
inner, loses the empty key K (s + 1) = 0 to the chain and moves its next klong
(jcv, jy) to the empty key (LE-b), the chain left out. -/
theorem rangeOrder_up_leb (N N' : NodeId → Option KNode) (t : Time) (r : NodeId)
    (X : Nat → NodeId) (Nn : Nat → KNode) (K : Nat → Nat) (s D : Nat) (hsD : s < D)
    (hR : RangeOrder N t r) (hT : TreeOK N t r) (hXs : TReach N t r (X s))
    (hN : ∀ i, s ≤ i → i ≤ D → N (X i) = some (Nn i))
    (hlinkK : ∀ i, s < i → i ≤ D → (K i, X i) ∈ (Nn (i - 1)).liveAt t)
    (hdist : ∀ i i', s ≤ i → i ≤ D → s ≤ i' → i' ≤ D → X i = X i' → i = i')
    (hagree : ∀ u, u ≠ X s → (∀ i, s < i → i ≤ D → u ≠ X i) → N' u = N u)
    (sn' : KNode) (hsn' : N' (X s) = some sn') (hsl : (Nn s).leaf = false)
    (hleaf' : sn'.leaf = (Nn s).leaf) (hK0 : K (s + 1) = 0)
    (jcv : Nat) (jy : NodeId) (hj : (jcv, jy) ∈ (Nn s).liveAt t) (hj0 : 0 < jcv)
    (hmin : ∀ c z, (c, z) ∈ (Nn s).liveAt t → c ≠ 0 → jcv ≤ c)
    (hlive' : ∀ c z, (c, z) ∈ sn'.liveAt t ↔
      (c = 0 ∧ z = jy) ∨ ((c, z) ∈ (Nn s).liveAt t ∧ c ≠ 0 ∧ c ≠ jcv)) :
    RangeOrder N' t r := by
  have hNs := hN s (Nat.le_refl _) (by omega)
  have hR1 : RangeOrder (updN N (X s) sn') t r :=
    rangeOrder_leb N (updN N (X s) sn') t r (X s) (Nn s) sn' jcv jy hR hNs hsl (updN_self _ _ _)
      (by rw [hleaf', hsl]) (fun z hz => updN_ne _ _ _ _ hz) hj (by omega) hmin
      (fun cc z h => by
        rcases (hlive' cc z).mp h with h1 | ⟨h1, _, h3⟩
        · exact Or.inl h1
        · exact Or.inr ⟨h1, h3⟩)
  refine rangeOrder_agree _ N' t r hR1 ?_
  intro z hz
  have hsub := tReach_up_sub_tr N (updN N (X s) sn') t r X Nn K s D hsD hT hXs hN hlinkK hdist
    (fun u hu _ => updN_ne _ _ _ _ hu) sn' (updN_self _ _ _)
    (fun c z h => by
      rcases (hlive' c z).mp h with ⟨_, h2⟩ | ⟨h1, h2, _⟩
      · exact ⟨jcv, by rw [h2]; exact hj, by omega⟩
      · exact ⟨c, h1, by omega⟩) z hz
  by_cases hzs : z = X s
  · rw [hzs, hsn', updN_self]
  · rw [hagree z hzs hsub.2, updN_ne _ _ _ _ hzs]

/-- The upward delete with every stop keeps the walk's ranges (prover cost's
`writerWP_deleteUpward_up` with `RangeOrder` as its postcondition): the stop
node a segment leaf or an inner node, its klong to the emptied chain deleted by
a bitmap or, the empty key's, by LE-b; the merges off; root collapse at the
space root's segment, and at another segment by `hcollSegR`. -/
theorem rangeOrder_deleteUpward_up (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base)
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
      (∀ k, s < k → k ≤ depth → (Nn k).firstTime ≠ some c.i) ∧
      (((Nn s).leaf = true ∨ K (s + 1) ≠ 0) → (Nn s).size + 1 < c.p.M ∧
        deadOver c.p ((Nn s).setAt ((Nn s).size - 1)
          (.del (bitsUnion (Nn s).lastBitmap ((Nn s).bitsOf (K (s + 1)))))) = false ∧
        deadOver c.p ((Nn s).add c.i (.del (bitsUnion (Nn s).lastBitmap ((Nn s).bitsOf (K (s + 1)))))) =
          false) ∧
      ((Nn s).leaf = false → K (s + 1) = 0 → (Nn s).size + 3 ≤ c.p.M ∧
        ∀ b1 b2 e jcv jy, deadOver c.p (lebNode (Nn s) c.i b1 b2 e jcv jy) = false))
    (hmerges : c.p.merges = false)
    (hcollSegR : ∀ seg, 0 < seg → ∀ w', CollGetInv c base w' w' →
      RangeOrder (wNode c.p base w') c.i w'.top.rootKey →
      WriterWP (collapseRoot (pre ++ [cv]) seg c.p.fuel) c w' (fun _ w'' =>
        RangeOrder (wNode c.p base w'') c.i w''.top.rootKey)) :
    WriterWP (deleteUpward (X depth) depth cv (pre ++ [cv])) c w (fun _ w' =>
      RangeOrder (wNode c.p base w') c.i w'.top.rootKey) := by
  have hN : ∀ i, i ≤ depth → wNode c.p base w (X i) = some (Nn i) := fun i hi => by
    simp only [wNode, htk i hi, Bool.false_eq_true, ↓reduceIte, hlk i hi]
  have hpost := collGetInv_after_up c base X Nn K depth w hlk htk hdist hT hwf hRt hTimesR hICE hfit
    hnovalAll hreach hlinkK
  -- the tree after at tree level, from the frame facts of the state before collapse
  have hfr : ∀ (stop : Nat) (w' : W) (sn' : KNode), stop < depth → w'.taken = w.taken →
      (∀ y, y ≠ X stop → (∀ k, stop < k → k ≤ depth → y ≠ X k) →
        w'.nodes.lookup y = w.nodes.lookup y) →
      w'.nodes.lookup (X stop) = some sn' →
      (∀ u, u ≠ X stop → (∀ i, stop < i → i ≤ depth → u ≠ X i) →
        wNode c.p base w' u = wNode c.p base w u) ∧ wNode c.p base w' (X stop) = some sn' := by
    intro stop w' sn' hsD ht hnodes hsn'
    refine ⟨fun u hus hnc => by simp only [wNode, ht, hnodes u hus hnc], ?_⟩
    simp only [wNode, ht, htk stop (by omega), Bool.false_eq_true, ↓reduceIte, hsn']
  have hRbit : ∀ (stop : Nat) (w' : W) (sn' : KNode), stop < depth → w'.taken = w.taken →
      w'.top = w.top →
      (∀ y, y ≠ X stop → (∀ k, stop < k → k ≤ depth → y ≠ X k) →
        w'.nodes.lookup y = w.nodes.lookup y) →
      w'.nodes.lookup (X stop) = some sn' → sn'.leaf = (Nn stop).leaf →
      (∀ c' z, (c', z) ∈ sn'.liveAt c.i ↔ (c', z) ∈ (Nn stop).liveAt c.i ∧ c' ≠ K (stop + 1)) →
      RangeOrder (wNode c.p base w') c.i w'.top.rootKey := by
    intro stop w' sn' hsD ht htop hnodes hsn' hsl' hlive'
    obtain ⟨hagree, hsnw⟩ := hfr stop w' sn' hsD ht hnodes hsn'
    rw [htop]
    exact rangeOrder_up_bitmap (wNode c.p base w) (wNode c.p base w') c.i w.top.rootKey X Nn K stop
      depth hsD hR hT (hreach stop (by omega)) (fun i _ h2 => hN i h2)
      (fun i h1 h2 => hlinkK i (by omega) h2) (fun i i' _ h2 _ h4 he => hdist i i' h2 h4 he)
      hagree sn' hsnw hsl' (fun c' z h => (hlive' c' z).mp h)
  have hcollAny : ∀ seg w', CollGetInv c base w' w' →
      RangeOrder (wNode c.p base w') c.i w'.top.rootKey →
      WriterWP (collapseRoot (pre ++ [cv]) seg c.p.fuel) c w' (fun _ w'' =>
        RangeOrder (wNode c.p base w'') c.i w''.top.rootKey) := by
    intro seg w' hI hRO
    by_cases hseg : seg = 0
    · subst hseg
      refine writerWP_mono (writerWP_collapseRoot_spaceRO (pre ++ [cv]) c base hvc c.p.fuel w'
        ⟨hI.1, hRO⟩) ?_
      intro _ w'' h
      exact h.2
    · exact hcollSegR seg (by omega) w' hI hRO
  apply writerWP_deleteUpward_up_get c base X Nn K depth cv pre rk w _ hdepth hfuel hp hk hlk htk
    htimes hdist hne hall hleaf hT hR hwf hreach hlinkK (fun i hi => hnovalAll _ _ (hN i hi))
    hrk hcv hvisL huniq hstopOK hmerges
  · intro seg stop w' sn' hsD _ ht htop hv hnodes hsn' hsl' hsw' hst' hlive' _
    exact hcollAny seg w' (hpost stop w' sn' id hsD ht htop hv hnodes hsn' hsl' hsw' hst'
      (fun c' z h => ⟨c', ((hlive' c' z).mp h).1, ((hlive' c' z).mp h).2, rfl⟩))
      (hRbit stop w' sn' hsD ht htop hnodes hsn' hsl' hlive')
  · intro stop w' sn' hsD _ ht htop _ hnodes hsn' hsl' _ _ hlive' _
    exact hRbit stop w' sn' hsD ht htop hnodes hsn' hsl' hlive'
  · intro seg stop w' sn' jcv jy hsD _ ht htop hv hnodes hsn' hsl' hsw' hst' hsl hK0 hj hj0 hmin
      hlive' _
    obtain ⟨hagree, hsnw⟩ := hfr stop w' sn' hsD ht hnodes hsn'
    have hRO : RangeOrder (wNode c.p base w') c.i w'.top.rootKey := by
      rw [htop]
      exact rangeOrder_up_leb (wNode c.p base w) (wNode c.p base w') c.i w.top.rootKey X Nn K stop
        depth hsD hR hT (hreach stop (by omega)) (fun i _ h2 => hN i h2)
        (fun i h1 h2 => hlinkK i (by omega) h2) (fun i i' _ h2 _ h4 he => hdist i i' h2 h4 he)
        hagree sn' hsnw hsl hsl' hK0 jcv jy hj hj0 hmin hlive'
    refine hcollAny seg w' (hpost stop w' sn' (fun c' => if c' = jcv then 0 else c') hsD ht htop hv
      hnodes hsn' hsl' hsw' hst' ?_) hRO
    intro c' z h
    rcases (hlive' c' z).mp h with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩
    · refine ⟨jcv, by rw [h2]; exact hj, by omega, ?_⟩
      simp [h1]
    · exact ⟨c', h1, by omega, by simp [h3]⟩

end SIS.Tree
