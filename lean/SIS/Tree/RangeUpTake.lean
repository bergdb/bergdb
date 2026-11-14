/-
The upward delete with the take-back keeps the walk's ranges (bergdb 024-12,
TP10; `RangeOrder`): prover cost's `writerWP_deleteUpward_upT_get` (a node of
the chain made by the transaction taken back, its parent retargeted) with the
ranges as its postcondition, as `rangeOrder_deleteUpward_up` (RangeUpAll.lean):
the stop node's live klongs are the same at tree level.
-/
import SIS.Tree.WriterGetUpTake
import SIS.Tree.RangeUpAll

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- `rangeOrder_deleteUpward_up` with the take-back (cost's
`writerWP_deleteUpward_upT`): the chain's nodes may be made by the transaction. -/
theorem rangeOrder_deleteUpward_upT (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base)
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
  have hpost := collGetInv_after_upT c base X Nn K depth w hlk htk hdist hT hwf hRt hTimesR hICE hfit
    hnovalAll hreach hlinkK
  -- the tree after at tree level, from the frame facts of the state before collapse
  have hfr : ∀ (stop : Nat) (w' : W) (sn' : KNode), stop < depth →
      (∀ y, (∀ k, stop < k → k ≤ depth → y ≠ X k) → w'.taken.contains y = w.taken.contains y) →
      (∀ y, y ≠ X stop → (∀ k, stop < k → k ≤ depth → y ≠ X k) →
        w'.nodes.lookup y = w.nodes.lookup y) →
      w'.nodes.lookup (X stop) = some sn' →
      (∀ u, u ≠ X stop → (∀ i, stop < i → i ≤ depth → u ≠ X i) →
        wNode c.p base w' u = wNode c.p base w u) ∧ wNode c.p base w' (X stop) = some sn' := by
    intro stop w' sn' hsD ht hnodes hsn'
    refine ⟨fun u hus hnc => by simp only [wNode, ht u hnc, hnodes u hus hnc], ?_⟩
    simp only [wNode, ht (X stop) (fun k h1 h2 he => by have := hdist _ _ (by omega) h2 he; omega),
      htk stop (by omega), Bool.false_eq_true, ↓reduceIte, hsn']
  have hRbit : ∀ (stop : Nat) (w' : W) (sn' : KNode), stop < depth →
      (∀ y, (∀ k, stop < k → k ≤ depth → y ≠ X k) → w'.taken.contains y = w.taken.contains y) →
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
  apply writerWP_deleteUpward_upT_get c base X Nn K depth cv pre rk w _ hdepth hfuel hp hk hlk htk
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
