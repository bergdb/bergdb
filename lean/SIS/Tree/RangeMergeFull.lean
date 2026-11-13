/-
The merge with a full parent keeps the walk's ranges (bergdb 024-12, TP10;
`RangeOrder`): prover cost's `writerWP_mergeFull_branch` with the ranges
(`writerWP_mergeFull_branchRange`, by `writerWP_fullSplit_chainGRange`), and the
merge's last loop after it (`rangeOrder_after_cleanup`).
-/
import SIS.Tree.WriterTreeMergeFull
import SIS.Tree.RangeFullSplit
import SIS.Tree.RangeMergeMade

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- The merge's last loop at node-map level keeps the walk's ranges: the merged
nodes l and r reached no more, the parent p keeping its live klongs but those to
l and r (retargeted to m1). -/
theorem rangeOrder_after_cleanup (N N' : NodeId → Option KNode) (t : Time) (root p l r m1 : NodeId)
    (hR : RangeOrder N t root) (hl : ¬ TReach N t root l) (hr : ¬ TReach N t root r)
    (hother : ∀ y, y ≠ p → y ≠ l → y ≠ r → N' y = N y)
    (hp : ∀ n', N' p = some n' → ∃ n, N p = some n ∧ n'.leaf = n.leaf ∧ ∀ c z, (c, z) ∈ n'.liveAt t →
      (c, z) ∈ n.liveAt t ∨ (z = m1 ∧ ((c, l) ∈ n.liveAt t ∨ (c, r) ∈ n.liveAt t)))
    (hpN : (∃ n, N p = some n) → ∃ n', N' p = some n') :
    RangeOrder N' t root := by
  -- l and r as before
  have hR1 : RangeOrder (fun y => if y = l ∨ y = r then N' y else N y) t root :=
    rangeOrder_agree N _ t root hR (fun z hz => by
      have hzl : z ≠ l := fun h => hl (h ▸ hz)
      have hzr : z ≠ r := fun h => hr (h ▸ hz)
      simp [hzl, hzr])
  by_cases hpR : TReach N t root p
  · cases hNp : N' p with
    | none =>
      -- p no node after: then no node before
      cases hNp0 : N p with
      | none =>
        refine rangeOrder_agree _ _ t root hR1 (fun z _ => ?_)
        have hpl : p ≠ l := fun h => hl (h ▸ hpR)
        have hpr : p ≠ r := fun h => hr (h ▸ hpR)
        by_cases hzp : z = p
        · rw [hzp, hNp]; simp [hpl, hpr, hNp0]
        · by_cases hzlr : z = l ∨ z = r
          · simp [hzlr]
          · simp only [hzlr, ↓reduceIte]
            exact hother z hzp (fun h => hzlr (Or.inl h)) (fun h => hzlr (Or.inr h))
      | some n0 =>
        obtain ⟨n', hn'⟩ := hpN ⟨n0, hNp0⟩
        rw [hNp] at hn'; cases hn'
    | some n' =>
      obtain ⟨n, hn, hleaf, hsub⟩ := hp n' hNp
      have hsub' : ∀ c z, (c, z) ∈ n'.liveAt t → (c, z) ∈ n.liveAt t := by
        intro c z hm
        rcases hsub c z hm with h | ⟨_, h | h⟩
        · exact h
        · exact absurd (TReach.link hpR ⟨n, hn, h⟩) hl
        · exact absurd (TReach.link hpR ⟨n, hn, h⟩) hr
      have hpl : p ≠ l := fun h => hl (h ▸ hpR)
      have hpr : p ≠ r := fun h => hr (h ▸ hpR)
      have hNx : (fun y => if y = l ∨ y = r then N' y else N y) p = some n := by
        simp [hpl, hpr, hn]
      refine rangeOrder_shrink _ N' t root p n n' hR1 hNx (fun y => ?_) hleaf hsub'
      by_cases hyp : y = p
      · rw [hyp, hNp]; simp
      · by_cases hylr : y = l ∨ y = r
        · simp [hyp, hylr]
        · simp only [hyp, ↓reduceIte, hylr]
          exact hother y hyp (fun h => hylr (Or.inl h)) (fun h => hylr (Or.inr h))
  · refine rangeOrder_agree _ _ t root hR1 (fun z hz => ?_)
    have hz0 : TReach N t root z := by
      have hag : ∀ y, TReach (fun y => if y = l ∨ y = r then N' y else N y) t root y →
          TReach N t root y := by
        intro y hy
        induction hy with
        | root => exact TReach.root
        | @link a c b ha hlk ih =>
          obtain ⟨an, han, hab⟩ := hlk
          have hal : a ≠ l := fun h => hl (h ▸ ih)
          have har : a ≠ r := fun h => hr (h ▸ ih)
          simp only [hal, har, or_self, ↓reduceIte] at han
          exact TReach.link ih ⟨an, han, hab⟩
      exact hag z hz
    have hzp : z ≠ p := fun h => hpR (h ▸ hz0)
    have hzl : z ≠ l := fun h => hl (h ▸ hz0)
    have hzr : z ≠ r := fun h => hr (h ▸ hz0)
    simp only [hzl, hzr, or_self, ↓reduceIte]
    exact hother z hzp hzl hzr

set_option maxHeartbeats 1600000 in
/-- cost's `writerWP_mergeFull_branch` with the walk's ranges, given those of
the tree with the parent's last version put in. -/
theorem writerWP_mergeFull_branchRange (c : Ctx) (base : View BVal)
    (path0 : List (Option Nat × NodeId)) (s D : Nat) (X : Nat → NodeId) (K : Nat → Nat)
    (Nn : Nat → KNode) (hsD : s ≤ D)
    (hX : ∀ i, s ≤ i → i ≤ D + 1 → (path0[i]?).map (·.2) = some (X i))
    (hK : ∀ i, s < i → i ≤ D + 1 → path0[i]? = some (some (K i), X i))
    (hlinkK : ∀ i, s < i → i ≤ D + 1 → (K i, X i) ∈ (Nn (i - 1)).liveAt c.i)
    (hrange : ∀ i, s < i → i ≤ D → ¬ ChainRoom c (Nn i) → (Nn (i - 1)).leaf = false →
      ∀ c' z, (c', z) ∈ (Nn i).live → 0 < c' →
      K i ≤ c' ∧ ∀ c'' z', (c'', z') ∈ (Nn (i - 1)).live → K i < c'' → c' < c'')
    (hlen : ∀ i, s ≤ i → i ≤ D → ¬ ChainRoom c (Nn i) →
      c.p.splitAbove < ((Nn i).lastVersion c.i).size →
      2 ≤ (Nn i).live.length)
    (hwf : ∀ i, s ≤ i → i ≤ D + 1 → klongsWf (Nn i).ks = true)
    (htimes : ∀ i, s ≤ i → i ≤ D + 1 → ∀ t, Klong.time t ∈ (Nn i).ks → t ≤ c.i)
    (htop : ChainRoom c (Nn s) ∨ s = 0)
    (hdist : ∀ i i', s ≤ i → i ≤ D + 1 → s ≤ i' → i' ≤ D + 1 → X i = X i' → i = i')
    (p l r m1 : NodeId) (m2 : Option (NodeId × Nat)) (pn : KNode) (cL cR : Nat)
    (hXp : X (D + 1) = p) (hNp : Nn (D + 1) = pn)
    (hhalves : ∀ last, mergeFullLast pn c.i cL m1 cR m2 = some last →
      c.p.splitAbove < last.size → ∃ r0 : Nat, 0 < r0 ∧
      (halves (Nn (D + 1)).leaf c.i last []).2.2 = r0 ∧
      (∀ c' z, (c', z) ∈ (halves (Nn (D + 1)).leaf c.i last []).1.liveAt c.i → c' < r0 ∧
        (c', z) ∈ (⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode).liveAt c.i) ∧
      (∀ c' z, (c', z) ∈ (halves (Nn (D + 1)).leaf c.i last []).2.1.liveAt c.i → ∃ c0, r0 ≤ c0 ∧
        c' = splitLocalCv (Nn (D + 1)).leaf r0 c0 ∧
        (c0, z) ∈ (⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode).liveAt c.i) ∧
      ((Nn D).leaf = false →
        K (D + 1) ≤ r0 ∧ ∀ c'' z', (c'', z') ∈ (Nn D).live → K (D + 1) < c'' → r0 < c''))
    (w6 : W) (h6path : w6.path = path0)
    (h6S2 : ∀ i, s ≤ i → i ≤ D + 1 →
      w6.nodes.lookup (X i) = some (Nn i) ∧ w6.taken.contains (X i) = false)
    (h6T : TreeOK (wNode c.p base w6) c.i w6.top.rootKey)
    (h6S4 : ∀ i, s ≤ i → i ≤ D + 1 → TReach (wNode c.p base w6) c.i w6.top.rootKey (X i))
    (h6S5 : ∀ z, w6.next ≤ z → w6.nodes.lookup z = none ∧ w6.taken.contains z = false ∧
      knodeOf c.p base z = none)
    (h6S6 : ∀ u c' z, TLink (wNode c.p base w6) c.i u c' z → z < w6.next)
    (h6R0 : s = 0 → w6.top.rootKey = X 0)
    (hV : ∀ last, mergeFullLast pn c.i cL m1 cR m2 = some last →
      TreeOK (updN (wNode c.p base w6) p ⟨pn.leaf, last.ks⟩) c.i w6.top.rootKey ∧
      (∀ z, TReach (updN (wNode c.p base w6) p ⟨pn.leaf, last.ks⟩) c.i w6.top.rootKey z →
        z ≠ l ∧ z ≠ r) ∧
      ∀ c' z, (c', z) ∈ (⟨pn.leaf, last.ks⟩ : KNode).liveAt c.i → z < w6.next)
    (hlr : l < w6.next ∧ r < w6.next)
    (hhalvesR : ∀ last, mergeFullLast pn c.i cL m1 cR m2 = some last →
      c.p.splitAbove < last.size → ∀ r0, (halves (Nn (D + 1)).leaf c.i last []).2.2 = r0 →
      (∃ zs, (r0, zs) ∈ (⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode).liveAt c.i) ∧
      ∃ c0 z0, (c0, z0) ∈ (⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode).liveAt c.i ∧ c0 < r0)
    (hVR : ∀ last, mergeFullLast pn c.i cL m1 cR m2 = some last →
      RangeOrder (updN (wNode c.p base w6) p ⟨pn.leaf, last.ks⟩) c.i w6.top.rootKey) :
    ∀ last compact s', mergeFullLast pn c.i cL m1 cR m2 = some last →
      WriterWP (handleFull (D + 1) p last compact) c ({ w6 with trail := s' :: w6.trail } : W)
        (fun _ w7 => TreeOK (wNode c.p base w7) c.i w7.top.rootKey ∧
          ¬ TReach (wNode c.p base w7) c.i w7.top.rootKey l ∧
          ¬ TReach (wNode c.p base w7) c.i w7.top.rootKey r ∧
          w7.taken = w6.taken ∧ w7.vals = w6.vals ∧
          RangeOrder (wNode c.p base w7) c.i w7.top.rootKey) := by
  intro last compact s' hlast
  obtain ⟨hVt, hVlr, hvx⟩ := hV last hlast
  have hN6 : wNode c.p base ({ w6 with trail := s' :: w6.trail } : W) = wNode c.p base w6 := rfl
  show WriterWP (handleFullWith (fun q more => appendKlongs D q more) (D + 1) p [] last compact) c _ _
  rw [← hXp]
  have hVt' : TreeOK (updN (wNode c.p base ({ w6 with trail := s' :: w6.trail } : W)) (X (D + 1))
      (⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode)) c.i ({ w6 with trail := s' :: w6.trail } : W).top.rootKey := by
    rw [hN6, hXp, hNp]; exact hVt
  have hvx' : ∀ c' z, (c', z) ∈ (⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode).liveAt c.i →
      z < ({ w6 with trail := s' :: w6.trail } : W).next := by
    rw [hNp]; exact hvx
  have hVR' : RangeOrder (updN (wNode c.p base ({ w6 with trail := s' :: w6.trail } : W)) (X (D + 1))
      (⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode)) c.i ({ w6 with trail := s' :: w6.trail } : W).top.rootKey := by
    rw [hN6, hXp, hNp]; exact hVR last hlast
  refine writerWP_mono (writerWP_fullSplit_chainGRange c base path0 s D X K Nn last compact hsD hX hK hlinkK
    hrange hlen hwf htimes htop hdist (hhalves last hlast) (by rw [hNp]; exact hhalvesR last hlast) _ h6path
    h6S2 (by rw [hN6]; exact h6T)
    (by rw [hN6]; exact h6S4) h6S5 (by rw [hN6]; exact h6S6) h6R0 hVt' hvx' hVR') ?_
  rintro _ w7 ⟨hT7, ⟨_, ht7, _, _, hv7⟩, _, hreach7, hRO7⟩
  have hpt := (h6S2 (D + 1) (by omega) (Nat.le_refl _)).2
  refine ⟨hT7, fun hl => ?_, fun hr => ?_, ht7, hv7, hRO7⟩
  · rcases hreach7 l hl with h | h
    · rw [hN6, hXp, hNp] at h
      exact (hVlr l h).1 rfl
    · have := hlr.1; simp only at h; omega
  · rcases hreach7 r hr with h | h
    · rw [hN6, hXp, hNp] at h
      exact (hVlr r h).2 rfl
    · have := hlr.2; simp only at h; omega


end SIS.Tree
