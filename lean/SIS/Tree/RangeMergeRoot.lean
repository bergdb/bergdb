import SIS.Tree.RangeMergeHalves

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-! The merge under the space root keeps the walk's ranges (bergdb 024-12, case
(4), the merge step's `RangeOrder` part at d = 1): putinv's merge range lemmas
with the root's split (`writerWP_rootSplit_rangeL`) in place of the full
parent's cascade, as prover cost's `writerWP_mergeTail_root_getF` does for the
reading. -/

set_option maxHeartbeats 1600000 in
/-- `writerWP_mergeFull_branchRange` at the space root (d = 1): the root's split
with the merge's last version keeps the walk's ranges, given those of the tree
with the root's content replaced by it (`writerWP_rootSplit_rangeL`). -/
theorem writerWP_mergeFull_rootBranchRange (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base)
    (p l r m1 : NodeId) (m2 : Option (NodeId × Nat)) (pn : KNode) (cL cR : Nat)
    (hhalves : ∀ last, mergeFullLast pn c.i cL m1 cR m2 = some last →
      c.p.splitAbove < last.size → ∃ r0 : Nat, 0 < r0 ∧
      (halves pn.leaf c.i last []).2.2 = r0 ∧
      (∀ c' z, (c', z) ∈ (halves pn.leaf c.i last []).1.liveAt c.i → c' < r0 ∧
        (c', z) ∈ (⟨pn.leaf, last.ks⟩ : KNode).liveAt c.i) ∧
      (∀ c' z, (c', z) ∈ (halves pn.leaf c.i last []).2.1.liveAt c.i → ∃ c0, r0 ≤ c0 ∧
        c' = splitLocalCv pn.leaf r0 c0 ∧
        (c0, z) ∈ (⟨pn.leaf, last.ks⟩ : KNode).liveAt c.i))
    (hhalvesR : ∀ last, mergeFullLast pn c.i cL m1 cR m2 = some last →
      c.p.splitAbove < last.size → ∀ r0, (halves pn.leaf c.i last []).2.2 = r0 →
      (∃ zs, (r0, zs) ∈ (⟨pn.leaf, last.ks⟩ : KNode).liveAt c.i) ∧
      ∃ c0 z0, (c0, z0) ∈ (⟨pn.leaf, last.ks⟩ : KNode).liveAt c.i ∧ c0 < r0)
    (w6 : W) (h6p : w6.nodes.lookup p = some pn) (h6tk : w6.taken.contains p = false)
    (h6top : w6.top.rootKey = p)
    (h6S5 : ∀ z, w6.next ≤ z → w6.nodes.lookup z = none ∧ w6.taken.contains z = false ∧
      knodeOf c.p base z = none)
    (h6S6 : ∀ u c' z, TLink (wNode c.p base w6) c.i u c' z → z < w6.next)
    (hV : ∀ last, mergeFullLast pn c.i cL m1 cR m2 = some last →
      TreeOK (updN (wNode c.p base w6) p ⟨pn.leaf, last.ks⟩) c.i w6.top.rootKey ∧
      (∀ z, TReach (updN (wNode c.p base w6) p ⟨pn.leaf, last.ks⟩) c.i w6.top.rootKey z →
        z ≠ l ∧ z ≠ r) ∧
      ∀ c' z, (c', z) ∈ (⟨pn.leaf, last.ks⟩ : KNode).liveAt c.i → z < w6.next)
    (hlr : l < w6.next ∧ r < w6.next)
    (hVR : ∀ last, mergeFullLast pn c.i cL m1 cR m2 = some last →
      RangeOrder (updN (wNode c.p base w6) p ⟨pn.leaf, last.ks⟩) c.i w6.top.rootKey) :
    ∀ last compact s', mergeFullLast pn c.i cL m1 cR m2 = some last →
      WriterWP (handleFull 0 p last compact) c ({ w6 with trail := s' :: w6.trail } : W)
        (fun _ w7 => TreeOK (wNode c.p base w7) c.i w7.top.rootKey ∧
          ¬ TReach (wNode c.p base w7) c.i w7.top.rootKey l ∧
          ¬ TReach (wNode c.p base w7) c.i w7.top.rootKey r ∧
          w7.taken = w6.taken ∧
          RangeOrder (wNode c.p base w7) c.i w7.top.rootKey) := by
  intro last compact s' hlast
  obtain ⟨hVt, hVlr, hvx⟩ := hV last hlast
  have hN6 : wNode c.p base ({ w6 with trail := s' :: w6.trail } : W) = wNode c.p base w6 := rfl
  unfold handleFull
  refine writerWP_mono (writerWP_rootSplit_rangeL c base hvc _ p pn last compact
    (fun hsp => by
      obtain ⟨r0, h1, h2, h3, h4⟩ := hhalves last hlast hsp
      exact ⟨(r0, p), h1, h2, h3, h4⟩) (hhalvesR last hlast)
    ({ w6 with trail := s' :: w6.trail } : W) h6p h6tk h6top h6S5 (by rw [hN6]; exact h6S6)
    (by rw [hN6]; exact hVt) (by rw [hN6]; exact hVR last hlast) hvx) ?_
  rintro _ w7 ⟨hT7, hreach7, hRO7, ht7⟩
  refine ⟨hT7, fun hl => ?_, fun hr => ?_, ht7, hRO7⟩
  · rcases hreach7 l hl with h | h
    · rw [hN6] at h
      exact (hVlr l h).1 rfl
    · have := hlr.1; simp only at h; omega
  · rcases hreach7 r hr with h | h
    · rw [hN6] at h
      exact (hVlr r h).2 rfl
    · have := hlr.2; simp only at h; omega

set_option maxHeartbeats 3200000 in
/-- `writerWP_mergeTail_any_range2` for the parent at the space root (d = 1):
a full root splits with its last version (`writerWP_mergeFull_rootBranchRange`).
The full parent's halves are asked for the merge's values only (`MergeGOrd`). -/
theorem writerWP_mergeTail_root_range (c : Ctx) (base : View BVal) (x : NodeId) (d : Nat) (p : NodeId)
    (pn xn : KNode) (leftSome : Bool) (l : NodeId) (ln : KNode) (il : Nat) (r : NodeId)
    (rn : KNode) (ir : Nat) (cL cR : Nat) (N : NodeId → Option KNode) (root : NodeId) (nx : Nat)
    (w3 : W) (hT : TreeOK N c.i root) (hp : TReach N c.i root p) (hpn : N p = some pn)
    (hL : pn.ks[il]? = some (.key cL l)) (hLL : LastLive pn.ks pn.lastBitmap il cL)
    (hR : pn.ks[ir]? = some (.key cR r)) (hRL : LastLive pn.ks pn.lastBitmap ir cR)
    (hc : cL ≠ cR) (hxlr : x = l ∨ x = r) (hln : N l = some ln) (hrn : N r = some rn)
    (hpwf : klongsWf pn.ks = true) (hpt : ∀ s, Klong.time s ∈ pn.ks → s ≤ c.i)
    (hch : ∀ cc z zn, (cc, z) ∈ pn.liveAt c.i → N z = some zn →
      ∀ s, Klong.time s ∈ zn.ks → s ≤ c.i)
    (hN3 : wNode c.p base w3 = N) (h3top : w3.top.rootKey = root) (h3next : w3.next = nx)
    (h3p : w3.nodes.lookup p = some pn) (h3src : ∀ z, (w3.nodes.lookup z).isSome = true → z < nx)
    (hfree : ∀ z, nx ≤ z → N z = none ∧ w3.taken.contains z = false)
    (hfreshT : ∀ z, nx ≤ z → ∀ u c', TReach N c.i root u → ¬ TLink N c.i u c' z)
    (hvc : ViewCoherent c base)
    (hlinksAll : ∀ u c' z, TLink N c.i u c' z → z < nx)
    (hbaseF : ∀ z, nx ≤ z → knodeOf c.p base z = none)
    (hd : d - 1 = 0) (hroot : root = p)
    (hhalves : ∀ m1 m2 last, mergeFullLast pn c.i cL m1 cR m2 = some last →
      MergeGOrd ln rn cR m2 c.i → c.p.splitAbove < last.size → ∃ r0 : Nat, 0 < r0 ∧
      (halves pn.leaf c.i last []).2.2 = r0 ∧
      (∀ c' z, (c', z) ∈ (halves pn.leaf c.i last []).1.liveAt c.i → c' < r0 ∧
        (c', z) ∈ (⟨pn.leaf, last.ks⟩ : KNode).liveAt c.i) ∧
      (∀ c' z, (c', z) ∈ (halves pn.leaf c.i last []).2.1.liveAt c.i → ∃ c0, r0 ≤ c0 ∧
        c' = splitLocalCv pn.leaf r0 c0 ∧
        (c0, z) ∈ (⟨pn.leaf, last.ks⟩ : KNode).liveAt c.i))
    (hhalvesR : ∀ m1 m2 last, mergeFullLast pn c.i cL m1 cR m2 = some last →
      MergeGOrd ln rn cR m2 c.i → c.p.splitAbove < last.size → ∀ r0, (halves pn.leaf c.i last []).2.2 = r0 →
      (∃ zs, (r0, zs) ∈ (⟨pn.leaf, last.ks⟩ : KNode).liveAt c.i) ∧
      ∃ c0 z0, (c0, z0) ∈ (⟨pn.leaf, last.ks⟩ : KNode).liveAt c.i ∧ c0 < r0)
    (hpleaf : pn.leaf = false) (hclt : cL < cR) (hcap : 1 ≤ c.p.mergeMax)
    (hadj : ∀ cc z, (cc, z) ∈ pn.liveAt c.i → cc ≤ cL ∨ cR ≤ cc)
    (hll : ln.leaf = xn.leaf) (hrl : rn.leaf = xn.leaf)
    (hlrange : ∀ cc z, (cc, z) ∈ ln.liveAt c.i → cc < cR)
    (hllow : ∀ cc z, (cc, z) ∈ ln.liveAt c.i →
      ((!xn.leaf) = true → cc = 0 ∨ cL < cc) ∧ ((!xn.leaf) = false → cL ≤ cc))
    (hrrange : ∀ cc z, (cc, z) ∈ rn.liveAt c.i →
      ((!xn.leaf) = true → cc = 0 ∨ cR < cc) ∧ ((!xn.leaf) = false → cR ≤ cc))
    (hrup : ∀ k z, (k, z) ∈ pn.liveAt c.i → cR < k → ∀ cc z', (cc, z') ∈ rn.liveAt c.i → cc < k)
    (hRO : RangeOrder N c.i root) :
    WriterWP (mergeTail c x d p pn xn leftSome l ln il r rn ir) c w3
      (fun _ w' => RangeOrder (wNode c.p base w') c.i w'.top.rootKey) := by
  -- the tree's facts
  have hpL : (cL, l) ∈ pn.liveAt c.i := by
    rw [KNode.liveAt_of_times pn c.i hpt]
    apply mem_of_lookup_nodup
    rw [KNode.live_lookup]
    exact keyLookup_of_last _ _ _ il l hL hLL
  have hpR : (cR, r) ∈ pn.liveAt c.i := by
    rw [KNode.liveAt_of_times pn c.i hpt]
    apply mem_of_lookup_nodup
    rw [KNode.live_lookup]
    exact keyLookup_of_last _ _ _ ir r hR hRL
  have hlink_l : TLink N c.i p cL l := ⟨pn, hpn, hpL⟩
  have hlink_r : TLink N c.i p cR r := ⟨pn, hpn, hpR⟩
  have hlR : TReach N c.i root l := TReach.link hp hlink_l
  have hrR : TReach N c.i root r := TReach.link hp hlink_r
  have hpl : p ≠ l := fun h => hT.no_self_link p cL hp (by rw [← h] at hlink_l; exact hlink_l)
  have hpr : p ≠ r := fun h => hT.no_self_link p cR hp (by rw [← h] at hlink_r; exact hlink_r)
  have hpx : p ≠ x := by rcases hxlr with h | h <;> rw [h] <;> assumption
  have hlt := hch cL l ln hpL hln
  have hrt := hch cR r rn hpR hrn
  have hcvL : pn.cv? il = some cL := by simp [KNode.cv?, hL]
  have hcvR : pn.cv? ir = some cR := by simp [KNode.cv?, hR]
  have hlt_nx : ∀ y yn, N y = some yn → y < nx := by
    intro y yn hy
    rcases Nat.lt_or_ge y nx with h | h
    · exact h
    · have := (hfree y h).1; rw [this] at hy; cases hy
  have hlnx := hlt_nx l ln hln
  have hrnx := hlt_nx r rn hrn
  have hpnx := hlt_nx p pn hpn
  -- the parent at the space root as a chain of one node (s = D + 1 = 1)
  obtain ⟨s, D, X, Nn, hs1, hD0, hXdef, hNdef⟩ : ∃ (s D : Nat) (X : Nat → NodeId) (Nn : Nat → KNode),
      s = 1 ∧ D = 0 ∧ (∀ i, X i = p) ∧ (∀ i, Nn i = pn) :=
    ⟨1, 0, fun _ => p, fun _ => pn, rfl, rfl, fun _ => rfl, fun _ => rfl⟩
  have hXp : X (D + 1) = p := hXdef _
  have hNp : Nn (D + 1) = pn := hNdef _
  have hpT0 : w3.taken.contains p = false := by
    have := hN3 ▸ hpn
    unfold wNode at this
    split at this
    · cases this
    · rename_i h; simpa using h
  have hS2 : ∀ i, s ≤ i → i ≤ D + 1 →
      w3.nodes.lookup (X i) = some (Nn i) ∧ w3.taken.contains (X i) = false :=
    fun i _ _ => by rw [hXdef, hNdef]; exact ⟨h3p, hpT0⟩
  have hS4 : ∀ i, s ≤ i → i ≤ D + 1 → TReach N c.i root (X i) := fun i _ _ => by rw [hXdef]; exact hp
  have hR0 : s = 0 → root = X 0 := fun h => by omega
  have hXx : ∀ i, s ≤ i → i ≤ D + 1 → X i ≠ x := fun i _ _ => by rw [hXdef]; exact hpx
  unfold mergeTail
  simp only [hcvL, hcvR]
  generalize hLM : (ln.firstTime == some c.i) = lMade
  generalize hRM : (rn.firstTime == some c.i) = rMade
  simp only [note, writerWP_bind, writerWP_modify, writerWP_pure]
  generalize hmk : mergeKlongs (!xn.leaf) c.p.mergeMax cR ln.live rn.live = fs
  obtain ⟨first, second⟩ := fs
  wpSplit
  · simp only [writerWP_bind]; exact writerWP_throw _ _ _ _
  wpSplit
  · simp only [writerWP_bind]; exact writerWP_throw _ _ _ _
  rename_i hne1 hne2
  have hrhead : (!xn.leaf) = true → ∃ y0 tl, rn.live = (0, y0) :: tl := by
    intro hin
    rw [hin] at hne2
    simp only [Bool.true_and, Bool.or_eq_true, bne_iff_ne, ne_eq, not_or, Decidable.not_not]
      at hne2
    cases hr' : rn.live with
    | nil => rw [hr'] at hne2; simp at hne2
    | cons a tl =>
      rw [hr'] at hne2
      simp only [List.head?_cons, Option.map_some, Option.some.injEq] at hne2
      exact ⟨a.2, tl, by rw [← hne2.2]⟩
  have hsortE := mrg_mergeList_sorted ln rn c.i (!xn.leaf) cR hlt hrt hlrange hrrange hrhead
  have hndE : ((mergeList (!xn.leaf) cR ln.live rn.live).map Prod.fst).Nodup :=
    List.pairwise_map.mpr (hsortE.imp (by intro a b hab; omega))
  have hll' : ln.leaf = !(!xn.leaf) := by rw [hll]; simp
  have hrl' : rn.leaf = !(!xn.leaf) := by rw [hrl]; simp
  have hm1notR : ¬ TReach N c.i root nx := not_reach_fresh N c.i root nx hT (hfree nx (Nat.le_refl _)).1
    (hfreshT nx (Nat.le_refl _))
  obtain ⟨hparOne, hparTwo⟩ := mrg_parent_liveAt pn c.i il cL nx ir cR l r hpwf hpt hL hLL hR hRL hc
  have hadjR : ∀ q ∈ pn.liveAt c.i, cL < q.1 → cR ≤ q.1 :=
    fun q hq hlt => (hadj q.1 q.2 hq).resolve_left (by omega)
  have hhead : (!xn.leaf) = true → ∃ y, rn.live.head? = some (0, y) := by
    intro h
    obtain ⟨y0, tl, he⟩ := hrhead h
    exact ⟨y0, by rw [he]; rfl⟩
  simp only [writerWP_bind, writerWP_modify]
  refine writerWP_mono (writerWP_and (writerWP_ghOf_frame x c _) (writerWP_ghOf_reads x c _ base hvc)) ?_
  intro gh w4 ⟨⟨h4t, h4top, h4n, h4v, h4p, h4m, h4l⟩, hr4⟩
  have hcl' : ∀ (b1 b2 : Bool) y, y ≠ l → y ≠ r → ∀ q ∈ [(l, b1), (r, b2)], y ≠ (q : NodeId × Bool).1 := by
    intro b1 b2 y hyl hyr q hq
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hq
    rcases hq with h | h <;> rw [h] <;> assumption
  have hne' : ∀ (b1 b2 : Bool), ∀ q ∈ [(l, b1), (r, b2)], (q : NodeId × Bool).1 ≠ p := by
    intro b1 b2 q hq
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hq
    rcases hq with h | h <;> rw [h]
    · exact Ne.symm hpl
    · exact Ne.symm hpr
  cases lMade <;> cases rMade <;>
    simp only [Bool.false_eq_true, ↓reduceIte, writerWP_bind, writerWP_modify, writerWP_pure,
      replacedBy, writerWP_get]
  all_goals
    refine writerWP_mono (writerWP_newKey_frame _ _ _ _ c _) ?_
    intro m1 w5 ⟨hm1, h5n, h5t, h5top, h5next, h5v, h5p, h5m⟩
    refine writerWP_mono (writerWP_setMadeFor_frame _ _ c _) ?_
    intro _ w6 ⟨h6n, h6t, h6top, h6next, h6v, h6p⟩
    -- the ids
    have hm1 : m1 = nx := by rw [hm1, h4n, h3next]
    subst hm1
    have hxnx : x < m1 := by rcases hxlr with h | h <;> rw [h] <;> assumption
    have hlk4 : ∀ y, y ≠ x → w4.nodes.lookup y = w3.nodes.lookup y := h4l
    have hnone3 : ∀ z, m1 ≤ z → w3.nodes.lookup z = none := by
      intro z hz
      cases h' : w3.nodes.lookup z with
      | none => rfl
      | some _ => have := h3src z (by rw [h']; rfl); omega
    have hw6p : w6.nodes.lookup p = some pn := by
      rw [h6n, h5n, lookup_append_single_ne _ _ _ _ (by omega), hlk4 p hpx, h3p]
    have hw6m1 : w6.nodes.lookup w4.next = some ⟨!!xn.leaf, newKlongs c.i first⟩ := by
      rw [h6n, h5n, lookup_append_single_self]
      rw [hlk4 _ (by rw [h4n, h3next]; omega), h4n, h3next]
      exact hnone3 m1 (Nat.le_refl _)
    have h6taken : w6.taken = w3.taken := by rw [h6t, h5t, h4t]
    have h6old : ∀ y, y ≠ x → y ≠ m1 → w6.nodes.lookup y = w3.nodes.lookup y := by
      intro y hyx hym
      rw [h6n, h5n, lookup_append_single_ne _ _ _ _ (by rw [h4n, h3next]; exact hym), hlk4 y hyx]
    have hpT : w3.taken.contains p = false := by
      have := hN3 ▸ hpn
      unfold wNode at this
      split at this
      · cases this
      · rename_i h; simpa using h
    have hm1T : w3.taken.contains m1 = false := (hfree m1 (Nat.le_refl _)).2
    have hm1N : N m1 = none := (hfree m1 (Nat.le_refl _)).1
    have hNw3 : ∀ y, wNode c.p base w3 y = N y := fun y => by rw [hN3]
    have hhtd := htd_last pn
    -- the parent after
    have hpliveAt : ∀ (m2 : Option (NodeId × Nat)),
        ∀ cc z, (cc, z) ∈ (mergeParentNode pn c.i il cL m1 ir cR m2).liveAt c.i →
        (mergeParentNode pn c.i il cL m1 ir cR m2).live.lookup cc = some z := by
      intro m2 cc z hm
      rw [KNode.liveAt_of_times _ c.i (by
        rw [mergeParentNode_eq]
        exact mpNode_times pn c.i il cL m1 ir cR m2 _ _ _ (hhtd _) hpt)] at hm
      exact lookup_of_mem_nodup _ (KNode.live_keys_nodup _) cc z hm
    have hlm1 : l ≠ m1 := by omega
    have hrm1 : r ≠ m1 := by omega
    have hpm1 : p ≠ m1 := by omega
    have hw4m1 : w4.next = m1 := by rw [h4n, h3next]
    rw [hw4m1] at hw6m1
    have hmkd : splitMerged (!xn.leaf) c.p.mergeMax (mergeList (!xn.leaf) cR ln.live rn.live) =
        (first, second) := hmk
    have h6top' : w6.top.rootKey = root := by rw [h6top, h5top, h4top, h3top]
    have hyx : ∀ y, y ≠ l → y ≠ r → y ≠ x := by
      intro y hyl hyr; rcases hxlr with h | h <;> rw [h] <;> assumption
    have hlr' : ∀ (b1 b2 : Bool) (q : NodeId × Bool), q ∈ [(l, b1), (r, b2)] → q.1 = l ∨ q.1 = r := by
      intro b1 b2 q hq
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hq
      rcases hq with h | h <;> rw [h]
      · exact Or.inl rfl
      · exact Or.inr rfl
    -- the full parent's facts, from any state S with the nodes below m1 as before
    have hlnx' : l < m1 := hlnx
    have hrnx' : r < m1 := hrnx
    have hchild : ∀ z, ((∃ c0, (c0, z) ∈ ln.live) ∨ (∃ c0, (c0, z) ∈ rn.live)) → z < m1 := by
      rintro z (⟨c0, h0⟩ | ⟨c0, h0⟩)
      · exact hlinksAll l c0 z ⟨ln, hln, by rw [KNode.liveAt_of_times ln c.i hlt]; exact h0⟩
      · exact hlinksAll r c0 z ⟨rn, hrn, by rw [KNode.liveAt_of_times rn c.i hrt]; exact h0⟩
    have hsnd : ∀ z (E : List (Nat × NodeId)), (∀ q ∈ E, ∃ q' ∈ ln.live ++ rn.live, q'.2 = q.2) →
        ∀ c', (c', z) ∈ E → (∃ c0, (c0, z) ∈ ln.live) ∨ (∃ c0, (c0, z) ∈ rn.live) := by
      intro z E hE c' hm
      obtain ⟨q', hq', he⟩ := hE (c', z) hm
      rcases List.mem_append.mp hq' with h | h
      · exact Or.inl ⟨q'.1, by rw [show z = q'.2 from he.symm]; exact h⟩
      · exact Or.inr ⟨q'.1, by rw [show z = q'.2 from he.symm]; exact h⟩
    have hXlt : ∀ i, s ≤ i → i ≤ D + 1 → X i < m1 := by
      intro i h1 h2
      obtain ⟨hl3, ht3⟩ := hS2 i h1 h2
      have hNX : N (X i) = some (Nn i) := by
        rw [← hNw3]; simp only [wNode, ht3, Bool.false_eq_true, ↓reduceIte, hl3]
      rcases Nat.lt_or_ge (X i) m1 with h | h
      · exact h
      · rw [(hfree _ h).1] at hNX; cases hNX
    have hm1R : ¬ TReach N c.i root m1 := not_reach_fresh N c.i root m1 hT hm1N (hfreshT m1 (Nat.le_refl _))
    -- the parent after, into one node
    have hchar1 : ∀ cc z, (cc, z) ∈ (mergeParentNode pn c.i il cL m1 ir cR none).liveAt c.i →
        (cc = cL ∧ z = m1) ∨ ((cc, z) ∈ pn.liveAt c.i ∧ cc ≠ cL ∧ cc ≠ cR) := by
      intro cc z hm
      have hlk := hpliveAt none cc z hm
      rw [mergeParentNode_eq, mpNode_live_lookup pn c.i il cL m1 ir cR none _ _ _ l r hpwf hL hLL hR hRL
        hc ?htd (fun _ _ _ h => by cases h) cc] at hlk
      case htd =>
        intro h
        cases hg : pn.ks.getLast? with
        | none => rw [hg] at h; simp at h
        | some k =>
          cases k with
          | del old => exact ⟨old, rfl⟩
          | time t => rw [hg] at h; simp at h
          | key a y => rw [hg] at h; simp at h
      simp only at hlk
      by_cases h1 : cc = cL
      · simp only [h1, ↓reduceIte, Option.some.injEq] at hlk
        exact Or.inl ⟨h1, hlk.symm⟩
      · by_cases h2 : cc = cR
        · simp [h2, Ne.symm hc] at hlk
        · simp only [h1, h2, ↓reduceIte] at hlk
          right
          refine ⟨?_, h1, h2⟩
          rw [KNode.liveAt_of_times pn c.i hpt]
          exact mem_of_lookup_nodup _ cc z hlk
    -- the parent after, into two nodes
    have hchar2 : ∀ (m2 : NodeId) (g2 : Nat) cc z,
        (cc, z) ∈ (mergeParentNode pn c.i il cL m1 ir cR (some (m2, g2))).liveAt c.i →
        (cc = cL ∧ z = m1) ∨ (cc = g2 ∧ z = m2) ∨ ((cc, z) ∈ pn.liveAt c.i ∧ cc ≠ cL ∧ cc ≠ cR) := by
      intro m2 g2 cc z hm
      have hlk := hpliveAt (some (m2, g2)) cc z hm
      rw [mergeParentNode_eq, mpNode_live_lookup pn c.i il cL m1 ir cR (some (m2, g2)) _ _ _ l r
        hpwf hL hLL hR hRL hc ?htd ?hrip cc] at hlk
      case htd =>
        intro h
        cases hg : pn.ks.getLast? with
        | none => rw [hg] at h; simp at h
        | some k =>
          cases k with
          | del old => exact ⟨old, rfl⟩
          | time t => rw [hg] at h; simp at h
          | key a y => rw [hg] at h; simp at h
      case hrip =>
        intro h y g heq
        simp only [Option.some.injEq, Prod.mk.injEq] at heq
        obtain ⟨_, rfl⟩ := heq
        simp at h
        exact h.1.1
      simp only at hlk
      by_cases h0 : cc = g2
      · simp only [h0, ↓reduceIte, Option.some.injEq] at hlk
        exact Or.inr (Or.inl ⟨h0, hlk.symm⟩)
      · by_cases h1 : cc = cL
        · subst h1
          simp only [h0, ↓reduceIte, Option.some.injEq] at hlk
          exact Or.inl ⟨rfl, hlk.symm⟩
        · by_cases h2 : cc = cR
          · subst h2
            simp [h0, h1] at hlk
          · simp only [h0, h1, h2, ↓reduceIte] at hlk
            right; right
            refine ⟨?_, h1, h2⟩
            rw [KNode.liveAt_of_times pn c.i hpt]
            exact mem_of_lookup_nodup _ cc z hlk
    -- neither merged node is named live by the parent after
    have hnoOld : ∀ z, (z = l ∨ z = r) → ∀ cc, (cc, z) ∈ pn.liveAt c.i → cc ≠ cL → cc ≠ cR → False := by
      intro z hz cc hm h1 h2
      rcases hz with hz | hz
      · rw [hz] at hm
        exact h1 (hT.oneLink p cc p cL l hp hp ⟨pn, hpn, hm⟩ hlink_l).2
      · rw [hz] at hm
        exact h2 (hT.oneLink p cc p cR r hp hp ⟨pn, hpn, hm⟩ hlink_r).2
    cases hsec : second with
    | none =>
      rw [hsec] at hmkd
      have hfirst : first = mergeList (!xn.leaf) cR ln.live rn.live := splitMerged_one _ _ _ _ hmkd
      simp only [writerWP_bind, writerWP_pure]
      refine writerWP_mergeParent_cases p pn (d - 1) il cL m1 ir cR none c w6 _ hw6p ?_ ?_
      rotate_left
      · intro last compact s7 hlast
        rw [hd]
        have hw6w4 : ∀ y, y ≠ m1 → wNode c.p base w6 y = wNode c.p base w4 y := by
          intro y hym
          unfold wNode
          rw [h6taken, ← h4t, h6n, h5n, lookup_append_single_ne _ _ _ _ (by rw [hw4m1]; exact hym)]
        have hlow6 : ∀ y, y < m1 → wNode c.p base w6 y = N y := by
          intro y hy
          rw [hw6w4 y (by omega), hr4.1, ← hN3]; rfl
        have hnew6 : ∀ y yn, m1 ≤ y → w6.nodes.lookup y = some yn → ∀ c' z, (c', z) ∈ yn.liveAt c.i →
            z < m1 := by
          intro y yn hy hyn c' z hz
          by_cases hym : y = m1
          · rw [hym, hw6m1] at hyn
            cases hyn
            have hm := liveAt_newKlongs_mem _ c.i c.i first c' z hz
            apply hchild
            apply hsnd z first _ c' hm
            intro q hq
            have : q.2 ∈ (ln.live ++ rn.live).map Prod.snd := by
              rw [List.map_append, ← mergeList_map_snd (!xn.leaf) cR, ← hfirst]
              exact List.mem_map.mpr ⟨q, hq, rfl⟩
            obtain ⟨q', hq', he⟩ := List.mem_map.mp this
            exact ⟨q', hq', he⟩
          · rw [h6old y (by omega) hym, hnone3 y hy] at hyn; cases hyn
        have hhigh6 : ∀ y, w6.next ≤ y → w6.nodes.lookup y = none := by
          intro y hy
          have h6nx : w6.next = m1 + 2 := by rw [h6next, h5next, hw4m1]
          rw [h6old y (by omega) (by omega), hnone3 y (by omega)]
        obtain ⟨h6S2, h6T, h6S4, h6S5, h6S6, h6R0⟩ := mergeState_facts c base N root m1 w3 w6 s D X Nn
          hT h3top hfree hlinksAll hbaseF hS2 hS4 hR0
          (fun i h1 h2 => h6old _ (hXx i h1 h2) (by have := hXlt i h1 h2; omega)) h6taken
          (by rw [h6top, h5top, h4top]) (by rw [h6next, h5next, hw4m1]; omega) hlow6 hnew6 hhigh6
        have hV6 : ∀ last, mergeFullLast pn c.i cL m1 cR none = some last →
            TreeOK (updN (wNode c.p base w6) p ⟨pn.leaf, last.ks⟩) c.i w6.top.rootKey ∧
            (∀ z, TReach (updN (wNode c.p base w6) p ⟨pn.leaf, last.ks⟩) c.i w6.top.rootKey z →
              z ≠ l ∧ z ≠ r) ∧
            ∀ c' z, (c', z) ∈ (⟨pn.leaf, last.ks⟩ : KNode).liveAt c.i → z < w6.next := by
          intro last hlast
          obtain ⟨_, hleafl, hnoneL, _⟩ := mergeFullLast_liveAt pn c.i cL m1 cR none last hlast hpt
          have hlasteq : (⟨pn.leaf, last.ks⟩ : KNode) = last := by
            cases last with
            | mk lf ks => simp only at hleafl; rw [hleafl]
          rw [hlasteq, h6top']
          have hVp : updN (wNode c.p base w6) p last p = some last := updN_self _ _ _
          have hVm1 : updN (wNode c.p base w6) p last m1 = some ⟨!!xn.leaf, newKlongs c.i first⟩ := by
            rw [updN_ne _ _ _ _ (Ne.symm hpm1)]
            simp only [wNode, h6taken, hm1T, Bool.false_eq_true, ↓reduceIte, hw6m1]
          have hVN : ∀ y, y ≠ p → y ≠ m1 → updN (wNode c.p base w6) p last y = N y := by
            intro y hyp hym
            rw [updN_ne _ _ _ _ hyp]
            rcases Nat.lt_or_ge y m1 with hy | hy
            · exact hlow6 y hy
            · have hyw : wNode c.p base w6 y = none := by
                simp only [wNode, h6taken, (hfree y hy).2, Bool.false_eq_true, ↓reduceIte,
                  h6old y (by omega) hym, hnone3 y hy, hbaseF y hy]
              rw [hyw, (hfree y hy).1]
          have hmn : ∀ cc z, (cc, z) ∈ ({ leaf := !!xn.leaf, ks := newKlongs c.i first } : KNode).liveAt c.i →
              (cc, z) ∈ mergeList (!xn.leaf) cR ln.live rn.live := by
            intro cc z hm
            have := liveAt_newKlongs_mem (!!xn.leaf) c.i c.i first cc z hm
            rw [hfirst] at this; exact this
          refine ⟨treeOK_mergeOneAfter N _ c.i root p l r m1 pn ln rn last ⟨!!xn.leaf, newKlongs c.i first⟩
            (!xn.leaf) cL cR hT hp hpn hpL hpR hc hln hrn hlt hrt hm1N (hfreshT m1 (Nat.le_refl _))
            hVm1 hmn hVp (hnoneL rfl) (fun y hyp _ _ hym => hVN y hyp hym), fun z hz => ?_, fun c' z hm => ?_⟩
          · have := mergeV_reach N _ c.i root p l r m1 none pn ln rn last cL cR hT hp hpn hpL hpR hln hrn hVp
              (fun cc z hm => by
                rcases hnoneL rfl cc z hm with ⟨_, h⟩ | h
                · exact Or.inl h
                · exact Or.inr (Or.inr h))
              (fun m mn hm hmn' cc z hz => by
                rcases hm with hm | hm
                · rw [hm, hVm1] at hmn'
                  cases hmn'
                  have hm2 := hmn cc z hz
                  have hsn := (mergeList_map_snd (!xn.leaf) cR ln.live rn.live)
                  have hz' : z ∈ (ln.live ++ rn.live).map Prod.snd := by
                    rw [List.map_append, ← hsn]; exact List.mem_map.mpr ⟨(cc, z), hm2, rfl⟩
                  obtain ⟨q', hq', he⟩ := List.mem_map.mp hz'
                  rcases List.mem_append.mp hq' with h | h
                  · exact Or.inl ⟨q'.1, by rw [KNode.liveAt_of_times ln c.i hlt, ← he]; exact h⟩
                  · exact Or.inr ⟨q'.1, by rw [KNode.liveAt_of_times rn c.i hrt, ← he]; exact h⟩
                · cases hm)
              (fun y hyp _ _ hym _ => hVN y hyp hym) hm1R (fun m hm => by cases hm) z hz
            exact ⟨this.2.1, this.2.2⟩
          · have h6nx : w6.next = m1 + 2 := by rw [h6next, h5next, hw4m1]
            rcases hnoneL rfl c' z hm with ⟨_, h⟩ | ⟨h, _, _⟩
            · omega
            · have := hlinksAll p c' z ⟨pn, hpn, h⟩; omega
        have hVR6 : ∀ last, mergeFullLast pn c.i cL m1 cR none = some last →
            RangeOrder (updN (wNode c.p base w6) p ⟨pn.leaf, last.ks⟩) c.i w6.top.rootKey := by
          intro last hlast
          obtain ⟨_, hleafl, hnoneL, _⟩ := mergeFullLast_liveAt pn c.i cL m1 cR none last hlast hpt
          have hlasteq : (⟨pn.leaf, last.ks⟩ : KNode) = last := by
            cases last with
            | mk lf ks => simp only at hleafl; rw [hleafl]
          rw [hlasteq, h6top']
          have hVN : ∀ y, y ≠ p → y ≠ m1 → updN (wNode c.p base w6) p last y = N y := by
            intro y hyp hym
            rw [updN_ne _ _ _ _ hyp]
            rcases Nat.lt_or_ge y m1 with hy | hy
            · exact hlow6 y hy
            · have hyw : wNode c.p base w6 y = none := by
                simp only [wNode, h6taken, (hfree y hy).2, Bool.false_eq_true, ↓reduceIte,
                  h6old y (by omega) hym, hnone3 y hy, hbaseF y hy]
              rw [hyw, (hfree y hy).1]
          apply rangeOrder_mergeOne N (updN (wNode c.p base w6) p last) c.i root p l r m1 pn ln rn last
            ⟨!!xn.leaf, newKlongs c.i first⟩ (!xn.leaf) cL cR
            hRO hT hp hpn hpleaf hpL hpR hclt hadjR hln hrn hlt hrt (by rw [hll]) (hrl.trans hll.symm)
            hhead hm1N (hfreshT m1 (Nat.le_refl _))
          · rw [updN_ne _ _ _ _ (Ne.symm hpm1)]
            simp only [wNode, h6taken, hm1T, Bool.false_eq_true, ↓reduceIte, hw6m1]
          · show (!!xn.leaf) = ln.leaf
            rw [Bool.not_not, hll]
          · intro cc z hm
            have := liveAt_newKlongs_mem (!!xn.leaf) c.i c.i first cc z hm
            rw [hfirst] at this; exact this
          · exact updN_self _ _ _
          · rw [hleafl]; exact hpleaf
          · exact hnoneL rfl
          · intro y hyp _ _ hym
            exact hVN y hyp hym
        obtain ⟨hlk6p, htk6p⟩ := h6S2 (D + 1) (by omega) (Nat.le_refl _)
        rw [hXp, hNp] at hlk6p
        rw [hXp] at htk6p
        have hbr := writerWP_mergeFull_rootBranchRange c base hvc p l r m1 none pn cL cR
          (fun last h => hhalves m1 none last h (fun _ _ hh => by cases hh))
          (fun last h => hhalvesR m1 none last h (fun _ _ hh => by cases hh))
          w6 hlk6p htk6p (by rw [h6top', hroot]) h6S5 h6S6 hV6
          ⟨by rw [h6next, h5next, hw4m1]; omega, by rw [h6next, h5next, hw4m1]; omega⟩
          hVR6 last compact s7 hlast
        refine writerWP_mono hbr ?_
        rintro _ w7 ⟨hT7, hl7, hr7, ht7, hRO7⟩
        refine writerWP_mono (writerWP_mergeCleanup_wNode p m1 c base hvc _ w7 (hne' _ _)
          (by rw [ht7, h6taken]; exact hpT)) ?_
        rintro _ w8 ⟨h8top, _, _, _, h8l, h8ex, h8p⟩
        try simp only [writerWP_pure]
        rw [h8top]
        refine rangeOrder_after_cleanup (wNode c.p base w7) (wNode c.p base w8) c.i w7.top.rootKey p l r m1
          hRO7 hl7 hr7 (fun y hyp hyl hyr => h8l y hyp (hcl' _ _ y hyl hyr)) (fun n' hn' => ?_) h8ex
        · obtain ⟨n, hn, hleaf, hsub⟩ := h8p n' hn'
          refine ⟨n, hn, hleaf, fun c' z hm => ?_⟩
          rcases hsub c' z hm with h | ⟨hz, q, hq, h⟩
          · exact Or.inl h
          · rcases hlr' _ _ q hq with h' | h' <;> rw [h'] at h
            · exact Or.inr ⟨hz, Or.inl h⟩
            · exact Or.inr ⟨hz, Or.inr h⟩
      intro s7
      generalize hw7 : ({ ({ w6 with trail := s7 :: w6.trail } : W) with
        nodes := upsert w6.nodes p (mergeParentNode pn c.i il cL m1 ir cR none) } : W) = w7
      have h7n : w7.nodes = upsert w6.nodes p (mergeParentNode pn c.i il cL m1 ir cR none) := by rw [← hw7]
      have h7t : w7.taken = w6.taken := by rw [← hw7]
      have h7top : w7.top = w6.top := by rw [← hw7]
      have hlk7 : w7.nodes.lookup p = some (mergeParentNode pn c.i il cL m1 ir cR none) := by
        rw [h7n, lookup_upsert]; simp
      refine writerWP_mono (writerWP_mergeCleanup_keep p m1 c.i c _ w7 _ (hne' _ _) hlk7
        (fun q hq c' hm => by
          rcases hchar1 c' q.1 hm with ⟨_, h⟩ | ⟨hold, h1, h2⟩
          · rcases hlr' _ _ q hq with h' | h' <;> rw [h'] at h
            · exact hlm1 h
            · exact hrm1 h
          · exact hnoOld q.1 (hlr' _ _ q hq) c' hold h1 h2)) ?_
      intro _ w8 ⟨h8top, _, h8t, h8l, pn8, h8p, h8leaf, h8sub⟩
      try simp only [writerWP_pure]
      have h8tc : ∀ y, y ≠ l → y ≠ r → w8.taken.contains y = w3.taken.contains y := by
        intro y hyl hyr; rw [h8t y (hcl' _ _ y hyl hyr), h7t, h6taken]
      have h8l' : ∀ y, y ≠ p → y ≠ l → y ≠ r → w8.nodes.lookup y = w6.nodes.lookup y := by
        intro y hyp hyl hyr; rw [h8l y hyp (hcl' _ _ y hyl hyr), h7n, lookup_upsert]; simp [hyp]
      rw [h8top, h7top, h6top']
      apply rangeOrder_mergeOne N (wNode c.p base w8) c.i root p l r m1 pn ln rn pn8
        ⟨!!xn.leaf, newKlongs c.i first⟩ (!xn.leaf) cL cR
        hRO hT hp hpn hpleaf hpL hpR hclt hadjR hln hrn hlt hrt (by rw [hll]) (hrl.trans hll.symm)
        hhead hm1N (hfreshT m1 (Nat.le_refl _))
      · simp only [wNode, h8tc m1 (Ne.symm hlm1) (Ne.symm hrm1), hm1T, Bool.false_eq_true, ↓reduceIte]
        rw [h8l' m1 (Ne.symm hpm1) (Ne.symm hlm1) (Ne.symm hrm1), hw6m1]
      · show (!!xn.leaf) = ln.leaf
        rw [Bool.not_not, hll]
      · intro cc z hm
        have := liveAt_newKlongs_mem (!!xn.leaf) c.i c.i first cc z hm
        rw [hfirst] at this; exact this
      · simp only [wNode, h8tc p hpl hpr, hpT, Bool.false_eq_true, ↓reduceIte, h8p]
      · rw [h8leaf, mrg_mergeParentNode_leaf]; exact hpleaf
      · intro cc z hm
        exact hchar1 cc z ((h8sub cc z).mp hm)
      · intro y hyp hyl hyr hym
        rw [← hNw3 y]
        unfold wNode
        rw [h8tc y hyl hyr, h8l' y hyp hyl hyr, h6old y (hyx y hyl hyr) hym]
    | some ksg =>
      obtain ⟨ks2, g2⟩ := ksg
      rw [hsec] at hmkd
      have hE : (first ++ ks2).map Prod.snd = (ln.live ++ rn.live).map Prod.snd := by
        rw [splitMerged_map_snd _ _ _ first ks2 g2 hmkd, mergeList_map_snd, List.map_append]
      simp only [writerWP_bind, writerWP_pure, writerWP_get]
      refine writerWP_mono (writerWP_newKey_frame _ _ _ _ c w6) ?_
      intro m2 w7 ⟨hm2, h7n, h7t, h7top, h7next, _, h7p, _⟩
      have hm2' : m2 = m1 + 2 := by rw [hm2, h6next, h5next, hw4m1]
      subst hm2'
      try simp only [writerWP_bind, writerWP_pure, writerWP_get]
      refine writerWP_mono (writerWP_setMadeFor_frame _ _ c _) ?_
      intro _ w8 ⟨h8n, h8t, h8top, h8next, _, h8p⟩
      try simp only [writerWP_pure]
      have hw6m2 : w6.nodes.lookup (m1 + 2) = none := by
        rw [h6n, h5n, lookup_append_single_ne _ _ _ _ (by rw [hw4m1]; omega),
          hlk4 _ (by omega)]
        exact hnone3 _ (by omega)
      have h8l : ∀ y, w8.nodes.lookup y = (w6.nodes ++ [(m1 + 2,
          ({ leaf := !!xn.leaf, ks := newKlongs c.i ks2 } : KNode))]).lookup y := by
        intro y; rw [h8n, h7n, h6next, h5next, hw4m1]
      have hw8p : w8.nodes.lookup p = some pn := by
        rw [h8l, lookup_append_single_ne _ _ _ _ (by omega)]
        exact hw6p
      obtain ⟨yg, hE1, hgs, hE2⟩ := mrg_splitMerged_two (!xn.leaf) c.p.mergeMax hcap _ first ks2 g2 hmkd
      have hElen : c.p.mergeMax < (mergeList (!xn.leaf) cR ln.live rn.live).length := by
        rcases Nat.lt_or_ge c.p.mergeMax (mergeList (!xn.leaf) cR ln.live rn.live).length with h | h
        · exact h
        · exfalso
          unfold splitMerged at hmkd
          simp only [show (mergeList (!xn.leaf) cR ln.live rn.live).length ≤ c.p.mergeMax from h,
            ↓reduceIte, Prod.mk.injEq, reduceCtorEq, and_false] at hmkd
      have hlnL : ∀ q ∈ ln.live, q.1 < cR ∧ ((!xn.leaf) = true → q.1 = 0 ∨ cL < q.1) ∧
          ((!xn.leaf) = false → cL ≤ q.1) := by
        intro q hq
        have hq' : (q.1, q.2) ∈ ln.liveAt c.i := by rw [KNode.liveAt_of_times ln c.i hlt]; exact hq
        exact ⟨hlrange _ _ hq', hllow _ _ hq'⟩
      have hrnR : ∀ q ∈ rn.live, ((!xn.leaf) = true → q.1 = 0 ∨ cR < q.1) ∧
          ((!xn.leaf) = false → cR ≤ q.1) := by
        intro q hq
        have hq' : (q.1, q.2) ∈ rn.liveAt c.i := by rw [KNode.liveAt_of_times rn c.i hrt]; exact hq
        exact hrrange _ _ hq'
      obtain ⟨hgL, hg0, hgU0⟩ := mrg_two_g (!xn.leaf) cL cR ln.live rn.live
        (((mergeList (!xn.leaf) cR ln.live rn.live).length + 1) / 2) g2 yg hsortE (by omega) hgs
        hclt hlnL hrnR
      have hgU : ∀ k z, (k, z) ∈ pn.liveAt c.i → cR < k → g2 < k := by
        intro k z hk hkc
        apply hgU0 k hkc
        intro q hq
        have hq' : (q.1, q.2) ∈ rn.liveAt c.i := by rw [KNode.liveAt_of_times rn c.i hrt]; exact hq
        exact hrup k z hk hkc _ _ hq'
      have hnd1 : (first.map Prod.fst).Nodup := by
        rw [hE1]
        exact List.pairwise_map.mpr ((hsortE.sublist (List.take_sublist _ _)).imp
          (by intro a b hab; omega))
      have hsortD : CvSorted ((mergeList (!xn.leaf) cR ln.live rn.live).drop
          (((mergeList (!xn.leaf) cR ln.live rn.live).length + 1) / 2)) :=
        hsortE.sublist (List.drop_sublist _ _)
      have hnd2 : (ks2.map Prod.fst).Nodup := by
        rw [hE2]
        apply List.pairwise_map.mpr
        apply List.Pairwise.imp (R := fun a b : Nat × NodeId => a.1 < b.1)
          (by intro a b hab; omega)
        generalize hb : (!xn.leaf) = b at hsortD hgs ⊢
        cases b with
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          exact hsortD
        | true =>
          simp only [↓reduceIte]
          apply renameHead_sorted 0 _ hsortD
          intro q hq
          cases hd : (mergeList true cR ln.live rn.live).drop
              (((mergeList true cR ln.live rn.live).length + 1) / 2) with
          | nil => rw [hd] at hq; simp at hq
          | cons a tl =>
            rw [hd] at hq hgs hsortD
            simp only [List.head?_cons, Option.some.injEq] at hgs
            subst hgs
            simp only [List.tail_cons] at hq
            have := (List.pairwise_cons.mp hsortD).1 q hq
            simp at this; omega
      have hTD : List.Pairwise (fun a b : Nat × NodeId => a.1 < b.1)
          ((mergeList (!xn.leaf) cR ln.live rn.live).take (((mergeList (!xn.leaf) cR ln.live rn.live).length + 1) / 2) ++ (mergeList (!xn.leaf) cR ln.live rn.live).drop (((mergeList (!xn.leaf) cR ln.live rn.live).length + 1) / 2)) := by
        rw [List.take_append_drop]; exact hsortE
      have hTDlt := (List.pairwise_append.mp hTD).2.2
      have hgD : (g2, yg) ∈ (mergeList (!xn.leaf) cR ln.live rn.live).drop (((mergeList (!xn.leaf) cR ln.live rn.live).length + 1) / 2) := List.mem_of_head? hgs
      refine writerWP_mergeParent_cases p pn (d - 1) il cL m1 ir cR (some (m1 + 2, g2)) c w8 _ hw8p ?_ ?_
      rotate_left
      · intro last compact s9 hlast
        rw [hd]
        have h8taken : w8.taken = w3.taken := by rw [h8t, h7t, h6taken]
        have h8nx : w8.next = m1 + 4 := by rw [h8next, h7next, h6next, h5next, hw4m1]
        have h8old : ∀ y, y ≠ x → y ≠ m1 → y ≠ m1 + 2 → w8.nodes.lookup y = w3.nodes.lookup y := by
          intro y hyx hym hym2
          rw [h8l, lookup_append_single_ne _ _ _ _ hym2, h6old y hyx hym]
        have hw8m1 : w8.nodes.lookup m1 = some ⟨!!xn.leaf, newKlongs c.i first⟩ := by
          rw [h8l, lookup_append_single_ne _ _ _ _ (by omega)]; exact hw6m1
        have hw8m2 : w8.nodes.lookup (m1 + 2) = some ⟨!!xn.leaf, newKlongs c.i ks2⟩ := by
          rw [h8l, lookup_append_single_self _ _ _ hw6m2]
        have hw8w4 : ∀ y, y ≠ m1 → y ≠ m1 + 2 → wNode c.p base w8 y = wNode c.p base w4 y := by
          intro y hym hym2
          unfold wNode
          rw [h8taken, ← h4t, h8l, lookup_append_single_ne _ _ _ _ hym2, h6n, h5n,
            lookup_append_single_ne _ _ _ _ (by rw [hw4m1]; exact hym)]
        have hlow8 : ∀ y, y < m1 → wNode c.p base w8 y = N y := by
          intro y hy
          rw [hw8w4 y (by omega) (by omega), hr4.1, ← hN3]; rfl
        have hE' : ∀ q ∈ first ++ ks2, ∃ q' ∈ ln.live ++ rn.live, q'.2 = q.2 := by
          intro q hq
          have : q.2 ∈ (ln.live ++ rn.live).map Prod.snd := by
            rw [← hE]; exact List.mem_map.mpr ⟨q, hq, rfl⟩
          obtain ⟨q', hq', he⟩ := List.mem_map.mp this
          exact ⟨q', hq', he⟩
        have hnew8 : ∀ y yn, m1 ≤ y → w8.nodes.lookup y = some yn → ∀ c' z, (c', z) ∈ yn.liveAt c.i →
            z < m1 := by
          intro y yn hy hyn c' z hz
          by_cases hym : y = m1
          · rw [hym, hw8m1] at hyn
            cases hyn
            have hm := liveAt_newKlongs_mem _ c.i c.i first c' z hz
            exact hchild z (hsnd z (first ++ ks2) hE' c' (List.mem_append_left _ hm))
          · by_cases hym2 : y = m1 + 2
            · rw [hym2, hw8m2] at hyn
              cases hyn
              have hm := liveAt_newKlongs_mem _ c.i c.i ks2 c' z hz
              exact hchild z (hsnd z (first ++ ks2) hE' c' (List.mem_append_right _ hm))
            · rw [h8old y (by omega) hym hym2, hnone3 y hy] at hyn; cases hyn
        have hhigh8 : ∀ y, w8.next ≤ y → w8.nodes.lookup y = none := by
          intro y hy
          rw [h8old y (by omega) (by omega) (by omega), hnone3 y (by omega)]
        obtain ⟨h8S2, h8T, h8S4, h8S5, h8S6, h8R0⟩ := mergeState_facts c base N root m1 w3 w8 s D X Nn
          hT h3top hfree hlinksAll hbaseF hS2 hS4 hR0
          (fun i h1 h2 => h8old _ (hXx i h1 h2) (by have := hXlt i h1 h2; omega)
            (by have := hXlt i h1 h2; omega)) h8taken
          (by rw [h8top, h7top, h6top, h5top, h4top]) (by omega) hlow8 hnew8 hhigh8
        have h8top' : w8.top.rootKey = root := by rw [h8top, h7top, h6top']
        have hm2N : N (m1 + 2) = none := (hfree _ (by omega)).1
        have hm2T : w3.taken.contains (m1 + 2) = false := (hfree _ (by omega)).2
        have hV8 : ∀ last, mergeFullLast pn c.i cL m1 cR (some (m1 + 2, g2)) = some last →
            TreeOK (updN (wNode c.p base w8) p ⟨pn.leaf, last.ks⟩) c.i w8.top.rootKey ∧
            (∀ z, TReach (updN (wNode c.p base w8) p ⟨pn.leaf, last.ks⟩) c.i w8.top.rootKey z →
              z ≠ l ∧ z ≠ r) ∧
            ∀ c' z, (c', z) ∈ (⟨pn.leaf, last.ks⟩ : KNode).liveAt c.i → z < w8.next := by
          intro last hlast
          obtain ⟨_, hleafl, _, hsomeL⟩ := mergeFullLast_liveAt pn c.i cL m1 cR _ last hlast hpt
          have hlasteq : (⟨pn.leaf, last.ks⟩ : KNode) = last := by
            cases last with
            | mk lf ks => simp only at hleafl; rw [hleafl]
          rw [hlasteq, h8top']
          have hVp : updN (wNode c.p base w8) p last p = some last := updN_self _ _ _
          have hVm1 : updN (wNode c.p base w8) p last m1 = some ⟨!!xn.leaf, newKlongs c.i first⟩ := by
            rw [updN_ne _ _ _ _ (Ne.symm hpm1)]
            simp only [wNode, h8taken, hm1T, Bool.false_eq_true, ↓reduceIte, hw8m1]
          have hVm2 : updN (wNode c.p base w8) p last (m1 + 2) = some ⟨!!xn.leaf, newKlongs c.i ks2⟩ := by
            rw [updN_ne _ _ _ _ (by omega)]
            simp only [wNode, h8taken, hm2T, Bool.false_eq_true, ↓reduceIte, hw8m2]
          have hVN : ∀ y, y ≠ p → y ≠ m1 → y ≠ m1 + 2 → updN (wNode c.p base w8) p last y = N y := by
            intro y hyp hym hym2
            rw [updN_ne _ _ _ _ hyp]
            rcases Nat.lt_or_ge y m1 with hy | hy
            · exact hlow8 y hy
            · have hyw : wNode c.p base w8 y = none := by
                simp only [wNode, h8taken, (hfree y hy).2, Bool.false_eq_true, ↓reduceIte,
                  h8old y (by omega) hym hym2, hnone3 y hy, hbaseF y hy]
              rw [hyw, (hfree y hy).1]
          refine ⟨treeOK_mergeTwoAfter N _ c.i root p l r m1 (m1 + 2) pn ln rn last
            ⟨!!xn.leaf, newKlongs c.i first⟩ ⟨!!xn.leaf, newKlongs c.i ks2⟩ cL cR g2 first ks2
            hT hp hpn hpL hpR hc hln hrn hlt hrt hm1N (hfreshT m1 (Nat.le_refl _))
            hm2N (hfreshT _ (by omega)) (by omega) hE hVm1
            (fun cc z hm => liveAt_newKlongs_mem (!!xn.leaf) c.i c.i first cc z hm) hVm2
            (fun cc z hm => liveAt_newKlongs_mem (!!xn.leaf) c.i c.i ks2 cc z hm) hVp
            (hsomeL (m1 + 2) g2 rfl) (fun y hyp _ _ hym hym2 => hVN y hyp hym hym2),
            fun z hz => ?_, fun c' z hm => ?_⟩
          · have := mergeV_reach N _ c.i root p l r m1 (some (m1 + 2)) pn ln rn last cL cR hT hp hpn hpL
              hpR hln hrn hVp
              (fun cc z hm => by
                rcases hsomeL (m1 + 2) g2 rfl cc z hm with ⟨_, h⟩ | ⟨_, h⟩ | h
                · exact Or.inl h
                · exact Or.inr (Or.inl (by rw [h]))
                · exact Or.inr (Or.inr h))
              (fun m mn hm hmn' cc z hz => by
                have hmem : (cc, z) ∈ first ++ ks2 := by
                  rcases hm with hm | hm
                  · rw [hm, hVm1] at hmn'
                    cases hmn'
                    exact List.mem_append_left _ (liveAt_newKlongs_mem _ c.i c.i first cc z hz)
                  · simp only [Option.some.injEq] at hm
                    rw [hm, hVm2] at hmn'
                    cases hmn'
                    exact List.mem_append_right _ (liveAt_newKlongs_mem _ c.i c.i ks2 cc z hz)
                rcases hsnd z (first ++ ks2) hE' cc hmem with ⟨c0, h0⟩ | ⟨c0, h0⟩
                · exact Or.inl ⟨c0, by rw [KNode.liveAt_of_times ln c.i hlt]; exact h0⟩
                · exact Or.inr ⟨c0, by rw [KNode.liveAt_of_times rn c.i hrt]; exact h0⟩)
              (fun y hyp _ _ hym hym2 => hVN y hyp hym (fun h => hym2 (by rw [h])))
              hm1R (fun m hm => by
                simp only [Option.some.injEq] at hm
                rw [hm]; exact not_reach_fresh N c.i root _ hT hm2N (hfreshT _ (by omega))) z hz
            exact ⟨this.2.1, this.2.2⟩
          · rcases hsomeL (m1 + 2) g2 rfl c' z hm with ⟨_, h⟩ | ⟨_, h⟩ | ⟨h, _, _⟩
            · omega
            · omega
            · have := hlinksAll p c' z ⟨pn, hpn, h⟩; omega
        have hVR8 : ∀ last, mergeFullLast pn c.i cL m1 cR (some (m1 + 2, g2)) = some last →
            RangeOrder (updN (wNode c.p base w8) p ⟨pn.leaf, last.ks⟩) c.i w8.top.rootKey := by
          intro last hlast
          obtain ⟨htl, hleafl, _, hsomeL⟩ := mergeFullLast_liveAt pn c.i cL m1 cR _ last hlast hpt
          obtain ⟨_, _, hsomeLk⟩ := mergeFullLast_lookup pn c.i cL m1 cR _ last hlast
          have hlasteq : (⟨pn.leaf, last.ks⟩ : KNode) = last := by
            cases last with
            | mk lf ks => simp only at hleafl; rw [hleafl]
          rw [hlasteq, h8top']
          have hVN : ∀ y, y ≠ p → y ≠ m1 → y ≠ m1 + 2 → updN (wNode c.p base w8) p last y = N y := by
            intro y hyp hym hym2
            rw [updN_ne _ _ _ _ hyp]
            rcases Nat.lt_or_ge y m1 with hy | hy
            · exact hlow8 y hy
            · have hyw : wNode c.p base w8 y = none := by
                simp only [wNode, h8taken, (hfree y hy).2, Bool.false_eq_true, ↓reduceIte,
                  h8old y (by omega) hym hym2, hnone3 y hy, hbaseF y hy]
              rw [hyw, (hfree y hy).1]
          apply rangeOrder_mergeTwo N (updN (wNode c.p base w8) p last) c.i root p l r m1 (m1 + 2) pn ln rn
            last ⟨!!xn.leaf, newKlongs c.i first⟩
            ⟨!!xn.leaf, newKlongs c.i ks2⟩ (!xn.leaf) cL cR g2
            hRO hT hp hpn hpleaf hpL hpR hclt hadjR hln hrn hlt hrt (by rw [hll]) (hrl.trans hll.symm)
            hhead hm1N (hfreshT m1 (Nat.le_refl _)) (hfree _ (by omega)).1 (hfreshT _ (by omega))
            (by omega)
          · rw [updN_ne _ _ _ _ (Ne.symm hpm1)]
            simp only [wNode, h8taken, hm1T, Bool.false_eq_true, ↓reduceIte, hw8m1]
          · show (!!xn.leaf) = ln.leaf
            rw [Bool.not_not, hll]
          · intro cc z hm
            rw [mrg_newKlongs_liveAt_iff _ c.i first hnd1 cc z, hE1] at hm
            exact ⟨List.mem_of_mem_take hm, hTDlt _ hm _ hgD⟩
          · rw [updN_ne _ _ _ _ (by omega)]
            simp only [wNode, h8taken, hm2T, Bool.false_eq_true, ↓reduceIte, hw8m2]
          · show (!!xn.leaf) = ln.leaf
            rw [Bool.not_not, hll]
          · intro cc z hm
            rw [mrg_newKlongs_liveAt_iff _ c.i ks2 hnd2 cc z, hE2] at hm
            obtain ⟨tl, hdtl⟩ : ∃ tl, (mergeList (!xn.leaf) cR ln.live rn.live).drop (((mergeList (!xn.leaf) cR ln.live rn.live).length + 1) / 2) = (g2, yg) :: tl := by
              cases hd : (mergeList (!xn.leaf) cR ln.live rn.live).drop (((mergeList (!xn.leaf) cR ln.live rn.live).length + 1) / 2) with
              | nil => rw [hd] at hgs; simp at hgs
              | cons a tl =>
                rw [hd] at hgs
                simp only [List.head?_cons, Option.some.injEq] at hgs
                exact ⟨tl, by rw [hgs]⟩
            have hmemD : ∀ q, q ∈ (g2, yg) :: tl → q ∈ (mergeList (!xn.leaf) cR ln.live rn.live) :=
              fun q hq => List.mem_of_mem_drop (by rw [hdtl]; exact hq)
            have hsD := hsortD
            rw [hdtl] at hsD hm
            have htl : ∀ q ∈ tl, g2 < q.1 := fun q hq => (List.pairwise_cons.mp hsD).1 q hq
            by_cases hin : (!xn.leaf) = true
            · rw [ite_eq_left hin] at hm
              simp only [renameHead, List.mem_cons] at hm
              rcases hm with h | h
              · simp only [Prod.mk.injEq] at h
                exact ⟨g2, Nat.le_refl _, by rw [h.2]; exact hmemD _ List.mem_cons_self,
                  by rw [ite_eq_left ⟨rfl, hin⟩]; exact h.1⟩
              · have h3 : g2 < cc := htl _ h
                exact ⟨cc, Nat.le_of_lt h3, hmemD _ (List.mem_cons_of_mem _ h),
                  by rw [ite_eq_right (fun h' => absurd h'.1 (by omega))]⟩
            · rw [ite_eq_right hin] at hm
              rcases List.mem_cons.mp hm with h | h
              · simp only [Prod.mk.injEq] at h
                exact ⟨g2, Nat.le_refl _, by rw [h.2]; exact hmemD _ List.mem_cons_self,
                  by rw [ite_eq_right (fun h' => hin h'.2)]; exact h.1⟩
              · have h3 : g2 < cc := htl _ h
                exact ⟨cc, Nat.le_of_lt h3, hmemD _ (List.mem_cons_of_mem _ h),
                  by rw [ite_eq_right (fun h' => absurd h'.1 (by omega))]⟩
          · exact ⟨yg, List.mem_of_mem_drop hgD⟩
          · obtain ⟨q, hq⟩ : ∃ q, q ∈ (mergeList (!xn.leaf) cR ln.live rn.live).take (((mergeList (!xn.leaf) cR ln.live rn.live).length + 1) / 2) := by
              cases ht : (mergeList (!xn.leaf) cR ln.live rn.live).take (((mergeList (!xn.leaf) cR ln.live rn.live).length + 1) / 2) with
              | nil =>
                exfalso
                have := congrArg List.length ht
                simp only [List.length_take, List.length_nil] at this
                omega
              | cons q _ => exact ⟨q, List.mem_cons_self⟩
            exact ⟨q.1, q.2, List.mem_of_mem_take hq, hTDlt _ hq _ hgD⟩
          · exact updN_self _ _ _
          · rw [hleafl]; exact hpleaf
          · exact hsomeL (m1 + 2) g2 rfl
          · rw [KNode.liveAt_of_times last c.i htl]
            apply mem_of_lookup_nodup
            rw [hsomeLk (m1 + 2) g2 rfl g2]
            simp
          · intro y hyp _ _ hym hym2
            exact hVN y hyp hym hym2
        have hGO2 : MergeGOrd ln rn cR (some (m1 + 2, g2)) c.i :=
          mergeGOrd_two _ ln rn c.i cR _ g2 yg (m1 + 2) hlt hrt hsortE (by omega) hgs
        obtain ⟨hlk8p, htk8p⟩ := h8S2 (D + 1) (by omega) (Nat.le_refl _)
        rw [hXp, hNp] at hlk8p
        rw [hXp] at htk8p
        have hbr := writerWP_mergeFull_rootBranchRange c base hvc p l r m1 (some (m1 + 2, g2)) pn cL cR
          (fun last h => hhalves m1 (some (m1 + 2, g2)) last h hGO2)
          (fun last h => hhalvesR m1 (some (m1 + 2, g2)) last h hGO2)
          w8 hlk8p htk8p (by rw [h8top', hroot]) h8S5 h8S6 hV8 ⟨by omega, by omega⟩ hVR8 last compact s9 hlast
        refine writerWP_mono hbr ?_
        rintro _ w11 ⟨hT11, hl11, hr11, ht11, hRO11⟩
        refine writerWP_mono (writerWP_mergeCleanup_wNode p m1 c base hvc _ w11 (hne' _ _)
          (by rw [ht11, h8taken]; exact hpT)) ?_
        rintro _ w12 ⟨h12top, _, _, _, h12l, h12ex, h12p⟩
        try simp only [writerWP_pure]
        rw [h12top]
        refine rangeOrder_after_cleanup (wNode c.p base w11) (wNode c.p base w12) c.i w11.top.rootKey p l r m1
          hRO11 hl11 hr11 (fun y hyp hyl hyr => h12l y hyp (hcl' _ _ y hyl hyr)) (fun n' hn' => ?_) h12ex
        · obtain ⟨n, hn, hleaf, hsub⟩ := h12p n' hn'
          refine ⟨n, hn, hleaf, fun c' z hm => ?_⟩
          rcases hsub c' z hm with h | ⟨hz, q, hq, h⟩
          · exact Or.inl h
          · rcases hlr' _ _ q hq with h' | h' <;> rw [h'] at h
            · exact Or.inr ⟨hz, Or.inl h⟩
            · exact Or.inr ⟨hz, Or.inr h⟩
      intro s9
      generalize hw9 : ({ ({ w8 with trail := s9 :: w8.trail } : W) with
        nodes := upsert w8.nodes p (mergeParentNode pn c.i il cL m1 ir cR (some (m1 + 2, g2))) } : W) = w9
      have h9n : w9.nodes = upsert w8.nodes p (mergeParentNode pn c.i il cL m1 ir cR (some (m1 + 2, g2))) := by
        rw [← hw9]
      have h9t : w9.taken = w8.taken := by rw [← hw9]
      have h9top : w9.top = w8.top := by rw [← hw9]
      have hlk9 : w9.nodes.lookup p = some (mergeParentNode pn c.i il cL m1 ir cR (some (m1 + 2, g2))) := by
        rw [h9n, lookup_upsert]; simp
      refine writerWP_mono (writerWP_mergeCleanup_keep p m1 c.i c _ w9 _ (hne' _ _) hlk9
        (fun q hq c' hm => by
          rcases hchar2 (m1 + 2) g2 c' q.1 hm with ⟨_, h⟩ | ⟨_, h⟩ | ⟨hold, h1, h2⟩
          · rcases hlr' _ _ q hq with h' | h' <;> rw [h'] at h
            · exact hlm1 h
            · exact hrm1 h
          · rcases hlr' _ _ q hq with h' | h' <;> rw [h'] at h <;> omega
          · exact hnoOld q.1 (hlr' _ _ q hq) c' hold h1 h2)) ?_
      intro _ w10 ⟨h10top, _, h10t, h10l, pn10, h10p, h10leaf, h10sub⟩
      try simp only [writerWP_pure]
      have h10tc : ∀ y, y ≠ l → y ≠ r → w10.taken.contains y = w3.taken.contains y := by
        intro y hyl hyr; rw [h10t y (hcl' _ _ y hyl hyr), h9t, h8t, h7t, h6taken]
      have h10l' : ∀ y, y ≠ p → y ≠ l → y ≠ r → w10.nodes.lookup y = w8.nodes.lookup y := by
        intro y hyp hyl hyr; rw [h10l y hyp (hcl' _ _ y hyl hyr), h9n, lookup_upsert]; simp [hyp]
      have hm2T : w3.taken.contains (m1 + 2) = false := (hfree _ (by omega)).2
      rw [h10top, h9top, h8top, h7top, h6top']
      apply rangeOrder_mergeTwo N (wNode c.p base w10) c.i root p l r m1 (m1 + 2) pn ln rn
        pn10 ⟨!!xn.leaf, newKlongs c.i first⟩
        ⟨!!xn.leaf, newKlongs c.i ks2⟩ (!xn.leaf) cL cR g2
        hRO hT hp hpn hpleaf hpL hpR hclt hadjR hln hrn hlt hrt (by rw [hll]) (hrl.trans hll.symm)
        hhead hm1N (hfreshT m1 (Nat.le_refl _)) (hfree _ (by omega)).1 (hfreshT _ (by omega))
        (by omega)
      · simp only [wNode, h10tc m1 (Ne.symm hlm1) (Ne.symm hrm1), hm1T, Bool.false_eq_true, ↓reduceIte]
        rw [h10l' m1 (Ne.symm hpm1) (Ne.symm hlm1) (Ne.symm hrm1), h8l,
          lookup_append_single_ne _ _ _ _ (by omega), hw6m1]
      · show (!!xn.leaf) = ln.leaf
        rw [Bool.not_not, hll]
      · intro cc z hm
        rw [mrg_newKlongs_liveAt_iff _ c.i first hnd1 cc z, hE1] at hm
        exact ⟨List.mem_of_mem_take hm, hTDlt _ hm _ hgD⟩
      · simp only [wNode, h10tc (m1 + 2) (by omega) (by omega), hm2T, Bool.false_eq_true, ↓reduceIte]
        rw [h10l' _ (by omega) (by omega) (by omega), h8l, lookup_append_single_self _ _ _ hw6m2]
      · show (!!xn.leaf) = ln.leaf
        rw [Bool.not_not, hll]
      · intro cc z hm
        rw [mrg_newKlongs_liveAt_iff _ c.i ks2 hnd2 cc z, hE2] at hm
        obtain ⟨tl, hdtl⟩ : ∃ tl, (mergeList (!xn.leaf) cR ln.live rn.live).drop (((mergeList (!xn.leaf) cR ln.live rn.live).length + 1) / 2) = (g2, yg) :: tl := by
          cases hd : (mergeList (!xn.leaf) cR ln.live rn.live).drop (((mergeList (!xn.leaf) cR ln.live rn.live).length + 1) / 2) with
          | nil => rw [hd] at hgs; simp at hgs
          | cons a tl =>
            rw [hd] at hgs
            simp only [List.head?_cons, Option.some.injEq] at hgs
            exact ⟨tl, by rw [hgs]⟩
        have hmemD : ∀ q, q ∈ (g2, yg) :: tl → q ∈ (mergeList (!xn.leaf) cR ln.live rn.live) :=
          fun q hq => List.mem_of_mem_drop (by rw [hdtl]; exact hq)
        have hsD := hsortD
        rw [hdtl] at hsD hm
        have htl : ∀ q ∈ tl, g2 < q.1 := fun q hq => (List.pairwise_cons.mp hsD).1 q hq
        by_cases hin : (!xn.leaf) = true
        · rw [ite_eq_left hin] at hm
          simp only [renameHead, List.mem_cons] at hm
          rcases hm with h | h
          · simp only [Prod.mk.injEq] at h
            exact ⟨g2, Nat.le_refl _, by rw [h.2]; exact hmemD _ List.mem_cons_self,
              by rw [ite_eq_left ⟨rfl, hin⟩]; exact h.1⟩
          · have h3 : g2 < cc := htl _ h
            exact ⟨cc, Nat.le_of_lt h3, hmemD _ (List.mem_cons_of_mem _ h),
              by rw [ite_eq_right (fun h' => absurd h'.1 (by omega))]⟩
        · rw [ite_eq_right hin] at hm
          rcases List.mem_cons.mp hm with h | h
          · simp only [Prod.mk.injEq] at h
            exact ⟨g2, Nat.le_refl _, by rw [h.2]; exact hmemD _ List.mem_cons_self,
              by rw [ite_eq_right (fun h' => hin h'.2)]; exact h.1⟩
          · have h3 : g2 < cc := htl _ h
            exact ⟨cc, Nat.le_of_lt h3, hmemD _ (List.mem_cons_of_mem _ h),
              by rw [ite_eq_right (fun h' => absurd h'.1 (by omega))]⟩
      · exact ⟨yg, List.mem_of_mem_drop hgD⟩
      · obtain ⟨q, hq⟩ : ∃ q, q ∈ (mergeList (!xn.leaf) cR ln.live rn.live).take (((mergeList (!xn.leaf) cR ln.live rn.live).length + 1) / 2) := by
          cases ht : (mergeList (!xn.leaf) cR ln.live rn.live).take (((mergeList (!xn.leaf) cR ln.live rn.live).length + 1) / 2) with
          | nil =>
            exfalso
            have := congrArg List.length ht
            simp only [List.length_take, List.length_nil] at this
            omega
          | cons q _ => exact ⟨q, List.mem_cons_self⟩
        exact ⟨q.1, q.2, List.mem_of_mem_take hq, hTDlt _ hq _ hgD⟩
      · simp only [wNode, h10tc p hpl hpr, hpT, Bool.false_eq_true, ↓reduceIte, h10p]
      · rw [h10leaf, mrg_mergeParentNode_leaf]; exact hpleaf
      · intro cc z hm
        rcases (hparTwo (m1 + 2) g2 cc z).mp ((h10sub cc z).mp hm) with h | ⟨_, h⟩ | ⟨_, h1, h2, h3⟩
        · exact Or.inr (Or.inl h)
        · exact Or.inl h
        · exact Or.inr (Or.inr ⟨h3, h1, h2⟩)
      · exact (h10sub g2 (m1 + 2)).mpr ((hparTwo (m1 + 2) g2 g2 (m1 + 2)).mpr (Or.inl ⟨rfl, rfl⟩))
      · intro y hyp hyl hyr hym hym2
        rw [← hNw3 y]
        unfold wNode
        rw [h10tc y hyl hyr, h10l' y hyp hyl hyr, h8l, lookup_append_single_ne _ _ _ _ hym2,
          h6old y (hyx y hyl hyr) hym]

/-- `mergeLast_halves` without the parent's range: the premises `hhalves` and
`hhalvesR` of `writerWP_mergeTail_root_range`. -/
theorem mergeLast_halves0 (c : Ctx) (N : NodeId → Option KNode) (root : NodeId)
    (hR : RangeOrder N c.i root) (p : NodeId) (pn : KNode)
    (hpn : N p = some pn) (hpl : pn.leaf = false)
    (hpRS : ReachS N c.i root p)
    (hpt : ∀ s, Klong.time s ∈ pn.ks → s ≤ c.i)
    (cL cR : Nat) (l r : NodeId) (ln rn : KNode) (hclt : cL < cR)
    (hpL : (cL, l) ∈ pn.liveAt c.i) (hpR : (cR, r) ∈ pn.liveAt c.i)
    (hln : N l = some ln) (hrn : N r = some rn) (hsa2 : 2 ≤ c.p.splitAbove)
    (m1 : NodeId) (m2 : Option (NodeId × Nat)) (last : KNode)
    (hlast : mergeFullLast pn c.i cL m1 cR m2 = some last) (hg : MergeGOrd ln rn cR m2 c.i)
    (hsp : c.p.splitAbove < last.size) :
    (∃ r0 : Nat, 0 < r0 ∧
      (halves pn.leaf c.i last []).2.2 = r0 ∧
      (∀ c' z, (c', z) ∈ (halves pn.leaf c.i last []).1.liveAt c.i → c' < r0 ∧
        (c', z) ∈ (⟨pn.leaf, last.ks⟩ : KNode).liveAt c.i) ∧
      (∀ c' z, (c', z) ∈ (halves pn.leaf c.i last []).2.1.liveAt c.i → ∃ c0, r0 ≤ c0 ∧
        c' = splitLocalCv pn.leaf r0 c0 ∧
        (c0, z) ∈ (⟨pn.leaf, last.ks⟩ : KNode).liveAt c.i)) ∧
    (∀ r0, (halves pn.leaf c.i last []).2.2 = r0 →
      (∃ zs, (r0, zs) ∈ (⟨pn.leaf, last.ks⟩ : KNode).liveAt c.i) ∧
      ∃ c0 z0, (c0, z0) ∈ (⟨pn.leaf, last.ks⟩ : KNode).liveAt c.i ∧ c0 < r0) := by
  obtain ⟨hl1, hl2⟩ := mrg_child_range N c.i root hR p pn hpRS hpn hpl cL l ln hpL hln
  obtain ⟨hr1, hr2⟩ := mrg_child_range N c.i root hR p pn hpRS hpn hpl cR r rn hpR hrn
  -- the second node's compare value is no live one of the parent's but cR
  have hg2none : ∀ y g, m2 = some (y, g) → g ≠ cR → pn.live.lookup g = none := by
    intro y g hm hgc
    obtain ⟨hg0, hw⟩ := hg y g hm
    cases hlk : pn.live.lookup g with
    | none => rfl
    | some z =>
      exfalso
      have hz : (g, z) ∈ pn.liveAt c.i := by
        rw [KNode.liveAt_of_times pn c.i hpt]; exact mem_of_lookup_nodup _ g z hlk
      rcases hw with hgc' | ⟨z1, hz1⟩ | ⟨⟨z1, hz1⟩, c0, z0, hc0, hc0g⟩
      · exact hgc hgc'
      · obtain ⟨ha, hb⟩ := hr1 g z1 hz1
        have hcg : cR < g := by
          cases hrl : rn.leaf
          · rcases hb hrl with h | h
            · omega
            · exact h (by omega)
          · have := ha hrl (by omega); omega
        have := hr2 g z hz hcg g z1 hz1
        omega
      · have hcg : cL < g := by
          rcases Nat.eq_zero_or_pos cL with h0 | h0
          · omega
          · cases hll : ln.leaf
            · rcases (hl1 g z1 hz1).2 hll with h | h
              · omega
              · exact h h0
            · have := (hl1 c0 z0 hc0).1 hll h0; omega
        have := hl2 g z hz hcg g z1 hz1
        omega
  obtain ⟨pairs, hks, hs⟩ := mergeFullLast_sorted pn c.i cL m1 cR m2 last hlast hg2none
  have hleaf := (mergeFullLast_lookup pn c.i cL m1 cR m2 last hlast).1
  refine ⟨?_, ?_⟩
  · obtain ⟨r0, h1, h2, h3, h4, _⟩ := hhalves_of_sorted c pn last pairs hleaf hks hs ⟨true, []⟩ 0
      (fun _ h => by simp at h) hsa2 hsp
    exact ⟨r0, h1, h2, h3, h4⟩
  intro r0 hr0
  have hxe : (⟨pn.leaf, last.ks⟩ : KNode) = ⟨pn.leaf, newKlongs c.i pairs⟩ := by rw [hks]
  have hlv : (⟨pn.leaf, last.ks⟩ : KNode).lastVersion c.i = last := by
    rw [hxe, KNode.lastVersion_newKlongs_sorted _ _ _ hs, ← hks]
    cases last with
    | mk lf ks => simp only at hleaf; rw [hleaf]
  have h2 : 2 ≤ (⟨pn.leaf, last.ks⟩ : KNode).live.length := by
    rw [hxe, KNode.live_newKlongs_sorted _ _ _ hs]
    have : last.size = pairs.length + 1 := by simp [KNode.size, hks, newKlongs]
    omega
  have ht : ∀ s, Klong.time s ∈ (⟨pn.leaf, last.ks⟩ : KNode).ks → s ≤ c.i := by
    show ∀ s, Klong.time s ∈ last.ks → s ≤ c.i
    rw [hks]; exact newKlongs_times c.i pairs
  obtain ⟨_, _, _, ⟨y, hy⟩, ⟨q0, hq0, hq0lt⟩⟩ :=
    halves_node (⟨pn.leaf, last.ks⟩ : KNode) c.i [] ht h2 List.Pairwise.nil
  rw [hlv] at hy hq0lt
  have hy' : ((halves pn.leaf c.i last []).2.2, y) ∈ (⟨pn.leaf, last.ks⟩ : KNode).live := hy
  have hq0lt' : q0.1 < (halves pn.leaf c.i last []).2.2 := hq0lt
  rw [hr0] at hy' hq0lt'
  refine ⟨⟨y, by rw [KNode.liveAt_of_times _ c.i ht]; exact hy'⟩, q0.1, q0.2,
    by rw [KNode.liveAt_of_times _ c.i ht]; exact hq0, hq0lt'⟩

/-- `writerWP_merge_any_range2` with the parent at the space root (d = 1,
`writerWP_mergeTail_root_range`): the merge keeps the walk's ranges. -/
theorem writerWP_merge_root_range (x : NodeId) (d : Nat) (c : Ctx) (base : View BVal)
    (hvc : ViewCoherent c base) (w : W)
    (hT : TreeOK (wNode c.p base w) c.i w.top.rootKey)
    (hpar : ∀ p, (w.path[d - 1]?).map (·.2) = some p →
      TReach (wNode c.p base w) c.i w.top.rootKey p ∧ ∃ pn, wNode c.p base w p = some pn ∧
        pn.leaf = false ∧ klongsWf pn.ks = true ∧ (∀ s, Klong.time s ∈ pn.ks → s ≤ c.i) ∧
        ∀ cc z zn, (cc, z) ∈ pn.liveAt c.i → wNode c.p base w z = some zn →
          ∀ s, Klong.time s ∈ zn.ks → s ≤ c.i)
    (hRt : ∀ y, TReach (wNode c.p base w) c.i w.top.rootKey y → w.taken.contains y = false)
    (hids : (∀ z, (w.nodes.lookup z).isSome = true → z < w.next) ∧
      (∀ z, (c.view z).isSome = true → z < w.next) ∧ (∀ z, w.taken.contains z = true → z < w.next))
    (hbaseF : ∀ z, w.next ≤ z → knodeOf c.p base z = none)
    (hfreshT : ∀ z, w.next ≤ z → ∀ u c', TReach (wNode c.p base w) c.i w.top.rootKey u →
      ¬ TLink (wNode c.p base w) c.i u c' z)
    (hlinksAll : ∀ u c' z, TLink (wNode c.p base w) c.i u c' z → z < w.next)
    (hd : d - 1 = 0) (hpath0 : (w.path[0]?).map (·.2) = some w.top.rootKey)
    (hR : RangeOrder (wNode c.p base w) c.i w.top.rootKey) (hcap : 1 ≤ c.p.mergeMax)
    (hsa2 : 2 ≤ c.p.splitAbove) :
    WriterWP (merge x d) c w (fun _ w' => RangeOrder (wNode c.p base w') c.i w'.top.rootKey) := by
  obtain ⟨hidn, hidv, hidt⟩ := hids
  have hfree : ∀ z, w.next ≤ z → wNode c.p base w z = none ∧ w.taken.contains z = false := by
    intro z hz
    have htz : w.taken.contains z = false := by
      cases h' : w.taken.contains z with
      | false => rfl
      | true => have := hidt z h'; omega
    have hnz : w.nodes.lookup z = none := by
      cases h' : w.nodes.lookup z with
      | none => rfl
      | some _ => have := hidn z (by rw [h']; rfl); omega
    exact ⟨by simp only [wNode, htz, Bool.false_eq_true, ↓reduceIte, hnz, hbaseF z hz], htz⟩
  unfold merge
  simp only [writerWP_bind, writerWP_read]
  unfold pathNode
  simp only [writerWP_bind, writerWP_get]
  split
  · rename_i e he
    simp only [writerWP_pure]
    obtain ⟨hpR, pn0, hpn0, hpleaf, hpwf, hpt, hch⟩ := hpar e.2 (by rw [he]; rfl)
    have hXp : w.top.rootKey = e.2 := by
      have h1 : (w.path[d - 1]?).map (·.2) = some w.top.rootKey := by
        rw [hd]; exact hpath0
      rw [he] at h1
      simp only [Option.map_some, Option.some.injEq] at h1
      exact h1.symm
    refine writerWP_mono (writerWP_and (writerWP_getNode_all e.2 c w base hvc)
      (writerWP_getNode_cache e.2 c w)) ?_
    intro pn w1 ⟨⟨hr1, hlk1, hwn1, hpre1, hsrc1⟩, _, _, hp1⟩
    rw [hwn1 (hRt _ hpR)] at hpn0
    cases hpn0
    have hpn : wNode c.p base w e.2 = some pn0 := hwn1 (hRt _ hpR)
    have hpRS := tReach_reachS _ c.i _ _ hpR
    -- the tail from any state that reads as w
    have tailOK : ∀ (leftSome : Bool) (l : NodeId) (ln : KNode) (il : Nat) (r : NodeId)
        (rn : KNode) (ir cL cR : Nat) (xn : KNode) (w3 : W), ReadsAs c.p base w w3 →
        w1.nodes <+: w3.nodes → (∀ z, (w3.nodes.lookup z).isSome = true → z < w.next) →
        w3.path = w.path →
        pn0.ks[il]? = some (.key cL l) → LastLive pn0.ks pn0.lastBitmap il cL →
        pn0.ks[ir]? = some (.key cR r) → LastLive pn0.ks pn0.lastBitmap ir cR → cL < cR →
        (∀ cc z, (cc, z) ∈ pn0.liveAt c.i → cc ≤ cL ∨ cR ≤ cc) →
        ln.leaf = xn.leaf → rn.leaf = xn.leaf →
        (x = l ∨ x = r) → wNode c.p base w l = some ln → wNode c.p base w r = some rn →
        WriterWP (mergeTail c x d e.2 pn0 xn leftSome l ln il r rn ir) c w3
          (fun _ w' => RangeOrder (wNode c.p base w') c.i w'.top.rootKey) := by
      intro leftSome l ln il r rn ir cL cR xn w3 hr3 hpre3 hsrc3 hp3 hL hLL hR' hRL hclt hadj hll hrl
        hxlr hln hrn
      have hmemL : (cL, l) ∈ pn0.liveAt c.i := by
        rw [KNode.liveAt_of_times pn0 c.i hpt]
        apply mem_of_lookup_nodup
        rw [KNode.live_lookup]
        exact keyLookup_of_last _ _ _ il l hL hLL
      have hmemR : (cR, r) ∈ pn0.liveAt c.i := by
        rw [KNode.liveAt_of_times pn0 c.i hpt]
        apply mem_of_lookup_nodup
        rw [KNode.live_lookup]
        exact keyLookup_of_last _ _ _ ir r hR' hRL
      obtain ⟨hlr1, hlr2⟩ := mrg_child_range (wNode c.p base w) c.i w.top.rootKey hR e.2 pn0 hpRS hpn
        hpleaf cL l ln hmemL hln
      obtain ⟨hrr1, hrr2⟩ := mrg_child_range (wNode c.p base w) c.i w.top.rootKey hR e.2 pn0 hpRS hpn
        hpleaf cR r rn hmemR hrn
      apply writerWP_mergeTail_root_range c base x d e.2 pn0 xn leftSome l ln il r rn ir cL cR
        (wNode c.p base w) w.top.rootKey w.next w3 hT hpR (hwn1 (hRt _ hpR)) hL hLL hR' hRL (by omega) hxlr
        hln hrn hpwf hpt hch hr3.1 (by rw [hr3.2.1]) hr3.2.2.2.2
        (lookup_of_prefix _ _ hpre3 _ _ hlk1) hsrc3
        (fun z hz => ⟨(hfree z hz).1, by rw [hr3.2.2.1]; exact (hfree z hz).2⟩) hfreshT hvc hlinksAll
        hbaseF hd hXp
        (fun m1 m2 last h hg hsp => (mergeLast_halves0 c (wNode c.p base w) w.top.rootKey hR e.2 pn0
          hpn hpleaf hpRS hpt cL cR l r ln rn hclt hmemL hmemR hln hrn hsa2 m1 m2 last h hg hsp).1)
        (fun m1 m2 last h hg hsp => (mergeLast_halves0 c (wNode c.p base w) w.top.rootKey hR e.2 pn0
          hpn hpleaf hpRS hpt cL cR l r ln rn hclt hmemL hmemR hln hrn hsa2 m1 m2 last h hg hsp).2)
        hpleaf hclt hcap hadj hll hrl
        (fun cc z h => hlr2 cR r hmemR hclt cc z h)
        (by
          intro cc z h
          have h1 := hlr1 cc z h
          rw [hll] at h1
          constructor
          · intro hin
            have hxl : xn.leaf = false := by simpa using hin
            rcases (h1.2 hxl) with h0 | h0
            · exact Or.inl h0
            · rcases Nat.eq_zero_or_pos cL with hc0 | hc0
              · rcases Nat.eq_zero_or_pos cc with hcc | hcc
                · exact Or.inl hcc
                · exact Or.inr (by omega)
              · exact Or.inr (h0 hc0)
          · intro hin
            have hxl : xn.leaf = true := by simpa using hin
            rcases Nat.eq_zero_or_pos cL with hc0 | hc0
            · omega
            · exact h1.1 hxl hc0)
        (by
          intro cc z h
          have h1 := hrr1 cc z h
          rw [hrl] at h1
          constructor
          · intro hin
            have hxl : xn.leaf = false := by simpa using hin
            rcases (h1.2 hxl) with h0 | h0
            · exact Or.inl h0
            · exact Or.inr (h0 (by omega))
          · intro hin
            have hxl : xn.leaf = true := by simpa using hin
            exact h1.1 hxl (by omega))
        (fun k z hk hkc cc z' h => hrr2 k z hk hkc cc z' h)
        hR
    -- a klong of p that is the last live one of its compare value names a reached node
    have hchild : ∀ i cv y, pn0.ks[i]? = some (.key cv y) → LastLive pn0.ks pn0.lastBitmap i cv →
        (cv, y) ∈ pn0.liveAt c.i ∧ TReach (wNode c.p base w) c.i w.top.rootKey y := by
      intro i cv y hk hl
      have hm : (cv, y) ∈ pn0.liveAt c.i := by
        rw [KNode.liveAt_of_times pn0 c.i hpt]
        apply mem_of_lookup_nodup
        rw [KNode.live_lookup]
        exact keyLookup_of_last _ _ _ i y hk hl
      exact ⟨hm, TReach.link hpR ⟨pn0, hpn, hm⟩⟩
    have hptrk : ∀ i cv y, LastLive pn0.ks pn0.lastBitmap i cv → pn0.ptr? i = some y →
        pn0.ks[i]? = some (.key cv y) := by
      intro i cv y hl hy
      obtain ⟨⟨y0, hy0⟩, _, _⟩ := hl
      simp only [KNode.ptr?, hy0, Option.some.injEq] at hy
      rw [hy0, hy]
    refine writerWP_mono (writerWP_and (writerWP_getNode_all x c w1 base hvc)
      (writerWP_getNode_cache x c w1)) ?_
    intro xn w2 ⟨⟨hr2, hlk2, hwn2, hpre2, hsrc2⟩, _, _, hp2⟩
    have hp02 : w2.path = w.path := by rw [hp2, hp1]
    have hr02 := ReadsAs.trans _ _ _ _ _ hr1 hr2
    have hpre02 : w1.nodes <+: w2.nodes := hpre2
    have hsrc02 : ∀ z, (w2.nodes.lookup z).isSome = true → z < w.next := by
      intro z hz
      rcases hsrc2 z hz with h | h
      · rcases hsrc1 z h with h' | h'
        · exact hidn z h'
        · exact hidv z h'
      · exact hidv z h
    unfold klongAt
    simp only [writerWP_bind, writerWP_get]
    split
    · rename_i cx _ hcx
      simp only [writerWP_pure]
      generalize hmi : mergeIdx pn0 cx = mi
      obtain ⟨ixo, ia, ib⟩ := mi
      have hML := mergeIdx_last pn0 cx
      rw [hmi] at hML
      obtain ⟨hMx, hMa, hMb⟩ := hML
      split
      · rename_i ix hix
        simp only [writerWP_bind, writerWP_pure]
        have hLx := hMx ix hix
        refine writerWP_if _ _ _ _ _ _ (fun _ => ?_) (fun hptr => ?_)
        · simp only [writerWP_bind]; exact writerWP_throw _ _ _ _
        have hpx : pn0.ptr? ix = some x := by simpa using hptr
        have hkx := hptrk ix cx x hLx hpx
        obtain ⟨_, hxR⟩ := hchild ix cx x hkx hLx
        have hxn : wNode c.p base w x = some xn := by
          rw [← hr1.1]; exact hwn2 (by rw [hr1.2.2.1]; exact hRt x hxR)
        -- the step after a sibling is read: both nodes known
        have hsib : ∀ (wb : W) (i cv : Nat) (sn : NodeId × KNode) (w3 : W),
            ReadsAs c.p base w wb → w1.nodes <+: wb.nodes →
            (∀ z, (wb.nodes.lookup z).isSome = true → z < w.next) →
            LastLive pn0.ks pn0.lastBitmap i cv →
            pn0.ptr? i = some sn.1 → ReadsAs c.p base wb w3 → wb.nodes <+: w3.nodes →
            (∀ z, (w3.nodes.lookup z).isSome = true → (wb.nodes.lookup z).isSome = true ∨
              (c.view z).isSome = true) →
            (wb.taken.contains sn.1 = false → wNode c.p base wb sn.1 = some sn.2) →
            pn0.ks[i]? = some (.key cv sn.1) ∧ wNode c.p base w sn.1 = some sn.2 ∧
              ReadsAs c.p base w w3 ∧ w1.nodes <+: w3.nodes ∧
              (∀ z, (w3.nodes.lookup z).isSome = true → z < w.next) := by
          intro wb i cv sn w3 hrb hpreb hsrcb hl hp hr3 hpre3 hsrc3 hwn3
          have hk := hptrk i cv sn.1 hl hp
          obtain ⟨_, hsR⟩ := hchild i cv sn.1 hk hl
          refine ⟨hk, ?_, ReadsAs.trans _ _ _ _ _ hrb hr3, hpreb.trans hpre3, ?_⟩
          · rw [← hrb.1]; exact hwn3 (by rw [hrb.2.2.1]; exact hRt _ hsR)
          · intro z hz
            rcases hsrc3 z hz with h | h
            · exact hsrcb z h
            · exact hidv z h
        -- the right sibling, read from a state wb
        have hright : ∀ (wb : W) (ia0 cva : Nat), ReadsAs c.p base w wb → w1.nodes <+: wb.nodes →
            (∀ z, (wb.nodes.lookup z).isSome = true → z < w.next) → wb.path = w.path →
            LastLive pn0.ks pn0.lastBitmap ia0 cva → cx < cva →
            (mergeIdx pn0 cx).2.1 = some (ia0, cva) →
            WriterWP (do
              let __x ← sibling e.2 pn0 ia0 !xn.leaf
              mergeTail c x d e.2 pn0 xn false x xn ix __x.1 __x.2 ia0) c wb
              (fun _ w' => RangeOrder (wNode c.p base w') c.i w'.top.rootKey) := by
          intro wb ia0 cva hrb hpreb hsrcb hpb hLa hax hia
          rw [writerWP_bind]
          refine writerWP_mono (writerWP_and (writerWP_sibling_leaf e.2 pn0 ia0 (!xn.leaf) c wb base hvc)
            (writerWP_sibling_path e.2 pn0 ia0 (!xn.leaf) c wb)) ?_
          rintro ⟨rs, rsn⟩ w4 ⟨⟨hs1, hr4, _, hwn4, hpre4, hsrc4, hsl⟩, hp4⟩
          obtain ⟨hka, hrn, hr04, hpre14, hsrc04⟩ :=
            hsib wb ia0 cva (rs, rsn) w4 hrb hpreb hsrcb hLa hs1 hr4 hpre4 hsrc4 hwn4
          have hmin := mergeIdx_right_min pn0 cx ia0 cva hia
          exact tailOK false x xn ix rs rsn ia0 cx cva xn w4 hr04 hpre14 hsrc04 (by rw [hp4, hpb]) hkx hLx
            hka hLa hax (by
              intro cc z hm
              rcases Nat.lt_or_ge cx cc with h | h
              · have hm' : (cc, z) ∈ pn0.live := by rw [← KNode.liveAt_of_times pn0 c.i hpt]; exact hm
                exact Or.inr (hmin cc z hm' h)
              · exact Or.inl h) rfl (by rw [hsl]; simp) (Or.inl rfl) hxn hrn
        split
        · rename_i ib0 cvb
          obtain ⟨hLb, hbx⟩ := hMb ib0 cvb rfl
          simp only [writerWP_bind]
          refine writerWP_mono (writerWP_and (writerWP_sibling_leaf e.2 pn0 ib0 (!xn.leaf) c w2 base hvc)
            (writerWP_sibling_path e.2 pn0 ib0 (!xn.leaf) c w2)) ?_
          rintro ⟨ls, lsn⟩ w3 ⟨⟨hs1, hr3, _, hwn3, hpre3, hsrc3, hsl⟩, hp3⟩
          obtain ⟨hkb, hln, hr03, hpre13, hsrc03⟩ :=
            hsib w2 ib0 cvb (ls, lsn) w3 hr02 hpre02 hsrc02 hLb hs1 hr3 hpre3 hsrc3 hwn3
          refine writerWP_if _ _ _ _ _ _ (fun _ => ?_) (fun _ => ?_)
          · show WriterWP (mergeTail c x d e.2 pn0 xn true ls lsn ib0 x xn ix) c w3 _
            have hmax := mergeIdx_left_max pn0 cx ib0 cvb (by rw [hmi])
            exact tailOK true ls lsn ib0 x xn ix cvb cx xn w3 hr03 hpre13 hsrc03 (by rw [hp3, hp02]) hkb hLb
              hkx hLx hbx (by
                intro cc z hm
                rcases Nat.lt_or_ge cc cx with h | h
                · have hm' : (cc, z) ∈ pn0.live := by rw [← KNode.liveAt_of_times pn0 c.i hpt]; exact hm
                  exact Or.inl (hmax cc z hm' h)
                · exact Or.inr h) (by rw [hsl]; simp) rfl (Or.inr rfl) hln hxn
          · rw [writerWP_bind, writerWP_pure]
            dsimp only
            split
            · rename_i ia0 cva _
              obtain ⟨hLa, hax⟩ := hMa ia0 cva rfl
              exact hright w3 ia0 cva hr03 hpre13 hsrc03 (by rw [hp3, hp02]) hLa hax (by rw [hmi])
            · exact writerWP_throw _ _ _ _
        · rw [writerWP_bind, writerWP_pure]
          dsimp only
          split
          · rename_i ia0 cva
            obtain ⟨hLa, hax⟩ := hMa ia0 cva rfl
            exact hright w2 ia0 cva hr02 hpre02 hsrc02 hp02 hLa hax (by rw [hmi])
          · exact writerWP_throw _ _ _ _
      · exact writerWP_throw _ _ _ _
    · exact writerWP_throw _ _ _ _
  · exact writerWP_throw _ _ _ _

/-- The writer's merge keeps the walk's ranges, from the invariants of the state
before it (`writerWP_merge_get_inv`'s): `writerWP_merge_root_range` for a
parent at the space root, `writerWP_merge_any_range2` below it. -/
theorem writerWP_merge_range_inv (x : NodeId) (d : Nat) (c : Ctx) (base : View BVal)
    (hvc : ViewCoherent c base) (w : W) (hI : PutInv c base w) (hG : PutInvG c base w)
    (hRO : RangeOrder (wNode c.p base w) c.i w.top.rootKey)
    (X : Nat → NodeId) (K : Nat → Nat) (Nn : Nat → KNode) (hP : PathOK c w d X K Nn)
    (hd0 : 0 < d) (hx : X d = x) (hql : (Nn (d - 1)).leaf = false)
    (hsa2 : 2 ≤ c.p.splitAbove) (hcap : 1 ≤ c.p.mergeMax) :
    WriterWP (merge x d) c w (fun _ w' => RangeOrder (wNode c.p base w') c.i w'.top.rootKey) := by
  have hP' := hP
  obtain ⟨hX, hK, hS2, hlink, h0⟩ := hP'
  have hT := hI.tree
  have hreach := pathOK_reach c base w d X K Nn hP
  have hdist := pathOK_dist c base w d X K Nn hP hT
  have hw : ∀ j, j ≤ d → wNode c.p base w (X j) = some (Nn j) := by
    intro j hj
    obtain ⟨a, b⟩ := hS2 j hj
    simp only [wNode, b, Bool.false_eq_true, ↓reduceIte, a]
  have hO := ordG_of_rangeOrder c _ _ hRO hI.times
  have hpar : ∀ p, (w.path[d - 1]?).map (·.2) = some p →
      TReach (wNode c.p base w) c.i w.top.rootKey p ∧ ∃ pn, wNode c.p base w p = some pn ∧
        pn.leaf = false ∧ klongsWf pn.ks = true ∧ (∀ s, Klong.time s ∈ pn.ks → s ≤ c.i) ∧
        ∀ cc z zn, (cc, z) ∈ pn.liveAt c.i → wNode c.p base w z = some zn →
          ∀ s, Klong.time s ∈ zn.ks → s ≤ c.i := by
    intro p hp
    have hpX : p = X (d - 1) := by
      rw [hX (d - 1) (by omega)] at hp; exact (Option.some.inj hp).symm
    subst hpX
    exact ⟨hreach (d - 1) (by omega), Nn (d - 1), hw (d - 1) (by omega), hql,
      hI.wf _ _ (hw (d - 1) (by omega)), hI.times _ _ (hw (d - 1) (by omega)),
      fun cc z zn _ hz => hI.times z zn hz⟩
  have hRt : ∀ y, TReach (wNode c.p base w) c.i w.top.rootKey y → w.taken.contains y = false :=
    fun y hy => hI.untaken y (tReach_reachS _ _ _ _ hy)
  have hids : (∀ z, (w.nodes.lookup z).isSome = true → z < w.next) ∧
      (∀ z, (c.view z).isSome = true → z < w.next) ∧ (∀ z, w.taken.contains z = true → z < w.next) :=
    ⟨hI.ids.1, hI.ids.2.1, hI.ids.2.2.1⟩
  have hbaseF : ∀ z, w.next ≤ z → knodeOf c.p base z = none := fun z hz => (hI.fresh z hz).1
  have hlinksAll : ∀ u c' z, TLink (wNode c.p base w) c.i u c' z → z < w.next :=
    fun u c' z ⟨un, hun, hl⟩ => hG.links u un c' z hun hl
  have hfreshT : ∀ z, w.next ≤ z → ∀ u c', TReach (wNode c.p base w) c.i w.top.rootKey u →
      ¬ TLink (wNode c.p base w) c.i u c' z := by
    intro z hz u c' _ hl; have := hlinksAll u c' z hl; omega
  by_cases hd1 : d = 1
  · subst hd1
    exact writerWP_merge_root_range x 1 c base hvc w hT hpar hRt hids hbaseF hfreshT hlinksAll rfl
      (by rw [hX 0 (by omega), h0]) hRO hcap hsa2
  · exact writerWP_merge_any_range2 x d c base hvc w hT hpar hRt hids hbaseF hfreshT hlinksAll 0 (d - 2)
      X K Nn (Nat.zero_le _) (by omega)
      (fun i _ hi => hX i (by omega))
      (fun i h1 hi => hK i h1 (by omega))
      (fun i h1 hi => hlink i h1 (by omega))
      (fun i h1 hi hNR hql' c' z hz hpos =>
        rangeG_of_rangeOrder c _ _ hRO hI.times (X (i - 1)) (Nn (i - 1)) (X i) (Nn i) (K i)
          (hreach (i - 1) (by omega)) (hw (i - 1) (by omega)) hql' (hlink i h1 (by omega))
          (hw i (by omega)) hNR c' z hz hpos)
      (fun i _ hi hNR hsp => lenG_of_splitAbove c _ _ hsa2 (X i) (Nn i) (hreach i (by omega))
        (hw i (by omega)) hNR hsp)
      (fun i _ hi => hI.wf _ _ (hw i (by omega)))
      (fun i _ hi => hI.times _ _ (hw i (by omega)))
      (Or.inr rfl)
      (fun i i' _ hi _ hi' he => hdist i i' (by omega) (by omega) he)
      (fun i _ hi => hS2 i (by omega))
      (fun i _ hi => hreach i (by omega))
      (fun _ => by rw [h0])
      (fun i _ hi he => by
        have := hdist i d (by omega) (Nat.le_refl _) (by rw [he, hx]); omega)
      hRO hcap hsa2

end SIS.Tree
