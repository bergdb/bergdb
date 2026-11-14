import SIS.Tree.WriterGetMergeTail
import SIS.Tree.RangeMerge

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-! The writer's merge keeps the walk's ranges (bergdb 024-12, TP10;
`RangeOrder`): the merge's tail (`writerWP_mergeTail_range`) and the merge of
two nodes the transaction did not make under a parent with room
(`writerWP_merge_range`), on prover cost's `writerWP_mergeTail_get` and
`writerWP_merge_get`. -/

set_option maxHeartbeats 800000 in
/-- The merge's tail keeps the walk's ranges (`RangeOrder`): two siblings l and
r under a reached inner parent p with room, which the transaction did not make,
merged into one node or two (`rangeOrder_mergeOne`, `rangeOrder_mergeTwo`); the
premises those of prover cost's `writerWP_mergeTail_get`. -/
theorem writerWP_mergeTail_range (c : Ctx) (base : View BVal) (x : NodeId) (d : Nat) (p : NodeId)
    (pn xn : KNode) (leftSome : Bool) (l : NodeId) (ln : KNode) (il : Nat) (r : NodeId)
    (rn : KNode) (ir : Nat) (cL cR : Nat) (N : NodeId → Option KNode) (root : NodeId) (nx : Nat)
    (w3 : W) (hT : TreeOK N c.i root) (hp : TReach N c.i root p) (hpn : N p = some pn)
    (hL : pn.ks[il]? = some (.key cL l)) (hLL : LastLive pn.ks pn.lastBitmap il cL)
    (hR : pn.ks[ir]? = some (.key cR r)) (hRL : LastLive pn.ks pn.lastBitmap ir cR)
    (hc : cL ≠ cR) (hxlr : x = l ∨ x = r) (hln : N l = some ln) (hrn : N r = some rn)
    (hroom : pn.size + 4 ≤ c.p.M)
    (hdead : ∀ il cL m1 ir cR m2, deadOver c.p (mergeParentNode pn c.i il cL m1 ir cR m2) = false)
    (hpwf : klongsWf pn.ks = true) (hpt : ∀ s, Klong.time s ∈ pn.ks → s ≤ c.i)
    (hch : ∀ cc z zn, (cc, z) ∈ pn.liveAt c.i → N z = some zn →
      zn.firstTime ≠ some c.i ∧ ∀ s, Klong.time s ∈ zn.ks → s ≤ c.i)
    (hN3 : wNode c.p base w3 = N) (h3top : w3.top.rootKey = root) (h3next : w3.next = nx)
    (h3p : w3.nodes.lookup p = some pn) (h3src : ∀ z, (w3.nodes.lookup z).isSome = true → z < nx)
    (hfree : ∀ z, nx ≤ z → N z = none ∧ w3.taken.contains z = false)
    (hfreshT : ∀ z, nx ≤ z → ∀ u c', TReach N c.i root u → ¬ TLink N c.i u c' z)
    (hpleaf : pn.leaf = false) (hclt : cL < cR) (hcap : 1 ≤ c.p.mergeMax)
    (hadj : ∀ cc z, (cc, z) ∈ pn.liveAt c.i → cc ≤ cL ∨ cR ≤ cc)
    (hll : ln.leaf = xn.leaf) (hrl : rn.leaf = xn.leaf)
    (hlrange : ∀ cc z, (cc, z) ∈ ln.liveAt c.i → cc < cR)
    (hllow : ∀ cc z, (cc, z) ∈ ln.liveAt c.i →
      ((!xn.leaf) = true → cc = 0 ∨ cL < cc) ∧ ((!xn.leaf) = false → cL ≤ cc))
    (hrrange : ∀ cc z, (cc, z) ∈ rn.liveAt c.i →
      ((!xn.leaf) = true → cc = 0 ∨ cR < cc) ∧ ((!xn.leaf) = false → cR ≤ cc))
    (hrup : ∀ k z, (k, z) ∈ pn.liveAt c.i → cR < k → ∀ cc z', (cc, z') ∈ rn.liveAt c.i → cc < k)
    (htimesN : ∀ y yn, N y = some yn → ∀ s, Klong.time s ∈ yn.ks → s ≤ c.i)
    (hwfN : ∀ y yn, N y = some yn → klongsWf yn.ks = true)
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
  obtain ⟨hlm, hlt⟩ := hch cL l ln hpL hln
  obtain ⟨hrm, hrt⟩ := hch cR r rn hpR hrn
  have hlm' : (ln.firstTime == some c.i) = false := by simpa using hlm
  have hrm' : (rn.firstTime == some c.i) = false := by simpa using hrm
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
  unfold mergeTail
  simp only [hlm', hrm', hcvL, hcvR, Bool.false_eq_true, ↓reduceIte]
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
  simp only [writerWP_bind, writerWP_modify]
  refine writerWP_mono (writerWP_ghOf_frame x c _) ?_
  intro gh w4 ⟨h4t, h4top, h4n, h4v, h4p, h4m, h4l⟩
  simp only [writerWP_pure]
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
  have hcl : ∀ y, (∀ q ∈ [(l, false), (r, false)], y ≠ (q : NodeId × Bool).1) ↔ (y ≠ l ∧ y ≠ r) := by
    intro y; simp
  have hoBool : ∀ q ∈ [(l, false), (r, false)], (q : NodeId × Bool).2 = false := by simp
  have hyx : ∀ y, y ≠ l → y ≠ r → y ≠ x := by
    intro y hyl hyr; rcases hxlr with h | h <;> rw [h] <;> assumption
  have hpL' : (cL, l) ∈ pn.liveAt c.i := hpL
  have hadjR : ∀ q ∈ pn.liveAt c.i, cL < q.1 → cR ≤ q.1 :=
    fun q hq hlt => (hadj q.1 q.2 hq).resolve_left (by omega)
  have hhead : (!xn.leaf) = true → ∃ y, rn.live.head? = some (0, y) := by
    intro h
    obtain ⟨y0, tl, he⟩ := hrhead h
    exact ⟨y0, by rw [he]; rfl⟩
  cases hsec : second with
  | none =>
    rw [hsec] at hmkd
    have hfirst : first = mergeList (!xn.leaf) cR ln.live rn.live := splitMerged_one _ _ _ _ hmkd
    simp only [writerWP_bind, writerWP_pure]
    refine writerWP_mono (writerWP_mergeParent_room p pn (d - 1) il cL m1 ir cR none c w6 hw6p hroom
      (hdead _ _ _ _ _ _)) ?_
    intro _ w7 ⟨h7n, h7t, h7top, _, h7v, _, _, _⟩
    refine writerWP_mono (writerWP_mergeCleanup_unmadeV _ c [(l, false), (r, false)] w7 hoBool) ?_
    intro _ w8 ⟨h8t, h8top, _, h8v, h8l⟩
    try simp only [writerWP_pure]
    have h8t' : w8.taken = w3.taken := by rw [h8t, h7t, h6taken]
    have h8l' : ∀ y, y ≠ l → y ≠ r → w8.nodes.lookup y =
        (upsert w6.nodes p (mergeParentNode pn c.i il cL m1 ir cR none)).lookup y := by
      intro y hyl hyr; rw [h8l y ((hcl y).mpr ⟨hyl, hyr⟩), h7n]
    have h8v' : w8.vals = w3.vals := by rw [h8v, h7v, h6v, h5v, h4v]
    have hV8 : wValue base w8 = wValue base w3 := wValue_congr' base w8 w3 h8t' h8v'
    rw [h8top, h7top, h6top']
    apply rangeOrder_mergeOne N (wNode c.p base w8) c.i root p l r m1 pn ln rn
      (mergeParentNode pn c.i il cL m1 ir cR none) ⟨!!xn.leaf, newKlongs c.i first⟩ (!xn.leaf) cL cR
      hRO hT hp hpn hpleaf hpL hpR hclt hadjR hln hrn hlt hrt (by rw [hll]) (hrl.trans hll.symm)
      hhead hm1N (hfreshT m1 (Nat.le_refl _))
    · simp only [wNode, h8t', hm1T, Bool.false_eq_true, ↓reduceIte]
      rw [h8l' m1 (Ne.symm hlm1) (Ne.symm hrm1), lookup_upsert]
      simp only [Ne.symm hpm1, ↓reduceIte, hw6m1]
    · show (!!xn.leaf) = ln.leaf
      rw [Bool.not_not, hll]
    · intro cc z hm
      have := liveAt_newKlongs_mem (!!xn.leaf) c.i c.i first cc z hm
      rw [hfirst] at this; exact this
    · simp only [wNode, h8t', hpT, Bool.false_eq_true, ↓reduceIte]
      rw [h8l' p hpl hpr, lookup_upsert]
      simp
    · rw [mrg_mergeParentNode_leaf]; exact hpleaf
    · intro cc z hm
      exact (hparOne cc z).mp hm
    · intro y hyp hyl hyr hym
      rw [← hNw3 y]
      apply wNode_congr _ _ _ _ _ h8t'
      rw [h8l' y hyl hyr, lookup_upsert]
      simp only [hyp, ↓reduceIte]
      exact h6old y (hyx y hyl hyr) hym
  | some ksg =>
    obtain ⟨ks2, g2⟩ := ksg
    rw [hsec] at hmkd
    have hE : (first ++ ks2).map Prod.snd = (ln.live ++ rn.live).map Prod.snd := by
      rw [splitMerged_map_snd _ _ _ first ks2 g2 hmkd, mergeList_map_snd, List.map_append]
    simp only [writerWP_bind, writerWP_pure]
    refine writerWP_mono (writerWP_newKey_frame _ _ _ _ c w6) ?_
    intro m2 w7 ⟨hm2, h7n, h7t, h7top, _, h7v, _, _⟩
    have hm2' : m2 = m1 + 2 := by rw [hm2, h6next, h5next, hw4m1]
    subst hm2'
    refine writerWP_mono (writerWP_setMadeFor_frame _ _ c w7) ?_
    intro _ w8 ⟨h8n, h8t, h8top, _, h8v, _⟩
    try simp only [writerWP_pure]
    have hw6m2 : w6.nodes.lookup (m1 + 2) = none := by
      rw [h6n, h5n, lookup_append_single_ne _ _ _ _ (by rw [hw4m1]; omega),
        hlk4 _ (by omega)]
      exact hnone3 _ (by omega)
    have hw8p : w8.nodes.lookup p = some pn := by
      rw [h8n, h7n, h6next, h5next, hw4m1, lookup_append_single_ne _ _ _ _ (by omega)]
      exact hw6p
    refine writerWP_mono (writerWP_mergeParent_room p pn (d - 1) il cL m1 ir cR (some (m1 + 2, g2)) c
      w8 hw8p hroom (hdead _ _ _ _ _ _)) ?_
    intro _ w9 ⟨h9n, h9t, h9top, _, h9v, _, _, _⟩
    refine writerWP_mono (writerWP_mergeCleanup_unmadeV _ c [(l, false), (r, false)] w9 hoBool) ?_
    intro _ w10 ⟨h10t, h10top, _, h10v, h10l⟩
    try simp only [writerWP_pure]
    have h10t' : w10.taken = w3.taken := by rw [h10t, h9t, h8t, h7t, h6taken]
    have h8l : ∀ y, w8.nodes.lookup y = (w6.nodes ++ [(m1 + 2,
        ({ leaf := !!xn.leaf, ks := newKlongs c.i ks2 } : KNode))]).lookup y := by
      intro y; rw [h8n, h7n, h6next, h5next, hw4m1]
    have h10l' : ∀ y, y ≠ l → y ≠ r → w10.nodes.lookup y =
        (upsert w8.nodes p (mergeParentNode pn c.i il cL m1 ir cR (some (m1 + 2, g2)))).lookup y := by
      intro y hyl hyr; rw [h10l y ((hcl y).mpr ⟨hyl, hyr⟩), h9n]
    have hm2T : w3.taken.contains (m1 + 2) = false := (hfree _ (by omega)).2
    have h10v' : w10.vals = w3.vals := by rw [h10v, h9v, h8v, h7v, h6v, h5v, h4v]
    have hV10 : wValue base w10 = wValue base w3 := wValue_congr' base w10 w3 h10t' h10v'
    -- the halves of the merged klongs
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
    rw [h10top, h9top, h8top, h7top, h6top']
    apply rangeOrder_mergeTwo N (wNode c.p base w10) c.i root p l r m1 (m1 + 2) pn ln rn
      (mergeParentNode pn c.i il cL m1 ir cR (some (m1 + 2, g2))) ⟨!!xn.leaf, newKlongs c.i first⟩
      ⟨!!xn.leaf, newKlongs c.i ks2⟩ (!xn.leaf) cL cR g2
      hRO hT hp hpn hpleaf hpL hpR hclt hadjR hln hrn hlt hrt (by rw [hll]) (hrl.trans hll.symm)
      hhead hm1N (hfreshT m1 (Nat.le_refl _)) (hfree _ (by omega)).1 (hfreshT _ (by omega))
      (by omega)
    · simp only [wNode, h10t', hm1T, Bool.false_eq_true, ↓reduceIte]
      rw [h10l' m1 (Ne.symm hlm1) (Ne.symm hrm1), lookup_upsert]
      simp only [Ne.symm hpm1, ↓reduceIte]
      rw [h8l, lookup_append_single_ne _ _ _ _ (by omega), hw6m1]
    · show (!!xn.leaf) = ln.leaf
      rw [Bool.not_not, hll]
    · intro cc z hm
      rw [mrg_newKlongs_liveAt_iff _ c.i first hnd1 cc z, hE1] at hm
      exact ⟨List.mem_of_mem_take hm, hTDlt _ hm _ hgD⟩
    · simp only [wNode, h10t', hm2T, Bool.false_eq_true, ↓reduceIte]
      rw [h10l' _ (by omega) (by omega), lookup_upsert]
      simp only [show m1 + 2 ≠ p by omega, ↓reduceIte]
      rw [h8l, lookup_append_single_self _ _ _ hw6m2]
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
    · simp only [wNode, h10t', hpT, Bool.false_eq_true, ↓reduceIte]
      rw [h10l' p hpl hpr, lookup_upsert]
      simp
    · rw [mrg_mergeParentNode_leaf]; exact hpleaf
    · intro cc z hm
      rcases (hparTwo (m1 + 2) g2 cc z).mp hm with h | ⟨_, h⟩ | ⟨_, h1, h2, h3⟩
      · exact Or.inr (Or.inl h)
      · exact Or.inl h
      · exact Or.inr (Or.inr ⟨h3, h1, h2⟩)
    · exact (hparTwo (m1 + 2) g2 g2 (m1 + 2)).mpr (Or.inl ⟨rfl, rfl⟩)
    · intro y hyp hyl hyr hym hym2
      rw [← hNw3 y]
      apply wNode_congr _ _ _ _ _ h10t'
      rw [h10l' y hyl hyr, lookup_upsert]
      simp only [hyp, ↓reduceIte]
      rw [h8l, lookup_append_single_ne _ _ _ _ hym2]
      exact h6old y (hyx y hyl hyr) hym

/-- The writer's merge keeps the walk's ranges (`RangeOrder`): x at depth d
merged with a sibling under a reached inner parent with room, neither made by
the transaction; the premises those of prover cost's `writerWP_merge_get`. -/
theorem writerWP_merge_range (x : NodeId) (d : Nat) (c : Ctx) (base : View BVal)
    (hvc : ViewCoherent c base) (w : W)
    (hT : TreeOK (wNode c.p base w) c.i w.top.rootKey)
    (hpar : ∀ p, (w.path[d - 1]?).map (·.2) = some p →
      TReach (wNode c.p base w) c.i w.top.rootKey p ∧ ∃ pn, wNode c.p base w p = some pn ∧
        pn.leaf = false ∧ pn.size + 4 ≤ c.p.M ∧
        (∀ il cL m1 ir cR m2, deadOver c.p (mergeParentNode pn c.i il cL m1 ir cR m2) = false) ∧
        klongsWf pn.ks = true ∧ (∀ s, Klong.time s ∈ pn.ks → s ≤ c.i) ∧
        ∀ cc z zn, (cc, z) ∈ pn.liveAt c.i → wNode c.p base w z = some zn →
          zn.firstTime ≠ some c.i ∧ ∀ s, Klong.time s ∈ zn.ks → s ≤ c.i)
    (hRt : ∀ y, TReach (wNode c.p base w) c.i w.top.rootKey y → w.taken.contains y = false)
    (hids : (∀ z, (w.nodes.lookup z).isSome = true → z < w.next) ∧
      (∀ z, (c.view z).isSome = true → z < w.next) ∧ (∀ z, w.taken.contains z = true → z < w.next))
    (hbaseF : ∀ z, w.next ≤ z → knodeOf c.p base z = none)
    (hfreshT : ∀ z, w.next ≤ z → ∀ u c', TReach (wNode c.p base w) c.i w.top.rootKey u →
      ¬ TLink (wNode c.p base w) c.i u c' z)
    (hR : RangeOrder (wNode c.p base w) c.i w.top.rootKey) (hcap : 1 ≤ c.p.mergeMax)
    (htimesN : ∀ y yn, wNode c.p base w y = some yn → ∀ s, Klong.time s ∈ yn.ks → s ≤ c.i)
    (hwfN : ∀ y yn, wNode c.p base w y = some yn → klongsWf yn.ks = true) :
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
    obtain ⟨hpR, pn0, hpn0, hpleaf, hroom, hdead, hpwf, hpt, hch⟩ := hpar e.2 (by rw [he]; rfl)
    refine writerWP_mono (writerWP_getNode_all e.2 c w base hvc) ?_
    intro pn w1 ⟨hr1, hlk1, hwn1, hpre1, hsrc1⟩
    rw [hwn1 (hRt _ hpR)] at hpn0
    cases hpn0
    -- the tail from any state that reads as w
    have hpn : wNode c.p base w e.2 = some pn0 := hwn1 (hRt _ hpR)
    have hpRS := tReach_reachS _ c.i _ _ hpR
    have tailOK : ∀ (leftSome : Bool) (l : NodeId) (ln : KNode) (il : Nat) (r : NodeId)
        (rn : KNode) (ir cL cR : Nat) (xn : KNode) (w3 : W), ReadsAs c.p base w w3 →
        w1.nodes <+: w3.nodes → (∀ z, (w3.nodes.lookup z).isSome = true → z < w.next) →
        pn0.ks[il]? = some (.key cL l) → LastLive pn0.ks pn0.lastBitmap il cL →
        pn0.ks[ir]? = some (.key cR r) → LastLive pn0.ks pn0.lastBitmap ir cR → cL < cR →
        (∀ cc z, (cc, z) ∈ pn0.liveAt c.i → cc ≤ cL ∨ cR ≤ cc) →
        ln.leaf = xn.leaf → rn.leaf = xn.leaf →
        (x = l ∨ x = r) → wNode c.p base w l = some ln → wNode c.p base w r = some rn →
        WriterWP (mergeTail c x d e.2 pn0 xn leftSome l ln il r rn ir) c w3
          (fun _ w' => RangeOrder (wNode c.p base w') c.i w'.top.rootKey) := by
      intro leftSome l ln il r rn ir cL cR xn w3 hr3 hpre3 hsrc3 hL hLL hR' hRL hclt hadj hll hrl
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
      refine writerWP_mono (writerWP_mergeTail_range c base x d e.2 pn0 xn leftSome l ln il r rn ir cL cR
        (wNode c.p base w) w.top.rootKey w.next w3 hT hpR hpn hL hLL hR' hRL (by omega) hxlr
        hln hrn hroom hdead hpwf hpt hch hr3.1 (by rw [hr3.2.1]) hr3.2.2.2.2
        (lookup_of_prefix _ _ hpre3 _ _ hlk1) hsrc3
        (fun z hz => ⟨(hfree z hz).1, by rw [hr3.2.2.1]; exact (hfree z hz).2⟩) hfreshT
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
        htimesN hwfN hR) ?_
      intro _ w' h
      exact h
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
    refine writerWP_mono (writerWP_getNode_all x c w1 base hvc) ?_
    intro xn w2 ⟨hr2, hlk2, hwn2, hpre2, hsrc2⟩
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
            (∀ z, (wb.nodes.lookup z).isSome = true → z < w.next) →
            LastLive pn0.ks pn0.lastBitmap ia0 cva → cx < cva →
            (mergeIdx pn0 cx).2.1 = some (ia0, cva) →
            WriterWP (do
              let __x ← sibling e.2 pn0 ia0 !xn.leaf
              mergeTail c x d e.2 pn0 xn false x xn ix __x.1 __x.2 ia0) c wb
              (fun _ w' => RangeOrder (wNode c.p base w') c.i w'.top.rootKey) := by
          intro wb ia0 cva hrb hpreb hsrcb hLa hax hia
          rw [writerWP_bind]
          refine writerWP_mono (writerWP_sibling_leaf e.2 pn0 ia0 (!xn.leaf) c wb base hvc) ?_
          rintro ⟨rs, rsn⟩ w4 ⟨hs1, hr4, _, hwn4, hpre4, hsrc4, hsl⟩
          obtain ⟨hka, hrn, hr04, hpre14, hsrc04⟩ :=
            hsib wb ia0 cva (rs, rsn) w4 hrb hpreb hsrcb hLa hs1 hr4 hpre4 hsrc4 hwn4
          have hmin := mergeIdx_right_min pn0 cx ia0 cva hia
          exact tailOK false x xn ix rs rsn ia0 cx cva xn w4 hr04 hpre14 hsrc04 hkx hLx hka hLa
            hax (by
              intro cc z hm
              rcases Nat.lt_or_ge cx cc with h | h
              · have hm' : (cc, z) ∈ pn0.live := by rw [← KNode.liveAt_of_times pn0 c.i hpt]; exact hm
                exact Or.inr (hmin cc z hm' h)
              · exact Or.inl h) rfl (by rw [hsl]; simp) (Or.inl rfl) hxn hrn
        split
        · rename_i ib0 cvb
          obtain ⟨hLb, hbx⟩ := hMb ib0 cvb rfl
          simp only [writerWP_bind]
          refine writerWP_mono (writerWP_sibling_leaf e.2 pn0 ib0 (!xn.leaf) c w2 base hvc) ?_
          rintro ⟨ls, lsn⟩ w3 ⟨hs1, hr3, _, hwn3, hpre3, hsrc3, hsl⟩
          obtain ⟨hkb, hln, hr03, hpre13, hsrc03⟩ :=
            hsib w2 ib0 cvb (ls, lsn) w3 hr02 hpre02 hsrc02 hLb hs1 hr3 hpre3 hsrc3 hwn3
          refine writerWP_if _ _ _ _ _ _ (fun _ => ?_) (fun _ => ?_)
          · show WriterWP (mergeTail c x d e.2 pn0 xn true ls lsn ib0 x xn ix) c w3 _
            have hmax := mergeIdx_left_max pn0 cx ib0 cvb (by rw [hmi])
            exact tailOK true ls lsn ib0 x xn ix cvb cx xn w3 hr03 hpre13 hsrc03 hkb hLb hkx hLx
              hbx (by
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
              exact hright w3 ia0 cva hr03 hpre13 hsrc03 hLa hax (by rw [hmi])
            · exact writerWP_throw _ _ _ _
        · rw [writerWP_bind, writerWP_pure]
          dsimp only
          split
          · rename_i ia0 cva
            obtain ⟨hLa, hax⟩ := hMa ia0 cva rfl
            exact hright w2 ia0 cva hr02 hpre02 hsrc02 hLa hax (by rw [hmi])
          · exact writerWP_throw _ _ _ _
      · exact writerWP_throw _ _ _ _
    · exact writerWP_throw _ _ _ _
  · exact writerWP_throw _ _ _ _

end SIS.Tree
