/-
The dead klongs' bound through a merge (bergdb 024-12, section 1, `d4`'s plan of
2026-11-15, step 2; `DW`, DeadLocal.lean): the merge's new nodes hold no dead
klong when the two siblings' live klongs are in order about the parent's klong of
the right one (`mergeKlongs_deadCount`'s premises, here from the ranges given as
in `writerWP_mergeTail_any_get`); the parent and the merged nodes keep it as
`dw_mergeParent` and `dw_mergeCleanup` say.
-/
import SIS.Tree.DeadDelete
import SIS.Tree.GetMergeAny

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

set_option maxHeartbeats 8000000 in
/-- The merge after its reads keeps `DW`, given the siblings' ranges about the
parent's klongs (`hlrange`, `hllow`, `hrrange`, `hrup`) and their adjacency in the
parent (`hadj`). -/
theorem dw_mergeTail (base : View BVal) (c : Ctx) (x : NodeId) (d : Nat) (p : NodeId) (pn xn : KNode)
    (leftSome : Bool) (l : NodeId) (ln : KNode) (il : Nat) (r : NodeId) (rn : KNode) (ir cL cR : Nat)
    (w3 : W) (hvc : ViewCoherent c base) (hth : 2 ≤ c.p.theta ∨ c.p.theta = 0) (hw3 : DW c base w3)
    (hlk : w3.nodes.lookup p = some pn) (hpn : DOK c.p pn ∨ w3.taken.contains p = true)
    (hpx : p ≠ x)
    (hL : pn.ks[il]? = some (.key cL l)) (hLL : LastLive pn.ks pn.lastBitmap il cL)
    (hR : pn.ks[ir]? = some (.key cR r)) (hRL : LastLive pn.ks pn.lastBitmap ir cR)
    (hclt : cL < cR) (hpt : ∀ s, Klong.time s ∈ pn.ks → s ≤ c.i)
    (hadj : ∀ cc z, (cc, z) ∈ pn.liveAt c.i → cc ≤ cL ∨ cR ≤ cc)
    (hlt : ∀ s, Klong.time s ∈ ln.ks → s ≤ c.i) (hrt : ∀ s, Klong.time s ∈ rn.ks → s ≤ c.i)
    (hlrange : ∀ cc z, (cc, z) ∈ ln.liveAt c.i → cc < cR)
    (hllow : ∀ cc z, (cc, z) ∈ ln.liveAt c.i →
      ((!xn.leaf) = true → cc = 0 ∨ cL < cc) ∧ ((!xn.leaf) = false → cL ≤ cc))
    (hrrange : ∀ cc z, (cc, z) ∈ rn.liveAt c.i →
      ((!xn.leaf) = true → cc = 0 ∨ cR < cc) ∧ ((!xn.leaf) = false → cR ≤ cc))
    (hrup : ∀ k z, (k, z) ∈ pn.liveAt c.i → cR < k → ∀ cc z', (cc, z') ∈ rn.liveAt c.i → cc < k)
    (hcap : 1 ≤ c.p.mergeMax) :
    WriterWP (mergeTail c x d p pn xn leftSome l ln il r rn ir) c w3 (fun _ v => DW c base v) := by
  have hcvL : pn.cv? il = some cL := by simp [KNode.cv?, hL]
  have hcvR : pn.cv? ir = some cR := by simp [KNode.cv?, hR]
  have hkR : pn.live.lookup cR = some r := by
    rw [KNode.live_lookup]; exact keyLookup_of_last _ _ _ ir r hR hRL
  have hcR : cR ∈ pn.live.map Prod.fst := List.mem_map.mpr ⟨(cR, r), bk_mem_of_lookup _ _ _ hkR, rfl⟩
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
  have hmkd : splitMerged (!xn.leaf) c.p.mergeMax (mergeList (!xn.leaf) cR ln.live rn.live) =
      (first, second) := hmk
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
  -- the new nodes hold no dead klong, and the second's compare value is not live in p
  have hnew : DOK c.p ⟨!(!xn.leaf), newKlongs c.i first⟩ ∧
      ∀ ks2 g2, second = some (ks2, g2) → DOK c.p ⟨!(!xn.leaf), newKlongs c.i ks2⟩ ∧
        (g2 ≠ cR → pn.live.lookup g2 = none) := by
    cases hsec : second with
    | none =>
      rw [hsec] at hmkd
      have hfirst : first = mergeList (!xn.leaf) cR ln.live rn.live := splitMerged_one _ _ _ _ hmkd
      refine ⟨dok_newKlongs _ _ _ _ ?_, fun _ _ h => by cases h⟩
      rw [hfirst]
      exact List.pairwise_map.mpr (hsortE.imp (by intro a b hab; omega))
    | some kg =>
      obtain ⟨ks2, g2⟩ := kg
      rw [hsec] at hmkd
      obtain ⟨yg, hE1, hgs, hE2⟩ := mrg_splitMerged_two (!xn.leaf) c.p.mergeMax hcap _ first ks2 g2 hmkd
      have hElen : c.p.mergeMax < (mergeList (!xn.leaf) cR ln.live rn.live).length := by
        rcases Nat.lt_or_ge c.p.mergeMax (mergeList (!xn.leaf) cR ln.live rn.live).length with h | h
        · exact h
        · exfalso
          unfold splitMerged at hmkd
          simp only [show (mergeList (!xn.leaf) cR ln.live rn.live).length ≤ c.p.mergeMax from h,
            ↓reduceIte, Prod.mk.injEq, reduceCtorEq, and_false] at hmkd
      obtain ⟨hgL, _, hgU0⟩ := mrg_two_g (!xn.leaf) cL cR ln.live rn.live
        (((mergeList (!xn.leaf) cR ln.live rn.live).length + 1) / 2) g2 yg hsortE (by omega) hgs
        hclt hlnL hrnR
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
      refine ⟨dok_newKlongs _ _ _ _ hnd1, fun ks2' g2' h => ?_⟩
      cases h
      refine ⟨dok_newKlongs _ _ _ _ hnd2, fun hne => ?_⟩
      cases hlg : pn.live.lookup g2 with
      | none => rfl
      | some z =>
        exfalso
        have hm : (g2, z) ∈ pn.liveAt c.i := by
          rw [KNode.liveAt_of_times pn c.i hpt]; exact bk_mem_of_lookup _ _ _ hlg
        rcases hadj g2 z hm with h1 | h1
        · omega
        · have hgt : cR < g2 := by omega
          have := hgU0 g2 hgt (fun q hq => hrup g2 z hm hgt q.1 q.2 (by
            rw [KNode.liveAt_of_times rn c.i hrt]; exact hq))
          omega
  obtain ⟨hdok1, hdok2⟩ := hnew
  have hw3' : DW c base w3 := hw3
  simp only [writerWP_bind, writerWP_modify, writerWP_pure]
  refine writerWP_mono (writerWP_and (dw_ghOf base x c _ hvc (dw_same rfl rfl hw3'))
    (writerWP_ghOf_frame x c _)) ?_
  rintro ⟨g, h⟩ w4 ⟨⟨hw4, _⟩, h4t, _, _, _, _, _, h4l⟩
  have hlk4 : w4.nodes.lookup p = some pn := by rw [h4l p hpx]; exact hlk
  have hpn4 : DOK c.p pn ∨ w4.taken.contains p = true := by rw [h4t]; exact hpn
  dsimp only
  cases lMade <;> cases rMade <;>
    simp only [Bool.false_eq_true, ↓reduceIte, writerWP_bind, writerWP_modify, writerWP_pure,
      replacedBy, writerWP_get]
  all_goals
    refine writerWP_mono (writerWP_and (dw_newKey base g h _ _ c _ (dw_same rfl rfl hw4) hdok1)
      (writerWP_newKey_frame _ _ _ _ c _)) ?_
    rintro m1 w5 ⟨⟨hw5, _⟩, _, h5n, h5t, _, _, _, _, _⟩
    refine writerWP_mono (writerWP_and (dw_frame base _ c _ (fr_setMadeFor _ _ c _) hw5)
      (writerWP_setMadeFor_frame _ _ c _)) ?_
    rintro _ w6 ⟨⟨hw6, _⟩, h6n, h6t, _⟩
    have hlk6 : w6.nodes.lookup p = some pn := by
      rw [h6n, h5n, List.lookup_append]
      show (List.lookup p w4.nodes).or _ = _
      rw [hlk4]; rfl
    have hpn6 : DOK c.p pn ∨ w6.taken.contains p = true := by
      rw [h6t, h5t]; first | exact hpn4 | exact hpn
    cases hsec : second with
    | none =>
      simp only [writerWP_bind, writerWP_pure]
      refine writerWP_mono (dw_mergeParent base p pn (d - 1) il cL m1 ir cR none c w6 hvc hth hw6 hlk6 hpn6
        hcR (fun _ _ h => by cases h)) ?_
      intro _ w7 hw7
      refine writerWP_mono (dw_mergeCleanup base p m1 c hvc hth _ w7 hw7) ?_
      intro _ w8 hw8
      first | exact hw8 | (simp only [writerWP_pure]; exact hw8)
    | some kg =>
      obtain ⟨ks2, g2⟩ := kg
      obtain ⟨hdk2, hg2⟩ := hdok2 ks2 g2 hsec
      simp only [writerWP_bind, writerWP_pure]
      refine writerWP_mono (writerWP_and (dw_newKey base g h _ _ c _ hw6 hdk2)
        (writerWP_newKey_frame _ _ _ _ c _)) ?_
      rintro m2 w7 ⟨⟨hw7, _⟩, _, h7n, h7t, _, _, _, _, _⟩
      try simp only [writerWP_bind, writerWP_pure, writerWP_get]
      refine writerWP_mono (writerWP_and (dw_frame base _ c _ (fr_setMadeFor _ _ c _) hw7)
        (writerWP_setMadeFor_frame _ _ c _)) ?_
      rintro _ w8 ⟨⟨hw8, _⟩, h8n, h8t, _⟩
      try simp only [writerWP_pure]
      have hlk8 : w8.nodes.lookup p = some pn := by
        rw [h8n, h7n, List.lookup_append, hlk6]; rfl
      have hpn8 : DOK c.p pn ∨ w8.taken.contains p = true := by rw [h8t, h7t]; exact hpn6
      refine writerWP_mono (dw_mergeParent base p pn (d - 1) il cL m1 ir cR (some (m2, g2)) c w8 hvc hth hw8
        hlk8 hpn8 hcR (fun y g h hne => by cases h; exact hg2 hne)) ?_
      intro _ w9 hw9
      refine writerWP_mono (dw_mergeCleanup base p m1 c hvc hth _ w9 hw9) ?_
      intro _ w10 hw10
      first | exact hw10 | (simp only [writerWP_pure]; exact hw10)

set_option maxHeartbeats 8000000 in
/-- A merge keeps `DW`, from the ranges of the state it starts from (`hR`), the
parent on the key access path reached and inner (`hpar`), and the reached nodes
not taken back (`hRt`). -/
theorem dw_merge (base : View BVal) (x : NodeId) (d : Nat) (c : Ctx) (w : W)
    (hvc : ViewCoherent c base) (hth : 2 ≤ c.p.theta ∨ c.p.theta = 0) (hcap : 1 ≤ c.p.mergeMax)
    (hw : DW c base w)
    (hT : TreeOK (wNode c.p base w) c.i w.top.rootKey)
    (hR : RangeOrder (wNode c.p base w) c.i w.top.rootKey)
    (hpar : ∀ p, (w.path[d - 1]?).map (·.2) = some p →
      TReach (wNode c.p base w) c.i w.top.rootKey p ∧ ∃ pn, wNode c.p base w p = some pn ∧
        pn.leaf = false ∧ (∀ s, Klong.time s ∈ pn.ks → s ≤ c.i) ∧
        ∀ cc z zn, (cc, z) ∈ pn.liveAt c.i → wNode c.p base w z = some zn →
          ∀ s, Klong.time s ∈ zn.ks → s ≤ c.i)
    (hRt : ∀ y, TReach (wNode c.p base w) c.i w.top.rootKey y → w.taken.contains y = false) :
    WriterWP (merge x d) c w (fun _ v => DW c base v) := by
  unfold merge
  simp only [writerWP_bind, writerWP_read]
  unfold pathNode
  simp only [writerWP_bind, writerWP_get]
  split
  · rename_i e he
    simp only [writerWP_pure]
    obtain ⟨hpR, pn0, hpn0, hpleaf, hpt, hch⟩ := hpar e.2 (by rw [he]; rfl)
    refine writerWP_mono (writerWP_getNode_all e.2 c w base hvc) ?_
    intro pn w1 ⟨hr1, hlk1, hwn1, hpre1, _⟩
    rw [hwn1 (hRt _ hpR)] at hpn0
    cases hpn0
    have hpn : wNode c.p base w e.2 = some pn0 := hwn1 (hRt _ hpR)
    have hpRS := tReach_reachS _ c.i _ _ hpR
    have hpDOK : DOK c.p pn0 := dw_node hw hpn
    -- the tail from any state that reads as w
    have tailDW : ∀ (leftSome : Bool) (l : NodeId) (ln : KNode) (il : Nat) (r : NodeId)
        (rn : KNode) (ir cL cR : Nat) (xn : KNode) (w3 : W), ReadsAs c.p base w w3 →
        w1.nodes <+: w3.nodes →
        pn0.ks[il]? = some (.key cL l) → LastLive pn0.ks pn0.lastBitmap il cL →
        pn0.ks[ir]? = some (.key cR r) → LastLive pn0.ks pn0.lastBitmap ir cR → cL < cR →
        (∀ cc z, (cc, z) ∈ pn0.liveAt c.i → cc ≤ cL ∨ cR ≤ cc) →
        ln.leaf = xn.leaf → rn.leaf = xn.leaf →
        (x = l ∨ x = r) → wNode c.p base w l = some ln → wNode c.p base w r = some rn →
        WriterWP (mergeTail c x d e.2 pn0 xn leftSome l ln il r rn ir) c w3
          (fun _ v => DW c base v) := by
      intro leftSome l ln il r rn ir cL cR xn w3 hr3 hpre3 hL hLL hR' hRL hclt hadj hll hrl hxlr hln hrn
      have hmemL : (cL, l) ∈ pn0.liveAt c.i := by
        rw [KNode.liveAt_of_times pn0 c.i hpt]
        apply bk_mem_of_lookup
        rw [KNode.live_lookup]
        exact keyLookup_of_last _ _ _ il l hL hLL
      have hmemR : (cR, r) ∈ pn0.liveAt c.i := by
        rw [KNode.liveAt_of_times pn0 c.i hpt]
        apply bk_mem_of_lookup
        rw [KNode.live_lookup]
        exact keyLookup_of_last _ _ _ ir r hR' hRL
      have hlink_l : TLink (wNode c.p base w) c.i e.2 cL l := ⟨pn0, hpn, hmemL⟩
      have hlink_r : TLink (wNode c.p base w) c.i e.2 cR r := ⟨pn0, hpn, hmemR⟩
      have hpl : e.2 ≠ l := fun h => hT.no_self_link e.2 cL hpR (by rw [← h] at hlink_l; exact hlink_l)
      have hpr : e.2 ≠ r := fun h => hT.no_self_link e.2 cR hpR (by rw [← h] at hlink_r; exact hlink_r)
      have hpx : e.2 ≠ x := by rcases hxlr with h | h <;> rw [h] <;> assumption
      obtain ⟨hlr1, hlr2⟩ := mrg_child_range (wNode c.p base w) c.i w.top.rootKey hR e.2 pn0 hpRS hpn
        hpleaf cL l ln hmemL hln
      obtain ⟨hrr1, hrr2⟩ := mrg_child_range (wNode c.p base w) c.i w.top.rootKey hR e.2 pn0 hpRS hpn
        hpleaf cR r rn hmemR hrn
      refine dw_mergeTail base c x d e.2 pn0 xn leftSome l ln il r rn ir cL cR w3 hvc hth
        (dw_of_wNode hr3.1 hw) (lookup_of_prefix _ _ hpre3 _ _ hlk1) (Or.inl hpDOK) hpx hL hLL hR' hRL
        hclt hpt hadj (hch cL l ln hmemL hln) (hch cR r rn hmemR hrn)
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
        (fun k z hk hkc cc z' h => hrr2 k z hk hkc cc z' h) hcap
    have hchild : ∀ i cv y, pn0.ks[i]? = some (.key cv y) → LastLive pn0.ks pn0.lastBitmap i cv →
        (cv, y) ∈ pn0.liveAt c.i ∧ TReach (wNode c.p base w) c.i w.top.rootKey y := by
      intro i cv y hk hl
      have hm : (cv, y) ∈ pn0.liveAt c.i := by
        rw [KNode.liveAt_of_times pn0 c.i hpt]
        apply bk_mem_of_lookup
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
    intro xn w2 ⟨hr2, _, hwn2, hpre2, _⟩
    have hr02 := ReadsAs.trans _ _ _ _ _ hr1 hr2
    have hpre02 : w1.nodes <+: w2.nodes := hpre2
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
        have hsib : ∀ (wb : W) (i cv : Nat) (sn : NodeId × KNode) (w3 : W),
            ReadsAs c.p base w wb → w1.nodes <+: wb.nodes →
            LastLive pn0.ks pn0.lastBitmap i cv →
            pn0.ptr? i = some sn.1 → ReadsAs c.p base wb w3 → wb.nodes <+: w3.nodes →
            (wb.taken.contains sn.1 = false → wNode c.p base wb sn.1 = some sn.2) →
            pn0.ks[i]? = some (.key cv sn.1) ∧ wNode c.p base w sn.1 = some sn.2 ∧
              ReadsAs c.p base w w3 ∧ w1.nodes <+: w3.nodes := by
          intro wb i cv sn w3 hrb hpreb hl hp hr3 hpre3 hwn3
          have hk := hptrk i cv sn.1 hl hp
          obtain ⟨_, hsR⟩ := hchild i cv sn.1 hk hl
          refine ⟨hk, ?_, ReadsAs.trans _ _ _ _ _ hrb hr3, hpreb.trans hpre3⟩
          rw [← hrb.1]; exact hwn3 (by rw [hrb.2.2.1]; exact hRt _ hsR)
        have hright : ∀ (wb : W) (ia0 cva : Nat), ReadsAs c.p base w wb → w1.nodes <+: wb.nodes →
            LastLive pn0.ks pn0.lastBitmap ia0 cva → cx < cva →
            (mergeIdx pn0 cx).2.1 = some (ia0, cva) →
            WriterWP (do
              let __x ← sibling e.2 pn0 ia0 !xn.leaf
              mergeTail c x d e.2 pn0 xn false x xn ix __x.1 __x.2 ia0) c wb
              (fun _ v => DW c base v) := by
          intro wb ia0 cva hrb hpreb hLa hax hia
          rw [writerWP_bind]
          refine writerWP_mono (writerWP_sibling_leaf e.2 pn0 ia0 (!xn.leaf) c wb base hvc) ?_
          rintro ⟨rs, rsn⟩ w4 ⟨hs1, hr4, _, hwn4, hpre4, _, hsl⟩
          obtain ⟨hka, hrn, hr04, hpre14⟩ :=
            hsib wb ia0 cva (rs, rsn) w4 hrb hpreb hLa hs1 hr4 hpre4 hwn4
          have hmin := mergeIdx_right_min pn0 cx ia0 cva hia
          exact tailDW false x xn ix rs rsn ia0 cx cva xn w4 hr04 hpre14 hkx hLx hka hLa
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
          rintro ⟨ls, lsn⟩ w3 ⟨hs1, hr3, _, hwn3, hpre3, _, hsl⟩
          obtain ⟨hkb, hln, hr03, hpre13⟩ :=
            hsib w2 ib0 cvb (ls, lsn) w3 hr02 hpre02 hLb hs1 hr3 hpre3 hwn3
          refine writerWP_if _ _ _ _ _ _ (fun _ => ?_) (fun _ => ?_)
          · show WriterWP (mergeTail c x d e.2 pn0 xn true ls lsn ib0 x xn ix) c w3 _
            have hmax := mergeIdx_left_max pn0 cx ib0 cvb (by rw [hmi])
            exact tailDW true ls lsn ib0 x xn ix cvb cx xn w3 hr03 hpre13 hkb hLb hkx hLx
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
              exact hright w3 ia0 cva hr03 hpre13 hLa hax (by rw [hmi])
            · exact writerWP_throw _ _ _ _
        · rw [writerWP_bind, writerWP_pure]
          dsimp only
          split
          · rename_i ia0 cva
            obtain ⟨hLa, hax⟩ := hMa ia0 cva rfl
            exact hright w2 ia0 cva hr02 hpre02 hLa hax (by rw [hmi])
          · exact writerWP_throw _ _ _ _
      · exact writerWP_throw _ _ _ _
    · exact writerWP_throw _ _ _ _
  · exact writerWP_throw _ _ _ _

end SIS.Tree
