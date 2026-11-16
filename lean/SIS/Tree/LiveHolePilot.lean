/-
The pilot of `l4`'s route B (bergdb 030-01, step 2): one merge of the merges'
loop keeps the hole's form, the hole one height up.

`liveHoleW_merge_pilot`: at a round of `mergeUp` at (g, h), whose descent finds
x at depth d under its parent p, a merge into one node of x with a sibling
(`merge x d`), p with room, no compaction and no child made by the
transaction, takes `LiveHoleW key g h` (the live counts but at the node the
round's descent finds) to `LiveHoleW key g (h + 1)`. Its parts:

* `writerWP_mergeTail_livePilot`, `writerWP_merge_livePilot`: the merge at the
  writer's level, on the steps of `writerWP_mergeTail_any_treeS2` and
  `dw_merge`, gives `LiveEdgesH` with p the hole (`liveEdgesH_mergeOne`) and
  reads every node but p, its children and the new node as before;
* `gradedL_of_ht`: the heights' walk (`HtInv`) gives the heights of the
  descent's path one less below each inner node;
* with them `descendToHeight_up` (LiveHoleDescent.lean) gives that the next
  round's descent finds p (030-01's stall point R1).

`HoleAtW` is `HoleAt` (LiveHole.lean) for the writer's preconditions: the node
that every successful run of the descent finds, so that the next round's hole
follows from a precondition of its descent; `HoleAt` asked for a run.
-/
import SIS.Tree.LiveHoleDescent
import SIS.Tree.MergeTreeInv
import SIS.Tree.WriterGetMergeMade
import SIS.Tree.MergeLiveFill
import SIS.Tree.MergePathCache
import SIS.Tree.WriterHeightsDel
import SIS.Tree.WriterBookMerge
import SIS.Tree.WriterMergeUpLoop
set_option autoImplicit false
namespace SIS.Tree
open SIS SIS.Check

theorem writerWP_true {α : Type} (f : M α) (c : Ctx) (w : W) : WriterWP f c w (fun _ _ => True) :=
  fun _ _ _ => trivial

/-- `mergeParent` of a merge into one node, with room and no compaction: the
parent's new version stored in place. -/
theorem writerWP_mergeParent_roomOne (p : NodeId) (pn : KNode) (depth il cL : Nat) (m1 : NodeId)
    (ir cR : Nat) (c : Ctx) (w : W) (post : Unit → W → Prop)
    (hlk : w.nodes.lookup p = some pn) (hroom : pn.size + 3 ≤ c.p.M)
    (hnd : deadOver c.p (mergeParentNode pn c.i il cL m1 ir cR none) = false)
    (hroomP : ∀ s : String, post () ({ ({ w with trail := s :: w.trail } : W) with
      nodes := upsert w.nodes p (mergeParentNode pn c.i il cL m1 ir cR none) } : W)) :
    WriterWP (mergeParent p depth il cL m1 ir cR none) c w post := by
  unfold mergeParent
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_getNode_known p pn c w hlk]
  apply writerWP_if
  · intro _
    apply writerWP_if
    · intro hd
      exfalso
      have h' : deadOver c.p (mergeParentNode pn c.i il cL m1 ir cR none) = true := hd
      rw [hnd] at h'
      cases h'
    · intro _
      simp only [note, putNode, writerWP_bind, writerWP_modify]
      exact hroomP _
  · intro hn
    exfalso
    apply hn
    simp only [Option.isNone_none, Bool.true_or, ↓reduceIte, Nat.add_zero]
    repeat' split
    all_goals omega

set_option maxHeartbeats 4000000 in
/-- The pilot (bergdb 030-01, step 2): a merge into one node of two siblings that
the transaction did not make, the parent with room and no compaction, keeps the
hole's form, the parent the hole after; the nodes but the parent, the two
merged and the new one keep their lookups. -/
theorem writerWP_mergeTail_livePilot (c : Ctx) (base : View BVal) (x : NodeId) (d : Nat) (p : NodeId)
    (pn xn : KNode) (leftSome : Bool) (l : NodeId) (ln : KNode) (il : Nat) (r : NodeId)
    (rn : KNode) (ir : Nat) (cL cR : Nat) (N : NodeId → Option KNode) (root : NodeId) (nx : Nat)
    (w3 : W) (Hl : NodeId → Prop) (hm : c.p.merges = true)
    (hT : TreeOK N c.i root) (hp : TReach N c.i root p) (hpn : N p = some pn)
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
    (hpleaf : pn.leaf = false) (hll : ln.leaf = xn.leaf) (hrl : rn.leaf = xn.leaf)
    (hlrange : ∀ cc z, (cc, z) ∈ ln.liveAt c.i → cc < cR)
    (hrrange : ∀ cc z, (cc, z) ∈ rn.liveAt c.i →
      ((!xn.leaf) = true → cc = 0 ∨ cR < cc) ∧ ((!xn.leaf) = false → cR ≤ cc))
    (hlm : (ln.firstTime == some c.i) = false) (hrm : (rn.firstTime == some c.i) = false)
    (hroom : pn.size + 3 ≤ c.p.M)
    (hnd : deadOver c.p (mergeParentNode pn c.i il cL nx ir cR none) = false)
    (hLive : LiveEdgesH c.p N c.i root Hl) (hHl : ∀ y, Hl y → y = x) :
    WriterWP (mergeTail c x d p pn xn leftSome l ln il r rn ir) c w3
      (fun res w' => res = 1 → LiveEdgesH c.p (wNode c.p base w') c.i w'.top.rootKey (fun y => y = p) ∧
        (∀ y, y ≠ p → y ≠ l → y ≠ r → y ≠ nx → w'.nodes.lookup y = w3.nodes.lookup y) ∧
        w'.top = w3.top) := by
  -- the tree's facts
  have hpL : (cL, l) ∈ pn.liveAt c.i := by
    rw [KNode.liveAt_of_times pn c.i hpt]
    apply bk_mem_of_lookup
    rw [KNode.live_lookup]
    exact keyLookup_of_last _ _ _ il l hL hLL
  have hpR : (cR, r) ∈ pn.liveAt c.i := by
    rw [KNode.liveAt_of_times pn c.i hpt]
    apply bk_mem_of_lookup
    rw [KNode.live_lookup]
    exact keyLookup_of_last _ _ _ ir r hR hRL
  have hlink_l : TLink N c.i p cL l := ⟨pn, hpn, hpL⟩
  have hlink_r : TLink N c.i p cR r := ⟨pn, hpn, hpR⟩
  have hpl : p ≠ l := fun h => hT.no_self_link p cL hp (by rw [← h] at hlink_l; exact hlink_l)
  have hpr : p ≠ r := fun h => hT.no_self_link p cR hp (by rw [← h] at hlink_r; exact hlink_r)
  have hlr : l ≠ r := fun h => hc (hT.oneLink p cL p cR l hp hp hlink_l (by rw [h]; exact hlink_r)).2
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
  -- the sibling of the hole is filled: the two hold m live klongs or more
  have hsib : c.p.mergeBelow ≤ ln.live.length + rn.live.length := by
    have hok : ∀ s sn, N s = some sn → (∃ cs, (cs, s) ∈ pn.liveAt c.i) → s ≠ x →
        c.p.mergeBelow ≤ (sn.liveAt c.i).length := by
      intro s sn hs ⟨cs, hcs⟩ hsx
      exact ((hLive.2 p pn cs s sn hp hpn hcs hs).1 (fun h => hsx (hHl s h))).2.2 hpleaf hm
    rcases hxlr with hx | hx
    · have := hok r rn hrn ⟨cR, hpR⟩ (by rw [hx]; exact hlr.symm)
      rw [KNode.liveAt_of_times rn c.i hrt] at this
      omega
    · have := hok l ln hln ⟨cL, hpL⟩ (by rw [hx]; exact hlr)
      rw [KNode.liveAt_of_times ln c.i hlt] at this
      omega
  unfold mergeTail
  simp only [hcvL, hcvR]
  rw [hlm, hrm]
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
  simp only [writerWP_bind, writerWP_modify]
  refine writerWP_mono (writerWP_ghOf_frame x c _) ?_
  intro gh w4 ⟨h4t, h4top, h4n, h4v, h4p, h4m, h4l⟩
  simp only [Bool.false_eq_true, ↓reduceIte, writerWP_bind, writerWP_pure]
  refine writerWP_mono (writerWP_newKey_frame _ _ _ _ c _) ?_
  intro m1 w5 ⟨hm1, h5n, h5t, h5top, h5next, h5v, h5p, h5m⟩
  refine writerWP_mono (writerWP_setMadeFor_frame _ _ c _) ?_
  intro _ w6 ⟨h6n, h6t, h6top, h6next, h6v, h6p⟩
  have hm1 : m1 = nx := by rw [hm1, h4n, h3next]
  subst hm1
  have hxnx : x < m1 := by rcases hxlr with h | h <;> rw [h] <;> assumption
  have hlk4 : ∀ y, y ≠ x → w4.nodes.lookup y = w3.nodes.lookup y := h4l
  have hnone3 : ∀ z, m1 ≤ z → w3.nodes.lookup z = none := by
    intro z hz
    cases h' : w3.nodes.lookup z with
    | none => rfl
    | some _ => have := h3src z (by rw [h']; rfl); omega
  have hpx : p ≠ x := by rcases hxlr with h | h <;> rw [h] <;> assumption
  have hw6p : w6.nodes.lookup p = some pn := by
    rw [h6n, h5n, lookup_append_single_ne _ _ _ _ (by omega), hlk4 p hpx, h3p]
  have hw6m1 : w6.nodes.lookup w4.next = some ⟨!!xn.leaf, newKlongs c.i first⟩ := by
    rw [h6n, h5n, lookup_append_single_self]
    rw [hlk4 _ (by rw [h4n, h3next]; omega), h4n, h3next]
    exact hnone3 m1 (Nat.le_refl _)
  have hw4m1 : w4.next = m1 := by rw [h4n, h3next]
  rw [hw4m1] at hw6m1
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
  have hlm1 : l ≠ m1 := by omega
  have hrm1 : r ≠ m1 := by omega
  have hpm1 : p ≠ m1 := by omega
  have hm1R : ¬ TReach N c.i root m1 := not_reach_fresh N c.i root m1 hT hm1N (hfreshT m1 (Nat.le_refl _))
  have hmkd : splitMerged (!xn.leaf) c.p.mergeMax (mergeList (!xn.leaf) cR ln.live rn.live) =
      (first, second) := hmk
  have h6top' : w6.top.rootKey = root := by rw [h6top, h5top, h4top, h3top]
  have hcl' : ∀ y, y ≠ l → y ≠ r → ∀ q ∈ [(l, false), (r, false)], y ≠ (q : NodeId × Bool).1 := by
    intro y hyl hyr q hq
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hq
    rcases hq with h | h <;> rw [h] <;> assumption
  have hne' : ∀ q ∈ [(l, false), (r, false)], (q : NodeId × Bool).1 ≠ p := by
    intro q hq
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hq
    rcases hq with h | h <;> rw [h]
    · exact Ne.symm hpl
    · exact Ne.symm hpr
  have hlr' : ∀ (q : NodeId × Bool), q ∈ [(l, false), (r, false)] → q.1 = l ∨ q.1 = r := by
    intro q hq
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hq
    rcases hq with h | h <;> rw [h]
    · exact Or.inl rfl
    · exact Or.inr rfl
  -- the parent after, into one node
  have hchar1 : ∀ cc z, (cc, z) ∈ (mergeParentNode pn c.i il cL m1 ir cR none).liveAt c.i →
      (cc = cL ∧ z = m1) ∨ ((cc, z) ∈ pn.liveAt c.i ∧ cc ≠ cL ∧ cc ≠ cR) := by
    intro cc z hmem
    have htm : ∀ s, Klong.time s ∈ (mergeParentNode pn c.i il cL m1 ir cR none).ks → s ≤ c.i := by
      rw [mergeParentNode_eq]
      exact mpNode_times pn c.i il cL m1 ir cR none _ _ _ (htd_last pn _) hpt
    rw [KNode.liveAt_of_times _ c.i htm] at hmem
    have hlk := lookup_of_mem_nodup _ (KNode.live_keys_nodup _) cc z hmem
    rw [mergeParentNode_eq, mpNode_live_lookup pn c.i il cL m1 ir cR none _ _ _ l r hpwf hL hLL hR hRL
      hc ?htd (fun _ _ _ h => by cases h) cc] at hlk
    case htd => exact htd_last pn _
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
        exact bk_mem_of_lookup _ cc z hlk
  have hcLm1 : (cL, m1) ∈ (mergeParentNode pn c.i il cL m1 ir cR none).liveAt c.i := by
    have htm : ∀ s, Klong.time s ∈ (mergeParentNode pn c.i il cL m1 ir cR none).ks → s ≤ c.i := by
      rw [mergeParentNode_eq]
      exact mpNode_times pn c.i il cL m1 ir cR none _ _ _ (htd_last pn _) hpt
    rw [KNode.liveAt_of_times _ c.i htm]
    apply bk_mem_of_lookup
    rw [mergeParentNode_eq, mpNode_live_lookup pn c.i il cL m1 ir cR none _ _ _ l r hpwf hL hLL hR hRL
      hc ?htd (fun _ _ _ h => by cases h) cL]
    case htd => exact htd_last pn _
    simp
  cases hsec : second with
  | some ksg =>
    -- into two nodes: no claim
    simp only [writerWP_bind]
    repeat (first
      | (refine (writerWP_pure _ c _ _).mpr ?_; simp; done)
      | (refine writerWP_mono (writerWP_true _ c _) ?_; intro _ _ _))
  | none =>
    rw [hsec] at hmkd
    have hfirst : first = mergeList (!xn.leaf) cR ln.live rn.live := splitMerged_one _ _ _ _ hmkd
    simp only [writerWP_bind, writerWP_pure]
    refine writerWP_mergeParent_roomOne p pn (d - 1) il cL m1 ir cR c w6 _ hw6p hroom hnd ?_
    intro s7
    generalize hw7 : ({ ({ w6 with trail := s7 :: w6.trail } : W) with
      nodes := upsert w6.nodes p (mergeParentNode pn c.i il cL m1 ir cR none) } : W) = w7
    have h7n : w7.nodes = upsert w6.nodes p (mergeParentNode pn c.i il cL m1 ir cR none) := by rw [← hw7]
    have h7t : w7.taken = w6.taken := by rw [← hw7]
    have h7top : w7.top = w6.top := by rw [← hw7]
    have hlk7 : w7.nodes.lookup p = some (mergeParentNode pn c.i il cL m1 ir cR none) := by
      rw [h7n, lookup_upsert]; simp
    -- neither merged node is named live by the parent after
    have hnoOld : ∀ z, (z = l ∨ z = r) → ∀ cc, (cc, z) ∈ pn.liveAt c.i → cc ≠ cL → cc ≠ cR → False := by
      intro z hz cc hmem h1 h2
      rcases hz with hz | hz
      · rw [hz] at hmem
        exact h1 (hT.oneLink p cc p cL l hp hp ⟨pn, hpn, hmem⟩ hlink_l).2
      · rw [hz] at hmem
        exact h2 (hT.oneLink p cc p cR r hp hp ⟨pn, hpn, hmem⟩ hlink_r).2
    refine writerWP_mono (writerWP_mergeCleanup_frameV p m1 c.i c _ w7 _ hne' hlk7
      (fun q hq c' hmem => by
        rcases hchar1 c' q.1 hmem with ⟨_, h⟩ | ⟨hold, h1, h2⟩
        · rcases hlr' q hq with h' | h' <;> rw [h'] at h
          · exact hlm1 h
          · exact hrm1 h
        · exact hnoOld q.1 (hlr' q hq) c' hold h1 h2)) ?_
    intro _ w8 ⟨h8top, _, _, h8t, h8l, pn8, h8p, h8leaf, _, h8iff⟩
    intro _
    have h8tc : ∀ y, y ≠ l → y ≠ r → w8.taken.contains y = w3.taken.contains y := by
      intro y hyl hyr; rw [h8t y (hcl' y hyl hyr), h7t, h6taken]
    have h8l' : ∀ y, y ≠ p → y ≠ l → y ≠ r → w8.nodes.lookup y = w6.nodes.lookup y := by
      intro y hyp hyl hyr; rw [h8l y hyp (hcl' y hyl hyr), h7n, lookup_upsert]; simp [hyp]
    refine ⟨?_, fun y hyp hyl hyr hym => ?_, by rw [h8top, h7top, h6top, h5top, h4top]⟩
    rotate_left
    · rw [h8l' y hyp hyl hyr, h6old y (by rcases hxlr with h | h <;> rw [h] <;> assumption) hym]
    rw [h8top, h7top, h6top']
    -- the new node: its live klongs, of the merged nodes' children, m or more
    have hfirstS : CvSorted first := by rw [hfirst]; exact hsortE
    have hmlen : first.length = ln.live.length + rn.live.length := by
      have := congrArg List.length (mergeList_map_snd (!xn.leaf) cR ln.live rn.live)
      rw [← hfirst] at this
      simpa using this
    have hmtimes : ∀ s, Klong.time s ∈ ({ leaf := !!xn.leaf, ks := newKlongs c.i first } : KNode).ks →
        s ≤ c.i := by
      intro s hs
      simp only [newKlongs, List.mem_cons, Klong.time.injEq, List.mem_map, reduceCtorEq, and_false,
        exists_false, or_false] at hs
      omega
    have hmcnt : (({ leaf := !!xn.leaf, ks := newKlongs c.i first } : KNode).liveAt c.i).length =
        ln.live.length + rn.live.length := by
      rw [KNode.liveAt_of_times _ c.i hmtimes, ← hmlen]
      exact newKlongs_cnt_of_sorted _ _ _ hfirstS
    have hmb : 2 ≤ c.p.mergeBelow := by simpa [Params.merges] using hm
    refine liveEdgesH_mergeOne c.p N (wNode c.p base w8) c.i root p l r m1 pn ln rn pn8
      ⟨!!xn.leaf, newKlongs c.i first⟩ cL cR Hl hT hp hpn hpleaf hpL hpR hln hrn hm1R ?_ ?_
      (by show (!!xn.leaf) = ln.leaf; rw [hll, Bool.not_not]) (by rw [hrl, hll]) ?_ (by rw [hmcnt]; exact hsib) ?_ (by rw [h8leaf, mrg_mergeParentNode_leaf]) ?_ ?_ ?_
      (fun y hy => by
        have hyx := hHl y hy
        rcases hxlr with h | h
        · exact Or.inl (hyx.trans h)
        · exact Or.inr (hyx.trans h))
      hLive
    · simp only [wNode, h8tc m1 (Ne.symm hlm1) (Ne.symm hrm1), hm1T, Bool.false_eq_true, ↓reduceIte]
      rw [h8l' m1 (Ne.symm hpm1) (Ne.symm hlm1) (Ne.symm hrm1), hw6m1]
    · intro cc z hmem
      have hm2 := liveAt_newKlongs_mem (!!xn.leaf) c.i c.i first cc z hmem
      rw [hfirst] at hm2
      have hsn := mergeList_map_snd (!xn.leaf) cR ln.live rn.live
      have hz' : z ∈ (ln.live ++ rn.live).map Prod.snd := by
        rw [List.map_append, ← hsn]; exact List.mem_map.mpr ⟨(cc, z), hm2, rfl⟩
      obtain ⟨q', hq', he⟩ := List.mem_map.mp hz'
      rcases List.mem_append.mp hq' with h | h
      · exact Or.inl ⟨q'.1, by rw [KNode.liveAt_of_times ln c.i hlt, ← he]; exact h⟩
      · exact Or.inr ⟨q'.1, by rw [KNode.liveAt_of_times rn c.i hrt, ← he]; exact h⟩
    · intro h0
      have h1 : (({ leaf := !!xn.leaf, ks := newKlongs c.i first } : KNode).liveAt c.i).length = 0 := by
        rw [h0]; rfl
      omega
    · simp only [wNode, h8tc p hpl hpr, hpT, Bool.false_eq_true, ↓reduceIte, h8p]
    · intro cc z hmem
      exact hchar1 cc z ((h8iff cc z).mp hmem)
    · intro h0
      have := (h8iff cL m1).mpr hcLm1
      rw [h0] at this
      cases this
    · intro y hyp hyl hyr hym
      rw [← hNw3 y]
      unfold wNode
      rw [h8tc y hyl hyr, h8l' y hyp hyl hyr, h6old y (by rcases hxlr with h | h <;> rw [h] <;> assumption) hym]

theorem writerWP_sibling_rd (p : NodeId) (pn : KNode) (i : Nat) (inner : Bool) (c : Ctx) (w : W) :
    WriterWP (sibling p pn i inner) c w (fun _ v => ObsKept c w v) := by
  unfold sibling
  simp only [writerWP_bind, writerWP_read]
  split
  · exact writerWP_throw _ _ _ _
  · simp only [writerWP_bind]
    refine writerWP_mono (writerWP_getNode_rd _ c w) ?_
    rintro sn v ⟨_, hk, _, _⟩
    split
    · exact writerWP_throw _ _ _ _
    · simp only [writerWP_pure]; exact hk

set_option maxHeartbeats 8000000 in
/-- The pilot at a merge of the loop (bergdb 030-01, step 2): a merge into one
node, its parent p on the key access path with room and no compaction and no
child made by the transaction, keeps the hole's form with p the hole after; it
reads every node outside p's children, p and the new node as before. -/
theorem writerWP_merge_livePilot (base : View BVal) (x : NodeId) (d : Nat) (c : Ctx) (w : W)
    (hvc : ViewCoherent c base) (hm : c.p.merges = true)
    (hT : TreeOK (wNode c.p base w) c.i w.top.rootKey)
    (hR : RangeOrder (wNode c.p base w) c.i w.top.rootKey)
    (p : NodeId) (pn : KNode) (hpath : (w.path[d - 1]?).map (·.2) = some p)
    (hpR : TReach (wNode c.p base w) c.i w.top.rootKey p) (hpn : wNode c.p base w p = some pn)
    (hpleaf : pn.leaf = false) (hpwf : klongsWf pn.ks = true)
    (hpt : ∀ s, Klong.time s ∈ pn.ks → s ≤ c.i)
    (hch : ∀ cc z zn, (cc, z) ∈ pn.liveAt c.i → wNode c.p base w z = some zn →
      ∀ s, Klong.time s ∈ zn.ks → s ≤ c.i)
    (hRt : ∀ y, TReach (wNode c.p base w) c.i w.top.rootKey y → w.taken.contains y = false)
    (hidn : ∀ z, (w.nodes.lookup z).isSome = true → z < w.next)
    (hidv : ∀ z, (c.view z).isSome = true → z < w.next)
    (hfree : ∀ z, w.next ≤ z → wNode c.p base w z = none ∧ w.taken.contains z = false)
    (hfreshT : ∀ z, w.next ≤ z → ∀ u c', TReach (wNode c.p base w) c.i w.top.rootKey u →
      ¬ TLink (wNode c.p base w) c.i u c' z)
    (Hl : NodeId → Prop) (hLive : LiveEdgesH c.p (wNode c.p base w) c.i w.top.rootKey Hl)
    (hHl : ∀ y, Hl y → y = x)
    (hmade : ∀ cc y yn, (cc, y) ∈ pn.liveAt c.i → wNode c.p base w y = some yn →
      (yn.firstTime == some c.i) = false)
    (hroom : pn.size + 3 ≤ c.p.M)
    (hnd : ∀ il cL ir cR, deadOver c.p (mergeParentNode pn c.i il cL w.next ir cR none) = false) :
    WriterWP (merge x d) c w (fun res w' => res = 1 →
      LiveEdgesH c.p (wNode c.p base w') c.i w'.top.rootKey (fun y => y = p) ∧
      (∀ y, y ≠ p → (∀ cc, (cc, y) ∉ pn.liveAt c.i) → y ≠ w.next → rdN c w' y = rdN c w y) ∧
      w'.top = w.top) := by
  unfold merge
  simp only [writerWP_bind, writerWP_read]
  unfold pathNode
  simp only [writerWP_bind, writerWP_get]
  split
  · rename_i e he
    simp only [writerWP_pure]
    have hep : e.2 = p := by rw [he] at hpath; simpa using hpath
    subst hep
    refine writerWP_mono (writerWP_and (writerWP_getNode_all e.2 c w base hvc)
      (writerWP_getNode_rd e.2 c w)) ?_
    intro pn' w1 ⟨⟨hr1, hlk1, hwn1, hpre1, hsrc1⟩, _, hk1, _, _⟩
    rw [hwn1 (hRt _ hpR)] at hpn
    cases hpn
    have hpn : wNode c.p base w e.2 = some pn := hwn1 (hRt _ hpR)
    have hpRS := tReach_reachS _ c.i _ _ hpR
    -- the tail from any state that reads as w
    have tailL : ∀ (leftSome : Bool) (l : NodeId) (ln : KNode) (il : Nat) (r : NodeId)
        (rn : KNode) (ir cL cR : Nat) (xn : KNode) (w3 : W), ReadsAs c.p base w w3 →
        w1.nodes <+: w3.nodes → ObsKept c w w3 →
        (∀ z, (w3.nodes.lookup z).isSome = true → (w.nodes.lookup z).isSome = true ∨
          (c.view z).isSome = true) →
        pn.ks[il]? = some (.key cL l) → LastLive pn.ks pn.lastBitmap il cL →
        pn.ks[ir]? = some (.key cR r) → LastLive pn.ks pn.lastBitmap ir cR → cL < cR →
        ln.leaf = xn.leaf → rn.leaf = xn.leaf →
        (x = l ∨ x = r) → wNode c.p base w l = some ln → wNode c.p base w r = some rn →
        WriterWP (mergeTail c x d e.2 pn xn leftSome l ln il r rn ir) c w3
          (fun res w' => res = 1 →
            LiveEdgesH c.p (wNode c.p base w') c.i w'.top.rootKey (fun y => y = e.2) ∧
            (∀ y, y ≠ e.2 → (∀ cc, (cc, y) ∉ pn.liveAt c.i) → y ≠ w.next → rdN c w' y = rdN c w y) ∧
            w'.top = w.top) := by
      intro leftSome l ln il r rn ir cL cR xn w3 hr3 hpre3 hk3 hsrc3 hL hLL hR' hRL hclt hll hrl hxlr hln hrn
      have hmemL : (cL, l) ∈ pn.liveAt c.i := by
        rw [KNode.liveAt_of_times pn c.i hpt]
        apply bk_mem_of_lookup
        rw [KNode.live_lookup]
        exact keyLookup_of_last _ _ _ il l hL hLL
      have hmemR : (cR, r) ∈ pn.liveAt c.i := by
        rw [KNode.liveAt_of_times pn c.i hpt]
        apply bk_mem_of_lookup
        rw [KNode.live_lookup]
        exact keyLookup_of_last _ _ _ ir r hR' hRL
      obtain ⟨hlr1, hlr2⟩ := mrg_child_range (wNode c.p base w) c.i w.top.rootKey hR e.2 pn hpRS hpn
        hpleaf cL l ln hmemL hln
      obtain ⟨hrr1, _⟩ := mrg_child_range (wNode c.p base w) c.i w.top.rootKey hR e.2 pn hpRS hpn
        hpleaf cR r rn hmemR hrn
      have hN3 : wNode c.p base w3 = wNode c.p base w := hr3.1
      refine writerWP_mono (writerWP_mergeTail_livePilot c base x d e.2 pn xn leftSome l ln il r rn ir
        cL cR (wNode c.p base w) w.top.rootKey w.next w3 Hl hm hT hpR hpn hL hLL hR' hRL (by omega) hxlr
        hln hrn hpwf hpt hch hN3 (by rw [hr3.2.1]) hr3.2.2.2.2 (lookup_of_prefix _ _ hpre3 _ _ hlk1)
        (fun z hz => by
          rcases hsrc3 z hz with h | h
          · exact hidn z h
          · exact hidv z h)
        (fun z hz => ⟨(hfree z hz).1, by rw [hr3.2.2.1]; exact (hfree z hz).2⟩)
        hfreshT hpleaf hll hrl
        (fun cc z h => hlr2 cR r hmemR hclt cc z h)
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
        (hmade cL l ln hmemL hln) (hmade cR r rn hmemR hrn) hroom (hnd il cL ir cR) hLive hHl) ?_
      rintro res w' hpost hres
      obtain ⟨hL', hfr, htop⟩ := hpost hres
      refine ⟨hL', fun y hyp hych hyn => ?_, by rw [htop, hr3.2.1]⟩
      have hyl : y ≠ l := fun h => hych cL (by rw [h]; exact hmemL)
      have hyr : y ≠ r := fun h => hych cR (by rw [h]; exact hmemR)
      have hlk := hfr y hyp hyl hyr hyn
      have : rdN c w' y = rdN c w3 y := by simp only [rdN, hlk]
      rw [this, hk3.1]
    have hptrk : ∀ i cv y, LastLive pn.ks pn.lastBitmap i cv → pn.ptr? i = some y →
        pn.ks[i]? = some (.key cv y) := by
      intro i cv y hl hy
      obtain ⟨⟨y0, hy0⟩, _, _⟩ := hl
      simp only [KNode.ptr?, hy0, Option.some.injEq] at hy
      rw [hy0, hy]
    have hchild : ∀ i cv y, pn.ks[i]? = some (.key cv y) → LastLive pn.ks pn.lastBitmap i cv →
        (cv, y) ∈ pn.liveAt c.i ∧ TReach (wNode c.p base w) c.i w.top.rootKey y := by
      intro i cv y hk hl
      have hm : (cv, y) ∈ pn.liveAt c.i := by
        rw [KNode.liveAt_of_times pn c.i hpt]
        apply bk_mem_of_lookup
        rw [KNode.live_lookup]
        exact keyLookup_of_last _ _ _ i y hk hl
      exact ⟨hm, TReach.link hpR ⟨pn, hpn, hm⟩⟩
    refine writerWP_mono (writerWP_and (writerWP_getNode_all x c w1 base hvc)
      (writerWP_getNode_rd x c w1)) ?_
    intro xn w2 ⟨⟨hr2, _, hwn2, hpre2, hsrc2⟩, _, hk2, _, _⟩
    have hr02 := ReadsAs.trans _ _ _ _ _ hr1 hr2
    have hk02 := hk1.trans hk2
    have hsrc02 : ∀ z, (w2.nodes.lookup z).isSome = true → (w.nodes.lookup z).isSome = true ∨
        (c.view z).isSome = true := by
      intro z hz
      rcases hsrc2 z hz with h | h
      · exact hsrc1 z h
      · exact Or.inr h
    unfold klongAt
    simp only [writerWP_bind, writerWP_get]
    split
    · rename_i cx _ hcx
      simp only [writerWP_pure]
      generalize hmi : mergeIdx pn cx = mi
      obtain ⟨ixo, ia, ib⟩ := mi
      have hML := mergeIdx_last pn cx
      rw [hmi] at hML
      obtain ⟨hMx, hMa, hMb⟩ := hML
      split
      · rename_i ix hix
        simp only [writerWP_bind, writerWP_pure]
        have hLx := hMx ix hix
        refine writerWP_if _ _ _ _ _ _ (fun _ => ?_) (fun hptr => ?_)
        · simp only [writerWP_bind]; exact writerWP_throw _ _ _ _
        have hpx : pn.ptr? ix = some x := by simpa using hptr
        have hkx := hptrk ix cx x hLx hpx
        obtain ⟨_, hxR⟩ := hchild ix cx x hkx hLx
        have hxn : wNode c.p base w x = some xn := by
          rw [← hr1.1]; exact hwn2 (by rw [hr1.2.2.1]; exact hRt x hxR)
        -- a sibling read
        have hsib : ∀ (wb : W) (i cv : Nat) (sn : NodeId × KNode) (w3 : W),
            ReadsAs c.p base w wb → w1.nodes <+: wb.nodes →
            LastLive pn.ks pn.lastBitmap i cv →
            pn.ptr? i = some sn.1 → ReadsAs c.p base wb w3 → wb.nodes <+: w3.nodes →
            (wb.taken.contains sn.1 = false → wNode c.p base wb sn.1 = some sn.2) →
            pn.ks[i]? = some (.key cv sn.1) ∧ wNode c.p base w sn.1 = some sn.2 ∧
              ReadsAs c.p base w w3 ∧ w1.nodes <+: w3.nodes := by
          intro wb i cv sn w3 hrb hpreb hl hp hr3 hpre3 hwn3
          have hk := hptrk i cv sn.1 hl hp
          obtain ⟨_, hsR⟩ := hchild i cv sn.1 hk hl
          refine ⟨hk, ?_, ReadsAs.trans _ _ _ _ _ hrb hr3, hpreb.trans hpre3⟩
          rw [← hrb.1]; exact hwn3 (by rw [hrb.2.2.1]; exact hRt _ hsR)
        have hright : ∀ (wb : W) (ia0 cva : Nat), ReadsAs c.p base w wb → w1.nodes <+: wb.nodes →
            ObsKept c w wb →
            (∀ z, (wb.nodes.lookup z).isSome = true → (w.nodes.lookup z).isSome = true ∨
              (c.view z).isSome = true) →
            LastLive pn.ks pn.lastBitmap ia0 cva → cx < cva →
            (mergeIdx pn cx).2.1 = some (ia0, cva) →
            WriterWP (do
              let __x ← sibling e.2 pn ia0 !xn.leaf
              mergeTail c x d e.2 pn xn false x xn ix __x.1 __x.2 ia0) c wb
              (fun res w' => res = 1 →
                LiveEdgesH c.p (wNode c.p base w') c.i w'.top.rootKey (fun y => y = e.2) ∧
                (∀ y, y ≠ e.2 → (∀ cc, (cc, y) ∉ pn.liveAt c.i) → y ≠ w.next →
                  rdN c w' y = rdN c w y) ∧ w'.top = w.top) := by
          intro wb ia0 cva hrb hpreb hkb hsrcb hLa hax hia
          rw [writerWP_bind]
          refine writerWP_mono (writerWP_and (writerWP_and
            (writerWP_sibling_leaf e.2 pn ia0 (!xn.leaf) c wb base hvc)
            (writerWP_sibling_rd e.2 pn ia0 (!xn.leaf) c wb))
            (writerWP_true _ c wb)) ?_
          rintro ⟨rs, rsn⟩ w4 ⟨⟨⟨hs1, hr4, _, hwn4, hpre4, hsrc4, hsl⟩, hk4⟩, _⟩
          obtain ⟨hka, hrn, hr04, hpre14⟩ :=
            hsib wb ia0 cva (rs, rsn) w4 hrb hpreb hLa hs1 hr4 hpre4 hwn4
          exact tailL false x xn ix rs rsn ia0 cx cva xn w4 hr04 hpre14 (hkb.trans hk4)
            (fun z hz => by
              rcases hsrc4 z hz with h | h
              · exact hsrcb z h
              · exact Or.inr h)
            hkx hLx hka hLa hax rfl (by rw [hsl]; simp) (Or.inl rfl) hxn hrn
        split
        · rename_i ib0 cvb
          obtain ⟨hLb, hbx⟩ := hMb ib0 cvb rfl
          simp only [writerWP_bind]
          refine writerWP_mono (writerWP_and
            (writerWP_sibling_leaf e.2 pn ib0 (!xn.leaf) c w2 base hvc)
            (writerWP_sibling_rd e.2 pn ib0 (!xn.leaf) c w2)) ?_
          rintro ⟨ls, lsn⟩ w3 ⟨⟨hs1, hr3, _, hwn3, hpre3, hsrc3, hsl⟩, hk3⟩
          obtain ⟨hkb, hln, hr03, hpre13⟩ :=
            hsib w2 ib0 cvb (ls, lsn) w3 hr02 hpre2 hLb hs1 hr3 hpre3 hwn3
          have hsrc03 : ∀ z, (w3.nodes.lookup z).isSome = true → (w.nodes.lookup z).isSome = true ∨
              (c.view z).isSome = true := by
            intro z hz
            rcases hsrc3 z hz with h | h
            · exact hsrc02 z h
            · exact Or.inr h
          refine writerWP_if _ _ _ _ _ _ (fun _ => ?_) (fun _ => ?_)
          · show WriterWP (mergeTail c x d e.2 pn xn true ls lsn ib0 x xn ix) c w3 _
            exact tailL true ls lsn ib0 x xn ix cvb cx xn w3 hr03 hpre13 (hk02.trans hk3) hsrc03
              hkb hLb hkx hLx hbx (by rw [hsl]; simp) rfl (Or.inr rfl) hln hxn
          · rw [writerWP_bind, writerWP_pure]
            dsimp only
            split
            · rename_i ia0 cva _
              obtain ⟨hLa, hax⟩ := hMa ia0 cva rfl
              exact hright w3 ia0 cva hr03 hpre13 (hk02.trans hk3) hsrc03 hLa hax (by rw [hmi])
            · exact writerWP_throw _ _ _ _
        · rw [writerWP_bind, writerWP_pure]
          dsimp only
          split
          · rename_i ia0 cva
            obtain ⟨hLa, hax⟩ := hMa ia0 cva rfl
            exact hright w2 ia0 cva hr02 hpre2 hk02 hsrc02 hLa hax (by rw [hmi])
          · exact writerWP_throw _ _ _ _
      · exact writerWP_throw _ _ _ _
    · exact writerWP_throw _ _ _ _
  · exact writerWP_throw _ _ _ _

theorem gradedL_of_idx (Rd : NodeId → Option KNode) (Gh : NodeId → Option (Nat × Nat)) :
    ∀ (l : List NodeId), (∀ j (hj : j + 1 < l.length), ∀ n, Rd l[j] = some n → n.leaf = false →
      ∃ g1 h1 g2 h2, Gh l[j] = some (g1, h1) ∧ Gh l[j + 1] = some (g2, h2) ∧ h1 = h2 + 1) →
      GradedL Rd Gh l := by
  intro l
  induction l with
  | nil => intro _; trivial
  | cons x l ih =>
    intro h
    cases l with
    | nil => trivial
    | cons y l' =>
      refine ⟨fun n hn hl => h 0 (by simp) n hn hl, ih (fun j hj n hn hl => ?_)⟩
      exact h (j + 1) (by simp at hj ⊢; omega) n hn hl

/-- The heights' walk gives the path's heights: one less below each inner node. -/
theorem gradedL_of_ht {H : NodeId → Nat → Prop} {B : NodeId} {c : Ctx} {w : W}
    (hvh : ViewHeights H B c) (hb : Book B c w) (hi : HtInv H B c w)
    (hpf : PathFreeTo w w.path.length) (hpc : PathCached w) :
    GradedL (rdN c w) (rdG c w) (w.path.map (·.2)) := by
  apply gradedL_of_idx
  intro j hj n hn hl
  simp only [List.length_map] at hj
  have hj0 : j < w.path.length := by omega
  have he : w.path[j]? = some w.path[j] := List.getElem?_eq_getElem hj0
  have he' : w.path[j + 1]? = some w.path[j + 1] := List.getElem?_eq_getElem hj
  obtain ⟨nx, hlx⟩ := hpc w.path[j] (List.getElem_mem hj0)
  obtain ⟨ny, hly⟩ := hpc w.path[j + 1] (List.getElem_mem hj)
  simp only [List.getElem_map] at hn ⊢
  rw [rdN_of_lookup c w _ nx hlx] at hn
  cases hn
  obtain ⟨g1, h1, hm1⟩ := kd_tag_of_lookup hb hlx
  obtain ⟨g2, h2, hm2⟩ := kd_tag_of_lookup hb hly
  have hlk : ∀ z g h, (z, g, h) ∈ w.gh → w.gh.lookup z = some (g, h) :=
    fun z g h hm => lookup_of_mem_nodup _ hb.nodup z (g, h) hm
  refine ⟨g1, h1, g2, h2, by rw [rdG_of_lookup c w _ n hlx]; exact hlk _ _ _ hm1,
    by rw [rdG_of_lookup c w _ ny hly]; exact hlk _ _ _ hm2, ?_⟩
  have hleaf := kd_leaf hb hlx hm1
  rw [hl] at hleaf
  have hh1 : h1 ≠ 0 := by intro h0; rw [h0] at hleaf; simp at hleaf
  have htk := hpf j _ _ hj0 he
  obtain ⟨cv, hcv⟩ : ∃ cv, w.path[j + 1].1 = some cv := by
    have := hi.pathSome j w.path[j + 1].1 w.path[j + 1].2 (by rw [he'])
    cases h' : w.path[j + 1].1 with
    | none => exact absurd h' this
    | some cv => exact ⟨cv, rfl⟩
  have hHas := hi.path j w.path[j].1 w.path[j].2 cv w.path[j + 1].2 (by rw [he])
    (by rw [he', ← hcv]) g1 h1 hm1 htk hh1
  have := hasHt_tag hb hvh hm2 hHas
  omega


/-- `HoleAt` for the writer's preconditions: the node that every successful run
of the merges' descent at (g, h) finds; every node if none succeeds. -/
def HoleAtW (key : Key) (g h : Nat) (c : Ctx) (v : W) (y : NodeId) : Prop :=
  ∀ d v', descendToHeight key g h c v = .ok (d, v') → (v'.path[d]?).map (·.2) = some y

/-- The live counts at a round of the merges' loop at (g, h), the hole as `HoleAtW`. -/
def LiveHoleW (key : Key) (g h : Nat) (c : Ctx) (base : View BVal) (v : W) : Prop :=
  LiveEdgesH c.p (wNode c.p base v) c.i v.top.rootKey (HoleAtW key g h c v)

set_option maxHeartbeats 4000000 in
/-- The pilot of `l4`'s route (bergdb 030-01, step 2), at a round of the merges'
loop at (g, h) from v: its descent finds x at depth d with its parent p (v1),
its reads (to v3), and a merge into one node of x with a sibling, p with room,
no compaction and no child made by the transaction. If the live counts hold but
at the node the round's descent finds, they hold after the merge but at the
node that the next round's descent finds, one height up. The heights' walk at
v1 gives the descent one height up (`descendToHeight_up`, `gradedL_of_ht`). -/
theorem liveHoleW_merge_pilot (key : Key) (g h : Nat) (c : Ctx) (base : View BVal) (v v1 v3 : W)
    (d : Nat) (hvc : ViewCoherent c base) (hm : c.p.merges = true)
    (hS : descendToHeight key g h c v = .ok (d, v1)) (hd : 0 < d)
    (hr13 : ReadsAs c.p base v1 v3) (hk13 : ObsKept c v1 v3) (hp13 : v3.path = v1.path)
    (hLH : LiveHoleW key g h c base v)
    (hT : TreeOK (wNode c.p base v3) c.i v3.top.rootKey)
    (hR : RangeOrder (wNode c.p base v3) c.i v3.top.rootKey)
    (hRt : ∀ y, TReach (wNode c.p base v3) c.i v3.top.rootKey y → v3.taken.contains y = false)
    (hidn : ∀ z, (v3.nodes.lookup z).isSome = true → z < v3.next)
    (hidv : ∀ z, (c.view z).isSome = true → z < v3.next)
    (hfree : ∀ z, v3.next ≤ z → wNode c.p base v3 z = none ∧ v3.taken.contains z = false)
    (hfreshT : ∀ z, v3.next ≤ z → ∀ u c', TReach (wNode c.p base v3) c.i v3.top.rootKey u →
      ¬ TLink (wNode c.p base v3) c.i u c' z)
    (hdepth : ∀ j e, v3.path[j]? = some e → PathLen (wNode c.p base v3) c.i v3.top.rootKey e.2 j)
    (hpc3 : PathCached v3)
    (x p : NodeId) (pn : KNode) (hx : (v3.path[d]?).map (·.2) = some x)
    (hpath : (v3.path[d - 1]?).map (·.2) = some p) (hplk : v3.nodes.lookup p = some pn)
    (hpleaf : pn.leaf = false) (hpwf : klongsWf pn.ks = true)
    (hpt : ∀ s, Klong.time s ∈ pn.ks → s ≤ c.i)
    (hch : ∀ cc z zn, (cc, z) ∈ pn.liveAt c.i → wNode c.p base v3 z = some zn →
      ∀ s, Klong.time s ∈ zn.ks → s ≤ c.i)
    {H : NodeId → Nat → Prop} {B : NodeId} (hvh : ViewHeights H B c) (hvb : ViewIdsBelow B c.view)
    (hb1 : Book B c v1) (hi1 : HtInv H B c v1) (hpf1 : PathFreeTo v1 v1.path.length)
    (hb3 : Book B c v3)
    (hmade : ∀ cc y yn, (cc, y) ∈ pn.liveAt c.i → wNode c.p base v3 y = some yn →
      (yn.firstTime == some c.i) = false)
    (hroom : pn.size + 3 ≤ c.p.M)
    (hnd : ∀ il cL ir cR, deadOver c.p (mergeParentNode pn c.i il cL v3.next ir cR none) = false) :
    WriterWP (merge x d) c v3 (fun res v4 => res = 1 → LiveHoleW key g (h + 1) c base v4) := by
  -- the round's descent: it reads, and finds x
  have hk01 : ObsKept c v v1 := by
    obtain ⟨_, _, _, _, _, _, _, _, _, hk⟩ := writerWP_descendToHeight_rd key g h c v d v1 hS
    exact hk
  have hr01 : ReadsAs c.p base v v1 := writerWP_descendToHeight_readsU key g h c base hvc v d v1 hS
  have hk03 := hk01.trans hk13
  have hHl : ∀ y, HoleAtW key g h c v y → y = x := by
    intro y hy
    have h1 := hy d v1 hS
    rw [← hp13, hx] at h1
    exact (Option.some.inj h1).symm
  have hN3 : wNode c.p base v3 = wNode c.p base v := by rw [hr13.1, hr01.1]
  have htop3 : v3.top = v.top := hk03.2.2
  have hLive : LiveEdgesH c.p (wNode c.p base v3) c.i v3.top.rootKey (HoleAtW key g h c v) := by
    rw [hN3, htop3]; exact hLH
  have hpR : TReach (wNode c.p base v3) c.i v3.top.rootKey p := by
    obtain ⟨e, he⟩ : ∃ e, v3.path[d - 1]? = some e := by
      cases h' : v3.path[d - 1]? with
      | none => rw [h'] at hpath; cases hpath
      | some e => exact ⟨e, rfl⟩
    have hep : e.2 = p := by rw [he] at hpath; simpa using hpath
    rw [← hep]; exact (hdepth _ e he).reach
  have hpT := hRt p hpR
  have hpT' : p ∉ v3.taken := by simpa using hpT
  have hpn : wNode c.p base v3 p = some pn := by simp [wNode, hpT', hplk]
  refine writerWP_mono (writerWP_and (writerWP_merge_livePilot base x d c v3 hvc hm hT hR p pn
    hpath hpR hpn hpleaf hpwf hpt hch hRt hidn hidv hfree hfreshT (HoleAtW key g h c v) hLive hHl hmade
    hroom hnd) (book_merge B x d c v3 hvb hb3)) ?_
  rintro res v4 ⟨hpost, hb4, hkept⟩ hres
  obtain ⟨hL4, hfr, htop4⟩ := hpost hres
  -- the path below the descent: its length and its node at d - 1
  have hlen1 : v1.path.length = d + 1 := by
    obtain ⟨_, _, _, _, _, _, _, hp, hdd, _⟩ := writerWP_descendToHeight_rd key g h c v d v1 hS
    rw [hp]; rw [← hp] at hdd ⊢
    have : d < v1.path.length := by
      rw [← hp13]
      by_cases hc : d < v3.path.length
      · exact hc
      · rw [List.getElem?_eq_none (by omega)] at hx; cases hx
    omega
  -- the descent one height up stops at p
  have hup : ∀ d' T1, descendToHeight key g (h + 1) c v4 = .ok (d', T1) →
      (T1.path[d']?).map (·.2) = some p := by
    intro d' T1 hT1
    refine (fun hres' => ?_) (descendToHeight_up key g h c v v1 v4 d hS hd ?_ ?_ ?_ ?_ ?_ d' T1 hT1)
    · obtain ⟨hd', hpath'⟩ := hres'
      rw [hd', hpath', List.getElem?_dropLast]
      have : d - 1 < v1.path.length - 1 := by omega
      simp only [this, ↓reduceIte]
      rw [← hp13]; exact hpath
    · intro e he
      have hep : e.2 = p := by rw [← hp13] at he; rw [he] at hpath; simpa using hpath
      refine ⟨pn, ?_, hpleaf⟩
      rw [hep, ← hk03.1]; exact rdN_of_lookup c v3 p pn hplk
    · rw [htop4, htop3]
    · intro y hy
      -- a node of the path two above the end: not p, not p's child, not new
      rw [List.mem_iff_getElem] at hy
      obtain ⟨j, hj, hjy⟩ := hy
      simp only [List.length_dropLast, List.length_map] at hj
      have hjd : j + 1 < d := by omega
      have hjl : j < v1.path.length := by omega
      have hy' : y = v1.path[j].2 := by
        rw [← hjy]; simp [List.getElem_dropLast]
      have hej : v3.path[j]? = some v1.path[j] := by rw [hp13]; exact List.getElem?_eq_getElem hjl
      have hpl := hdepth j _ hej
      obtain ⟨ep, hep⟩ : ∃ ep, v3.path[d - 1]? = some ep := by
        cases h' : v3.path[d - 1]? with
        | none => rw [h'] at hpath; cases hpath
        | some e => exact ⟨e, rfl⟩
      have hepp : ep.2 = p := by rw [hep] at hpath; simpa using hpath
      have hpd := hdepth (d - 1) ep hep
      rw [hepp] at hpd
      have hpl' : PathLen (wNode c.p base v3) c.i v3.top.rootKey y j := by rw [hy']; exact hpl
      have hyp : y ≠ p := by
        intro he; rw [he] at hpl'
        have := PathLen.depth_unique hT _ _ _ hpl' hpd; omega
      have hych : ∀ cc, (cc, y) ∉ pn.liveAt c.i := by
        intro cc hcc
        have hl : PathLen (wNode c.p base v3) c.i v3.top.rootKey y (d - 1 + 1) :=
          PathLen.link hpd ⟨pn, hpn, hcc⟩
        have := PathLen.depth_unique hT _ _ _ hpl' hl; omega
      have hyn : y ≠ v3.next := by
        have hjl3 : j < v3.path.length := by rw [hp13]; exact hjl
        have hy3 : v3.path[j].2 = y := by rw [hy']; simp [hp13]
        obtain ⟨n, hn⟩ := hpc3 _ (List.getElem_mem hjl3)
        have := hidn _ (by rw [hn]; rfl)
        rw [hy3] at this
        omega
      rw [hfr y hyp hych hyn, ← hk03.1]
    · intro y hy
      -- the nodes of the path but the last are cached with their segment and height
      rw [List.mem_iff_getElem] at hy
      obtain ⟨j, hj, hjy⟩ := hy
      simp only [List.length_dropLast, List.length_map] at hj
      have hjl : j < v1.path.length := by omega
      have hy' : y = v1.path[j].2 := by rw [← hjy]; simp [List.getElem_dropLast]
      have hjl3 : j < v3.path.length := by rw [hp13]; exact hjl
      obtain ⟨n3, hn3⟩ := hpc3 _ (List.getElem_mem hjl3)
      have hy3 : v3.path[j].2 = y := by rw [hy']; simp [hp13]
      rw [hy3] at hn3
      obtain ⟨g0, h0, hm0⟩ := kd_tag_of_lookup hb3 hn3
      obtain ⟨n4, hn4, _⟩ := hkept.1 y n3 hn3
      have h4 : rdG c v4 y = some (g0, h0) := by
        rw [rdG_of_lookup c v4 y n4 hn4]
        exact lookup_of_mem_nodup _ hb4.nodup y (g0, h0) (hkept.2 _ hm0)
      have h3 : rdG c v3 y = some (g0, h0) := by
        rw [rdG_of_lookup c v3 y n3 hn3]
        exact lookup_of_mem_nodup _ hb3.nodup y (g0, h0) hm0
      rw [h4, ← h3, hk03.2.1]
    · have hpc1 : PathCached v1 := writerWP_descendToHeight_path_cached key g h c v d v1 hS
      have := gradedL_of_ht hvh hb1 hi1 hpf1 hpc1
      rw [hk01.1, hk01.2.1] at this
      exact this
  refine liveEdgesH_mono c.p _ c.i _ (fun y => y = p) _ (fun y hy => hy ▸ hup) ?_ hL4
  intro u un cc y yn hu hun hcc hyn _ hyp
  exact ((hL4.2 u un cc y yn hu hun hcc hyn).1 hyp).1

end SIS.Tree
