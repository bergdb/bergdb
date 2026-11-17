/-
The merge's tail where its parent goes `full` and the transaction made the
parent (bergdb 030-01, step 3's rest): the parent splits in time in place, so
its node becomes its last version with the new pointers and nothing else
changes; the room proof's steps carry over, and the next round's descent finds
the parent (`descendToHeight_up`). The rest is `MergeTailFullRest2OK`.
-/
import SIS.Tree.LiveMergeFull

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- The time split in place of the merge's parent that the transaction made
(`timeSplitInPlace`), its parent cached: p's node becomes its last version; the
nodes but p, the taken nodes, the super root, the heights' cache and the path
stay. -/
theorem writerWP_handleFullWith_timeInPlace_nodesL (up : NodeId → List (Nat × NodeId) → M Unit)
    (depth : Nat) (L : NodeId) (n last : KNode) (compact : Bool) (c : Ctx) (w : W)
    (hlk : w.nodes.lookup L = some n) (hfirst : n.firstTime = some c.i)
    (hcs : (!compact && decide (last.size > c.p.splitAbove)) = false)
    (hqc : ∀ e q, depth = e + 1 → (w.path[e]?).map (·.2) = some q → ∃ qn, w.nodes.lookup q = some qn) :
    WriterWP (handleFullWith up depth L [] last compact) c w (fun _ w' =>
      w'.nodes = upsert w.nodes L ⟨n.leaf, last.ks⟩ ∧ w'.taken = w.taken ∧ w'.top = w.top ∧
        w'.gh = w.gh ∧ w'.path = w.path) := by
  unfold handleFullWith
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_getNode_known L n c w hlk]
  refine writerWP_ghOf_cached L n c w hlk _ (fun gh => ?_)
  have hnew : (n.firstTime == some c.i) = true := by simp [hfirst]
  simp only [hnew]
  have hpar : WriterWP (parentAt depth) c w (fun a v => v = w ∧
      ∀ q, a = some q → ∃ qn, w.nodes.lookup q = some qn) := by
    unfold parentAt pathNode
    cases depth with
    | zero => simp only [writerWP_pure]; exact ⟨trivial, fun q h => by cases h⟩
    | succ e =>
      simp only [writerWP_bind, writerWP_get]
      split
      · rename_i en hen
        simp only [writerWP_pure]
        refine ⟨trivial, fun q hq => ?_⟩
        cases hq
        exact hqc e en.2 rfl (by rw [hen]; rfl)
      · exact writerWP_throw _ _ _ _
  refine writerWP_mono hpar ?_
  rintro a w1 ⟨hw1, hqa⟩
  subst w1
  have hrest : ∀ w2 : W, w2.nodes = w.nodes → w2.taken = w.taken → w2.top = w.top → w2.gh = w.gh →
      w2.path = w.path →
      WriterWP (do
        let l ← replaceOrAdd last []
        if (l.size == 1) = true then do
            note "lone-time-klong"
            putNode L { leaf := n.leaf, ks := l.ks }
          else putNode L { leaf := n.leaf, ks := l.ks }) c w2 (fun _ w' =>
        w'.nodes = upsert w.nodes L ⟨n.leaf, last.ks⟩ ∧ w'.taken = w.taken ∧ w'.top = w.top ∧
          w'.gh = w.gh ∧ w'.path = w.path) := by
    intro w2 h2n h2t h2top h2gh h2path
    simp only [writerWP_bind]
    refine writerWP_mono (writerWP_replaceOrAdd_nil last c _) ?_
    rintro l w3 ⟨hw3, hl⟩
    subst hw3 hl
    split <;>
    · simp only [note, putNode, writerWP_bind, writerWP_modify]
      exact ⟨by rw [h2n], h2t, h2top, h2gh, h2path⟩
  simp only [note, writerWP_bind] at hrest
  cases compact with
  | true =>
    simp only [↓reduceIte, note, Bool.not_true, Bool.false_and, Bool.false_eq_true]
    cases a with
    | none =>
      simp only [writerWP_bind, writerWP_pure, writerWP_modify]
      exact hrest _ rfl rfl rfl rfl rfl
    | some q =>
      simp only [writerWP_bind, writerWP_pure, writerWP_modify]
      obtain ⟨qn, hqn⟩ := hqa q rfl
      rw [writerWP_getNode_known q qn c _ hqn]
      exact hrest _ rfl rfl rfl rfl rfl
  | false =>
    simp only [Bool.not_false, Bool.true_and] at hcs
    simp only [hcs, ↓reduceIte, note, Bool.not_false, Bool.true_and, Bool.false_eq_true]
    cases a with
    | none =>
      simp only [writerWP_bind, writerWP_pure, writerWP_modify]
      exact hrest _ rfl rfl rfl rfl rfl
    | some q =>
      simp only [writerWP_bind, writerWP_pure, writerWP_modify]
      obtain ⟨qn, hqn⟩ := hqa q rfl
      rw [writerWP_getNode_known q qn c _ hqn]
      exact hrest _ rfl rfl rfl rfl rfl

/-- The merge's last loop keeps the heights' cache at p, cached and not one of
its nodes. -/
theorem writerWP_mergeCleanup_ghp (p m1 : NodeId) (c : Ctx) :
    ∀ (xs : List (NodeId × Bool)) (w : W), (∃ n, w.nodes.lookup p = some n) → (∀ q ∈ xs, q.1 ≠ p) →
    WriterWP (forIn xs PUnit.unit (fun q _ => if q.2 = true then (do
        retarget p q.1 m1
        takenBack q.1
        note "merge.takeback"
        pure (ForInStep.yield PUnit.unit)) else (do
        unlink q.1
        pure (ForInStep.yield PUnit.unit)))) c w
      (fun _ w' => w'.gh.lookup p = w.gh.lookup p) := by
  intro xs
  induction xs with
  | nil =>
    intro w _ _
    rw [List.forIn_nil]
    exact (writerWP_pure _ c w _).mpr rfl
  | cons q qs ih =>
    intro w hpc hne
    rw [List.forIn_cons]
    have hqp : q.1 ≠ p := hne q List.mem_cons_self
    have hrest : ∀ w1 : W, (∃ n, w1.nodes.lookup p = some n) → w1.gh.lookup p = w.gh.lookup p →
        WriterWP (forIn qs PUnit.unit (fun q _ => if q.2 = true then (do
          retarget p q.1 m1
          takenBack q.1
          note "merge.takeback"
          pure (ForInStep.yield PUnit.unit)) else (do
          unlink q.1
          pure (ForInStep.yield PUnit.unit)))) c w1
        (fun _ w' => w'.gh.lookup p = w.gh.lookup p) := by
      intro w1 h1c h1
      refine writerWP_mono (ih w1 h1c (fun q' hq' => hne q' (List.mem_cons_of_mem _ hq'))) ?_
      intro _ w2 h2
      rw [h2, h1]
    obtain ⟨np, hnp⟩ := hpc
    split
    · simp only [writerWP_bind]
      unfold retarget
      simp only [writerWP_bind, writerWP_read]
      rw [writerWP_getNode_known p np c w hnp]
      split
      · simp only [putNode, takenBack, note, writerWP_bind, writerWP_modify, writerWP_pure]
        exact hrest _ ⟨_, by show (upsert w.nodes p _).lookup p = _; rw [lookup_upsert, if_pos rfl]⟩ rfl
      · simp only [takenBack, note, writerWP_bind, writerWP_modify, writerWP_pure]
        exact hrest _ ⟨np, hnp⟩ rfl
    · simp only [writerWP_bind]
      unfold unlink
      simp only [writerWP_bind, writerWP_read]
      refine writerWP_mono (writerWP_and (writerWP_getNode_ghL q.1 c w) (writerWP_getNode_frame q.1 c w)) ?_
      intro n w1 ⟨h1, _, _, _, _, _, _, h1n⟩
      split
      · simp only [putNode, writerWP_bind, writerWP_modify, writerWP_pure]
        refine hrest _ ⟨np, ?_⟩ (h1 p (Ne.symm hqp))
        show (upsert w1.nodes q.1 _).lookup p = _
        rw [lookup_upsert, if_neg (Ne.symm hqp), h1n p (Ne.symm hqp), hnp]
      · simp only [writerWP_bind, writerWP_pure]
        exact hrest _ ⟨np, by rw [h1n p (Ne.symm hqp), hnp]⟩ (h1 p (Ne.symm hqp))

set_option maxHeartbeats 16000000 in
/-- A merge whose parent p, made by the transaction, goes `full` and splits in
time in place: p's node becomes its last version with the new pointers, nothing
else changes, so the room proof's steps carry over: into one node the hole is p
after, into two nodes there is none. Beside the room tail's frames: the heights'
cache below nx but at l and r, and p's node. -/
theorem writerWP_mergeTail_liveMade (c : Ctx) (base : View BVal) (x : NodeId) (d : Nat) (p : NodeId)
    (pn xn : KNode) (leftSome : Bool) (l : NodeId) (ln : KNode) (il : Nat) (r : NodeId)
    (rn : KNode) (ir : Nat) (cL cR : Nat) (N : NodeId → Option KNode) (root : NodeId) (nx : Nat)
    (w3 : W) (Hl : NodeId → Prop) (hm : c.p.merges = true) (hMP : MergeParamsOK c.p)
    (hT : TreeOK N c.i root) (hp : TReach N c.i root p) (hpn : N p = some pn)
    (hL : pn.ks[il]? = some (.key cL l)) (hLL : LastLive pn.ks pn.lastBitmap il cL)
    (hR : pn.ks[ir]? = some (.key cR r)) (hRL : LastLive pn.ks pn.lastBitmap ir cR)
    (hclt : cL < cR) (hadj : ∀ cc z, (cc, z) ∈ pn.liveAt c.i → cc ≤ cL ∨ cR ≤ cc)
    (hxlr : x = l ∨ x = r) (hln : N l = some ln) (hrn : N r = some rn)
    (hpt : ∀ s, Klong.time s ∈ pn.ks → s ≤ c.i)
    (hch : ∀ cc z zn, (cc, z) ∈ pn.liveAt c.i → N z = some zn →
      ∀ s, Klong.time s ∈ zn.ks → s ≤ c.i)
    (hN3 : wNode c.p base w3 = N) (h3top : w3.top.rootKey = root) (h3next : w3.next = nx)
    (h3p : w3.nodes.lookup p = some pn) (h3src : ∀ z, (w3.nodes.lookup z).isSome = true → z < nx)
    (hfree : ∀ z, nx ≤ z → N z = none ∧ w3.taken.contains z = false)
    (hfreshT : ∀ z, nx ≤ z → ∀ u c', TReach N c.i root u → ¬ TLink N c.i u c' z)
    (hpleaf : pn.leaf = false) (hll : ln.leaf = xn.leaf) (hrl : rn.leaf = xn.leaf)
    (hlrange : ∀ cc z, (cc, z) ∈ ln.liveAt c.i → cc < cR)
    (hllow : ∀ cc z, (cc, z) ∈ ln.liveAt c.i →
      ((!xn.leaf) = true → cc = 0 ∨ cL < cc) ∧ ((!xn.leaf) = false → cL ≤ cc))
    (hrrange : ∀ cc z, (cc, z) ∈ rn.liveAt c.i →
      ((!xn.leaf) = true → cc = 0 ∨ cR < cc) ∧ ((!xn.leaf) = false → cR ≤ cc))
    (hrup : ∀ k z, (k, z) ∈ pn.liveAt c.i → cR < k → ∀ cc z', (cc, z') ∈ rn.liveAt c.i → cc < k)
    (hmade : pn.firstTime = some c.i)
    (hnB : ¬ MergeParentRoom c pn il cL nx ir cR (mergeM2 c xn ln rn cR nx))
    (htime : ∀ last, mergeFullLast pn c.i cL nx cR (mergeM2 c xn ln rn cR nx) = some last →
      pn.size + mergeParentNeed c.i pn il ir cR (mergeM2 c xn ln rn cR nx) ≤ c.p.M ∨
        last.size ≤ c.p.splitAbove)
    (hqc3 : ∀ e q, d - 1 = e + 1 → (w3.path[e]?).map (·.2) = some q →
      (∃ qn, w3.nodes.lookup q = some qn) ∧ q ≠ x)
    (hLive : LiveEdgesH c.p N c.i root Hl) (hHl : ∀ y, Hl y → y = x) :
    WriterWP (mergeTail c x d p pn xn leftSome l ln il r rn ir) c w3
      (fun res w' => (res = 1 →
        LiveEdgesH c.p (wNode c.p base w') c.i w'.top.rootKey (fun y => y = p) ∧
        (∀ y, y ≠ p → y ≠ l → y ≠ r → y ≠ nx → w'.nodes.lookup y = w3.nodes.lookup y) ∧
        (∀ y, y ≠ l → y ≠ r → y < nx → w'.gh.lookup y = w3.gh.lookup y) ∧
        (∃ pn', w'.nodes.lookup p = some pn' ∧ pn'.leaf = pn.leaf) ∧
        w'.top = w3.top) ∧
        (res ≠ 1 → LiveEdges c.p (wNode c.p base w') c.i w'.top.rootKey)) := by
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
  have hc : cL ≠ cR := Nat.ne_of_lt hclt
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
  have hmb : 2 ≤ c.p.mergeBelow := hMP.1
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
  have hElen : (mergeList (!xn.leaf) cR ln.live rn.live).length = ln.live.length + rn.live.length :=
    by simpa using congrArg List.length (mergeList_map_snd (!xn.leaf) cR ln.live rn.live)
  -- the new nodes: their klongs name children of l or r, and they are filled
  have hsrcE : ∀ z, z ∈ (mergeList (!xn.leaf) cR ln.live rn.live).map Prod.snd →
      (∃ c0, (c0, z) ∈ ln.liveAt c.i) ∨ (∃ c0, (c0, z) ∈ rn.liveAt c.i) := by
    intro z hz
    rw [mergeList_map_snd] at hz
    rcases List.mem_append.mp hz with h | h
    · obtain ⟨q', hq', he⟩ := List.mem_map.mp h
      exact Or.inl ⟨q'.1, by rw [KNode.liveAt_of_times ln c.i hlt, ← he]; exact hq'⟩
    · obtain ⟨q', hq', he⟩ := List.mem_map.mp h
      exact Or.inr ⟨q'.1, by rw [KNode.liveAt_of_times rn c.i hrt, ← he]; exact hq'⟩
  have hnewT : ∀ ks : List (Nat × NodeId), ∀ s, Klong.time s ∈
      ({ leaf := !!xn.leaf, ks := newKlongs c.i ks } : KNode).ks → s ≤ c.i := by
    intro ks s hs
    simp only [newKlongs, List.mem_cons, Klong.time.injEq, List.mem_map, reduceCtorEq, and_false,
      exists_false, or_false] at hs
    omega
  have hnewSrc : ∀ ks : List (Nat × NodeId), (∀ z, z ∈ ks.map Prod.snd →
      z ∈ (mergeList (!xn.leaf) cR ln.live rn.live).map Prod.snd) → ∀ cc z,
      (cc, z) ∈ ({ leaf := !!xn.leaf, ks := newKlongs c.i ks } : KNode).liveAt c.i →
      (∃ c0, (c0, z) ∈ ln.liveAt c.i) ∨ (∃ c0, (c0, z) ∈ rn.liveAt c.i) := by
    intro ks hks cc z hmem
    have hm2 := liveAt_newKlongs_mem (!!xn.leaf) c.i c.i ks cc z hmem
    exact hsrcE z (hks z (List.mem_map.mpr ⟨(cc, z), hm2, rfl⟩))
  have hnewFill : ∀ ks : List (Nat × NodeId), CvSorted ks → c.p.mergeBelow ≤ ks.length →
      ({ leaf := !!xn.leaf, ks := newKlongs c.i ks } : KNode).liveAt c.i ≠ [] ∧
      c.p.mergeBelow ≤ (({ leaf := !!xn.leaf, ks := newKlongs c.i ks } : KNode).liveAt c.i).length := by
    intro ks hks hlen
    have hcnt : (({ leaf := !!xn.leaf, ks := newKlongs c.i ks } : KNode).liveAt c.i).length =
        ks.length := by
      rw [KNode.liveAt_of_times _ c.i (hnewT ks)]
      exact newKlongs_cnt_of_sorted _ _ _ hks
    refine ⟨fun h0 => ?_, by rw [hcnt]; exact hlen⟩
    have : (({ leaf := !!xn.leaf, ks := newKlongs c.i ks } : KNode).liveAt c.i).length = 0 := by
      rw [h0]; rfl
    omega
  simp only [writerWP_bind, writerWP_modify]
  refine writerWP_mono (writerWP_and (writerWP_ghOf_frame x c _) (writerWP_ghOf_ghL x c _)) ?_
  intro gh w4 ⟨⟨h4t, h4top, h4n, h4v, h4p, h4m, h4l⟩, h4gh⟩
  have hlk4 : ∀ y, y ≠ x → w4.nodes.lookup y = w3.nodes.lookup y := h4l
  have hnone3 : ∀ z, nx ≤ z → w3.nodes.lookup z = none := by
    intro z hz
    cases h' : w3.nodes.lookup z with
    | none => rfl
    | some _ => have := h3src z (by rw [h']; rfl); omega
  have hpx : p ≠ x := by rcases hxlr with h | h <;> rw [h] <;> assumption
  have hxnx : x < nx := by rcases hxlr with h | h <;> rw [h] <;> assumption
  have hpT : w3.taken.contains p = false := by
    have := hN3 ▸ hpn
    unfold wNode at this
    split at this
    · cases this
    · rename_i h; simpa using h
  have hNw3 : ∀ y, wNode c.p base w3 y = N y := fun y => by rw [hN3]
  have hcl' : ∀ y, y ≠ l → y ≠ r → ∀ q ∈ [(l, lMade), (r, rMade)], y ≠ (q : NodeId × Bool).1 := by
    intro y hyl hyr q hq
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hq
    rcases hq with h | h <;> rw [h] <;> assumption
  have hne' : ∀ q ∈ [(l, lMade), (r, rMade)], (q : NodeId × Bool).1 ≠ p := by
    intro q hq
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hq
    rcases hq with h | h <;> rw [h]
    · exact Ne.symm hpl
    · exact Ne.symm hpr
  have hlr' : ∀ (q : NodeId × Bool), q ∈ [(l, lMade), (r, rMade)] → q.1 = l ∨ q.1 = r := by
    intro q hq
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hq
    rcases hq with h | h <;> rw [h]
    · exact Or.inl rfl
    · exact Or.inr rfl
  have hnoOld : ∀ z, (z = l ∨ z = r) → ∀ cc, (cc, z) ∈ pn.liveAt c.i → cc ≠ cL → cc ≠ cR → False := by
    intro z hz cc hmem h1 h2
    rcases hz with hz | hz
    · rw [hz] at hmem
      exact h1 (hT.oneLink p cc p cL l hp hp ⟨pn, hpn, hmem⟩ hlink_l).2
    · rw [hz] at hmem
      exact h2 (hT.oneLink p cc p cR r hp hp ⟨pn, hpn, hmem⟩ hlink_r).2
  try dsimp only
  cases lMade <;> cases rMade <;>
    simp only [Bool.false_eq_true, ↓reduceIte, writerWP_bind, writerWP_modify, writerWP_pure,
      replacedBy, writerWP_get]
  all_goals
    refine writerWP_mono (writerWP_and (writerWP_newKey_frame _ _ _ _ c _)
      (writerWP_newKey_ghL _ _ _ _ c _)) ?_
    intro m1 w5 ⟨⟨hm1, h5n, h5t, h5top, h5next, h5v, h5p, h5m⟩, h5gh⟩
    refine writerWP_mono (writerWP_and (writerWP_setMadeFor_frame _ _ c _)
      (writerWP_setMadeFor_gh _ _ c _)) ?_
    intro _ w6 ⟨⟨h6n, h6t, h6top, h6next, h6v, h6p⟩, h6gh⟩
    try dsimp only at hm1 h5n h5t h5top h5next h5v h5p h5m
    have hm1 : m1 = nx := by rw [hm1, h4n, h3next]
    subst hm1
    have hw6p : w6.nodes.lookup p = some pn := by
      rw [h6n, h5n, lookup_append_single_ne _ _ _ _ (by omega), hlk4 p hpx, h3p]
    have hw6m1 : w6.nodes.lookup m1 = some ⟨!!xn.leaf, newKlongs c.i first⟩ := by
      rw [h6n, h5n, h4n, h3next, lookup_append_single_self]
      rw [hlk4 _ (by omega)]
      exact hnone3 m1 (Nat.le_refl _)
    have h6taken : w6.taken = w3.taken := by rw [h6t, h5t, h4t]
    have h6old : ∀ y, y ≠ x → y ≠ m1 → w6.nodes.lookup y = w3.nodes.lookup y := by
      intro y hyx hym
      rw [h6n, h5n, h4n, h3next, lookup_append_single_ne _ _ _ _ hym, hlk4 y hyx]
    have h6next' : w6.next = m1 + 2 := by rw [h6next, h5next, h4n, h3next]
    have h6top' : w6.top.rootKey = root := by rw [h6top, h5top, h4top, h3top]
    have hm1T : w3.taken.contains m1 = false := (hfree m1 (Nat.le_refl _)).2
    have hm1N : N m1 = none := (hfree m1 (Nat.le_refl _)).1
    have hlm1 : l ≠ m1 := by omega
    have hrm1 : r ≠ m1 := by omega
    have hpm1 : p ≠ m1 := by omega
    have hm1R : ¬ TReach N c.i root m1 :=
      not_reach_fresh N c.i root m1 hT hm1N (hfreshT m1 (Nat.le_refl _))
    have h6path : w6.path = w3.path := by rw [h6p, h5p, h4p]
    have hqc6 : ∀ e q, d - 1 = e + 1 → (w6.path[e]?).map (·.2) = some q →
        ∃ qn, w6.nodes.lookup q = some qn := by
      intro e q he hq
      rw [h6path] at hq
      obtain ⟨⟨qn, hqn⟩, hqx⟩ := hqc3 e q he hq
      have hqm : q ≠ m1 := by have := h3src q (by rw [hqn]; rfl); omega
      exact ⟨qn, by rw [h6old q hqx hqm, hqn]⟩
    cases hsec : second with
    | none =>
      rw [hsec] at hmkd
      have hfirst : first = mergeList (!xn.leaf) cR ln.live rn.live := splitMerged_one _ _ _ _ hmkd
      simp only [writerWP_bind, writerWP_pure]
      have hm2n : mergeM2 c xn ln rn cR m1 = none := by simp [mergeM2, hmk, hsec]
      rw [hm2n] at hnB htime
      refine writerWP_mergeParent_fullB p pn (d - 1) il cL m1 ir cR none c w6 _ hw6p hnB ?_
      intro last compact s7 hlast hcomp
      obtain ⟨hlastT, hleafl, hnoneL, _⟩ := mergeFullLast_liveAt pn c.i cL m1 cR none last hlast hpt
      have hlasteq : (⟨pn.leaf, last.ks⟩ : KNode) = last := by
        cases last with
        | mk lf ks => simp only at hleafl; rw [hleafl]
      have hcs : (!compact && decide (last.size > c.p.splitAbove)) = false := by
        rcases htime last hlast with h | h
        · rw [hcomp, decide_eq_true h]; rfl
        · have h' : ¬ (last.size > c.p.splitAbove) := by omega
          simp [h']
      unfold handleFull
      refine writerWP_mono (writerWP_handleFullWith_timeInPlace_nodesL _ (d - 1) p pn last compact c
        ({ w6 with trail := s7 :: w6.trail } : W) hw6p hmade hcs hqc6) ?_
      rintro _ w7 ⟨h7n, h7t, h7top, h7gh, _⟩
      change w7.nodes = upsert w6.nodes p ⟨pn.leaf, last.ks⟩ at h7n
      change w7.taken = w6.taken at h7t
      change w7.top = w6.top at h7top
      change w7.gh = w6.gh at h7gh
      have hlk7 : w7.nodes.lookup p = some ⟨pn.leaf, last.ks⟩ := by
        rw [h7n, lookup_upsert]; simp
      have hchar1 : ∀ cc z, (cc, z) ∈ (⟨pn.leaf, last.ks⟩ : KNode).liveAt c.i →
          (cc = cL ∧ z = m1) ∨ ((cc, z) ∈ pn.liveAt c.i ∧ cc ≠ cL ∧ cc ≠ cR) := by
        rw [hlasteq]; exact hnoneL rfl
      have hcLm1 : (cL, m1) ∈ (⟨pn.leaf, last.ks⟩ : KNode).liveAt c.i := by
        rw [hlasteq, KNode.liveAt_of_times last c.i hlastT]
        apply bk_mem_of_lookup
        rw [(mergeFullLast_lookup pn c.i cL m1 cR none last hlast).2.1 rfl cL]
        simp
      refine writerWP_mono (writerWP_and (writerWP_mergeCleanup_frameV p m1 c.i c _ w7 _ hne' hlk7
        (fun q hq c' hmem => by
          rcases hchar1 c' q.1 hmem with ⟨_, h⟩ | ⟨hold, h1, h2⟩
          · rcases hlr' q hq with h' | h' <;> rw [h'] at h
            · exact hlm1 h
            · exact hrm1 h
          · exact hnoOld q.1 (hlr' q hq) c' hold h1 h2))
        (writerWP_and (writerWP_mergeCleanup_frameL p m1 c _ w7)
          (writerWP_mergeCleanup_ghp p m1 c _ w7 ⟨_, hlk7⟩ hne'))) ?_
      intro _ w8 ⟨⟨h8top, _, _, h8t, h8l, pn8, h8p, h8leaf, _, h8iff⟩, ⟨_, _, h8fl⟩, h8gp⟩
      refine ⟨fun _ => ?_, fun h => absurd rfl h⟩
      have h8tc : ∀ y, y ≠ l → y ≠ r → w8.taken.contains y = w3.taken.contains y := by
        intro y hyl hyr; rw [h8t y (hcl' y hyl hyr), h7t, h6taken]
      have h8l' : ∀ y, y ≠ p → y ≠ l → y ≠ r → w8.nodes.lookup y = w6.nodes.lookup y := by
        intro y hyp hyl hyr; rw [h8l y hyp (hcl' y hyl hyr), h7n, lookup_upsert]; simp [hyp]
      refine ⟨?_, fun y hyp hyl hyr hym => ?_, fun y hyl hyr hylt => ?_, ⟨pn8, h8p, by rw [h8leaf]⟩,
        by rw [h8top, h7top, h6top, h5top, h4top]⟩
      rotate_left
      · rw [h8l' y hyp hyl hyr, h6old y (by rcases hxlr with h | h <;> rw [h] <;> assumption) hym]
      · have hyx : y ≠ x := by rcases hxlr with h | h <;> rw [h] <;> assumption
        by_cases hyp : y = p
        · rw [hyp, h8gp, h7gh, h6gh, h5gh p hpm1, h4gh p hpx]
        · rw [(h8fl y hyp (hcl' y hyl hyr)).1, h7gh, h6gh, h5gh y (by omega), h4gh y hyx]
      rw [h8top, h7top, h6top']
      have hfirstS : CvSorted first := by rw [hfirst]; exact hsortE
      have hmlen : first.length = ln.live.length + rn.live.length := by rw [hfirst, hElen]
      obtain ⟨hmne, hmfill⟩ := hnewFill first hfirstS (by rw [hmlen]; exact hsib)
      refine liveEdgesH_mergeOne c.p N (wNode c.p base w8) c.i root p l r m1 pn ln rn pn8
        ⟨!!xn.leaf, newKlongs c.i first⟩ cL cR Hl hT hp hpn hpleaf hpL hpR hln hrn hm1R ?_
        (hnewSrc first (fun z hz => by rw [hfirst] at hz; exact hz))
        (by show (!!xn.leaf) = ln.leaf; rw [hll, Bool.not_not]) (by rw [hrl, hll]) hmne hmfill ?_
        (by rw [h8leaf]) ?_ ?_ ?_
        (fun y hy => by
          have hyx := hHl y hy
          rcases hxlr with h | h
          · exact Or.inl (hyx.trans h)
          · exact Or.inr (hyx.trans h))
        hLive
      · simp only [wNode, h8tc m1 (Ne.symm hlm1) (Ne.symm hrm1), hm1T, Bool.false_eq_true,
          ↓reduceIte]
        rw [h8l' m1 (Ne.symm hpm1) (Ne.symm hlm1) (Ne.symm hrm1), hw6m1]
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
        rw [h8tc y hyl hyr, h8l' y hyp hyl hyr,
          h6old y (by rcases hxlr with h | h <;> rw [h] <;> assumption) hym]
    | some ksg =>
      obtain ⟨ks2, g2⟩ := ksg
      rw [hsec] at hmkd
      have hcap : 1 ≤ c.p.mergeMax := by have := hMP.1; have := hMP.2.1; omega
      obtain ⟨yg, hE1, hgs, hE2⟩ := mrg_splitMerged_two (!xn.leaf) c.p.mergeMax hcap _ first ks2 g2 hmkd
      have hElt : c.p.mergeMax < (mergeList (!xn.leaf) cR ln.live rn.live).length := by
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
      obtain ⟨hgL, _, hgU0⟩ := mrg_two_g (!xn.leaf) cL cR ln.live rn.live
        (((mergeList (!xn.leaf) cR ln.live rn.live).length + 1) / 2) g2 yg hsortE (by omega) hgs
        hclt hlnL hrnR
      have hg2 : g2 ≠ cR → pn.live.lookup g2 = none := by
        intro hne
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
      -- the halves: sorted, filled, naming children of l or r
      have hsortD : CvSorted ((mergeList (!xn.leaf) cR ln.live rn.live).drop
          (((mergeList (!xn.leaf) cR ln.live rn.live).length + 1) / 2)) :=
        hsortE.sublist (List.drop_sublist _ _)
      have hS1 : CvSorted first := by rw [hE1]; exact hsortE.sublist (List.take_sublist _ _)
      have hS2 : CvSorted ks2 := by
        rw [hE2]
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
      have hlen1 : first.length = ((mergeList (!xn.leaf) cR ln.live rn.live).length + 1) / 2 := by
        rw [hE1, List.length_take]; omega
      have hlen2 : ks2.length = (mergeList (!xn.leaf) cR ln.live rn.live).length -
          ((mergeList (!xn.leaf) cR ln.live rn.live).length + 1) / 2 := by
        rw [hE2]
        split <;> simp [renameHead_length, List.length_drop]
      have hmb2 := hMP.2.1
      obtain ⟨hmne1, hmfill1⟩ := hnewFill first hS1 (by omega)
      obtain ⟨hmne2, hmfill2⟩ := hnewFill ks2 hS2 (by omega)
      have hsnd := splitMerged_map_snd (!xn.leaf) c.p.mergeMax _ first ks2 g2 hmkd
      have hsrc1 : ∀ z, z ∈ first.map Prod.snd →
          z ∈ (mergeList (!xn.leaf) cR ln.live rn.live).map Prod.snd := by
        intro z hz; rw [← hsnd, List.map_append]; exact List.mem_append_left _ hz
      have hsrc2 : ∀ z, z ∈ ks2.map Prod.snd →
          z ∈ (mergeList (!xn.leaf) cR ln.live rn.live).map Prod.snd := by
        intro z hz; rw [← hsnd, List.map_append]; exact List.mem_append_right _ hz
      simp only [writerWP_bind, writerWP_pure]
      refine writerWP_mono (writerWP_newKey_frame _ _ _ _ c _) ?_
      intro m2 w7 ⟨hm2, h7n, h7t, h7top, h7next, h7v, h7p, h7m⟩
      try simp only [writerWP_bind, writerWP_pure, writerWP_get]
      refine writerWP_mono (writerWP_setMadeFor_frame _ _ c _) ?_
      intro _ w8 ⟨h8n, h8t, h8top, h8next, h8v, h8p⟩
      try simp only [writerWP_pure]
      have hm2' : m2 = m1 + 2 := by rw [hm2, h6next']
      subst hm2'
      have hw8p : w8.nodes.lookup p = some pn := by
        rw [h8n, h7n, lookup_append_single_ne _ _ _ _ (by omega), hw6p]
      have hw8m1 : w8.nodes.lookup m1 = some ⟨!!xn.leaf, newKlongs c.i first⟩ := by
        rw [h8n, h7n, lookup_append_single_ne _ _ _ _ (by omega), hw6m1]
      have hw8m2 : w8.nodes.lookup (m1 + 2) = some ⟨!!xn.leaf, newKlongs c.i ks2⟩ := by
        rw [h8n, h7n, h6next', lookup_append_single_self]
        rw [h6old _ (by omega) (by omega)]
        exact hnone3 _ (by omega)
      have h8old : ∀ y, y ≠ x → y ≠ m1 → y ≠ m1 + 2 → w8.nodes.lookup y = w3.nodes.lookup y := by
        intro y hyx hym hym2
        rw [h8n, h7n, h6next', lookup_append_single_ne _ _ _ _ hym2, h6old y hyx hym]
      have h8taken : w8.taken = w3.taken := by rw [h8t, h7t, h6taken]
      have hm2T : w3.taken.contains (m1 + 2) = false := (hfree (m1 + 2) (by omega)).2
      have hm2N : N (m1 + 2) = none := (hfree (m1 + 2) (by omega)).1
      have hm2R : ¬ TReach N c.i root (m1 + 2) :=
        not_reach_fresh N c.i root (m1 + 2) hT hm2N (hfreshT (m1 + 2) (by omega))
      have hlm2 : l ≠ m1 + 2 := by omega
      have hrm2 : r ≠ m1 + 2 := by omega
      have hpm2 : p ≠ m1 + 2 := by omega
      have hm2s : mergeM2 c xn ln rn cR m1 = some (m1 + 2, g2) := by simp [mergeM2, hmk, hsec]
      rw [hm2s] at hnB htime
      refine writerWP_mergeParent_fullB p pn (d - 1) il cL m1 ir cR (some (m1 + 2, g2)) c w8 _ hw8p hnB ?_
      intro last compact s9 hlast hcomp
      obtain ⟨hlastT, hleafl, _, _⟩ := mergeFullLast_liveAt pn c.i cL m1 cR _ last hlast hpt
      have hlasteq : (⟨pn.leaf, last.ks⟩ : KNode) = last := by
        cases last with
        | mk lf ks => simp only at hleafl; rw [hleafl]
      have hcs : (!compact && decide (last.size > c.p.splitAbove)) = false := by
        rcases htime last hlast with h | h
        · rw [hcomp, decide_eq_true h]; rfl
        · have h' : ¬ (last.size > c.p.splitAbove) := by omega
          simp [h']
      have hqc8 : ∀ e q, d - 1 = e + 1 → (w8.path[e]?).map (·.2) = some q →
          ∃ qn, w8.nodes.lookup q = some qn := by
        intro e q he hq
        rw [h8p, h7p] at hq
        obtain ⟨qn, hqn⟩ := hqc6 e q he hq
        have hqm2 : q ≠ m1 + 2 := by
          intro hqe
          rw [hqe, h6old _ (by omega) (by omega), hnone3 _ (by omega)] at hqn
          cases hqn
        exact ⟨qn, by rw [h8n, h7n, h6next', lookup_append_single_ne _ _ _ _ hqm2, hqn]⟩
      unfold handleFull
      refine writerWP_mono (writerWP_handleFullWith_timeInPlace_nodesL _ (d - 1) p pn last compact c
        ({ w8 with trail := s9 :: w8.trail } : W) hw8p hmade hcs hqc8) ?_
      rintro _ w9 ⟨h9n, h9t, h9top, _, _⟩
      change w9.nodes = upsert w8.nodes p ⟨pn.leaf, last.ks⟩ at h9n
      change w9.taken = w8.taken at h9t
      change w9.top = w8.top at h9top
      rw [hlasteq] at h9n
      have hlk9 : w9.nodes.lookup p = some last := by
        rw [h9n, lookup_upsert]; simp
      have hlk2 := (mergeFullLast_lookup pn c.i cL m1 cR _ last hlast).2.2 (m1 + 2) g2 rfl
      have hmpT2 := hlastT
      have hchar2 : ∀ cc z, (cc, z) ∈
          last.liveAt c.i →
          z = m1 ∨ z = m1 + 2 ∨ ((cc, z) ∈ pn.liveAt c.i ∧ cc ≠ cL ∧ cc ≠ cR) := by
        intro cc z hmem
        rw [KNode.liveAt_of_times _ c.i hmpT2] at hmem
        have hlk := lookup_of_mem_nodup _ (KNode.live_keys_nodup _) cc z hmem
        rw [hlk2 cc] at hlk
        by_cases h0 : cc = g2
        · rw [if_pos h0] at hlk
          exact Or.inr (Or.inl (Option.some.inj hlk).symm)
        · by_cases h1 : cc = cL
          · rw [if_neg h0, if_pos h1] at hlk
            exact Or.inl (Option.some.inj hlk).symm
          · by_cases h2 : cc = cR
            · rw [if_neg h0, if_neg h1, if_pos h2] at hlk; cases hlk
            · rw [if_neg h0, if_neg h1, if_neg h2] at hlk
              right; right
              refine ⟨?_, h1, h2⟩
              rw [KNode.liveAt_of_times pn c.i hpt]
              exact bk_mem_of_lookup _ cc z hlk
      have hlen9 : pn.live.length ≤
          last.live.length :=
        live_len_mergeTwo pn _ cL cR g2 m1 (m1 + 2) hlk2 (by omega)
          ⟨r, by rw [KNode.live_lookup]; exact keyLookup_of_last _ _ _ ir r hR hRL⟩ hg2
      refine writerWP_mono (writerWP_mergeCleanup_frameV p m1 c.i c _ w9 _ hne' hlk9
        (fun q hq c' hmem => by
          rcases hchar2 c' q.1 hmem with h | h | ⟨hold, h1, h2⟩
          · rcases hlr' q hq with h' | h' <;> rw [h'] at h
            · exact hlm1 h
            · exact hrm1 h
          · rcases hlr' q hq with h' | h' <;> rw [h'] at h
            · exact hlm2 h
            · exact hrm2 h
          · exact hnoOld q.1 (hlr' q hq) c' hold h1 h2)) ?_
      intro _ w10 ⟨h10top0, _, _, h10t, h10l, pn10, h10p, h10leaf, h10times, h10iff⟩
      refine ⟨fun h => absurd h (by simp), fun _ => ?_⟩
      have h10tc : ∀ y, y ≠ l → y ≠ r → w10.taken.contains y = w3.taken.contains y := by
        intro y hyl hyr; rw [h10t y (hcl' y hyl hyr), h9t, h8taken]
      have h10l' : ∀ y, y ≠ p → y ≠ l → y ≠ r → w10.nodes.lookup y = w8.nodes.lookup y := by
        intro y hyp hyl hyr; rw [h10l y hyp (hcl' y hyl hyr), h9n, lookup_upsert]; simp [hyp]
      have h10top : w10.top.rootKey = root := by
        rw [h10top0, h9top, h8top, h7top, h6top']
      rw [h10top]
      have hpn10T := h10times hmpT2
      have hlen10 : (pn.liveAt c.i).length ≤ (pn10.liveAt c.i).length := by
        rw [KNode.liveAt_of_times pn c.i hpt, KNode.liveAt_of_times pn10 c.i hpn10T]
        refine Nat.le_trans hlen9 (length_le_of_nodup_sub _ _
          (nodup_of_keys_nodup _ (KNode.live_keys_nodup _)) (fun q hq => ?_))
        have hq' : (q.1, q.2) ∈ pn10.liveAt c.i :=
          (h10iff q.1 q.2).mpr (by rw [KNode.liveAt_of_times _ c.i hmpT2]; exact hq)
        rw [KNode.liveAt_of_times pn10 c.i hpn10T] at hq'
        exact hq'
      refine liveEdges_mergeTwo c.p N (wNode c.p base w10) c.i root p l r m1 (m1 + 2) pn ln rn pn10
        ⟨!!xn.leaf, newKlongs c.i first⟩ ⟨!!xn.leaf, newKlongs c.i ks2⟩ cL cR Hl hT hp hpn hpleaf
        hpL hpR hln hrn hm1R hm2R ?_ ?_ ?_
        (by show (!!xn.leaf) = ln.leaf; rw [hll, Bool.not_not])
        (by show (!!xn.leaf) = ln.leaf; rw [hll, Bool.not_not]) (by rw [hrl, hll])
        ⟨hmne1, hmne2⟩ ⟨hmfill1, hmfill2⟩ ?_ (by rw [h10leaf]; exact hleafl)
        (fun cc z hmem => hchar2 cc z ((h10iff cc z).mp hmem)) hlen10 ?_
        (fun y hy => by
          have hyx := hHl y hy
          rcases hxlr with h | h
          · exact Or.inl (hyx.trans h)
          · exact Or.inr (hyx.trans h))
        hLive
      · simp only [wNode, h10tc m1 (Ne.symm hlm1) (Ne.symm hrm1), hm1T, Bool.false_eq_true,
          ↓reduceIte]
        rw [h10l' m1 (Ne.symm hpm1) (Ne.symm hlm1) (Ne.symm hrm1), hw8m1]
      · simp only [wNode, h10tc (m1 + 2) (Ne.symm hlm2) (Ne.symm hrm2), hm2T, Bool.false_eq_true,
          ↓reduceIte]
        rw [h10l' (m1 + 2) (Ne.symm hpm2) (Ne.symm hlm2) (Ne.symm hrm2), hw8m2]
      · intro mn hmn cc z hmem
        rcases hmn with h | h <;> subst h
        · exact hnewSrc first hsrc1 cc z hmem
        · exact hnewSrc ks2 hsrc2 cc z hmem
      · simp only [wNode, h10tc p hpl hpr, hpT, Bool.false_eq_true, ↓reduceIte, h10p]
      · intro y hyp hyl hyr hym hym2
        rw [← hNw3 y]
        unfold wNode
        rw [h10tc y hyl hyr, h10l' y hyp hyl hyr,
          h8old y (by rcases hxlr with h | h <;> rw [h] <;> assumption) hym hym2]

/-! ## At a round: the made parent's time split in place -/

/-- The case of `MergeTailFullRestOK` that `writerWP_mergeTail_liveMade` proves:
the merge's parent p, made by the transaction, goes `full` and splits in time
(in place). -/
def MergeFullMadeTime (c : Ctx) (v3 : W) (pn xn ln rn : KNode) (il cL ir cR : Nat) :
    Prop :=
  pn.firstTime = some c.i ∧
  ∀ last, mergeFullLast pn c.i cL v3.next cR (mergeM2 c xn ln rn cR v3.next) = some last →
    pn.size + mergeParentNeed c.i pn il ir cR (mergeM2 c xn ln rn cR v3.next) ≤ c.p.M ∨
      last.size ≤ c.p.splitAbove

set_option maxHeartbeats 16000000 in
/-- `MergeTailFullOK` in its case `MergeFullMadeTime`: at a round with
`MergeLiveOK`'s facts, the merge's tail keeps the hole's form one height up, the
hole p, which the next round's descent finds (`descendToHeight_up`: the path
reads alike above p, p's height too). -/
theorem writerWP_mergeTail_liveMadeRound (c : Ctx) (base : View BVal)
    (hvc : ViewCoherent c base) (hm : c.p.merges = true) (hMP : MergeParamsOK c.p)
    {B : NodeId} {H : NodeId → Nat → Prop} (hvo : ViewHtOK H B c)
    (key : Key) (g h : Nat) (v v1 v3 : W) (d F : Nat) (w0 : W) (k0 : Key) (KO : KindOracle)
    (X : Nat → NodeId) (K : Nat → Nat) (Nn : Nat → KNode) (x p : NodeId)
    (pn xn : KNode)
    (hS : descendToHeight key g h c v = .ok (d, v1)) (hd : 0 < d)
    (hr13 : ReadsAs c.p base v1 v3) (hk13 : ObsKept c v1 v3) (hp13 : v3.path = v1.path)
    (hLH : LiveHoleW key g h c base v)
    (hJ3 : DelInvJ c base w0 k0 F KO B B v3) (hP3 : PathOK c v3 d X K Nn)
    (hb1 : Book B c v1) (hi1 : HtInv H B c v1) (hpf1 : PathFreeTo v1 v1.path.length)
    (hx : (v3.path[d]?).map (·.2) = some x) (hpath : (v3.path[d - 1]?).map (·.2) = some p)
    (hplk : v3.nodes.lookup p = some pn) (hpleaf : pn.leaf = false)
    (leftSome : Bool) (l : NodeId) (ln : KNode) (il : Nat) (r : NodeId) (rn : KNode)
    (ir cL cR : Nat) (w3 : W) (hr3 : ReadsAs c.p base v3 w3)
    (h3p : w3.nodes.lookup p = some pn) (hk3 : ObsKept c v3 w3)
    (hsrc3 : ∀ z, (w3.nodes.lookup z).isSome = true → (v3.nodes.lookup z).isSome = true ∨
      (c.view z).isSome = true)
    (hL : pn.ks[il]? = some (.key cL l)) (hLL : LastLive pn.ks pn.lastBitmap il cL)
    (hR : pn.ks[ir]? = some (.key cR r)) (hRL : LastLive pn.ks pn.lastBitmap ir cR) (hclt : cL < cR)
    (hadj : ∀ cc z, (cc, z) ∈ pn.liveAt c.i → cc ≤ cL ∨ cR ≤ cc)
    (hll : ln.leaf = xn.leaf) (hrl : rn.leaf = xn.leaf)
    (hxlr : x = l ∨ x = r) (hln : wNode c.p base v3 l = some ln) (hrn : wNode c.p base v3 r = some rn)
    (hpre3 : v3.nodes <+: w3.nodes) (hpath3 : w3.path = v3.path)
    (hnB : ¬ MergeParentRoom c pn il cL v3.next ir cR (mergeM2 c xn ln rn cR v3.next))
    (hN : MergeFullMadeTime c v3 pn xn ln rn il cL ir cR) :
    WriterWP (mergeTail c x d p pn xn leftSome l ln il r rn ir) c w3
      (fun res v4 => (res = 1 → LiveHoleW key g (h + 1) c base v4) ∧
        (res ≠ 1 → LiveEdges c.p (wNode c.p base v4) c.i v4.top.rootKey)) := by
  obtain ⟨hmade, htime⟩ := hN
  have hI : PutInv c base v3 := hJ3.1.1.1
  have hRO : RangeOrder (wNode c.p base v3) c.i v3.top.rootKey := hJ3.1.1.2.2.1
  obtain ⟨hX, _, hS2, _, _⟩ := id hP3
  have hXi : ∀ i, i ≤ d → ∀ z, (v3.path[i]?).map (·.2) = some z → z = X i := by
    intro i hi z hz; have := hX i hi; rw [hz] at this; exact Option.some.inj this
  have hpX := hXi (d - 1) (by omega) p hpath
  have hxX := hXi d (Nat.le_refl _) x hx
  have hNlk : ∀ i, i ≤ d → wNode c.p base v3 (X i) = some (Nn i) := by
    intro i hi
    obtain ⟨a, b⟩ := hS2 i hi
    simp only [wNode, b, Bool.false_eq_true, ↓reduceIte, a]
  have hpnN : Nn (d - 1) = pn := by
    have := (hS2 (d - 1) (by omega)).1; rw [← hpX, hplk] at this; exact (Option.some.inj this).symm
  have hpn : wNode c.p base v3 p = some pn := by rw [hpX, ← hpnN]; exact hNlk _ (by omega)
  have hdep : ∀ i, i ≤ d → PathLen (wNode c.p base v3) c.i v3.top.rootKey (X i) i :=
    pathOK_depth c base v3 d X K Nn hP3
  have hpP : PathLen (wNode c.p base v3) c.i v3.top.rootKey p (d - 1) := by
    rw [hpX]; exact hdep _ (by omega)
  have hpR := hpP.reach
  have hpRS := tReach_reachS _ c.i _ _ hpR
  have hfree : ∀ z, v3.next ≤ z → wNode c.p base v3 z = none ∧ v3.taken.contains z = false := by
    intro z hz
    have hl : v3.nodes.lookup z = none := by
      cases h' : v3.nodes.lookup z with
      | none => rfl
      | some _ => have := hI.ids.1 z (by rw [h']; rfl); omega
    have ht : v3.taken.contains z = false := by
      cases h' : v3.taken.contains z with
      | false => rfl
      | true => have := hI.ids.2.2.1 z h'; omega
    refine ⟨?_, ht⟩
    simp only [wNode, ht, Bool.false_eq_true, ↓reduceIte, hl, (hI.fresh z hz).1]
  have hfreshT : ∀ z, v3.next ≤ z → ∀ u c', TReach (wNode c.p base v3) c.i v3.top.rootKey u →
      ¬ TLink (wNode c.p base v3) c.i u c' z := by
    intro z hz u c' hu hl
    obtain ⟨un, hun, hc⟩ := hl
    have := hI.links u un c' z (tReach_reachS _ _ _ _ hu) hun hc
    omega
  have hmemL : (cL, l) ∈ pn.liveAt c.i := by
    rw [KNode.liveAt_of_times pn c.i (hI.times p pn hpn)]
    apply bk_mem_of_lookup
    rw [KNode.live_lookup]
    exact keyLookup_of_last _ _ _ il l hL hLL
  have hmemR : (cR, r) ∈ pn.liveAt c.i := by
    rw [KNode.liveAt_of_times pn c.i (hI.times p pn hpn)]
    apply bk_mem_of_lookup
    rw [KNode.live_lookup]
    exact keyLookup_of_last _ _ _ ir r hR hRL
  obtain ⟨hlr1, hlr2⟩ := mrg_child_range (wNode c.p base v3) c.i v3.top.rootKey hRO p pn hpRS hpn
    hpleaf cL l ln hmemL hln
  obtain ⟨hrr1, hrr2⟩ := mrg_child_range (wNode c.p base v3) c.i v3.top.rootKey hRO p pn hpRS hpn
    hpleaf cR r rn hmemR hrn
  have hllow : ∀ cc z, (cc, z) ∈ ln.liveAt c.i →
      ((!xn.leaf) = true → cc = 0 ∨ cL < cc) ∧ ((!xn.leaf) = false → cL ≤ cc) := by
    intro cc z h'
    have h1 := hlr1 cc z h'
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
      · exact h1.1 hxl hc0
  have hrrange : ∀ cc z, (cc, z) ∈ rn.liveAt c.i →
      ((!xn.leaf) = true → cc = 0 ∨ cR < cc) ∧ ((!xn.leaf) = false → cR ≤ cc) := by
    intro cc z h'
    have h1 := hrr1 cc z h'
    rw [hrl] at h1
    constructor
    · intro hin
      have hxl : xn.leaf = false := by simpa using hin
      rcases (h1.2 hxl) with h0 | h0
      · exact Or.inl h0
      · exact Or.inr (h0 (by omega))
    · intro hin
      have hxl : xn.leaf = true := by simpa using hin
      exact h1.1 hxl (by omega)
  -- the round's descent
  obtain ⟨_, _, _, _, _, _, _, _, _, hk01⟩ := writerWP_descendToHeight_rd key g h c v d v1 hS
  have hr01 : ReadsAs c.p base v v1 := writerWP_descendToHeight_readsU key g h c base hvc v _ v1 hS
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
  have hlP : PathLen (wNode c.p base v3) c.i v3.top.rootKey l (d - 1 + 1) :=
    PathLen.link hpP ⟨pn, hpn, hmemL⟩
  have hrP : PathLen (wNode c.p base v3) c.i v3.top.rootKey r (d - 1 + 1) :=
    PathLen.link hpP ⟨pn, hpn, hmemR⟩
  have hqc3 : ∀ e q, d - 1 = e + 1 → (w3.path[e]?).map (·.2) = some q →
      (∃ qn, w3.nodes.lookup q = some qn) ∧ q ≠ x := by
    intro e q he hq
    rw [hpath3] at hq
    have hqX := hXi e (by omega) q hq
    refine ⟨⟨Nn e, lookup_of_prefix _ _ hpre3 _ _ (by rw [hqX]; exact (hS2 e (by omega)).1)⟩, ?_⟩
    intro hqx
    have h1 := hdep e (by omega)
    rw [← hqX, hqx, hxX] at h1
    have := PathLen.depth_unique hI.tree _ _ _ h1 (hdep d (Nat.le_refl _)); omega
  refine writerWP_mono (writerWP_mergeTail_liveMade c base x d p pn xn leftSome l ln il r rn ir cL cR
    (wNode c.p base v3) v3.top.rootKey v3.next w3 (HoleAtW key g h c v) hm hMP hI.tree hpR hpn
    hL hLL hR hRL hclt hadj hxlr hln hrn (hI.times p pn hpn) (fun cc z zn _ hzn => hI.times z zn hzn)
    hr3.1 (by rw [hr3.2.1]) hr3.2.2.2.2 h3p
    (fun z hz => by
      rcases hsrc3 z hz with h' | h'
      · exact hI.ids.1 z h'
      · exact hI.ids.2.1 z h')
    (fun z hz => ⟨(hfree z hz).1, by rw [hr3.2.2.1]; exact (hfree z hz).2⟩) hfreshT hpleaf hll hrl
    (fun cc z h' => hlr2 cR r hmemR hclt cc z h') hllow hrrange
    (fun k z hk hkc cc z' h' => hrr2 k z hk hkc cc z' h') hmade hnB htime hqc3 hLive hHl) ?_
  rintro res v4 ⟨hpost, hpost2⟩
  refine ⟨fun hres => ?_, hpost2⟩
  obtain ⟨hL4, hfr4, hgfr4, ⟨pn4, hp4, _⟩, htop4⟩ := hpost hres
  have hlen1 : v1.path.length = d + 1 := by
    obtain ⟨_, _, hl, _, _⟩ := descend_exit_shape key g h c v v1 d hS
    omega
  have hpathX : ∀ j, j ≤ d → (v1.path.map (·.2))[j]? = some (X j) := by
    intro j hj; rw [List.getElem?_map, ← hp13]; exact hX j hj
  have hmemIdx : ∀ (k : Nat) u, u ∈ (List.map (·.2) v1.path).take k → ∃ j, j < k ∧ j < d + 1 ∧ u = X j := by
    intro k u hu
    rw [List.mem_iff_getElem] at hu
    obtain ⟨j, hj, hju⟩ := hu
    simp only [List.length_take, List.length_map] at hj
    refine ⟨j, by omega, by omega, ?_⟩
    have := hpathX j (by omega)
    rw [← hju, List.getElem_take] at *
    rw [List.getElem?_eq_getElem (by simp; omega)] at this
    exact Option.some.inj this
  have hdl2 : (v1.path.map (·.2)).dropLast.dropLast = (v1.path.map (·.2)).take (d - 1) := by
    simp only [List.dropLast_eq_take, List.length_take, List.length_map, hlen1, List.take_take]
    congr 1; omega
  have hdl1 : (v1.path.map (·.2)).dropLast = (v1.path.map (·.2)).take d := by
    simp only [List.dropLast_eq_take, List.length_map, hlen1]
    congr 1
  have hlow : ∀ j, j ≤ d - 1 → X j ≠ l ∧ X j ≠ r ∧ X j < v3.next ∧
      v3.nodes.lookup (X j) = some (Nn j) := by
    intro j hj
    have hPj := hdep j (by omega)
    have hlj := (hS2 j (by omega)).1
    refine ⟨fun he => ?_, fun he => ?_, hI.ids.1 _ (by rw [hlj]; rfl), hlj⟩
    · rw [he] at hPj; have := PathLen.depth_unique hI.tree _ _ _ hPj hlP; omega
    · rw [he] at hPj; have := PathLen.depth_unique hI.tree _ _ _ hPj hrP; omega
  have hw3lk : ∀ j, j ≤ d - 1 → w3.nodes.lookup (X j) = some (Nn j) :=
    fun j hj => lookup_of_prefix _ _ hpre3 _ _ (hlow j hj).2.2.2
  have hup : HoleAtW key g (h + 1) c v4 p := by
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
    · rw [htop4, hr3.2.1, htop3]
    · intro u hu
      rw [hdl2] at hu
      obtain ⟨j, hj, _, rfl⟩ := hmemIdx (d - 1) u hu
      obtain ⟨hjl, hjr, hjn, hjlk⟩ := hlow j (by omega)
      have hjp : X j ≠ p := by
        intro he
        have h1 := hdep j (by omega); rw [he] at h1
        have := PathLen.depth_unique hI.tree _ _ _ h1 hpP; omega
      rw [← hk03.1, rdN_of_lookup c v3 _ _ hjlk]
      exact rdN_of_lookup c v4 _ _ (by rw [hfr4 _ hjp hjl hjr (by omega), hw3lk j (by omega)])
    · intro u hu
      rw [hdl1] at hu
      obtain ⟨j, hj, _, rfl⟩ := hmemIdx d u hu
      obtain ⟨hjl, hjr, hjn, hjlk⟩ := hlow j (by omega)
      obtain ⟨n4, hn4⟩ : ∃ n4, v4.nodes.lookup (X j) = some n4 := by
        by_cases hjp : X j = p
        · rw [hjp]; exact ⟨_, hp4⟩
        · exact ⟨_, by rw [hfr4 _ hjp hjl hjr (by omega), hw3lk j (by omega)]⟩
      rw [← hk03.2.1, ← hk3.2.1, rdG_of_lookup c v4 _ _ hn4,
        rdG_of_lookup c w3 _ _ (hw3lk j (by omega)), hgfr4 _ hjl hjr hjn]
    · have hpc1 : PathCached v1 := writerWP_descendToHeight_path_cached key g h c v d v1 hS
      have := gradedL_of_ht hvo.heights hb1 hi1 hpf1 hpc1
      rw [hk01.1, hk01.2.1] at this
      exact this
  refine liveEdgesH_mono c.p _ c.i _ (fun y => y = p) _ (fun y hy => hy ▸ hup) ?_ hL4
  intro u un cc y yn' hu hun hcc hyn _ hyp
  exact ((hL4.2 u un cc y yn' hu hun hcc hyn).1 hyp).1

/-! ## What is left of `MergeTailFullRestOK` -/

/-- `MergeTailFullRestOK` but in its case `MergeFullMadeTime` (bergdb 030-01,
step 3's rest): the merge's tail where its parent p goes `full`, and p, not made
by the transaction, splits in space, or is the space root (d = 1) or a segment
root (its parent q a segment leaf), or q has no room for one more klong or would
compact (the cascade); or p, made by the transaction, splits in space (in
place). -/
def MergeTailFullRest2OK (c : Ctx) (base : View BVal) (B : NodeId) (H : NodeId → Nat → Prop) :
    Prop :=
  ∀ (key : Key) (g h : Nat) (v v1 v3 : W) (d F : Nat) (w0 : W) (k0 : Key) (KO : KindOracle)
    (top0 : Top) (X : Nat → NodeId) (K : Nat → Nat) (Nn : Nat → KNode) (x p : NodeId)
    (pn xn : KNode),
    descendToHeight key g h c v = .ok (d, v1) → 0 < d →
    ReadsAs c.p base v1 v3 → ObsKept c v1 v3 → v3.path = v1.path →
    LiveHoleW key g h c base v →
    DelInvJ c base w0 k0 F KO B B v3 → PutBook c B top0 v3 → PathOK c v3 d X K Nn →
    Book B c v1 → HtInv H B c v1 → PathFreeTo v1 v1.path.length → HtInv H B c v3 →
    (v3.path[d]?).map (·.2) = some x → (v3.path[d - 1]?).map (·.2) = some p →
    v3.nodes.lookup p = some pn → pn.leaf = false → v3.nodes.lookup x = some xn →
    xn.cnt < c.p.mergeBelow →
    ∀ (leftSome : Bool) (l : NodeId) (ln : KNode) (il : Nat) (r : NodeId) (rn : KNode)
      (ir cL cR : Nat) (w3 : W), ReadsAs c.p base v3 w3 →
    w3.nodes.lookup p = some pn → ObsKept c v3 w3 →
    (∀ z, (w3.nodes.lookup z).isSome = true → (v3.nodes.lookup z).isSome = true ∨
      (c.view z).isSome = true) →
    pn.ks[il]? = some (.key cL l) → LastLive pn.ks pn.lastBitmap il cL →
    pn.ks[ir]? = some (.key cR r) → LastLive pn.ks pn.lastBitmap ir cR → cL < cR →
    (∀ cc z, (cc, z) ∈ pn.liveAt c.i → cc ≤ cL ∨ cR ≤ cc) →
    ln.leaf = xn.leaf → rn.leaf = xn.leaf →
    (x = l ∨ x = r) → wNode c.p base v3 l = some ln → wNode c.p base v3 r = some rn →
    v3.nodes <+: w3.nodes → w3.path = v3.path →
    ¬ MergeParentRoom c pn il cL v3.next ir cR (mergeM2 c xn ln rn cR v3.next) →
    ¬ MergeFullTimeRoom c v3 d p pn xn ln rn il cL ir cR →
    ¬ MergeFullMadeTime c v3 pn xn ln rn il cL ir cR →
    WriterWP (mergeTail c x d p pn xn leftSome l ln il r rn ir) c w3
      (fun res v4 => (res = 1 → LiveHoleW key g (h + 1) c base v4) ∧
        (res ≠ 1 → LiveEdges c.p (wNode c.p base v4) c.i v4.top.rootKey))

/-- `MergeTailFullRestOK` from its rest: its case `MergeFullMadeTime` is proved
(`writerWP_mergeTail_liveMadeRound`). -/
theorem mergeTailFullRestOK_of_rest2 (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base)
    (hm : c.p.merges = true) (hMP : MergeParamsOK c.p) {B : NodeId} {H : NodeId → Nat → Prop}
    (hvo : ViewHtOK H B c) (hF : MergeTailFullRest2OK c base B H) : MergeTailFullRestOK c base B H := by
  intro key g h v v1 v3 d F w0 k0 KO top0 X K Nn x p pn xn hS hd hr13 hk13 hp13 hLH hJ3 hpb3 hP3 hb1
    hi1 hpf1 hi3 hx hpath hplk hpleaf hxlk hcnt leftSome l ln il r rn ir cL cR w3 hr3 h3p hk3 hsrc3
    hL hLL hR hRL hclt hadj hll hrl hxlr hln hrn hpre3 hpath3 hnB hNT
  by_cases hN : MergeFullMadeTime c v3 pn xn ln rn il cL ir cR
  · exact writerWP_mergeTail_liveMadeRound c base hvc hm hMP hvo key g h v v1 v3 d F w0 k0 KO
      X K Nn x p pn xn hS hd hr13 hk13 hp13 hLH hJ3 hP3 hb1 hi1 hpf1 hx hpath hplk hpleaf
      leftSome l ln il r rn ir cL cR w3 hr3 h3p hk3 hsrc3 hL hLL hR hRL hclt hadj hll hrl hxlr hln hrn
      hpre3 hpath3 hnB hN
  · exact hF key g h v v1 v3 d F w0 k0 KO top0 X K Nn x p pn xn hS hd hr13 hk13 hp13 hLH hJ3 hpb3 hP3
      hb1 hi1 hpf1 hi3 hx hpath hplk hpleaf hxlk hcnt leftSome l ln il r rn ir cL cR w3 hr3 h3p hk3
      hsrc3 hL hLL hR hRL hclt hadj hll hrl hxlr hln hrn hpre3 hpath3 hnB hNT hN

/-- `afterDelete` with the hole (bergdb 030-01, steps 3 and 4): from the call's
facts to `LiveEdges`, premises `MergeTailFullRest2OK`, `MergeParamsOK` and R3
after the merges' loop. -/
theorem writerWP_afterDelete_liveTR2 (key : Key) (g : Nat) (c : Ctx) (base : View BVal)
    (hvc : ViewCoherent c base) (hm : c.p.merges = true) (hMP : MergeParamsOK c.p) (KO : KindOracle)
    (B : NodeId) (hv : ViewIdsBelow B c.view) (hk : ViewKinds KO B c)
    (hICEk : ICEFromKinds c base KO B) (hsa2 : 2 ≤ c.p.splitAbove) (hcap : 1 ≤ c.p.mergeMax)
    (hpos : 0 < c.i) {H : NodeId → Nat → Prop} (hvo : ViewHtOK H B c)
    (hkw : ViewKlongsWf c.p c.view) (top0 : Top) (hB : PutBase c base B)
    (hF : MergeTailFullRest2OK c base B H)
    (v : W) (hJ : DelInvJAE c base KO B B v) (hpb : PutBook c B top0 v) (hhi : HtInv H B c v)
    (hLH : LiveHoleW key g 0 c base v)
    (hR3 : WriterWP (mergeUp key g c.p.fuel 0 false) c v
      (fun merged v' => merged = true → R3At key g c v')) :
    WriterWP (afterDelete key g 0) c v
      (fun _ v' => LiveEdges c.p (wNode c.p base v') c.i v'.top.rootKey) :=
  writerWP_afterDelete_liveTR key g c base hvc hm hMP KO B hv hk hICEk hsa2 hcap hpos hvo hkw top0 hB
    (mergeTailFullRestOK_of_rest2 c base hvc hm hMP hvo hF) v hJ hpb hhi hLH hR3


end SIS.Tree
