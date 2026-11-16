/-
`htb`'s sites (bergdb 025-05, step 8): the delete's checked copy keeps the tall nodes'
frame (`TallOK`, HtbFrame.lean). A merge changes its parent, which is no tall node below
the loop's last height, and takes back or unlinks two of the parent's live children;
root collapse takes back a root with one live klong, which is no tall node.
-/
import SIS.Tree.HtbFrame

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

section Merge

variable {base : View BVal} {T : NodeId → Prop}

theorem tk_sibling (p : NodeId) (pn : KNode) (i : Nat) (inner : Bool) (c : Ctx) (w : W)
    (hvc : ViewCoherent c base) (h : TallOK base T c w) :
    WriterWP (sibling p pn i inner) c w (fun sn v => TallOK base T c v ∧ pn.ptr? i = some sn.1) := by
  unfold sibling
  simp only [writerWP_bind, writerWP_read]
  split
  · exact writerWP_throw _ _ _ _
  · rename_i s hs
    simp only [writerWP_bind]
    refine writerWP_mono (tk_getNodeI s c w hvc h) ?_
    rintro sn v ⟨hv, -⟩
    split
    · exact writerWP_throw _ _ _ _
    · exact (writerWP_pure _ _ _ _).mpr ⟨hv, hs⟩

/-- The merge's cleanup: each of the two nodes merged, no tall node, is taken back or
unlinked; the parent is repointed. -/
theorem tk_cleanup (p m1 : NodeId) (c : Ctx) (hmp : MergeParamsOK c.p) (hvc : ViewCoherent c base) :
    ∀ (xs : List (NodeId × Bool)) (w : W), (∀ q ∈ xs, ¬ T q.1) → TallOK base T c w →
    WriterWP (forIn xs PUnit.unit (fun q _ => if q.2 = true then (do
        retarget p q.1 m1
        checkFree q.1
        takenBack q.1
        note "merge.takeback"
        pure (ForInStep.yield PUnit.unit)) else (do
        unlink q.1
        pure (ForInStep.yield PUnit.unit)))) c w (fun _ v => TallOK base T c v) := by
  intro xs
  induction xs with
  | nil => intro w _ h; rw [List.forIn_nil]; exact (writerWP_pure _ _ _ _).mpr h
  | cons q qs ih =>
    intro w hT h
    rw [List.forIn_cons]
    have hq : ¬ T q.1 := hT q List.mem_cons_self
    have hk : ∀ v, TallOK base T c v → WriterWP (forIn qs PUnit.unit _) c v (fun _ v => TallOK base T c v) :=
      fun v hv => ih v (fun q' hq' => hT q' (List.mem_cons_of_mem _ hq')) hv
    simp only [writerWP_bind]
    split
    · simp only [writerWP_bind]
      refine writerWP_mono (tk_retarget p q.1 m1 c w hmp hvc h) ?_
      intro _ w1 h1
      refine writerWP_mono (tk_checkFree q.1 c w1 hmp hvc h1) ?_
      intro _ w2 h2
      refine writerWP_mono (tk_takenBack q.1 c w2 h2 hq) ?_
      intro _ w3 h3
      refine writerWP_mono (tk_note _ c w3 hmp hvc h3) ?_
      intro _ w4 h4
      simp only [writerWP_pure]
      exact hk w4 h4
    · simp only [writerWP_bind]
      refine writerWP_mono (tk_unlink q.1 c w hvc h hq) ?_
      intro _ w1 h1
      simp only [writerWP_pure]
      exact hk w1 h1

theorem tk_ite_note (b : Bool) (s : String) :
    TallKeeps base T (if b = true then note s else (pure PUnit.unit : M PUnit)) := by
  intro c w hmp hvc h
  split
  · exact tk_note s c w hmp hvc h
  · exact (writerWP_pure _ _ _ _).mpr h

macro "tkG " pat:term "," h:term : tactic => `(tactic| (
  (with_unfolding_none guard_target = WriterWP $pat _ _ _)
  tkUse $h))

set_option maxHeartbeats 6400000 in
/-- The merge's tail: the parent p, and the two nodes merged, are no tall nodes. -/
theorem tk_mergeTailChk (c : Ctx) (x : NodeId) (d : Nat) (p : NodeId) (pn xn : KNode)
    (leftSome : Bool) (l : NodeId) (ln : KNode) (il : Nat) (r : NodeId) (rn : KNode) (ir : Nat)
    (w : W) (hmp : MergeParamsOK c.p) (hvc : ViewCoherent c base) (h : TallOK base T c w)
    (hp : ¬ T p) (hl : ¬ T l) (hr : ¬ T r) :
    WriterWP (mergeTailChk c x d p pn xn leftSome l ln il r rn ir) c w
      (fun _ v => TallOK base T c v) := by
  have hlr : ∀ q ∈ [(l, ln.firstTime == some c.i), (r, rn.firstTime == some c.i)], ¬ T q.1 := by
    intro q hq
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hq
    rcases hq with hq | hq <;> rw [hq]
    · exact hl
    · exact hr
  unfold mergeTailChk
  repeat' first
    | (with_reducible assumption)
    | wpSimplify
    | (with_unfolding_none exact writerWP_throw _ _ _ _)
    | tkG (note _), (tk_note _)
    | tkG (@ite _ _ _ (note _) _), (tk_ite_note _ _)
    | tkG (ghOf _), (tk_ghOf _)
    | tkNew
    | tkG (setMadeFor _ _), (tk_setMadeFor _ _)
    | ((with_unfolding_none guard_target = WriterWP (replacedBy _) _ _ _)
       refine writerWP_mono (kd_replacedBy _ _ _) ?_; rintro _ _ ⟨heq, _⟩; subst heq)
    | (with_unfolding_none guard_target = WriterWP (mergeParent _ _ _ _ _ _ _ _) _ _ _
       refine writerWP_mono (tk_mergeParent _ _ _ _ _ _ _ _ c _ hmp hvc (by assumption) hp) ?_
       intro _ _ _)
    | wpSplit
    | split
  all_goals exact tk_cleanup _ _ c hmp hvc _ _ hlr (by assumption)

set_option maxHeartbeats 3200000 in
/-- The merge of x, the path's node at depth d: its parent is no tall node, nor are the
parent's live children. -/
theorem tk_mergeChk (x : NodeId) (d : Nat) (c : Ctx) (w : W) (hmp : MergeParamsOK c.p)
    (hvc : ViewCoherent c base) (h : TallOK base T c w)
    (hq : ∀ a q, w.path[d - 1]? = some (a, q) → w.taken.contains q = false ∧ ¬ T q ∧
      ∀ qn, wNode c.p base w q = some qn → ∀ cv y, (cv, y) ∈ qn.live → ¬ T y) :
    WriterWP (mergeChk x d) c w (fun _ v => TallOK base T c v) := by
  unfold mergeChk
  simp only [writerWP_bind, writerWP_read]
  refine writerWP_mono (kd_pathNode (d - 1) c w) ?_
  rintro p w0 ⟨hw0, ap, hpp⟩
  subst hw0
  obtain ⟨hpt, hpT, hch⟩ := hq ap p hpp
  refine writerWP_mono (tk_getNodeI p c w0 hvc h) ?_
  rintro pn w1 ⟨h1, hn1, ht1, -, -, hw1⟩
  have hpn : wNode c.p base w0 p = some pn := by rw [← hw1]; exact hn1 (by rw [ht1]; exact hpt)
  have hchild : ∀ i cv y, LastLive pn.ks pn.lastBitmap i cv → pn.ptr? i = some y → ¬ T y :=
    fun i cv y hl hy => hch pn hpn cv y (ht_live_of_last hl hy).2
  refine writerWP_mono (tk_getNodeI x c w1 hvc h1) ?_
  rintro xn w2 ⟨h2, -⟩
  refine writerWP_mono (kd_klongAt d c w2) ?_
  rintro cx w2' ⟨hw2, -, -⟩
  subst w2'
  generalize hmi : mergeIdx pn cx = mi
  obtain ⟨ixo, ia, ib⟩ := mi
  have hML := mergeIdx_last pn cx
  rw [hmi] at hML
  obtain ⟨hMx, hMa, hMb⟩ := hML
  split
  · rename_i ix hix
    simp only [writerWP_bind, writerWP_pure]
    refine writerWP_if _ _ _ _ _ _ (fun _ => ?_) (fun hptr => ?_)
    · simp only [writerWP_bind]; exact writerWP_throw _ _ _ _
    have hpx' : pn.ptr? ix = some x := by simpa using hptr
    have hxT := hchild ix cx x (hMx ix hix) hpx'
    have hright : ∀ (wb : W) (ia0 cva : Nat), TallOK base T c wb → LastLive pn.ks pn.lastBitmap ia0 cva →
        WriterWP (do
          let __x ← sibling p pn ia0 !xn.leaf
          mergeTailChk c x d p pn xn false x xn ix __x.1 __x.2 ia0) c wb
          (fun _ v => TallOK base T c v) := by
      intro wb ia0 cva hb hLa
      rw [writerWP_bind]
      refine writerWP_mono (tk_sibling p pn ia0 (!xn.leaf) c wb hvc hb) ?_
      rintro ⟨rs, rsn⟩ w4 ⟨h4, hs4⟩
      exact tk_mergeTailChk c x d p pn xn false x xn ix rs rsn ia0 w4 hmp hvc h4 hpT hxT
        (hchild ia0 cva rs hLa hs4)
    split
    · rename_i ib0 cvb
      obtain ⟨hLb, _⟩ := hMb ib0 cvb rfl
      simp only [writerWP_bind]
      refine writerWP_mono (tk_sibling p pn ib0 (!xn.leaf) c w2 hvc h2) ?_
      rintro ⟨ls, lsn⟩ w3 ⟨h3, hs3⟩
      refine writerWP_if _ _ _ _ _ _ (fun _ => ?_) (fun _ => ?_)
      · exact tk_mergeTailChk c x d p pn xn true ls lsn ib0 x xn ix w3 hmp hvc h3 hpT
          (hchild ib0 cvb ls hLb hs3) hxT
      · rw [writerWP_bind, writerWP_pure]
        dsimp only
        split
        · rename_i ia0 cva _
          obtain ⟨hLa, _⟩ := hMa ia0 cva rfl
          exact hright w3 ia0 cva h3 hLa
        · exact writerWP_throw _ _ _ _
    · rw [writerWP_bind, writerWP_pure]
      dsimp only
      split
      · rename_i ia0 cva
        obtain ⟨hLa, _⟩ := hMa ia0 cva rfl
        exact hright w2 ia0 cva h2 hLa
      · exact writerWP_throw _ _ _ _
  · exact writerWP_throw _ _ _ _

set_option maxHeartbeats 3200000 in
/-- Root collapse takes back a root with one live klong, which is no tall node. -/
theorem tk_collapseRootChk (key : Key) (segment : Nat) (c : Ctx) (hmp : MergeParamsOK c.p)
    (hvc : ViewCoherent c base) :
    ∀ fuel w, TallOK base T c w →
      WriterWP (collapseRootChk key segment fuel) c w (fun _ v => TallOK base T c v) := by
  intro fuel
  induction fuel with
  | zero => intro w _; exact writerWP_throw _ _ _ _
  | succ f ih =>
    intro w h
    unfold collapseRootChk
    simp only [writerWP_bind, writerWP_read]
    refine writerWP_mono (writerWP_descendToSegmentRoot_readsU key segment c base hvc w) ?_
    intro root w1 hr1
    have h1 := h.of_reads hr1
    refine writerWP_mono (tk_getNodeI root c w1 hvc h1) ?_
    rintro n w2 ⟨h2, hn2, -, -, -, -⟩
    have hone : n.cnt ≤ 1 → ¬ T root := by
      intro hc hT
      obtain ⟨_, hun, m, hm, _, _, hmc⟩ := h2 root hT
      rw [hn2 hun] at hm
      cases hm
      omega
    have hmade : n.firstTime ≠ some c.i → ¬ T root := by
      intro hf hT
      obtain ⟨_, hun, m, hm, _, hmf, _⟩ := h2 root hT
      rw [hn2 hun] at hm
      cases hm
      exact hf hmf
    split
    · exact (writerWP_pure _ _ _ _).mpr h2
    · simp only [writerWP_bind]
      refine writerWP_mono (kd_replacedBy root c w2) ?_
      rintro rb w3 ⟨hw3, -⟩
      subst w3
      split
      · exact (writerWP_pure _ _ _ _).mpr h2
      · split
        · exact (writerWP_pure _ _ _ _).mpr h2
        · rename_i only honly
          have hT1 : ¬ T root := hone (KNode.onlyLiveKlong_some_cnt_le_one n only honly)
          split
          · exact writerWP_throw _ _ _ _
          · simp only [writerWP_bind]
            refine writerWP_mono (kd_pathSize c w2) ?_
            rintro sz w4 ⟨hw4, -⟩
            subst w4
            split
            · simp only [writerWP_bind]
              refine writerWP_mono (tk_checkRoot root _ c w2 hmp hvc h2) ?_
              intro _ w5 h5
              refine writerWP_mono (tk_takeBackRoot root _ only c w5 hmp hvc h5 hT1) ?_
              intro _ w6 h6
              exact ih w6 h6
            · simp only [writerWP_bind]
              refine writerWP_mono (tk_replaceRoot root _ only c w2 hmp hvc h2 hT1) ?_
              intro _ w6 h6
              exact ih w6 h6

end Merge

end SIS.Tree
