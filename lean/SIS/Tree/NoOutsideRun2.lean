/-
The run machinery for the runs of `N.Within` (bergdb 025-03; NoOutsideBase.lean):
the take-back's induction over runs and the delete steps' assembly,
each lemma as in its own file (named in its docstring) with `Within` the runs with no
key node outside the level bounds.
-/
import SIS.Tree.NoOutsideRun1

set_option autoImplicit false

namespace SIS.Tree.N

open SIS SIS.Check

/-- As `SIS.Tree.writerTreeOK_foldU`, for the runs of `N.Within`. -/
theorem writerTreeOK_foldU (p : Params) (R : Struct BVal → Time → Prop) (ho : OpTreeOKUnder p R)
    (ts : List Tx) (tx : Tx) (hw : Within p (ts ++ [tx])) (hr : R (treeRun p ts) ts.length) (z : NodeId) (top : Top)
    (hz : lastTop (view (treeSpec p) (treeRun p ts) ts.length) = some z)
    (htop : topOf p (ctxOf p ts).view z = .ok top) :
    ∀ todo done extra, tx.ops = done ++ todo ++ extra → ∀ r w,
      (done.mapM putKv) (ctxOf p ts) (wInit tx top) = .ok (r, w) →
      WriterTreeOK p (treeRun p ts) (ts.length + 1) w →
      ∀ r' w', (todo.mapM putKv) (ctxOf p ts) w = .ok (r', w') →
      WriterTreeOK p (treeRun p ts) (ts.length + 1) w' := by
  intro todo
  induction todo with
  | nil =>
    intro done _ _ r w _ hT r' w' hrun
    simp only [List.mapM_nil, pure, ReaderT.pure, StateT.pure, Except.pure, Except.ok.injEq,
      Prod.mk.injEq] at hrun
    rw [← hrun.2]
    exact hT
  | cons op rest ih =>
    intro done extra hsplit r w hdone hT r' w' hrun
    obtain ⟨a, w1, r1, h1, h2⟩ := mapM_cons_run op rest _ w w' r' hrun
    have hT1 := ho ts tx hw hr z top hz htop done op (rest ++ extra) (by rw [hsplit]; simp) r w hdone
      hT a w1 h1
    have hdone' := mapM_snoc_run done op _ _ w w1 r a hdone h1
    exact ih (done ++ [op]) extra (by rw [hsplit]; simp) _ w1 hdone' hT1 r1 w' h2

/-- As `SIS.Tree.writerTreeOK_reachedU`, for the runs of `N.Within`. -/
theorem writerTreeOK_reachedU (p : Params) (R : Struct BVal → Time → Prop) (ho : OpTreeOKUnder p R)
    (ts : List Tx) (tx : Tx) (hw : Within p (ts ++ [tx])) (hr : R (treeRun p ts) ts.length) (z : NodeId) (top : Top)
    (hz : lastTop (view (treeSpec p) (treeRun p ts) ts.length) = some z)
    (htop : topOf p (ctxOf p ts).view z = .ok top)
    (hT : TreeAt p (treeRun p ts) ts.length) (pre : List Tree.Op) (post : List Tree.Op)
    (hsplit : tx.ops = pre ++ post) (r : List Bool) (w : W)
    (hpre : (pre.mapM putKv) (ctxOf p ts) (wInit tx top) = .ok (r, w)) :
    WriterTreeOK p (treeRun p ts) (ts.length + 1) w :=
  writerTreeOK_foldU p R ho ts tx hw hr z top hz htop pre [] post (by simp [hsplit]) [] (wInit tx top)
    (by simp only [List.mapM_nil, pure, ReaderT.pure, StateT.pure, Except.pure])
    (writerTreeOK_init p ts tx z top hz htop hT) r w hpre

/-- As `SIS.Tree.treeAt_stepU`, for the runs of `N.Within`. -/
theorem treeAt_stepU (p : Params) (R : Struct BVal → Time → Prop) (ho : OpTreeOKUnder p R)
    (ts : List Tx) (tx : Tx) (hw : Within p (ts ++ [tx])) (hr : R (treeRun p ts) ts.length) (hT : TreeAt p (treeRun p ts) ts.length)
    (hl : CommitLiftAt p ts tx) : TreeAt p (treeRun p (ts ++ [tx])) (ts.length + 1) := by
  obtain ⟨noops, w, hrun⟩ := within_last_ok p ts tx hw
  obtain ⟨z, top, hz, htop, hops⟩ := runOps_ok p _ _ _ _ noops w hrun
  have hW := writerTreeOK_reachedU p R ho ts tx hw hr z top hz htop hT tx.ops [] (by simp) noops w hops
  obtain ⟨hK, htaken, htopt⟩ := hl noops w hrun
  have hR := rootAt_commit_of_lift p ts tx hw noops w hrun hK htaken htopt
  exact ⟨w.top.rootKey, hR, treeOK_congr_look _ _ _ _ (funext hK).symm hW⟩

set_option maxHeartbeats 800000 in
/-- As `SIS.Tree.invOK_snocR`, for the runs of `N.Within`. -/
theorem invOK_snocR (p : Params) (R : Struct BVal → Time → Prop)
    (hRL : ∀ P t, R P t → RunLinksOK p P t) (hRT : ∀ P t, R P t → TreeAt p P t)
    (hRI : ∀ P t, R P t → InvOK p P t)
    (hT : OpCaseOK p R (QTree p) AnyOp) (hPI : OpCaseOK p R (QPutInv p) AnyOp)
    (hO : OpCaseOK p R (QRange p) AnyOp) (hLv : OpCaseOK p R (QLive p) AnyOp)
    (ts : List Tx) (tx : Tx) (hw : Within p (ts ++ [tx])) (hr : R (treeRun p ts) ts.length)
    (hL' : RunLinksOK p (treeRun p (ts ++ [tx])) (ts.length + 1))
    (hT' : TreeAt p (treeRun p (ts ++ [tx])) (ts.length + 1))
    (hK' : KindsAllOK p (treeRun p (ts ++ [tx])))
    (hA' : HeightAllOK p (treeRun p (ts ++ [tx])) (ts.length + 1))
    (hS' : SizeOK p (treeRun p (ts ++ [tx])))
    (hLA' : LeftAllOK p (treeRun p (ts ++ [tx])))
    (hD' : DeadAllOK p (treeRun p (ts ++ [tx]))) :
    InvOK p (treeRun p (ts ++ [tx])) (ts.length + 1) := by
  obtain ⟨noops, w, hrun⟩ := within_last_ok p ts tx hw
  obtain ⟨z, top, hz, htop, hops⟩ := runOps_ok p _ _ _ _ noops w hrun
  have hcl : CommitLiftAt p ts tx := commitLiftAt_of_links p ts tx hw (hRL _ _ hr)
  have hRO := (joint_reached p R hRL hT hPI hO ts tx hw hr (hRT _ _ hr) (hRI _ _ hr) z top hz
    htop tx.ops [] (by simp) noops w hops).2
  have hLC := live_reached p R hRL hT hPI hO hLv ts tx hw hr (hRT _ _ hr) (hRI _ _ hr) z top
    hz htop tx.ops [] (by simp) noops w hops
  obtain ⟨hNE, hRT, hF⟩ := liveCounts_commit p ts tx hw hcl noops w hrun hLC
  have hRA := rangeAtOK_commit p ts tx hw hcl noops w hrun hRO
  have hLM : LeftmostOK p (treeRun p (ts ++ [tx])) (ts ++ [tx]).length :=
    leftmostOK_of_leftAll p _ _ (treeRun_timesLE p _) hL'.2.1 hLA'
  have hlen : (ts ++ [tx]).length = ts.length + 1 := by simp
  rw [hlen] at hLM
  exact invOK_of_parts p _ _ (rootKeyOK_of_treeAt p _ _ hT') (keyNodesOK_of_parts p _ hS' hL'.2.1 hL'.1 hD')
    hK' (heightLiveOK_of_all p _ _ hA' (ht_keyNodesAt_key p _ _)) hNE hLM hRT hF hRA

/-- As `SIS.Tree.opCaseOK_anti`, for the runs of `N.Within`. -/
theorem opCaseOK_anti (p : Params) (R R' : Struct BVal → Time → Prop) (h : ∀ P t, R P t → R' P t)
    (Q : List Tx → Op → W → W → Prop) (C : Ctx → View BVal → W → Op → Prop)
    (hC : OpCaseOK p R' Q C) : OpCaseOK p R Q C :=
  fun ts tx hw hr => hC ts tx hw (h _ _ hr)

/-- As `SIS.Tree.opTreeOKUnder_of_cases`, for the runs of `N.Within`. -/
theorem opTreeOKUnder_of_cases (p : Params) (R : Struct BVal → Time → Prop)
    (hRL : ∀ P t, R P t → RunLinksOK p P t) (hRT : ∀ P t, R P t → TreeAt p P t)
    (hRI : ∀ P t, R P t → InvOK p P t)
    (hT : OpCaseOK p R (QTree p) AnyOp) (hP : OpCaseOK p R (QPutInv p) AnyOp)
    (hO : OpCaseOK p R (QRange p) AnyOp) : OpTreeOKUnder p R := by
  intro ts tx hw hr z top hz htop pre op post hsplit r w hpre _
  obtain ⟨hI, hRO⟩ := joint_reached p R hRL hT hP hO ts tx hw hr (hRT _ _ hr) (hRI _ _ hr) z top
    hz htop pre (op :: post) hsplit r w hpre
  exact hT ts tx hw hr z top hz htop pre op post hsplit r w hpre hI hRO trivial

/-- As `SIS.Tree.putInvStateOK_of_cases`, for the runs of `N.Within`. -/
theorem putInvStateOK_of_cases (p : Params) (R : Struct BVal → Time → Prop)
    (hRL : ∀ P t, R P t → RunLinksOK p P t) (hRT : ∀ P t, R P t → TreeAt p P t)
    (hRI : ∀ P t, R P t → InvOK p P t)
    (hT : OpCaseOK p R (QTree p) AnyOp) (hP : OpCaseOK p R (QPutInv p) AnyOp)
    (hO : OpCaseOK p R (QRange p) AnyOp) :
    StateOK p R (fun ts _ w => PutInv (ctxOf p ts) (viewOf (treeRun p ts)) w) :=
  fun ts tx hw hr z top hz htop pre post hsplit r w hpre =>
    (joint_reached p R hRL hT hP hO ts tx hw hr (hRT _ _ hr) (hRI _ _ hr) z top hz htop pre post
      hsplit r w hpre).1

/-- As `SIS.Tree.rangeStateOK_of_cases`, for the runs of `N.Within`. -/
theorem rangeStateOK_of_cases (p : Params) (R : Struct BVal → Time → Prop)
    (hRL : ∀ P t, R P t → RunLinksOK p P t) (hRT : ∀ P t, R P t → TreeAt p P t)
    (hRI : ∀ P t, R P t → InvOK p P t)
    (hT : OpCaseOK p R (QTree p) AnyOp) (hP : OpCaseOK p R (QPutInv p) AnyOp)
    (hO : OpCaseOK p R (QRange p) AnyOp) :
    StateOK p R (fun ts _ w =>
      RangeOrder (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) w.top.rootKey) :=
  fun ts tx hw hr z top hz htop pre post hsplit r w hpre =>
    (joint_reached p R hRL hT hP hO ts tx hw hr (hRT _ _ hr) (hRI _ _ hr) z top hz htop pre post
      hsplit r w hpre).2

/-- As `SIS.Tree.opGetCaseOK_of'`, for the runs of `N.Within`. -/
theorem opGetCaseOK_of' (p : Params) (R : Struct BVal → Time → Prop)
    (P : Ctx → View BVal → W → Op → Prop) (h : OpGetCaseOK' p R P) (hfit : TxSegFitsOK p R) :
    OpGetCaseOK p R P := by
  intro ts tx hw hr z top hz htop pre op post hops r w hpre hI hRO hP
  exact h ts tx hw hr z top hz htop pre op post hops r w hpre hI hRO
    (hfit ts tx hw hr z top hz htop pre (op :: post) hops r w hpre) hP

/-- As `SIS.Tree.j2_reached`, for the runs of `N.Within`. -/
theorem j2_reached (p : Params) (R : Struct BVal → Time → Prop) (S : List Tx → Tx → W → Prop)
    (hO : OpJ2OK p R S)
    (ho : OpTreeOKUnder p R) (ts : List Tx) (tx : Tx) (hw : Within p (ts ++ [tx]))
    (hr : R (treeRun p ts) ts.length)
    (hT : TreeAt p (treeRun p ts) ts.length) (z : NodeId) (top : Top)
    (hz : lastTop (view (treeSpec p) (treeRun p ts) ts.length) = some z)
    (htop : topOf p (ctxOf p ts).view z = .ok top)
    (hS : ∀ pre post, tx.ops = pre ++ post → ∀ r w,
      (pre.mapM putKv) (ctxOf p ts) (wInit tx top) = .ok (r, w) → S ts tx w)
    (h0 : J2At p (treeRun p ts) (ts.length + 1) tx.base (wInit tx top)) :
    ∀ pre post, tx.ops = pre ++ post → ∀ r w,
      (pre.mapM putKv) (ctxOf p ts) (wInit tx top) = .ok (r, w) →
      J2At p (treeRun p ts) (ts.length + 1) tx.base w := by
  intro pre
  suffices hk : ∀ k, ∀ pre : List Op, pre.length = k → ∀ post, tx.ops = pre ++ post → ∀ r w,
      (pre.mapM putKv) (ctxOf p ts) (wInit tx top) = .ok (r, w) →
      J2At p (treeRun p ts) (ts.length + 1) tx.base w
    from hk pre.length pre rfl
  intro k
  induction k with
  | zero =>
    intro pre hl _ _ r w h
    have hnil : pre = [] := List.eq_nil_of_length_eq_zero hl
    subst hnil
    simp only [List.mapM_nil, pure, ReaderT.pure, StateT.pure, Except.pure, Except.ok.injEq,
      Prod.mk.injEq] at h
    rw [← h.2]
    exact h0
  | succ k ih =>
    intro pre hl post hsplit r w h
    rcases List.eq_nil_or_concat pre with hnil | ⟨pre', op, hpre⟩
    · subst hnil; simp at hl
    · rw [List.concat_eq_append] at hpre
      subst hpre
      have hl' : pre'.length = k := by simp at hl; omega
      have h0 := h
      rw [List.mapM_append] at h
      simp only [List.mapM_cons, List.mapM_nil, bind, ReaderT.bind, StateT.bind, Except.bind] at h
      cases h1 : (pre'.mapM putKv) (ctxOf p ts) (wInit tx top) with
      | error e => rw [h1] at h; cases h
      | ok rw1 =>
        rcases rw1 with ⟨r1, w1⟩
        rw [h1] at h
        simp only at h
        cases h2 : putKv op (ctxOf p ts) w1 with
        | error e => rw [h2] at h; cases h
        | ok aw =>
          rcases aw with ⟨a, w2⟩
          rw [h2] at h
          simp only [pure, ReaderT.pure, StateT.pure, Except.pure, Except.ok.injEq,
            Prod.mk.injEq] at h
          have hsplit' : tx.ops = pre' ++ op :: post := by rw [hsplit]; simp
          have hI1 := ih pre' hl' (op :: post) hsplit' r1 w1 h1
          have hT1 := writerTreeOK_reachedU p R ho ts tx hw hr z top hz htop hT pre' (op :: post)
            hsplit' r1 w1 h1
          have hT2 := writerTreeOK_reachedU p R ho ts tx hw hr z top hz htop hT (pre' ++ [op]) post
            (by rw [hsplit]) r w h0
          rw [← h.2] at hT2 ⊢
          exact hO ts tx hw hr z top hz htop pre' op post hsplit' r1 w1 h1 hT1
            (hS pre' (op :: post) hsplit' r1 w1 h1) hI1 a w2 h2 hT2

/-- As `SIS.Tree.takeBackOKUnder_of_opsJ2`, for the runs of `N.Within`. -/
theorem takeBackOKUnder_of_opsJ2 (p : Params) (R : Struct BVal → Time → Prop)
    (hRL : ∀ P t, R P t → RunLinksOK p P t) (hRT : ∀ P t, R P t → TreeAt p P t)
    (ho : OpTreeOKUnder p R) (S : List Tx → Tx → W → Prop) (hO : OpJ2OK p R S)
    (hS : StateOK p R S) (hSRF : ∀ ts tx w, S ts tx w → ReachedFree p (treeRun p ts) (ts.length + 1) w)
    (hB : BaseStartOK p R) (hTV : TakenNotValOK p R) : TakeBackOKUnder p R := by
  intro ts tx hw hr noops w hrun
  obtain ⟨z, top, hz, htop, hops⟩ := runOps_ok p _ _ _ _ noops w hrun
  have hJ := j2_reached p R S hO ho ts tx hw hr (hRT _ _ hr) z top hz htop
    (hS ts tx hw hr z top hz htop) (takeInvJ_init p ts tx hw (hRL _ _ hr) top (hB ts tx hw hr)).2
    tx.ops [] (by simp) noops w hops
  have hI : TakeInvJ p (treeRun p ts) (ts.length + 1) tx.base w :=
    ⟨hSRF ts tx w (hS ts tx hw hr z top hz htop tx.ops [] (by simp) noops w hops), hJ⟩
  have hl := commitLiftAt_of_links p ts tx hw (hRL _ _ hr) noops w hrun
  have hfresh : ∀ q ∈ treeRun p ts, q.1 < tx.base := by
    have h := (hw.w.2 ts.length (by simp)).1
    have hj : (ts ++ [tx])[ts.length]'(by simp) = tx := by simp
    have ht : (ts ++ [tx]).take ts.length = ts := by simp
    rw [hj, ht] at h
    exact h
  have hU : (w.nodes.map (·.1)).Nodup := execW_cacheUnique p tx (ts.length + 1) _ noops w
    (viewIdsBelow_view p (treeRun p ts) ts.length tx.base hfresh) hrun
  obtain ⟨hP, _, hN⟩ := hRL _ _ hr
  have htimes : StructTimesLE (treeRun p ts) (ts.length + 1 - 1) := treeRun_timesLE p ts
  have hvl : ViewLinksOK tx.base p (view (treeSpec p) (treeRun p ts) (ts.length + 1 - 1)) :=
    viewLinksOK_of p _ _ tx.base hfresh htimes hP hN
  have hvg := viewGood_of p (treeRun p ts) (ts.length + 1) tx.base (by omega) hfresh htimes hvl
  have he : execW p tx (ts.length + 1) (view (treeSpec p) (treeRun p ts) (ts.length + 1 - 1)) =
      .ok (noops, w) := hrun
  have hG := execW_good p tx (ts.length + 1) _ noops w hvg he
  have hDT := deadTakenLive_of_deadLive p (treeRun p ts) (ts.length + 1) tx.base w hI.2.2.1 hU hl.2.1
    (hTV ts tx hw hr noops w hrun)
  exact takeBackEnd_of_invT p (treeRun p ts) tx.base _ w hvg hG ⟨hI.1, hI.2.1⟩ hDT hl.2.1 hU

/-- As `SIS.Tree.runTree_jointJ2`, for the runs of `N.Within`. -/
theorem runTree_jointJ2 (p : Params) (hM : 2 ≤ p.M) (Q : Struct BVal → Time → Prop)
    (hQ0 : Q (initStruct p) 0)
    (hQs : ∀ ts tx, Within p (ts ++ [tx]) → RunTreeQ p Q (treeRun p ts) ts.length →
      RunLinksOK p (treeRun p (ts ++ [tx])) (ts.length + 1) →
      TreeAt p (treeRun p (ts ++ [tx])) (ts.length + 1) →
      Q (treeRun p (ts ++ [tx])) (ts.length + 1))
    (ho : OpTreeOKUnder p (RunTreeQ p Q)) (S : List Tx → Tx → W → Prop) (hO : OpJ2OK p (RunTreeQ p Q) S)
    (hS : StateOK p (RunTreeQ p Q) S)
    (hSRF : ∀ ts tx w, S ts tx w → ReachedFree p (treeRun p ts) (ts.length + 1) w) (hB : BaseStartOK p (RunTreeQ p Q)) (hTV : TakenNotValOK p (RunTreeQ p Q)) :
    ∀ ts, Within p ts → RunTreeQ p Q (treeRun p ts) ts.length := by
  have hTB : TakeBackOKUnder p (RunTreeQ p Q) :=
    takeBackOKUnder_of_opsJ2 p _ (fun _ _ h => h.1) (fun _ _ h => h.2.1) ho S hO hS hSRF hB hTV
  intro ts hw
  have hk : ∀ n, n ≤ ts.length → RunTreeQ p Q (treeRun p (ts.take n)) n := by
    intro n
    induction n with
    | zero =>
      intro _
      have h0 : treeRun p (ts.take 0) = initStruct p := by simp [treeRun]
      rw [h0]
      exact ⟨runLinksOK_init p, treeAt_init p, hQ0⟩
    | succ n ih =>
      intro hn
      have hlt : n < ts.length := by omega
      have htake : ts.take (n + 1) = ts.take n ++ [ts[n]] := List.take_succ_eq_append_getElem hlt
      have hlen : (ts.take n).length = n := by
        simp only [List.length_take]; omega
      have hwn : Within p (ts.take n ++ [ts[n]]) := by
        rw [← htake]; exact within_take p ts hw (n + 1)
      have hr : RunTreeQ p Q (treeRun p (ts.take n)) (ts.take n).length := by
        rw [hlen]; exact ih (by omega)
      have hL := runLinksOK_step p hM (ts.take n) ts[n] hwn hr.1
        (fun noops w hrun => hTB (ts.take n) ts[n] hwn hr noops w hrun)
      have hT := treeAt_stepU p _ ho (ts.take n) ts[n] hwn hr hr.2.1
        (commitLiftAt_of_links p (ts.take n) ts[n] hwn hr.1)
      have hQ := hQs (ts.take n) ts[n] hwn hr hL hT
      rw [htake]
      rw [hlen] at hL hT hQ
      exact ⟨hL, hT, hQ⟩
  have h := hk ts.length (Nat.le_refl _)
  rwa [List.take_length] at h

/-- As `SIS.Tree.innerChildren_reached`, for the runs of `N.Within`. -/
theorem innerChildren_reached (p : Params) (hM : 2 ≤ p.M)
    (hP : ∀ ts, Within p ts → PointersOK (treeRun p ts))
    (ts : List Tx) (tx : Tx) (hw : Within p (ts ++ [tx])) (top : Top)
    (pre post : List Op) (hsplit : tx.ops = pre ++ post) (r : List Bool) (w : W)
    (h : (pre.mapM putKv) (ctxOf p ts) (wInit tx top) = .ok (r, w))
    (hun : ∀ x, TReach (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) w.top.rootKey x →
      w.taken.contains x = false) :
    ∀ y yn cc z, TReach (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) w.top.rootKey y →
      wNode p (viewOf (treeRun p ts)) w y = some yn → yn.leaf = false →
      (cc, z) ∈ yn.liveAt (ts.length + 1) →
      ∃ m, wNode p (viewOf (treeRun p ts)) w z = some m := by
  have hwts : Within p ts := by
    have := within_take p (ts ++ [tx]) hw ts.length
    simpa using this
  have hfresh : ∀ q ∈ treeRun p ts, q.1 < tx.base := by
    have := (hw.w.2 ts.length (by simp)).1
    simpa using this
  have hwf : tx.wf = true := (hw.w.1 tx (by simp)).2
  have hkeys : ∀ op ∈ pre, keyWf op.key = true := by
    intro op hop
    unfold Tx.wf at hwf
    exact List.all_eq_true.mp hwf op (by rw [hsplit]; exact List.mem_append_left _ hop)
  have hK := treeRun_kindsAllOK p hM hP ts hwts
  have hkd := kd_ops (kindOracleOf p (treeRun p ts)) tx.base (appendFrameOK tx.base) pre
    (ctxOf p ts) (wInit tx top)
    (viewIdsBelow_rootless _ _ (viewIdsBelow_view p (treeRun p ts) ts.length tx.base hfresh))
    (viewKinds_of p (treeRun p ts) ts.length tx.base hfresh (treeRun_timesLE p ts) (hP ts hwts) hK)
    (book_start _ _ top) (kdInv_start _ _ top) hM hkeys r w h
  exact innerChildren_of_kinds p (treeRun p ts) tx.base (ctxOf p ts) w rfl hK (hP ts hwts) hkd.1
    hkd.2.1.cache hun

/-- As `SIS.Tree.opJ2OK_of_cases`, for the runs of `N.Within`. -/
theorem opJ2OK_of_cases (p : Params) (R : Struct BVal → Time → Prop) (S : List Tx → Tx → W → Prop)
    (c1 : OpJ2CaseOK p R S PutLeafRoomCase) (c2 : OpJ2CaseOK p R S PutLeafFullCase)
    (c3 : OpJ2CaseOK p R S PutNewSegCase) (c4 : OpJ2CaseOK p R S DelMergeCase)
    (c5 : OpJ2CaseOK p R S DelNoLeafCase) (c6 : OpJ2CaseOK p R S DelNoopCase)
    (c7 : OpJ2CaseOK p R S DelEmptyCase) (c8 : OpJ2CaseOK p R S DelRoomCase)
    (c9 : OpJ2CaseOK p R S DelFullCase) : OpJ2OK p R S := by
  intro ts tx hw hr z top hz htop pre op post hsplit r w hpre hT hS hJ
  rcases opCase_cover (ctxOf p ts) (viewOf (treeRun p ts)) w op with h | h | h | h | h | h | h | h | h
  · exact c1 ts tx hw hr z top hz htop pre op post hsplit r w hpre hT hS hJ h
  · exact c2 ts tx hw hr z top hz htop pre op post hsplit r w hpre hT hS hJ h
  · exact c3 ts tx hw hr z top hz htop pre op post hsplit r w hpre hT hS hJ h
  · exact c4 ts tx hw hr z top hz htop pre op post hsplit r w hpre hT hS hJ h
  · exact c5 ts tx hw hr z top hz htop pre op post hsplit r w hpre hT hS hJ h
  · exact c6 ts tx hw hr z top hz htop pre op post hsplit r w hpre hT hS hJ h
  · exact c7 ts tx hw hr z top hz htop pre op post hsplit r w hpre hT hS hJ h
  · exact c8 ts tx hw hr z top hz htop pre op post hsplit r w hpre hT hS hJ h
  · exact c9 ts tx hw hr z top hz htop pre op post hsplit r w hpre hT hS hJ h

/-- As `SIS.Tree.opJ2Case_putNewSeg`, for the runs of `N.Within`. -/
theorem opJ2Case_putNewSeg (p : Params) (R : Struct BVal → Time → Prop) (S : List Tx → Tx → W → Prop)
    (hM : 2 ≤ p.M)
    (hSI : ∀ ts tx w, S ts tx w → PutInv (ctxOf p ts) (viewOf (treeRun p ts)) w)
    (hSB : ∀ ts tx w, S ts tx w → tx.base ≤ w.next)
    (hfull : OpJ2CaseOK p R S PutNewSegFullCase) : OpJ2CaseOK p R S PutNewSegCase := by
  intro ts tx hw hr z top hz htop ops op post hops r w hpre hT hS hJ hP
  have hI := hSI ts tx w hS
  obtain ⟨key, h, hop, hno⟩ := hP
  have hkey : keyWf key = true := by
    have := within_op_keyWf p ts tx hw ops _ post hops
    rw [hop] at this; exact this
  have hne : key ≠ [] := by intro h; subst h; simp [keyWf] at hkey
  have hno' : NoLeafFrom (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) p.fuel key
      w.top.rootKey := by
    rintro ⟨pre, cv, rk, L, n, hsplit, hrk, hvis, hn, hnl⟩
    exact hno ⟨pre, cv, L, n, hsplit, rk, hrk, hvis, hn, hnl⟩
  by_cases hseg : NewSegFrom (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) p.fuel key
      w.top.rootKey
  · obtain ⟨pre, c0, tail, rk0, L, n, hk, htail, hrk0, hL, hn, hnl, hnone⟩ := hseg
    subst hk
    by_cases hroom : n.size + 1 < p.M
    · subst hop
      have hone : ∀ L' n', (L', c0) ∈ eqVisits (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1)
          c0 p.fuel rk0 → wNode p (viewOf (treeRun p ts)) w L' = some n' → n'.leaf = true →
          L' = L ∧ n' = n := by
        intro L' n' hL' hn' hnl'
        have he := eqVisits_leaf_unique _ _ _ _ _ _ _ _ _ hL' hL hn' hnl' hn hnl
        subst he
        rw [hn] at hn'
        exact ⟨rfl, (Option.some.inj hn').symm⟩
      refine writerWP_mono (writerWP_put_newSegs_j2 (ctxOf p ts) _ (viewCoherent_ctxOf p ts) pre c0 h
        tail htail rk0 tx.base w hM (by simp [ctxOf]) hrk0 (hI.pathUntaken _) hI.ids hI.fresh
        (fun L' n' hL' hn' hnl' => by
          obtain ⟨_, he2⟩ := hone L' n' hL' hn' hnl'
          rw [he2]
          exact ⟨hI.wf L n hn, hI.times L n hn, hnone, hroom⟩)
        hJ (hSB ts tx w hS) (fun L' hL' => reachS_tReach _ _ _ _ (fromVisits_reach _ _ _ _
          (fun x xn _ hn => hI.wf x xn hn) (pre ++ c0 :: tail) _ L' c0 ReachS.root
          (fromVisits_append_gen _ _ _ c0 tail pre _ rk0 hrk0 _ hL')))) ?_
      intro _ w' h' _
      exact h'
    · exact hfull ts tx hw hr z top hz htop ops op post hops r w hpre hT hS hJ
        ⟨pre, c0, tail, h, rk0, L, n, hop, ⟨htail, hrk0, hL, hn, hnl, hnone⟩, hroom⟩
  · subst hop
    unfold putKv pathClear findRoot pathAdd
    wpSimplify
    generalize hw2 : ({ ({ w with path := [] } : W) with
      path := ([] : List (Option Nat × NodeId)) ++ [(none, w.top.rootKey)] } : W) = w2
    have hr02 : ReadsAs (ctxOf p ts).p (viewOf (treeRun p ts)) w w2 := by
      subst hw2; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
    refine writerWP_mono (writerWP_putSegs_put_fail (ctxOf p ts) _ (viewCoherent_ctxOf p ts) key h
      key w.top.rootKey w2 hne ?_ ?_ ?_) (fun _ _ hf => hf.elim)
    · intro q hq
      rw [hr02.2.2.1]
      rw [hr02.1] at hq
      exact hI.pathUntaken key q hq
    · rw [hr02.1]; exact hno'
    · rw [hr02.1]; exact hseg

/-- As `SIS.Tree.delStepsOK_of_cases`, for the runs of `N.Within`. -/
theorem delStepsOK_of_cases (p : Params) (R : Struct BVal → Time → Prop)
    (c5 : DelStepsCaseOK p R DelNoLeafM) (c6 : DelStepsCaseOK p R DelNoopM)
    (c7 : DelStepsCaseOK p R DelEmptyM) (c8 : DelStepsCaseOK p R DelRoomM)
    (c9 : DelStepsCaseOK p R DelFullM) : DelStepsOK p R := by
  intro ts tx hw hr z top hz htop pre op post hops r w hpre hI hRO hF key hop hm hA hMU hCR
  rcases delMerge_cover (ctxOf p ts) (viewOf (treeRun p ts)) w key hm with h | h | h | h | h
  · exact c5 ts tx hw hr z top hz htop pre op post hops r w hpre hI hRO hF key hop (hop ▸ h) hA hMU hCR
  · exact c6 ts tx hw hr z top hz htop pre op post hops r w hpre hI hRO hF key hop (hop ▸ h) hA hMU hCR
  · exact c7 ts tx hw hr z top hz htop pre op post hops r w hpre hI hRO hF key hop (hop ▸ h) hA hMU hCR
  · exact c8 ts tx hw hr z top hz htop pre op post hops r w hpre hI hRO hF key hop (hop ▸ h) hA hMU hCR
  · exact c9 ts tx hw hr z top hz htop pre op post hops r w hpre hI hRO hF key hop (hop ▸ h) hA hMU hCR

/-- As `SIS.Tree.kd_context`, for the runs of `N.Within`. -/
theorem kd_context (p : Params) (hM : 2 ≤ p.M) (hP : ∀ ts, Within p ts → PointersOK (treeRun p ts))
    (ts : List Tx) (tx : Tx) (hw : Within p (ts ++ [tx])) (top : Top) (pre post : List Op)
    (hsplit : tx.ops = pre ++ post) (r : List Bool) (w : W)
    (h : (pre.mapM putKv) (ctxOf p ts) (wInit tx top) = .ok (r, w)) :
    ViewIdsBelow tx.base (ctxOf p ts).view ∧
      ViewKinds (kindOracleOf p (treeRun p ts)) tx.base (ctxOf p ts) ∧
      Book tx.base (ctxOf p ts) w ∧ KdInv (kindOracleOf p (treeRun p ts)) tx.base w := by
  have hwts : Within p ts := by
    have := within_take p (ts ++ [tx]) hw ts.length
    simpa using this
  have hfresh : ∀ q ∈ treeRun p ts, q.1 < tx.base := by
    have := (hw.w.2 ts.length (by simp)).1
    simpa using this
  have hwf : tx.wf = true := (hw.w.1 tx (by simp)).2
  have hkeys : ∀ op ∈ pre, keyWf op.key = true := by
    intro op hop
    unfold Tx.wf at hwf
    exact List.all_eq_true.mp hwf op (by rw [hsplit]; exact List.mem_append_left _ hop)
  have hK := treeRun_kindsAllOK p hM hP ts hwts
  have hv : ViewIdsBelow tx.base (ctxOf p ts).view :=
    viewIdsBelow_rootless _ _ (viewIdsBelow_view p (treeRun p ts) ts.length tx.base hfresh)
  have hk : ViewKinds (kindOracleOf p (treeRun p ts)) tx.base (ctxOf p ts) :=
    viewKinds_of p (treeRun p ts) ts.length tx.base hfresh (treeRun_timesLE p ts) (hP ts hwts) hK
  have hkd := kd_ops (kindOracleOf p (treeRun p ts)) tx.base (appendFrameOK tx.base) pre
    (ctxOf p ts) (wInit tx top) hv hk (book_start _ _ top) (kdInv_start _ _ top) hM hkeys r w h
  exact ⟨hv, hk, hkd.1, hkd.2.1⟩

/-- As `SIS.Tree.delStepsCaseOK_room`, for the runs of `N.Within`. -/
theorem delStepsCaseOK_room (p : Params) (R : Struct BVal → Time → Prop) (hM : 2 ≤ p.M)
    (hRL : ∀ P t, R P t → RunLinksOK p P t)
    (hP : ∀ ts, Within p ts → PointersOK (treeRun p ts)) :
    DelStepsCaseOK p R DelRoomM := by
  intro ts tx hw hr z top _ htop ops op post hops r w hpre hI hRO hF key hop hPc hA _ _
  obtain ⟨pre, cv, L0, n0, hop', _, hK, hne0, hkeep0, hroom0⟩ := hPc
  subst hop'
  cases hop
  have hkey : keyWf (pre ++ [cv]) = true := within_op_keyWf p ts tx hw ops _ post hops
  obtain ⟨rk, hrk, hn0⟩ := keyLeaf_rk hK
  have hB := putBase_of_run p ts tx hw (hRL _ _ hr)
  have hbook := putBook_reached p ts tx hw (hRL _ _ hr) z top htop ops r w hpre
  have hICE := innerChildren_reached p hM hP ts tx hw top ops (.del (pre ++ [cv]) :: post) hops r w hpre
    (fun x hx => hI.untaken x (tReach_reachS _ _ _ _ hx))
  obtain ⟨hv, hk, hb0, hi0⟩ := kd_context p hM hP ts tx hw top ops (.del (pre ++ [cv]) :: post) hops r w hpre
  have hJ0 : KdJ (ctxOf p ts) tx.base top (kindOracleOf p (treeRun p ts)) tx.base w := ⟨hbook, hb0, hi0⟩
  refine writerWP_del_toLeafMK (ctxOf p ts) _ (viewCoherent_ctxOf p ts) pre cv rk w _ hJ0
    (fun s f x v hJ hx => kdJ_descendLte _ _ tx.base top hB _ tx.base hv hk s f x v hJ hx)
    (fun s x L n v hJ hL hlk hkm => kdJ_pathAdd _ _ tx.base top hB _ tx.base hv s x L n v hJ hL hlk hkm)
    (kdJ_start _ _ tx.base top hB _ tx.base hv w hJ0) hrk (hI.pathUntaken _) hI.wf _ ?_ ?_
  · intro v hv'
    unfold fresh
    wpSimplify
    exact hv'
  · intro L n P w3 hL hn hnl hr03 hJ3 hlk3 hp3' _ hXD _
    obtain ⟨hwf, htimes, hne, hkeep, hroomD⟩ := keyLeaf_all hK hrk
      (fun m => klongsWf m.ks = true ∧ (∀ s, Klong.time s ∈ m.ks → s ≤ (ctxOf p ts).i) ∧
        bitsUnion m.lastBitmap (m.bitsOf cv) ≠ m.lastBitmap ∧
        m.allKeysIn (bitsUnion m.lastBitmap (m.bitsOf cv)) = false ∧ DelRoom (ctxOf p ts) cv m)
      ⟨hI.wf L0 n0 hn0, hI.times L0 n0 hn0, hne0, hkeep0, hroom0⟩ L n hL hn hnl
    have hLt : w.taken.contains L = false :=
      hI.pathUntaken _ (L, cv) (fromVisits_append _ _ _ pre cv _ rk hrk _ hL)
    obtain ⟨a, hpx⟩ := path_last_of_toLeaf w w3 P L hp3' hXD
    refine writerWP_deleteUpward_full (ctxOf p ts) L n P.length cv (pre ++ [cv]) w3 hlk3 hne hkeep
      (fun v => DelInv (ctxOf p ts) (viewOf (treeRun p ts)) w (pre ++ [cv]) (p.fuel + 1)
        (kindOracleOf p (treeRun p ts)) tx.base v) _ ?_ ?_
    · refine writerWP_mono (writerWP_and (writerWP_and
        (writerWP_appendDeleteKlong_room_exactD L _ cv n _ _ hlk3 htimes hwf hne hroomD)
        (putBook_appendDeleteKlong L _ cv _ _ tx.base top hB _ hJ3.1))
        (kd_appendDeleteKlong _ tx.base L P.length cv _ w3 hv hk hJ3.2.1 hJ3.2.2 a hpx)) ?_
      rintro _ v ⟨⟨⟨h1, h2, h3, _, _, _, h7⟩, hbv⟩, hkv⟩
      exact ⟨delInvF_after_bitmap (ctxOf p ts) _ tx.base top hB w w3 v pre cv rk L n hI hRO hICE hF
        hkey hrk hL hn hnl hr03 hLt h1 h2 h3 h7 hbv, hkv.1, hkv.2.1⟩
    · intro g h v hv'
      refine writerWP_mono (hA g h v hv') ?_
      intro _ v' hv'' hFv' key' hk'
      have := runGet_of_delInvF p ts w v' (pre ++ [cv]) hv''.1 hI hF hFv' key' hk'
      simpa [Op.key, Op.value] using this

/-- As `SIS.Tree.delStepsCaseOK_emptyRoom`, for the runs of `N.Within`. -/
theorem delStepsCaseOK_emptyRoom (p : Params) (R : Struct BVal → Time → Prop) (hM : 2 ≤ p.M)
    (hRL : ∀ P t, R P t → RunLinksOK p P t)
    (hP : ∀ ts, Within p ts → PointersOK (treeRun p ts)) :
    DelStepsCaseOK p R DelEmptyRoomM := by
  intro ts tx hw hr z top _ htop ops op post hops r w hpre hI hRO hF key hop hPc hA hMU hCR
  obtain ⟨pre, cv, L0, n0, hop', hm, hK, hne0, hall0, hup0⟩ := hPc
  subst hop'
  cases hop
  have hkey : keyWf (pre ++ [cv]) = true := within_op_keyWf p ts tx hw ops _ post hops
  obtain ⟨rk, hrk, _⟩ := keyLeaf_rk hK
  have hB := putBase_of_run p ts tx hw (hRL _ _ hr)
  have hbook := putBook_reached p ts tx hw (hRL _ _ hr) z top htop ops r w hpre
  have hICE := innerChildren_reached p hM hP ts tx hw top ops (.del (pre ++ [cv]) :: post) hops r w hpre
    (fun x hx => hI.untaken x (tReach_reachS _ _ _ _ hx))
  obtain ⟨hv, hk, hb0, hi0⟩ := kd_context p hM hP ts tx hw top ops (.del (pre ++ [cv]) :: post) hops r w hpre
  refine writerWP_del_emptyRoomMK (ctxOf p ts) _ (viewCoherent_ctxOf p ts) pre cv rk w tx.base top hB hbook
    _ tx.base hv hk hb0 hi0 hI hRO hF hICE hkey hrk (keyLeaf_all2 hK hrk _ ⟨hne0, hall0, hup0⟩) hm
    (by simp [ctxOf]) hA hMU hCR _ (fun v hv' => by unfold fresh; wpSimplify; exact hv') ?_
  intro v hv' hFv key' hk'
  have := runGet_of_delInvF p ts w v (pre ++ [cv]) hv'.1 hI hF hFv key' hk'
  simpa [Op.key, Op.value] using this

/-- As `SIS.Tree.delStepsCaseOK_or`, for the runs of `N.Within`. -/
theorem delStepsCaseOK_or (p : Params) (R : Struct BVal → Time → Prop)
    (P P1 P2 : Ctx → View BVal → W → Op → Prop)
    (hs : ∀ c base w op, P c base w op → P1 c base w op ∨ P2 c base w op)
    (h1 : DelStepsCaseOK p R P1) (h2 : DelStepsCaseOK p R P2) : DelStepsCaseOK p R P := by
  intro ts tx hw hr z top hz htop pre op post hops r w hpre hI hRO hF key hop hPc hA hMU hCR
  rcases hs _ _ _ _ hPc with h | h
  · exact h1 ts tx hw hr z top hz htop pre op post hops r w hpre hI hRO hF key hop h hA hMU hCR
  · exact h2 ts tx hw hr z top hz htop pre op post hops r w hpre hI hRO hF key hop h hA hMU hCR

set_option maxHeartbeats 1600000 in
/-- As `SIS.Tree.delStepsCaseOK_emptyRoot`, for the runs of `N.Within`. -/
theorem delStepsCaseOK_emptyRoot (p : Params) (R : Struct BVal → Time → Prop) (hM : 2 ≤ p.M)
    (hsa2 : 2 ≤ p.splitAbove)
    (hRL : ∀ P t, R P t → RunLinksOK p P t)
    (hP : ∀ ts, Within p ts → PointersOK (treeRun p ts)) :
    DelStepsCaseOK p R DelEmptyRootM := by
  intro ts tx hw hr z top _ htop ops op post hops r w hpre hI hRO hF key hop hPc _ _ _
  obtain ⟨pre, cv, L0, n0, hop', _, hK, hne0, hall0, hroot0⟩ := hPc
  subst hop'
  cases hop
  have hkey : keyWf (pre ++ [cv]) = true := within_op_keyWf p ts tx hw ops _ post hops
  obtain ⟨rk, hrk, hn0⟩ := keyLeaf_rk hK
  have hB := putBase_of_run p ts tx hw (hRL _ _ hr)
  have hbook := putBook_reached p ts tx hw (hRL _ _ hr) z top htop ops r w hpre
  have hICE := innerChildren_reached p hM hP ts tx hw top ops (.del (pre ++ [cv]) :: post) hops r w hpre
    (fun x hx => hI.untaken x (tReach_reachS _ _ _ _ hx))
  obtain ⟨hv, hk, hb0, hi0⟩ := kd_context p hM hP ts tx hw top ops (.del (pre ++ [cv]) :: post) hops r w hpre
  have hJ0 : KdJ (ctxOf p ts) tx.base top (kindOracleOf p (treeRun p ts)) tx.base w := ⟨hbook, hb0, hi0⟩
  have hfuel : 1 ≤ p.fuel := by unfold Params.fuel; omega
  refine writerWP_del_toLeafMK (ctxOf p ts) _ (viewCoherent_ctxOf p ts) pre cv rk w _ hJ0
    (fun s f x v hJ hx => kdJ_descendLte _ _ tx.base top hB _ tx.base hv hk s f x v hJ hx)
    (fun s x L n v hJ hL hlk hkm => kdJ_pathAdd _ _ tx.base top hB _ tx.base hv s x L n v hJ hL hlk hkm)
    (kdJ_start _ _ tx.base top hB _ tx.base hv w hJ0) hrk (hI.pathUntaken _) hI.wf _ ?_ ?_
  · intro v hv'
    unfold fresh
    wpSimplify
    exact hv'
  · intro L n P w3 hL hn hnl hr03 hJ3 hlk3 hp3' hlinkP hXD hlkX
    obtain ⟨hne, hall, hLr⟩ := keyLeaf_all2 hK hrk
      (fun L' m => bitsUnion m.lastBitmap (m.bitsOf cv) ≠ m.lastBitmap ∧
        m.allKeysIn (bitsUnion m.lastBitmap (m.bitsOf cv)) = true ∧ L' = w.top.rootKey)
      ⟨hne0, hall0, hroot0⟩ L n hL hn hnl
    have hPnil := path_nil_of_root _ _ w hI.tree P hlinkP (by rw [hXD, hLr])
    subst hPnil
    have hp0 : (w3.path[0]?).map (·.2) = some L := by rw [hp3', hLr]; rfl
    refine writerWP_deleteUpward_rootEmpty (ctxOf p ts) L n cv (pre ++ [cv]) w3 hlk3 hp0 hnl hne hall _ ?_
    have hr03' : ReadsAs (ctxOf p ts).p (viewOf (treeRun p ts)) w
        ({ w3 with trail := "up.root-kept-empty" :: w3.trail } : W) :=
      ⟨hr03.1, hr03.2.1, hr03.2.2.1, hr03.2.2.2.1, hr03.2.2.2.2⟩
    have hb3' := putBook_note "up.root-kept-empty" (ctxOf p ts) _ tx.base top hB w3 hJ3.1
    have hn' : wNode p (viewOf (treeRun p ts)) w L = some n := hn
    have hLt : w.taken.contains L = false :=
      hI.pathUntaken _ (L, cv) (fromVisits_append _ _ _ pre cv _ rk hrk _ hL)
    by_cases hroom : DelRoom (ctxOf p ts) cv n
    · refine writerWP_mono (writerWP_and
        (writerWP_appendDeleteKlong_room_exactD L _ cv n _ _ hlk3 (hI.times L n hn) (hI.wf L n hn) hne hroom)
        (putBook_appendDeleteKlong L _ cv _ _ tx.base top hB _ hb3')) ?_
      rintro _ v ⟨⟨h1, h2, h3, _, _, _, h7⟩, hbv⟩
      have hD := delInvF_after_bitmap (ctxOf p ts) _ tx.base top hB w _ v pre cv rk L n hI hRO hICE hF
        hkey hrk hL hn hnl hr03' hLt h1 h2 h3 h7 hbv
      intro hFv key' hk'
      have := runGet_of_delInvF p ts w v (pre ++ [cv]) hD hI hF hFv key' hk'
      simpa [Op.key, Op.value] using this
    · have hPOK := pathOK_of_toLeaf (ctxOf p ts) _ w ({ w3 with trail := "up.root-kept-empty" :: w3.trail } : W)
        [] n hI hr03' hp3' hlinkP hlkX
      have hNn : (wNode (ctxOf p ts).p (viewOf (treeRun p ts)) w (nodeAt w.top.rootKey [] 0)).getD
          ⟨true, []⟩ = n := by
        rw [show nodeAt w.top.rootKey [] 0 = L from hXD, hn]; rfl
      have hI3 := putInv_of_readsAs _ _ w _ hI hr03'
      have hG3 := putInvG_of_book _ _ tx.base top _ hB hb3'
      have hinv := delFullRootStepOK_ctx p ts _ hI3 hG3 (by rw [hr03'.1, hr03'.2.1]; exact hRO)
        (by rw [hr03'.1, hr03'.2.1]; exact hF) hsa2 _ _ _ hPOK pre cv rk hkey
        (by rw [hr03'.1, hr03'.2.1]; exact hrk)
        (by show (nodeAt w.top.rootKey [] 0, cv) ∈ _; rw [show nodeAt w.top.rootKey [] 0 = L from hXD, hr03'.1]; exact hL)
        (by rw [hr03'.1, hr03'.2.1]; exact hI.keyUniq pre cv rk hkey hrk)
        (by rw [hNn]; exact hnl) (by rw [hNn]; exact hne) (by rw [hNn]; exact hroom)
      simp only [show nodeAt w.top.rootKey [] 0 = L from hXD] at hinv
      refine writerWP_mono (writerWP_and hinv (putBook_appendDeleteKlong L _ cv _ _ tx.base top hB _ hb3')) ?_
      rintro _ v ⟨⟨hTv, htv, _, _, hreachv, hRv, hreadv⟩, hbv⟩
      intro hFv key' hk'
      have hun : ∀ y, ReachS (wNode p (viewOf (treeRun p ts)) v) (ts.length + 1) v.top.rootKey y →
          v.taken.contains y = false := by
        intro y hy
        rw [htv]
        rcases hreachv y (reachS_tReach _ _ _ _ hy) with h | h
        · exact hI3.untaken y (tReach_reachS _ _ _ _ h)
        · cases h' : ({ w3 with trail := "up.root-kept-empty" :: w3.trail } : W).taken.contains y with
          | false => rfl
          | true => have := hI3.ids.2.2.1 y h'; dsimp only at this h; omega
      obtain ⟨hPv, _⟩ := putInv_after_step (ctxOf p ts) _ v tx.base top hB hbv hTv hun hRv
      have hr := hreadv (segFits_mono _ _ _ _ _ hFv (by simp only [ctxOf]; omega)) key' hk'
      have hwfv : ∀ x xn, ReachS (wNode p (viewOf (treeRun p ts)) v) (ts.length + 1) v.top.rootKey x →
          wNode p (viewOf (treeRun p ts)) v x = some xn → klongsWf xn.ks = true := fun x xn _ h => hPv.wf x xn h
      have hwfw : ∀ x xn, ReachS (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) w.top.rootKey x →
          wNode p (viewOf (treeRun p ts)) w x = some xn → klongsWf xn.ks = true := fun x xn _ h => hI.wf x xn h
      have e1 := wGetAt_eq_wGet (ctxOf p ts) _ v ((ctxOf p ts).p.fuel + 1) (by omega) hwfv hFv key'
      have e2 := wGetAt_eq_wGet (ctxOf p ts) _ w ((ctxOf p ts).p.fuel + 1) (by omega) hwfw hF key'
      have e3 : wGetAt (ctxOf p ts).p (ctxOf p ts).i (viewOf (treeRun p ts))
          ({ w3 with trail := "up.root-kept-empty" :: w3.trail } : W) ((ctxOf p ts).p.fuel + 1) key' =
          wGetAt (ctxOf p ts).p (ctxOf p ts).i (viewOf (treeRun p ts)) w ((ctxOf p ts).p.fuel + 1) key' := by
        unfold wGetAt
        rw [ReadsAs.value _ _ _ _ hr03', hr03'.1, hr03'.2.1]
      rw [e3, e2, e1] at hr
      unfold runGet
      simp only [ctxOf] at hr
      rw [hr]
      simp [Op.key, Op.value]

/-- As `SIS.Tree.opGetCaseOK'_delMerge`, for the runs of `N.Within`. -/
theorem opGetCaseOK'_delMerge (p : Params) (R : Struct BVal → Time → Prop) (hS : DelStepsOK p R)
    (hM : ∀ ts, MergeStepOK (ctxOf p ts) (viewOf (treeRun p ts)) (p.fuel + 1))
    (hC : ∀ ts, CollapseStepOK (ctxOf p ts) (viewOf (treeRun p ts)) (p.fuel + 1))
    (hsa2 : 2 ≤ p.splitAbove) (hcap : 1 ≤ p.mergeMax) (hMM : 2 ≤ p.M)
    (hPtr : ∀ ts, Within p ts → PointersOK (treeRun p ts)) :
    OpGetCaseOK' p R DelMergeCase := by
  have hf2 : 2 ≤ p.fuel + 1 := by unfold Params.fuel; omega
  intro ts tx hw hr z top hz htop pre op post hops r w hpre hI hRO hF0 hP
  obtain ⟨key, hop, hmerges⟩ := hP
  have hwts : Within p ts := by
    have := within_take p (ts ++ [tx]) hw ts.length
    simpa using this
  have hfresh : ∀ q ∈ treeRun p ts, q.1 < tx.base := by
    have := (hw.w.2 ts.length (by simp)).1
    simpa using this
  have hK := treeRun_kindsAllOK p hMM hPtr ts hwts
  have hv : ViewIdsBelow tx.base (ctxOf p ts).view :=
    viewIdsBelow_rootless _ _ (viewIdsBelow_view p (treeRun p ts) ts.length tx.base hfresh)
  have hk : ViewKinds (kindOracleOf p (treeRun p ts)) tx.base (ctxOf p ts) :=
    viewKinds_of p (treeRun p ts) ts.length tx.base hfresh (treeRun_timesLE p ts) (hPtr ts hwts) hK
  have hICEk : ICEFromKinds (ctxOf p ts) (viewOf (treeRun p ts)) (kindOracleOf p (treeRun p ts)) tx.base :=
    fun v hb hi hun => innerChildren_of_kinds p (treeRun p ts) tx.base (ctxOf p ts) v rfl hK
      (hPtr ts hwts) hb hi.cache hun
  exact hS ts tx hw hr z top hz htop pre op post hops r w hpre hI hRO hF0 key hop hmerges
    (fun g h v hv' => writerWP_afterDelete_del key g h (ctxOf p ts) _ (viewCoherent_ctxOf p ts)
      (p.fuel + 1) hf2 (hM ts) (hC ts) _ _ hv hk hICEk hsa2 hcap w key v hv')
    (fun g h merged v hv' => writerWP_mergeUp_del key g (ctxOf p ts) _ (viewCoherent_ctxOf p ts)
      (p.fuel + 1) hf2 (hM ts) _ _ hv hk hICEk hsa2 hcap w key p.fuel h merged v hv')
    (fun seg v hv' => writerWP_collapseRoot_del key seg (ctxOf p ts) _ (viewCoherent_ctxOf p ts)
      (p.fuel + 1) hf2 (hC ts) w key _ _ hv hk hICEk hsa2 v hv')

/-- As `SIS.Tree.opGetCaseOK_delMerge`, for the runs of `N.Within`. -/
theorem opGetCaseOK_delMerge (p : Params) (R : Struct BVal → Time → Prop) (hS : DelStepsOK p R)
    (hM : ∀ ts, MergeStepOK (ctxOf p ts) (viewOf (treeRun p ts)) (p.fuel + 1))
    (hC : ∀ ts, CollapseStepOK (ctxOf p ts) (viewOf (treeRun p ts)) (p.fuel + 1))
    (hsa2 : 2 ≤ p.splitAbove) (hcap : 1 ≤ p.mergeMax) (hMM : 2 ≤ p.M)
    (hPtr : ∀ ts, Within p ts → PointersOK (treeRun p ts)) (hfit : TxSegFitsOK p R) :
    OpGetCaseOK p R DelMergeCase :=
  opGetCaseOK_of' p R DelMergeCase (opGetCaseOK'_delMerge p R hS hM hC hsa2 hcap hMM hPtr) hfit

/-- As `SIS.Tree.delStepsJ2OK_of_cases`, for the runs of `N.Within`. -/
theorem delStepsJ2OK_of_cases (p : Params) (R : Struct BVal → Time → Prop) (S : List Tx → Tx → W → Prop)
    (c5 : DelStepsCaseJ2OK p R S DelNoLeafM) (c6 : DelStepsCaseJ2OK p R S DelNoopM)
    (c7 : DelStepsCaseJ2OK p R S DelEmptyM) (c8 : DelStepsCaseJ2OK p R S DelRoomM)
    (c9 : DelStepsCaseJ2OK p R S DelFullM) : DelStepsJ2OK p R S := by
  intro ts tx hw hr z top hz htop pre op post hops r w hpre hS hJ key hop hm hA hMU hCR
  rcases delMerge_cover (ctxOf p ts) (viewOf (treeRun p ts)) w key hm with h | h | h | h | h
  · exact c5 ts tx hw hr z top hz htop pre op post hops r w hpre hS hJ key hop (hop ▸ h) hA hMU hCR
  · exact c6 ts tx hw hr z top hz htop pre op post hops r w hpre hS hJ key hop (hop ▸ h) hA hMU hCR
  · exact c7 ts tx hw hr z top hz htop pre op post hops r w hpre hS hJ key hop (hop ▸ h) hA hMU hCR
  · exact c8 ts tx hw hr z top hz htop pre op post hops r w hpre hS hJ key hop (hop ▸ h) hA hMU hCR
  · exact c9 ts tx hw hr z top hz htop pre op post hops r w hpre hS hJ key hop (hop ▸ h) hA hMU hCR

/-- As `SIS.Tree.delStepsCaseJ2OK_or`, for the runs of `N.Within`. -/
theorem delStepsCaseJ2OK_or (p : Params) (R : Struct BVal → Time → Prop) (S : List Tx → Tx → W → Prop)
    (P P1 P2 : Ctx → View BVal → W → Op → Prop)
    (hs : ∀ c base w op, P c base w op → P1 c base w op ∨ P2 c base w op)
    (h1 : DelStepsCaseJ2OK p R S P1) (h2 : DelStepsCaseJ2OK p R S P2) : DelStepsCaseJ2OK p R S P := by
  intro ts tx hw hr z top hz htop pre op post hops r w hpre hS hJ key hop hPc hA hMU hCR
  rcases hs _ _ _ _ hPc with h | h
  · exact h1 ts tx hw hr z top hz htop pre op post hops r w hpre hS hJ key hop h hA hMU hCR
  · exact h2 ts tx hw hr z top hz htop pre op post hops r w hpre hS hJ key hop h hA hMU hCR

/-- As `SIS.Tree.opJ2Case_delMergeR`, for the runs of `N.Within`. -/
theorem opJ2Case_delMergeR (p : Params) (R : Struct BVal → Time → Prop) (S : List Tx → Tx → W → Prop)
    (hS : DelStepsJ2OK p R S)
    (hM : ∀ ts, MergeStepOK (ctxOf p ts) (viewOf (treeRun p ts)) (p.fuel + 1))
    (hC : ∀ ts, CollapseStepOK (ctxOf p ts) (viewOf (treeRun p ts)) (p.fuel + 1))
    (hRJ : ∀ ts B, ReplaceRootFullJ2OK (ctxOf p ts) (viewOf (treeRun p ts)) (p.fuel + 1) B)
    (hsa2 : 2 ≤ p.splitAbove) (hcap : 1 ≤ p.mergeMax)
    (hRP : ∀ P t, R P t → PointersOK P) (hRK : ∀ P t, R P t → KindsAllOK p P) :
    OpJ2CaseOK p R S DelMergeCase := by
  have hf2 : 2 ≤ p.fuel + 1 := by unfold Params.fuel; omega
  intro ts tx hw hr z top hz htop pre op post hops r w hpre _ hSw hJ hPc
  obtain ⟨key, hop, hmerges⟩ := hPc
  have hpos : 0 < (ctxOf p ts).i := by simp [ctxOf]
  have hwts : Within p ts := by
    have := within_take p (ts ++ [tx]) hw ts.length
    simpa using this
  have hfresh : ∀ q ∈ treeRun p ts, q.1 < tx.base := by
    have := (hw.w.2 ts.length (by simp)).1
    simpa using this
  have hK := hRK _ _ hr
  have hv : ViewIdsBelow tx.base (ctxOf p ts).view :=
    viewIdsBelow_rootless _ _ (viewIdsBelow_view p (treeRun p ts) ts.length tx.base hfresh)
  have hk : ViewKinds (kindOracleOf p (treeRun p ts)) tx.base (ctxOf p ts) :=
    viewKinds_of p (treeRun p ts) ts.length tx.base hfresh (treeRun_timesLE p ts) (hRP _ _ hr) hK
  have hICEk : ICEFromKinds (ctxOf p ts) (viewOf (treeRun p ts)) (kindOracleOf p (treeRun p ts)) tx.base :=
    fun v hb hi hun => innerChildren_of_kinds p (treeRun p ts) tx.base (ctxOf p ts) v rfl hK
      (hRP _ _ hr) hb hi.cache hun
  refine writerWP_mono (hS ts tx hw hr z top hz htop pre op post hops r w hpre hSw hJ key hop hmerges
    (fun g h v hv' => writerWP_afterDelete_delJ key g h (ctxOf p ts) _ (viewCoherent_ctxOf p ts)
      (p.fuel + 1) hf2 (hM ts) (hC ts) _ _ hv hk hICEk hsa2 hcap tx.base hpos (hRJ ts tx.base) w key v hv')
    (fun g h merged v hv' => writerWP_mergeUp_delJ key g (ctxOf p ts) _ (viewCoherent_ctxOf p ts)
      (p.fuel + 1) hf2 (hM ts) _ _ hv hk hICEk hsa2 hcap tx.base hpos w key p.fuel h merged v hv')
    (fun seg v hv' => writerWP_collapseRoot_delJ key seg (ctxOf p ts) _ (viewCoherent_ctxOf p ts)
      (p.fuel + 1) hf2 (hC ts) w key _ _ hv hk hICEk hsa2 tx.base hpos (hRJ ts tx.base) v hv')) ?_
  intro _ w' h' _
  exact h'

/-- As `SIS.Tree.runTreeQ_of_cases3S`, for the runs of `N.Within`. -/
theorem runTreeQ_of_cases3S (p : Params) (hM : 2 ≤ p.M) (hsa : 2 ≤ p.splitAbove)
    (Q : Struct BVal → Time → Prop) (hQ0 : Q (initStruct p) 0)
    (hQs : ∀ ts tx, Within p (ts ++ [tx]) → RunTreeQ p Q (treeRun p ts) ts.length →
      RunLinksOK p (treeRun p (ts ++ [tx])) (ts.length + 1) →
      TreeAt p (treeRun p (ts ++ [tx])) (ts.length + 1) →
      Q (treeRun p (ts ++ [tx])) (ts.length + 1))
    (hQP : ∀ P t, Q P t → PointersOK P) (hQK : ∀ P t, Q P t → KindsAllOK p P)
    (ho : OpTreeOKUnder p (RunTreeQ p Q))
    (hPI : StateOK p (RunTreeQ p Q) (fun ts _ w => PutInv (ctxOf p ts) (viewOf (treeRun p ts)) w))
    (hRO : StateOK p (RunTreeQ p Q) (fun ts _ w =>
      RangeOrder (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) w.top.rootKey))
    (hB : BaseStartOK p (RunTreeQ p Q))
    (hFS : StateOK p (RunTreeQ p Q) (fun ts _ w =>
      SegFits (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) (p.fuel - 1) w.top.rootKey))
    (hMF : StateOK p (RunTreeQ p Q) (fun _ tx w => ∀ x o, w.madeFor.lookup x = some o → o < tx.base))
    (c3 : OpJ2CaseOK p (RunTreeQ p Q) (TakeS4 p) PutNewSegFullCase)
    (c4 : OpJ2CaseOK p (RunTreeQ p Q) (TakeS4 p) DelMergeCase)
    (c7 : OpJ2CaseOK p (RunTreeQ p Q) (TakeS4 p) DelEmptyCase)
    (c9 : OpJ2CaseOK p (RunTreeQ p Q) (TakeS4 p) DelFullCase) :
    ∀ ts, Within p ts → RunTreeQ p Q (treeRun p ts) ts.length := by
  have hSI : ∀ ts tx w, TakeS4 p ts tx w → PutInv (ctxOf p ts) (viewOf (treeRun p ts)) w :=
    fun _ _ _ h => h.1.1.1.1
  have hSV : ∀ ts tx w, TakeS4 p ts tx w → LeafVals (ctxOf p ts) (viewOf (treeRun p ts)) tx.base w :=
    fun _ _ _ h => h.1.1.1.2
  have hSB : ∀ ts tx w, TakeS4 p ts tx w → tx.base ≤ w.next := fun _ _ _ h => h.1.1.2
  have hSR : ∀ ts tx w, TakeS4 p ts tx w →
      RangeOrder (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) w.top.rootKey := fun _ _ _ h => h.1.2
  have hS : StateOK p (RunTreeQ p Q) (TakeS4 p) := by
    intro ts tx hw hr z top hz htop pre post hsplit r w h
    exact ⟨⟨⟨⟨hPI ts tx hw hr z top hz htop pre post hsplit r w h,
      leafVals_reached p hM ts tx hw top pre post hsplit r w h (hQP _ _ hr.2.2) (hQK _ _ hr.2.2)⟩,
      base_le_next_reached p hM ts tx hw top pre post hsplit r w h (hQP _ _ hr.2.2) (hQK _ _ hr.2.2)⟩,
      hRO ts tx hw hr z top hz htop pre post hsplit r w h⟩,
      hFS ts tx hw hr z top hz htop pre post hsplit r w h, hMF ts tx hw hr z top hz htop pre post hsplit r w h⟩
  have hSRF : ∀ ts tx w, TakeS4 p ts tx w → ReachedFree p (treeRun p ts) (ts.length + 1) w :=
    fun ts _ w h y hy => h.1.1.1.1.untaken y (tReach_reachS _ _ _ _ hy)
  have hO : OpJ2OK p (RunTreeQ p Q) (TakeS4 p) :=
    opJ2OK_of_cases p _ _ (opJ2Case_putLeafRoom p _ _ hSI hSV)
      (opJ2Case_putLeafFull p _ _ (fun _ _ h => h.1) hsa hSI hSV hSB hSR)
      (opJ2Case_putNewSeg p _ _ hM hSI hSB c3) c4
      (opJ2Case_delNoLeaf p _ _ hSI) (opJ2Case_delNoop p _ _ hSI) c7 (opJ2Case_delRoom p _ _ hSI hSV) c9
  exact runTree_jointJ2 p hM Q hQ0 hQs ho (TakeS4 p) hO hS hSRF hB
    (takenNotValOK_of p hM _ (fun _ _ h => hQP _ _ h.2.2) (fun _ _ h => hQK _ _ h.2.2))

/-- As `SIS.Tree.runTreeQ_of_cases4S`, for the runs of `N.Within`. -/
theorem runTreeQ_of_cases4S (p : Params) (hM : 2 ≤ p.M) (hsa : 2 ≤ p.splitAbove)
    (Q : Struct BVal → Time → Prop) (hQ0 : Q (initStruct p) 0)
    (hQs : ∀ ts tx, Within p (ts ++ [tx]) → RunTreeQ p Q (treeRun p ts) ts.length →
      RunLinksOK p (treeRun p (ts ++ [tx])) (ts.length + 1) →
      TreeAt p (treeRun p (ts ++ [tx])) (ts.length + 1) →
      Q (treeRun p (ts ++ [tx])) (ts.length + 1))
    (hQP : ∀ P t, Q P t → PointersOK P) (hQK : ∀ P t, Q P t → KindsAllOK p P)
    (ho : OpTreeOKUnder p (RunTreeQ p Q))
    (hPI : StateOK p (RunTreeQ p Q) (fun ts _ w => PutInv (ctxOf p ts) (viewOf (treeRun p ts)) w))
    (hRO : StateOK p (RunTreeQ p Q) (fun ts _ w =>
      RangeOrder (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) w.top.rootKey))
    (hB : BaseStartOK p (RunTreeQ p Q))
    (hFS : StateOK p (RunTreeQ p Q) (fun ts _ w =>
      SegFits (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) (p.fuel - 1) w.top.rootKey))
    (hMF : StateOK p (RunTreeQ p Q) (fun _ tx w => ∀ x o, w.madeFor.lookup x = some o → o < tx.base))
    (c4 : OpJ2CaseOK p (RunTreeQ p Q) (TakeS4 p) DelMergeCase)
    (c7 : OpJ2CaseOK p (RunTreeQ p Q) (TakeS4 p) DelEmptyCase)
    (c9 : OpJ2CaseOK p (RunTreeQ p Q) (TakeS4 p) DelFullCase) :
    ∀ ts, Within p ts → RunTreeQ p Q (treeRun p ts) ts.length :=
  runTreeQ_of_cases3S p hM hsa Q hQ0 hQs hQP hQK ho hPI hRO hB hFS hMF
    (opJ2Case_putNewSegFull p _ _ (fun _ _ h => h.1) hM hsa (fun _ _ _ h => h.1.1.1.1)
      (fun _ _ _ h => h.1.1.2) (fun _ _ _ h => h.1.2)) c4 c7 c9

/-- As `SIS.Tree.runTreeQ_of_cases_merges4S`, for the runs of `N.Within`. -/
theorem runTreeQ_of_cases_merges4S (p : Params) (hM : 2 ≤ p.M) (hsa : 2 ≤ p.splitAbove)
    (hm : p.merges = true) (Q : Struct BVal → Time → Prop) (hQ0 : Q (initStruct p) 0)
    (hQs : ∀ ts tx, Within p (ts ++ [tx]) → RunTreeQ p Q (treeRun p ts) ts.length →
      RunLinksOK p (treeRun p (ts ++ [tx])) (ts.length + 1) →
      TreeAt p (treeRun p (ts ++ [tx])) (ts.length + 1) →
      Q (treeRun p (ts ++ [tx])) (ts.length + 1))
    (hQP : ∀ P t, Q P t → PointersOK P) (hQK : ∀ P t, Q P t → KindsAllOK p P)
    (ho : OpTreeOKUnder p (RunTreeQ p Q))
    (hPI : StateOK p (RunTreeQ p Q) (fun ts _ w => PutInv (ctxOf p ts) (viewOf (treeRun p ts)) w))
    (hRO : StateOK p (RunTreeQ p Q) (fun ts _ w =>
      RangeOrder (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) w.top.rootKey))
    (hB : BaseStartOK p (RunTreeQ p Q))
    (hFS : StateOK p (RunTreeQ p Q) (fun ts _ w =>
      SegFits (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) (p.fuel - 1) w.top.rootKey))
    (hMF : StateOK p (RunTreeQ p Q) (fun _ tx w => ∀ x o, w.madeFor.lookup x = some o → o < tx.base))
    (c4 : OpJ2CaseOK p (RunTreeQ p Q) (TakeS4 p) DelMergeCase) :
    ∀ ts, Within p ts → RunTreeQ p Q (treeRun p ts) ts.length :=
  runTreeQ_of_cases4S p hM hsa Q hQ0 hQs hQP hQK ho hPI hRO hB hFS hMF c4
    (opJ2CaseOK_void p _ _ _ hm delEmptyCase_merges) (opJ2CaseOK_void p _ _ _ hm delFullCase_merges)

/-- As `SIS.Tree.runTreeQ_of_mergesS`, for the runs of `N.Within`. -/
theorem runTreeQ_of_mergesS (p : Params) (hM : 2 ≤ p.M) (hsa : 2 ≤ p.splitAbove)
    (hcap : 1 ≤ p.mergeMax) (hm : p.merges = true)
    (Q : Struct BVal → Time → Prop) (hQ0 : Q (initStruct p) 0)
    (hQs : ∀ ts tx, Within p (ts ++ [tx]) → RunTreeQ p Q (treeRun p ts) ts.length →
      RunLinksOK p (treeRun p (ts ++ [tx])) (ts.length + 1) →
      TreeAt p (treeRun p (ts ++ [tx])) (ts.length + 1) →
      Q (treeRun p (ts ++ [tx])) (ts.length + 1))
    (hQP : ∀ P t, Q P t → PointersOK P) (hQK : ∀ P t, Q P t → KindsAllOK p P)
    (ho : OpTreeOKUnder p (RunTreeQ p Q))
    (hPI : StateOK p (RunTreeQ p Q) (fun ts _ w => PutInv (ctxOf p ts) (viewOf (treeRun p ts)) w))
    (hRO : StateOK p (RunTreeQ p Q) (fun ts _ w =>
      RangeOrder (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) w.top.rootKey))
    (hFS : StateOK p (RunTreeQ p Q) (fun ts _ w =>
      SegFits (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) (p.fuel - 1) w.top.rootKey))
    (hMF : StateOK p (RunTreeQ p Q) (fun _ tx w => ∀ x o, w.madeFor.lookup x = some o → o < tx.base))
    (hDS : DelStepsJ2OK p (RunTreeQ p Q) (TakeS4 p))
    (hMS : ∀ ts, MergeStepOK (ctxOf p ts) (viewOf (treeRun p ts)) (p.fuel + 1))
    (hCo : ∀ ts, CollapseStepOK (ctxOf p ts) (viewOf (treeRun p ts)) (p.fuel + 1))
    (hRJ : ∀ ts B, ReplaceRootFullJ2OK (ctxOf p ts) (viewOf (treeRun p ts)) (p.fuel + 1) B) :
    ∀ ts, Within p ts → RunTreeQ p Q (treeRun p ts) ts.length :=
  runTreeQ_of_cases_merges4S p hM hsa hm Q hQ0 hQs hQP hQK ho hPI hRO (baseStartOK_runTreeQ p Q) hFS hMF
    (opJ2Case_delMergeR p _ _ hDS hMS hCo hRJ hsa hcap (fun _ _ h => hQP _ _ h.2.2) (fun _ _ h => hQK _ _ h.2.2))

/-- As `SIS.Tree.dead_reached`, for the runs of `N.Within`. -/
theorem dead_reached (p : Params) (R : Struct BVal → Time → Prop)
    (hRL : ∀ P t, R P t → RunLinksOK p P t)
    (hT : OpCaseOK p R (QTree p) AnyOp) (hP : OpCaseOK p R (QPutInv p) AnyOp)
    (hO : OpCaseOK p R (QRange p) AnyOp) (hDd : OpCaseOK p R (QDead p) AnyOp)
    (ts : List Tx) (tx : Tx) (hw : Within p (ts ++ [tx])) (hr : R (treeRun p ts) ts.length)
    (hTA : TreeAt p (treeRun p ts) ts.length) (hI : InvOK p (treeRun p ts) ts.length)
    (hD : DeadAllOK p (treeRun p ts))
    (z : NodeId) (top : Top)
    (hz : lastTop (view (treeSpec p) (treeRun p ts) ts.length) = some z)
    (htop : topOf p (ctxOf p ts).view z = .ok top) :
    ∀ pre post, tx.ops = pre ++ post → ∀ r w,
      (pre.mapM putKv) (ctxOf p ts) (wInit tx top) = .ok (r, w) →
      WDeadOK p (treeRun p ts) w := by
  intro pre
  suffices hk : ∀ k, ∀ pre : List Op, pre.length = k → ∀ post, tx.ops = pre ++ post → ∀ r w,
      (pre.mapM putKv) (ctxOf p ts) (wInit tx top) = .ok (r, w) →
      WDeadOK p (treeRun p ts) w
    from hk pre.length pre rfl
  intro k
  induction k with
  | zero =>
    intro pre hl _ _ r w h
    have hnil : pre = [] := List.eq_nil_of_length_eq_zero hl
    subst hnil
    simp only [List.mapM_nil, pure, ReaderT.pure, StateT.pure, Except.pure, Except.ok.injEq,
      Prod.mk.injEq] at h
    rw [← h.2]
    exact wDeadOK_init p ts tx top hD
  | succ k ih =>
    intro pre hl post hsplit r w h
    rcases List.eq_nil_or_concat pre with hnil | ⟨pre', op, hpre⟩
    · subst hnil; simp at hl
    · rw [List.concat_eq_append] at hpre
      subst hpre
      have hl' : pre'.length = k := by simp at hl; omega
      rw [List.mapM_append] at h
      simp only [List.mapM_cons, List.mapM_nil, bind, ReaderT.bind, StateT.bind, Except.bind] at h
      cases h1 : (pre'.mapM putKv) (ctxOf p ts) (wInit tx top) with
      | error e => rw [h1] at h; cases h
      | ok rw1 =>
        rcases rw1 with ⟨r1, w1⟩
        rw [h1] at h
        simp only at h
        cases h2 : putKv op (ctxOf p ts) w1 with
        | error e => rw [h2] at h; cases h
        | ok aw =>
          rcases aw with ⟨a, w2⟩
          rw [h2] at h
          simp only [pure, ReaderT.pure, StateT.pure, Except.pure, Except.ok.injEq,
            Prod.mk.injEq] at h
          have hsplit' : tx.ops = pre' ++ op :: post := by rw [hsplit]; simp
          obtain ⟨hI1, hR1⟩ := joint_reached p R hRL hT hP hO ts tx hw hr hTA hI z top hz htop
            pre' (op :: post) hsplit' r1 w1 h1
          have hD1 := ih pre' hl' (op :: post) hsplit' r1 w1 h1
          have hD2 := hDd ts tx hw hr z top hz htop pre' op post hsplit' r1 w1 h1 hI1 hR1 trivial a
            w2 h2 hD1
          rw [← h.2]
          exact hD2

/-- As `SIS.Tree.deadAllOK_snocR`, for the runs of `N.Within`. -/
theorem deadAllOK_snocR (p : Params) (R : Struct BVal → Time → Prop)
    (hRL : ∀ P t, R P t → RunLinksOK p P t) (hRT : ∀ P t, R P t → TreeAt p P t)
    (hRI : ∀ P t, R P t → InvOK p P t)
    (hT : OpCaseOK p R (QTree p) AnyOp) (hPI : OpCaseOK p R (QPutInv p) AnyOp)
    (hO : OpCaseOK p R (QRange p) AnyOp) (hDd : OpCaseOK p R (QDead p) AnyOp)
    (ts : List Tx) (tx : Tx) (hw : Within p (ts ++ [tx])) (hr : R (treeRun p ts) ts.length)
    (hD : DeadAllOK p (treeRun p ts)) : DeadAllOK p (treeRun p (ts ++ [tx])) := by
  obtain ⟨noops, w, hrun⟩ := within_last_ok p ts tx hw
  obtain ⟨z, top, hz, htop, hops⟩ := runOps_ok p _ _ _ _ noops w hrun
  have hcl : CommitLiftAt p ts tx := commitLiftAt_of_links p ts tx hw (hRL _ _ hr)
  exact deadAllOK_commit p ts tx hcl noops w hrun
    (dead_reached p R hRL hT hPI hO hDd ts tx hw hr (hRT _ _ hr) (hRI _ _ hr) hD z top hz htop
      tx.ops [] (by simp) noops w hops)

end SIS.Tree.N
