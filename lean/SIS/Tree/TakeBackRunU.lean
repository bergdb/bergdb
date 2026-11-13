/-
The take-back's joint induction with the writer's tree under a run premise
(bergdb 024-12, TP4 and TP7): `OpTreeOKUnder p R`, cost's `OpTreeOK` for runs
that meet R, the form latest's assembly gives from its operation cases
(`GetOpAssembly.lean`). Each theorem here is the one of the same name without
`U` (TakeBackRun.lean, TakeBackRunT.lean, TakeBackDead.lean, WriterTree.lean)
with `OpTreeOKUnder` in place of `OpTreeOK`.
-/
import SIS.Tree.TakeBackDead

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- cost's `OpTreeOK` for the runs that meet R: every operation of a
transaction within reach, from a state with the writer's tree that its earlier
operations reach, keeps the writer's tree. -/
def OpTreeOKUnder (p : Params) (R : Struct BVal → Time → Prop) : Prop :=
  ∀ ts tx, Within p (ts ++ [tx]) → R (treeRun p ts) ts.length → ∀ z top,
    lastTop (view (treeSpec p) (treeRun p ts) ts.length) = some z →
    topOf p (ctxOf p ts).view z = .ok top →
    ∀ pre op post, tx.ops = pre ++ op :: post →
    ∀ r w, (pre.mapM putKv) (ctxOf p ts) (wInit tx top) = .ok (r, w) →
    WriterTreeOK p (treeRun p ts) (ts.length + 1) w →
    WriterWP (putKv op) (ctxOf p ts) w (fun _ w' =>
      WriterTreeOK p (treeRun p ts) (ts.length + 1) w')

theorem opTreeOKUnder_of_opTreeOK (p : Params) (R : Struct BVal → Time → Prop) (ho : OpTreeOK p) :
    OpTreeOKUnder p R :=
  fun ts tx hw _ => ho ts tx hw

/-- Every state that a prefix of the operations reaches has the writer's tree,
from the first state's and `OpTreeOK`. -/
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

/-- The writer's tree at every state between operations, from P's tree before
the transaction and `OpTreeOK`. -/
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

/-- P's tree after one transaction, from P's tree before it, `OpTreeOK` and the
lift of that transaction (`treeAt_commit_of_lift` at one step). -/
theorem treeAt_stepU (p : Params) (R : Struct BVal → Time → Prop) (ho : OpTreeOKUnder p R)
    (ts : List Tx) (tx : Tx) (hw : Within p (ts ++ [tx])) (hr : R (treeRun p ts) ts.length) (hT : TreeAt p (treeRun p ts) ts.length)
    (hl : CommitLiftAt p ts tx) : TreeAt p (treeRun p (ts ++ [tx])) (ts.length + 1) := by
  obtain ⟨noops, w, hrun⟩ := within_last_ok p ts tx hw
  obtain ⟨z, top, hz, htop, hops⟩ := runOps_ok p _ _ _ _ noops w hrun
  have hW := writerTreeOK_reachedU p R ho ts tx hw hr z top hz htop hT tx.ops [] (by simp) noops w hops
  obtain ⟨hK, htaken, htopt⟩ := hl noops w hrun
  have hR := rootAt_commit_of_lift p ts tx hw noops w hrun hK htaken htopt
  exact ⟨w.top.rootKey, hR, treeOK_congr_look _ _ _ _ (funext hK).symm hW⟩

/-- (A) and (B) at every state that a prefix of a transaction's operations
reaches, from the first state, `OpTakeOK` and the writer's tree at every such
state (cost's `OpTreeOK`, `writerTreeOK_reachedU`). -/
theorem takeInv_reachedU (p : Params) (R : Struct BVal → Time → Prop) (hO : OpTakeOK p R)
    (ho : OpTreeOKUnder p R) (ts : List Tx) (tx : Tx) (hw : Within p (ts ++ [tx]))
    (hr : R (treeRun p ts) ts.length) (hRL : RunLinksOK p (treeRun p ts) ts.length)
    (hT : TreeAt p (treeRun p ts) ts.length) (z : NodeId) (top : Top)
    (hz : lastTop (view (treeSpec p) (treeRun p ts) ts.length) = some z)
    (htop : topOf p (ctxOf p ts).view z = .ok top) :
    ∀ pre post, tx.ops = pre ++ post → ∀ r w,
      (pre.mapM putKv) (ctxOf p ts) (wInit tx top) = .ok (r, w) →
      TakeInv p (treeRun p ts) (ts.length + 1) tx.base w := by
  intro pre
  suffices hk : ∀ k, ∀ pre : List Op, pre.length = k → ∀ post, tx.ops = pre ++ post → ∀ r w,
      (pre.mapM putKv) (ctxOf p ts) (wInit tx top) = .ok (r, w) →
      TakeInv p (treeRun p ts) (ts.length + 1) tx.base w
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
    exact takeInv_init p ts tx hw hRL top
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
          exact hO ts tx hw hr z top hz htop pre' op post hsplit' r1 w1 h1 hT1 hI1 a w2 h2 hT2

/-- The take-back discipline under R, from the writer's tree (`OpTreeOK`), (A)
and (B) kept by every operation and (C) at the end, if R has TP4 and P's tree. -/
theorem takeBackOKUnder_of_opsU (p : Params) (R : Struct BVal → Time → Prop)
    (hRL : ∀ P t, R P t → RunLinksOK p P t) (hRT : ∀ P t, R P t → TreeAt p P t)
    (ho : OpTreeOKUnder p R) (hO : OpTakeOK p R) (hD : DeadTakenLiveOK p R) : TakeBackOKUnder p R := by
  intro ts tx hw hr noops w hrun
  obtain ⟨z, top, hz, htop, hops⟩ := runOps_ok p _ _ _ _ noops w hrun
  have hI := takeInv_reachedU p R hO ho ts tx hw hr (hRL _ _ hr) (hRT _ _ hr) z top hz htop tx.ops []
    (by simp) noops w hops
  have hl := commitLiftAt_of_links p ts tx hw (hRL _ _ hr) noops w hrun
  have hfresh : ∀ q ∈ treeRun p ts, q.1 < tx.base := by
    have h := (hw.2 ts.length (by simp)).1
    have hj : (ts ++ [tx])[ts.length]'(by simp) = tx := by simp
    have ht : (ts ++ [tx]).take ts.length = ts := by simp
    rw [hj, ht] at h
    exact h
  have hU : (w.nodes.map (·.1)).Nodup := execW_cacheUnique p tx (ts.length + 1) _ noops w
    (viewIdsBelow_view p (treeRun p ts) ts.length tx.base hfresh) hrun
  exact takeBackEnd_of_inv p (treeRun p ts) (ts.length + 1) tx.base w hI
    (hD ts tx hw hr noops w hrun) hl.2.1 hU

/-- The induction: TP4 (with the histories), P's tree and Q at every run
within reach, from Q's first state and step, cost's `OpTreeOK`, and the two
statements about the writer (`OpTakeOK`, `DeadTakenLiveOK`) under what the
induction carries. -/
theorem runTree_jointU (p : Params) (hM : 2 ≤ p.M) (Q : Struct BVal → Time → Prop)
    (hQ0 : Q (initStruct p) 0)
    (hQs : ∀ ts tx, Within p (ts ++ [tx]) → RunTreeQ p Q (treeRun p ts) ts.length →
      RunLinksOK p (treeRun p (ts ++ [tx])) (ts.length + 1) →
      TreeAt p (treeRun p (ts ++ [tx])) (ts.length + 1) →
      Q (treeRun p (ts ++ [tx])) (ts.length + 1))
    (ho : OpTreeOKUnder p (RunTreeQ p Q)) (hO : OpTakeOK p (RunTreeQ p Q)) (hD : DeadTakenLiveOK p (RunTreeQ p Q)) :
    ∀ ts, Within p ts → RunTreeQ p Q (treeRun p ts) ts.length := by
  have hTB : TakeBackOKUnder p (RunTreeQ p Q) :=
    takeBackOKUnder_of_opsU p _ (fun _ _ h => h.1) (fun _ _ h => h.2.1) ho hO hD
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

/-- TP7's take-back statement, from the induction's premises. -/
theorem takeBackOK_of_jointU (p : Params) (hM : 2 ≤ p.M) (Q : Struct BVal → Time → Prop)
    (hQ0 : Q (initStruct p) 0)
    (hQs : ∀ ts tx, Within p (ts ++ [tx]) → RunTreeQ p Q (treeRun p ts) ts.length →
      RunLinksOK p (treeRun p (ts ++ [tx])) (ts.length + 1) →
      TreeAt p (treeRun p (ts ++ [tx])) (ts.length + 1) →
      Q (treeRun p (ts ++ [tx])) (ts.length + 1))
    (ho : OpTreeOKUnder p (RunTreeQ p Q)) (hO : OpTakeOK p (RunTreeQ p Q)) (hD : DeadTakenLiveOK p (RunTreeQ p Q)) :
    TakeBackOKUnder p (RunLinksOK p) := by
  intro ts tx hw _
  have hj := runTree_jointU p hM Q hQ0 hQs ho hO hD ts (within_snoc_prefix p ts tx hw)
  exact takeBackOKUnder_of_opsU p _ (fun _ _ h => h.1) (fun _ _ h => h.2.1) ho hO hD ts tx hw hj

/-- P's tree at every run within reach, with no premise on the lift
(`treeAt_run` takes `CommitLiftOK`). -/
theorem treeAt_of_jointU (p : Params) (hM : 2 ≤ p.M) (Q : Struct BVal → Time → Prop)
    (hQ0 : Q (initStruct p) 0)
    (hQs : ∀ ts tx, Within p (ts ++ [tx]) → RunTreeQ p Q (treeRun p ts) ts.length →
      RunLinksOK p (treeRun p (ts ++ [tx])) (ts.length + 1) →
      TreeAt p (treeRun p (ts ++ [tx])) (ts.length + 1) →
      Q (treeRun p (ts ++ [tx])) (ts.length + 1))
    (ho : OpTreeOKUnder p (RunTreeQ p Q)) (hO : OpTakeOK p (RunTreeQ p Q)) (hD : DeadTakenLiveOK p (RunTreeQ p Q)) :
    ∀ ts, Within p ts → TreeAt p (treeRun p ts) ts.length :=
  fun ts hw => (runTree_jointU p hM Q hQ0 hQs ho hO hD ts hw).2.1

/-- (A) and (B) at every state that a prefix of a transaction's operations
reaches. -/
theorem takeInvT_reachedU (p : Params) (R : Struct BVal → Time → Prop) (hO : OpTakeTOK p R)
    (ho : OpTreeOKUnder p R) (ts : List Tx) (tx : Tx) (hw : Within p (ts ++ [tx]))
    (hr : R (treeRun p ts) ts.length)
    (hT : TreeAt p (treeRun p ts) ts.length) (z : NodeId) (top : Top)
    (hz : lastTop (view (treeSpec p) (treeRun p ts) ts.length) = some z)
    (htop : topOf p (ctxOf p ts).view z = .ok top) :
    ∀ pre post, tx.ops = pre ++ post → ∀ r w,
      (pre.mapM putKv) (ctxOf p ts) (wInit tx top) = .ok (r, w) →
      TakeInvT p (treeRun p ts) (ts.length + 1) w := by
  intro pre
  suffices hk : ∀ k, ∀ pre : List Op, pre.length = k → ∀ post, tx.ops = pre ++ post → ∀ r w,
      (pre.mapM putKv) (ctxOf p ts) (wInit tx top) = .ok (r, w) →
      TakeInvT p (treeRun p ts) (ts.length + 1) w
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
    exact takeInvT_init p ts tx hw top
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
          exact hO ts tx hw hr z top hz htop pre' op post hsplit' r1 w1 h1 hT1 hI1 a w2 h2 hT2

/-- The take-back discipline under R from the writer's tree, (A) and (B) in
`TtReachedN`'s form kept by every operation, and (C) at the end. -/
theorem takeBackOKUnder_of_opsTU (p : Params) (R : Struct BVal → Time → Prop)
    (hRL : ∀ P t, R P t → RunLinksOK p P t) (hRT : ∀ P t, R P t → TreeAt p P t)
    (ho : OpTreeOKUnder p R) (hO : OpTakeTOK p R) (hD : DeadTakenLiveOK p R) : TakeBackOKUnder p R := by
  intro ts tx hw hr noops w hrun
  obtain ⟨z, top, hz, htop, hops⟩ := runOps_ok p _ _ _ _ noops w hrun
  have hI := takeInvT_reachedU p R hO ho ts tx hw hr (hRT _ _ hr) z top hz htop tx.ops []
    (by simp) noops w hops
  have hl := commitLiftAt_of_links p ts tx hw (hRL _ _ hr) noops w hrun
  have hfresh : ∀ q ∈ treeRun p ts, q.1 < tx.base := by
    have h := (hw.2 ts.length (by simp)).1
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
  exact takeBackEnd_of_invT p (treeRun p ts) tx.base _ w hvg hG hI (hD ts tx hw hr noops w hrun) hl.2.1 hU

/-- The induction over the runs with `OpTakeTOK` (`runTree_jointU`). -/
theorem runTree_jointTU (p : Params) (hM : 2 ≤ p.M) (Q : Struct BVal → Time → Prop)
    (hQ0 : Q (initStruct p) 0)
    (hQs : ∀ ts tx, Within p (ts ++ [tx]) → RunTreeQ p Q (treeRun p ts) ts.length →
      RunLinksOK p (treeRun p (ts ++ [tx])) (ts.length + 1) →
      TreeAt p (treeRun p (ts ++ [tx])) (ts.length + 1) →
      Q (treeRun p (ts ++ [tx])) (ts.length + 1))
    (ho : OpTreeOKUnder p (RunTreeQ p Q)) (hO : OpTakeTOK p (RunTreeQ p Q)) (hD : DeadTakenLiveOK p (RunTreeQ p Q)) :
    ∀ ts, Within p ts → RunTreeQ p Q (treeRun p ts) ts.length := by
  have hTB : TakeBackOKUnder p (RunTreeQ p Q) :=
    takeBackOKUnder_of_opsTU p _ (fun _ _ h => h.1) (fun _ _ h => h.2.1) ho hO hD
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

/-- TP7's take-back statement from the premises of `runTree_jointTU`. -/
theorem takeBackOK_of_jointTU (p : Params) (hM : 2 ≤ p.M) (Q : Struct BVal → Time → Prop)
    (hQ0 : Q (initStruct p) 0)
    (hQs : ∀ ts tx, Within p (ts ++ [tx]) → RunTreeQ p Q (treeRun p ts) ts.length →
      RunLinksOK p (treeRun p (ts ++ [tx])) (ts.length + 1) →
      TreeAt p (treeRun p (ts ++ [tx])) (ts.length + 1) →
      Q (treeRun p (ts ++ [tx])) (ts.length + 1))
    (ho : OpTreeOKUnder p (RunTreeQ p Q)) (hO : OpTakeTOK p (RunTreeQ p Q)) (hD : DeadTakenLiveOK p (RunTreeQ p Q)) :
    TakeBackOKUnder p (RunLinksOK p) := by
  intro ts tx hw _
  have hj := runTree_jointTU p hM Q hQ0 hQs ho hO hD ts (within_snoc_prefix p ts tx hw)
  exact takeBackOKUnder_of_opsTU p _ (fun _ _ h => h.1) (fun _ _ h => h.2.1) ho hO hD ts tx hw hj

/-- `DeadLive` at every state that a prefix of a transaction's operations
reaches, from `OpDeadLiveOK`, given the walk's ranges at every such state. -/
theorem deadLive_reachedU (p : Params) (R : Struct BVal → Time → Prop)
    (hRL : ∀ P t, R P t → RunLinksOK p P t) (hOT : OpTakeTOK p R) (hO : OpDeadLiveOK p R)
    (ho : OpTreeOKUnder p R) (ts : List Tx) (tx : Tx) (hw : Within p (ts ++ [tx]))
    (hr : R (treeRun p ts) ts.length)
    (hT : TreeAt p (treeRun p ts) ts.length) (z : NodeId) (top : Top)
    (hz : lastTop (view (treeSpec p) (treeRun p ts) ts.length) = some z)
    (htop : topOf p (ctxOf p ts).view z = .ok top)
    (hRange : ∀ pre post, tx.ops = pre ++ post → ∀ r w,
      (pre.mapM putKv) (ctxOf p ts) (wInit tx top) = .ok (r, w) →
      RangeOrder (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) w.top.rootKey) :
    ∀ pre post, tx.ops = pre ++ post → ∀ r w,
      (pre.mapM putKv) (ctxOf p ts) (wInit tx top) = .ok (r, w) →
      DeadLive p (treeRun p ts) (ts.length + 1) tx.base w := by
  intro pre
  suffices hk : ∀ k, ∀ pre : List Op, pre.length = k → ∀ post, tx.ops = pre ++ post → ∀ r w,
      (pre.mapM putKv) (ctxOf p ts) (wInit tx top) = .ok (r, w) →
      DeadLive p (treeRun p ts) (ts.length + 1) tx.base w
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
    exact deadLive_init p ts tx hw (hRL _ _ hr) top
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
          have hTI := takeInvT_reachedU p R hOT ho ts tx hw hr hT z top hz htop pre' (op :: post) hsplit'
            r1 w1 h1
          exact hO ts tx hw hr z top hz htop pre' op post hsplit' r1 w1 h1 hT1 hTI
            (hRange pre' (op :: post) hsplit' r1 w1 h1) hI1 a w2 h2

/-- (C) at every transaction's end from `OpDeadLiveOK`, given the walk's ranges
at every state between operations. -/
theorem deadTakenLiveOK_of_opsU (p : Params) (R : Struct BVal → Time → Prop)
    (hRL : ∀ P t, R P t → RunLinksOK p P t) (hRT : ∀ P t, R P t → TreeAt p P t)
    (ho : OpTreeOKUnder p R) (hOT : OpTakeTOK p R) (hO : OpDeadLiveOK p R)
    (hRange : ∀ ts tx, Within p (ts ++ [tx]) → R (treeRun p ts) ts.length → ∀ z top,
      lastTop (view (treeSpec p) (treeRun p ts) ts.length) = some z →
      topOf p (ctxOf p ts).view z = .ok top →
      ∀ pre post, tx.ops = pre ++ post → ∀ r w,
      (pre.mapM putKv) (ctxOf p ts) (wInit tx top) = .ok (r, w) →
      RangeOrder (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) w.top.rootKey)
    (hTV : TakenNotValOK p R) :
    DeadTakenLiveOK p R := by
  intro ts tx hw hr noops w hrun
  obtain ⟨z, top, hz, htop, hops⟩ := runOps_ok p _ _ _ _ noops w hrun
  have hD := deadLive_reachedU p R hRL hOT hO ho ts tx hw hr (hRT _ _ hr) z top hz htop
    (hRange ts tx hw hr z top hz htop) tx.ops [] (by simp) noops w hops
  have hl := commitLiftAt_of_links p ts tx hw (hRL _ _ hr) noops w hrun
  have hfresh : ∀ q ∈ treeRun p ts, q.1 < tx.base := by
    have h := (hw.2 ts.length (by simp)).1
    have hj : (ts ++ [tx])[ts.length]'(by simp) = tx := by simp
    have ht : (ts ++ [tx]).take ts.length = ts := by simp
    rw [hj, ht] at h
    exact h
  have he : execW p tx (ts.length + 1) (view (treeSpec p) (treeRun p ts) (ts.length + 1 - 1)) =
      .ok (noops, w) := hrun
  have hU : (w.nodes.map (·.1)).Nodup := execW_cacheUnique p tx (ts.length + 1) _ noops w
    (viewIdsBelow_view p (treeRun p ts) ts.length tx.base hfresh) hrun
  exact deadTakenLive_of_deadLive p (treeRun p ts) (ts.length + 1) tx.base w hD hU hl.2.1
    (hTV ts tx hw hr noops w hrun)

end SIS.Tree
