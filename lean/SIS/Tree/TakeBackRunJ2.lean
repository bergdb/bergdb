/-
The take-back's joint induction with (B), (C) and their node facts kept by
every operation, (A) from the state predicate S (bergdb 024-12, TP7): every
operation keeps `J2N` (`OpJ2OK`), and S at every state gives `ReachedFree`
(latest's `PutInv.untaken` does, with `tReach_reachS`).
-/
import SIS.Tree.TakeBackRunJ

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- (B), (C) and their node facts of the writer's state. -/
def J2At (p : Params) (P : Struct BVal) (t : Time) (B : NodeId) (w : W) : Prop :=
  J2N (wNode p (viewOf P) w) t w.top.rootKey B (w.vals.map (·.1))

/-- Every operation of a transaction within reach, from a state that its
earlier operations reach, with the writer's tree, S and `J2At`, keeps `J2At`
(given the writer's tree after). -/
def OpJ2OK (p : Params) (R : Struct BVal → Time → Prop) (S : List Tx → Tx → W → Prop) : Prop :=
  ∀ ts tx, Within p (ts ++ [tx]) → R (treeRun p ts) ts.length → ∀ z top,
    lastTop (view (treeSpec p) (treeRun p ts) ts.length) = some z →
    topOf p (ctxOf p ts).view z = .ok top →
    ∀ pre op post, tx.ops = pre ++ op :: post →
    ∀ r w, (pre.mapM putKv) (ctxOf p ts) (wInit tx top) = .ok (r, w) →
    WriterTreeOK p (treeRun p ts) (ts.length + 1) w → S ts tx w →
    J2At p (treeRun p ts) (ts.length + 1) tx.base w →
    WriterWP (putKv op) (ctxOf p ts) w (fun _ w' =>
      WriterTreeOK p (treeRun p ts) (ts.length + 1) w' →
      J2At p (treeRun p ts) (ts.length + 1) tx.base w')

/-- (B), (C) and the node facts at every state that a prefix of a
transaction's operations reaches, from `OpJ2OK`, the first state's and S at
every such state. -/
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

/-- The take-back discipline under R from the writer's tree under R,
`OpTakeJOK` with S at every state, P's key nodes starting before the
transaction, and no node taken back a value. -/
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
  have hDT := deadTakenLive_of_deadLive p (treeRun p ts) (ts.length + 1) tx.base w hI.2.2.1 hU hl.2.1
    (hTV ts tx hw hr noops w hrun)
  exact takeBackEnd_of_invT p (treeRun p ts) tx.base _ w hvg hG ⟨hI.1, hI.2.1⟩ hDT hl.2.1 hU

/-- The induction over the runs with `OpTakeTOK` (`runTree_jointU`). -/
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

/-- TP7's take-back statement from the premises of `runTree_jointTU`. -/
theorem takeBackOK_of_jointJ2 (p : Params) (hM : 2 ≤ p.M) (Q : Struct BVal → Time → Prop)
    (hQ0 : Q (initStruct p) 0)
    (hQs : ∀ ts tx, Within p (ts ++ [tx]) → RunTreeQ p Q (treeRun p ts) ts.length →
      RunLinksOK p (treeRun p (ts ++ [tx])) (ts.length + 1) →
      TreeAt p (treeRun p (ts ++ [tx])) (ts.length + 1) →
      Q (treeRun p (ts ++ [tx])) (ts.length + 1))
    (ho : OpTreeOKUnder p (RunTreeQ p Q)) (S : List Tx → Tx → W → Prop) (hO : OpJ2OK p (RunTreeQ p Q) S)
    (hS : StateOK p (RunTreeQ p Q) S)
    (hSRF : ∀ ts tx w, S ts tx w → ReachedFree p (treeRun p ts) (ts.length + 1) w) (hB : BaseStartOK p (RunTreeQ p Q)) (hTV : TakenNotValOK p (RunTreeQ p Q)) :
    TakeBackOKUnder p (RunLinksOK p) := by
  intro ts tx hw _
  have hj := runTree_jointJ2 p hM Q hQ0 hQs ho S hO hS hSRF hB hTV ts (within_snoc_prefix p ts tx hw)
  exact takeBackOKUnder_of_opsJ2 p _ (fun _ _ h => h.1) (fun _ _ h => h.2.1) ho S hO hS hSRF hB hTV ts tx hw hj

end SIS.Tree
