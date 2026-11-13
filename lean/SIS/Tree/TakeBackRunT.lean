/-
The take-back's induction (TakeBackRun.lean) with (B) in the form that every
rule of the writer keeps (bergdb 024-12, TP4): `TtReachedN`, a node with a klong
of the transaction's time is reached from the space root. With the overlay's
klongs before the transaction those of the view (`CacheGood`, `execW_good`),
whose pointers are below the transaction's first id (`ViewGood`), it gives the
take-back at the end (`takeBackEnd_of_invT`): a live klong to a node of the
transaction is a klong of the transaction's time. The per-operation premise is
`OpTakeTOK`; the rest is as in TakeBackRun.lean.
-/
import SIS.Tree.TakeInvTree
import SIS.Tree.WriterGoodOps

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- (A) and (B) in the form every rule keeps. -/
def TakeInvT (p : Params) (P : Struct BVal) (t : Time) (w : W) : Prop :=
  ReachedFree p P t w ∧ TtReachedN (wNode p (viewOf P) w) t w.top.rootKey

/-- `OpTakeOK` with `TakeInvT`. -/
def OpTakeTOK (p : Params) (R : Struct BVal → Time → Prop) : Prop :=
  ∀ ts tx, Within p (ts ++ [tx]) → R (treeRun p ts) ts.length → ∀ z top,
    lastTop (view (treeSpec p) (treeRun p ts) ts.length) = some z →
    topOf p (ctxOf p ts).view z = .ok top →
    ∀ pre op post, tx.ops = pre ++ op :: post →
    ∀ r w, (pre.mapM putKv) (ctxOf p ts) (wInit tx top) = .ok (r, w) →
    WriterTreeOK p (treeRun p ts) (ts.length + 1) w →
    TakeInvT p (treeRun p ts) (ts.length + 1) w →
    WriterWP (putKv op) (ctxOf p ts) w (fun _ w' =>
      WriterTreeOK p (treeRun p ts) (ts.length + 1) w' →
      TakeInvT p (treeRun p ts) (ts.length + 1) w')

/-- A live klong of an overlay node to a node at or above B is a klong of the
transaction's time: the node has a time klong of it. -/
theorem time_of_live_new (B : NodeId) (c : Ctx) (hv : ViewGood B c) (x : NodeId) (n : KNode)
    (hg : Good B c x n) (cv : Nat) (y : NodeId) (hk : Klong.key cv y ∈ n.ks) (hB : B ≤ y) :
    Klong.time c.i ∈ n.ks := by
  have hnot : Klong.key cv y ∉ prefixAt n.ks (c.i - 1) := by
    intro hm
    rw [hg.old] at hm
    unfold baseKlongs at hm
    cases hx : c.view x with
    | none => rw [hx] at hm; cases hm
    | some nd =>
      rw [hx] at hm
      have := hv.ptrs x nd hx cv y hm
      omega
  obtain ⟨s, hs, hts⟩ := later_time_of_not_mem_prefixAt n.ks (c.i - 1) _ hk hnot
  have hle := hg.times s hs
  have hpos := hv.pos
  have : s = c.i := by omega
  rw [← this]
  exact hs

/-- The take-back at a state from (A), (B) in `TtReachedN`'s form, (C), the
overlay's klongs before the transaction those of the view, the nodes taken
back at or above B, and one overlay entry per node. -/
theorem takeBackEnd_of_invT (p : Params) (P : Struct BVal) (B : NodeId) (c : Ctx) (w : W)
    (hv : ViewGood B c) (hG : CacheGood B c w) (hI : TakeInvT p P c.i w) (hD : DeadTakenLive c.i w)
    (hA : ∀ x ∈ w.taken, B ≤ x) (hU : (w.nodes.map (·.1)).Nodup) : TakeBackEnd w := by
  obtain ⟨hF, hL⟩ := hI
  refine ⟨?_, hF _ TReach.root⟩
  intro q hq hqk cv y hk
  cases hy : w.taken.contains y with
  | false => rfl
  | true =>
    exfalso
    obtain ⟨c', hc⟩ := hD q hq hqk cv y hk hy
    have hlk : w.nodes.lookup q.1 = some q.2 := nex_run_lookup_of_mem w.nodes q.1 q.2 hU hq
    have hqk' : q.1 ∉ w.taken := by simpa using hqk
    have hN : wNode p (viewOf P) w q.1 = some q.2 := by simp [wNode, hqk', hlk]
    have hB : B ≤ y := hA y (by simpa using hy)
    have htm := time_of_live_new B c hv q.1 q.2 (hG.2 q hq) c' y
      (KNode.liveAt_key_mem _ _ c' y hc) hB
    have hr := hL q.1 q.2 hN htm
    have hry : TReach (wNode p (viewOf P) w) c.i w.top.rootKey y := TReach.link hr ⟨q.2, hN, hc⟩
    have := hF y hry
    rw [hy] at this
    cases this

/-- (A) and (B) at a transaction's first state: nothing taken back, and P's
nodes have no klong of the transaction's time. -/
theorem takeInvT_init (p : Params) (ts : List Tx) (tx : Tx) (_hw : Within p (ts ++ [tx]))
    (top : Top) : TakeInvT p (treeRun p ts) (ts.length + 1) (wInit tx top) := by
  have hlook : wNode p (viewOf (treeRun p ts)) (wInit tx top) = knodeOf p (viewOf (treeRun p ts)) := by
    funext x
    simp [wNode, wInit]
  refine ⟨fun y _ => by simp [wInit], ?_⟩
  intro q qn hq hm
  rw [hlook] at hq
  exfalso
  unfold knodeOf viewOf at hq
  cases hg : (treeRun p ts).get? q with
  | none => simp [hg] at hq
  | some nd =>
    simp only [hg] at hq
    split at hq
    · cases hq
    · simp only [Option.some.injEq] at hq
      subst hq
      obtain ⟨e, he, het⟩ := klongsOf_time_mem nd.hist _ hm
      have := treeRun_timesLE p ts _ (mem_of_get? hg) e he
      omega

/-- (A) and (B) at every state that a prefix of a transaction's operations
reaches. -/
theorem takeInvT_reached (p : Params) (R : Struct BVal → Time → Prop) (hO : OpTakeTOK p R)
    (ho : OpTreeOK p) (ts : List Tx) (tx : Tx) (hw : Within p (ts ++ [tx]))
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
          have hT1 := writerTreeOK_reached p ho ts tx hw z top hz htop hT pre' (op :: post)
            hsplit' r1 w1 h1
          have hT2 := writerTreeOK_reached p ho ts tx hw z top hz htop hT (pre' ++ [op]) post
            (by rw [hsplit]) r w h0
          rw [← h.2] at hT2 ⊢
          exact hO ts tx hw hr z top hz htop pre' op post hsplit' r1 w1 h1 hT1 hI1 a w2 h2 hT2

/-- The take-back discipline under R from the writer's tree, (A) and (B) in
`TtReachedN`'s form kept by every operation, and (C) at the end. -/
theorem takeBackOKUnder_of_opsT (p : Params) (R : Struct BVal → Time → Prop)
    (hRL : ∀ P t, R P t → RunLinksOK p P t) (hRT : ∀ P t, R P t → TreeAt p P t)
    (ho : OpTreeOK p) (hO : OpTakeTOK p R) (hD : DeadTakenLiveOK p R) : TakeBackOKUnder p R := by
  intro ts tx hw hr noops w hrun
  obtain ⟨z, top, hz, htop, hops⟩ := runOps_ok p _ _ _ _ noops w hrun
  have hI := takeInvT_reached p R hO ho ts tx hw hr (hRT _ _ hr) z top hz htop tx.ops []
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

/-- The induction over the runs with `OpTakeTOK` (`runTree_joint`). -/
theorem runTree_jointT (p : Params) (hM : 2 ≤ p.M) (Q : Struct BVal → Time → Prop)
    (hQ0 : Q (initStruct p) 0)
    (hQs : ∀ ts tx, Within p (ts ++ [tx]) → RunTreeQ p Q (treeRun p ts) ts.length →
      RunLinksOK p (treeRun p (ts ++ [tx])) (ts.length + 1) →
      TreeAt p (treeRun p (ts ++ [tx])) (ts.length + 1) →
      Q (treeRun p (ts ++ [tx])) (ts.length + 1))
    (ho : OpTreeOK p) (hO : OpTakeTOK p (RunTreeQ p Q)) (hD : DeadTakenLiveOK p (RunTreeQ p Q)) :
    ∀ ts, Within p ts → RunTreeQ p Q (treeRun p ts) ts.length := by
  have hTB : TakeBackOKUnder p (RunTreeQ p Q) :=
    takeBackOKUnder_of_opsT p _ (fun _ _ h => h.1) (fun _ _ h => h.2.1) ho hO hD
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
      have hT := treeAt_step p ho (ts.take n) ts[n] hwn hr.2.1
        (commitLiftAt_of_links p (ts.take n) ts[n] hwn hr.1)
      have hQ := hQs (ts.take n) ts[n] hwn hr hL hT
      rw [htake]
      rw [hlen] at hL hT hQ
      exact ⟨hL, hT, hQ⟩
  have h := hk ts.length (Nat.le_refl _)
  rwa [List.take_length] at h

/-- TP7's take-back statement from the premises of `runTree_jointT`. -/
theorem takeBackOK_of_jointT (p : Params) (hM : 2 ≤ p.M) (Q : Struct BVal → Time → Prop)
    (hQ0 : Q (initStruct p) 0)
    (hQs : ∀ ts tx, Within p (ts ++ [tx]) → RunTreeQ p Q (treeRun p ts) ts.length →
      RunLinksOK p (treeRun p (ts ++ [tx])) (ts.length + 1) →
      TreeAt p (treeRun p (ts ++ [tx])) (ts.length + 1) →
      Q (treeRun p (ts ++ [tx])) (ts.length + 1))
    (ho : OpTreeOK p) (hO : OpTakeTOK p (RunTreeQ p Q)) (hD : DeadTakenLiveOK p (RunTreeQ p Q)) :
    TakeBackOKUnder p (RunLinksOK p) := by
  intro ts tx hw _
  have hj := runTree_jointT p hM Q hQ0 hQs ho hO hD ts (within_snoc_prefix p ts tx hw)
  exact takeBackOKUnder_of_opsT p _ (fun _ _ h => h.1) (fun _ _ h => h.2.1) ho hO hD ts tx hw hj

end SIS.Tree
