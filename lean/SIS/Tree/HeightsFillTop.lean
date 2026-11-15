/-
The joint route without `hHL` (bergdb 024-12, 024-22 section 11.1): one induction
along the transaction carries `PutInv`, the ranges, the fill, the heights, the
writer's tree and the take-back's node facts (`jointHtJ_reachedJ`), so `TakeJ2` is
at hand at every delete's start, and putinv2's `upHolderLive_of_J2` replaces `hHL`
in the stop node's cascade (HeightsFillHolder.lean). The top theorem on this route
is `invGetScanOK_merges` (CollapseCommuteTop.lean).
-/
import SIS.Tree.HeightsFillHolder

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- The take-back's state facts, the heights' facts and the fill at a state. -/
def SJ (p : Params) (ts : List Tx) (tx : Tx) (w : W) : Prop :=
  TakeS4 p ts tx w ∧ HtStartAt p ts tx w ∧ LiveCountsW p ts w

/-- `OpDelChk2OKR` with the take-back's node facts at the delete's start too. -/
def OpDelChk2ORJ (p : Params) (R : Struct BVal → Time → Prop) : Prop :=
  ∀ ts tx, Within p (ts ++ [tx]) → R (treeRun p ts) ts.length → ∀ z top,
    lastTop (view (treeSpec p) (treeRun p ts) ts.length) = some z →
    topOf p (ctxOf p ts).view z = .ok top →
    ∀ pre key post, tx.ops = pre ++ Op.del key :: post →
    ∀ r w, (pre.mapM putKv) (ctxOf p ts) (wInit tx top) = .ok (r, w) →
    PutInv (ctxOf p ts) (viewOf (treeRun p ts)) w →
    RangeOrder (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) w.top.rootKey →
    LiveCounts p (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) w.top.rootKey →
    HtInv (htOracleOf p (treeRun p ts)) tx.base (ctxOf p ts) w →
    J2At p (treeRun p ts) (ts.length + 1) tx.base w →
    ∀ r' v, putKv (.del key) (ctxOf p ts) w = .ok (r', v) →
      putKvDelChk2 key (ctxOf p ts) w = .ok (r', v)

set_option maxHeartbeats 1600000 in
/-- `jointHt_reached` with the writer's tree and the take-back's node facts
(`J2At`) too: the take-back's step (`OpJ2OK`, putinv's) with S the take-back's
state facts, the heights' and the fill, and the delete with the merges given
the take-back's node facts at its start (`hchk` given them too). -/
theorem jointHtJ_reachedJ (p : Params) (R : Struct BVal → Time → Prop) (hm : p.merges = true)
    (hM : 2 ≤ p.M) (hM4 : 4 ≤ p.M) (hRB : BaseStartOK p R)
    (hRL : ∀ P t, R P t → RunLinksOK p P t) (hRT : ∀ P t, R P t → TreeAt p P t)
    (hRI : ∀ P t, R P t → InvOK p P t) (hRP : ∀ P t, R P t → PointersOK P)
    (hRK : ∀ P t, R P t → KindsAllOK p P) (hRH : ∀ P t, R P t → HeightAllOK p P t)
    (hdel : TakeBelowFuelDelOK p)
    (hTp : OpCaseOK p R (QPut (QTree p)) AnyOp) (hPp : OpCaseOK p R (QPut (QPutInv p)) AnyOp)
    (hOp : OpCaseOK p R (QPut (QRange p)) AnyOp)
    (hTd : OpCaseOKJ p R (QTree p) DelMergeCaseL) (hPd : OpCaseOKJ p R (QPutInv p) DelMergeCaseL)
    (hOd : OpCaseOKJ p R (QRange p) DelMergeCaseL) (hJ2O : OpJ2OK p R (SJ p))
    (hLv : OpCaseOK p R (QLive p) AnyOp) (hchk : OpDelChk2ORJ p R)
    (ts : List Tx) (tx : Tx) (hw : Within p (ts ++ [tx])) (hr : R (treeRun p ts) ts.length)
    (z : NodeId) (top : Top)
    (hz : lastTop (view (treeSpec p) (treeRun p ts) ts.length) = some z)
    (htop : topOf p (ctxOf p ts).view z = .ok top) :
    ∀ pre post, tx.ops = pre ++ post → ∀ r w,
      (pre.mapM putKv) (ctxOf p ts) (wInit tx top) = .ok (r, w) →
      PutInv (ctxOf p ts) (viewOf (treeRun p ts)) w ∧
      RangeOrder (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) w.top.rootKey ∧
      LiveCounts p (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) w.top.rootKey ∧
      HtInv (htOracleOf p (treeRun p ts)) tx.base (ctxOf p ts) w ∧
      WriterTreeOK p (treeRun p ts) (ts.length + 1) w ∧ J2At p (treeRun p ts) (ts.length + 1) tx.base w := by
  intro pre
  suffices hk : ∀ k, ∀ pre : List Op, pre.length = k → ∀ post, tx.ops = pre ++ post → ∀ r w,
      (pre.mapM putKv) (ctxOf p ts) (wInit tx top) = .ok (r, w) →
      PutInv (ctxOf p ts) (viewOf (treeRun p ts)) w ∧
      RangeOrder (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) w.top.rootKey ∧
      LiveCounts p (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) w.top.rootKey ∧
      HtInv (htOracleOf p (treeRun p ts)) tx.base (ctxOf p ts) w ∧
      WriterTreeOK p (treeRun p ts) (ts.length + 1) w ∧ J2At p (treeRun p ts) (ts.length + 1) tx.base w
    from hk pre.length pre rfl
  have hR := hRL _ _ hr
  have hvo := viewHtOK_of_run p ts tx hw hR (hRK _ _ hr) (hRH _ _ hr)
  intro k
  induction k with
  | zero =>
    intro pre hl _ _ r w h
    have hnil : pre = [] := List.eq_nil_of_length_eq_zero hl
    subst hnil
    simp only [List.mapM_nil, pure, ReaderT.pure, StateT.pure, Except.pure, Except.ok.injEq,
      Prod.mk.injEq] at h
    rw [← h.2]
    exact ⟨putInv_init p ts tx hw hR (hRT _ _ hr) (hRI _ _ hr) z top hz htop,
      rangeOrder_init p ts tx (hRI _ _ hr) z top hz htop,
      liveCounts_init p ts tx (hRI _ _ hr) z top hz htop, htInv_start _ _ _ top,
      writerTreeOK_init p ts tx z top hz htop (hRT _ _ hr),
      (takeInvJ_init p ts tx hw hR top (hRB ts tx hw hr)).2⟩
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
          obtain ⟨hI1, hR1, hL1, hH1, hW1, hJ1⟩ := ih pre' hl' (op :: post) hsplit' r1 w1 h1
          have hbk := putBook_reached p ts tx hw hR z top htop pre' r1 w1 h1
          have hB := putBase_of_run p ts tx hw hR
          have hHS := htStart_of_ht p R hRL hRK hRH hdel ts tx hw hr z top hz htop pre'
            (op :: post) hsplit' r1 w1 h1 hH1
          have hMF1 := stateOK_madeFor p hM4 R hRL ts tx hw hr z top hz htop pre' (op :: post) hsplit' r1 w1 h1
          have hSJ : SJ p ts tx w1 :=
            ⟨⟨⟨⟨⟨hI1, leafVals_reached p hM ts tx hw top pre' (op :: post) hsplit' r1 w1 h1 (hRP _ _ hr)
              (hRK _ _ hr)⟩, base_le_next_reached p hM ts tx hw top pre' (op :: post) hsplit' r1 w1 h1
              (hRP _ _ hr) (hRK _ _ hr)⟩, hR1⟩, segFits_of_htStart p ts tx w1 hHS, hMF1⟩, hHS, hL1⟩
          have hJ2 := hJ2O ts tx hw hr z top hz htop pre' op post hsplit' r1 w1 h1 hW1 hSJ hJ1
          rw [← h.2]
          cases op with
          | put key hv0 =>
            have hne : ∀ key', Op.put key hv0 ≠ .del key' := fun _ he => by cases he
            have hT2 : WriterTreeOK p (treeRun p ts) (ts.length + 1) w2 :=
              hTp ts tx hw hr z top hz htop pre' _ post hsplit' r1 w1 h1 hI1 hR1 trivial a w2 h2 hne
            have hI2 := hPp ts tx hw hr z top hz htop pre' _ post hsplit' r1 w1 h1 hI1 hR1 trivial a w2
              h2 hne hT2
            have hR2 := hOp ts tx hw hr z top hz htop pre' _ post hsplit' r1 w1 h1 hI1 hR1 trivial a w2
              h2 hne hT2
            have hL2 := hLv ts tx hw hr z top hz htop pre' _ post hsplit' r1 w1 h1 hI1 hR1 trivial a w2
              h2 hT2 hL1
            have hH2 := (ht_putKv_put tx.base (appendFrameOK tx.base) key hv0 (ctxOf p ts) w1 hvo
              (by simp [ctxOf]) hbk.book hH1 hM hB.wf hbk.klongs a w2 h2).2.1
            exact ⟨hI2, hR2, hL2, hH2, hT2, hJ2 a w2 h2 hT2⟩
          | del key =>
            have hSt : StartJ p ts tx w1 := ⟨hHS, hJ1, hMF1⟩
            have hC : DelMergeCaseL (ctxOf p ts) (viewOf (treeRun p ts)) w1 (Op.del key) :=
              ⟨⟨key, rfl, hm⟩, hL1⟩
            have hT2 : WriterTreeOK p (treeRun p ts) (ts.length + 1) w2 :=
              hTd ts tx hw hr z top hz htop pre' _ post hsplit' r1 w1 h1 hSt hI1 hR1 hC a w2 h2
            have hI2 := hPd ts tx hw hr z top hz htop pre' _ post hsplit' r1 w1 h1 hSt hI1 hR1 hC a w2
              h2 hT2
            have hR2 := hOd ts tx hw hr z top hz htop pre' _ post hsplit' r1 w1 h1 hSt hI1 hR1 hC a w2
              h2 hT2
            have hL2 := hLv ts tx hw hr z top hz htop pre' _ post hsplit' r1 w1 h1 hI1 hR1 trivial a w2
              h2 hT2 hL1
            have hc2 := hchk ts tx hw hr z top hz htop pre' key post hsplit' r1 w1 h1 hI1 hR1 hL1 hH1
              hJ1 a w2 h2
            obtain ⟨-, hk, -, hki⟩ := kd_contextR p hM ts tx (hRP _ _ hr) (hRK _ _ hr) hw top pre'
              (Op.del key :: post) hsplit' r1 w1 h1
            have hH2 := (ht_putKvDelChk2 tx.base key (ctxOf p ts) w1 hvo (by simp [ctxOf])
              hHS.2.1 hbk.book hH1 hbk.klongs hk hki (by simpa [ctxOf] using hM) a w2 hc2).2.1
            exact ⟨hI2, hR2, hL2, hH2, hT2, hJ2 a w2 h2 hT2⟩


/-- `jointHtJ_reachedJ` with `hchk` at the deletes whose start has `PutInv`, the
ranges, the fill and the heights. -/
theorem jointHtJ_reached (p : Params) (R : Struct BVal → Time → Prop) (hm : p.merges = true)
    (hM : 2 ≤ p.M) (hM4 : 4 ≤ p.M) (hRB : BaseStartOK p R)
    (hRL : ∀ P t, R P t → RunLinksOK p P t) (hRT : ∀ P t, R P t → TreeAt p P t)
    (hRI : ∀ P t, R P t → InvOK p P t) (hRP : ∀ P t, R P t → PointersOK P)
    (hRK : ∀ P t, R P t → KindsAllOK p P) (hRH : ∀ P t, R P t → HeightAllOK p P t)
    (hdel : TakeBelowFuelDelOK p)
    (hTp : OpCaseOK p R (QPut (QTree p)) AnyOp) (hPp : OpCaseOK p R (QPut (QPutInv p)) AnyOp)
    (hOp : OpCaseOK p R (QPut (QRange p)) AnyOp)
    (hTd : OpCaseOKJ p R (QTree p) DelMergeCaseL) (hPd : OpCaseOKJ p R (QPutInv p) DelMergeCaseL)
    (hOd : OpCaseOKJ p R (QRange p) DelMergeCaseL) (hJ2O : OpJ2OK p R (SJ p))
    (hLv : OpCaseOK p R (QLive p) AnyOp) (hchk : OpDelChk2OKR p R)
    (ts : List Tx) (tx : Tx) (hw : Within p (ts ++ [tx])) (hr : R (treeRun p ts) ts.length)
    (z : NodeId) (top : Top)
    (hz : lastTop (view (treeSpec p) (treeRun p ts) ts.length) = some z)
    (htop : topOf p (ctxOf p ts).view z = .ok top) :
    ∀ pre post, tx.ops = pre ++ post → ∀ r w,
      (pre.mapM putKv) (ctxOf p ts) (wInit tx top) = .ok (r, w) →
      PutInv (ctxOf p ts) (viewOf (treeRun p ts)) w ∧
      RangeOrder (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) w.top.rootKey ∧
      LiveCounts p (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) w.top.rootKey ∧
      HtInv (htOracleOf p (treeRun p ts)) tx.base (ctxOf p ts) w ∧
      WriterTreeOK p (treeRun p ts) (ts.length + 1) w ∧ J2At p (treeRun p ts) (ts.length + 1) tx.base w :=
  jointHtJ_reachedJ p R hm hM hM4 hRB hRL hRT hRI hRP hRK hRH hdel hTp hPp hOp hTd hPd hOd hJ2O hLv
    (fun ts tx hw hr z top hz htop pre key post hs r w hpre hI hRO hL hH _ =>
      hchk ts tx hw hr z top hz htop pre key post hs r w hpre hI hRO hL hH) ts tx hw hr z top hz htop

theorem mapM_snoc_ok (c : Ctx) (w0 : W) (pre : List Op) (op : Op) (r : List Bool) (w : W) (a : Bool)
    (w' : W) (h1 : (pre.mapM putKv) c w0 = .ok (r, w)) (h2 : putKv op c w = .ok (a, w')) :
    ((pre ++ [op]).mapM putKv) c w0 = .ok (r ++ [a], w') := by
  rw [List.mapM_append]
  simp only [List.mapM_cons, List.mapM_nil, bind, ReaderT.bind, StateT.bind, Except.bind, h1, h2, pure,
    ReaderT.pure, StateT.pure, Except.pure]


end SIS.Tree
