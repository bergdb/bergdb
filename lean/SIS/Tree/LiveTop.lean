/-
The joint route's top theorem with `l4` reduced to its open case at one delete of the
induction's runs (bergdb 030-01, step 1): `invGetScanOK_merges_l4L`, premises `hp`,
`hth`, `htbL` and `l4L` (`LiveDelSL`), as `htbL` reduced `htb` (bergdb 025-05, step 9).
The joint induction (`jointHtJ_reachedJSL` and its wrappers, near-copies of
`jointHtJ_reachedJS` and its wrappers in HeightsFillTop.lean and StratumChk.lean) takes the
delete's live case given the facts at the delete's start (`LiveDelS`); `l4` gives `l4L`
(`liveDelSL_of`), so `invGetScanOK_merges_tbL` is a corollary
(`invGetScanOK_merges_tbL_of_l4L`). The old induction, its wrappers and
`invGetScanOK_merges_tbL` become corollaries of these at a close step.
-/
import SIS.Tree.DeadTop

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- `QLive` at the deletes of case P of the runs of R whose start has the joint
induction's facts (as `TakeBelowFuelDelS` for `htb`). -/
def LiveDelS (p : Params) (R : Struct BVal → Time → Prop) (P : Ctx → View BVal → W → Op → Prop) : Prop :=
  ∀ ts tx, Within p (ts ++ [tx]) → R (treeRun p ts) ts.length → ∀ z top,
    lastTop (view (treeSpec p) (treeRun p ts) ts.length) = some z →
    topOf p (ctxOf p ts).view z = .ok top →
    ∀ pre key post, tx.ops = pre ++ Op.del key :: post →
    ∀ r w, (pre.mapM putKv) (ctxOf p ts) (wInit tx top) = .ok (r, w) →
    PutInv (ctxOf p ts) (viewOf (treeRun p ts)) w →
    RangeOrder (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) w.top.rootKey →
    LiveCounts p (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) w.top.rootKey →
    HtInv (htOracleOf p (treeRun p ts)) tx.base (ctxOf p ts) w →
    WriterTreeOK p (treeRun p ts) (ts.length + 1) w →
    J2At p (treeRun p ts) (ts.length + 1) tx.base w →
    P (ctxOf p ts) (viewOf (treeRun p ts)) w (Op.del key) →
    WriterWP (putKv (Op.del key)) (ctxOf p ts) w (fun _ w' => QLive p ts (Op.del key) w w')

/-- `l4`'s reduced form: its open case at the induction's runs. -/
def LiveDelSL (p : Params) : Prop := LiveDelS p (RunTreeQ p (LatestQD p)) DelMergeOpenCase

/-- `l4` gives its reduced form. -/
theorem liveDelSL_of (p : Params) (l4 : OpCaseOK p (RunOK p) (QLive p) DelMergeOpenCase) :
    LiveDelSL p :=
  fun ts tx hw hr z top hz htop pre _ post hs r w hpre hI hRo _ _ _ _ hC =>
    l4 ts tx hw (runOK_of_runTreeQD p _ _ hr) z top hz htop pre _ post hs r w hpre hI hRo hC

/-- The open case gives every delete with the merges: the noop, the key with no
leaf and (4a) are proved for any R. -/
theorem liveDelS_merge_of_open (p : Params) (R : Struct BVal → Time → Prop)
    (hRL : ∀ P t, R P t → RunLinksOK p P t) (h : LiveDelS p R DelMergeOpenCase) :
    LiveDelS p R DelMergeCase := by
  intro ts tx hw hr z top hz htop pre key post hs r w hpre hI hRo hL hH hT hJ hC
  by_cases hrf : DelRoomFillCase (ctxOf p ts) (viewOf (treeRun p ts)) w (Op.del key)
  · exact liveCase_delRoomFill p R hRL ts tx hw hr z top hz htop pre _ post hs r w hpre hI hRo hrf
  by_cases hn : DelNoopM (ctxOf p ts) (viewOf (treeRun p ts)) w (Op.del key)
  · exact opCaseOK_delNoop p R (QLive p) (keptByReads_live p) ts tx hw hr z top hz htop pre _ post hs
      r w hpre hI hRo hn
  by_cases hl : DelNoLeafM (ctxOf p ts) (viewOf (treeRun p ts)) w (Op.del key)
  · exact opCaseOK_delNoLeaf p R (QLive p) (keptByReads_live p) ts tx hw hr z top hz htop pre _ post hs
      r w hpre hI hRo hl
  exact h ts tx hw hr z top hz htop pre key post hs r w hpre hI hRo hL hH hT hJ ⟨⟨hC, hrf⟩, hn, hl⟩

set_option maxHeartbeats 1600000 in
/-- `jointHtJ_reachedJS` (HeightsFillTop.lean) with the live case split: the puts as
before, the deletes with the merges given the induction's facts at their start
(bergdb 030-01, step 1). -/
theorem jointHtJ_reachedJSL (p : Params) (R : Struct BVal → Time → Prop) (hm : p.merges = true)
    (hM : 2 ≤ p.M) (hRB : BaseStartOK p R)
    (hRL : ∀ P t, R P t → RunLinksOK p P t) (hRT : ∀ P t, R P t → TreeAt p P t)
    (hRI : ∀ P t, R P t → InvOK p P t) (hRP : ∀ P t, R P t → PointersOK P)
    (hRK : ∀ P t, R P t → KindsAllOK p P) (hRH : ∀ P t, R P t → HeightAllOK p P t)
    (S St : List Tx → Tx → W → Prop) (hS : JointStartOK p R S) (hSt : JointStartOK p R St)
    (hTp : OpCaseOK p R (QPut (QTree p)) AnyOp) (hPp : OpCaseOK p R (QPut (QPutInv p)) AnyOp)
    (hOp : OpCaseOK p R (QPut (QRange p)) AnyOp)
    (hTd : OpCaseOKJS p R St (QTree p) DelMergeCaseL) (hPd : OpCaseOKJS p R St (QPutInv p) DelMergeCaseL)
    (hOd : OpCaseOKJS p R St (QRange p) DelMergeCaseL) (hJ2O : OpJ2OK p R S)
    (hLvP : OpCaseOK p R (QPut (QLive p)) AnyOp) (hLvD : LiveDelS p R DelMergeCase)
    (hchk : OpDelChk2ORJ p R)
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
          have hSJ : S ts tx w1 :=
            hS ts tx hw hr z top hz htop pre' (op :: post) hsplit' r1 w1 h1 hI1 hR1 hL1 hH1 hJ1
          have hStw : St ts tx w1 :=
            hSt ts tx hw hr z top hz htop pre' (op :: post) hsplit' r1 w1 h1 hI1 hR1 hL1 hH1 hJ1
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
            have hL2 := hLvP ts tx hw hr z top hz htop pre' _ post hsplit' r1 w1 h1 hI1 hR1 trivial a w2
              h2 hne hT2 hL1
            have hH2 := (ht_putKv_put tx.base (appendFrameOK tx.base) key hv0 (ctxOf p ts) w1 hvo
              (by simp [ctxOf]) hbk.book hH1 hM hB.wf hbk.klongs a w2 h2).2.1
            exact ⟨hI2, hR2, hL2, hH2, hT2, hJ2 a w2 h2 hT2⟩
          | del key =>
            have hC : DelMergeCaseL (ctxOf p ts) (viewOf (treeRun p ts)) w1 (Op.del key) :=
              ⟨⟨key, rfl, hm⟩, hL1⟩
            have hT2 : WriterTreeOK p (treeRun p ts) (ts.length + 1) w2 :=
              hTd ts tx hw hr z top hz htop pre' _ post hsplit' r1 w1 h1 hStw hI1 hR1 hC a w2 h2
            have hI2 := hPd ts tx hw hr z top hz htop pre' _ post hsplit' r1 w1 h1 hStw hI1 hR1 hC a w2
              h2 hT2
            have hR2 := hOd ts tx hw hr z top hz htop pre' _ post hsplit' r1 w1 h1 hStw hI1 hR1 hC a w2
              h2 hT2
            have hL2 := hLvD ts tx hw hr z top hz htop pre' key post hsplit' r1 w1 h1 hI1 hR1 hL1 hH1 hW1 hJ1
              ⟨key, rfl, hm⟩ a w2 h2 hT2 hL1
            have hc2 := hchk ts tx hw hr z top hz htop pre' key post hsplit' r1 w1 h1 hI1 hR1 hL1 hH1
              hJ1 a w2 h2
            obtain ⟨-, hk, -, hki⟩ := kd_contextR p hM ts tx (hRP _ _ hr) (hRK _ _ hr) hw top pre'
              (Op.del key :: post) hsplit' r1 w1 h1
            have hH2 := (ht_putKvDelChk2 tx.base key (ctxOf p ts) w1 hvo (by simp [ctxOf])
              hB.wf hbk.book hH1 hbk.klongs hk hki (by simpa [ctxOf] using hM) a w2 hc2).2.1
            exact ⟨hI2, hR2, hL2, hH2, hT2, hJ2 a w2 h2 hT2⟩

/-- The old form's live case gives the deletes' part (for the close step). -/
theorem liveDelS_of_any (p : Params) (R : Struct BVal → Time → Prop) (P : Ctx → View BVal → W → Op → Prop)
    (hLv : OpCaseOK p R (QLive p) AnyOp) : LiveDelS p R P :=
  fun ts tx hw hr z top hz htop pre _ post hs r w hpre hI hRo _ _ _ _ _ =>
    hLv ts tx hw hr z top hz htop pre _ post hs r w hpre hI hRo trivial

/-- The old form's live case gives the puts' part (for the close step). -/
theorem qput_of_any (p : Params) (R : Struct BVal → Time → Prop)
    (hLv : OpCaseOK p R (QLive p) AnyOp) : OpCaseOK p R (QPut (QLive p)) AnyOp :=
  fun ts tx hw hr z top hz htop pre op post hs r w hpre hI hRo hP =>
    writerWP_mono (hLv ts tx hw hr z top hz htop pre op post hs r w hpre hI hRo hP) (fun _ _ h _ => h)

/-- `jointHtJ_reached0` (Stratum.lean) with the live case split. -/
theorem jointHtJ_reached0L (p : Params) (R : Struct BVal → Time → Prop) (hm : p.merges = true)
    (hM : 2 ≤ p.M) (hM4 : 4 ≤ p.M) (hRB : BaseStartOK p R)
    (hRL : ∀ P t, R P t → RunLinksOK p P t) (hRT : ∀ P t, R P t → TreeAt p P t)
    (hRI : ∀ P t, R P t → InvOK p P t) (hRP : ∀ P t, R P t → PointersOK P)
    (hRK : ∀ P t, R P t → KindsAllOK p P) (hRH : ∀ P t, R P t → HeightAllOK p P t)
    (hTp : OpCaseOK p R (QPut (QTree p)) AnyOp) (hPp : OpCaseOK p R (QPut (QPutInv p)) AnyOp)
    (hOp : OpCaseOK p R (QPut (QRange p)) AnyOp)
    (hTd : OpCaseOKJS p R (StartJ0 p) (QTree p) DelMergeCaseL)
    (hPd : OpCaseOKJS p R (StartJ0 p) (QPutInv p) DelMergeCaseL)
    (hOd : OpCaseOKJS p R (StartJ0 p) (QRange p) DelMergeCaseL) (hJ2O : OpJ2OK p R (SJ0 p))
    (hLvP : OpCaseOK p R (QPut (QLive p)) AnyOp) (hLvD : LiveDelS p R DelMergeCase) (hchk : OpDelChk2ORJ p R)
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
  jointHtJ_reachedJSL p R hm hM hRB hRL hRT hRI hRP hRK hRH (SJ0 p) (StartJ0 p)
    (fun ts tx hw hr z top hz htop pre post hs r w hpre hI hRo hL hH _ =>
      ⟨⟨⟨⟨⟨hI, leafVals_reached p hM ts tx hw top pre post hs r w hpre (hRP _ _ hr) (hRK _ _ hr)⟩,
        base_le_next_reached p hM ts tx hw top pre post hs r w hpre (hRP _ _ hr) (hRK _ _ hr)⟩, hRo⟩,
        stateOK_madeFor p hM4 R hRL ts tx hw hr z top hz htop pre post hs r w hpre⟩,
        htStart0_of_ht p R hRL hRK hRH ts tx hw hr z top htop pre r w hpre hH, hL⟩)
    (fun ts tx hw hr z top hz htop pre post hs r w hpre _ _ _ hH hJ =>
      ⟨htStart0_of_ht p R hRL hRK hRH ts tx hw hr z top htop pre r w hpre hH, hJ,
        stateOK_madeFor p hM4 R hRL ts tx hw hr z top hz htop pre post hs r w hpre⟩)
    hTp hPp hOp hTd hPd hOd hJ2O hLvP hLvD hchk ts tx hw hr z top hz htop

/-- `jointHtJ_reachedT` (StratumSteps.lean) with the live case split. -/
theorem jointHtJ_reachedTL (p : Params) (R : Struct BVal → Time → Prop) (hm : p.merges = true)
    (hM : 2 ≤ p.M) (hM4 : 4 ≤ p.M) (hsa2 : 2 ≤ p.splitAbove) (hcap : 1 ≤ p.mergeMax)
    (hRB : BaseStartOK p R)
    (hRL : ∀ P t, R P t → RunLinksOK p P t) (hRT : ∀ P t, R P t → TreeAt p P t)
    (hRI : ∀ P t, R P t → InvOK p P t) (hRP : ∀ P t, R P t → PointersOK P)
    (hRK : ∀ P t, R P t → KindsAllOK p P) (hRH : ∀ P t, R P t → HeightAllOK p P t)
    (hTp : OpCaseOK p R (QPut (QTree p)) AnyOp) (hPp : OpCaseOK p R (QPut (QPutInv p)) AnyOp)
    (hOp : OpCaseOK p R (QPut (QRange p)) AnyOp) (hS : DelStepsTJA p R)
    (hLvP : OpCaseOK p R (QPut (QLive p)) AnyOp) (hLvD : LiveDelS p R DelMergeCase) (hchk : OpDelChk2ORJ p R)
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
  have hT := opCaseOKJ0_treeInvRange_delMergeT p R hM hS hsa2 hcap hRP hRK
  jointHtJ_reached0L p R hm hM hM4 hRB hRL hRT hRI hRP hRK hRH hTp hPp hOp hT.1 hT.2.1 hT.2.2
    (opJ2OK0_of_T p R hm hM hS hsa2 hcap hRL hRP hRK) hLvP hLvD hchk ts tx hw hr z top hz htop

/-- `jointHtJ_reachedS` (StratumCasc.lean) with the live case split. -/
theorem jointHtJ_reachedSL (p : Params) (R : Struct BVal → Time → Prop) (hm : p.merges = true)
    (hM : 2 ≤ p.M) (hM4 : 4 ≤ p.M) (hsa2 : 2 ≤ p.splitAbove) (hcap : 1 ≤ p.mergeMax)
    (hRB : BaseStartOK p R)
    (hRL : ∀ P t, R P t → RunLinksOK p P t) (hRT : ∀ P t, R P t → TreeAt p P t)
    (hRI : ∀ P t, R P t → InvOK p P t) (hRP : ∀ P t, R P t → PointersOK P)
    (hRK : ∀ P t, R P t → KindsAllOK p P) (hRH : ∀ P t, R P t → HeightAllOK p P t)
    (hTp : OpCaseOK p R (QPut (QTree p)) AnyOp) (hPp : OpCaseOK p R (QPut (QPutInv p)) AnyOp)
    (hOp : OpCaseOK p R (QPut (QRange p)) AnyOp)
    (hLvP : OpCaseOK p R (QPut (QLive p)) AnyOp) (hLvD : LiveDelS p R DelMergeCase) (hchk : OpDelChk2ORJ p R)
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
  jointHtJ_reachedTL p R hm hM hM4 hsa2 hcap hRB hRL hRT hRI hRP hRK hRH hTp hPp hOp
    (delStepsTJA_holds p R hM hsa2 hRL hRP hRK) hLvP hLvD hchk ts tx hw hr z top hz htop

/-- `jointHtJ_reached1` (StratumChk.lean) with the live case split. -/
theorem jointHtJ_reached1L (p : Params) (R : Struct BVal → Time → Prop) (hm : p.merges = true)
    (hM : 2 ≤ p.M) (hM4 : 4 ≤ p.M) (hsa2 : 2 ≤ p.splitAbove) (hcap : 1 ≤ p.mergeMax)
    (hRB : BaseStartOK p R)
    (hRL : ∀ P t, R P t → RunLinksOK p P t) (hRT : ∀ P t, R P t → TreeAt p P t)
    (hRI : ∀ P t, R P t → InvOK p P t) (hRP : ∀ P t, R P t → PointersOK P)
    (hRK : ∀ P t, R P t → KindsAllOK p P) (hRH : ∀ P t, R P t → HeightAllOK p P t)
    (hTp : OpCaseOK p R (QPut (QTree p)) AnyOp) (hPp : OpCaseOK p R (QPut (QPutInv p)) AnyOp)
    (hOp : OpCaseOK p R (QPut (QRange p)) AnyOp) (hLvP : OpCaseOK p R (QPut (QLive p)) AnyOp)
    (hLvD : LiveDelS p R DelMergeCase)
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
  jointHtJ_reachedSL p R hm hM hM4 hsa2 hcap hRB hRL hRT hRI hRP hRK hRH hTp hPp hOp hLvP hLvD
    (opDelChk2ORJ_T p R hm hM4 hsa2 hcap hRL hRP hRK) ts tx hw hr z top hz htop

set_option maxHeartbeats 3200000 in
/-- The joint route's top theorem with `l4` reduced to its open case at the deletes of
the induction's runs whose start has the first stratum's facts (bergdb 030-01, step 1):
TP7, TP10 and TP11 for Java's parameters from `hp`, `hth`, `htbL` and `l4L`. The proof is
`invGetScanOK_merges_tbL`'s with the joint induction `jointHtJ_reached1L`, whose delete
case takes `l4L` with the open case's proved cases added (`liveDelS_merge_of_open`); after
the induction, `hLv` comes from its conclusion. -/
theorem invGetScanOK_merges_l4L (p : Params) (hp : MergeParamsOK p)
    (hth : 2 ≤ p.theta ∨ p.theta = 0)
    (htbL : TakeBelowFuelDelSL p)
    (l4L : LiveDelSL p) :
    InvPreserved p ∧ GetOK p ∧ ScanOK p ∧ LatestGetOK p ∧ LatestScanOK p := by
  have hp' := hp
  unfold MergeParamsOK at hp'
  have hM := mergeParamsOK_M p hp
  have hM4 := four_le_M p hp
  have hm : p.merges = true := by
    unfold Params.merges; simp only [decide_eq_true_eq]; omega
  have hsa : 2 ≤ p.splitAbove := by omega
  have hcap : 1 ≤ p.mergeMax := by omega
  have hRL : ∀ P t, RunOK p P t → RunLinksOK p P t := fun _ _ h => h.1
  have hR : ∀ P t, RunTreeQ p (LatestQD p) P t → RunOK p P t := runOK_of_runTreeQD p
  have hRL' : ∀ P t, RunTreeQ p (LatestQD p) P t → RunLinksOK p P t := fun _ _ h => h.1
  have hRT' : ∀ P t, RunTreeQ p (LatestQD p) P t → TreeAt p P t := fun _ _ h => h.2.1
  have hRI' : ∀ P t, RunTreeQ p (LatestQD p) P t → InvOK p P t := fun _ _ h => h.2.2.1.1
  have hRP' : ∀ P t, RunTreeQ p (LatestQD p) P t → PointersOK P := fun _ _ h => h.1.1
  have hRK' : ∀ P t, RunTreeQ p (LatestQD p) P t → KindsAllOK p P := fun _ _ h => h.2.2.1.2.2.1
  have hRH' : ∀ P t, RunTreeQ p (LatestQD p) P t → HeightAllOK p P t :=
    fun _ _ h => h.2.2.1.2.2.2.1
  have hchk5 : OpDelChk5OKL p := opDelChk5OKR_T p _ hM4 hsa hcap hm hRL' hRP' hRK'
  have hLvD : LiveDelS p (RunTreeQ p (LatestQD p)) DelMergeCase := liveDelS_merge_of_open p _ hRL' l4L
  -- the joint induction's cases
  have hLvP := opCaseOK_put_of_cases p _ _ hm (liveCase_putLeafRoom p _)
    (liveCase_putLeafFull p _ hRL' hsa hp)
    (opCaseOK_putNewSeg_of_parts p _ _ (liveCase_putNewSeg1Room p _ (by omega))
      (liveCase_putNewSegsRoom p _ (by omega)) (liveCase_putNewSegFull p _ hRL' (by omega) hsa hp))
  have hTp := opCaseOK_put_of_cases p _ _ hm (treeCase_putLeafRoom p _)
    (treeCase_putLeafFull p _ hRL' hsa)
    (opCaseOK_putNewSeg_of_parts p _ _ (treeCase_putNewSeg1Room p _ (by omega))
      (treeCase_putNewSegsRoom p _ (by omega)) (treeCase_putNewSegFull p _ hRL' (by omega) hsa))
  have hPp := opCaseOK_put_of_cases p _ _ hm (putInvCase_putLeafRoom p _ hRL')
    (putInvCase_putLeafFull p _ hRL' hsa)
    (opCaseOK_putNewSeg_of_parts p _ _ (putInvCase_putNewSeg1Room p _ hRL' (by omega))
      (putInvCase_putNewSegsRoom p _ hRL' (by omega)) (putInvCase_putNewSegFull p _ hRL' (by omega) hsa))
  have hOp := opCaseOK_put_of_cases p _ _ hm (rangeCase_putLeafRoom p _)
    (rangeCase_putLeafFull p _ hRL' hsa)
    (opCaseOK_putNewSeg_of_parts p _ _ (rangeCase_putNewSeg1Room p _ (by omega))
      (rangeCase_putNewSegsRoom p _ (by omega)) (rangeCase_putNewSegFull p _ hRL' (by omega) hsa))
  have hchkR := opDelChk2ORJ_of_chk5 p _ hm hM4 hRL' hchk5
  have joint := jointHtJ_reached1L p _ hm (by omega) hM4 hsa hcap (baseStartOK_runTreeQ p (LatestQD p)) hRL' hRT'
    hRI' hRP' hRK' hRH' hTp hPp hOp hLvP hLvD
  -- from the joint induction: the heights' delete side, the fuel, the cases at every operation
  have hht : OpHtDelOKUnder p (RunTreeQ p (LatestQD p)) := by
    intro ts tx hw hr z top hz htop pre key post hsplit r w hpre hvo hkw hb hwf hi r' v he
    obtain ⟨hI, hRo, hL, _, _, hJ⟩ := joint ts tx hw hr z top hz htop pre (Op.del key :: post) hsplit r w hpre
    have hc := hchkR ts tx hw hr z top hz htop pre key post hsplit r w hpre hI hRo hL hi hJ r' v he
    obtain ⟨-, hk, -, hki⟩ := kd_contextR p (by omega) ts tx (hRP' _ _ hr) (hRK' _ _ hr) hw top pre
      (Op.del key :: post) hsplit r w hpre
    exact (ht_putKvDelChk2 tx.base key (ctxOf p ts) w hvo (by simp [ctxOf]) hkw hb hi hwf hk hki
      (by simpa [ctxOf] using (show 2 ≤ p.M by omega)) r' v hc).2.1
  have htbR : TakeBelowFuelDelR p (RunTreeQ p (LatestQD p)) := by
    intro ts tx hw hr z top hz htop pre key post hs r w hpre a v he x g h hm' hx hv
    obtain ⟨hI, hRo, hL, hH, hT, hJ⟩ := joint ts tx hw hr z top hz htop pre (Op.del key :: post) hs r w hpre
    exact htbL ts tx hw hr z top hz htop pre key post hs r w hpre hI hRo hL hH hT hJ a v he x g h hm' hx hv
  have hfitQ : TxSegFitsOK p (RunTreeQ p (LatestQD p)) :=
    txSegFitsOK_of_takeBelowDelRHUR p (by omega) _ hRL' hRK' hRH' hht htbR
  have hnext : ∀ ts tx, Within p (ts ++ [tx]) → RunTreeQ p (LatestQD p) (treeRun p ts) ts.length →
      ∀ z top, lastTop (view (treeSpec p) (treeRun p ts) ts.length) = some z →
      topOf p (ctxOf p ts).view z = .ok top →
      ∀ pre op post, tx.ops = pre ++ op :: post → ∀ r w,
      (pre.mapM putKv) (ctxOf p ts) (wInit tx top) = .ok (r, w) → ∀ a w', putKv op (ctxOf p ts) w = .ok (a, w') →
      WriterTreeOK p (treeRun p ts) (ts.length + 1) w' ∧
        PutInv (ctxOf p ts) (viewOf (treeRun p ts)) w' ∧
        RangeOrder (wNode p (viewOf (treeRun p ts)) w') (ts.length + 1) w'.top.rootKey := by
    intro ts tx hw hr z top hz htop pre op post hs r w hpre a w' he
    obtain ⟨hI', hR', _, _, hT', _⟩ := joint ts tx hw hr z top hz htop (pre ++ [op]) post (by rw [hs]; simp)
      (r ++ [a]) w' (mapM_snoc_ok _ _ pre op r w a w' hpre he)
    exact ⟨hT', hI', hR'⟩
  have hT : OpCaseOK p (RunTreeQ p (LatestQD p)) (QTree p) AnyOp :=
    fun ts tx hw hr z top hz htop pre op post hs r w hpre _ _ _ a w' he =>
      (hnext ts tx hw hr z top hz htop pre op post hs r w hpre a w' he).1
  have hPI : OpCaseOK p (RunTreeQ p (LatestQD p)) (QPutInv p) AnyOp :=
    fun ts tx hw hr z top hz htop pre op post hs r w hpre _ _ _ a w' he _ =>
      (hnext ts tx hw hr z top hz htop pre op post hs r w hpre a w' he).2.1
  have hO : OpCaseOK p (RunTreeQ p (LatestQD p)) (QRange p) AnyOp :=
    fun ts tx hw hr z top hz htop pre op post hs r w hpre _ _ _ a w' he _ =>
      (hnext ts tx hw hr z top hz htop pre op post hs r w hpre a w' he).2.2
  have hLv : OpCaseOK p (RunTreeQ p (LatestQD p)) (QLive p) AnyOp :=
    fun ts tx hw hr z top hz htop pre op post hs r w hpre _ _ _ a w' he _ _ =>
      (joint ts tx hw hr z top hz htop (pre ++ [op]) post (by rw [hs]; simp)
        (r ++ [a]) w' (mapM_snoc_ok _ _ pre op r w a w' hpre he)).2.2.1
  have hLC : StateOK p (RunTreeQ p (LatestQD p)) (fun ts _ w => LiveCountsW p ts w) :=
    fun ts tx hw hr z top hz htop pre post hs r w hpre =>
      (joint ts tx hw hr z top hz htop pre post hs r w hpre).2.2.1
  have hJ2S : StateOK p (RunTreeQ p (LatestQD p))
      (fun ts tx w => TakeJ2 (ctxOf p ts) (viewOf (treeRun p ts)) tx.base w) :=
    fun ts tx hw hr z top hz htop pre post hs r w hpre =>
      (joint ts tx hw hr z top hz htop pre post hs r w hpre).2.2.2.2.2
  have hMFS := stateOK_madeFor p hM4 (RunTreeQ p (LatestQD p)) hRL'
  -- the delete's steps without `hHL`
  have d4' : OpCaseOK p (RunTreeQ p (LatestQD p)) (QDead p) (fun c base w op =>
      DelMergeCase c base w op ∧ LiveCounts c.p (wNode c.p base w) c.i w.top.rootKey) :=
    fun ts tx hw hr z top hz htop pre op post hops r w hpre hI hRo hP =>
      opCaseOK_dead_delMergeA p _ (delStepsCaseDOK_mergeGR p _ (by omega) hsa hRL' hRP' hRK' hRH' hht htbR
        hLC hJ2S hMFS _) hsa hcap hRP' hRK' hfitQ hth ts tx hw hr z top hz htop pre op post hops
        r w hpre hI hRo hP.1
  have hTL := opCaseOK_L_of_any p _ _ hT
  have hPIL := opCaseOK_L_of_any p _ _ hPI
  have hOL := opCaseOK_L_of_any p _ _ hO
  have hLvL := opCaseOK_L_of_any p _ _ hLv
  have hDdL := opCaseOK_of_cases_mergesL p _ _ hm (deadCase_putLeafRoom p _)
    (deadCase_putLeafFull p _ hRL' hsa hth)
    (opCaseOK_putNewSeg_of_parts p _ _ (deadCase_putNewSeg1Room p _ (by omega))
      (deadCase_putNewSegsRoom p _ (by omega)) (deadCase_putNewSegFull p _ hRL' (by omega) hsa hth)) d4'
  have hDd := opCaseOK_any_of_L p _ hRL' hRT' hRI' hTL hPIL hOL hLvL _ hDdL
  have hJ := runTreeQ_of_mergesSA p (by omega) hsa hcap hm (LatestQD p) (latestQD_init p (by omega))
    (latestQD_snocR p hp hht hT hPI hO hLv hDd)
    (fun _ _ h => h.1.2.1) (fun _ _ h => h.1.2.2.1)
    (opTreeOKUnder_of_cases p _ hRL' hRT' hRI' hT hPI hO)
    (putInvStateOK_of_cases p _ hRL' hRT' hRI' hT hPI hO)
    (rangeStateOK_of_cases p _ hRL' hRT' hRI' hT hPI hO)
    hfitQ hMFS
    (delStepsJ2OKJ_of_openR_noUGR p _ (TakeS4 p) (by omega) hsa hRL' hRP' hRK'
      (fun _ _ _ h => h.1.1.1.1) (fun _ _ _ h => h.1.1.1.2) (fun _ _ _ h => h.1.1.2)
      (fun _ _ _ h => h.1.2) (fun _ _ _ h => h.2.1) (fun _ _ _ h => h.2.2) hRH' hht htbR hLC _)
  have hW : ∀ ts tx, Within p (ts ++ [tx]) → RunOK p (treeRun p ts) ts.length →
      RunTreeQ p (LatestQD p) (treeRun p ts) ts.length :=
    fun ts tx hw _ => hJ ts (within_snoc_prefix p ts tx hw)
  have hP : ∀ ts, Within p ts → PointersOK (treeRun p ts) := fun ts hw => (hJ ts hw).1.1
  have hfit : TxSegFitsOK p (RunOK p) :=
    fun ts tx hw _ => hfitQ ts tx hw (hJ ts (within_snoc_prefix p ts tx hw))
  have hSA : DelStepsOKA p (RunOK p) := fun ts tx hw hr =>
    delStepsOKJ_of_open_noUGR p _ (by omega) hsa hRL' hP hRK' hRH' hht htbR hLC hJ2S hMFS
      (fun ts tx w key v => DelInvA (ctxOf p ts) (viewOf (treeRun p ts)) w key
        (kindOracleOf p (treeRun p ts)) tx.base v) ts tx hw (hW ts tx hw hr)
  have hinv : InvPreserved p :=
    invPreserved_of_latest_pointers p hp (fun ts hw => (hJ ts hw).2.2.1.1) hP
      (fun ts hw => (hJ ts hw).2.2.2)
  have h := getOK_scanOK_of_cases_merges_open p hp hinv (fun ts hw => (hJ ts hw).1)
    (fun ts hw => (hJ ts hw).2.1) hfit
    (opCaseOK_of_within p _ _ hW _ _ (opCaseOK_of_any p _ _ _ hT))
    (opCaseOK_of_within p _ _ hW _ _ (opCaseOK_of_any p _ _ _ hPI))
    (opCaseOK_of_within p _ _ hW _ _ (opCaseOK_of_any p _ _ _ hO))
    (opGetCaseOK_delMergeA p (RunOK p) hSA hsa hcap (by omega) hP hfit)
  exact ⟨hinv, h.1, h.2, latestGetOK_of_getOK p h.1, latestScanOK_of_scanOK p h.2⟩

/-- `invGetScanOK_merges_tbL` (DeadTop.lean) from `invGetScanOK_merges_l4L`: `l4` gives
`l4L`. -/
theorem invGetScanOK_merges_tbL_of_l4L (p : Params) (hp : MergeParamsOK p)
    (hth : 2 ≤ p.theta ∨ p.theta = 0)
    (htbL : TakeBelowFuelDelSL p)
    (l4 : OpCaseOK p (RunOK p) (QLive p) DelMergeOpenCase) :
    InvPreserved p ∧ GetOK p ∧ ScanOK p ∧ LatestGetOK p ∧ LatestScanOK p :=
  invGetScanOK_merges_l4L p hp hth htbL (liveDelSL_of p l4)

end SIS.Tree
