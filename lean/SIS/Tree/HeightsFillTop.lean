/-
The top theorem without `hHL` (bergdb 024-12, 024-22 section 11.1), on the joint
route: one induction along the transaction carries `PutInv`, the ranges, the fill,
the heights, the writer's tree and the take-back's node facts (`jointHtJ_reached`),
so `TakeJ2` is at hand at every delete's start, and putinv2's `upHolderLive_of_J2`
replaces `hHL` in the stop node's cascade (HeightsFillHolder.lean). The operations'
cases at every state follow from the induction (`opCaseOK_of_jointJ`), and the
take-back's run induction and the reading take the delete's steps without `hHL`
(`delStepsJ2OKJ_of_openR`, `delStepsOKJ_of_open`).
-/
import SIS.Tree.HeightsFillHolder

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- The take-back's state facts, the heights' facts and the fill at a state. -/
def SJ (p : Params) (ts : List Tx) (tx : Tx) (w : W) : Prop :=
  TakeS4 p ts tx w ∧ HtStartAt p ts tx w ∧ LiveCountsW p ts w

set_option maxHeartbeats 1600000 in
/-- `jointHt_reached` with the writer's tree and the take-back's node facts
(`J2At`) too: the take-back's step (`OpJ2OK`, putinv's) with S the take-back's
state facts, the heights' and the fill, and the delete with the merges given
the take-back's node facts at its start. -/
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
              a w2 h2
            obtain ⟨-, hk, -, hki⟩ := kd_contextR p hM ts tx (hRP _ _ hr) (hRK _ _ hr) hw top pre'
              (Op.del key :: post) hsplit' r1 w1 h1
            have hH2 := (ht_putKvDelChk2 tx.base key (ctxOf p ts) w1 hvo (by simp [ctxOf])
              hHS.2.1 hbk.book hH1 hbk.klongs hk hki (by simpa [ctxOf] using hM) a w2 hc2).2.1
            exact ⟨hI2, hR2, hL2, hH2, hT2, hJ2 a w2 h2 hT2⟩


theorem mapM_snoc_ok (c : Ctx) (w0 : W) (pre : List Op) (op : Op) (r : List Bool) (w : W) (a : Bool)
    (w' : W) (h1 : (pre.mapM putKv) c w0 = .ok (r, w)) (h2 : putKv op c w = .ok (a, w')) :
    ((pre ++ [op]).mapM putKv) c w0 = .ok (r ++ [a], w') := by
  rw [List.mapM_append]
  simp only [List.mapM_cons, List.mapM_nil, bind, ReaderT.bind, StateT.bind, Except.bind, h1, h2, pure,
    ReaderT.pure, StateT.pure, Except.pure]

set_option maxHeartbeats 3200000 in
/-- TP7, TP10 and TP11, and the latest time's get and scan, without `hHL` and
`hMF`, and with `hchk` narrowed to the holders' checks at the deletes whose start
has the fill, `PutInv`, the ranges and the heights (`OpDelChk4OKL`): the joint
route (`jointHtJ_reached`). -/
theorem invGetScanOK_merges_joint (p : Params) (hp : MergeParamsOK p)
    (hth : 2 ≤ p.theta ∨ p.theta = 0)
    (hchk4 : OpDelChk4OKL p)
    (htb : TakeBelowFuelDelOK p)
    (d4 : OpCaseOK p (RunOK p) (QDead p) DelMergeDOpenCase)
    (l4 : OpCaseOK p (RunOK p) (QLive p) DelMergeOpenCase)
    (hU : ∀ ts, UpUnlinkTreeOK (ctxOf p ts) (viewOf (treeRun p ts)))
    (hMSF : ∀ ts, MergeFitsOK (ctxOf p ts) (viewOf (treeRun p ts)) (p.fuel + 1))
    (hCoF : ∀ ts, CollapseFitsOK (ctxOf p ts) (viewOf (treeRun p ts)) (p.fuel + 1))
    (hCoU : ∀ ts, CollapseUnlinkAllOK (ctxOf p ts) (viewOf (treeRun p ts)) (p.fuel + 1)) :
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
  have hMS : ∀ ts, MergeStepOK (ctxOf p ts) (viewOf (treeRun p ts)) (p.fuel + 1) :=
    fun ts => mergeStepOK_of_segFits (ctxOf p ts) _ _ (Nat.succ_pos _) hcap hsa (hMSF ts)
  have hCo : ∀ ts, CollapseStepOK (ctxOf p ts) (viewOf (treeRun p ts)) (p.fuel + 1) :=
    fun ts => ⟨hCoF ts, hCoU ts⟩
  have hR : ∀ P t, RunTreeQ p (LatestQD p) P t → RunOK p P t := runOK_of_runTreeQD p
  have hRL' : ∀ P t, RunTreeQ p (LatestQD p) P t → RunLinksOK p P t := fun _ _ h => h.1
  have hRT' : ∀ P t, RunTreeQ p (LatestQD p) P t → TreeAt p P t := fun _ _ h => h.2.1
  have hRI' : ∀ P t, RunTreeQ p (LatestQD p) P t → InvOK p P t := fun _ _ h => h.2.2.1.1
  have hRP' : ∀ P t, RunTreeQ p (LatestQD p) P t → PointersOK P := fun _ _ h => h.1.1
  have hRK' : ∀ P t, RunTreeQ p (LatestQD p) P t → KindsAllOK p P := fun _ _ h => h.2.2.1.2.2.1
  have hRH' : ∀ P t, RunTreeQ p (LatestQD p) P t → HeightAllOK p P t :=
    fun _ _ h => h.2.2.1.2.2.2.1
  have l4' := opCaseOK_anti p _ _ hR _ _
    (liveCase_delMerge_of_rest p (RunOK p) hRL
      (opCaseOK_of_open p (RunOK p) (QLive p) (keptByReads_live p) DelMergeRestCase l4))
  -- the joint induction's cases
  have hLv := opCaseOK_of_cases_merges p _ _ hm (liveCase_putLeafRoom p _)
    (liveCase_putLeafFull p _ hRL' hsa hp)
    (opCaseOK_putNewSeg_of_parts p _ _ (liveCase_putNewSeg1Room p _ (by omega))
      (liveCase_putNewSegsRoom p _ (by omega)) (liveCase_putNewSegFull p _ hRL' (by omega) hsa hp)) l4'
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
  have hTIRJ := opCaseOKJ_treeInvRange_delMergeRL p _
    (delStepsQdLJ_of_openR p _ (by omega) hsa hRL' hRP' hRK' hRH' hU) hMS hCo hsa hcap hRP' hRK'
  have hSI : ∀ ts tx w, SJ p ts tx w → PutInv (ctxOf p ts) (viewOf (treeRun p ts)) w :=
    fun _ _ _ h => h.1.1.1.1.1
  have hSV : ∀ ts tx w, SJ p ts tx w → LeafVals (ctxOf p ts) (viewOf (treeRun p ts)) tx.base w :=
    fun _ _ _ h => h.1.1.1.1.2
  have hSB : ∀ ts tx w, SJ p ts tx w → tx.base ≤ w.next := fun _ _ _ h => h.1.1.1.2
  have hSR : ∀ ts tx w, SJ p ts tx w →
      RangeOrder (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) w.top.rootKey := fun _ _ _ h => h.1.1.2
  have hSF : ∀ ts tx w, SJ p ts tx w →
      SegFits (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) (p.fuel - 1) w.top.rootKey :=
    fun _ _ _ h => h.1.2.1
  have hSM : ∀ ts tx w, SJ p ts tx w → ∀ x o, w.madeFor.lookup x = some o → o < tx.base :=
    fun _ _ _ h => h.1.2.2
  have hDSJ : DelStepsJ2OK p (RunTreeQ p (LatestQD p)) (SJ p) :=
    delStepsJ2OKS_of_openR p _ (SJ p) (by omega) hsa hRL' hRP' hRK' hSI hSV hSB hSR hSF hSM hRH'
      (fun _ _ _ h => h.2.1) (fun _ _ _ h => h.2.2) hU
  have hJ2O : OpJ2OK p (RunTreeQ p (LatestQD p)) (SJ p) :=
    opJ2OK_of_cases p _ _ (opJ2Case_putLeafRoom p _ _ hSI hSV)
      (opJ2Case_putLeafFull p _ _ hRL' hsa hSI hSV hSB hSR)
      (opJ2Case_putNewSeg p _ _ (by omega) hSI hSB (opJ2Case_putNewSegFull p _ _ hRL' (by omega) hsa hSI hSB hSR))
      (opJ2Case_delMergeR p _ _ hDSJ hMS hCo (replaceRootFullJ2OK_run p hsa) hsa hcap hRP' hRK')
      (opJ2Case_delNoLeaf p _ _ hSI) (opJ2Case_delNoop p _ _ hSI)
      (opJ2CaseOK_void p _ _ _ hm delEmptyCase_merges) (opJ2Case_delRoom p _ _ hSI hSV)
      (opJ2CaseOK_void p _ _ _ hm delFullCase_merges)
  have hchkR := opDelChk2OKR_of_chk4 p _ hm hM4 hRL' hchk4
  have joint := jointHtJ_reached p _ hm (by omega) hM4 (baseStartOK_runTreeQ p (LatestQD p)) hRL' hRT' hRI'
    hRP' hRK' hRH' htb hTp hPp hOp hTIRJ.1 hTIRJ.2.1 hTIRJ.2.2 hJ2O hLv hchkR
  -- from the joint induction: the heights' delete side, the fuel, the cases at every operation
  have hht : OpHtDelOKUnder p (RunTreeQ p (LatestQD p)) := by
    intro ts tx hw hr z top hz htop pre key post hsplit r w hpre hvo hkw hb hwf hi r' v he
    obtain ⟨hI, hRo, hL, _, _, _⟩ := joint ts tx hw hr z top hz htop pre (Op.del key :: post) hsplit r w hpre
    have hc := hchkR ts tx hw hr z top hz htop pre key post hsplit r w hpre hI hRo hL hi r' v he
    obtain ⟨-, hk, -, hki⟩ := kd_contextR p (by omega) ts tx (hRP' _ _ hr) (hRK' _ _ hr) hw top pre
      (Op.del key :: post) hsplit r w hpre
    exact (ht_putKvDelChk2 tx.base key (ctxOf p ts) w hvo (by simp [ctxOf]) hkw hb hi hwf hk hki
      (by simpa [ctxOf] using (show 2 ≤ p.M by omega)) r' v hc).2.1
  have hfitQ : TxSegFitsOK p (RunTreeQ p (LatestQD p)) :=
    txSegFitsOK_of_takeBelowDelRHU p (by omega) _ hRL' hRK' hRH' hht htb
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
  have hLC : StateOK p (RunTreeQ p (LatestQD p)) (fun ts _ w => LiveCountsW p ts w) :=
    fun ts tx hw hr z top hz htop pre post hs r w hpre =>
      (joint ts tx hw hr z top hz htop pre post hs r w hpre).2.2.1
  have hJ2S : StateOK p (RunTreeQ p (LatestQD p))
      (fun ts tx w => TakeJ2 (ctxOf p ts) (viewOf (treeRun p ts)) tx.base w) :=
    fun ts tx hw hr z top hz htop pre post hs r w hpre =>
      (joint ts tx hw hr z top hz htop pre post hs r w hpre).2.2.2.2.2
  have hMFS := stateOK_madeFor p hM4 (RunTreeQ p (LatestQD p)) hRL'
  -- from here as in `invGetScanOK_merges`, the delete's steps without `hHL`
  have d4' := opCaseOK_anti p _ _ hR _ _ (deadCase_delMergeL_of_rest p (RunOK p) hRL
    (opCaseOK_of_open p (RunOK p) (QDead p) (keptByReads_dead p) DelMergeDRestCase d4))
  have hTL := opCaseOK_L_of_any p _ _ hT
  have hPIL := opCaseOK_L_of_any p _ _ hPI
  have hOL := opCaseOK_L_of_any p _ _ hO
  have hLvL := opCaseOK_L_of_any p _ _ hLv
  have hDdL := opCaseOK_of_cases_mergesL p _ _ hm (deadCase_putLeafRoom p _)
    (deadCase_putLeafFull p _ hRL' hsa hth)
    (opCaseOK_putNewSeg_of_parts p _ _ (deadCase_putNewSeg1Room p _ (by omega))
      (deadCase_putNewSegsRoom p _ (by omega)) (deadCase_putNewSegFull p _ hRL' (by omega) hsa hth)) d4'
  have hDd := opCaseOK_any_of_L p _ hRL' hRT' hRI' hTL hPIL hOL hLvL _ hDdL
  have hJ := runTreeQ_of_mergesS p (by omega) hsa hcap hm (LatestQD p) (latestQD_init p (by omega))
    (latestQD_snocR p hp hht hT hPI hO hLv hDd)
    (fun _ _ h => h.1.2.1) (fun _ _ h => h.1.2.2.1)
    (opTreeOKUnder_of_cases p _ hRL' hRT' hRI' hT hPI hO)
    (putInvStateOK_of_cases p _ hRL' hRT' hRI' hT hPI hO)
    (rangeStateOK_of_cases p _ hRL' hRT' hRI' hT hPI hO)
    hfitQ hMFS
    (delStepsJ2OKJ_of_openR p _ (TakeS4 p) (by omega) hsa hRL' hRP' hRK'
      (fun _ _ _ h => h.1.1.1.1) (fun _ _ _ h => h.1.1.1.2) (fun _ _ _ h => h.1.1.2)
      (fun _ _ _ h => h.1.2) (fun _ _ _ h => h.2.1) (fun _ _ _ h => h.2.2) hRH' hht htb hU hLC)
    hMS hCo (replaceRootFullJ2OK_run p hsa)
  have hW : ∀ ts tx, Within p (ts ++ [tx]) → RunOK p (treeRun p ts) ts.length →
      RunTreeQ p (LatestQD p) (treeRun p ts) ts.length :=
    fun ts tx hw _ => hJ ts (within_snoc_prefix p ts tx hw)
  have hP : ∀ ts, Within p ts → PointersOK (treeRun p ts) := fun ts hw => (hJ ts hw).1.1
  have hfit : TxSegFitsOK p (RunOK p) :=
    fun ts tx hw _ => hfitQ ts tx hw (hJ ts (within_snoc_prefix p ts tx hw))
  have hinv : InvPreserved p :=
    invPreserved_of_latest_pointers p hp (fun ts hw => (hJ ts hw).2.2.1.1) hP
      (fun ts hw => (hJ ts hw).2.2.2)
  have h := getOK_scanOK_of_cases_merges_open p hp hinv (fun ts hw => (hJ ts hw).1)
    (fun ts hw => (hJ ts hw).2.1) hfit
    (opCaseOK_of_within p _ _ hW _ _ (opCaseOK_of_any p _ _ _ hT))
    (opCaseOK_of_within p _ _ hW _ _ (opCaseOK_of_any p _ _ _ hPI))
    (opCaseOK_of_within p _ _ hW _ _ (opCaseOK_of_any p _ _ _ hO))
    (opGetCaseOK_delMerge p (RunOK p)
      (delStepsOK_of_within p (RunOK p) _ hW
        (delStepsOKJ_of_open p _ (by omega) hsa hRL' hP hRK' hRH' hht htb hU hLC hJ2S hMFS))
      hMS hCo hsa hcap (by omega) hP hfit)
  exact ⟨hinv, h.1, h.2, latestGetOK_of_getOK p h.1, latestScanOK_of_scanOK p h.2⟩

end SIS.Tree
