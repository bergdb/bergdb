/-
The run induction's Q for the top theorem (bergdb 024-12, latest's target):
`LatestQ`, what TP7 and the writer's facts need of a run besides TP4 and P's
tree (`RunTreeQ`): TP7's invariant at its last time, TP4, the kinds, the
heights and the sizes. Its first state and its step (`latestQ_init`,
`latestQ_snoc`) are the ones of the run inductions on main
(`treeRun_kindsAllOK`, `treeRun_heightAllOK`, `treeRun_sizeOK_of_pointers`,
`latestInvOK_of_cases`) one transaction at a time, from what the run before has,
so that the take-back's joint induction (putinv's `runTree_jointJ2`) can carry
them. With that induction at every run, `LatestGetOK` and `LatestScanOK`
follow (`latestGetOK_latestScanOK_of_joint`): TP4 and P's tree are no longer
premises.
-/
import SIS.Tree.LatestOpen
import SIS.Tree.KindsRun
import SIS.Tree.HeightsRun
import SIS.Tree.TakeBackRunU
import SIS.Tree.TakeBackRunJ
import SIS.Tree.LeftRun

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-! ## The parts of TP7's invariant from a run's facts -/

/-- The space root of P's tree is a key node of P. -/
theorem rootKeyOK_of_treeAt (p : Params) (P : Struct BVal) (t : Time) (h : TreeAt p P t) :
    RootKeyOK p P t := by
  obtain ⟨r, hr, hT⟩ := h
  obtain ⟨n, hn⟩ := hT.rootKey
  unfold knodeOf at hn
  cases hb : viewOf P r with
  | none => rw [hb] at hn; cases hn
  | some nd =>
    rw [hb] at hn
    cases hd : nd.isData with
    | true => simp [hd] at hn
    | false =>
      by_cases hl : p.keyMax < nd.level
      · simp [hd, hl] at hn
      · exact ⟨r, nd, hr, hb, hd, by omega⟩

/-- `keyNodesOK_of_pointers` at one run: from P's sizes, its histories, TP4
and the bound on dead klongs there. -/
theorem keyNodesOK_of_parts (p : Params) (P : Struct BVal) (hS : SizeOK p P) (hH : KeyHistOK p P)
    (hP : PointersOK P) (hD : DeadAllOK p P) : KeyNodesOK p P := by
  intro x nd hx hd hl
  obtain ⟨hwf, hrt⟩ := hH x nd hx hd hl
  have hk := keyNodeAt_of p _ x nd hx hd hl
  refine ⟨hS x _ hk, hwf, hrt, ?_, hD x _ hk⟩
  intro c y hm
  obtain ⟨e, he, hv⟩ := klongsOf_key_mem nd.hist c y hm
  exact hP _ (mem_of_get? hx) e he y (by rw [hv]; simp [bptrs])

/-! ## One transaction's step of the run inductions -/

/-- `treeRun_kindsAllOK`'s step: the kinds after one more transaction, from
the run's links and kinds before it. -/
theorem kindsAllOK_snoc (p : Params) (hM : 2 ≤ p.M) (ts : List Tx) (tx : Tx)
    (hw : Within p (ts ++ [tx])) (hL : RunLinksOK p (treeRun p ts) ts.length)
    (hK : KindsAllOK p (treeRun p ts)) : KindsAllOK p (treeRun p (ts ++ [tx])) := by
  obtain ⟨hP', hH, hN⟩ := hL
  obtain ⟨bs, w, he0⟩ := execW_success_of_within_snoc p ts tx hw
  have hfresh : ∀ q ∈ treeRun p ts, q.1 < tx.base := by
    have := (hw.2 ts.length (by simp)).1
    simpa using this
  have htimes : StructTimesLE (treeRun p ts) (ts.length + 1 - 1) := treeRun_timesLE p ts
  have htimes' : StructTimesLE (treeRun p ts) ts.length := treeRun_timesLE p ts
  have hl := viewLinksOK_of p _ _ tx.base hfresh htimes hP' hN
  have hrun : runOps p tx.base tx.ops (ts.length + 1)
      (view (treeSpec p) (treeRun p ts) ts.length) = .ok (bs, w) := he0
  have he : execW p tx (ts.length + 1)
      (view (treeSpec p) (treeRun p ts) (ts.length + 1 - 1)) = .ok (bs, w) := hrun
  have he' : execW p tx (ts.length + 1)
      (view (treeSpec p) (treeRun p ts) ts.length) = .ok (bs, w) := hrun
  have hvg := viewGood_of p (treeRun p ts) (ts.length + 1) tx.base (by omega) hfresh htimes hl
  have hbook := execW_book p tx (ts.length + 1) _ bs w
    (viewIdsBelow_view p (treeRun p ts) (ts.length + 1 - 1) tx.base hfresh) he
  have htaken := execW_takenAbove p tx (ts.length + 1) _ bs w hvg he
  have hKW := execW_kinds (kindOracleOf p (treeRun p ts)) p tx (ts.length + 1) _ bs w hM
    (hw.1 tx (by simp)).2 (appendFrameOK tx.base)
    (viewIdsBelow_view p (treeRun p ts) ts.length tx.base hfresh)
    (viewKinds_of p (treeRun p ts) ts.length tx.base hfresh htimes' hP' hK) he'
  rw [treeRun_snoc_changes p ts tx bs w hrun]
  exact kindsAllOK_step p _ (ts.length + 1) tx bs w (by omega) hfresh htimes
    (treeRun_root_level p _) hH hl hP' he hbook htaken hK hKW

/-- `treeRun_sizeOK_of_pointers`'s step. -/
theorem sizeOK_snoc (p : Params) (hp : MergeParamsOK p) (ts : List Tx) (tx : Tx)
    (hw : Within p (ts ++ [tx])) (hL : RunLinksOK p (treeRun p ts) ts.length)
    (hS : SizeOK p (treeRun p ts)) : SizeOK p (treeRun p (ts ++ [tx])) := by
  have hM := mergeParamsOK_M p hp
  obtain ⟨hP', hH, hN⟩ := hL
  obtain ⟨bs, w, he0⟩ := execW_success_of_within_snoc p ts tx hw
  have hfresh : ∀ q ∈ treeRun p ts, q.1 < tx.base := by
    have := (hw.2 ts.length (by simp)).1
    simpa using this
  have htimes : StructTimesLE (treeRun p ts) (ts.length + 1 - 1) := treeRun_timesLE p ts
  have hl := viewLinksOK_of p _ _ tx.base hfresh htimes hP' hN
  have hrun : runOps p tx.base tx.ops (ts.length + 1)
      (view (treeSpec p) (treeRun p ts) ts.length) = .ok (bs, w) := he0
  rw [treeRun_snoc_changes p ts tx bs w hrun]
  exact sizeOK_step p _ (ts.length + 1) tx bs w hp (by omega) hfresh htimes
    (treeRun_root_level p _) hH hl hS hrun

/-- `treeRun_heightAllOK`'s step, given the delete side of the walk. -/
theorem heightAllOK_snoc (p : Params) (hM : 2 ≤ p.M) (hdel : OpHtDelOK p) (ts : List Tx) (tx : Tx)
    (hw : Within p (ts ++ [tx])) (hL : RunLinksOK p (treeRun p ts) ts.length)
    (hK : KindsAllOK p (treeRun p ts)) (hA : HeightAllOK p (treeRun p ts) ts.length) :
    HeightAllOK p (treeRun p (ts ++ [tx])) (ts.length + 1) := by
  obtain ⟨hP', hH, hN⟩ := hL
  obtain ⟨bs, w, he0⟩ := execW_success_of_within_snoc p ts tx hw
  have hfresh : ∀ q ∈ treeRun p ts, q.1 < tx.base := by
    have := (hw.2 ts.length (by simp)).1
    simpa using this
  have htimes : StructTimesLE (treeRun p ts) (ts.length + 1 - 1) := treeRun_timesLE p ts
  have hl := viewLinksOK_of p _ _ tx.base hfresh htimes hP' hN
  have hrun : runOps p tx.base tx.ops (ts.length + 1)
      (view (treeSpec p) (treeRun p ts) ts.length) = .ok (bs, w) := he0
  have he : execW p tx (ts.length + 1)
      (view (treeSpec p) (treeRun p ts) (ts.length + 1 - 1)) = .ok (bs, w) := hrun
  have hbook := execW_book p tx (ts.length + 1) _ bs w
    (viewIdsBelow_view p (treeRun p ts) (ts.length + 1 - 1) tx.base hfresh) he
  have hHt := execW_htCache p hM hdel ts tx hw ⟨hP', hH, hN⟩ hK hA bs w he0
  have hA' : HeightAllOK p (treeRun p ts) (ts.length + 1 - 1) := by simpa using hA
  have hstep := heightAllOK_step p _ (ts.length + 1) tx bs w (by omega) hfresh
    htimes (treeRun_root_level p _) hH hl hP' he hbook hA' hHt
  rw [treeRun_snoc_changes p ts tx bs w hrun]
  exact hstep

/-- `treeRun_leftAllOK`'s step. -/
theorem leftAllOK_snoc (p : Params) (hp : MergeParamsOK p) (ts : List Tx) (tx : Tx)
    (hw : Within p (ts ++ [tx])) (hL : RunLinksOK p (treeRun p ts) ts.length)
    (hLA : LeftAllOK p (treeRun p ts)) : LeftAllOK p (treeRun p (ts ++ [tx])) := by
  obtain ⟨hP', hH, hN⟩ := hL
  obtain ⟨bs, w, he0⟩ := execW_success_of_within_snoc p ts tx hw
  have hfresh : ∀ q ∈ treeRun p ts, q.1 < tx.base := by
    have := (hw.2 ts.length (by simp)).1
    simpa using this
  have htimes : StructTimesLE (treeRun p ts) (ts.length + 1 - 1) := treeRun_timesLE p ts
  have hl := viewLinksOK_of p _ _ tx.base hfresh htimes hP' hN
  have hrun : runOps p tx.base tx.ops (ts.length + 1)
      (view (treeSpec p) (treeRun p ts) ts.length) = .ok (bs, w) := he0
  have he : execW p tx (ts.length + 1)
      (view (treeSpec p) (treeRun p ts) (ts.length + 1 - 1)) = .ok (bs, w) := hrun
  have hvg := viewGood_of p (treeRun p ts) (ts.length + 1) tx.base (by omega) hfresh htimes hl
  have hbook := execW_book p tx (ts.length + 1) _ bs w
    (viewIdsBelow_view p (treeRun p ts) (ts.length + 1 - 1) tx.base hfresh) he
  have htaken := execW_takenAbove p tx (ts.length + 1) _ bs w hvg he
  have hLW := execW_leftOK p tx (ts.length + 1) _ bs w hp hvg
    (viewLeftOK_of_leftAll p _ _ htimes hLA) he
  rw [treeRun_snoc_changes p ts tx bs w hrun]
  exact leftAllOK_step p _ (ts.length + 1) tx bs w (by omega) hfresh htimes
    (treeRun_root_level p _) hH hl he hbook htaken hLA hLW

set_option maxHeartbeats 800000 in
/-- `latestInvOK_of_cases`' step: TP7's invariant after one more transaction,
from `RunOK` before it, TP10's three posts and `QLive` for every operation, and
after it: the run's links, P's tree, the kinds, the heights, the sizes and the
bound on dead klongs. -/
theorem invOK_snoc (p : Params)
    (hT : OpCaseOK p (RunOK p) (QTree p) AnyOp) (hPI : OpCaseOK p (RunOK p) (QPutInv p) AnyOp)
    (hO : OpCaseOK p (RunOK p) (QRange p) AnyOp) (hLv : OpCaseOK p (RunOK p) (QLive p) AnyOp)
    (ts : List Tx) (tx : Tx) (hw : Within p (ts ++ [tx])) (hr : RunOK p (treeRun p ts) ts.length)
    (hL' : RunLinksOK p (treeRun p (ts ++ [tx])) (ts.length + 1))
    (hT' : TreeAt p (treeRun p (ts ++ [tx])) (ts.length + 1))
    (hK' : KindsAllOK p (treeRun p (ts ++ [tx])))
    (hA' : HeightAllOK p (treeRun p (ts ++ [tx])) (ts.length + 1))
    (hS' : SizeOK p (treeRun p (ts ++ [tx])))
    (hLA' : LeftAllOK p (treeRun p (ts ++ [tx])))
    (hD' : DeadAllOK p (treeRun p (ts ++ [tx]))) :
    InvOK p (treeRun p (ts ++ [tx])) (ts.length + 1) := by
  have hRL : ∀ P t, RunOK p P t → RunLinksOK p P t := fun _ _ h => h.1
  obtain ⟨noops, w, hrun⟩ := within_last_ok p ts tx hw
  obtain ⟨z, top, hz, htop, hops⟩ := runOps_ok p _ _ _ _ noops w hrun
  have hcl : CommitLiftAt p ts tx := commitLiftAt_of_links p ts tx hw hr.1
  have hRO := (joint_reached p (RunOK p) hRL hT hPI hO ts tx hw hr hr.2.1 hr.2.2 z top hz
    htop tx.ops [] (by simp) noops w hops).2
  have hLC := live_reached p (RunOK p) hRL hT hPI hO hLv ts tx hw hr hr.2.1 hr.2.2 z top
    hz htop tx.ops [] (by simp) noops w hops
  obtain ⟨hNE, hRT, hF⟩ := liveCounts_commit p ts tx hw hcl noops w hrun hLC
  have hRA := rangeAtOK_commit p ts tx hw hcl noops w hrun hRO
  have hLM : LeftmostOK p (treeRun p (ts ++ [tx])) (ts ++ [tx]).length :=
    leftmostOK_of_leftAll p _ _ (treeRun_timesLE p _) hL'.2.1 hLA'
  have hlen : (ts ++ [tx]).length = ts.length + 1 := by simp
  rw [hlen] at hLM
  exact invOK_of_parts p _ _ (rootKeyOK_of_treeAt p _ _ hT') (keyNodesOK_of_parts p _ hS' hL'.2.1 hL'.1 hD')
    hK' (heightLiveOK_of_all p _ _ hA' (ht_keyNodesAt_key p _ _)) hNE hLM hRT hF hRA

/-! ## The run induction's Q -/

/-- What the run induction carries besides TP4 and P's tree: TP7's invariant
at the run's last time, TP4, the kinds, the heights, the sizes and the empty key
of every inner node. -/
def LatestQ (p : Params) (P : Struct BVal) (t : Time) : Prop :=
  InvOK p P t ∧ PointersOK P ∧ KindsAllOK p P ∧ HeightAllOK p P t ∧ SizeOK p P ∧ LeftAllOK p P

theorem latestQ_init (p : Params) (hM : 2 ≤ p.M) : LatestQ p (initStruct p) 0 :=
  ⟨invOK_init p (by omega) 0, (runLinksOK_init p).1, kindsAllOK_init p, heightAllOK_init p 0,
    sizeOK_init p (by omega), leftAllOK_init p⟩

/-- The step of `LatestQ` in the form of `runTree_jointJ2`'s `hQs`. -/
theorem latestQ_snoc (p : Params) (hp : MergeParamsOK p)
    (hD : ∀ ts, Within p ts → DeadAllOK p (treeRun p ts)) (hdel : OpHtDelOK p)
    (hT : OpCaseOK p (RunOK p) (QTree p) AnyOp) (hPI : OpCaseOK p (RunOK p) (QPutInv p) AnyOp)
    (hO : OpCaseOK p (RunOK p) (QRange p) AnyOp) (hLv : OpCaseOK p (RunOK p) (QLive p) AnyOp) :
    ∀ ts tx, Within p (ts ++ [tx]) → RunTreeQ p (LatestQ p) (treeRun p ts) ts.length →
      RunLinksOK p (treeRun p (ts ++ [tx])) (ts.length + 1) →
      TreeAt p (treeRun p (ts ++ [tx])) (ts.length + 1) →
      LatestQ p (treeRun p (ts ++ [tx])) (ts.length + 1) := by
  intro ts tx hw hr hL' hT'
  have hM := mergeParamsOK_M p hp
  obtain ⟨hL, hTA, hI, _, hK, hA, hS, hLA⟩ := hr
  have hK' := kindsAllOK_snoc p (by omega) ts tx hw hL hK
  have hA' := heightAllOK_snoc p (by omega) hdel ts tx hw hL hK hA
  have hS' := sizeOK_snoc p hp ts tx hw hL hS
  have hLA' := leftAllOK_snoc p hp ts tx hw hL hLA
  exact ⟨invOK_snoc p hT hPI hO hLv ts tx hw ⟨hL, hTA, hI⟩ hL' hT' hK' hA' hS' hLA' (hD _ hw),
    hL'.1, hK', hA', hS', hLA'⟩

/-! ## The writer's facts under the run induction -/

theorem opCaseOK_anti (p : Params) (R R' : Struct BVal → Time → Prop) (h : ∀ P t, R P t → R' P t)
    (Q : List Tx → Op → W → W → Prop) (C : Ctx → View BVal → W → Op → Prop)
    (hC : OpCaseOK p R' Q C) : OpCaseOK p R Q C :=
  fun ts tx hw hr => hC ts tx hw (h _ _ hr)

theorem runOK_of_runTreeQ (p : Params) (P : Struct BVal) (t : Time)
    (h : RunTreeQ p (LatestQ p) P t) : RunOK p P t :=
  ⟨h.1, h.2.1, h.2.2.1⟩

/-- The writer's tree kept by every operation, after a run that meets R. -/
theorem opTreeOKUnder_of_cases (p : Params) (R : Struct BVal → Time → Prop)
    (hRL : ∀ P t, R P t → RunLinksOK p P t) (hRT : ∀ P t, R P t → TreeAt p P t)
    (hRI : ∀ P t, R P t → InvOK p P t)
    (hT : OpCaseOK p R (QTree p) AnyOp) (hP : OpCaseOK p R (QPutInv p) AnyOp)
    (hO : OpCaseOK p R (QRange p) AnyOp) : OpTreeOKUnder p R := by
  intro ts tx hw hr z top hz htop pre op post hsplit r w hpre _
  obtain ⟨hI, hRO⟩ := joint_reached p R hRL hT hP hO ts tx hw hr (hRT _ _ hr) (hRI _ _ hr) z top
    hz htop pre (op :: post) hsplit r w hpre
  exact hT ts tx hw hr z top hz htop pre op post hsplit r w hpre hI hRO trivial

/-- `PutInv` at every state between operations, after a run that meets R. -/
theorem putInvStateOK_of_cases (p : Params) (R : Struct BVal → Time → Prop)
    (hRL : ∀ P t, R P t → RunLinksOK p P t) (hRT : ∀ P t, R P t → TreeAt p P t)
    (hRI : ∀ P t, R P t → InvOK p P t)
    (hT : OpCaseOK p R (QTree p) AnyOp) (hP : OpCaseOK p R (QPutInv p) AnyOp)
    (hO : OpCaseOK p R (QRange p) AnyOp) :
    StateOK p R (fun ts _ w => PutInv (ctxOf p ts) (viewOf (treeRun p ts)) w) :=
  fun ts tx hw hr z top hz htop pre post hsplit r w hpre =>
    (joint_reached p R hRL hT hP hO ts tx hw hr (hRT _ _ hr) (hRI _ _ hr) z top hz htop pre post
      hsplit r w hpre).1

/-- The walk's ranges at every state between operations, after a run that
meets R. -/
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

/-! ## The target from the run induction -/

/-- `LatestGetOK` and `LatestScanOK` for the parameters of `MergeParamsOK`, from
the run induction with `LatestQ` at every run (`hJ`): TP4, P's tree and TP7's
invariant come from it. Left: the bound on dead klongs, the fuel premise along
transactions, and the delete with the merges (4): TP10's three posts and its
reading. -/
theorem latestGetOK_latestScanOK_of_joint (p : Params) (hp : MergeParamsOK p)
    (hJ : ∀ ts, Within p ts → RunTreeQ p (LatestQ p) (treeRun p ts) ts.length)
    (hD : ∀ ts, Within p ts → DeadAllOK p (treeRun p ts))
    (hfit : TxSegFitsOK p (RunOK p))
    (t4 : OpCaseOK p (RunOK p) (QTree p) DelMergeCase)
    (i4 : OpCaseOK p (RunOK p) (QPutInv p) DelMergeCase)
    (r4 : OpCaseOK p (RunOK p) (QRange p) DelMergeCase)
    (c4 : OpGetCaseOK p (RunOK p) DelMergeCase) :
    LatestGetOK p ∧ LatestScanOK p := by
  have hP : ∀ ts, Within p ts → PointersOK (treeRun p ts) := fun ts hw => (hJ ts hw).1.1
  have hinv : InvPreserved p :=
    invPreserved_of_latest_pointers p hp (fun ts hw => (hJ ts hw).2.2.1) hP hD
  have h := getOK_scanOK_of_cases_merges_open p hp hinv (fun ts hw => (hJ ts hw).1)
    (fun ts hw => (hJ ts hw).2.1) hfit t4 i4 r4 c4
  exact ⟨latestGetOK_of_getOK p h.1, latestScanOK_of_scanOK p h.2⟩

end SIS.Tree
