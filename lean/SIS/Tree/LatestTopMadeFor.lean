/-
The top theorems without `hMF` (bergdb 024-12, section 1): the made-for ids
name old nodes at every state between operations (`stateOK_madeFor`, from the
walk of SIS/Tree/MadeForOld.lean), so `invGetScanOK_merges'` (the form with
`hchk` narrowed, `invGetScanOK_merges_chkL`) and `invGetScanOK_merges_noOutside'`
take the other premises only.
-/
import SIS.Tree.MadeForOld
import SIS.Tree.HeightsFill
import SIS.Tree.LatestTopNoOutside

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- The top theorem's `hMF`, for node size at least 4: at every state between
operations of a transaction after a run of R (whose runs have TP4's links),
every made-for id is below the transaction's first id. -/
theorem stateOK_madeFor (p : Params) (hM : 4 ≤ p.M) (R : Struct BVal → Time → Prop)
    (hR : ∀ P t, R P t → RunLinksOK p P t) :
    StateOK p R (fun _ tx w => ∀ x o, w.madeFor.lookup x = some o → o < tx.base) := by
  intro ts tx hw hr z top _ _ pre post _ r w he
  obtain ⟨hP', _, hN⟩ := hR _ _ hr
  have hfresh : ∀ q ∈ treeRun p ts, q.1 < tx.base := by
    have := (hw.2 ts.length (by simp)).1
    simpa using this
  have htimes : StructTimesLE (treeRun p ts) (ts.length + 1 - 1) := treeRun_timesLE p ts
  have hl := viewLinksOK_of p _ _ tx.base hfresh htimes hP' hN
  have hvg : ViewGood tx.base (ctxOf p ts) :=
    viewGood_of p (treeRun p ts) (ts.length + 1) tx.base (by omega) hfresh htimes hl
  have h := gmf_ops tx.base pre (ctxOf p ts) (wInit tx top) hM hvg
    ⟨Nat.le_refl _, by intro q hq; cases hq⟩ (by intro q hq; cases hq) r w he
  exact mfb_lookup tx.base w h.2

theorem four_le_M (p : Params) (hp : MergeParamsOK p) : 4 ≤ p.M := by
  unfold MergeParamsOK at hp; omega

/-- `invGetScanOK_merges_chkL` without `hMF`. -/
theorem invGetScanOK_merges' (p : Params) (hp : MergeParamsOK p)
    (hth : 2 ≤ p.theta ∨ p.theta = 0)
    (hchkL : OpDelChk2OKL p)
    (htb : TakeBelowFuelDelOK p)
    (d4 : OpCaseOK p (RunOK p) (QDead p) DelMergeDOpenCase)
    (l4 : OpCaseOK p (RunOK p) (QLive p) DelMergeOpenCase)
    (hU : ∀ ts, UpUnlinkTreeOK (ctxOf p ts) (viewOf (treeRun p ts)))
    (hHL : ∀ ts, UpHolderLiveRunOK (ctxOf p ts) (viewOf (treeRun p ts)))
    (hMSF : ∀ ts, MergeFitsOK (ctxOf p ts) (viewOf (treeRun p ts)) (p.fuel + 1))
    (hCoF : ∀ ts, CollapseFitsOK (ctxOf p ts) (viewOf (treeRun p ts)) (p.fuel + 1))
    (hCoU : ∀ ts, CollapseUnlinkAllOK (ctxOf p ts) (viewOf (treeRun p ts)) (p.fuel + 1)) :
    InvPreserved p ∧ GetOK p ∧ ScanOK p ∧ LatestGetOK p ∧ LatestScanOK p :=
  invGetScanOK_merges_chkL p hp hth hchkL htb d4 l4 hU hHL hMSF hCoF hCoU
    (stateOK_madeFor p (four_le_M p hp) (RunOK p) (fun _ _ h => h.1))

/-- `invGetScanOK_merges_noOutside` without `hMF`. -/
theorem invGetScanOK_merges_noOutside' (p : Params) (hp : MergeParamsOK p)
    (hth : 2 ≤ p.theta ∨ p.theta = 0)
    (hchk : OpDelChk2OK p)
    (d4 : OpCaseOK p (RunOK p) (QDead p) DelMergeDOpenCase)
    (l4 : OpCaseOK p (RunOK p) (QLive p) DelMergeOpenCase)
    (hU : ∀ ts, UpUnlinkTreeOK (ctxOf p ts) (viewOf (treeRun p ts)))
    (hHL : ∀ ts, UpHolderLiveRunOK (ctxOf p ts) (viewOf (treeRun p ts)))
    (hMSF : ∀ ts, MergeFitsOK (ctxOf p ts) (viewOf (treeRun p ts)) (p.fuel + 1))
    (hCoF : ∀ ts, CollapseFitsOK (ctxOf p ts) (viewOf (treeRun p ts)) (p.fuel + 1))
    (hCoU : ∀ ts, CollapseUnlinkAllOK (ctxOf p ts) (viewOf (treeRun p ts)) (p.fuel + 1)) :
    ∀ ts, Within p ts → NoOutside p ts →
      (∀ t ≤ ts.length, InvOK p (treeRun p ts) t ∧ PointersOK (treeRun p ts)) ∧
      (∀ t ≤ ts.length, ∀ key, keyWf key = true →
        get p (viewOf (treeRun p ts)) t key = refGet ts t key) ∧
      (∀ t ≤ ts.length, ∀ (req : ScanReq) (limit : Nat), req.wf = true →
        (scan p (viewOf (treeRun p ts)) t req limit).map (fun kv => (kv.key, kv.h)) =
          refScan ts t req limit) :=
  invGetScanOK_merges_noOutside p hp hth hchk d4 l4 hU hHL hMSF hCoF hCoU
    (stateOK_madeFor p (four_le_M p hp) (RunOK p) (fun _ _ h => h.1))

end SIS.Tree
