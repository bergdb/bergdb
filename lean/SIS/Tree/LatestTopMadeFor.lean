/-
The NoOutside route's top theorem (bergdb 025-03; 024-12, section 1):
`invGetScanOK_merges_noOutside`, TP7, TP10 and TP11 for every run within reach
with `NoOutside`, without `htb` and without `hMF`: the made-for ids name old nodes
at every state between operations (`stateOK_madeFor`, from the walk of
SIS/Tree/MadeForOld.lean), so `N.invGetScanOK_merges` (LatestTopNoOutside.lean)
takes the other premises only.
-/
import SIS.Tree.MadeForOld
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

/-- TP7, TP10 and TP11 (024-12, section 1) for the runs in which no key node is
made outside the level bounds G and H (`NoOutside`), for the parameters of
`MergeParamsOK`: after every such run within reach the invariants hold at every
time, and every get and scan at every time returns what the reference map
returns. The NoOutside route's top theorem: neither `htb` nor `hMF` is a premise
(`stateOK_madeFor`); its premises are those of the top theorem as it stood on
2026-11-14 but those two. For a run of Java's, H is chosen to cover the highest
moment of every transaction (bergdb 025-03). -/
theorem invGetScanOK_merges_noOutside (p : Params) (hp : MergeParamsOK p)
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
          refScan ts t req limit) := by
  intro ts hw hno
  obtain ⟨hinv, hget, hscan, -, -⟩ :=
    N.invGetScanOK_merges p hp hth hchk d4 l4 hU hHL hMSF hCoF hCoU
      (stateOK_madeFor p (four_le_M p hp) (RunOK p) (fun _ _ h => h.1))
  exact ⟨hinv ts ⟨hw, hno⟩, hget ts ⟨hw, hno⟩, hscan ts ⟨hw, hno⟩⟩

/-- `invGetScanOK_merges_noOutside` without `hU` (025-04, route (b)): the stop
node's split runs the same from the state with its bitmap (`handleFull_swap`).
Premises `hp`, `hth`, `hchk`, `d4`, `l4`, `hHL`, `hMSF`, `hCoF` and `hCoU`. -/
theorem invGetScanOK_merges_noOutside_noU (p : Params) (hp : MergeParamsOK p)
    (hth : 2 ≤ p.theta ∨ p.theta = 0)
    (hchk : OpDelChk2OK p)
    (d4 : OpCaseOK p (RunOK p) (QDead p) DelMergeDOpenCase)
    (l4 : OpCaseOK p (RunOK p) (QLive p) DelMergeOpenCase)
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
          refScan ts t req limit) := by
  intro ts hw hno
  obtain ⟨hinv, hget, hscan, -, -⟩ :=
    N.invGetScanOK_merges_noU p hp hth hchk d4 l4 hHL hMSF hCoF hCoU
      (stateOK_madeFor p (four_le_M p hp) (RunOK p) (fun _ _ h => h.1))
  exact ⟨hinv ts ⟨hw, hno⟩, hget ts ⟨hw, hno⟩, hscan ts ⟨hw, hno⟩⟩

end SIS.Tree
