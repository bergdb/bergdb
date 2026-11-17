/-
The merge's tail with its parent full at the runs' contexts, narrowed to what is left
after the cascade's space and time splits with no hole and the space root's splits
(bergdb 030-01, step 7): `MergeTailRuns9` (`MergeTailFullRest9OK` at the runs), and the
top theorem `invGetScanOK_merges_noL4d` with it in place of `MergeTailRuns6`.
-/
import SIS.Tree.LiveMergeTimeChain
import SIS.Tree.LiveDelHoleMade

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- The merge's tail with its parent full in the cases left after prover l4f's parts
(`MergeTailFullRest9OK`) at the contexts of the runs of R. -/
def MergeTailRuns9 (p : Params) (R : Struct BVal → Time → Prop) : Prop :=
  ∀ ts (tx : Tx), Within p (ts ++ [tx]) → R (treeRun p ts) ts.length →
    MergeTailFullRest9OK (ctxOf p ts) (viewOf (treeRun p ts)) tx.base (htOracleOf p (treeRun p ts))

/-- `MergeTailRuns6` from `MergeTailRuns9` (`mergeTailFullRest6OK_of_rest7`,
`mergeTailFullRest7OK_of_rest8`, `mergeTailFullRest8OK_of_rest9`). -/
theorem mergeTailRuns6_of_9 (p : Params) (hp : MergeParamsOK p) (R : Struct BVal → Time → Prop)
    (hRL : ∀ P t, R P t → RunLinksOK p P t) (hRK : ∀ P t, R P t → KindsAllOK p P)
    (hRH : ∀ P t, R P t → HeightAllOK p P t) (h9 : MergeTailRuns9 p R) : MergeTailRuns6 p R := by
  intro ts tx hw hr
  have hp' := hp
  unfold MergeParamsOK at hp'
  have hm : (ctxOf p ts).p.merges = true := by
    show p.merges = true
    unfold Params.merges; simp only [decide_eq_true_eq]; omega
  exact mergeTailFullRest6OK_of_rest7 (ctxOf p ts) _ (viewCoherent_ctxOf p ts) hm hp
    (viewHtOK_of_run p ts tx hw (hRL _ _ hr) (hRK _ _ hr) (hRH _ _ hr))
    (mergeTailFullRest7OK_of_rest8 (ctxOf p ts) _ (viewCoherent_ctxOf p ts) hm hp
      (mergeTailFullRest8OK_of_rest9 (ctxOf p ts) _ (viewCoherent_ctxOf p ts) hm hp (h9 ts tx hw hr)))

/-- `invGetScanOK_merges_noL4d` with the merge's tail narrowed to `MergeTailRuns9`.
Its premise `R3Calls` is believed false at unreached states (030-01's log), so this
theorem is believed vacuous until R3 is restated with a made-for fact carried to
`afterDelete`'s call. -/
theorem invGetScanOK_merges_noL4f (p : Params) (hp : MergeParamsOK p)
    (hth : 2 ≤ p.theta ∨ p.theta = 0)
    (hF : MergeTailRuns9 p (RunTreeQ p (LatestQD p))) (hR3 : R3Calls p (RunTreeQ p (LatestQD p)))
    (hR4 : DelCaseLive p (RunTreeQ p (LatestQD p)) DelFullTimeHole2M)
    (hCasc : DelCaseLive p (RunTreeQ p (LatestQD p)) DelEmptyCascM) :
    InvPreserved p ∧ GetOK p ∧ ScanOK p ∧ LatestGetOK p ∧ LatestScanOK p :=
  invGetScanOK_merges_noL4d p hp hth (mergeTailRuns6_of_9 p hp _ (fun _ _ h => h.1)
    (fun _ _ h => h.2.2.1.2.2.1) (fun _ _ h => h.2.2.1.2.2.2.1) hF) hR3 hR4 hCasc

end SIS.Tree
