/-
The night's top theorem for `l4` (bergdb 030-01, step 7; 2026-11-17): TP7, TP10 and
TP11 for Java's parameters with `l4`'s rest as the latest narrowed premise of each
prover of the night, in one statement.
-/
import SIS.Tree.LiveMergeInnerChain
import SIS.Tree.LiveUpCascCopy2

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- TP7, TP10 and TP11 for Java's parameters without `l4` (bergdb 030-01, step 7), its
rest in four premises at the runs of the induction (`RunTreeQ p (LatestQD p)`):
the merge's tail with its parent full in the cases left (`MergeTailRuns10`: a time
split's cascade into one node with the copy thin, and the parent made by the
transaction split in space; prover l4f), the full leaf's time split with its copy a
hole below a parent that is the space root not made, or splits in space
(`DelFullTimeHole2M`; prover l4b), the upward delete's full stop node in the cases
left (`UpCascSplitRest7Runs`; prover l4e), and R3 at the calls of `afterDelete`
(`R3Calls`). `R3Calls` is believed false at unreached states (030-01's log, 01:56 and
02:01: no fact handed to `afterDelete` carries a made-for entry), so this theorem is
believed vacuous until R3 is restated with a made-for fact carried to the call. -/
theorem invGetScanOK_merges_noL4Night (p : Params) (hp : MergeParamsOK p)
    (hth : 2 ≤ p.theta ∨ p.theta = 0)
    (hF : MergeTailRuns10 p (RunTreeQ p (LatestQD p))) (hR3 : R3Calls p (RunTreeQ p (LatestQD p)))
    (hR4 : DelCaseLive p (RunTreeQ p (LatestQD p)) DelFullTimeHole2M)
    (hU : UpCascSplitRest7Runs p (RunTreeQ p (LatestQD p))) :
    InvPreserved p ∧ GetOK p ∧ ScanOK p ∧ LatestGetOK p ∧ LatestScanOK p := by
  have hp' := hp
  unfold MergeParamsOK at hp'
  exact invGetScanOK_merges_noL4g p hp hth hF hR3 hR4
    (delCaseLive_emptyCasc p _ (by have := mergeParamsOK_M p hp; omega) (by omega) hp (fun _ _ h => h.1)
      (fun _ _ h => h.1.1) (fun _ _ h => h.2.2.1.2.2.1) (upCascCallRuns_of_rest7 p _ hU))

end SIS.Tree
