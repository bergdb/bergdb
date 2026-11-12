import SIS.Tree.MergeProps
import SIS.Tree.WriterSteps

namespace SIS.Tree

open SIS SIS.Check

attribute [local cbv_eval] appendKlongs_step_dead
attribute [local cbv_opaque] appendKlongs putSegs

@[local cbv_eval] theorem putSegs_scanBoundary_step (key : Key) (value : Option Nat)
    (segs : List Nat) (x : NodeId) :
    putSegs key value segs x = putSegs._sunfold key value segs x := by
  cases segs with
  | nil => rfl
  | cons cv rest => cases rest <;> rfl

/-- The scan's upper sentinel is finite, whereas the stated key predicate
places no upper bound on compare values. -/
def scanBoundaryParams : Params :=
  ({ M := 8, G := 0, H := 0 } : Params).withMerges.withTheta

def scanBoundaryKey : Key := [2 ^ 63]

def scanBoundaryTx : Tx := { base := 3, ops := [.put scanBoundaryKey 1] }

def scanBoundaryHistory : List Tx := [scanBoundaryTx]

def scanBoundaryReq : ScanReq := { forward := false }

theorem scanBoundaryParams_ok : MergeParamsOK scanBoundaryParams := by
  exact mergeParamsOK_withMerges ({ M := 8, G := 0, H := 0 } : Params) (by decide)

theorem scanBoundaryHistory_within : Within scanBoundaryParams scanBoundaryHistory := by
  constructor
  · intro tx htx
    have heq : tx = scanBoundaryTx := by simpa [scanBoundaryHistory] using htx
    subst tx
    decide +kernel
  · intro j hj
    have hj0 : j = 0 := by simpa [scanBoundaryHistory] using Nat.lt_one_iff.mp hj
    subst j
    constructor
    · intro q hq
      have hq' : q.1 ∈ (treeRun scanBoundaryParams
          (scanBoundaryHistory.take 0)).map Prod.fst :=
        List.mem_map.mpr ⟨q, hq, rfl⟩
      simp [treeRun, initStruct, scanBoundaryHistory, root] at hq'
      change q.1 < 3
      omega
    · cbv

theorem scanBoundary_result :
    (scan scanBoundaryParams (viewOf (treeRun scanBoundaryParams scanBoundaryHistory))
      1 scanBoundaryReq 1).map (fun kv => (kv.key, kv.h)) = [] := by
  cbv

theorem scanBoundary_reference :
    refScan scanBoundaryHistory 1 scanBoundaryReq 1 = [(scanBoundaryKey, 1)] := by
  cbv

theorem scanBoundary_invariants :
    InvOK scanBoundaryParams (treeRun scanBoundaryParams scanBoundaryHistory) 1 := by
  cbv

theorem scanBoundary_get :
    get scanBoundaryParams (viewOf (treeRun scanBoundaryParams scanBoundaryHistory))
      1 scanBoundaryKey = some 1 := by
  cbv

/-- TP11 fails even at valid merge thresholds, on one put and a backward
scan of one result: the key passes keyWf but exceeds cvHi. -/
theorem not_scanOK_scanBoundary : ¬ ScanOK scanBoundaryParams := by
  intro h
  have he := h scanBoundaryHistory scanBoundaryHistory_within 1 (by decide)
    scanBoundaryReq 1 (by decide +kernel)
  rw [scanBoundary_result, scanBoundary_reference] at he
  cases he

end SIS.Tree
