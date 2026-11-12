import SIS.Tree.MergeHeightExec
import SIS.Tree.SortedKeys

namespace SIS.Tree

open SIS SIS.Check

attribute [local cbv_eval] appendKlongs_step_dead
attribute [local cbv_opaque] appendKlongs putSegs

@[local cbv_eval] theorem putSegs_sortedExample_step (key : Key) (value : Option Nat)
    (segs : List Nat) (x : NodeId) :
    putSegs key value segs x = putSegs._sunfold key value segs x := by
  cases segs with
  | nil => rfl
  | cons cv rest => cases rest <;> rfl

def sortedOvershootParams : Params := ({M := 8, G := 0, H := 0} : Params).withMerges
def sortedOvershootKey (j : Nat) : Key := [64*j+8]
def sortedOvershootPrefix : Tx :=
  {base := 100, ops := (List.range 5).map (fun j => .put (sortedOvershootKey j) 1)}
def sortedOvershootTx : Tx :=
  {base := 300, ops := [.del (sortedOvershootKey 3), .del (sortedOvershootKey 4)]}

theorem sortedOvershootParams_ok : MergeParamsOK sortedOvershootParams :=
  mergeParamsOK_withMerges _ (by decide)

theorem sortedOvershootHistory_within : Within sortedOvershootParams [sortedOvershootPrefix] := by
  constructor
  · intro tx htx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at htx
    subst tx
    constructor <;> decide +kernel
  · intro j hj
    have hj0 : j = 0 := by simp only [List.length_singleton] at hj; omega
    subst j
    constructor
    · intro q hq
      have hf : (treeRun sortedOvershootParams []).all
          (fun q => decide (q.1 < sortedOvershootPrefix.base)) = true := by cbv
      exact of_decide_eq_true (List.all_eq_true.mp hf q hq)
    · cbv

theorem sortedOvershootTx_sorted : sortedOvershootTx.sorted = true := by decide +kernel
theorem sortedOvershootTx_wf : sortedOvershootTx.wf = true := by decide +kernel

theorem sortedOvershootTx_fresh :
    ∀ q ∈ treeRun sortedOvershootParams [sortedOvershootPrefix], q.1 < sortedOvershootTx.base := by
  have hf : (treeRun sortedOvershootParams [sortedOvershootPrefix]).all
      (fun q => decide (q.1 < sortedOvershootTx.base)) = true := by cbv
  intro q hq
  exact of_decide_eq_true (List.all_eq_true.mp hf q hq)

def sortedOvershootStats : Except String (Nat × Nat × Nat) := do
  let (bs,w) ← execW sortedOvershootParams sortedOvershootTx 2
    (view (treeSpec sortedOvershootParams)
      (treeRun sortedOvershootParams [sortedOvershootPrefix]) 1)
  pure (w.merges, deletesOf sortedOvershootTx bs, maxSeenHeight w.gh)

set_option maxRecDepth 100000 in
set_option cbv.maxSteps 2000000 in
theorem sortedOvershootStats_eq : sortedOvershootStats = .ok (1,2,1) := by cbv

/-- The extra-height premise admits this ordinary temporary root. -/
theorem sortedOvershoot_transientHeightBound (bs : List Bool) (w : W)
    (he : execW sortedOvershootParams sortedOvershootTx 2
      (view (treeSpec sortedOvershootParams)
        (treeRun sortedOvershootParams [sortedOvershootPrefix]) 1) = .ok (bs,w)) :
    SeenHeightBound (sortedOvershootParams.H+1) w := by
  have hc := sortedOvershootStats_eq
  unfold sortedOvershootStats at hc
  have heq : (w.merges, deletesOf sortedOvershootTx bs, maxSeenHeight w.gh) = (1,2,1) := by
    simpa only [he, bind, Except.bind, pure, Except.pure, Except.ok.injEq] using hc
  have hm := congrArg (fun q : Nat × Nat × Nat => q.2.2) heq
  change maxSeenHeight w.gh = 1 at hm
  intro x g height hx
  have hb := le_maxSeenHeight w.gh x g height hx
  rw [hm] at hb
  simpa only [sortedOvershootParams, Params.withMerges, Nat.zero_add] using hb

/-- Sorted, well-formed operations and fresh ids do not bound the whole cache
by H: a temporary root can be one height higher and be taken back. -/
theorem sorted_success_can_exceed_cacheHeight :
    ∃ noops w,
      execW sortedOvershootParams sortedOvershootTx 2
        (view (treeSpec sortedOvershootParams)
          (treeRun sortedOvershootParams [sortedOvershootPrefix]) 1) = .ok (noops,w) ∧
      ¬ SeenHeightBound sortedOvershootParams.H w := by
  have hc := sortedOvershootStats_eq
  unfold sortedOvershootStats at hc
  cases hr : execW sortedOvershootParams sortedOvershootTx 2
      (view (treeSpec sortedOvershootParams)
        (treeRun sortedOvershootParams [sortedOvershootPrefix]) 1) with
  | error e =>
    simp only [hr] at hc
    change Except.error e = Except.ok (1,2,1) at hc
    cases hc
  | ok result =>
    rcases result with ⟨bs,w⟩
    refine ⟨bs,w,rfl,?_⟩
    have hm : maxSeenHeight w.gh = 1 := by
      have he : (w.merges, deletesOf sortedOvershootTx bs, maxSeenHeight w.gh) = (1,2,1) := by
        simpa only [hr, bind, Except.bind, pure, Except.pure, Except.ok.injEq] using hc
      exact congrArg (fun q : Nat × Nat × Nat => q.2.2) he
    intro hb
    have hle := maxSeenHeight_le w.gh sortedOvershootParams.H hb
    simp only [sortedOvershootParams, Params.withMerges] at hle
    omega

end SIS.Tree
