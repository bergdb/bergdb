import SIS.Tree.MergePotential
import SIS.Tree.RunPrefix
import SIS.Tree.ListCongr
import SIS.Tree.HistoricalGet

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

theorem nodesRootsAt_init (p : Params) (t : Time) :
    nodesRootsAt p (initStruct p) t = [(1,true)] := by
  unfold nodesRootsAt
  rw [rootAt_init]
  dsimp only
  have hf : p.fuel = ((p.G + 1) * (p.H + 2) + 1) + 1 := by
    unfold Params.fuel
    omega
  rw [hf, nodesRoots.eq_def]
  dsimp only
  rw [knodeOf_init]
  simp [KNode.liveAt, prefixAt, KNode.delAt, lastBitmapOf, KNode.lastVersionGivenDel]

theorem treeFillPotential_init (p : Params) (t : Time) :
    treeFillPotential p (initStruct p) t = 0 := by
  simp only [treeFillPotential, nodesRootsAt_init, List.map_cons, List.map_nil,
    ↓reduceIte, List.sum_cons, List.sum_nil, Nat.zero_add]

theorem runCosts_snoc (p : Params) (ts : List Tx) (tx : Tx) :
    runCosts p (ts ++ [tx]) = runCosts p ts ++
      (match execW p tx (ts.length + 1)
        (view (treeSpec p) (treeRun p ts) ts.length) with
       | .ok (noops, w) => [(w.merges, deletesOf tx noops, w.spaceSplits)]
       | .error _ => []) := by
  unfold runCosts
  rw [List.zipIdx_append, List.filterMap_append]
  congr 1
  · apply filterMap_congr_mem
    intro q hq
    have hj : q.2 < ts.length := List.snd_lt_of_mem_zipIdx hq
    rw [List.take_append_of_le_length (by omega : q.2 ≤ ts.length)]
  · simp only [List.zipIdx_cons, List.zipIdx_nil, Nat.zero_add, List.filterMap_cons,
      List.filterMap_nil, List.take_append_of_le_length (Nat.le_refl ts.length),
      List.take_length]
    cases he : execW p tx (ts.length + 1) (view (treeSpec p) (treeRun p ts) ts.length) with
    | error e => rfl
    | ok out => cases out; rfl

theorem execW_success_of_within_snoc (p : Params) (ts : List Tx) (tx : Tx)
    (hw : Within p (ts ++ [tx])) :
    ∃ noops w, execW p tx (ts.length + 1)
      (view (treeSpec p) (treeRun p ts) ts.length) = .ok (noops,w) := by
  have hj : ts.length < (ts ++ [tx]).length := by simp
  have hh := (hw.2 ts.length hj).2
  have htx : (ts ++ [tx])[ts.length] = tx := by simp
  rw [htx, List.take_append_of_le_length (Nat.le_refl _), List.take_length] at hh
  unfold execW exec? at *
  cases he : runOps p tx.base tx.ops (ts.length + 1)
      (view (treeSpec p) (treeRun p ts) ts.length) with
  | error e => simp [he, isOk, Except.map] at hh
  | ok out => cases out; exact ⟨_, _, rfl⟩

/-- The remaining writer obligation in terms of the actual before and after
trees, rather than an existential annotation of the numerical cost list. -/
def RunPotentialStep (p : Params) : Prop :=
  ∀ ts tx, Within p (ts ++ [tx]) → ∀ noops w,
    execW p tx (ts.length + 1) (view (treeSpec p) (treeRun p ts) ts.length) = .ok (noops,w) →
    treeFillPotential p (treeRun p (ts ++ [tx])) (ts.length + 1) + w.merges ≤
      treeFillPotential p (treeRun p ts) ts.length + deletesOf tx noops + 2 * w.spaceSplits

/-- Exact telescoping over the actual successful transactions, retaining
the final nonnegative tree potential in the conclusion. -/
theorem treeFillPotential_run_costs (p : Params) (hstep : RunPotentialStep p)
    (ts : List Tx) (hw : Within p ts) :
    treeFillPotential p (treeRun p ts) ts.length + ((runCosts p ts).map (·.1)).sum ≤
      ((runCosts p ts).map (·.2.1)).sum + 2 * ((runCosts p ts).map (·.2.2)).sum := by
  have hf : ∀ revts : List Tx, Within p revts.reverse →
      treeFillPotential p (treeRun p revts.reverse) revts.reverse.length +
        ((runCosts p revts.reverse).map (·.1)).sum ≤
        ((runCosts p revts.reverse).map (·.2.1)).sum +
          2 * ((runCosts p revts.reverse).map (·.2.2)).sum := by
    intro revts
    induction revts with
    | nil =>
      intro _
      simp only [List.reverse_nil, treeRun, List.zipIdx_nil, List.foldl_nil,
        treeFillPotential_init, runCosts, List.filterMap_nil, List.map_nil, List.sum_nil]
      omega
    | cons tx revts ih =>
      intro hwithin
      simp only [List.reverse_cons] at hwithin ⊢
      have hprefix := within_snoc_prefix p revts.reverse tx hwithin
      have hcost := ih hprefix
      obtain ⟨noops, w, he⟩ := execW_success_of_within_snoc p revts.reverse tx hwithin
      have hlocal := hstep revts.reverse tx hwithin noops w he
      rw [runCosts_snoc, he]
      simp only [List.map_append, List.map_cons, List.map_nil, List.sum_append,
        List.sum_cons, List.sum_nil, Nat.add_zero, List.length_append, List.length_singleton]
      omega
  simpa only [List.reverse_reverse] using hf ts.reverse (by simpa using hw)

theorem mergeAmortized_of_runPotentialStep (p : Params)
    (hstep : MergeParamsOK p → RunPotentialStep p) : MergeAmortized p := by
  intro hp ts hw
  have hh := treeFillPotential_run_costs p (hstep hp) ts hw
  simp only [List.sum_eq_foldl] at hh
  exact Nat.le_trans (Nat.le_add_left _ _) hh

end SIS.Tree
