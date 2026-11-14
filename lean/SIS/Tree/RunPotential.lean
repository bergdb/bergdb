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

end SIS.Tree
