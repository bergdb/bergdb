/-
bergdb 030-37: a common interface for the no-join and full leaf-join
rebalance estimates. This no-join instance is the accounting of 030-36;
the leaf-join instance is `rebalance_leaf_budget`.
-/
import Contract.Proof.DnbLeafRebalance

namespace Contract.PE

open DNB PeProof

theorem rebalance_noJoin_budget {b : Nat} {cf : Cfg} {s : Tree} {i : Time} {f g h fs : Nat}
    {lv : List (Nat × NodeId)} {os : List (List Op)} {es es2 : List (Nat × VN)}
    {acc acc1 : Acc} (hout : DropOut b cf s fs g lv lv os es acc acc1)
    (hhead : lv.head?.map (·.1) = some 0) (hsort : lv.Pairwise CvLtA)
    (hstop : (kept es).length < 2 ∨ findSmall cf (kept es) = none)
    (hr : rebalance cf i s (f + 1) g h es = some es2) :
    let nd := ((childRs b s fs g lv os).map (·.nd)).sum
    let U := ((childRs b s fs g lv os).map (·.up)).sum
    vcostL es2 ≤ vcostL (kept es) + 2 * nd ∧
      lv.length ≤ (renameHead 0 (entries es2)).length + nd ∧
      (removedCvs lv (renameHead 0 (entries es2))).length +
        ((renameHead 0 (entries es2)).filter (isAdded lv)).length ≤ 4 * nd + U ∧
      (renameHead 0 (entries es2)).length ≤ lv.length +
        ((renameHead 0 (entries es2)).filter (isAdded lv)).length ∧
      (4 * nd + U = 0 → lv.map (fun q => (q.1, some q.2)) = renameHead 0 (entries es2)) := by
  intro nd U
  have heq := rebalance_filter_only hstop hr
  subst heq
  let E := entries (kept es)
  let L := renameHead 0 E
  have hR : (removedCvs lv E).length ≤ nd := hout.removed
  have hA : (E.filter (isAdded lv)).length ≤ U := hout.added
  have hE : E.length ≤ lv.length + (E.filter (isAdded lv)).length := hout.len
  have hLen : L.length = E.length := renameHead_length _ _
  have hhead0 : nd = 0 → L = E := by
    intro hn
    apply renameHead_of_head
    rw [hout.head0 hn, hhead]
  refine ⟨by omega, ?_, ?_, ?_, ?_⟩
  · have hge := flatMap_ents_length_ge (kept es)
    have hlost := hout.lost
    change (kept es).length ≤ E.length at hge
    change lv.length ≤ (kept es).length + nd at hlost
    change lv.length ≤ L.length + nd
    omega
  · change (removedCvs lv L).length + (L.filter (isAdded lv)).length ≤ 4 * nd + U
    by_cases hn : nd = 0
    · rw [hhead0 hn]; omega
    · have hR' := removed_renameHead_le hsort 0 E
      have hA' := added_renameHead_le (lb := lv) 0 E
      change (removedCvs lv L).length ≤ (removedCvs lv E).length + 1 at hR'
      change (L.filter (isAdded lv)).length ≤ (E.filter (isAdded lv)).length + 1 at hA'
      omega
  · have hA' := added_renameHead_ge (lb := lv) 0 E hout.own
    change (E.filter (isAdded lv)).length ≤ (L.filter (isAdded lv)).length at hA'
    change L.length ≤ lv.length + (L.filter (isAdded lv)).length
    omega
  · intro hz
    have hn : nd = 0 := by omega
    change lv.map (fun q => (q.1, some q.2)) = L
    rw [hhead0 hn]
    exact (hout.same0 hn (by change (E.filter (isAdded lv)).length = 0; omega)).symm

end Contract.PE
