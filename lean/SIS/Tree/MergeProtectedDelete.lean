import SIS.Tree.MergeKeptNode

namespace SIS.Tree

open SIS SIS.Check

/-- A physical live key prevents the all-keys-deleted test. -/
theorem KNode.allKeysIn_false_of_live_key (n : KNode) (del : List Nat)
    (a : Nat) (y : NodeId) (i : Nat) (hm : (.key a y,i) ∈ n.ks.zipIdx)
    (hi : i ∉ del) : n.allKeysIn del = false := by
  cases he : n.allKeysIn del with
  | false => rfl
  | true =>
    have ha := List.all_eq_true.mp he (.key a y,i) hm
    have hd : i ∈ del := by simpa using ha
    exact False.elim (hi hd)

end SIS.Tree
