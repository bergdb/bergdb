/-
A key klong's pointer changed in place (`KNode.repoint`): every live klong at
any time is the node's, or names the new pointer. For
the rules that point a klong of the transaction in place (bergdb 024-22: LE-b,
the merge's parent, the take-back, a segment root's split, root collapse).
-/
import SIS.Tree.WriterTreeDelete

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

theorem lastBitmapOf_set_key (l : List Klong) (i : Nat) (c0 : Nat) (y : NodeId)
    (hk : ∃ old, l[i]? = some (.key c0 old)) : lastBitmapOf (l.set i (.key c0 y)) = lastBitmapOf l := by
  unfold lastBitmapOf
  generalize ([] : List Nat) = d
  induction l generalizing i d with
  | nil => simp
  | cons b l ih =>
    cases i with
    | zero =>
      obtain ⟨old, hold⟩ := hk
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hold
      subst hold
      simp
    | succ i =>
      simp only [List.set_cons_succ, List.foldl_cons]
      exact ih i (by simpa using hk) _

end SIS.Tree
