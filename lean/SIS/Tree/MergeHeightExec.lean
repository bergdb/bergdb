import SIS.Tree.MergeOpBoundProof
import SIS.Tree.MergeRootHeight

namespace SIS.Tree

open SIS SIS.Check

/-- The largest height recorded by the writer. The cache retains taken-back
nodes, so this is a bound during the transaction, rather than just at its end. -/
def maxSeenHeight : List (NodeId × Nat × Nat) → Nat
  | [] => 0
  | q :: qs => max q.2.2 (maxSeenHeight qs)

theorem le_maxSeenHeight (ns : List (NodeId × Nat × Nat)) (x g h : Nat)
    (hm : (x,g,h) ∈ ns) : h ≤ maxSeenHeight ns := by
  induction ns with
  | nil => simp at hm
  | cons q qs ih =>
    simp only [List.mem_cons] at hm
    rcases hm with rfl | hm
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih hm) (Nat.le_max_right _ _)

theorem maxSeenHeight_le (ns : List (NodeId × Nat × Nat)) (cap : Nat)
    (hb : ∀ x g h, (x,g,h) ∈ ns → h ≤ cap) : maxSeenHeight ns ≤ cap := by
  induction ns with
  | nil => exact Nat.zero_le _
  | cons q qs ih =>
    have hh := hb q.1 q.2.1 q.2.2 (by simp)
    have ht := ih (fun x g h hm => hb x g h (by simp [hm]))
    simp only [maxSeenHeight]
    omega

end SIS.Tree
