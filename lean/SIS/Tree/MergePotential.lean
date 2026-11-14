import SIS.Tree.DeleteCount

namespace SIS.Tree

open SIS SIS.Check

/-- A nonroot node has one unit for its existence and one per missing live
entry below m. Roots have no such units. -/
def fillPotential (m cnt : Nat) : Nat := 1 + (m-cnt)

/-- The replacement potential of the current reachable key nodes. -/
def treeFillPotential (p : Params) (P : Struct BVal) (t : Time) : Nat :=
  ((nodesRootsAt p P t).map (fun q => if q.2 then 0 else
    ((keyNodeAt p P q.1).map (fun n => fillPotential p.mergeBelow (n.liveAt t).length)).getD 0)).sum

end SIS.Tree
