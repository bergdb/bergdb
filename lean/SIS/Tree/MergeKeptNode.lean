import SIS.Tree.FreshCache

namespace SIS.Tree

open SIS SIS.Check

structure NodeGuard where
  id : NodeId
  node : KNode
  g : Nat
  h : Nat

def GuardHeld (b : NodeGuard) (w : W) : Prop :=
  w.nodes.lookup b.id = some b.node ∧ w.gh.lookup b.id = some (b.g,b.h) ∧
    b.id ∉ w.taken ∧ b.id < w.next

end SIS.Tree
