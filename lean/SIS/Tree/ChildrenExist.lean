/-
A child of a reached inner node exists (bergdb 024-22; agreed with prover
putinv, who proves it for the writer's states from TP7's kinds): the premise of
root collapse that its child is a node.
-/
import SIS.Tree.WriterTree

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- Every live klong of a reached inner node names a node. -/
def InnerChildrenExist (N : NodeId → Option KNode) (t : Time) (r : NodeId) : Prop :=
  ∀ y yn c z, TReach N t r y → N y = some yn → yn.leaf = false → (c, z) ∈ yn.liveAt t →
    ∃ m, N z = some m

end SIS.Tree
