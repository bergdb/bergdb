/-
The tree model (bergdb 024-12, TP4 and TP7): where the pointers of the
writer's overlay come from (`PtrsOK`). Every node that a klong of the overlay
names is a node of P (`Old`) or a node that the transaction made; so is every
overlay node, the space root of the writer's super root, and the node a made
node replaces; the skip pointers of the super root name nodes of P; the
super root is one of P unless the transaction made it, at its own time.

With it TP4 after a transaction needs one more statement about the writer:
no node kept names a node taken back (`TakeBackOKUnder`,
SIS/Tree/PointersRun.lean). SIS/Tree/WriterPtrs*.lean take `PtrsOK` through
the writer.
-/
import SIS.Tree.FreshCache

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- The pointers of the writer's state name nodes of P (`Old`) or nodes that
the transaction made. -/
structure PtrsOK (Old : NodeId → Prop) (c : Ctx) (w : W) : Prop where
  klongs : ∀ q ∈ w.nodes, ∀ cv y, Klong.key cv y ∈ q.2.ks → Old y ∨ y ∈ w.made.map (·.id)
  ids : ∀ q ∈ w.nodes, Old q.1 ∨ q.1 ∈ w.made.map (·.id)
  rootKey : Old w.top.rootKey ∨ w.top.rootKey ∈ w.made.map (·.id)
  skips : ∀ q ∈ w.top.skips, Old q.2
  topId : w.newTop = false → Old w.top.id
  topTime : w.newTop = true → w.top.time = c.i
  madeFor : ∀ q ∈ w.madeFor, Old q.2 ∨ q.2 ∈ w.made.map (·.id)

/-- The writer's view names nodes of P only: its nodes, and the nodes that
the klongs of its nodes name. -/
def ViewPtrsOld (Old : NodeId → Prop) (v : View BVal) : Prop :=
  (∀ x nd, v x = some nd → Old x) ∧
  ∀ x nd, v x = some nd → ∀ cv y, Klong.key cv y ∈ klongsOf nd.hist → Old y

end SIS.Tree
