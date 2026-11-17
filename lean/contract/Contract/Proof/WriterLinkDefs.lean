/-
The contract package (bergdb 030-16): the link book, `LinkLive`, that the
take-back needs (030-10's B14 in another form).

A take-back (`takeBack`, a merge's `takenBack`, `takeBackRoot`) makes a node
the transaction made no node at all. The map then has no node for its id, so
no klong of a node reached may name it (PointersOK, live or dead). The writer
points the klongs of the transaction in the node's parent elsewhere
(`retarget`); that this reaches every klong that names the node is the link
book: in a node reached, an inner node, a key klong that names a node that is
no node of the tree before (a node the transaction made) names a node that the
node names by a live klong. With TREE (a node has one live parent) only the
parent names it. Kept by every step of the writer: a dead klong to a node of
the transaction is made only where the writer then points it to a node the
parent names live (`retarget`), or where the node it names is of before (the
klong of a node that a split replaced).
-/
import Contract.Proof.WriterDelDefs

namespace Contract

open SIS (View)
open SIS.Check (BVal)

/-- The link book of the state w of the transaction at time i from the tree s:
every key klong of an inner node reached that names a node of no node of s
names a node the node names by a live klong. -/
def LinkLive (i : Time) (s : Tree) (w : MW) : Prop :=
  ∀ u ∈ reachOf i s w, ∀ nu, (treeOf i s w).obj u = some (.key nu) → nu.leaf = false →
    ∀ c o, Klong.key c o ∈ nu.ks → s.obj o = none → ∃ c', (c', o) ∈ live nu.ks

end Contract
