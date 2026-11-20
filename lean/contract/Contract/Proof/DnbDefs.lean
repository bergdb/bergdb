/-
bergdb 030-29: definitions of the proof that `Dag.dirtyNodeBound`
(Contract/DirtyBound.lean) bounds the key nodes PE writes.

* `Filled`: the writer's fill rules that the proof needs, as a Prop: from a
  key node x, a segment tree's root (`isRoot`: the space root, or a node a
  segment leaf points to) or not: an inner root has two live klongs at least
  (RootsOK), any other key node m at least when m ≥ 2 (FillOK), and the same
  of every node below. Shape.lean's `shapeFaults` (the trace checker's walk,
  run on Java's tree after every traced transaction) gives it
  (`filled_of_shapeFaults`, DnbFill.lean).
-/
import Contract.DirtyBoundStatement
import Contract.Proof.PeDefs

namespace Contract.PE

/-- The fill rules from key node x (a segment tree's root if `isRoot`): RootsOK
for an inner root, FillOK for any other node (when m ≥ 2), and the same of
every node below it, through the segment leaves' long entries to the next
segment's roots. Of a node that is not a key node nothing is asked. -/
inductive Filled (cf : Cfg) (s : Tree) : Bool → NodeId → Prop where
  | key {isRoot : Bool} {x : NodeId} {n : KNode} :
      s.obj x = some (.key n) →
      (n.leaf = false → isRoot = true → 2 ≤ (live n.ks).length) →
      (2 ≤ cf.m → isRoot = false → cf.m ≤ (live n.ks).length) →
      (∀ c y, (c, y) ∈ live n.ks → n.leaf = true → isLong c = true → Filled cf s true y) →
      (∀ c y, (c, y) ∈ live n.ks → n.leaf = false → Filled cf s false y) →
      Filled cf s isRoot x
  | other {isRoot : Bool} {x : NodeId} :
      (∀ n, s.obj x ≠ some (.key n)) → Filled cf s isRoot x

end Contract.PE
