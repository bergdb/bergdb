/-
Self-indexed streams in Lean: bounds, part 3, the nodes a change makes
unreachable (bergdb item 007; 007-03, step 6). Trusted part: an assumption,
stated as a definition (`DropStep`), that bounds `removedAt` (SIS/BoundCold.lean).
The theorems are in SIS/BoundColdDTheorems.lean, the proofs in
SIS/Proof/BoundColdD.lean. Added 2026-11-13.

`DropStep` is not BergDB's. It was written as an assumption on BergDB's tree,
and it is false for Java (bergdb 007-09, section 2.2, and its second review):
one delete bitmap removes several children with one entry
(`Dag.appendDeleteKlong`), against its first point, and the upward delete
unlinks a parent with its children (`Dag.deleteUpward`), against its second.
SIS/BoundColdDropJExample.lean shows both failures on runs of 024-12's tree
model (`treeSpec`). It is replaced by `DropStepJ` (SIS/BoundColdDropJ.lean):
for `treeSpec`, `DropRunOKJ` holds with BergDB's weights (`bvalW`) and, for each
transaction, k the nodes it makes unreachable, given `RunOK`, BergDB's
still-dirty test and TREE (`DropRunOKJ_tree_removed`). `DropStep`, `DropRunOK`
and the theorems on them (`removedAt_bound`, `coldReads_tree_drop`,
`coldReads_height`) stay: they are true of the model, and no other theorem
uses them (bergdb 007-09, section 6, Q2, option B).

The prose it came from:

* lean/README.md, "Not done" (2026-11-13): "a bound on the nodes a transaction
  makes unreachable (`removedAt`, in `coldReads_tree`; one per split in BergDB,
  not an assumption of the model)".
* `coldReads_tree` (SIS/BoundColdTheorems.lean): "In BergDB a node that a
  transaction makes unreachable is one a split replaces, a child of a node
  given an entry."
* `PhysStep` (SIS/Phys.lean): "a split's new nodes take the children of the
  node they split, which stops being current or changes (bergdb 001-08, M43:
  no path moves a child from one current node to another)"; and "a key node's
  pointer (its klong) is live until a later klong of the same key".

Without an assumption no bound holds: a change that gives a node an entry that
replaces a live child by a new empty node makes the child's whole subtree
unreachable, and meets `RunOK` and TREE.
-/
import SIS.BoundCold

namespace SIS

variable {V T : Type} [DecidableEq V]

/-- The live children of node p at j - 1 in P that are not live children of p
at j in P' (the structure after the change at j), without repeats: the
children p loses at j. -/
def lostLive (sp : Spec V T) (P P' : Struct V) (j : Time) (p : NodeId) : List NodeId :=
  match P.get? p, P'.get? p with
  | some n, some n' =>
    (sp.live (n.hist.upTo (j - 1))).eraseDups.filter (fun y => !(sp.live (n'.hist.upTo j)).contains y)
  | _, _ => []

/-- The change c at time j to P drops no subtree (as first thought of BergDB: a
split replaces a node by new nodes that take its children; a new klong
replaces the key's previous one):

1. a node reachable at j - 1 and at j loses at most as many live children as c
   gives it entries (a split's parent gets entries for the new nodes and loses
   the node split; a key node gets a klong and loses its previous value);
2. every live child at j - 1 of a node that c makes unreachable is reachable at
   j (a split's new nodes take the children of the node they split).

False for Java (see the file's header); `DropStepJ` (SIS/BoundColdDropJ.lean)
replaces it. -/
structure DropStep (sp : Spec V T) (P : Struct V) (j : Time) (c : Changes V) : Prop where
  lost : ∀ p, reachable sp P (j - 1) p = true → reachable sp (P.apply j c) j p = true →
    (lostLive sp P (P.apply j c) j p).length ≤ (c.adds.filter (fun a => a.1 == p)).length
  adopted : ∀ z n, reachable sp P (j - 1) z = true → reachable sp (P.apply j c) j z = false →
    P.get? z = some n → ∀ y ∈ sp.live (n.hist.upTo (j - 1)), reachable sp (P.apply j c) j y = true

/-- `DropStep` for every transaction of a run. -/
def DropRunOK (sp : Spec V T) (al : Algo V T) (ts : List T) : Prop :=
  ∀ j (h : j < ts.length),
    let db := run sp al (ts.take j)
    DropStep sp db.P (j + 1) (sp.exec ts[j] (j + 1) (view sp db.P j))

end SIS
