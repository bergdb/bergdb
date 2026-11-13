/-
Self-indexed streams in Lean: bounds, part 3, the nodes a change makes
unreachable (bergdb item 007; 007-03, step 6). Trusted part: an assumption on
BergDB's tree, stated as a definition, that bounds `removedAt` (SIS/BoundCold.lean).
The theorems are in SIS/BoundColdDTheorems.lean, the proofs in
SIS/Proof/BoundColdD.lean. Added 2026-11-13.

The prose it comes from:

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

/-- The change c at time j to P drops no subtree (BergDB: a split replaces a
node by new nodes that take its children; a new klong replaces the key's
previous one):

1. a node reachable at j - 1 and at j loses at most as many live children as c
   gives it entries (a split's parent gets entries for the new nodes and loses
   the node split; a key node gets a klong and loses its previous value);
2. every live child at j - 1 of a node that c makes unreachable is reachable at
   j (a split's new nodes take the children of the node they split).

To check on Java's runs, as TREE and A6' are. -/
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
