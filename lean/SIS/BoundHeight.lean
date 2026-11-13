/-
Self-indexed streams in Lean: bounds counted by the height of the tree, not by
level numbers (bergdb item 007; 007-09, section 5). Trusted part: the
definition. The theorems are in SIS/BoundHeightTheorems.lean, the proofs in
SIS/Proof/BoundHeight.lean. Added 2026-11-13.

The prose (007-09, section 5, "Levels in BergDB's tree"): "The counts use the
root's level number as H. In 024-12's `treeSpec` (`lean/SIS/Tree/Spec.lean`)
a level is a code of segment and height, the top nodes have levels of their
own, and the virtual root is on level keyMax + 2 + 2^48 - 1. So (H + 1) and
lev(x) + 1 say nothing useful there. A bound for BergDB would count the nodes
on a path, the height, not the level number." And 007-01, 5.2: "BergDB never
merges nodes, so h is the log of the largest tree the database has had".
-/
import SIS.Basic

namespace SIS

variable {V T : Type}

/-- Every chain of live pointers at time t down from x has at most h steps:
x's live height at t is at most h (0 for a node without live children at t).
For BergDB's virtual root, its live child at t is the top node (skip pointers
to older top nodes are dead), so the root's live height at t is the tree's
height at t plus one. -/
def LiveHeightLe (sp : Spec V T) (P : Struct V) (t : Time) : Nat → NodeId → Prop
  | 0, x => ∀ n, P.get? x = some n → sp.live (n.hist.upTo t) = []
  | h + 1, x => ∀ n, P.get? x = some n → ∀ y ∈ sp.live (n.hist.upTo t), LiveHeightLe sp P t h y

end SIS
