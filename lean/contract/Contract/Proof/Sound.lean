/-
The contract package (bergdb 030-10): `Sound`, the contract's invariants,
TREE and the contents of a tree from its space root, with one node allowed
over the node size; `NodeIs`, what a node of a tree is. The definitions that
the writer's rules are stated with (TreeRules.lean) and that the writer's
state is measured by (WriterState.lean).
-/
import Contract.Proof.TreeCtx

namespace Contract

/-- The tree T from the space root r meets the invariants and TREE, and
holds the keys C; the node `ex` may hold M + 3 klongs. -/
structure Sound (M : Nat) (ex : Option NodeId) (T : Tree) (r : NodeId) (C : List (Key × Nat)) :
    Prop where
  key : ∃ n, T.obj r = some (.key n) ∧ (n.leaf = true ∨ live n.ks ≠ [])
  good : Good T r 0 none
  nodes : ∀ z ∈ reachAt T (T.fuel r) r, ∀ m, T.obj z = some (.key m) →
    nodeOk ⟨if ex = some z then M + 3 else M⟩ T m = true
  holds : L T r = C
  tree : (reachAt T (T.fuel r) r).Nodup

/-- Node u of B is a key node on this level, of this kind, with these live
klongs, and meets the rules of one node (W1 to W4, every klong names a node)
with at most `bound` klongs. -/
def NodeIs (B : Tree) (u : NodeId) (level : Nat) (leaf : Bool) (lv : List (Nat × NodeId))
    (bound : Nat) : Prop :=
  ∃ n, B.obj u = some (.key n) ∧ n.level = level ∧ n.leaf = leaf ∧ live n.ks = lv ∧
    nodeOk ⟨bound⟩ B n = true

/-- The size allowed for node z: M + 3 for the node `ex`. -/
def bnd (M : Nat) (ex : Option NodeId) (z : NodeId) : Nat := if ex = some z then M + 3 else M

end Contract
