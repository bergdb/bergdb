/-
bergdb 030-21, part 2: what a tree reaches from a node through live klongs, as
a relation (`Rch`), for the bridge's clauses A2 and A3 (Bridge.lean, section
3.4: every node PE writes is reached at its time).
-/
import Contract.Reach

namespace Contract.PE

/-- Node y is reached from node x in T through live klongs: x itself, or
through a live klong of the key node x and on from its pointee. -/
inductive Rch (T : Tree) : NodeId → NodeId → Prop where
  | refl (x : NodeId) : Rch T x x
  | step {x z y : NodeId} {n : KNode} {c : Nat} :
      T.obj x = some (.key n) → (c, z) ∈ live n.ks → Rch T z y → Rch T x y

theorem Rch.trans {T : Tree} {x y z : NodeId} (h1 : Rch T x y) (h2 : Rch T y z) : Rch T x z := by
  induction h1 with
  | refl => exact h2
  | step hx hc _ ih => exact Rch.step hx hc (ih h2)

theorem Rch.one {T : Tree} {x y : NodeId} {n : KNode} {c : Nat} (hx : T.obj x = some (.key n))
    (hc : (c, y) ∈ live n.ks) : Rch T x y :=
  Rch.step hx hc (Rch.refl y)

end Contract.PE
