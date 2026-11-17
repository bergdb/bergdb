/-
The contract package (bergdb 030-10): the statement of the writer's recursion
up the key access path for a key of any number of segments: as
WriterCascadeDefs.lean, but a parent may be a segment leaf (the node split is
then the root of the next segment's tree). `CasPreG` is `CasPre` without
`PathInner`; `UpOkG` is `UpOk` with it.

`SNamed s`: every key klong of every key node of the tree before the
transaction names a node of it. The writer relies on it where it points a
segment leaf's klong to a new segment root in place: the klong names a node
the transaction made, so it is no klong of before the transaction, and the
frame holds.
-/
import Contract.Proof.WriterCascadeDefs

namespace Contract

open SIS (View)
open SIS.Check (BVal)

/-- Every key klong of every key node of s, live or dead, names a node of s. -/
def SNamed (s : Tree) : Prop :=
  ∀ x n, s.obj x = some (.key n) → ∀ c y, Klong.key c y ∈ n.ks → (s.obj y).isSome = true

/-- `CasPre` without `PathInner`: a parent may be a segment leaf. Instead
(`nodup`): no node is twice on the path up to `depth` (with `PathInner` the
levels of the real tree give it; a segment leaf's klongs have no such rule,
and the tree that is sound is the one with x's klongs added). -/
structure CasPreG (p : MParams) (i : Time) (base : NodeId) (s : Tree) (tp : Top) (w : MW)
    (depth : Nat) (x : NodeId) (n : MNode) (ins : List (Nat × NodeId)) (C : List (Key × Nat)) :
    Prop where
  look : w.nodes.lookup x = some n
  on : ∃ c0, w.path[depth]? = some (c0, x)
  path : PathOk i s w depth
  nodup : ∀ e e' c c' u, e < e' → e' ≤ depth → w.path[e]? = some (c, u) →
    w.path[e']? = some (c', u) → False
  books : PutBooks p i base s w
  wf : klongsWf (ksOf n) = true
  size : n.size ≤ p.M
  len : ins.length = 1 ∨ ins.length = 2
  two : ∀ a y1 b y2, ins = [(a, y1), (b, y2)] → a < b ∧ (∃ y, (a, y) ∈ live (ksOf n)) ∧
    ∀ c' y', (c', y') ∈ live (ksOf n) → a < c' → b < c'
  hyp : PInv p i base s tp (some x) C (w.withNode x (addAll i n ins))

/-- `UpOk` with `CasPreG`. -/
def UpOkG (p : MParams) (i : Time) (base : NodeId) (s : Tree) (tp : Top) (v : View BVal)
    (up : NodeId → List (Nat × NodeId) → SIS.Tree.M Unit) (d : Nat) : Prop :=
  ∀ (q : NodeId) (ins : List (Nat × NodeId)) (w : MW) (n : MNode) (C : List (Key × Nat)),
    CasPreG p i base s tp w d q n ins C →
    WP (up q ins) { p := p, i := i, view := v } w (CasPost p i base s tp w d q n ins C)

end Contract
