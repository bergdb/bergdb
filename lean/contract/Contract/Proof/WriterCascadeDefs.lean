/-
The contract package (bergdb 030-10): the statement of the writer's recursion
up the key access path, `appendKlongs` with `handleFullWith` (Java's
`Dag.appendKlongs` and `handleFullNode`): key klongs go into a node; a full
node is replaced by its last version (a time split) or by two halves (a
space split), and its parent gets one or two klongs in turn, up to a new
space root.

The form: if the state with the klongs added to node x, x then maybe over
its size, meets `PInv` and holds the keys C (`CasPre`), then the step, where
it gives no error and leaves no key node outside the bounds G and H, ends in
a state that meets `PInv` with no node over its size and holds the keys C
(`CasPost`). For a key of one segment: x is a node of the space root's
segment tree, so a parent is an inner node (`PathInner`).
-/
import Contract.Proof.WriterPrim
import Contract.Proof.WriterTop
import Contract.Proof.NodeAlg2
import Contract.Proof.TreeRules

namespace Contract

open SIS (View)
open SIS.Check (BVal)

/-- The nodes reached from the space root of the state's map. -/
def reachOf (i : Time) (s : Tree) (w : MW) : List NodeId :=
  reachAt (treeOf i s w) ((treeOf i s w).fuel w.top.rootKey) w.top.rootKey

/-- What the step at `depth` of the key access path leaves for its caller,
from the state w (w0 is w with the klongs added to its node): the path is
kept; a node of the overlay that is not on the path up to `depth` is kept as
it is; ids are only added; a node reached after it was reached in w0 or is
new. -/
structure CascadePost (i : Time) (s : Tree) (w w0 w' : MW) (depth : Nat) : Prop where
  path : w'.path = w.path
  off : ∀ y n, w.nodes.lookup y = some n →
    (∀ d c, d ≤ depth → w.path[d]? ≠ some (c, y)) → w'.nodes.lookup y = some n
  next : w.next ≤ w'.next
  reach : ∀ z ∈ reachOf i s w', z ∈ reachOf i s w0 ∨ w.next ≤ z

/-- The path up to `depth` is in the space root's segment tree: every node
on it above `depth` is an inner node. (So for a key of one segment.) -/
def PathInner (w : MW) (depth : Nat) : Prop :=
  ∀ d c u n, d < depth → w.path[d]? = some (c, u) → w.nodes.lookup u = some n → n.leaf = false

/-- Before the step for node x at `depth` of the path, with its node n of the
overlay and the klongs `ins` to add: the path is a path of the tree; the
books; n is well formed and fits a node; one klong or two, and two are the
halves of a split of the child at the first one's compare value a: a is a
live klong of n, the second one's compare value b is above a and below every
live klong of n above a; and the state with the klongs added to x meets
`PInv` with x over its size and holds the keys C. -/
structure CasPre (p : MParams) (i : Time) (base : NodeId) (s : Tree) (tp : Top) (w : MW)
    (depth : Nat) (x : NodeId) (n : MNode) (ins : List (Nat × NodeId)) (C : List (Key × Nat)) :
    Prop where
  look : w.nodes.lookup x = some n
  on : ∃ c0, w.path[depth]? = some (c0, x)
  path : PathOk i s w depth
  nodup : ∀ e e' c c' u, e < e' → e' ≤ depth → w.path[e]? = some (c, u) →
    w.path[e']? = some (c', u) → False
  inner : PathInner w depth
  books : PutBooks p i base s w
  wf : klongsWf (ksOf n) = true
  size : n.size ≤ p.M
  len : ins.length = 1 ∨ ins.length = 2
  two : ∀ a y1 b y2, ins = [(a, y1), (b, y2)] → a < b ∧ (∃ y, (a, y) ∈ live (ksOf n)) ∧
    ∀ c' y', (c', y') ∈ live (ksOf n) → a < c' → b < c'
  hyp : PInv p i base s tp (some x) C (w.withNode x (addAll i n ins))

/-- After the step: if no key node is outside G and H, the state meets `PInv`
with no node over its size, holds the keys C, and `CascadePost`. -/
def CasPost (p : MParams) (i : Time) (base : NodeId) (s : Tree) (tp : Top) (w : MW)
    (depth : Nat) (x : NodeId) (n : MNode) (ins : List (Nat × NodeId)) (C : List (Key × Nat)) :
    Unit → MW → Prop :=
  fun _ w' => w'.outside = [] →
    PInv p i base s tp none C w' ∧ CascadePost i s w (w.withNode x (addAll i n ins)) w' depth

/-- The step `up`, which gives klongs to a parent at depth d, meets the
statement. -/
def UpOk (p : MParams) (i : Time) (base : NodeId) (s : Tree) (tp : Top) (v : View BVal)
    (up : NodeId → List (Nat × NodeId) → SIS.Tree.M Unit) (d : Nat) : Prop :=
  ∀ (q : NodeId) (ins : List (Nat × NodeId)) (w : MW) (n : MNode) (C : List (Key × Nat)),
    CasPre p i base s tp w d q n ins C →
    WP (up q ins) { p := p, i := i, view := v } w (CasPost p i base s tp w d q n ins C)

end Contract
