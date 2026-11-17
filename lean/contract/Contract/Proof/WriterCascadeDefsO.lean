/-
The contract package (bergdb 030-10): the statement of the writer's recursion
up the key access path while a new segment leaf has no klong yet.

A put that makes a new segment leaf (`setNode`, `segment.new`) links the leaf
by a klong before the leaf gets its own first klong. If the segment leaf that
gets that klong is full, it is split, and its parent may be, with the new
leaf still empty: the tree then does not meet the invariants (a node reached
with no live klong). The recursion is proved for the tree as it will be: the
map with some nodes set (`ovSet fs`) to what the writer gives them right
after the recursion (the new segment leaves with their klongs, the value).
The nodes of `fs` are away from the recursion: none is on the key access
path, and none gets its id during the recursion (`CasPostO`'s second
premise: an id of `fs` is below the first id the step makes, or at or above
the next id after it).

`PInvO` is `PInv` with soundness read on the map with `fs` set, and with the
books that allow a node with no klong yet (`PutBooksE`); `CasPreO`,
`CasPostO`, `UpOkO` are `CasPreG`, `CasPost`, `UpOkG` with it. With `fs = []`
they are the forms of WriterCascadeDefsG.lean.
-/
import Contract.Proof.WriterCascadeDefsG

namespace Contract

open SIS (View)
open SIS.Check (BVal)

/-- The tree with the nodes of fs set, in their order. -/
def ovSet (fs : List (NodeId × Obj)) (T : Tree) : Tree :=
  fs.foldl (fun T xo => T.set xo.1 xo.2) T

/-- `PInv` with soundness on the map with `fs` set; a node kept that has no
klong yet is a node of `fs`. -/
structure PInvO (p : MParams) (i : Time) (base : NodeId) (s : Tree) (tp : Top)
    (fs : List (NodeId × Obj)) (ex : Option NodeId) (C : List (Key × Nat)) (w : MW) : Prop where
  root : (treeOf i s w).root = some w.top.rootKey
  sound : Sound p.M ex (ovSet fs (treeOf i s w)) w.top.rootKey C
  frame : Frame i s (dirtyOf w) (treeOf i s w)
  top : WTopInv i s tp w.top w.newTop
  balanced : Balanced p (ovSet fs (treeOf i s w))
  books : PutBooksE p i base s w
  empties : ∀ x n, w.nodes.lookup x = some n → w.taken.contains x = false → n.ks = [] →
    x ∈ fs.map (·.1)

/-- The nodes reached from the space root of the state's map with `fs` set. -/
def reachOfO (i : Time) (s : Tree) (fs : List (NodeId × Obj)) (w : MW) : List NodeId :=
  reachAt (ovSet fs (treeOf i s w)) ((ovSet fs (treeOf i s w)).fuel w.top.rootKey) w.top.rootKey

/-- `CascadePost` with the nodes reached in the map with `fs` set. -/
structure CascadePostO (i : Time) (s : Tree) (fs : List (NodeId × Obj)) (w w0 w' : MW)
    (depth : Nat) : Prop where
  path : w'.path = w.path
  off : ∀ y n, w.nodes.lookup y = some n →
    (∀ d c, d ≤ depth → w.path[d]? ≠ some (c, y)) → w'.nodes.lookup y = some n
  next : w.next ≤ w'.next
  reach : ∀ z ∈ reachOfO i s fs w', z ∈ reachOfO i s fs w0 ∨ w.next ≤ z

/-- `CasPreG` with `fs`: no node of `fs` is on the path up to `depth`; the
books allow a node with no klong yet; x's node starts with a time klong. -/
structure CasPreO (p : MParams) (i : Time) (base : NodeId) (s : Tree) (tp : Top)
    (fs : List (NodeId × Obj)) (w : MW) (depth : Nat) (x : NodeId) (n : MNode)
    (ins : List (Nat × NodeId)) (C : List (Key × Nat)) : Prop where
  look : w.nodes.lookup x = some n
  on : ∃ c0, w.path[depth]? = some (c0, x)
  path : PathOk i s w depth
  nodup : ∀ e e' c c' u, e < e' → e' ≤ depth → w.path[e]? = some (c, u) →
    w.path[e']? = some (c', u) → False
  away : ∀ d c u, d ≤ depth → w.path[d]? = some (c, u) → u ∉ fs.map (·.1)
  books : PutBooksE p i base s w
  first : ∃ t rest, n.ks = SIS.Tree.Klong.time t :: rest
  wf : klongsWf (ksOf n) = true
  size : n.size ≤ p.M
  len : ins.length = 1 ∨ ins.length = 2
  two : ∀ a y1 b y2, ins = [(a, y1), (b, y2)] → a < b ∧ (∃ y, (a, y) ∈ live (ksOf n)) ∧
    ∀ c' y', (c', y') ∈ live (ksOf n) → a < c' → b < c'
  hyp : PInvO p i base s tp fs (some x) C (w.withNode x (addAll i n ins))

/-- After the step: if no key node is outside G and H, and no node of `fs` got
its id during the step, the state meets `PInvO` with no node over its size,
holds the keys C, and `CascadePostO`. -/
def CasPostO (p : MParams) (i : Time) (base : NodeId) (s : Tree) (tp : Top)
    (fs : List (NodeId × Obj)) (w : MW) (depth : Nat) (x : NodeId) (n : MNode)
    (ins : List (Nat × NodeId)) (C : List (Key × Nat)) : Unit → MW → Prop :=
  fun _ w' => w'.outside = [] → (∀ e ∈ fs.map (·.1), e < w.next ∨ w'.next ≤ e) →
    PInvO p i base s tp fs none C w' ∧
      CascadePostO i s fs w (w.withNode x (addAll i n ins)) w' depth

/-- `UpOkG` with `fs`. -/
def UpOkO (p : MParams) (i : Time) (base : NodeId) (s : Tree) (tp : Top) (v : View BVal)
    (fs : List (NodeId × Obj)) (up : NodeId → List (Nat × NodeId) → SIS.Tree.M Unit) (d : Nat) :
    Prop :=
  ∀ (q : NodeId) (ins : List (Nat × NodeId)) (w : MW) (n : MNode) (C : List (Key × Nat)),
    CasPreO p i base s tp fs w d q n ins C →
    WP (up q ins) { p := p, i := i, view := v } w (CasPostO p i base s tp fs w d q n ins C)

end Contract
