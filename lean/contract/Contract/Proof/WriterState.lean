/-
The contract package (bergdb 030-10): the writer's state within a put, as the
proofs of the put measure it.

* `PutBooks`: the books of `Mid` that a put relies on (B1, B2, B5, B6, B9,
  B10, B11, B13). The others (B3, B4, B7, B8, B12, B14) serve the delete.
* `PInv`: the state's map is sound from the writer's space root, with the node
  `ex` over its size, and holds the keys C (`Sound`); the frame; the top;
  BalancedOK; the put's books. With no node over its size it is what `Mid`
  says, but for the delete's books (`MidP`).
* `MW.withNode`, `addAll`: the state with a node of the overlay set; a node
  with key klongs added, as `addKeys` adds them. The writer's recursion up the
  key access path (`appendKlongs`) is proved in the form "if node x had these
  klongs, the state would meet `PInv` with x over its size".
* `PathOk`: the key access path up to a depth is a path of the tree from the
  space root, of nodes of the overlay.
-/
import Contract.Proof.WriterWP
import Contract.Proof.Sound
import Contract.Proof.NodeAlg

namespace Contract

open SIS (View)
open SIS.Check (BVal)

/-- What the put's splits ask of the parameters: a node size of 6 or more; a
last version of more than h klongs has two live klongs or more (h at least
2); a last version of at most h klongs with two klongs added fits a node. -/
structure ParamsOK (p : MParams) : Prop where
  size : 6 ≤ p.M
  splitLo : 2 ≤ p.splitAbove
  splitHi : p.splitAbove + 2 ≤ p.M

/-- The books of `Mid` that a put relies on. -/
structure PutBooks (p : MParams) (i : Time) (base : NodeId) (s : Tree) (w : MW) : Prop where
  first : ∀ x n, w.nodes.lookup x = some n → w.taken.contains x = false →
    ((s.obj x).isSome = true ↔ n.firstTime ≠ some i)
  times : ∀ x n, w.nodes.lookup x = some n → ∀ t, SIS.Tree.Klong.time t ∈ n.ks → t ≤ i
  levels : ∀ x n, w.nodes.lookup x = some n → w.taken.contains x = false →
    ∃ g h, w.gh.lookup x = some (g, h) ∧ g ≤ p.G ∧ h ≤ p.H ∧ wLevel s w x = p.keyLevel g h ∧
      n.leaf = (h == 0)
  ids : (∀ x n, w.nodes.lookup x = some n → x < w.next) ∧
    (∀ x h, w.vals.lookup x = some h → x < w.next) ∧
    (∀ m ∈ w.made, m.id < w.next ∧ base ≤ m.id) ∧
    base ≤ w.next ∧ (w.newTop = true → w.top.id < w.next)
  taken : ∀ x, w.taken.contains x = true → x ∈ w.made.map (·.id)
  overlay : ∀ x n, w.nodes.lookup x = some n → (s.obj x).isSome = true ∨ x ∈ w.made.map (·.id)
  within : w.outside = []
  timeFirst : ∀ x n, w.nodes.lookup x = some n → w.taken.contains x = false →
    ∃ t rest, n.ks = SIS.Tree.Klong.time t :: rest

/-- The writer's state within a put: sound from the writer's space root with
the node `ex` over its size, holding the keys C. -/
structure PInv (p : MParams) (i : Time) (base : NodeId) (s : Tree) (tp : Top)
    (ex : Option NodeId) (C : List (Key × Nat)) (w : MW) : Prop where
  root : (treeOf i s w).root = some w.top.rootKey
  sound : Sound p.M ex (treeOf i s w) w.top.rootKey C
  frame : Frame i s (dirtyOf w) (treeOf i s w)
  top : TopInv i s tp w.top w.newTop
  balanced : BalancedAll p (treeOf i s w)
  books : PutBooks p i base s w

/-- `Mid` but for the delete's books: what a put keeps. -/
def MidP (p : MParams) (i : Time) (base : NodeId) (s : Tree) (tp : Top) (done : List Op)
    (w : MW) : Prop :=
  PInv p i base s tp none (applyOps done (contents s)) w

/-- The state with node x of the overlay set to n (`putNode`). -/
def MW.withNode (w : MW) (x : NodeId) (n : MNode) : MW :=
  { w with nodes := SIS.Tree.upsert w.nodes x n }

/-- The node with the key klongs `ins` added at time i, as `addKeys` adds
them. -/
def addAll (i : Time) (n : MNode) (ins : List (Nat × NodeId)) : MNode :=
  ins.foldl (fun n cy => n.add i (.key cy.1 cy.2)) n

/-- The key access path up to `depth` is a path of the tree: it starts at the
space root, each node is in the overlay, and each node but the first is the
live child of the node before it, by the klong noted with it. -/
structure PathOk (i : Time) (s : Tree) (w : MW) (depth : Nat) : Prop where
  root : w.path[0]? = some (none, w.top.rootKey)
  nodes : ∀ d, d ≤ depth → ∃ c u n, w.path[d]? = some (c, u) ∧ w.nodes.lookup u = some n ∧
    w.taken.contains u = false
  links : ∀ d, d < depth → ∃ c0 u c y nu, w.path[d]? = some (c0, u) ∧
    w.path[d + 1]? = some (some c, y) ∧ (treeOf i s w).obj u = some (.key nu) ∧
    (c, y) ∈ live nu.ks

end Contract
