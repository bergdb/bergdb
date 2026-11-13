/-
The tree model (bergdb 024-12, TP7): the kinds of the nodes that the klongs
of the writer's overlay name (`KindCache`), for every klong, live or dead.
An inner node's klong names a key node of the node's segment; a segment
leaf's klong of a long segment names a key node of the next segment, any
other a value. What a node is: its entry in the writer's list of segments
and heights (`W.gh`) or of values (`W.vals`), or what P says of it
(`KindOracle`).

The heights are not in it: a dead klong can name a node of another height
(`takeBack` retargets a klong to the node that a made node replaced, which
for a root made by a split is one height lower). The walk of the invariants
asks, for live klongs, also that an inner node's child is one height below
it; that part is not proved here.

SIS/Tree/WriterKinds*.lean take `KindCache` through the writer;
SIS/Tree/KindsStep.lean has the step of a run.
-/
import SIS.Tree.OverlayBook

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- What P says of its nodes: a key node of segment g, or a value. -/
structure KindOracle where
  key : NodeId → Nat → Prop
  val : NodeId → Prop

/-- y is a key node of segment g: in the writer's list, or one of P. -/
def IsKeySeg (K : KindOracle) (w : W) (y : NodeId) (g : Nat) : Prop :=
  (∃ h, (y, g, h) ∈ w.gh) ∨ K.key y g

/-- y is a value: one the transaction made, or one of P. -/
def IsValId (K : KindOracle) (w : W) (y : NodeId) : Prop :=
  (∃ hh, (y, hh) ∈ w.vals) ∨ K.val y

/-- The klong (c, y) of a node of segment g and height h names a node of the
right kind. -/
def KindKlong (K : KindOracle) (w : W) (g h c : Nat) (y : NodeId) : Prop :=
  (h ≠ 0 → IsKeySeg K w y g) ∧
  (h = 0 → (segLen c = 7 → IsKeySeg K w y (g + 1)) ∧ (segLen c ≠ 7 → IsValId K w y))

/-- Every klong of every overlay node names a node of the right kind. -/
def KindCache (K : KindOracle) (w : W) : Prop :=
  ∀ x n g h, (x, n) ∈ w.nodes → (x, g, h) ∈ w.gh →
    ∀ c y, Klong.key c y ∈ n.ks → KindKlong K w g h c y

/-- The key access path follows klongs of the right kind: the node of an
entry is of the kind that the klong of the entry promises in the node of
the entry before it. -/
def PathKinds (K : KindOracle) (w : W) : Prop :=
  ∀ d a q c y, w.path[d]? = some (a, q) → w.path[d + 1]? = some (some c, y) →
    ∀ g h, (q, g, h) ∈ w.gh → KindKlong K w g h c y

/-- A made node and the node it replaces are of one segment. -/
def MadeForSeg (K : KindOracle) (w : W) : Prop :=
  ∀ q ∈ w.madeFor, ∀ g h, (q.1, g, h) ∈ w.gh → IsKeySeg K w q.2 g

/-- What the oracle must meet for the writer's view, with B the
transaction's first id: it knows only ids below B; a node has one kind and
one segment; a key node of the view is a key node of its level's segment;
and the klongs of the view's key nodes name nodes of the right kind. -/
structure ViewKinds (K : KindOracle) (B : NodeId) (c : Ctx) : Prop where
  old : ∀ y g, K.key y g → y < B
  oldVal : ∀ y, K.val y → y < B
  seg : ∀ y g g', K.key y g → K.key y g' → g = g'
  notBoth : ∀ y g, K.key y g → ¬ K.val y
  node : ∀ x nd, c.view x = some nd → nd.isData = false → nd.level ≤ c.p.keyMax →
    K.key x (c.p.segOf nd.level)
  klongs : ∀ x nd, c.view x = some nd → nd.isData = false → nd.level ≤ c.p.keyMax →
    ∀ cv y, Klong.key cv y ∈ klongsOf nd.hist →
      (c.p.heightOf nd.level ≠ 0 → K.key y (c.p.segOf nd.level)) ∧
      (c.p.heightOf nd.level = 0 →
        (segLen cv = 7 → K.key y (c.p.segOf nd.level + 1)) ∧ (segLen cv ≠ 7 → K.val y))

/-- A statement about `appendKlongs` that the walk of the kinds takes as a
premise: an empty segment leaf of the overlay that is not the node appended
to and not on the key access path stays as it is. (It is the new segment
leaf of `setNode`, between its making and the next step of `putSegs`.) -/
def AppendFrameOK (B : NodeId) : Prop :=
  ∀ (depth : Nat) (x : NodeId) (ins : List (Nat × NodeId)) (c : Ctx) (w : W) (y : NodeId),
    ViewIdsBelow B c.view → Book B c w → w.nodes.lookup y = some ⟨true, []⟩ → y ≠ x →
    (∀ e ∈ w.path, e.2 ≠ y) →
    WriterWP (appendKlongs depth x ins) c w (fun _ v => v.nodes.lookup y = some ⟨true, []⟩)

/-- The kinds in P, for every klong of every key node: an inner node's klong
names a key node of its segment; a segment leaf's klong of a long segment a
key node of the next segment, any other a value; for the nodes named that
are nodes of P. -/
def KindsAllOK (p : Params) (P : Struct BVal) : Prop :=
  ∀ x nd, P.get? x = some nd → nd.isData = false → nd.level ≤ p.keyMax →
    ∀ c y, Klong.key c y ∈ klongsOf nd.hist → ∀ ny, P.get? y = some ny →
      (p.heightOf nd.level ≠ 0 →
        ny.isData = false ∧ ny.level ≤ p.keyMax ∧ p.segOf ny.level = p.segOf nd.level) ∧
      (p.heightOf nd.level = 0 →
        (segLen c = 7 →
          ny.isData = false ∧ ny.level ≤ p.keyMax ∧ p.segOf ny.level = p.segOf nd.level + 1) ∧
        (segLen c ≠ 7 → ny.isData = true))

/-- The oracle of a structure P. -/
def kindOracleOf (p : Params) (P : Struct BVal) : KindOracle where
  key := fun y g => ∃ ny, P.get? y = some ny ∧ ny.isData = false ∧ ny.level ≤ p.keyMax ∧
    p.segOf ny.level = g
  val := fun y => ∃ ny, P.get? y = some ny ∧ ny.isData = true

end SIS.Tree
