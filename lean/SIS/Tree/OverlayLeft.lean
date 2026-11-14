/-
The tree model (bergdb 024-12, TP2 and TP7): the empty key in every inner
node of the writer's overlay (`LeftCache`), the writer's part of the
leftmost rule (LE-b). An inner node has a klong, and a klong of the empty
key (compare value 0) that its last bitmap does not delete (`Live0`); so its
smallest live compare value is the empty key's.

SIS/Tree/WriterLeft*.lean take it through the writer; SIS/Tree/LeftStep.lean
has the node's reading (`Live0` gives the head of the live klongs) and the
step of a run.
-/
import SIS.Tree.FreshCache

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- A klong of the empty key that the node's last bitmap does not delete. -/
def Live0 (n : KNode) : Prop :=
  ∃ i y, n.ks[i]? = some (Klong.key 0 y) ∧ n.lastBitmap.contains i = false

/-- An inner node has a klong and the empty key live. -/
def LeftNode (n : KNode) : Prop := n.leaf = false → n.ks ≠ [] ∧ Live0 n

/-- Every inner node of the overlay has the empty key live. -/
def LeftCache (w : W) : Prop := ∀ q ∈ w.nodes, LeftNode q.2

/-- Every inner key node of the view has the empty key live. -/
def ViewLeftOK (p : Params) (v : View BVal) : Prop :=
  ∀ x nd, v x = some nd → nd.isData = false → nd.level ≤ p.keyMax →
    LeftNode ⟨p.heightOf nd.level == 0, klongsOf nd.hist⟩

/-- Every inner key node of P has the empty key live. -/
def LeftAllOK (p : Params) (P : Struct BVal) : Prop :=
  ∀ x nd, P.get? x = some nd → nd.isData = false → nd.level ≤ p.keyMax →
    LeftNode ⟨p.heightOf nd.level == 0, klongsOf nd.hist⟩

end SIS.Tree
