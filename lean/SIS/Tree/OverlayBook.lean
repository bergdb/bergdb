/-
The tree model (bergdb 024-12, TP7): the writer's books of its overlay, as a
statement about its state (`Book`). The overlay holds a key node for each
entry of the list of segments and heights (`W.gh`), in the order of the
list, each id once; a node's leaf flag is that of its height; a node of the
view has the segment and height of its level; a node of the transaction is
in the list of made nodes with the level of its segment and height, and is
noted if it is outside the level bounds; a node taken back is in the
overlay; the transaction's own top node is not.

With it the structure after the transaction has, for every overlay node not
taken back, a key node of the overlay's kind (SIS/Tree/OverlayLift.lean).
SIS/Tree/WriterBook*.lean take it through the writer. `TakenAbove`: the
nodes taken back are the transaction's (SIS/Tree/WriterTaken*.lean).
-/
import SIS.Tree.FreshCache

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- The writer's books agree, with B the transaction's first id. -/
structure Book (B : NodeId) (c : Ctx) (w : W) : Prop where
  next : B ≤ w.next
  ids : w.nodes.map (·.1) = (w.gh.map (·.1)).reverse
  bound : ∀ q ∈ w.gh, q.1 < w.next
  nodup : (w.gh.map (·.1)).Nodup
  leaf : ∀ x n g h, (x, n) ∈ w.nodes → (x, g, h) ∈ w.gh → n.leaf = (h == 0)
  tag : ∀ x g h, (x, g, h) ∈ w.gh →
    (∃ nd, c.view x = some nd ∧ nd.isData = false ∧ nd.level ≤ c.p.keyMax ∧
      g = c.p.segOf nd.level ∧ h = c.p.heightOf nd.level) ∨
    (B ≤ x ∧ (⟨x, c.p.keyLevel g h, false⟩ : NewNode) ∈ w.made ∧
      ((c.p.G < g ∨ c.p.H < h) → (x, g, h) ∈ w.outside))
  taken : ∀ x ∈ w.taken, x ∈ w.gh.map (·.1)
  top : w.newTop = true → B ≤ w.top.id ∧ w.top.id < w.next ∧ w.top.id ∉ w.gh.map (·.1)

/-- The nodes taken back are nodes of the transaction. -/
def TakenAbove (B : NodeId) (w : W) : Prop := ∀ x ∈ w.taken, B ≤ x

end SIS.Tree
