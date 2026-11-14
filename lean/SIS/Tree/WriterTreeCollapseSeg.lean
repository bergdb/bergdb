/-
Root collapse at a segment root (bergdb 024-22, `OpTreeOK`; `replaceRoot` and
`takeBackRoot` below the segment leaf of the segment above): the leaf's klong
k names the root's only child instead of the root, which is left behind (with
room in the leaf) or taken back.
-/
import SIS.Tree.WriterTreeLeb

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

theorem writerWP_pathNode_known (d : Nat) (y : NodeId) (c : Ctx) (w : W)
    (h : (w.path[d]?).map (·.2) = some y) (post : NodeId → W → Prop) (hp : post y w) :
    WriterWP (pathNode d) c w post := by
  unfold pathNode
  simp only [writerWP_bind, writerWP_get]
  cases he : w.path[d]? with
  | none => rw [he] at h; cases h
  | some e =>
    rw [he] at h
    simp only [Option.map_some, Option.some.injEq] at h
    simp only [writerWP_pure]
    rw [h]; exact hp

theorem writerWP_klongAt_known (d k : Nat) (y : NodeId) (c : Ctx) (w : W)
    (h : w.path[d]? = some (some k, y)) (post : Nat → W → Prop) (hp : post k w) :
    WriterWP (klongAt d) c w post := by
  unfold klongAt
  simp only [writerWP_bind, writerWP_get, h, writerWP_pure]
  exact hp

end SIS.Tree
