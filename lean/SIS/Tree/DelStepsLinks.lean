/-
The links and klongs of the state after the upward loop from its books (bergdb
024-12): every node names ids below the next id and has well-formed klongs;
these facts hold at every state with the books
(`PutBook`, `putInvG_of_book`), so the stop node's cascade and LE-b need only
`UpUnlinkOK` and the fuel.
-/
import SIS.Tree.DelStepsLebFull

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- A state with the books names ids below the next id from every node, and
every node's klongs are well formed. -/
theorem linksWf_of_book (c : Ctx) (base : View BVal) (B : NodeId) (top0 : Top) (v w2 : W)
    (hB : PutBase c base B) (hb : PutBook c B top0 v)
    (hv : v = w2 ∨ ∃ s, v = { w2 with trail := s :: w2.trail }) :
    (∀ u c' z, TLink (wNode c.p base w2) c.i u c' z → z < w2.next) ∧
    (∀ z zn, wNode c.p base w2 z = some zn → klongsWf zn.ks = true) := by
  have hG := putInvG_of_book c base B top0 v hB hb
  have hwv : wNode c.p base v = wNode c.p base w2 := by
    rcases hv with rfl | ⟨s, rfl⟩ <;> rfl
  have hnx : v.next = w2.next := by rcases hv with rfl | ⟨s, rfl⟩ <;> rfl
  refine ⟨fun u c' z ⟨un, hun, hl⟩ => ?_, fun z zn h => ?_⟩
  · rw [← hwv] at hun
    rw [← hnx]
    exact hG.links u un c' z hun hl
  · rw [← hwv] at h
    exact hG.wf z zn h

end SIS.Tree
