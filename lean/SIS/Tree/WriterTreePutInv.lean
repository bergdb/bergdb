/-
The writer's tree kept by every put at leaf level without an inner split
(bergdb 024-22, `OpTreeOK`), under prover latest's writer invariant `PutInv`
(GetPutInv.lean): a put into a space whose root is a leaf, and a put into a
leaf below inner nodes with room for two klongs, each case by the rule that the
leaf's state chooses. Here: the facts of `PutInv` that these rules take.
-/
import SIS.Tree.WriterTreeMergeOp
import SIS.Tree.GetPutInv

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- The facts of `PutInv` that the tree's put rules take. -/
theorem PutInv.facts (c : Ctx) (base : View BVal) (w : W) (hI : PutInv c base w) :
    (∀ x xn, ReachS (wNode c.p base w) c.i w.top.rootKey x →
      wNode c.p base w x = some xn → klongsWf xn.ks = true) ∧
    (∀ z, w.next ≤ z → knodeOf c.p base z = none) ∧
    (∀ z, w.next ≤ z → ∀ u c', TReach (wNode c.p base w) c.i w.top.rootKey u →
      ¬ TLink (wNode c.p base w) c.i u c' z) ∧
    (∀ z, w.next ≤ z → wNode c.p base w z = none) ∧
    (∀ (key : List Nat), ∀ q ∈ fromVisits (wNode c.p base w) c.i c.p.fuel key w.top.rootKey,
      w.taken.contains q.1 = false) := by
  obtain ⟨hidn, _, hidt, _, _⟩ := hI.ids
  have hwf : ∀ x xn, ReachS (wNode c.p base w) c.i w.top.rootKey x →
      wNode c.p base w x = some xn → klongsWf xn.ks = true := fun x xn _ hn => hI.wf x xn hn
  refine ⟨hwf, fun z hz => (hI.fresh z hz).1, ?_, ?_, ?_⟩
  · intro z hz u c' hu hl
    obtain ⟨m, hm, hc⟩ := hl
    have := hI.links u m c' z (tReach_reachS _ _ _ _ hu) hm hc
    omega
  · intro z hz
    have htz : w.taken.contains z = false := by
      cases h' : w.taken.contains z with
      | false => rfl
      | true => have := hidt z h'; omega
    have hnz : w.nodes.lookup z = none := by
      cases h' : w.nodes.lookup z with
      | none => rfl
      | some _ => have := hidn z (by rw [h']; rfl); omega
    simp only [wNode, htz, Bool.false_eq_true, ↓reduceIte, hnz, (hI.fresh z hz).1]
  · intro key q hq
    exact hI.untaken q.1 (fromVisits_reach _ _ _ _ hwf key _ q.1 q.2 ReachS.root hq)

end SIS.Tree
