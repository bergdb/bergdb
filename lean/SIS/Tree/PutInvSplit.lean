import SIS.Tree.PutInvRoom
import SIS.Tree.GetInPlace
import SIS.Tree.WriterTreeRoot
import SIS.Tree.WriterTreeMerge

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-! Facts of `PutInv` for the time splits of a put (bergdb 024-12, TP10): in
place (a leaf the transaction made becomes its last version with the put's
klong), and of a leaf that existed before the transaction below an inner
parent with room (a new node holds the last version, the parent's klong names
it). -/

theorem PutInv.lt_next {c : Ctx} {base : View BVal} {w : W} (hI : PutInv c base w)
    (x : NodeId) (xn : KNode) (h : wNode c.p base w x = some xn) : x < w.next := by
  rcases (wNode_cases _ _ _ _ _ h).2 with hl | ⟨_, hk⟩
  · exact hI.ids.1 x (by rw [hl]; rfl)
  · cases Nat.lt_or_ge x w.next with
    | inl h => exact h
    | inr h => rw [(hI.fresh x h).1] at hk; cases hk

theorem PutInv.none_of_ge {c : Ctx} {base : View BVal} {w : W} (hI : PutInv c base w)
    (z : NodeId) (hz : w.next ≤ z) : wNode c.p base w z = none := by
  cases h : wNode c.p base w z with
  | none => rfl
  | some xn => have := hI.lt_next z xn h; omega

theorem PutInv.untaken_of_ge {c : Ctx} {base : View BVal} {w : W} (hI : PutInv c base w)
    (z : NodeId) (hz : w.next ≤ z) : w.taken.contains z = false := by
  cases h' : w.taken.contains z with
  | false => rfl
  | true => have := hI.ids.2.2.1 _ h'; omega

/-- A property of the start that every live link keeps holds of every node
reachable. -/
theorem reachS_closed (N' : NodeId → Option KNode) (t : Time) (r' : NodeId) (P : NodeId → Prop)
    (hr : P r') (hstep : ∀ x xn c z, P x → N' x = some xn → (c, z) ∈ xn.liveAt t → P z) :
    ∀ x, ReachS N' t r' x → P x := by
  intro x hx
  induction hx with
  | root => exact hr
  | step x n c z _ hn hc ih => exact hstep x n c z ih hn hc

/-- Every node reachable in the writer's tree has an id below the next one. -/
theorem PutInv.reach_lt {c : Ctx} {base : View BVal} {w : W} (hI : PutInv c base w)
    (x : NodeId) (hx : ReachS (wNode c.p base w) c.i w.top.rootKey x) : x < w.next := by
  induction hx with
  | root => exact hI.ids.2.2.2.2
  | step x n cc z hx hn hc _ => exact hI.links x n cc z hx hn hc

end SIS.Tree
