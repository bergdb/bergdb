/-
The tree model with option 2 of dead klongs (bergdb 024-23; 024-18, section
4): the stated properties of the rule, TP39 and TP40, in 024-12's series. Each
is a definition of type `Prop`. TP39 is computed after every transaction by
`treetest` (with `theta`), and on Java's traces by `treecheck` (C-T6), through
the invariants' walk (`DeadOK`); neither is proved. Proved here: the local form
of the rule (a write that `deadOver` lets through leaves at most theta) and the
values of `Params.thetaFor` at the node sizes of a database. Trusted part: the
statements.

The rule's other consequences are statements of 024-12 and 024-22 already,
which take the parameters, so with `Params.withTheta` they speak of the tree
with option 2: V1 and BU1's count (TP29 to TP31; a compaction keeps every live
klong), TP23 (`dirtyNodeBound`, with the count of 024-23, 2.6), TP26.
-/
import SIS.Tree.MergeProps

namespace SIS.Tree

open SIS SIS.Check

/-! ## theta -/

/-- theta at the node sizes of a database (024-23, OD2; 024-19, Q4): 2, 3, 7 and
14 at 8, 14, 30 and 62; off below 8. -/
theorem thetaFor_values :
    Params.thetaFor 8 = 2 ∧ Params.thetaFor 14 = 3 ∧ Params.thetaFor 30 = 7 ∧
      Params.thetaFor 62 = 14 ∧ Params.thetaFor 6 = 0 := by
  decide

/-- From node size 8 theta is on, and at least 2 (024-19, Q4). -/
theorem thetaFor_pos (m : Nat) (h : 8 ≤ m) : 2 ≤ Params.thetaFor m := by
  simp only [Params.thetaFor, show ¬ m < 8 from by omega, ↓reduceIte]
  omega

/-! ## TP39, TP40: the bound -/

/-- The local form of the rule: a node with a write applied that `deadOver`
lets through holds at most theta dead klongs. -/
theorem deadOver_false (p : Params) (n : KNode) (h : deadOver p n = false) (ht : p.theta ≠ 0) :
    n.deadCount ≤ p.theta := by
  simp only [deadOver, Bool.and_eq_false_iff, bne_eq_false_iff_eq, decide_eq_false_iff_not] at h
  rcases h with h | h
  · exact absurd h ht
  · omega

/-- TP39 (024-23, 2.5): with option 2 on, after every transaction of a run
within reach, every key node reachable at its time holds at most theta dead key
klongs. `walk` checks it (`DeadOK`), so it is part of `InvOK` (TP6) with theta
on. -/
def DeadBoundOK (p : Params) : Prop :=
  p.theta ≠ 0 → ∀ ts, Within p ts → ∀ x ∈ keyNodesAt p (treeRun p ts) ts.length,
    ∀ n, keyNodeAt p (treeRun p ts) x = some n → n.deadCount ≤ p.theta

/-- TP40 (024-23, 2.5), the bound write by write: with option 2 on, if every
key node of P@(i-1) holds at most theta dead klongs, then every key node that
the writer holds at the transaction's end (read, made or changed, and not
taken back; a replaced node with its klongs of the transaction dropped) holds
at most theta. Each write keeps it: `deadOver` or a compaction (whose node
holds at most one dead klong, a space split's half one shadowed klong of the
parent's write). -/
def DeadWriteOK (p : Params) : Prop :=
  p.theta ≠ 0 → ∀ ts, Within p ts → ∀ (tx : Tx) noops w,
    (∀ x n, keyNodeAt p (treeRun p ts) x = some n → n.deadCount ≤ p.theta) →
    execW p tx (ts.length + 1) (view (treeSpec p) (treeRun p ts) ts.length) = .ok (noops, w) →
    ∀ q ∈ w.nodes, w.taken.contains q.1 = false → q.2.deadCount ≤ p.theta

end SIS.Tree
