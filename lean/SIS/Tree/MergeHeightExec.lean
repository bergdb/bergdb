import SIS.Tree.MergeOpBoundProof
import SIS.Tree.MergeRootBoundedExec

namespace SIS.Tree

open SIS SIS.Check

/-- The root is excluded from the merge levels, so cap rather than cap + 1
is enough when cap bounds all heights seen during the transaction. -/
theorem execW_mergeRootHeightBound_of_cache (p : Params) (tx : Tx) (i : Time) (v : View BVal)
    (noops : List Bool) (w : W) (cap : Nat)
    (h : execW p tx i v = .ok (noops,w)) (hc : SeenHeightBound cap w) :
    w.merges ≤ deletesOf tx noops * cap := by
  unfold execW runOps runOpsFrom at h
  cases hz : lastTop v with
  | none => simp [hz] at h
  | some z =>
    simp only [hz] at h
    cases ht : topOf p (rootless v) z with
    | error e => simp [ht] at h
    | ok top =>
      simp only [ht] at h
      have hr := boundsOK_ok p _ noops w h
      have hb := writerWP_ops_rootHeightBound {p := p, i := i, view := rootless v}
        {next := tx.base, top := top} tx.ops cap noops w hr hc
      simpa [deletesOf] using hb

/-- A bound using every height seen during the transaction, including nodes
that are taken back before its final bounds check. -/
theorem execW_mergeHeightBound_of_cache (p : Params) (tx : Tx) (i : Time) (v : View BVal)
    (noops : List Bool) (w : W) (cap : Nat)
    (h : execW p tx i v = .ok (noops,w)) (hc : SeenHeightBound cap w) :
    w.merges ≤ deletesOf tx noops * (cap+1) := by
  have hb := execW_mergeRootHeightBound_of_cache p tx i v noops w cap h hc
  have hm : deletesOf tx noops * cap ≤ deletesOf tx noops * (cap+1) :=
    Nat.mul_le_mul_left _ (by omega)
  exact Nat.le_trans hb hm

/-- The largest height recorded by the writer. The cache retains taken-back
nodes, so this is a bound during the transaction, rather than just at its end. -/
def maxSeenHeight : List (NodeId × Nat × Nat) → Nat
  | [] => 0
  | q :: qs => max q.2.2 (maxSeenHeight qs)

theorem le_maxSeenHeight (ns : List (NodeId × Nat × Nat)) (x g h : Nat)
    (hm : (x,g,h) ∈ ns) : h ≤ maxSeenHeight ns := by
  induction ns with
  | nil => simp at hm
  | cons q qs ih =>
    simp only [List.mem_cons] at hm
    rcases hm with rfl | hm
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih hm) (Nat.le_max_right _ _)

theorem maxSeenHeight_le (ns : List (NodeId × Nat × Nat)) (cap : Nat)
    (hb : ∀ x g h, (x,g,h) ∈ ns → h ≤ cap) : maxSeenHeight ns ≤ cap := by
  induction ns with
  | nil => exact Nat.zero_le _
  | cons q qs ih =>
    have hh := hb q.1 q.2.1 q.2.2 (by simp)
    have ht := ih (fun x g h hm => hb x g h (by simp [hm]))
    simp only [maxSeenHeight]
    omega

/-- An unconditional height-sensitive bound, with the actual maximum cached
height instead of the descent fuel. -/
theorem execW_mergeSeenHeightBound (p : Params) (tx : Tx) (i : Time) (v : View BVal)
    (noops : List Bool) (w : W) (h : execW p tx i v = .ok (noops,w)) :
    w.merges ≤ deletesOf tx noops * (maxSeenHeight w.gh+1) := by
  apply execW_mergeHeightBound_of_cache p tx i v noops w _ h
  exact le_maxSeenHeight w.gh

/-- The H + 1 bound when the writer's whole height cache is within H. -/
theorem execW_mergeHeightBound (p : Params) (tx : Tx) (i : Time) (v : View BVal)
    (noops : List Bool) (w : W) (h : execW p tx i v = .ok (noops,w))
    (hc : SeenHeightBound p.H w) :
    w.merges ≤ deletesOf tx noops * (p.H+1) :=
  execW_mergeHeightBound_of_cache p tx i v noops w p.H h hc

/-- An unconditional bound by the actual maximum height: there is at most
one merge a height strictly below the segment root, per effective delete. -/
theorem execW_mergeRootSeenHeightBound (p : Params) (tx : Tx) (i : Time) (v : View BVal)
    (noops : List Bool) (w : W) (h : execW p tx i v = .ok (noops,w)) :
    w.merges ≤ deletesOf tx noops * maxSeenHeight w.gh := by
  apply execW_mergeRootHeightBound_of_cache p tx i v noops w _ h
  exact le_maxSeenHeight w.gh

/-- TP32 follows when temporary nodes are at most one height above H. This
premise allows a root made and taken back within a successful operation. -/
theorem execW_mergeOpBound_of_transientHeight (p : Params) (tx : Tx) (i : Time) (v : View BVal)
    (noops : List Bool) (w : W) (h : execW p tx i v = .ok (noops,w))
    (hc : SeenHeightBound (p.H+1) w) :
    w.merges ≤ deletesOf tx noops * (p.H+1) :=
  execW_mergeRootHeightBound_of_cache p tx i v noops w (p.H+1) h hc

end SIS.Tree
