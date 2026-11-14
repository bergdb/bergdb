/-
The per-segment fuel as an invariant (bergdb 024-22, step 4 of the coordinator's
plan of 2026-11-13): every segment tree is balanced, its segment leaves all at
one depth (`SegDepthEq`), so that a descent that succeeds bounds the whole tree.
-/
import SIS.Tree.FuelPaths
import SIS.Tree.WriterGetCollapseLoop

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- The segment tree of x has all its segment leaves at depth d: at depth 0 x is
a segment leaf, else an inner node whose live children are at depth d - 1. -/
def SegDepthEq (N : NodeId → Option KNode) (t : Time) : Nat → NodeId → Prop
  | 0, x => ∀ n, N x = some n → n.leaf = true
  | d + 1, x => ∀ n, N x = some n → n.leaf = false ∧ ∀ c y, (c, y) ∈ n.liveAt t → SegDepthEq N t d y

theorem SegDepthEq.le {N : NodeId → Option KNode} {t : Time} :
    ∀ d x, SegDepthEq N t d x → SegDepthLe N t d x := by
  intro d
  induction d with
  | zero => intro x h; exact h
  | succ d ih =>
    intro x h n hn _ c y hy
    exact ih y ((h n hn).2 c y hy)

/-- A descent of the writer that reaches a segment leaf from a node of depth d
had fuel above d: with no more fuel, it throws. -/
theorem writerWP_descendLte_depth (cv : Nat) (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base) :
    ∀ (f d : Nat) (x : NodeId) (w : W), SegDepthEq (wNode c.p base w) c.i d x →
      (∀ q ∈ eqVisits (wNode c.p base w) c.i cv f x, w.taken.contains q.1 = false) →
      WriterWP (descendLte cv f x) c w (fun _ _ => d < f) := by
  intro f
  induction f with
  | zero => intro d x w _ _; exact writerWP_throw _ _ _ _
  | succ f ih =>
    intro d x w hd ht
    unfold descendLte
    simp only [writerWP_bind, writerWP_read]
    refine writerWP_mono (writerWP_getNode_reads x c w base hvc) ?_
    intro n v ⟨hrv, _, hwn⟩
    have hx := hwn (ht (x, cv) (by simp [eqVisits]))
    split
    · rename_i hleaf
      simp only [writerWP_pure]
      cases d with
      | zero => omega
      | succ d => have := (hd n hx).1; rw [hleaf] at this; cases this
    · rename_i hleaf
      split
      · exact writerWP_throw _ _ _ _
      · rename_i fd hfd
        cases d with
        | zero => have := hd n hx; simp only [Bool.not_eq_true] at hleaf; rw [hleaf] at this; cases this
        | succ d =>
          have hy := (hd n hx).2 fd.c fd.y (KNode.searchLte_mem n c.i cv fd hfd)
          simp only [writerWP_bind]
          refine writerWP_mono (writerWP_pathAdd_reads (some fd.c) fd.y c v base) ?_
          intro _ v1 hr1
          have hr01 := ReadsAs.trans _ _ _ _ _ hrv hr1
          have hy1 : SegDepthEq (wNode c.p base v1) c.i d fd.y := by rw [hr01.1]; exact hy
          have ht1 : ∀ q ∈ eqVisits (wNode c.p base v1) c.i cv f fd.y, v1.taken.contains q.1 = false := by
            intro q hq
            rw [hr01.2.2.1]
            rw [hr01.1] at hq
            apply ht q
            simp only [eqVisits, hx, Bool.not_eq_true] at hleaf ⊢
            simp only [hleaf, Bool.false_eq_true, ↓reduceIte, hfd, List.mem_cons]
            exact Or.inr hq
          exact writerWP_mono (ih d fd.y v1 hy1 ht1) (fun _ _ h => by omega)

end SIS.Tree
