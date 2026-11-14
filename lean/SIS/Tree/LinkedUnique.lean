/-
A key access path from the space root to a node of a tree is unique
(bergdb 024-12): two linked paths that end at the same node are equal.
-/
import SIS.Tree.GetPutPath
import SIS.Tree.WriterTreeDepth

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

theorem linkedFrom_unique (N : NodeId → Option KNode) (t : Time) (r : NodeId) (hT : TreeOK N t r)
    (P P' : List (Option Nat × NodeId)) (hP : LinkedFrom N t r P) (hP' : LinkedFrom N t r P')
    (hend : nodeAt r P P.length = nodeAt r P' P'.length) : P = P' := by
  have hPL := LinkedFrom.pathLen N t r P hP
  have hPL' := LinkedFrom.pathLen N t r P' hP'
  have hlen : P.length = P'.length := by
    have a := hPL P.length (Nat.le_refl _)
    have b := hPL' P'.length (Nat.le_refl _)
    rw [hend] at a
    exact PathLen.depth_unique hT _ _ _ a b
  have hnodes : ∀ j, j ≤ P.length → nodeAt r P (P.length - j) = nodeAt r P' (P.length - j) ∧
      (j ≠ 0 → ∃ k, P[P.length - j]? = some (some k, nodeAt r P (P.length - j + 1)) ∧
        P'[P.length - j]? = some (some k, nodeAt r P' (P.length - j + 1))) := by
    intro j
    induction j with
    | zero => intro _; simp only [Nat.sub_zero]; exact ⟨by rw [hend, hlen], fun h => absurd rfl h⟩
    | succ j ih =>
      intro hj
      obtain ⟨hih, _⟩ := ih (by omega)
      have hi : P.length - (j + 1) + 1 = P.length - j := by omega
      obtain ⟨k, n, e1, e2, e3⟩ := LinkedFrom.get N t r P hP (P.length - (j + 1)) (by omega)
      obtain ⟨k', n', e1', e2', e3'⟩ := LinkedFrom.get N t r P' hP' (P.length - (j + 1)) (by omega)
      rw [hi] at e1 e3 e1' e3'
      rw [hih] at e3
      have hr1 := (hPL (P.length - (j + 1)) (by omega)).reach
      have hr2 := (hPL' (P.length - (j + 1)) (by omega)).reach
      obtain ⟨hx, hc⟩ := hT.oneLink _ k _ k' _ hr1 hr2 ⟨n, e2, e3⟩ ⟨n', e2', e3'⟩
      refine ⟨hx, fun _ => ⟨k, ?_, ?_⟩⟩
      · rw [hi]; exact e1
      · rw [hi, hc]; exact e1'
  apply List.ext_getElem? 
  intro i
  rcases Nat.lt_or_ge i P.length with h | h
  · obtain ⟨_, hk⟩ := hnodes (P.length - i) (by omega)
    obtain ⟨k, h1, h2⟩ := hk (by omega)
    have hii : P.length - (P.length - i) = i := by omega
    rw [hii] at h1 h2
    rw [h1, h2]
    have hn := (hnodes (P.length - (i + 1)) (by omega)).1
    have hii' : P.length - (P.length - (i + 1)) = i + 1 := by omega
    rw [hii'] at hn
    rw [hn]
  · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]

end SIS.Tree
