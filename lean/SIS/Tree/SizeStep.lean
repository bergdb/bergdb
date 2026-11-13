/-
The tree model (bergdb 024-12, TP7): TP5 after a transaction. Every key node
of P has at most M klongs (`SizeOK`), so every key node of the writer's view
of P@(i-1) has (`sizeStep_view`), and the writer keeps every node of its
overlay at most M klongs (`execW_sizeOK`). A key node of the structure after
the transaction is a node of the overlay, with the overlay's klongs, or a key
node of P as it was (`apply_keyNode`), so it has at most M klongs
(`sizeOK_step`).
-/
import SIS.Tree.KeyHistRun
import SIS.Tree.WriterSizeMerge

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- The key nodes of the writer's view of P@t are key nodes of P, so they have
at most M klongs. -/
theorem sizeStep_view (p : Params) (P : Struct BVal) (t : Time) (htimes : StructTimesLE P t)
    (hS : SizeOK p P) : ViewSizeOK p (view (treeSpec p) P t) := by
  intro x nd hx hd hl
  have hg := view_eq_get? p P t htimes x nd hx
  have := hS x _ (keyNodeAt_of p P x nd hg hd hl)
  simpa [nodeK, KNode.size] using this

/-- A node of the overlay found by `lookup` is a member of it. -/
theorem sizeStep_lookup_mem (l : List (NodeId × KNode)) (x : NodeId) (n : KNode)
    (h : l.lookup x = some n) : (x, n) ∈ l := by
  obtain ⟨pre, post, he, _⟩ := List.lookup_eq_some_iff.mp h
  rw [he]
  simp

/-- TP5 after a transaction: for a successful run of the writer at time i on
P@(i-1), with the premises of `apply_keyNode`, every key node of the structure
after it has at most M klongs if every key node of P has. -/
theorem sizeOK_step (p : Params) (P : Struct BVal) (i : Time) (tx : Tx) (bs : List Bool) (w : W)
    (hp : MergeParamsOK p) (hpos : 0 < i) (hfresh : ∀ q ∈ P, q.1 < tx.base)
    (htimes : StructTimesLE P (i - 1))
    (hroot : ∃ r, P.get? root = some r ∧ p.keyMax < r.level) (hH : KeyHistOK p P)
    (hl : ViewLinksOK tx.base p (view (treeSpec p) P (i - 1)))
    (hS : SizeOK p P)
    (he : execW p tx i (view (treeSpec p) P (i - 1)) = .ok (bs, w)) :
    SizeOK p (P.apply i (changesOf i w)) := by
  have hw := execW_sizeOK p tx i _ bs w hp (sizeStep_view p P (i - 1) htimes hS) he
  intro x n hn
  unfold keyNodeAt at hn
  cases hx : (P.apply i (changesOf i w)).get? x with
  | none => simp [hx] at hn
  | some nd' =>
    rw [hx] at hn
    cases hd : nd'.isData with
    | true => simp [hd] at hn
    | false =>
      by_cases hlv : nd'.level ≤ p.keyMax
      · simp only [hd, hlv, Bool.not_false, decide_true, Bool.and_self, ↓reduceIte,
          Option.some.injEq] at hn
        subst hn
        show (klongsOf nd'.hist).length ≤ p.M
        rcases apply_keyNode p P i tx bs w hpos hfresh htimes hroot hH hl he x nd' hx hd hlv with
          ⟨n0, hlook, _, _, hks, _⟩ | ⟨hp0, _⟩
        · rw [hks]
          exact (hw _ (sizeStep_lookup_mem _ x n0 hlook)).1
        · have := hS x _ (keyNodeAt_of p P x nd' hp0 hd hlv)
          simpa [nodeK, KNode.size] using this
      · simp [hd, hlv] at hn

end SIS.Tree
