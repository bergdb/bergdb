/-
The contract package (bergdb 030-08): TREE at earlier times. A tree that
holds a sound tree (`Sub`, Proof/Frame.lean) reaches the same nodes from the
space root, so TREE carries over, as the invariants and the contents do.
-/
import Mathlib.Tactic
import Contract.Reach
import Contract.Proof.Frame

namespace Contract

variable {p : Params} {s s' : Tree}

theorem reachAt_val (hs : Sub s s') {y : NodeId} {h : Nat} (hy : s.obj y = some (.val h)) :
    ∀ f, reachAt s' f y = reachAt s f y
  | 0 => rfl
  | f + 1 => by simp [reachAt, hy, hs.1 y _ hy]

theorem reachAt_kid (hs : Sub s s') {n : KNode} {lo : Nat} {hi : Option Nat} {f : Nat}
    (ih : ∀ y lo hi, walk p s f y lo hi = true → reachAt s' f y = reachAt s f y)
    {c : Nat} {y : NodeId} {rest : List (Nat × NodeId)}
    (h : kidOk s n lo hi (fun y lo' hi' => walk p s f y lo' hi') c y rest = true) :
    reachAt s' f y = reachAt s f y := by
  unfold kidOk at h
  cases ho : s.obj y with
  | none =>
    rw [ho] at h
    by_cases hleaf : n.leaf = true <;> by_cases hlong : isLong c = true <;>
      simp [hleaf, hlong] at h
  | some o =>
    cases o with
    | val v => exact reachAt_val hs ho f
    | key m =>
      rw [ho] at h
      by_cases hleaf : n.leaf = true <;> by_cases hlong : isLong c = true <;>
        simp [hleaf, hlong] at h
      · exact ih _ _ _ h.2.2.2
      · exact ih _ _ _ h.2.2
      · exact ih _ _ _ h.2.2

theorem reachAt_kids (hs : Sub s s') {n : KNode} {lo : Nat} {hi : Option Nat} {f : Nat}
    (ih : ∀ y lo hi, walk p s f y lo hi = true → reachAt s' f y = reachAt s f y) :
    ∀ cs : List (Nat × NodeId),
      kidsOk s n lo hi (fun y lo' hi' => walk p s f y lo' hi') cs = true →
      cs.flatMap (fun cy => reachAt s' f cy.2) = cs.flatMap (fun cy => reachAt s f cy.2)
  | [], _ => rfl
  | (c, y) :: rest, h => by
    simp only [kidsOk, Bool.and_eq_true] at h
    simp only [List.flatMap_cons]
    rw [reachAt_kid hs ih h.1, reachAt_kids hs ih rest h.2]

/-- The larger tree reaches, below a sound node, what the smaller one
reaches. -/
theorem reachAt_sub (hs : Sub s s') : ∀ (f : Nat) (x : NodeId) (lo : Nat) (hi : Option Nat),
    walk p s f x lo hi = true → reachAt s' f x = reachAt s f x
  | 0, _, _, _, h => by simp [walk] at h
  | f + 1, x, lo, hi, h => by
    unfold walk at h
    cases ho : s.obj x with
    | none => simp [ho] at h
    | some o =>
      rw [ho] at h
      cases o with
      | val v => simp at h
      | key n =>
        simp only [Bool.and_eq_true] at h
        simp only [reachAt, ho, hs.1 x _ ho]
        rw [reachAt_kids hs (fun y lo hi hw => reachAt_sub hs f y lo hi hw) _ h.2]

/-- And so does the tree from its space root. -/
theorem reach_sub (hs : Sub s s') (h : invOk p s = true) : reach s' = reach s := by
  unfold invOk Tree.root at h
  unfold reach Tree.root Tree.fuel
  rw [hs.2]
  cases hr : s.roots.getLast?.map (·.2) with
  | none => rfl
  | some r =>
    simp only [hr] at h ⊢
    cases ho : s.obj r with
    | none => simp [ho] at h
    | some o =>
      rw [hs.1 r o ho]
      rw [ho] at h
      cases o with
      | val v => simp at h
      | key n =>
        simp only [Bool.and_eq_true] at h
        exact reachAt_sub hs _ _ _ _ h.2

/-- Earlier times: after a transaction that meets the frame, the tree at an
earlier time reaches the nodes it reached, so it meets TREE if it did. -/
theorem Frame.treeOk {i : Time} {s s' : Tree} {D : List NodeId} (h : Frame i s D s')
    {t : Time} (ht : t < i) (hi : invOk p (s.at t) = true) (htr : TreeOk (s.at t)) :
    TreeOk (s'.at t) := by
  unfold TreeOk at htr ⊢
  rw [reach_sub (h.sub ht) hi]
  exact htr

end Contract
