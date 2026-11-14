import SIS.Tree.GetChain

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-! The space split of an inner node (bergdb 024-12, TP10; the cascades): the
halves of an inner node's last version with a klong put find, for compare values
below the second half's first one, what the first half finds, and from it on,
what the second finds, the second half's first klong renamed to the empty key
(`halves_inner_searchLte`). -/

/-- `getEqR_split` for an inner node L split into the inner halves F and S: the
descents of N2 are those of Nm on the nodes that Nm reaches but L, F and S, and
from F (below sc) or S (from sc on) as from L. -/
theorem getEqR_split_inner (Nm N2 : NodeId → Option KNode) (t : Time) (r0 L q F S : NodeId)
    (qn qn2 m f s : KNode) (sc : Nat)
    (hNq : Nm q = some qn) (hql : qn.leaf = false) (hN2q : N2 q = some qn2)
    (hq2l : qn2.leaf = false)
    (hqsearch : ∀ c : Nat, (qn2.searchLte t c).map (·.y) =
      (qn.searchLte t c).map (fun fd => if fd.y = L then (if c < sc then F else S) else fd.y))
    (hNmL : Nm L = some m) (hml : m.leaf = false) (hrL : ReachS Nm t r0 L)
    (hN2F : N2 F = some f) (hfl : f.leaf = false) (hN2S : N2 S = some s) (hsl : s.leaf = false)
    (hsF : ∀ c : Nat, c < sc → (f.searchLte t c).map (·.y) = (m.searchLte t c).map (·.y))
    (hsS : ∀ c : Nat, sc ≤ c → (s.searchLte t c).map (·.y) = (m.searchLte t c).map (·.y))
    (hsame : ∀ x, x ≠ L → x ≠ q → x ≠ F → x ≠ S → N2 x = Nm x)
    (hnotL : ∀ x xn c z, ReachS Nm t r0 x → x ≠ q → Nm x = some xn → (c, z) ∈ xn.liveAt t → z ≠ L)
    (hnotFS : ∀ x xn c z, ReachS Nm t r0 x → Nm x = some xn → (c, z) ∈ xn.liveAt t →
      z ≠ F ∧ z ≠ S) (hLq : L ≠ q) (c : Nat) :
    ∀ (fu : Nat), (∀ (x : NodeId), ReachS Nm t r0 x → x ≠ L → x ≠ F → x ≠ S →
      getEqR N2 t c fu x = getEqR Nm t c fu x) ∧
      getEqR N2 t c fu (if c < sc then F else S) = getEqR Nm t c fu L := by
  intro fu
  induction fu with
  | zero => exact ⟨fun _ _ _ _ _ => rfl, rfl⟩
  | succ fu ih =>
    obtain ⟨ihP, ihQ⟩ := ih
    refine ⟨?_, ?_⟩
    · intro x hx hxL hxF hxS
      by_cases hxq : x = q
      · subst hxq
        simp only [getEqR, hNq, hN2q, hql, hq2l, Bool.false_eq_true, ↓reduceIte]
        have hs := hqsearch c
        cases h1 : qn.searchLte t c with
        | none =>
          rw [h1] at hs
          cases h2 : qn2.searchLte t c with
          | none => rfl
          | some _ => rw [h2] at hs; cases hs
        | some fd =>
          rw [h1] at hs
          cases h2 : qn2.searchLte t c with
          | none => rw [h2] at hs; cases hs
          | some fd2 =>
            rw [h2] at hs
            simp only [Option.map_some, Option.some.injEq] at hs
            simp only
            have hmem := KNode.searchLte_mem qn t c fd h1
            have hrfd : ReachS Nm t r0 fd.y := ReachS.step x qn fd.c fd.y hx hNq hmem
            by_cases hL : fd.y = L
            · rw [hL] at hs
              simp only [↓reduceIte] at hs
              rw [hs, hL]
              exact ihQ
            · simp only [hL, ↓reduceIte] at hs
              rw [hs]
              have hfs := hnotFS x qn fd.c fd.y hx hNq hmem
              exact ihP fd.y hrfd hL hfs.1 hfs.2
      · have he := hsame x hxL hxq hxF hxS
        simp only [getEqR, he]
        cases hn : Nm x with
        | none => rfl
        | some xn =>
          simp only
          split
          · rfl
          · cases h1 : xn.searchLte t c with
            | none => rfl
            | some fd =>
              simp only
              have hmem := KNode.searchLte_mem xn t c fd h1
              have hrfd : ReachS Nm t r0 fd.y := ReachS.step x xn fd.c fd.y hx hn hmem
              have hfs := hnotFS x xn fd.c fd.y hx hn hmem
              exact ihP fd.y hrfd (hnotL x xn fd.c fd.y hx hxq hn hmem) hfs.1 hfs.2
    · -- the halves search as L does, then the same child
      have hchild : ∀ fd : Found, m.searchLte t c = some fd →
          getEqR N2 t c fu fd.y = getEqR Nm t c fu fd.y := by
        intro fd hfd
        have hmem := KNode.searchLte_mem m t c fd hfd
        have hfs := hnotFS L m fd.c fd.y hrL hNmL hmem
        exact ihP fd.y (ReachS.step L m fd.c fd.y hrL hNmL hmem)
          (hnotL L m fd.c fd.y hrL hLq hNmL hmem) hfs.1 hfs.2
      by_cases hc : c < sc
      · simp only [hc, ↓reduceIte, getEqR, hN2F, hfl, hNmL, hml, Bool.false_eq_true]
        have he := hsF c hc
        cases h1 : m.searchLte t c with
        | none =>
          rw [h1] at he
          cases h2 : f.searchLte t c with
          | none => rfl
          | some _ => rw [h2] at he; cases he
        | some fd =>
          rw [h1] at he
          cases h2 : f.searchLte t c with
          | none => rw [h2] at he; cases he
          | some fd2 =>
            rw [h2] at he
            simp only [Option.map_some, Option.some.injEq] at he
            simp only
            rw [he]
            exact hchild fd h1
      · simp only [hc, ↓reduceIte, getEqR, hN2S, hsl, hNmL, hml, Bool.false_eq_true]
        have he := hsS c (by omega)
        cases h1 : m.searchLte t c with
        | none =>
          rw [h1] at he
          cases h2 : s.searchLte t c with
          | none => rfl
          | some _ => rw [h2] at he; cases he
        | some fd =>
          rw [h1] at he
          cases h2 : s.searchLte t c with
          | none => rw [h2] at he; cases he
          | some fd2 =>
            rw [h2] at he
            simp only [Option.map_some, Option.some.injEq] at he
            simp only
            rw [he]
            exact hchild fd h1

/-! ## The writer: a time split of a leaf whose inner parent is full and space split -/

/-! ## The reading after a leaf's time split and its parent's space split -/

/-! ## The rule: a time split of a leaf and a space split of its full parent -/

end SIS.Tree
