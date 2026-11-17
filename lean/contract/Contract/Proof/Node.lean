/-
The contract package (bergdb 030-04): one node. The live klongs of a node are
in strictly increasing order of their compare values, and Java's searches
(Tree.lean) are lookups in the live klongs.
-/
import Mathlib.Tactic
import Contract.Statement

namespace Contract

/-- The order of live klongs: by compare value, strictly. -/
abbrev CvLt (a b : Nat × NodeId) : Prop := a.1 < b.1

theorem live_sorted (ks : List Klong) : (live ks).Pairwise CvLt := by
  sorry

theorem searchEq_spec (ks : List Klong) (h : klongsWf ks = true) (c : Nat) :
    searchEq ks c = (live ks).lookup c := by
  sorry

theorem searchLte_spec (ks : List Klong) (p : Pos) :
    searchLte ks p = ((live ks).filter (fun cy => !p.below cy.1)).getLast? := by
  sorry

theorem searchLt_spec (ks : List Klong) (p : Pos) :
    searchLt ks p = ((live ks).filter (fun cy => p.above cy.1)).getLast? := by
  sorry

theorem searchGt_spec (ks : List Klong) (p : Pos) :
    searchGt ks p = ((live ks).filter (fun cy => p.below cy.1)).head? := by
  sorry

theorem searchGte_spec (ks : List Klong) (p : Pos) :
    searchGte ks p = ((live ks).filter (fun cy => !p.above cy.1)).head? := by
  sorry

end Contract
