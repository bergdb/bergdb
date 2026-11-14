import SIS.Tree.GetCascadeChain
import SIS.Tree.RangeSim

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-! Cascades of time and space splits of any depth keep the walk's ranges
(bergdb 024-12, TP10; `RangeOrder`): prover cost's cascade with the ranges
carried along. -/

/-- A fold of pair lookups from a found value finds one. -/
theorem pairLookupFold_isSome (c : Nat) :
    ∀ (ins : List (Nat × NodeId)) (acc : Option NodeId), acc.isSome = true →
      ∃ z, ins.foldl (pairLookupStep c) acc = some z := by
  intro ins
  induction ins with
  | nil =>
    intro acc h
    cases acc with
    | none => cases h
    | some z => exact ⟨z, rfl⟩
  | cons a rest ih =>
    intro acc h
    rw [List.foldl_cons]
    apply ih
    unfold pairLookupStep
    split
    · rfl
    · exact h

/-- A live klong of a node with two or more, below its divider. -/
theorem live_below_divider (n : KNode) (r : Nat × NodeId) (h2 : 2 ≤ n.live.length)
    (hr : (n.live.drop (n.live.length / 2)).head? = some r) : ∃ a ∈ n.live, a.1 < r.1 := by
  have hleft := halves_left_lt_divider n.live (n.live.length / 2) n.live_order r hr
  obtain ⟨a, ha⟩ : ∃ a, a ∈ n.live.take (n.live.length / 2) := by
    cases h : n.live.take (n.live.length / 2) with
    | nil =>
      exfalso
      have := congrArg List.length h
      simp only [List.length_take, List.length_nil] at this
      omega
    | cons a _ => exact ⟨a, List.mem_cons_self⟩
  exact ⟨a, List.mem_of_mem_take ha, hleft a ha⟩

end SIS.Tree
