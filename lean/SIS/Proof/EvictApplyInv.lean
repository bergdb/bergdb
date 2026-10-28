/-
Proofs for stage 2 (bergdb item 001, WP E3), part 9: after the writer's paths,
the change applied to the canonical objects gives `AInv`.
-/
import SIS.Proof.EvictApply

set_option linter.unusedSectionVars false

namespace SIS

variable {V T : Type} [DecidableEq V]

theorem pointees_append_mem {sp : Spec V T} {h1 h2 : History V} {y : NodeId}
    (hy : y ∈ pointees sp (h1 ++ h2)) : y ∈ pointees sp h1 ∨ y ∈ pointees sp h2 := by
  rw [mem_pointees] at hy
  obtain ⟨e, he, hye⟩ := hy
  rcases List.mem_append.mp he with he | he
  · exact Or.inl ((mem_pointees sp h1 y).mpr ⟨e, he, hye⟩)
  · exact Or.inr ((mem_pointees sp h2 y).mpr ⟨e, he, hye⟩)

theorem pointees_adds_mem {sp : Spec V T} {L : List (NodeId × V)} {j : Time} {y : NodeId}
    (hy : y ∈ pointees sp (L.map (fun a => (⟨j, a.2⟩ : Entry V)))) :
    ∃ a ∈ L, y ∈ sp.ptrs a.2 := by
  rw [mem_pointees] at hy
  obtain ⟨e, he, hye⟩ := hy
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp he
  exact ⟨a, ha, hye⟩

section ApplyInv

variable {sp : Spec V T} {db : DB V T} {S0 : Stream V T} {k : Nat} {m : Mem V} {c : Changes V}

end ApplyInv

end SIS
