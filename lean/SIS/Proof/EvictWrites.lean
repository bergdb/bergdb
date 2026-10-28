/-
Proofs for stage 2 (bergdb item 001, WP E3), part 10: the physical writer's two
loops (the new data nodes, then the taken nodes) write the model's record, and
leave the invariant of the next state.
-/
import SIS.Proof.EvictApplyInv

set_option linter.unusedSectionVars false

namespace SIS

variable {V T : Type} [DecidableEq V]

/-! ## What the writer's loop changes -/

section Loop

variable (sp : Spec V T) (S0 : Stream V T) (D : Dirty) (i : Nat)

end Loop

/-! ## The two loops of a transaction -/

section Writes

variable {sp : Spec V T} {al : Algo V T} {db : DB V T} {tr : T} {S0 : Stream V T} {k : Nat}

/-- The nodes taken are in D. -/
theorem step_taken_inD {k : Nat} (hinv : Inv sp db k) {x : NodeId}
    (hx : x ∈ (parts sp al db tr).taken) : ∃ d, (x, d) ∈ db.D ∧ d ≤ (parts sp al db tr).s := by
  obtain ⟨d, hd, hds⟩ := (step_taken_mem sp al db tr x).mp hx
  rcases (step_D1_mem sp al db tr hinv.len _).mp hd with h | ⟨h, -⟩
  · exact ⟨d, h, hds⟩
  · exfalso; simp only at h; have := step_s_le sp al db tr hinv.len; omega

theorem dOf_of_mem : ∀ {D : Dirty}, (D.map (·.1)).Nodup → ∀ {z : NodeId} {d : Nat}, (z, d) ∈ D →
    dOf D z = some d
  | [], _, _, _, h => by cases h
  | e :: D, hnd, z, d, h => by
    simp only [List.map_cons, List.nodup_cons] at hnd
    unfold dOf
    simp only [List.find?_cons]
    rcases List.mem_cons.mp h with rfl | h
    · simp
    · have hne : e.1 ≠ z := by
        intro he; apply hnd.1; rw [he]; exact List.mem_map.mpr ⟨(z, d), h, rfl⟩
      have : (e.1 == z) = false := by simp [hne]
      simp only [this]
      exact dOf_of_mem hnd.2 h

theorem mem_of_dOf {D : Dirty} {z : NodeId} {d : Nat} (h : dOf D z = some d) : (z, d) ∈ D := by
  unfold dOf at h
  cases hf : D.find? (fun e => e.1 == z) with
  | none => rw [hf] at h; cases h
  | some e =>
    rw [hf] at h
    simp only [Option.map_some, Option.some.injEq] at h
    have he := List.find?_some hf
    simp only [beq_iff_eq] at he
    have hm := List.mem_of_find?_eq_some hf
    rw [← he, ← h]
    exact hm

theorem dOf_inD {D : Dirty} {z : NodeId} (h : inD D z = true) : ∃ d, dOf D z = some d := by
  obtain ⟨d, hd⟩ := (inD_iff D z).mp h
  unfold dOf
  cases hf : D.find? (fun e => e.1 == z) with
  | none =>
    exfalso
    rw [List.find?_eq_none] at hf
    exact hf (z, d) hd (by simp)
  | some e => exact ⟨e.2, rfl⟩

/-- An entry of D after the transaction: got dirty in it, or an entry of D before
that was not taken. -/
theorem step_D'_entry {k : Nat} (hinv : Inv sp db k) {z : NodeId} {d : Nat}
    (h : (z, d) ∈ (parts sp al db tr).r7.1) : d = k + 1 ∨ ((z, d) ∈ db.D ∧ (parts sp al db tr).s < d) := by
  rw [(step_r7_shape sp al db tr hinv.len).1] at h
  rcases List.mem_append.mp h with h | h
  · obtain ⟨hD1, hs⟩ := (step_D2_mem sp al db tr _).mp h
    rcases (step_D1_mem sp al db tr hinv.len _).mp hD1 with h1 | ⟨h1, -⟩
    · exact Or.inr ⟨h1, hs⟩
    · exact Or.inl h1
  · obtain ⟨x, -, hx⟩ := List.mem_map.mp h
    simp only [Prod.mk.injEq] at hx
    exact Or.inl hx.2.symm

theorem lv_building_Snew (z : NodeId) :
    (db.S.building (parts sp al db tr).vs).lv z = (Snew sp al db tr).lv z := by
  unfold Snew Stream.building
  rw [lv_append, lv_append]
  simp [Stream.lv, parts_R]

end Writes

end SIS
