/-
Proofs for stage 2 (bergdb item 001, WP E3), part 5: the writer's follow. Through
a live slot of the canonical object of a current node, the writer reaches its
child's canonical object, or the snapshot of the child's latest version, which
it makes canonical (`Mem.promote`); the invariant is kept.
-/
import SIS.Proof.EvictFollow

set_option linter.unusedSectionVars false

namespace SIS

variable {V T : Type} [DecidableEq V]

theorem mem_pointees_of_live' {sp : Spec V T} (hls : LiveSub sp) {h : History V} {y : NodeId}
    (hy : y ∈ sp.live h) : y ∈ pointees sp h := by
  obtain ⟨e, he, hye⟩ := hls _ _ hy
  simp only [pointees, List.mem_eraseDups, List.mem_flatMap]
  exact ⟨e, he, hye⟩

section Clean

variable {sp : Spec V T} {db : DB V T} {S0 : Stream V T} {k : Nat} {m : Mem V}

end Clean

/-! ## Promotion of a snapshot -/

section Promote

variable {sp : Spec V T} {db : DB V T} {S0 : Stream V T} {k : Nat} {m : Mem V}

theorem setTable_nodup (m : Mem V) (y : NodeId) (h : Nat) (hnd : (m.table.map (·.1)).Nodup) :
    ((m.setTable y h).table.map (·.1)).Nodup := by
  unfold Mem.setTable
  simp only [List.map_cons, List.nodup_cons]
  refine ⟨?_, (List.Sublist.map _ List.filter_sublist).nodup hnd⟩
  intro hm
  obtain ⟨p, hp, hpy⟩ := List.mem_map.mp hm
  have := (List.mem_filter.mp hp).2
  rw [hpy] at this
  simp at this

end Promote

/-! ## The writer's follow -/

section Writer

variable {sp : Spec V T} {db : DB V T} {S0 : Stream V T} {k : Nat} {m : Mem V}

end Writer

end SIS
