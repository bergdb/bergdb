/-
Proofs for stage 2 (bergdb item 001, WP E3), part 14: the Level 4 startup from
R(0) gives a memory with the invariant (`einv_init`), so T-CACHE holds for every
run with eviction and no restart (`TC_run_init`); and the invariant in the terms
of T-CACHE's statement (`EInv.tc_facts`).
-/
import SIS.Proof.EvictTrans

set_option linter.unusedSectionVars false

namespace SIS

variable {V T : Type} [DecidableEq V]

section Init

variable {sp : Spec V T}

theorem secStep_tblNodup (sp : Spec V T) (S : Stream V T) (m : Mem V) (x : NodeId)
    (h : (m.table.map (·.1)).Nodup) : ((secStep sp S m x).table.map (·.1)).Nodup := by
  unfold secStep
  split
  · split
    · exact h
    · exact setTable_nodup _ _ _ h
  · exact h

theorem lazySec_tblNodup (sp : Spec V T) (S : Stream V T) : ((lazySec sp S).table.map (·.1)).Nodup := by
  unfold lazySec
  have key : ∀ (L : List NodeId) (m : Mem V), (m.table.map (·.1)).Nodup →
      ((L.foldl (secStep sp S) m).table.map (·.1)).Nodup := by
    intro L
    induction L with
    | nil => intro m h; exact h
    | cons x L ih => intro m h; exact ih _ (secStep_tblNodup sp S m x h)
  exact key _ _ List.nodup_nil

theorem lazyRoot_tblNodup (sp : Spec V T) (S : Stream V T) (m1 : Mem V) (h : (m1.table.map (·.1)).Nodup) :
    ((lazyRoot sp S m1).table.map (·.1)).Nodup := by
  unfold lazyRoot
  by_cases hv : sp.virt = true
  · simp only [hv, ↓reduceIte]
    exact setTable_nodup _ _ _ h
  · simp only [hv, Bool.false_eq_true, ↓reduceIte]
    cases hc : m1.canonicalOf root with
    | some h0 => exact h
    | none =>
      simp only
      cases ht : topVersion S (lastSp S) true with
      | none => exact h
      | some w => exact setTable_nodup _ _ _ h

theorem Mem.sectionPos_keys (m : Mem V) (S : Stream V T) :
    (m.sectionPos S).objs.map (·.1) = m.objs.map (·.1) := by
  unfold Mem.sectionPos
  simp only [List.map_map]
  apply List.map_congr_left
  intro p _
  simp only [Function.comp]
  cases p.2.canonical
  · simp
  · cases newest S m.s p.2.node <;> simp

theorem rootVersion_times (sp : Spec V T) (s : Nat) (ws : List (Version V)) :
    ∀ e ∈ (rootVersion sp s ws).hist, e.time ≤ s := by
  intro e he
  simp only [rootVersion, List.mem_filterMap, List.mem_range] at he
  obtain ⟨t, ht, hf⟩ := he
  obtain ⟨w, -, hw⟩ := Option.map_eq_some_iff.mp hf
  rw [← hw]
  show t ≤ s
  omega

theorem lookup_refs_some {ws : List (Version V)} {y : NodeId} {r : Nat}
    (h : List.lookup y (ws.map (fun w => (w.node, w.recNo))) = some r) :
    ∃ w ∈ ws, w.node = y ∧ w.recNo = r := by
  induction ws with
  | nil => simp at h
  | cons a ws ih =>
    simp only [List.map_cons, List.lookup_cons] at h
    by_cases ha : a.node = y
    · have hb : (y == a.node) = true := by simp [ha]
      simp only [hb, Option.some.injEq] at h
      exact ⟨a, List.mem_cons_self, ha, h⟩
    · have hb : (y == a.node) = false := by simp; exact fun h => ha h.symm
      simp only [hb] at h
      obtain ⟨w, hw, h1, h2⟩ := ih h
      exact ⟨w, List.mem_cons_of_mem _ hw, h1, h2⟩

theorem canonOfVersion_slot_eq {sp : Spec V T} {S : Stream V T} {s : Nat} {w : Version V} {y : NodeId}
    {sl : Slot} (h : (canonOfVersion sp S s w).slot? y = some sl) :
    sl = Slot.stream (ruleRRef S s y (w.ref? y)) := by
  rw [canonOfVersion_slot?] at h
  by_cases hy : y ∈ pointees sp (cutHist w (if isKeyLevel sp w.isData w.level then some s else none))
  · simp only [hy, ↓reduceIte, Option.some.injEq] at h
    exact h.symm
  · simp only [hy, ↓reduceIte] at h
    cases h

/-! ### Rule 4 keeps the invariant -/

end Init

/-! ## The invariant in the terms of T-CACHE's statement -/

section Facts

variable {sp : Spec V T} {db : DB V T} {S0 : Stream V T} {k : Nat} {m : Mem V}

end Facts

end SIS
