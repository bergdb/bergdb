/-
Proofs for stage 2 (bergdb item 001, WP E3), part 8: the change applied to the
canonical objects (`Mem.applyChange4`), the shapes of the objects after it (as
PhysApply.lean for stage 1, with `Mem.newSlot4`).
-/
import SIS.Proof.EvictPromote

set_option linter.unusedSectionVars false

namespace SIS

variable {V T : Type} [DecidableEq V]

section Slots4

variable (sp : Spec V T) (P : Struct V) (j : Time)

end Slots4

/-! ## The memory after the change -/

/-- A nodup list with two different members has two elements at least. -/
theorem two_le_length {α : Type} [DecidableEq α] : ∀ {l : List α}, l.Nodup → ∀ {a b : α}, a ∈ l → b ∈ l →
    a ≠ b → 2 ≤ l.length
  | [], _, _, _, ha, _, _ => by cases ha
  | x :: l, hnd, a, b, ha, hb, hab => by
    simp only [List.nodup_cons] at hnd
    simp only [List.length_cons]
    rcases List.mem_cons.mp ha with rfl | ha
    · rcases List.mem_cons.mp hb with rfl | hb
      · exact absurd rfl hab
      · have : 0 < l.length := List.length_pos_of_mem hb
        omega
    · have : 0 < l.length := List.length_pos_of_mem ha
      omega

/-- Node x has z as a live child at t. -/
def liveParentB (sp : Spec V T) (P : Struct V) (t : Time) (z x : NodeId) : Bool :=
  match P.get? x with
  | some n => (sp.live (n.hist.upTo t)).contains z
  | none => false

/-- TREE: a reachable node other than the root is the live child of one reachable
node only. -/
theorem treeAt_unique {sp : Spec V T} {P : Struct V} {t : Time} (htr : treeAt sp P t) {z : NodeId}
    (hz : reachable sp P t z = true) (hzr : z ≠ root) {x1 x2 : NodeId} {n1 n2 : Node V}
    (h1 : reachable sp P t x1 = true) (h2 : reachable sp P t x2 = true) (hn1 : P.get? x1 = some n1)
    (hn2 : P.get? x2 = some n2) (hz1 : z ∈ sp.live (n1.hist.upTo t)) (hz2 : z ∈ sp.live (n2.hist.upTo t)) :
    x1 = x2 := by
  by_cases hne : x1 = x2
  · exact hne
  exfalso
  have hlen : ((reachList sp P t).eraseDups.filter (liveParentB sp P t z)).length = 1 := htr z hz hzr
  have hmem : ∀ x n, reachable sp P t x = true → P.get? x = some n → z ∈ sp.live (n.hist.upTo t) →
      x ∈ (reachList sp P t).eraseDups.filter (liveParentB sp P t z) := by
    intro x n hr hn hzl
    rw [List.mem_filter, List.mem_eraseDups]
    refine ⟨by simpa [reachable] using hr, ?_⟩
    unfold liveParentB
    rw [hn]; exact List.contains_iff_mem.mpr hzl
  have := two_le_length (nodup_filter (nodup_eraseDups _) _) (hmem x1 n1 h1 hn1 hz1)
    (hmem x2 n2 h2 hn2 hz2) hne
  omega

section NewSlots

variable {sp : Spec V T} {db : DB V T} {S0 : Stream V T} {k : Nat} {m : Mem V} {c : Changes V}

/-- A node of the structure is not new. -/
theorem not_new_of_get? (hstep : StepOK sp db.P (k + 1) c) {y : NodeId} {n : Node V}
    (hn : db.P.get? y = some n) : y ∉ c.new.map (·.id) := by
  intro hy
  obtain ⟨nn, hnn, hid⟩ := List.mem_map.mp hy
  have := hstep.fresh nn hnn
  rw [hid, hn] at this; cases this

/-- The new node with a given id. -/
theorem new_unique : ∀ {N : List NewNode}, (N.map (·.id)).Nodup → ∀ {nn nn' : NewNode}, nn ∈ N → nn' ∈ N →
    nn.id = nn'.id → nn = nn'
  | [], _, _, _, h1, _, _ => by cases h1
  | a :: l, hnd, nn, nn', h1, h2, he => by
    simp only [List.map_cons, List.nodup_cons] at hnd
    rcases List.mem_cons.mp h1 with rfl | h1' <;> rcases List.mem_cons.mp h2 with rfl | h2'
    · rfl
    · exfalso; apply hnd.1; rw [he]; exact List.mem_map.mpr ⟨nn', h2', rfl⟩
    · exfalso; apply hnd.1; rw [← he]; exact List.mem_map.mpr ⟨nn, h1', rfl⟩
    · exact new_unique hnd.2 h1' h2' he

end NewSlots

/-! ## The invariant after the change -/

end SIS
