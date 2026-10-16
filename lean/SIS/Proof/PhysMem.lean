/-
Proofs about the physical layer, part 1: the memory's operations, one at a
time (bergdb item 001, WP L3).
-/
import SIS.Phys
import SIS.Proof.Basic

set_option linter.unusedSectionVars false

namespace SIS

variable {V T : Type} [DecidableEq V]

/-! ### Objects by handle -/

theorem lookup_cons_eq {β : Type} (a b : Nat) (x : β) (l : List (Nat × β)) :
    List.lookup b ((a, x) :: l) = if b = a then some x else List.lookup b l := by
  simp only [List.lookup_cons]
  by_cases h : b = a
  · subst h; simp
  · have : (b == a) = false := by simp [h]
    simp only [this, h, ↓reduceIte]

theorem lookup_filter_ne {β : Type} (a b : Nat) (l : List (Nat × β))
    (h : b ≠ a) : List.lookup b (l.filter (fun p => p.1 != a)) = List.lookup b l := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    obtain ⟨c, x⟩ := p
    by_cases hc : c = a
    · subst hc
      rw [List.filter_cons]
      simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
      rw [ih, lookup_cons_eq]
      simp only [h, ↓reduceIte]
    · rw [List.filter_cons]
      have : (c != a) = true := by simp [hc]
      simp only [this, ↓reduceIte]
      rw [lookup_cons_eq, lookup_cons_eq, ih]

theorem Mem.obj?_setObj (m : Mem V) (h h' : Nat) (o : Obj V) :
    (m.setObj h o).obj? h' = if h' = h then some o else m.obj? h' := by
  unfold Mem.setObj Mem.obj?
  simp only
  rw [lookup_cons_eq]
  split
  · rfl
  · rename_i hne
    exact lookup_filter_ne h h' m.objs hne

theorem Mem.obj?_setObj_self (m : Mem V) (h : Nat) (o : Obj V) : (m.setObj h o).obj? h = some o := by
  rw [Mem.obj?_setObj]; simp

theorem Mem.obj?_setObj_ne (m : Mem V) {h h' : Nat} (o : Obj V) (hne : h' ≠ h) :
    (m.setObj h o).obj? h' = m.obj? h' := by
  rw [Mem.obj?_setObj]; simp only [hne, ↓reduceIte]

@[simp] theorem Mem.setObj_table (m : Mem V) (h : Nat) (o : Obj V) : (m.setObj h o).table = m.table := rfl
@[simp] theorem Mem.setObj_s (m : Mem V) (h : Nat) (o : Obj V) : (m.setObj h o).s = m.s := rfl
@[simp] theorem Mem.setObj_root (m : Mem V) (h : Nat) (o : Obj V) : (m.setObj h o).root = m.root := rfl
@[simp] theorem Mem.setObj_next (m : Mem V) (h : Nat) (o : Obj V) : (m.setObj h o).next = m.next := rfl

theorem Mem.tableOf_setObj (m : Mem V) (h : Nat) (o : Obj V) (y : NodeId) :
    (m.setObj h o).tableOf y = m.tableOf y := rfl

theorem Mem.obj?_addObj (m : Mem V) (o : Obj V) (h' : Nat) :
    (m.addObj o).1.obj? h' = if h' = m.next then some o else m.obj? h' := by
  unfold Mem.addObj Mem.obj?
  exact lookup_cons_eq _ _ _ _

@[simp] theorem Mem.addObj_snd (m : Mem V) (o : Obj V) : (m.addObj o).2 = m.next := rfl
@[simp] theorem Mem.addObj_table (m : Mem V) (o : Obj V) : (m.addObj o).1.table = m.table := rfl
@[simp] theorem Mem.addObj_s (m : Mem V) (o : Obj V) : (m.addObj o).1.s = m.s := rfl
@[simp] theorem Mem.addObj_root (m : Mem V) (o : Obj V) : (m.addObj o).1.root = m.root := rfl
@[simp] theorem Mem.addObj_next (m : Mem V) (o : Obj V) : (m.addObj o).1.next = m.next + 1 := rfl

theorem Mem.tableOf_addObj (m : Mem V) (o : Obj V) (y : NodeId) :
    (m.addObj o).1.tableOf y = m.tableOf y := rfl

/-! ### The node table -/

theorem Mem.tableOf_setTable (m : Mem V) (y : NodeId) (h : Nat) (y' : NodeId) :
    (m.setTable y h).tableOf y' = if y' = y then some h else m.tableOf y' := by
  unfold Mem.setTable Mem.tableOf
  simp only
  rw [lookup_cons_eq]
  split
  · rfl
  · rename_i hne
    exact lookup_filter_ne y y' m.table hne

@[simp] theorem Mem.setTable_objs (m : Mem V) (y : NodeId) (h : Nat) : (m.setTable y h).objs = m.objs := rfl
@[simp] theorem Mem.setTable_s (m : Mem V) (y : NodeId) (h : Nat) : (m.setTable y h).s = m.s := rfl
@[simp] theorem Mem.setTable_root (m : Mem V) (y : NodeId) (h : Nat) : (m.setTable y h).root = m.root := rfl
@[simp] theorem Mem.setTable_next (m : Mem V) (y : NodeId) (h : Nat) : (m.setTable y h).next = m.next := rfl

theorem Mem.obj?_setTable (m : Mem V) (y : NodeId) (h h' : Nat) :
    (m.setTable y h).obj? h' = m.obj? h' := rfl

/-! ### Slots -/

theorem lookup_map_set {β : Type} (l : List (Nat × β)) (a b : Nat) (x : β) :
    List.lookup b (l.map (fun p => if p.1 == a then (a, x) else p)) =
      if b = a then (List.lookup a l).map (fun _ => x) else List.lookup b l := by
  induction l with
  | nil => by_cases h : b = a <;> simp [h]
  | cons p l ih =>
    obtain ⟨c, z⟩ := p
    simp only [List.map_cons]
    by_cases hc : c = a
    · subst hc
      simp only [beq_self_eq_true, ↓reduceIte]
      rw [lookup_cons_eq, lookup_cons_eq]
      by_cases hb : b = c
      · subst hb; simp
      · simp only [hb, ↓reduceIte]
        rw [ih, lookup_cons_eq]; simp [hb]
    · have : (c == a) = false := by simp [hc]
      simp only [this, Bool.false_eq_true, ↓reduceIte]
      rw [lookup_cons_eq, ih]
      by_cases hb : b = a
      · subst hb
        rw [lookup_cons_eq]
        have : ¬ b = c := fun h => hc h.symm
        simp [this]
      · simp only [hb, ↓reduceIte]
        rw [lookup_cons_eq]

theorem Obj.slot?_setSlot (o : Obj V) (y : NodeId) (sl : Slot) (y' : NodeId) :
    (o.setSlot y sl).slot? y' = if y' = y then (o.slot? y).map (fun _ => sl) else o.slot? y' := by
  unfold Obj.setSlot Obj.slot?
  exact lookup_map_set o.slots y y' sl

theorem Obj.slot?_putSlot (o : Obj V) (y : NodeId) (sl : Slot) (y' : NodeId) :
    (o.putSlot y sl).slot? y' = if y' = y then some sl else o.slot? y' := by
  unfold Obj.putSlot
  split
  · rename_i hs
    rw [Obj.slot?_setSlot]
    split
    · rename_i hy
      subst hy
      obtain ⟨sl0, h0⟩ := Option.isSome_iff_exists.mp hs
      rw [h0]; rfl
    · rfl
  · rename_i hs
    unfold Obj.slot?
    simp only
    rw [List.lookup_append]
    split
    · rename_i hy
      subst hy
      have : o.slot? y' = none := Option.not_isSome_iff_eq_none.mp hs
      unfold Obj.slot? at this
      rw [this]; simp
    · rename_i hy
      cases h : List.lookup y' o.slots with
      | some z => rfl
      | none =>
        simp only [Option.none_or]
        rw [lookup_cons_eq]
        simp only [hy, ↓reduceIte]
        rfl

@[simp] theorem Obj.setSlot_node (o : Obj V) (y : NodeId) (sl : Slot) : (o.setSlot y sl).node = o.node := rfl
@[simp] theorem Obj.setSlot_level (o : Obj V) (y : NodeId) (sl : Slot) : (o.setSlot y sl).level = o.level := rfl
@[simp] theorem Obj.setSlot_isData (o : Obj V) (y : NodeId) (sl : Slot) : (o.setSlot y sl).isData = o.isData := rfl
@[simp] theorem Obj.setSlot_hist (o : Obj V) (y : NodeId) (sl : Slot) : (o.setSlot y sl).hist = o.hist := rfl
@[simp] theorem Obj.setSlot_canonical (o : Obj V) (y : NodeId) (sl : Slot) :
    (o.setSlot y sl).canonical = o.canonical := rfl
@[simp] theorem Obj.setSlot_pos (o : Obj V) (y : NodeId) (sl : Slot) : (o.setSlot y sl).pos = o.pos := rfl

theorem Obj.putSlot_fields (o : Obj V) (y : NodeId) (sl : Slot) :
    (o.putSlot y sl).node = o.node ∧ (o.putSlot y sl).level = o.level ∧
    (o.putSlot y sl).isData = o.isData ∧ (o.putSlot y sl).hist = o.hist ∧
    (o.putSlot y sl).canonical = o.canonical ∧ (o.putSlot y sl).pos = o.pos := by
  unfold Obj.putSlot
  split <;> simp

/-! ### Canonical objects -/

theorem Mem.canonicalOf_eq_some (m : Mem V) (y : NodeId) (h : Nat) :
    m.canonicalOf y = some h ↔ m.tableOf y = some h ∧ ∃ o, m.obj? h = some o ∧ o.canonical = true := by
  unfold Mem.canonicalOf
  constructor
  · intro hc
    split at hc
    · rename_i h0 ht
      split at hc
      · rename_i o ho
        split at hc
        · rename_i hcan
          cases hc
          exact ⟨ht, o, ho, hcan⟩
        · simp at hc
      · simp at hc
    · simp at hc
  · rintro ⟨ht, o, ho, hcan⟩
    rw [ht]
    simp only [ho, hcan, ite_true]

theorem Mem.canonicalOf_eq_none (m : Mem V) (y : NodeId) :
    m.canonicalOf y = none ↔ ∀ h o, m.tableOf y = some h → m.obj? h = some o → o.canonical = false := by
  constructor
  · intro hc h o ht ho
    cases hcan : o.canonical
    · rfl
    · have := (m.canonicalOf_eq_some y h).mpr ⟨ht, o, ho, hcan⟩
      rw [hc] at this; cases this
  · intro hall
    cases hc : m.canonicalOf y with
    | none => rfl
    | some h =>
      obtain ⟨ht, o, ho, hcan⟩ := (m.canonicalOf_eq_some y h).mp hc
      rw [hall h o ht ho] at hcan; cases hcan

end SIS
