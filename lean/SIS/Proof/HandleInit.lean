/-
Proofs about the physical layer with handles (bergdb item 009, step 2d), part
12: the memory with handles of the startup, before the startup's invariant
(SIS/Proof/HandleStart.lean): the memory with handles that holds the objects of
stage 1's memory (`Mem.toH`), by lookup, and rule 4 with handles
(`HMem.linkD`), by object and pointer.
-/
import SIS.Proof.HandleTrans

set_option linter.unusedSectionVars false

namespace SIS

variable {V T : Type} [DecidableEq V]

/-! ## Lookups -/

theorem lookup_map_het {β γ : Type} (f : Nat × β → Nat × γ) (hf : ∀ q, (f q).1 = q.1) (y : Nat) :
    ∀ (l : List (Nat × β)), List.lookup y (l.map f) = (List.lookup y l).map (fun b => (f (y, b)).2) := by
  intro l
  induction l with
  | nil => rfl
  | cons q l ih =>
    obtain ⟨a, b⟩ := q
    have hfa : f (a, b) = (a, (f (a, b)).2) := by
      have h1 := hf (a, b)
      cases hq : f (a, b) with
      | mk a' c => rw [hq] at h1; simp only at h1; rw [h1]
    rw [List.map_cons, hfa, lookup_cons_eq, lookup_cons_eq]
    by_cases hya : y = a
    · subst hya
      simp only [↓reduceIte, Option.map_some]
    · simp only [hya, ↓reduceIte, ih]

theorem lookup_filter_map {β γ : Type} (P : Nat → Bool) (f : β → γ) (a : Nat) :
    ∀ (l : List (Nat × β)), List.lookup a ((l.filter (fun p => P p.1)).map (fun p => (p.1, f p.2))) =
      if P a then (List.lookup a l).map f else none := by
  intro l
  induction l with
  | nil => simp
  | cons q l ih =>
    obtain ⟨b, x⟩ := q
    by_cases hb : P b = true
    · rw [List.filter_cons_of_pos (by simpa using hb), List.map_cons, lookup_cons_eq, lookup_cons_eq, ih]
      by_cases hab : a = b
      · subst hab; simp [hb]
      · simp [hab]
    · rw [List.filter_cons_of_neg (by simpa using hb), ih, lookup_cons_eq]
      by_cases hab : a = b
      · subst hab; simp [hb]
      · simp [hab]

theorem lookup_map_snd {β : Type} (g : NodeId × Nat → β) (n : Nat) :
    ∀ (l : List (NodeId × Nat)), List.lookup n (l.map (fun e => (e.2, g e))) =
      (l.find? (fun e => e.2 == n)).map g := by
  intro l
  induction l with
  | nil => rfl
  | cons e l ih =>
    obtain ⟨y, b⟩ := e
    rw [List.map_cons, lookup_cons_eq, List.find?_cons, ih]
    by_cases hb : n = b
    · subst hb; simp
    · have : (b == n) = false := by simp [Ne.symm hb]
      simp [hb, this]

theorem nodup_map_of_inj {α β : Type} (f : α → β) : ∀ (l : List α), l.Nodup →
    (∀ x ∈ l, ∀ y ∈ l, f x = f y → x = y) → (l.map f).Nodup
  | [], _, _ => List.nodup_nil
  | a :: l, hnd, hinj => by
    simp only [List.nodup_cons] at hnd
    simp only [List.map_cons, List.nodup_cons]
    refine ⟨fun hmem => ?_, nodup_map_of_inj f l hnd.2 (fun x hx y hy h =>
      hinj x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy) h)⟩
    obtain ⟨b, hb, hfb⟩ := List.mem_map.mp hmem
    have := hinj b (List.mem_cons_of_mem _ hb) a List.mem_cons_self hfb
    subst this
    exact hnd.1 hb

theorem nodup_of_map {α β : Type} (f : α → β) : ∀ {l : List α}, (l.map f).Nodup → l.Nodup
  | [], _ => List.nodup_nil
  | a :: l, h => by
    simp only [List.map_cons, List.nodup_cons] at h
    exact List.nodup_cons.mpr ⟨fun ha => h.1 (List.mem_map.mpr ⟨a, ha, rfl⟩), nodup_of_map f h.2⟩

/-! ## Stage 1's memory with handles -/

/-- Whether the node table names object a. -/
def Mem.heldA (m : Mem V) (a : Nat) : Bool := m.table.any (fun e => e.2 == a)

/-- A slot of an object of m, as a pointer of `Mem.toH`. -/
def Mem.ptrOfH (m : Mem V) (q : NodeId × Slot) : NodeId × HPtr :=
  match q.2 with
  | Slot.mem a =>
    (q.1, ({ ref := (m.obj? a).bind (·.pos), handle := if m.table.any (fun e => e.2 == a) then some a else none } :
      HPtr))
  | Slot.stream r => (q.1, ({ ref := r, handle := none } : HPtr))

/-- An object of m, as an object of `Mem.toH`. -/
def Mem.objH (m : Mem V) (o : Obj V) : HObj V :=
  { node := o.node, level := o.level, isData := o.isData, hist := o.hist, canonical := o.canonical,
    pos := o.pos, ptrs := o.slots.map m.ptrOfH }

/-- The live handle of `Mem.toH` for a table entry. -/
def handleOfEntry (e : NodeId × Nat) : Handle := { node := e.1, obj := some e.2, written := none, dead := false }

theorem Mem.toH_objs (m : Mem V) :
    m.toH.objs = (m.objs.filter (fun p => m.heldA p.1)).map (fun p => (p.1, m.objH p.2)) := rfl
theorem Mem.toH_handles (m : Mem V) : m.toH.handles = m.table.map (fun e => (e.2, handleOfEntry e)) := rfl
theorem Mem.toH_tableOf (m : Mem V) (y : NodeId) : m.toH.tableOf y = m.tableOf y := rfl

theorem Mem.toH_obj? (m : Mem V) (a : Nat) :
    m.toH.obj? a = if m.heldA a then (m.obj? a).map m.objH else none := by
  unfold HMem.obj?
  rw [Mem.toH_objs]
  exact lookup_filter_map m.heldA m.objH a m.objs

theorem Mem.toH_handle? (m : Mem V) (n : Nat) :
    m.toH.handle? n = (m.table.find? (fun e => e.2 == n)).map handleOfEntry := by
  unfold HMem.handle?
  rw [Mem.toH_handles]
  exact lookup_map_snd handleOfEntry n m.table

theorem Mem.ptrOfH_fst (m : Mem V) (q : NodeId × Slot) : (m.ptrOfH q).1 = q.1 := by
  unfold Mem.ptrOfH; split <;> rfl

theorem Mem.objH_ptr? (m : Mem V) (o : Obj V) (y : NodeId) :
    (m.objH o).ptr? y = (o.slot? y).map (fun sl => (m.ptrOfH (y, sl)).2) := by
  unfold Mem.objH HObj.ptr? Obj.slot?
  exact lookup_map_het m.ptrOfH (Mem.ptrOfH_fst m) y o.slots

/-- The table's entry with address a, when the table names objects of their
nodes. -/
theorem Mem.table_find {m : Mem V} (hnd : (m.table.map (·.1)).Nodup)
    (hv : ∀ y a, m.tableOf y = some a → ∃ o, m.obj? a = some o ∧ o.node = y) {y : NodeId} {a : Nat}
    (h : m.tableOf y = some a) : m.table.find? (fun e => e.2 == a) = some (y, a) := by
  have hmem : (y, a) ∈ m.table := mem_of_lookup m.table y a h
  have hsome : (m.table.find? (fun e => e.2 == a)).isSome :=
    List.find?_isSome.mpr ⟨(y, a), hmem, by simp⟩
  obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp hsome
  have he1 := List.find?_some he
  have he2 := List.mem_of_find?_eq_some he
  obtain ⟨y', a'⟩ := e
  simp only [beq_iff_eq] at he1
  subst he1
  have hl : m.table.lookup y' = some a' := lookup_of_mem m.table hnd (y', a') he2
  obtain ⟨o, ho, hon⟩ := hv y' a' hl
  obtain ⟨o', ho', hon'⟩ := hv y a' h
  rw [ho, Option.some.injEq] at ho'
  subst ho'
  have hyy : y' = y := hon.symm.trans hon'
  rw [he, hyy]

theorem Mem.toH_handle?_some {m : Mem V} (hnd : (m.table.map (·.1)).Nodup) {n : Nat} {hd : Handle}
    (h : m.toH.handle? n = some hd) : ∃ y, m.tableOf y = some n ∧ hd = handleOfEntry (y, n) := by
  rw [Mem.toH_handle?] at h
  cases hf : m.table.find? (fun e => e.2 == n) with
  | none => rw [hf] at h; cases h
  | some e =>
    rw [hf] at h
    simp only [Option.map_some, Option.some.injEq] at h
    have he1 := List.find?_some hf
    have he2 := List.mem_of_find?_eq_some hf
    obtain ⟨y, b⟩ := e
    simp only [beq_iff_eq] at he1
    subst he1
    exact ⟨y, lookup_of_mem m.table hnd (y, b) he2, h.symm⟩

/-! ## Rule 4 with handles -/

/-- A pointer as rule 4 with handles leaves it. -/
def HMem.linkPtr (m : HMem V) (q : NodeId × HPtr) : NodeId × HPtr :=
  match q.2.handle with
  | none => match m.canonicalOf q.1 with
    | some _ => (q.1, { q.2 with handle := m.tableOf q.1 })
    | none => q
  | some _ => q

/-- Object o at address a as rule 4 with handles leaves it. -/
def HMem.linkObj (m : HMem V) (D : Dirty) (a : Nat) (o : HObj V) : HObj V :=
  if !(o.canonical && (inD D o.node || a == m.root)) then o else { o with ptrs := o.ptrs.map m.linkPtr }

theorem HMem.linkD_objs (m : HMem V) (D : Dirty) :
    (m.linkD D).objs = m.objs.map (fun p => (p.1, m.linkObj D p.1 p.2)) := by
  unfold HMem.linkD HMem.linkObj HMem.linkPtr
  simp only
  apply List.map_congr_left
  intro p _
  cases (!(p.2.canonical && (inD D p.2.node || p.1 == m.root)))
  · simp only [Bool.false_eq_true, ↓reduceIte]; rfl
  · simp only [↓reduceIte]

theorem HMem.linkD_obj? (m : HMem V) (D : Dirty) (a : Nat) :
    (m.linkD D).obj? a = (m.obj? a).map (m.linkObj D a) := by
  unfold HMem.obj?
  rw [HMem.linkD_objs]
  exact lookup_map_key (fun p => (p.1, m.linkObj D p.1 p.2)) (fun _ => rfl) a m.objs

theorem HMem.linkD_keys (m : HMem V) (D : Dirty) : (m.linkD D).objs.map (·.1) = m.objs.map (·.1) := by
  rw [HMem.linkD_objs, List.map_map]
  rfl

theorem HMem.linkPtr_fst (m : HMem V) (q : NodeId × HPtr) : (m.linkPtr q).1 = q.1 := by
  unfold HMem.linkPtr
  split
  · split <;> rfl
  · rfl

theorem HMem.linkObj_core (m : HMem V) (D : Dirty) (a : Nat) (o : HObj V) :
    (m.linkObj D a o).core = o.core := by
  unfold HMem.linkObj
  split <;> rfl

end SIS
