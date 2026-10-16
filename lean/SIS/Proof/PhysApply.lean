/-
Proofs about the physical layer, part 11: a transaction's change applied to
the canonical objects in the rerun (bergdb item 001, WP L3).
-/
import SIS.Proof.PhysRerun

set_option linter.unusedSectionVars false

namespace SIS

variable {V T : Type} [DecidableEq V]

/-! ### The objects of new nodes -/

/-- The canonical object of a new node. -/
def newObj (nn : NewNode) : Obj V :=
  { node := nn.id, level := nn.level, isData := nn.isData, hist := [], canonical := true,
    pos := none, slots := [] }

/-- Add the canonical object of a new node. -/
def addNew (m : Mem V) (nn : NewNode) : Mem V :=
  ((m.addObj (newObj nn)).1).setTable nn.id m.next

theorem addNew_next (m : Mem V) (nn : NewNode) : (addNew m nn).next = m.next + 1 := rfl

theorem addNew_obj (m : Mem V) (nn : NewNode) (h : Nat) :
    (addNew m nn).obj? h = if h = m.next then some (newObj nn) else m.obj? h := by
  unfold addNew; rw [Mem.obj?_setTable, Mem.obj?_addObj]

theorem addNew_table (m : Mem V) (nn : NewNode) (y : NodeId) :
    (addNew m nn).tableOf y = if y = nn.id then some m.next else m.tableOf y := by
  unfold addNew; rw [Mem.tableOf_setTable, Mem.tableOf_addObj]

theorem foldl_addNew_next (N : List NewNode) : ∀ (m : Mem V),
    (N.foldl addNew m).next = m.next + N.length := by
  induction N with
  | nil => intro m; rfl
  | cons nn N ih => intro m; simp only [List.foldl_cons, ih, addNew_next, List.length_cons]; omega

theorem foldl_addNew_old (N : List NewNode) : ∀ (m : Mem V) (h : Nat), h < m.next →
    (N.foldl addNew m).obj? h = m.obj? h := by
  induction N with
  | nil => intro m h _; rfl
  | cons nn N ih =>
    intro m h hh
    simp only [List.foldl_cons]
    rw [ih _ h (by rw [addNew_next]; omega), addNew_obj]
    simp only [show h ≠ m.next by omega, ↓reduceIte]

theorem foldl_addNew_table_old (N : List NewNode) : ∀ (m : Mem V) (y : NodeId),
    y ∉ N.map (·.id) → (N.foldl addNew m).tableOf y = m.tableOf y := by
  induction N with
  | nil => intro m y _; rfl
  | cons nn N ih =>
    intro m y hy
    simp only [List.map_cons, List.mem_cons, not_or] at hy
    simp only [List.foldl_cons]
    rw [ih _ y hy.2, addNew_table]
    simp only [hy.1, ↓reduceIte]

/-- After the new nodes: each has its canonical object, at a new handle. -/
theorem foldl_addNew_new (N : List NewNode) (hnd : (N.map (·.id)).Nodup) : ∀ (m : Mem V),
    ∀ nn ∈ N, ∃ h, m.next ≤ h ∧ (N.foldl addNew m).tableOf nn.id = some h ∧
      (N.foldl addNew m).obj? h = some (newObj nn) := by
  induction N with
  | nil => intro m nn h; cases h
  | cons nn0 N ih =>
    intro m nn hnn
    simp only [List.map_cons, List.nodup_cons] at hnd
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hnn with h | h
    · subst h
      refine ⟨m.next, Nat.le_refl _, ?_, ?_⟩
      · rw [foldl_addNew_table_old N _ _ hnd.1, addNew_table]; simp
      · rw [foldl_addNew_old N _ _ (by rw [addNew_next]; omega), addNew_obj]; simp
    · obtain ⟨h1, hle, ht, ho⟩ := ih hnd.2 (addNew m nn0) nn h
      rw [addNew_next] at hle
      exact ⟨h1, by omega, ht, ho⟩

/-- The handles after the new nodes: the old ones, and new nodes' objects. -/
theorem foldl_addNew_obj (N : List NewNode) (hnd : (N.map (·.id)).Nodup) :
    ∀ (m : Mem V), (∀ h, m.next ≤ h → m.obj? h = none) → ∀ (h : Nat) (o : Obj V),
    (N.foldl addNew m).obj? h = some o → (h < m.next ∧ m.obj? h = some o) ∨
      (m.next ≤ h ∧ ∃ nn ∈ N, o = newObj nn ∧ (N.foldl addNew m).tableOf nn.id = some h) := by
  induction N with
  | nil =>
    intro m hfr h o ho
    simp only [List.foldl_nil] at ho
    left
    refine ⟨Nat.lt_of_not_le (fun hle => by rw [hfr h hle] at ho; cases ho), ho⟩
  | cons nn0 N ih =>
    intro m hfr h o ho
    simp only [List.map_cons, List.nodup_cons] at hnd
    simp only [List.foldl_cons] at ho ⊢
    have hfr' : ∀ h, (addNew m nn0).next ≤ h → (addNew m nn0).obj? h = none := by
      intro h' hh'
      rw [addNew_next] at hh'
      rw [addNew_obj]
      simp only [show h' ≠ m.next by omega, ↓reduceIte]
      exact hfr h' (by omega)
    rcases ih hnd.2 (addNew m nn0) hfr' h o ho with ⟨hlt, ho'⟩ | ⟨hle, nn, hnn, hon, ht⟩
    · rw [addNew_obj] at ho'
      rw [addNew_next] at hlt
      split at ho'
      · rename_i hh
        cases ho'
        right
        refine ⟨by omega, nn0, List.mem_cons_self, rfl, ?_⟩
        rw [foldl_addNew_table_old N _ _ hnd.1, addNew_table]
        simp [hh]
      · left; exact ⟨by omega, ho'⟩
    · right
      rw [addNew_next] at hle
      exact ⟨by omega, nn, List.mem_cons_of_mem _ hnn, hon, ht⟩

/-! ### The slots of new pointers -/

section Slots

variable (sp : Spec V T) (P : Struct V) (j : Time)

/-- The copied slot, if there is a source. -/
def srcSlot (m : Mem V) (y : NodeId) : Option Slot :=
  (m.objs.find? (srcOK sp P j y)).bind (fun p => p.2.slot? y)

/-- Any canonical object's slot for y. -/
def anySlot (m : Mem V) (y : NodeId) : Option Slot :=
  (m.objs.find? (fun p => p.2.canonical && (p.2.slot? y).isSome)).bind (fun p => p.2.slot? y)

/-- The new slot that does not depend on the object: to y's canonical object, or
copied from a source. -/
def NS1 (m : Mem V) (y : NodeId) : Option Slot :=
  ((m.canonicalOf y).map Slot.mem).or (srcSlot sp P j m y)

theorem newSlot_eq (m : Mem V) (o : Obj V) (y : NodeId) :
    m.newSlot sp P j o y = (NS1 sp P j m y).or ((o.slot? y).or (anySlot m y)) := by
  unfold Mem.newSlot NS1 srcSlot anySlot
  cases hc : m.canonicalOf y with
  | some h => rfl
  | none =>
    simp only [Option.map_none, Option.none_or]
    cases hf : m.objs.find? (srcOK sp P j y) with
    | some p =>
      simp only [Option.bind_some]
      have hp := List.find?_some hf
      unfold srcOK at hp
      simp only [Bool.and_eq_true] at hp
      obtain ⟨sl, hsl⟩ := Option.isSome_iff_exists.mp hp.1.1.2
      rw [hsl]; rfl
    | none =>
      simp only [Option.bind_none, Option.none_or]
      cases o.slot? y <;> rfl

/-- One pointer of a new entry: its slot. -/
def upd1 (m1 : Mem V) (o' : Obj V) (y : NodeId) : Obj V :=
  match m1.newSlot sp P j o' y with
  | some sl => o'.putSlot y sl
  | none => o'

theorem upd1_core (m1 : Mem V) (o' : Obj V) (y : NodeId) : (upd1 sp P j m1 o' y).core = o'.core := by
  unfold upd1
  split
  · obtain ⟨a, b, c, d, e, f⟩ := Obj.putSlot_fields o' y ‹_›
    unfold Obj.core; rw [a, b, c, d, e, f]
  · rfl

/-- The slot that a pointer gets: NS1, or the object's own slot, or any
canonical object's. -/
def combo (m1 : Mem V) (o : Obj V) (y : NodeId) : Option Slot :=
  (NS1 sp P j m1 y).or ((o.slot? y).or (anySlot m1 y))

theorem upd1_slot (m1 : Mem V) (o' : Obj V) (y y' : NodeId) :
    (upd1 sp P j m1 o' y).slot? y' = if y' = y then combo sp P j m1 o' y else o'.slot? y' := by
  unfold upd1 combo
  rw [newSlot_eq]
  cases hc : (NS1 sp P j m1 y).or ((o'.slot? y).or (anySlot m1 y)) with
  | none =>
    simp only
    split
    · rename_i hy; subst hy
      simp only [Option.or_eq_none_iff] at hc
      exact hc.2.1
    · rfl
  | some sl =>
    simp only
    rw [Obj.slot?_putSlot]

theorem combo_idem (m1 : Mem V) (o : Obj V) (y : NodeId) (o' : Obj V)
    (h : o'.slot? y = combo sp P j m1 o y) : combo sp P j m1 o' y = combo sp P j m1 o y := by
  unfold combo at h ⊢
  rw [h]
  cases NS1 sp P j m1 y with
  | some _ => rfl
  | none =>
    simp only [Option.none_or]
    rw [Option.or_assoc, Option.or_self]

/-- The pointers of one entry, in turn. -/
theorem foldl_upd1_slot (m1 : Mem V) (ys : List NodeId) : ∀ (o : Obj V) (y' : NodeId),
    (ys.foldl (upd1 sp P j m1) o).slot? y' = if y' ∈ ys then combo sp P j m1 o y' else o.slot? y' := by
  induction ys with
  | nil => intro o y'; simp
  | cons y ys ih =>
    intro o y'
    simp only [List.foldl_cons]
    rw [ih]
    by_cases hy : y' ∈ ys
    · simp only [hy, ↓reduceIte, List.mem_cons, or_true]
      by_cases hyy : y' = y
      · subst hyy
        apply combo_idem
        rw [upd1_slot]; simp
      · unfold combo
        rw [upd1_slot]
        simp only [hyy, ↓reduceIte]
    · simp only [hy, ↓reduceIte, List.mem_cons, or_false]
      rw [upd1_slot]
      by_cases hyy : y' = y
      · subst hyy; simp
      · simp [hyy]

theorem foldl_upd1_core (m1 : Mem V) (ys : List NodeId) : ∀ (o : Obj V),
    (ys.foldl (upd1 sp P j m1) o).core = o.core := by
  induction ys with
  | nil => intro o; rfl
  | cons y ys ih => intro o; simp only [List.foldl_cons]; rw [ih, upd1_core]

theorem combo_congr (m1 : Mem V) {o o' : Obj V} {y : NodeId} (h : o'.slot? y = o.slot? y) :
    combo sp P j m1 o' y = combo sp P j m1 o y := by
  unfold combo; rw [h]

/-- One entry v of the transaction applied to the canonical object o. -/
def updObj (m1 : Mem V) (o : Obj V) (v : V) : Obj V :=
  (sp.ptrs v).foldl (upd1 sp P j m1) { o with hist := o.hist ++ [⟨j, v⟩] }

theorem updObj_core (m1 : Mem V) (o : Obj V) (v : V) :
    (updObj sp P j m1 o v).node = o.node ∧ (updObj sp P j m1 o v).level = o.level ∧
    (updObj sp P j m1 o v).isData = o.isData ∧ (updObj sp P j m1 o v).hist = o.hist ++ [⟨j, v⟩] ∧
    (updObj sp P j m1 o v).canonical = o.canonical ∧ (updObj sp P j m1 o v).pos = o.pos := by
  have := foldl_upd1_core sp P j m1 (sp.ptrs v) { o with hist := o.hist ++ [⟨j, v⟩] }
  unfold updObj
  simp only [Obj.core, Prod.mk.injEq] at this
  exact ⟨this.1, this.2.1, this.2.2.1, this.2.2.2.1, this.2.2.2.2.1, this.2.2.2.2.2⟩

theorem updObj_slot (m1 : Mem V) (o : Obj V) (v : V) (y : NodeId) :
    (updObj sp P j m1 o v).slot? y = if y ∈ sp.ptrs v then combo sp P j m1 o y else o.slot? y := by
  unfold updObj
  rw [foldl_upd1_slot]
  split
  · exact combo_congr sp P j m1 rfl
  · rfl

/-- The entries of a list of adds, in turn. -/
def updAll (m1 : Mem V) (L : List (NodeId × V)) (o : Obj V) : Obj V :=
  L.foldl (fun o a => updObj sp P j m1 o a.2) o

theorem updAll_core (m1 : Mem V) (L : List (NodeId × V)) : ∀ (o : Obj V),
    (updAll sp P j m1 L o).node = o.node ∧ (updAll sp P j m1 L o).level = o.level ∧
    (updAll sp P j m1 L o).isData = o.isData ∧
    (updAll sp P j m1 L o).hist = o.hist ++ L.map (fun a => (⟨j, a.2⟩ : Entry V)) ∧
    (updAll sp P j m1 L o).canonical = o.canonical ∧ (updAll sp P j m1 L o).pos = o.pos := by
  induction L with
  | nil => intro o; simp [updAll]
  | cons a L ih =>
    intro o
    unfold updAll at ih ⊢
    simp only [List.foldl_cons]
    obtain ⟨a1, a2, a3, a4, a5, a6⟩ := ih (updObj sp P j m1 o a.2)
    obtain ⟨b1, b2, b3, b4, b5, b6⟩ := updObj_core sp P j m1 o a.2
    refine ⟨by rw [a1, b1], by rw [a2, b2], by rw [a3, b3], by rw [a4, b4]; simp, by rw [a5, b5],
      by rw [a6, b6]⟩

theorem updAll_slot (m1 : Mem V) (L : List (NodeId × V)) : ∀ (o : Obj V) (y : NodeId),
    (updAll sp P j m1 L o).slot? y =
      if y ∈ L.flatMap (fun a => sp.ptrs a.2) then combo sp P j m1 o y else o.slot? y := by
  induction L with
  | nil => intro o y; simp [updAll]
  | cons a L ih =>
    intro o y
    unfold updAll at ih ⊢
    simp only [List.foldl_cons]
    rw [ih, List.flatMap_cons]
    by_cases h1 : y ∈ L.flatMap (fun a => sp.ptrs a.2)
    · simp only [h1, ↓reduceIte, List.mem_append, or_true]
      by_cases h2 : y ∈ sp.ptrs a.2
      · apply combo_idem
        rw [updObj_slot]; simp [h2]
      · apply combo_congr
        rw [updObj_slot]; simp [h2]
    · simp only [h1, ↓reduceIte, List.mem_append, or_false]
      rw [updObj_slot]

/-! ### The adds of the transaction, in turn -/

/-- One add: the entry appended to its node's canonical object. -/
def addsStep (m1 : Mem V) (m : Mem V) (a : NodeId × V) : Mem V :=
  match m.canonicalOf a.1 with
  | none => m
  | some h =>
    match m.obj? h with
    | none => m
    | some o => m.setObj h (updObj sp P j m1 o a.2)

theorem applyChange_eq (m : Mem V) (c : Changes V) :
    m.applyChange sp P j c =
      c.adds.foldl (addsStep sp P j (c.new.foldl addNew m)) (c.new.foldl addNew m) := rfl

end Slots

/-- The objects after the adds: each canonical object of a changed node has its
node's adds, the others are as before. -/
theorem adds_fold (m1 : Mem V) (L : List (NodeId × V)) : ∀ (L0 : List (NodeId × V)) (m : Mem V),
    m.table = m1.table → m.next = m1.next → m.s = m1.s → m.root = m1.root →
    (∀ h, m.obj? h = (m1.obj? h).map
      (updAll sp P j m1 (L0.filter (fun a => m1.canonicalOf a.1 == some h)))) →
    (L.foldl (addsStep sp P j m1) m).table = m1.table ∧
    (L.foldl (addsStep sp P j m1) m).next = m1.next ∧
    (L.foldl (addsStep sp P j m1) m).s = m1.s ∧
    (L.foldl (addsStep sp P j m1) m).root = m1.root ∧
    (∀ h, (L.foldl (addsStep sp P j m1) m).obj? h = (m1.obj? h).map
      (updAll sp P j m1 ((L0 ++ L).filter (fun a => m1.canonicalOf a.1 == some h)))) ∧
    (((m.objs.map (·.1)).Nodup) → ((L.foldl (addsStep sp P j m1) m).objs.map (·.1)).Nodup) := by
  induction L with
  | nil => intro L0 m ht hn hs hr ho; simp only [List.foldl_nil, List.append_nil]; exact ⟨ht, hn, hs, hr, ho, id⟩
  | cons a L ih =>
    intro L0 m ht hn hs hr ho
    simp only [List.foldl_cons]
    -- canonicalOf is the same in m as in m1
    have hcan : ∀ y, m.canonicalOf y = m1.canonicalOf y := by
      intro y
      unfold Mem.canonicalOf Mem.tableOf
      rw [ht]
      cases hty : List.lookup y m1.table with
      | none => rfl
      | some h =>
        simp only
        rw [ho h]
        cases ho1 : m1.obj? h with
        | none => rfl
        | some o1 =>
          simp only [Option.map_some]
          rw [(updAll_core sp P j m1 _ o1).2.2.2.2.1]
    have hstep : ∀ h, (addsStep sp P j m1 m a).obj? h = (m1.obj? h).map
        (updAll sp P j m1 ((L0 ++ [a]).filter (fun a => m1.canonicalOf a.1 == some h))) := by
      intro h
      unfold addsStep
      rw [hcan]
      cases hc : m1.canonicalOf a.1 with
      | none =>
        simp only
        rw [ho h, List.filter_append]
        simp [hc]
      | some h1 =>
        simp only
        rw [ho h1]
        cases ho1 : m1.obj? h1 with
        | none =>
          simp only [Option.map_none]
          rw [ho h, List.filter_append]
          by_cases hh : h = h1
          · subst hh; rw [ho1]; rfl
          · have : (some h1 == some h) = false := by simp [Ne.symm hh]
            simp [hc, this]
        | some o1 =>
          simp only [Option.map_some]
          rw [Mem.obj?_setObj]
          split
          · rename_i hh
            subst hh
            rw [ho1, List.filter_append]
            simp only [Option.map_some, Option.some.injEq]
            unfold updAll
            simp [hc, List.foldl_append]
          · rename_i hh
            rw [ho h, List.filter_append]
            have : (some h1 == some h) = false := by simp [Ne.symm hh]
            simp [hc, this]
    have hm' : (addsStep sp P j m1 m a).table = m1.table ∧ (addsStep sp P j m1 m a).next = m1.next ∧
        (addsStep sp P j m1 m a).s = m1.s ∧ (addsStep sp P j m1 m a).root = m1.root ∧
        (((m.objs.map (·.1)).Nodup) → ((addsStep sp P j m1 m a).objs.map (·.1)).Nodup) := by
      unfold addsStep
      split
      · exact ⟨ht, hn, hs, hr, id⟩
      · split
        · exact ⟨ht, hn, hs, hr, id⟩
        · exact ⟨ht, hn, hs, hr, fun h => nodup_setObj_keys m _ _ h⟩
    obtain ⟨h1, h2, h3, h4, h5⟩ := hm'
    obtain ⟨g1, g2, g3, g4, g5, g6⟩ := ih (L0 ++ [a]) _ h1 h2 h3 h4 hstep
    refine ⟨g1, g2, g3, g4, ?_, fun hnd => g6 (h5 hnd)⟩
    intro h
    rw [g5 h, List.append_assoc]
    rfl

end SIS
