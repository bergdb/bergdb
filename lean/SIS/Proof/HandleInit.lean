/-
Proofs about the physical layer with handles (bergdb item 009, step 2d), part
12: the startup with handles from R(0) (`handleStartup`) gives a memory with the
invariant. From E3's: the memory of Evict.lean's lazy startup from R(0), with
the positions of the section, has `EInv` (SIS/Proof/EvictInit.lean); the memory
with handles that holds its objects (`Mem.toH`) has `HEInv`; and rule 4 with
handles (`HMem.linkD`) keeps it.
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

/-! ## Evict.lean's memory with handles -/

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

/-- The memory with handles that holds the objects of a memory with E3's
invariant, all canonical, whose stream slots name versions, has the invariant
with handles. -/
theorem EInv.toH {sp : Spec V T} {db : DB V T} {S0 : Stream V T} {k : Nat} {M : Mem V}
    (hinv : Inv sp db k) (hm : EInv sp db S0 k M)
    (hall : ∀ h o, M.obj? h = some o → o.canonical = true)
    (hstr : ∀ h o y r, M.obj? h = some o → o.slot? y = some (Slot.stream r) →
      ∀ r', r = some r' → ∃ u, db.S.versionAt r' y = some u) :
    HEInv sp db S0 k M.toH := by
  have hv : ∀ y a, M.tableOf y = some a → ∃ o, M.obj? a = some o ∧ o.node = y := hm.tbl
  have hheld : ∀ a o, M.obj? a = some o → M.heldA a = true := by
    intro a o ho
    have ht := hm.canonTbl a o ho (hall a o ho)
    unfold Mem.heldA
    apply List.any_eq_true.mpr
    exact ⟨(o.node, a), mem_of_lookup M.table o.node a ht, by simp⟩
  have hobjH : ∀ a o, M.obj? a = some o → M.toH.obj? a = some (M.objH o) := by
    intro a o ho
    rw [Mem.toH_obj?, hheld a o ho, ho]; rfl
  have hback : ∀ a o', M.toH.obj? a = some o' → ∃ o, M.obj? a = some o ∧ o' = M.objH o := by
    intro a o' ho'
    rw [Mem.toH_obj?] at ho'
    split at ho'
    · cases ho : M.obj? a with
      | none => rw [ho] at ho'; cases ho'
      | some o =>
        rw [ho] at ho'
        simp only [Option.map_some, Option.some.injEq] at ho'
        exact ⟨o, rfl, ho'.symm⟩
    · cases ho'
  -- One live handle per table entry, holding its object.
  have hhandle : ∀ y a, M.tableOf y = some a → M.toH.handle? a = some (handleOfEntry (y, a)) := by
    intro y a h
    rw [Mem.toH_handle?, Mem.table_find hm.tblNodup hv h]; rfl
  have hobjOf : ∀ y a, M.tableOf y = some a → M.toH.objOf a = some a := by
    intro y a h; unfold HMem.objOf; rw [hhandle y a h]; rfl
  -- The canonical objects are M's.
  have hcan : ∀ y, M.toH.canonicalOf y = M.canonicalOf y := by
    intro y
    unfold HMem.canonicalOf Mem.canonicalOf
    rw [Mem.toH_tableOf]
    cases ht : M.tableOf y with
    | none => rfl
    | some a =>
      simp only [Option.bind_some]
      rw [hobjOf y a ht]
      simp only
      obtain ⟨o, ho, -⟩ := hv y a ht
      rw [hobjH a o ho, ho]
      rfl
  -- The record rule for a converted slot: the slot's serialized reference.
  have hptrRef : ∀ a o y sl, M.obj? a = some o → o.slot? y = some sl →
      M.toH.ptrRef S0 y (M.ptrOfH (y, sl)).2 = slotRefOf S0 M y sl := by
    intro a o y sl ho hsl
    cases sl with
    | mem b =>
      obtain ⟨ob, hob, hnb⟩ := hm.slotsNode a o ho y b hsl
      have hb := hheld b ob hob
      have htb : M.tableOf ob.node = some b := hm.canonTbl b ob hob (hall b ob hob)
      have hp : (M.ptrOfH (y, Slot.mem b)).2 = { ref := (M.obj? b).bind (·.pos), handle := some b } := by
        show ({ ref := (M.obj? b).bind (·.pos), handle := if M.heldA b then some b else none } : HPtr) = _
        simp [hb]
      rw [hp]
      unfold HMem.ptrRef
      simp only [Option.bind_some, hhandle ob.node b htb, handleOfEntry, hobjH b ob hob, Mem.objH,
        hall b ob hob, ↓reduceIte]
      simp only [slotRefOf, hob, Option.bind_some]
    | stream r =>
      show M.toH.ptrRef S0 y { ref := r, handle := none } = _
      unfold HMem.ptrRef
      simp only [Option.bind_none]
      rfl
  -- A converted memory slot to y's canonical object holds y's live handle.
  have hholds : ∀ y b, M.canonicalOf y = some b → M.toH.HoldsLive y (M.ptrOfH (y, Slot.mem b)).2 := by
    intro y b hc
    obtain ⟨ht, ob, hob, -⟩ := (M.canonicalOf_eq_some y b).mp hc
    refine ⟨b, ?_, by rw [Mem.toH_tableOf]; exact ht, by simp [hcan, hc]⟩
    show (if M.heldA b then some b else none) = some b
    simp [hheld b ob hob]
  refine
    { len := hm.len
      pre := hm.pre
      sEq := hm.sEq
      freshO := ?_
      freshH := ?_
      objNodup := ?_
      hNodup := ?_
      root := ?_
      tbl := ?_
      liveW := ?_
      cc := ?_
      pos := ?_
      dCanon := fun y hy => by rw [hcan]; exact hm.dCanon y hy
      snap := ?_
      ruleR := ?_
      wver := ?_
      rver := ?_
      slots := ?_
      live := ?_ }
  · intro a ha
    rw [Mem.toH_obj?]
    split
    · rw [hm.fresh a ha]; rfl
    · rfl
  · intro n hn
    cases hh : M.toH.handle? n with
    | none => rfl
    | some hd =>
      exfalso
      obtain ⟨y, ht, -⟩ := Mem.toH_handle?_some hm.tblNodup hh
      obtain ⟨o, ho, -⟩ := hv y n ht
      rw [hm.fresh n hn] at ho; cases ho
  · rw [Mem.toH_objs, List.map_map]
    exact (List.Sublist.map _ List.filter_sublist).nodup hm.objNodup
  · rw [Mem.toH_handles, List.map_map]
    have hinj : ∀ x ∈ M.table, ∀ z ∈ M.table, x.2 = z.2 → x = z := by
      intro x hx z hz hxz
      obtain ⟨y1, a1⟩ := x
      obtain ⟨y2, a2⟩ := z
      simp only at hxz
      subst hxz
      have h1 := lookup_of_mem M.table hm.tblNodup (y1, a1) hx
      have h2 := lookup_of_mem M.table hm.tblNodup (y2, a1) hz
      obtain ⟨o1, ho1, hn1⟩ := hv y1 a1 h1
      obtain ⟨o2, ho2, hn2⟩ := hv y2 a1 h2
      rw [ho1, Option.some.injEq] at ho2
      subst ho2
      rw [← hn1, hn2]
    exact nodup_map_of_inj _ M.table (nodup_of_map _ hm.tblNodup) (fun x hx z hz h => hinj x hx z hz h)
  · obtain ⟨o, ho, hc, hn⟩ := hm.root
    exact ⟨M.objH o, hobjH _ o ho, hc, hn⟩
  · refine ⟨fun y n hy => ?_, hm.tblNodup, fun n hd hh hl => ?_, fun n hd hh hdd => ?_, fun a o' ho' => ?_,
      fun a o' y p n ho' hp hpn => ?_⟩
    · rw [Mem.toH_tableOf] at hy
      obtain ⟨o, ho, hon⟩ := hv y n hy
      exact ⟨handleOfEntry (y, n), n, M.objH o, hhandle y n hy, rfl, rfl, rfl, hobjH n o ho, hon⟩
    · obtain ⟨y, ht, rfl⟩ := Mem.toH_handle?_some hm.tblNodup hh
      exact ht
    · obtain ⟨y, ht, rfl⟩ := Mem.toH_handle?_some hm.tblNodup hh
      cases hdd
    · obtain ⟨o, ho, rfl⟩ := hback a o' ho'
      have ht := hm.canonTbl a o ho (hall a o ho)
      exact ⟨a, ht, hobjOf o.node a ht⟩
    · obtain ⟨o, ho, rfl⟩ := hback a o' ho'
      rw [Mem.objH_ptr?] at hp
      cases hsl : o.slot? y with
      | none => rw [hsl] at hp; cases hp
      | some sl =>
        rw [hsl] at hp
        simp only [Option.map_some, Option.some.injEq] at hp
        subst hp
        cases sl with
        | stream r => cases hpn
        | mem b =>
          obtain ⟨ob, hob, hnb⟩ := hm.slotsNode a o ho y b hsl
          have htb := hm.canonTbl b ob hob (hall b ob hob)
          have hpn' : (if M.heldA b then some b else none) = some n := hpn
          simp [hheld b ob hob] at hpn'
          subst hpn'
          exact ⟨handleOfEntry (ob.node, b), hhandle ob.node b htb, hnb⟩
  · intro n hd hh _
    obtain ⟨y, -, rfl⟩ := Mem.toH_handle?_some hm.tblNodup hh
    rfl
  · intro a o' ho' hc
    obtain ⟨o, ho, rfl⟩ := hback a o' ho'
    exact hm.cc a o ho hc
  · intro a o' ho' hc
    obtain ⟨o, ho, rfl⟩ := hback a o' ho'
    exact hm.pos.lv0 (hm.canonicalOf_of ho hc) ho
  · intro a o' ho' hc
    obtain ⟨o, ho, rfl⟩ := hback a o' ho'
    have h1 : o.canonical = false := hc
    rw [hall a o ho] at h1; cases h1
  · intro n hd b o' w hh hb ho' hc _
    obtain ⟨o, ho, rfl⟩ := hback b o' ho'
    have h1 : o.canonical = false := hc
    rw [hall b o ho] at h1; cases h1
  · intro n hd w hh hw
    obtain ⟨y, -, rfl⟩ := Mem.toH_handle?_some hm.tblNodup hh
    cases hw
  · intro a o' y p r ho' hp hr
    obtain ⟨o, ho, rfl⟩ := hback a o' ho'
    rw [Mem.objH_ptr?] at hp
    cases hsl : o.slot? y with
    | none => rw [hsl] at hp; cases hp
    | some sl =>
      rw [hsl] at hp
      simp only [Option.map_some, Option.some.injEq] at hp
      subst hp
      cases sl with
      | stream r0 => exact hstr a o y r0 ho hsl r hr
      | mem b =>
        obtain ⟨ob, hob, hnb⟩ := hm.slotsNode a o ho y b hsl
        have hr' : (M.obj? b).bind (·.pos) = some r := hr
        rw [hob] at hr'
        simp only [Option.bind_some] at hr'
        rw [hm.pos.lv0 (hm.canonicalOf_of hob (hall b ob hob)) hob, hnb] at hr'
        cases hl : db.S.lv y with
        | none => rw [hl] at hr'; cases hr'
        | some v =>
          rw [hl] at hr'
          simp only [Option.map_some, Option.some.injEq] at hr'
          subst hr'
          exact ⟨v, hinv.lv_at hl⟩
  · intro a o' ho' hrel y hy
    obtain ⟨o, ho, rfl⟩ := hback a o' ho'
    obtain ⟨sl, hsl, hi1, hi2⟩ := hm.slots a o ho hrel y hy
    refine ⟨(M.ptrOfH (y, sl)).2, by rw [Mem.objH_ptr?, hsl]; rfl, fun hD => ?_, fun hD => ?_⟩
    · rw [hptrRef a o y sl ho hsl]; exact hi1 hD
    · rcases hi2 hD with ⟨b, rfl, hc⟩ | h
      · exact Or.inl (hholds y b hc)
      · exact Or.inr h
  · intro a o' ho' hc hr y hy
    obtain ⟨o, ho, rfl⟩ := hback a o' ho'
    obtain ⟨sl, hsl, hl1, hl2⟩ := hm.live a o ho hc hr y hy
    refine ⟨(M.ptrOfH (y, sl)).2, by rw [Mem.objH_ptr?, hsl]; rfl, fun hD => ?_, fun hD => ?_⟩
    · obtain ⟨b, rfl, hcb⟩ := hl1 hD
      exact hholds y b hcb
    · rw [hptrRef a o y sl ho hsl]; exact hl2 hD

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

theorem HMem.linkObj_ptr (m : HMem V) (D : Dirty) (a : Nat) (o : HObj V) (y : NodeId) :
    (m.linkObj D a o).ptr? y = o.ptr? y ∨
      ∃ q, o.ptr? y = some q ∧ q.handle = none ∧ (m.canonicalOf y).isSome = true ∧
        (m.linkObj D a o).ptr? y = some { q with handle := m.tableOf y } := by
  unfold HMem.linkObj
  split
  · exact Or.inl rfl
  · unfold HObj.ptr?
    simp only
    rw [lookup_map_key m.linkPtr (HMem.linkPtr_fst m) y o.ptrs]
    cases hs : List.lookup y o.ptrs with
    | none => exact Or.inl rfl
    | some q =>
      simp only [Option.map_some]
      unfold HMem.linkPtr
      simp only
      cases hq : q.handle with
      | some n => left; rfl
      | none =>
        simp only
        cases hc : m.canonicalOf y with
        | none => left; rfl
        | some b => right; exact ⟨q, rfl, hq, rfl, rfl⟩

section Relink

variable {sp : Spec V T} {db : DB V T} {S0 : Stream V T} {k : Nat} {m m' : HMem V}

/-- The invariant survives pointers taking the live handle of a node with a
canonical object, with any reference that names a version, the cores, the
table, the handles and the rest staying. Rule 4 with handles keeps the
pointer's own reference; the startup from the stream after T(k), against
Evict.lean's taken to handles, has the stream slot's reference where Evict.lean
has the canonical object's position (SIS/Proof/HandleRestart.lean). -/
theorem HEInv.relinkH (hm : HEInv sp db S0 k m)
    (hfw : ∀ a o, m.obj? a = some o → ∃ o', m'.obj? a = some o')
    (hbk : ∀ a o', m'.obj? a = some o' → ∃ o, m.obj? a = some o ∧ o'.core = o.core ∧
      (o.canonical = false → o' = o) ∧
      ∀ y, o'.ptr? y = o.ptr? y ∨ ∃ q q', o.ptr? y = some q ∧ o'.ptr? y = some q' ∧
        q'.handle = m.tableOf y ∧ (m.canonicalOf y).isSome = true ∧
        ∀ r, q'.ref = some r → ∃ u, db.S.versionAt r y = some u)
    (htab : m'.table = m.table) (hh : m'.handles = m.handles) (hs : m'.s = m.s) (hroot : m'.root = m.root)
    (hno : m'.nextObj = m.nextObj) (hnh : m'.nextHandle = m.nextHandle)
    (hnd : (m'.objs.map (·.1)).Nodup) : HEInv sp db S0 k m' := by
  have htab' : ∀ y, m'.tableOf y = m.tableOf y := by intro y; unfold HMem.tableOf; rw [htab]
  have hh' : ∀ n, m'.handle? n = m.handle? n := by intro n; unfold HMem.handle?; rw [hh]
  have hof : ∀ n, m'.objOf n = m.objOf n := by intro n; unfold HMem.objOf; rw [hh']
  have hcore : ∀ a, (m'.obj? a).map (fun o => (o.canonical, o.pos)) =
      (m.obj? a).map (fun o => (o.canonical, o.pos)) := by
    intro a
    cases ho' : m'.obj? a with
    | none =>
      cases ho : m.obj? a with
      | none => rfl
      | some o => obtain ⟨o', ho''⟩ := hfw a o ho; rw [ho'] at ho''; cases ho''
    | some o' =>
      obtain ⟨o, ho, hc, -⟩ := hbk a o' ho'
      rw [ho]
      have e5 : o'.canonical = o.canonical := congrArg (fun c => c.2.2.2.2.1) hc
      have e6 : o'.pos = o.pos := congrArg (fun c => c.2.2.2.2.2) hc
      simp [e5, e6]
  have hcan : ∀ y, m'.canonicalOf y = m.canonicalOf y := by
    apply HMem.canonicalOf_congr htab' hh'
    intro a
    have h := congrArg (Option.map Prod.fst) (hcore a)
    rw [Option.map_map, Option.map_map] at h
    exact h
  have href : ∀ y p, m'.ptrRef S0 y p = m.ptrRef S0 y p := by
    intro y p
    apply HMem.ptrRef_congr S0 hs
    · cases p.handle with
      | none => rfl
      | some n => simp only [Option.bind_some]; exact hh' n
    · intro hd b _ _; exact hcore b
  have hhl : ∀ y p, m.HoldsLive y p → m'.HoldsLive y p := by
    intro y p ⟨n, h1, h2, h3⟩
    exact ⟨n, h1, by rw [htab']; exact h2, by rw [hcan]; exact h3⟩
  -- A pointer that takes y's live handle: what INV-SLOT and the live pointers ask.
  have hnewp : ∀ (y : NodeId) (q : HPtr), q.handle = m.tableOf y → (m.canonicalOf y).isSome = true →
      m'.HoldsLive y q ∧ m'.ptrRef S0 y q = (db.S.lv y).map (·.recNo) := by
    intro y q hq hc
    have hc' : (m'.canonicalOf y).isSome = true := by rw [hcan]; exact hc
    obtain ⟨b0, hb0⟩ := Option.isSome_iff_exists.mp hc'
    obtain ⟨n0, -, htn0, -⟩ := (m'.canonicalOf_eq_some y b0).mp hb0
    have hhl' : m'.HoldsLive y q := ⟨n0, by rw [hq, ← htab', htn0], htn0, hc'⟩
    refine ⟨hhl', ?_⟩
    obtain ⟨b, o, hcb, ho, -, hpr⟩ := HMem.ptrRef_of_holdsLive S0 hhl'
    rw [hpr]
    obtain ⟨o0, ho0, hc0, hn0⟩ := hm.obj_of_canonicalOf (by rw [← hcan]; exact hcb)
    have h1 := hcore b
    rw [ho, ho0] at h1
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h1
    rw [h1.2, hm.pos b o0 ho0 hc0, hn0]
  have hbk' : ∀ a o', m'.obj? a = some o' → ∃ o, m.obj? a = some o ∧ o'.node = o.node ∧
      o'.level = o.level ∧ o'.isData = o.isData ∧ o'.hist = o.hist ∧ o'.canonical = o.canonical ∧
      o'.pos = o.pos ∧ (o.canonical = false → o' = o) ∧
      ∀ y, o'.ptr? y = o.ptr? y ∨ ∃ q q', o.ptr? y = some q ∧ o'.ptr? y = some q' ∧
        q'.handle = m.tableOf y ∧ (m.canonicalOf y).isSome = true ∧
        ∀ r, q'.ref = some r → ∃ u, db.S.versionAt r y = some u := by
    intro a o' ho'
    obtain ⟨o, ho, hc, hsn, hpt⟩ := hbk a o' ho'
    simp only [HObj.core, Prod.mk.injEq] at hc
    exact ⟨o, ho, hc.1, hc.2.1, hc.2.2.1, hc.2.2.2.1, hc.2.2.2.2.1, hc.2.2.2.2.2, hsn, hpt⟩
  refine
    { len := hm.len
      pre := hm.pre
      sEq := by rw [hs]; exact hm.sEq
      freshO := fun a ha => by
        cases ho' : m'.obj? a with
        | none => rfl
        | some o' =>
          obtain ⟨o, ho, -⟩ := hbk a o' ho'
          rw [hm.freshO a (by rw [← hno]; exact ha)] at ho; cases ho
      freshH := fun n hn => by rw [hh']; exact hm.freshH n (by rw [← hnh]; exact hn)
      objNodup := hnd
      hNodup := by rw [hh]; exact hm.hNodup
      root := ?_
      tbl := ?_
      liveW := fun n hd h1 h2 => hm.liveW n hd (by rw [← hh']; exact h1) h2
      cc := ?_
      pos := ?_
      dCanon := fun y hy => by rw [hcan]; exact hm.dCanon y hy
      snap := ?_
      ruleR := ?_
      wver := fun n hd w h1 h2 => hm.wver n hd w (by rw [← hh']; exact h1) h2
      rver := ?_
      slots := ?_
      live := ?_ }
  · obtain ⟨o, ho, hc, hn⟩ := hm.root
    obtain ⟨o', ho'⟩ := hfw _ o ho
    obtain ⟨o0, ho0, e1, -, -, -, e5, -⟩ := hbk' _ o' ho'
    rw [ho, Option.some.injEq] at ho0
    subst ho0
    exact ⟨o', by rw [hroot]; exact ho', by rw [e5, hc], by rw [e1, hn]⟩
  · refine ⟨fun y n hy => ?_, by rw [htab]; exact hm.tbl.nodup, fun n hd h1 h2 => ?_, fun n hd h1 h2 => ?_,
      fun a o' ho' => ?_, fun a o' y q n ho' hq hqn => ?_⟩
    · rw [htab'] at hy
      obtain ⟨hd, b, ob, h1, h2, h3, h4, h5, h6⟩ := hm.tbl.entry hy
      obtain ⟨ob', hob'⟩ := hfw b ob h5
      obtain ⟨ob0, hob0, e1, -⟩ := hbk' b ob' hob'
      rw [h5, Option.some.injEq] at hob0
      subst hob0
      exact ⟨hd, b, ob', by rw [hh']; exact h1, h2, h3, h4, hob', by rw [e1, h6]⟩
    · rw [hh'] at h1; rw [htab']; exact hm.tbl.liveIn h1 h2
    · rw [hh'] at h1; exact hm.tbl.deadNone h1 h2
    · obtain ⟨o, ho, e1, -⟩ := hbk' a o' ho'
      obtain ⟨n, h1, h2⟩ := hm.tbl.held ho
      exact ⟨n, by rw [htab', e1]; exact h1, by rw [hof]; exact h2⟩
    · obtain ⟨o, ho, -, -, -, -, -, -, -, hpt⟩ := hbk' a o' ho'
      rcases hpt y with h | ⟨q0, q1, -, h, hq1, -, -⟩
      · rw [h] at hq
        obtain ⟨hd, h1, h2⟩ := hm.tbl.ptrNode ho hq hqn
        exact ⟨hd, by rw [hh']; exact h1, h2⟩
      · rw [h, Option.some.injEq] at hq
        rw [← hq, hq1] at hqn
        obtain ⟨hd, -, -, h1, -, h2, -⟩ := hm.tbl.entry hqn
        exact ⟨hd, by rw [hh']; exact h1, h2⟩
  · intro a o' ho' hc
    obtain ⟨o, ho, e1, e2, e3, e4, e5, -⟩ := hbk' a o' ho'
    rw [e1, e2, e3, e4]
    exact hm.cc a o ho (by rw [← e5]; exact hc)
  · intro a o' ho' hc
    obtain ⟨o, ho, e1, -, -, -, e5, e6, -⟩ := hbk' a o' ho'
    rw [e6, e1]
    exact hm.pos a o ho (by rw [← e5]; exact hc)
  · intro a o' ho' hc
    obtain ⟨o, ho, -, -, -, -, e5, -, hsn, -⟩ := hbk' a o' ho'
    have hc0 : o.canonical = false := by rw [← e5]; exact hc
    rw [hsn hc0]
    exact (hm.snap a o ho hc0).of_s hs
  · intro n hd b o' w h1 h2 ho' hc hw
    obtain ⟨o, ho, -, -, -, -, e5, -, hsn, -⟩ := hbk' b o' ho'
    have hc0 : o.canonical = false := by rw [← e5]; exact hc
    rw [hsn hc0]
    rw [hs] at hw
    exact hm.ruleR n hd b o w (by rw [← hh']; exact h1) h2 ho hc0 hw
  · intro a o' y q r ho' hq hr
    obtain ⟨o, ho, -, -, -, -, -, -, -, hpt⟩ := hbk' a o' ho'
    rcases hpt y with h | ⟨q0, q1, -, h, -, -, hv⟩
    · rw [h] at hq; exact hm.rver a o y q r ho hq hr
    · rw [h, Option.some.injEq] at hq
      rw [← hq] at hr
      exact hv r hr
  · intro a o' ho' hrel y hy
    obtain ⟨o, ho, e1, -, -, e4, e5, -, -, hpt⟩ := hbk' a o' ho'
    have hrel0 : HRelevant sp db k o := by
      obtain ⟨h1, h2, h3⟩ := hrel
      exact ⟨by rw [← e5]; exact h1, by rw [← e1]; exact h2, by rw [← e1]; exact h3⟩
    obtain ⟨q, hq, hi1, hi2⟩ := hm.slots a o ho hrel0 y (by rw [← e4]; exact hy)
    rcases hpt y with h | ⟨q0, q1, -, h, hq1, hc, -⟩
    · refine ⟨q, by rw [h]; exact hq, fun hD => by rw [href]; exact hi1 hD, fun hD => ?_⟩
      rcases hi2 hD with h' | h'
      · exact Or.inl (hhl y q h')
      · rw [e1]; exact Or.inr h'
    · obtain ⟨hhl', hval⟩ := hnewp y q1 hq1 hc
      exact ⟨_, h, fun _ => hval, fun _ => Or.inl hhl'⟩
  · intro a o' ho' hc hr y hy
    obtain ⟨o, ho, e1, -, -, e4, e5, -, -, hpt⟩ := hbk' a o' ho'
    obtain ⟨q, hq, hl1, hl2⟩ := hm.live a o ho (by rw [← e5]; exact hc) (by rw [← e1]; exact hr) y
      (by rw [← e4]; exact hy)
    rcases hpt y with h | ⟨q0, q1, -, h, hq1, hcz, -⟩
    · exact ⟨q, by rw [h]; exact hq, fun hD => hhl y q (hl1 hD), fun hD => by rw [href]; exact hl2 hD⟩
    · obtain ⟨hhl', hval⟩ := hnewp y q1 hq1 hcz
      exact ⟨_, h, fun _ => hhl', fun _ => hval⟩

/-- Rule 4 with handles keeps the invariant. -/
theorem HEInv.linkD (hm : HEInv sp db S0 k m) (D : Dirty) : HEInv sp db S0 k (m.linkD D) := by
  apply hm.relinkH
  · intro a o ho
    exact ⟨_, by rw [HMem.linkD_obj?, ho]; rfl⟩
  · intro a o' ho'
    rw [HMem.linkD_obj?] at ho'
    obtain ⟨o, ho, rfl⟩ := Option.map_eq_some_iff.mp ho'
    refine ⟨o, ho, HMem.linkObj_core m D a o, fun hc => ?_, fun y => ?_⟩
    · unfold HMem.linkObj
      simp [hc]
    · rcases HMem.linkObj_ptr m D a o y with h | ⟨q, hq, -, hc, h⟩
      · exact Or.inl h
      · exact Or.inr ⟨q, _, hq, h, rfl, hc, fun r hr => hm.rver a o y q r ho hq hr⟩
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rw [HMem.linkD_keys]; exact hm.objNodup

end Relink

/-! ## The startup with handles from R(0) -/

/-- The startup with handles from R(0) gives a memory with the invariant. -/
theorem heinv_init {sp : Spec V T} (hsp : SpecOK sp) :
    HEInv sp (init sp) (init sp).S 0 (handleStartup sp (init sp).S) := by
  have hinv := inv_init sp hsp
  have hb := hinv.base2 (sp := sp)
  have h0 := einv_lazyBase hsp
  have hs : (lazyBase sp (init sp).S).Same ((lazyBase sp (init sp).S).sectionPos (init sp).S) := by
    apply Mem.sectionPos_same
    intro h o ho hc w hw
    rw [h0.sEq, init_lastSp, init_newest] at hw
    rw [h0.pos.lv0 (h0.canonicalOf_of ho hc) ho, hw]
    rfl
  have hM := h0.same hs h0.tblNodup (by rw [Mem.sectionPos_keys]; exact h0.objNodup)
  -- Every object of the lazy startup is canonical.
  have hall0 : ∀ h o, (lazyBase sp (init sp).S).obj? h = some o → o.canonical = true := by
    intro h o ho
    unfold lazyBase at ho
    rw [linkCanonical_obj?] at ho
    obtain ⟨o2, ho2, rfl⟩ := Option.map_eq_some_iff.mp ho
    rw [(linkObj_fields _ o2).2.2.2.2.1]
    exact (hb.obj h o2 ho2).2.1
  have hall : ∀ h o, ((lazyBase sp (init sp).S).sectionPos (init sp).S).obj? h = some o →
      o.canonical = true := by
    intro h o ho; rw [hs.1] at ho; exact hall0 h o ho
  -- Its stream slots name the pointees' latest versions.
  have hstr0 : ∀ h o y r, (lazyBase sp (init sp).S).obj? h = some o → o.slot? y = some (Slot.stream r) →
      r = ((init sp).S.lv y).map (·.recNo) := by
    intro h o y r ho hsl
    unfold lazyBase at ho
    rw [linkCanonical_obj?] at ho
    obtain ⟨o2, ho2, rfl⟩ := Option.map_eq_some_iff.mp ho
    obtain ⟨-, hc2, -⟩ := hb.obj h o2 ho2
    rw [linkObj_slot? _ hc2] at hsl
    cases hs2 : o2.slot? y with
    | none => rw [hs2] at hsl; cases hsl
    | some sl2 =>
      rw [hs2] at hsl
      simp only [Option.map_some, Option.some.injEq] at hsl
      have hsl2 := (init_base_slot hsp ho2).2 y sl2 hs2
      subst hsl2
      cases hl : (init sp).S.lv y with
      | none =>
        rw [hl] at hsl
        have he : (linkQ (lazyRoot sp (init sp).S (lazySec sp (init sp).S))
            (y, Slot.stream (Option.map (fun x : Version V => x.recNo) none))).2 = Slot.stream none := rfl
        rw [he] at hsl
        cases hsl
        rfl
      | some v =>
        rw [hl] at hsl
        simp only [Option.map_some] at hsl
        rcases linkQ_some (lazyRoot sp (init sp).S (lazySec sp (init sp).S)) y v.recNo with he | ⟨h0', o0, -, -, he⟩
        · rw [he] at hsl; cases hsl; rfl
        · rw [he] at hsl; cases hsl
  have hstr : ∀ h o y r, ((lazyBase sp (init sp).S).sectionPos (init sp).S).obj? h = some o →
      o.slot? y = some (Slot.stream r) → ∀ r', r = some r' → ∃ u, (init sp).S.versionAt r' y = some u := by
    intro h o y r ho hsl r' hr
    rw [hs.1] at ho
    rw [hstr0 h o y r ho hsl] at hr
    cases hl : (init sp).S.lv y with
    | none => rw [hl] at hr; cases hr
    | some v =>
      rw [hl] at hr
      simp only [Option.map_some, Option.some.injEq] at hr
      subst hr
      exact ⟨v, hinv.lv_at hl⟩
  have he : handleStartup sp (init sp).S =
      (((lazyBase sp (init sp).S).sectionPos (init sp).S).toH).linkD (init sp).D := by
    unfold handleStartup
    rw [init_lazyStartup, init_startup_D]; rfl
  rw [he]
  exact (hM.toH hinv hall hstr).linkD _

end SIS
