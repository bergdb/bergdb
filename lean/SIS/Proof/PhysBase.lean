/-
Proofs about the physical layer, part 14: the memory before the rerun of a
lazy startup (steps 1 and 2 and the memory slots) meets the invariant at the
startup pos s (bergdb item 001, WP L3).
-/
import SIS.Proof.PhysLazy

set_option linter.unusedSectionVars false

namespace SIS

variable {V T : Type} [DecidableEq V]

/-! ### Lookups in lists whose keys a map keeps -/

theorem lookup_map_key {β : Type} (f : Nat × β → Nat × β) (hf : ∀ q, (f q).1 = q.1) (y : Nat) :
    ∀ (l : List (Nat × β)), List.lookup y (l.map f) = (List.lookup y l).map (fun b => (f (y, b)).2) := by
  intro l
  induction l with
  | nil => rfl
  | cons q l ih =>
    obtain ⟨a, b⟩ := q
    rw [List.map_cons, lookup_cons_eq, lookup_cons_eq, hf]
    by_cases hya : y = a
    · subst hya
      simp only [↓reduceIte, Option.map_some]
    · simp only [hya, ↓reduceIte, ih]

/-! ### The memory slots between canonical objects (`linkCanonical`) -/

/-- What `linkCanonical` makes of the slot q of a canonical object. -/
def linkQ (m : Mem V) (q : NodeId × Slot) : NodeId × Slot :=
  match q.2 with
  | Slot.stream (some r) =>
    match m.tableOf q.1 with
    | some h0 =>
      match m.obj? h0 with
      | some o0 => if o0.canonical && o0.pos == some r then (q.1, Slot.mem h0) else q
      | none => q
    | none => q
  | _ => q

/-- What `linkCanonical` makes of object o. -/
def linkObj (m : Mem V) (o : Obj V) : Obj V :=
  if !o.canonical then o else { o with slots := o.slots.map (linkQ m) }

theorem linkCanonical_eq (m : Mem V) :
    m.linkCanonical = { m with objs := m.objs.map (fun p => (p.1, linkObj m p.2)) } := by
  unfold Mem.linkCanonical
  congr 1
  apply List.map_congr_left
  intro p _
  unfold linkObj
  cases hc : p.2.canonical
  · simp
  · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, Prod.mk.injEq, true_and]
    rw [hc]
    rfl

theorem linkQ_fst (m : Mem V) (q : NodeId × Slot) : (linkQ m q).1 = q.1 := by
  unfold linkQ
  split
  · split
    · split
      · split <;> rfl
      · rfl
    · rfl
  · rfl

theorem linkQ_cases (m : Mem V) (y : NodeId) (sl : Slot) :
    (linkQ m (y, sl)).2 = sl ∨ ∃ h0 o0, m.tableOf y = some h0 ∧ m.obj? h0 = some o0 ∧
      o0.canonical = true ∧ (linkQ m (y, sl)).2 = Slot.mem h0 := by
  unfold linkQ
  simp only
  split
  · split
    · rename_i h0 ht
      split
      · rename_i o0 ho
        split
        · rename_i hc
          right
          simp only [Bool.and_eq_true] at hc
          exact ⟨h0, o0, ht, ho, hc.1, rfl⟩
        · left; rfl
      · left; rfl
    · left; rfl
  · left; rfl

@[simp] theorem linkCanonical_s (m : Mem V) : m.linkCanonical.s = m.s := rfl
@[simp] theorem linkCanonical_root (m : Mem V) : m.linkCanonical.root = m.root := rfl
@[simp] theorem linkCanonical_next (m : Mem V) : m.linkCanonical.next = m.next := rfl
theorem linkCanonical_tableOf (m : Mem V) (y : NodeId) : m.linkCanonical.tableOf y = m.tableOf y := rfl

theorem linkCanonical_obj? (m : Mem V) (h : Nat) :
    m.linkCanonical.obj? h = (m.obj? h).map (linkObj m) := by
  rw [linkCanonical_eq]
  unfold Mem.obj?
  exact lookup_map_key (fun p => (p.1, linkObj m p.2)) (fun _ => rfl) h m.objs

theorem linkCanonical_keys (m : Mem V) : m.linkCanonical.objs.map (·.1) = m.objs.map (·.1) := by
  rw [linkCanonical_eq]
  simp

theorem linkObj_fields (m : Mem V) (o : Obj V) :
    (linkObj m o).node = o.node ∧ (linkObj m o).level = o.level ∧ (linkObj m o).isData = o.isData ∧
    (linkObj m o).hist = o.hist ∧ (linkObj m o).canonical = o.canonical ∧ (linkObj m o).pos = o.pos := by
  unfold linkObj
  cases hc : o.canonical <;> simp [hc]

theorem linkObj_slot? (m : Mem V) {o : Obj V} (hc : o.canonical = true) (y : NodeId) :
    (linkObj m o).slot? y = (o.slot? y).map (fun sl => (linkQ m (y, sl)).2) := by
  unfold linkObj Obj.slot?
  simp only [hc, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  exact lookup_map_key (linkQ m) (linkQ_fst m) y o.slots

theorem linkCanonical_canonicalOf (m : Mem V) (y : NodeId) :
    m.linkCanonical.canonicalOf y = m.canonicalOf y := by
  unfold Mem.canonicalOf
  rw [linkCanonical_tableOf]
  cases m.tableOf y with
  | none => rfl
  | some h =>
    simp only
    rw [linkCanonical_obj?]
    cases m.obj? h with
    | none => rfl
    | some o => simp only [Option.map_some, (linkObj_fields m o).2.2.2.2.1]

/-! ### The objects that startup makes from versions -/

theorem canonOfVersion_fields (sp : Spec V T) (S : Stream V T) (s : Nat) (w : Version V) :
    (canonOfVersion sp S s w).node = w.node ∧ (canonOfVersion sp S s w).level = w.level ∧
    (canonOfVersion sp S s w).isData = w.isData ∧
    (canonOfVersion sp S s w).hist =
      cutHist w (if isKeyLevel sp w.isData w.level then some s else none) ∧
    (canonOfVersion sp S s w).canonical = true ∧ (canonOfVersion sp S s w).pos = some w.recNo := by
  obtain ⟨f1, f2, f3, f4, -, f6⟩ := Obj.ofVersion_fields sp w
    (if isKeyLevel sp w.isData w.level then some s else none)
  unfold canonOfVersion
  exact ⟨f1, f2, f3, f4, rfl, f6⟩

theorem canonOfVersion_slot? (sp : Spec V T) (S : Stream V T) (s : Nat) (w : Version V) (y : NodeId) :
    (canonOfVersion sp S s w).slot? y =
      if y ∈ pointees sp (cutHist w (if isKeyLevel sp w.isData w.level then some s else none)) then
        some (Slot.stream (ruleRRef S s y (w.ref? y))) else none := by
  have key := Obj.ofVersion_slot? sp w (if isKeyLevel sp w.isData w.level then some s else none) y
  unfold canonOfVersion Obj.slot?
  simp only
  rw [lookup_map_key _ (fun q => by split <;> rfl) y]
  unfold Obj.slot? at key
  rw [key]
  by_cases hy : y ∈ pointees sp (cutHist w (if isKeyLevel sp w.isData w.level then some s else none))
  · simp only [hy, ↓reduceIte, Option.map_some]
  · simp only [hy, ↓reduceIte, Option.map_none]

theorem canonOfVersion_stream (sp : Spec V T) (S : Stream V T) (s : Nat) (w : Version V) {y : NodeId}
    {sl : Slot} (h : (canonOfVersion sp S s w).slot? y = some sl) : ∃ r, sl = Slot.stream r := by
  rw [canonOfVersion_slot?] at h
  by_cases hy : y ∈ pointees sp (cutHist w (if isKeyLevel sp w.isData w.level then some s else none))
  · simp only [hy, ↓reduceIte, Option.some.injEq] at h
    exact ⟨_, h.symm⟩
  · simp only [hy, ↓reduceIte] at h
    cases h

/-! ### Step 1: the section -/

section Sec

variable {sp : Spec V T} {S : Stream V T}

theorem newest_node {s : Nat} {x : NodeId} {w : Version V} (h : newest S s x = some w) :
    w.node = x := by
  obtain ⟨r, -, hr⟩ := newest_some h
  obtain ⟨R, -, -, hwy⟩ := versionAt_spec hr
  exact hwy

/-- Step 1, after the nodes L of the section. -/
structure Sec1 (sp : Spec V T) (S : Stream V T) (L : List NodeId) (m : Mem V) : Prop where
  s : m.s = lastSp S
  root : m.root = 0
  fresh : ∀ h, m.next ≤ h → m.obj? h = none
  nodup : (m.objs.map (·.1)).Nodup
  obj : ∀ h o, m.obj? h = some o → ∃ w, newest S (lastSp S) o.node = some w ∧
    w.hist.upTo (lastSp S) ≠ [] ∧ o = canonOfVersion sp S (lastSp S) w ∧ m.tableOf o.node = some h
  tbl : ∀ y h, m.tableOf y = some h → y ∈ L ∧ ∃ o, m.obj? h = some o ∧ o.node = y
  cover : ∀ x ∈ L, ∀ w, newest S (lastSp S) x = some w → w.hist.upTo (lastSp S) ≠ [] →
    m.tableOf x ≠ none

theorem sec1_init : Sec1 sp S [] (mem0 S) :=
  ⟨rfl, rfl, fun _ _ => rfl, List.nodup_nil, (fun _ _ ho => by cases ho), (fun _ _ ht => by cases ht),
    (fun _ hx => by cases hx)⟩

theorem Sec1.same {L : List NodeId} {m : Mem V} (hm : Sec1 sp S L m) {x : NodeId}
    (hx : ∀ w, newest S (lastSp S) x = some w → w.hist.upTo (lastSp S) ≠ [] → False) :
    Sec1 sp S (L ++ [x]) m := by
  refine ⟨hm.s, hm.root, hm.fresh, hm.nodup, hm.obj, fun y h ht => ?_, fun x' hx' w hw hne => ?_⟩
  · obtain ⟨h1, h2⟩ := hm.tbl y h ht; exact ⟨List.mem_append_left _ h1, h2⟩
  · rcases List.mem_append.mp hx' with h1 | h1
    · exact hm.cover x' h1 w hw hne
    · rw [List.mem_singleton] at h1; subst h1; exact (hx w hw hne).elim

theorem secStep_add {m : Mem V} {x : NodeId} {w : Version V} (hn : newest S (lastSp S) x = some w)
    (he : (w.hist.upTo (lastSp S)).isEmpty = false) :
    secStep sp S m x = (m.addObj (canonOfVersion sp S (lastSp S) w)).1.setTable x m.next := by
  unfold secStep
  simp only [hn, he, Bool.false_eq_true, ↓reduceIte]
  rfl

theorem sec1_step {L : List NodeId} {m : Mem V} (hm : Sec1 sp S L m) {x : NodeId} (hx : x ∉ L) :
    Sec1 sp S (L ++ [x]) (secStep sp S m x) := by
  cases hn : newest S (lastSp S) x with
  | none =>
    have : secStep sp S m x = m := by unfold secStep; rw [hn]
    rw [this]
    exact hm.same (fun w hw _ => by rw [hn] at hw; cases hw)
  | some w =>
    cases he : (w.hist.upTo (lastSp S)).isEmpty with
    | true =>
      have : secStep sp S m x = m := by unfold secStep; simp only [hn, he, ↓reduceIte]
      rw [this]
      refine hm.same (fun w' hw' hne => ?_)
      rw [hn, Option.some.injEq] at hw'
      subst hw'
      exact hne (List.isEmpty_iff.mp he)
    | false =>
      rw [secStep_add hn he]
      have hwx := newest_node hn
      have hne : w.hist.upTo (lastSp S) ≠ [] := by
        intro h; rw [h] at he; cases he
      obtain ⟨f1, -, -, -, f5, -⟩ := canonOfVersion_fields sp S (lastSp S) w
      have hobj : ∀ h', ((m.addObj (canonOfVersion sp S (lastSp S) w)).1.setTable x m.next).obj? h' =
          if h' = m.next then some (canonOfVersion sp S (lastSp S) w) else m.obj? h' := by
        intro h'; rw [Mem.obj?_setTable, Mem.obj?_addObj]
      have htab : ∀ y, ((m.addObj (canonOfVersion sp S (lastSp S) w)).1.setTable x m.next).tableOf y =
          if y = x then some m.next else m.tableOf y := by
        intro y; rw [Mem.tableOf_setTable, Mem.tableOf_addObj]
      refine ⟨hm.s, hm.root, ?_, ?_, ?_, ?_, ?_⟩
      · intro h' hh'
        simp only [Mem.setTable_next, Mem.addObj_next] at hh'
        have hne' : h' ≠ m.next := by omega
        rw [hobj]
        simp only [hne', ↓reduceIte]
        exact hm.fresh h' (by omega)
      · simp only [Mem.setTable_objs]
        exact nodup_addObj_keys m _ hm.nodup hm.fresh
      · intro h' o ho
        rw [hobj] at ho
        by_cases hh : h' = m.next
        · simp only [hh, ↓reduceIte, Option.some.injEq] at ho
          subst ho; subst hh
          refine ⟨w, by rw [f1, hwx]; exact hn, hne, rfl, ?_⟩
          rw [htab, f1, hwx]
          simp
        · simp only [hh, ↓reduceIte] at ho
          obtain ⟨w', h1, h2, h3, h4⟩ := hm.obj h' o ho
          refine ⟨w', h1, h2, h3, ?_⟩
          have hox : o.node ≠ x := by
            intro hox
            exact hx (hox ▸ (hm.tbl o.node h' h4).1)
          rw [htab]
          simp only [hox, ↓reduceIte]
          exact h4
      · intro y h' ht
        rw [htab] at ht
        by_cases hy : y = x
        · simp only [hy, ↓reduceIte, Option.some.injEq] at ht
          subst ht; subst hy
          refine ⟨List.mem_append_right _ (List.mem_singleton_self _), canonOfVersion sp S (lastSp S) w,
            by rw [hobj]; simp, ?_⟩
          rw [f1, hwx]
        · simp only [hy, ↓reduceIte] at ht
          obtain ⟨h1, o, ho, hon⟩ := hm.tbl y h' ht
          have hne' : h' ≠ m.next := by
            intro he'; rw [he', hm.fresh m.next (Nat.le_refl _)] at ho; cases ho
          exact ⟨List.mem_append_left _ h1, o, by rw [hobj]; simp only [hne', ↓reduceIte]; exact ho, hon⟩
      · intro x' hx' w' hw' hne'
        rw [htab]
        by_cases hxx : x' = x
        · simp [hxx]
        · simp only [hxx, ↓reduceIte]
          rcases List.mem_append.mp hx' with h1 | h1
          · exact hm.cover x' h1 w' hw' hne'
          · exact absurd (List.mem_singleton.mp h1) hxx

theorem sec1_fold : ∀ (rest L : List NodeId) (m : Mem V), Sec1 sp S L m → (L ++ rest).Nodup →
    Sec1 sp S (L ++ rest) (rest.foldl (secStep sp S) m) := by
  intro rest
  induction rest with
  | nil => intro L m hm _; simpa using hm
  | cons x rest ih =>
    intro L m hm hnd
    simp only [List.foldl_cons]
    have hx : x ∉ L := by
      intro hxL
      have := List.nodup_append.mp hnd
      exact this.2.2 x hxL x List.mem_cons_self rfl
    have := ih (L ++ [x]) _ (sec1_step hm hx) (by simpa using hnd)
    simpa using this

/-- After step 1: the canonical objects of the section's index nodes with
entries up to s. -/
theorem sec1_lazySec : Sec1 sp S (sectionNodes S (lastSp S)) (lazySec sp S) := by
  have := sec1_fold (sp := sp) (S := S) (sectionNodes S (lastSp S)) [] (mem0 S) sec1_init
    (by rw [List.nil_append]; unfold sectionNodes; exact nodup_eraseDups _)
  unfold lazySec
  simpa using this

theorem mem_sectionNodes {s : Nat} {x : NodeId} {w : Version V} (h : newest S s x = some w)
    (hd : w.isData = false) : x ∈ sectionNodes S s := by
  unfold sectionNodes
  rw [List.mem_eraseDups]
  rw [newest_eq] at h
  obtain ⟨r, hr⟩ := lv_versionAt h
  obtain ⟨R, hR, hwR, hwx⟩ := versionAt_spec hr
  simp only [List.mem_flatMap, List.mem_map, List.mem_filter]
  exact ⟨R, List.mem_of_getElem? hR, w, ⟨hwR, by simp [hd]⟩, hwx⟩

end Sec

/-! ### Step 2: the root -/

section Root

variable {sp : Spec V T} {db : DB V T} {k : Nat}

/-- The virtual root's object that startup makes. -/
def vRootObj (sp : Spec V T) (S : Stream V T) : Obj V :=
  { (canonOfVersion sp S (lastSp S) (rootVersion sp (lastSp S) (topsRead sp S (lastSp S) true))) with
    hist := (rootVersion sp (lastSp S) (topsRead sp S (lastSp S) true)).hist, pos := none }

/-- Where an object before the memory slots comes from: a version of the
section (with entries up to s, but the root's); the virtual root; or the
root's latest version, written before s. -/
def BaseSrc (sp : Spec V T) (db : DB V T) (o : Obj V) : Prop :=
  (∃ w r, db.S.versionAt r o.node = some w ∧ lastSp db.S ≤ r ∧
      o = canonOfVersion sp db.S (lastSp db.S) w ∧ (o.node ≠ root → w.hist.upTo (lastSp db.S) ≠ [])) ∨
  (sp.virt = true ∧ o = vRootObj sp db.S) ∨
  (sp.virt = false ∧ ∃ u, db.S.lv root = some u ∧ u.recNo < lastSp db.S ∧
      newest db.S (lastSp db.S) root = none ∧ o = canonOfVersion sp db.S (lastSp db.S) u)

/-- The memory after steps 1 and 2. -/
structure Base2 (sp : Spec V T) (db : DB V T) (m : Mem V) : Prop where
  s : m.s = lastSp db.S
  fresh : ∀ h, m.next ≤ h → m.obj? h = none
  nodup : (m.objs.map (·.1)).Nodup
  root : m.tableOf root = some m.root ∧ ∃ o, m.obj? m.root = some o ∧ o.canonical = true ∧ o.node = root
  tbl : ∀ y h, m.tableOf y = some h → ∃ o, m.obj? h = some o ∧ o.node = y
  obj : ∀ h o, m.obj? h = some o → m.tableOf o.node = some h ∧ o.canonical = true ∧ BaseSrc sp db o
  cover : ∀ x w, newest db.S (lastSp db.S) x = some w → w.isData = false →
    w.hist.upTo (lastSp db.S) ≠ [] → m.canonicalOf x ≠ none

theorem Sec1.canonicalOf {S : Stream V T} {L : List NodeId} {m : Mem V} (hm : Sec1 sp S L m)
    {y : NodeId} {h : Nat} (ht : m.tableOf y = some h) : m.canonicalOf y = some h := by
  obtain ⟨-, o, ho, -⟩ := hm.tbl y h ht
  obtain ⟨w, -, -, hw, -⟩ := hm.obj h o ho
  have hc : o.canonical = true := by rw [hw]; exact (canonOfVersion_fields sp S _ w).2.2.2.2.1
  exact (m.canonicalOf_eq_some y h).mpr ⟨ht, o, ho, hc⟩

theorem Sec1.src {L : List NodeId} {m : Mem V} (hm : Sec1 sp db.S L m) {h : Nat} {o : Obj V}
    (ho : m.obj? h = some o) : o.canonical = true ∧ BaseSrc sp db o := by
  obtain ⟨w, hn, hne, hw, -⟩ := hm.obj h o ho
  obtain ⟨r, hr, hwr⟩ := newest_some hn
  refine ⟨by rw [hw]; exact (canonOfVersion_fields sp _ _ w).2.2.2.2.1, Or.inl ⟨w, r, hwr, hr, hw, fun _ => hne⟩⟩

/-- Step 2 adds a canonical object for the root. -/
theorem base2_add {m1 : Mem V} (h1 : Sec1 sp db.S (sectionNodes db.S (lastSp db.S)) m1)
    (hr : m1.tableOf root = none) {o : Obj V} (hon : o.node = root) (hoc : o.canonical = true)
    (hsrc : BaseSrc sp db o) :
    Base2 sp db { ((m1.addObj o).1.setTable root m1.next) with root := m1.next } := by
  have hobj : ∀ h', ({ ((m1.addObj o).1.setTable root m1.next) with root := m1.next } : Mem V).obj? h' =
      if h' = m1.next then some o else m1.obj? h' := by
    intro h'
    show ((m1.addObj o).1.setTable root m1.next).obj? h' = _
    rw [Mem.obj?_setTable, Mem.obj?_addObj]
  have htab : ∀ y, ({ ((m1.addObj o).1.setTable root m1.next) with root := m1.next } : Mem V).tableOf y =
      if y = root then some m1.next else m1.tableOf y := by
    intro y
    show ((m1.addObj o).1.setTable root m1.next).tableOf y = _
    rw [Mem.tableOf_setTable, Mem.tableOf_addObj]
  have hold : ∀ h' o', m1.obj? h' = some o' → o'.node ≠ root := by
    intro h' o' ho' hn'
    obtain ⟨-, -, -, -, h4⟩ := h1.obj h' o' ho'
    rw [hn', hr] at h4; cases h4
  have hne : ∀ h' o', m1.obj? h' = some o' → h' ≠ m1.next := by
    intro h' o' ho' he; rw [he, h1.fresh m1.next (Nat.le_refl _)] at ho'; cases ho'
  refine ⟨h1.s, ?_, ?_, ⟨?_, o, ?_, hoc, hon⟩, ?_, ?_, ?_⟩
  · intro h' hh'
    have : h' ≠ m1.next := by simp at hh'; omega
    rw [hobj]; simp only [this, ↓reduceIte]
    exact h1.fresh h' (by simp at hh'; omega)
  · exact nodup_addObj_keys m1 o h1.nodup h1.fresh
  · rw [htab]; simp
  · rw [hobj]; simp
  · intro y h' ht
    rw [htab] at ht
    by_cases hy : y = root
    · simp only [hy, ↓reduceIte, Option.some.injEq] at ht
      subst ht
      exact ⟨o, by rw [hobj]; simp, by rw [hon, hy]⟩
    · simp only [hy, ↓reduceIte] at ht
      obtain ⟨-, o', ho', hn'⟩ := h1.tbl y h' ht
      exact ⟨o', by rw [hobj]; simp only [hne h' o' ho', ↓reduceIte]; exact ho', hn'⟩
  · intro h' o' ho'
    rw [hobj] at ho'
    by_cases hh : h' = m1.next
    · simp only [hh, ↓reduceIte, Option.some.injEq] at ho'
      subst ho'; subst hh
      exact ⟨by rw [htab, hon]; simp, hoc, hsrc⟩
    · simp only [hh, ↓reduceIte] at ho'
      obtain ⟨-, -, -, -, h4⟩ := h1.obj h' o' ho'
      refine ⟨by rw [htab]; simp only [hold h' o' ho', ↓reduceIte]; exact h4, h1.src ho'⟩
  · intro x w hw hd hne'
    by_cases hx : x = root
    · subst hx
      rw [(Mem.canonicalOf_eq_some _ root m1.next).mpr ⟨by rw [htab]; simp, o, by rw [hobj]; simp, hoc⟩]
      simp
    · obtain ⟨h0, ht0⟩ := Option.ne_none_iff_exists'.mp
        (h1.cover x (mem_sectionNodes hw hd) w hw hne')
      obtain ⟨-, o0, ho0, -⟩ := h1.tbl x h0 ht0
      obtain ⟨hc0, -⟩ := h1.src ho0
      rw [(Mem.canonicalOf_eq_some _ x h0).mpr ⟨by rw [htab]; simp only [hx, ↓reduceIte]; exact ht0,
        o0, by rw [hobj]; simp only [hne h0 o0 ho0, ↓reduceIte]; exact ho0, hc0⟩]
      simp

/-- Step 2 keeps the root's canonical object from step 1. -/
theorem base2_keep {m1 : Mem V} (h1 : Sec1 sp db.S (sectionNodes db.S (lastSp db.S)) m1) {h : Nat}
    (hc : m1.canonicalOf root = some h) : Base2 sp db { m1 with root := h } := by
  obtain ⟨ht, o, ho, hoc⟩ := (m1.canonicalOf_eq_some root h).mp hc
  obtain ⟨-, o', ho', hn'⟩ := h1.tbl root h ht
  rw [ho, Option.some.injEq] at ho'
  subst ho'
  refine ⟨h1.s, h1.fresh, h1.nodup, ⟨ht, o, ho, hoc, hn'⟩, fun y h' ht' => (h1.tbl y h' ht').2, ?_, ?_⟩
  · intro h' o' ho'
    obtain ⟨-, -, -, -, h4⟩ := h1.obj h' o' ho'
    exact ⟨h4, h1.src ho'⟩
  · intro x w hw hd hne
    obtain ⟨h0, ht0⟩ := Option.ne_none_iff_exists'.mp (h1.cover x (mem_sectionNodes hw hd) w hw hne)
    show m1.canonicalOf x ≠ none
    rw [h1.canonicalOf ht0]; simp

/-- With a written root, top(k) names the root's latest version. -/
theorem Inv.topVersion_nv (hinv : Inv sp db k) (hv : sp.virt = false) :
    ∃ u, db.S.lv root = some u ∧
      topVersion db.S (lastSp db.S) true = follow db.S (lastSp db.S) true root (some u.recNo) := by
  obtain ⟨u, hu⟩ := hinv.lv_root hv
  refine ⟨u, hu, ?_⟩
  have htop : db.S.getLast?.bind (·.top) = some (root, u.recNo) := by
    cases hl : db.S.getLast? with
    | none =>
      have : db.S = [] := List.getLast?_eq_none_iff.mp hl
      have := hinv.len; simp_all
    | some R =>
      simp only [Option.bind_some]
      rw [hinv.top R hl]
      simp [topOf, hv, hu]
  unfold topVersion
  rw [htop]

theorem lazyRoot_virt (S : Stream V T) (m1 : Mem V) (hv : sp.virt = true) :
    lazyRoot sp S m1 =
      { ((m1.addObj (vRootObj sp S)).1.setTable root m1.next) with root := m1.next } := by
  unfold lazyRoot
  simp only [hv, ↓reduceIte]
  rfl

/-- After steps 1 and 2. -/
theorem Inv.base2 (hinv : Inv sp db k) : Base2 sp db (lazyRoot sp db.S (lazySec sp db.S)) := by
  have h1 := sec1_lazySec (sp := sp) (S := db.S)
  have hall : ∀ y, (lazySec sp db.S).tableOf y = none ∨ (lazySec sp db.S).canonicalOf y ≠ none := by
    intro y
    cases ht : (lazySec sp db.S).tableOf y with
    | none => exact Or.inl rfl
    | some h => right; rw [h1.canonicalOf ht]; simp
  cases hv : sp.virt
  · -- A written root.
    cases hc : (lazySec sp db.S).canonicalOf root with
    | some h =>
      have : lazyRoot sp db.S (lazySec sp db.S) = { lazySec sp db.S with root := h } := by
        unfold lazyRoot; simp only [hv, Bool.false_eq_true, ↓reduceIte, hc]
      rw [this]
      exact base2_keep h1 hc
    | none =>
      have hr : (lazySec sp db.S).tableOf root = none := by
        rcases hall root with h | h
        · exact h
        · exact absurd hc h
      obtain ⟨u, hu, htv⟩ := hinv.topVersion_nv hv
      have hu' := hinv.lv_at hu
      obtain ⟨hun, -, -⟩ := hinv.version_node hu'
      cases hnw : newest db.S (lastSp db.S) root with
      | some w =>
        rw [follow_newest hnw] at htv
        have : lazyRoot sp db.S (lazySec sp db.S) =
            { (((lazySec sp db.S).addObj (canonOfVersion sp db.S (lastSp db.S) w)).1.setTable root
              (lazySec sp db.S).next) with root := (lazySec sp db.S).next } := by
          unfold lazyRoot; simp only [hv, Bool.false_eq_true, ↓reduceIte, hc, htv]; rfl
        rw [this]
        obtain ⟨r, hrs, hwr⟩ := newest_some hnw
        have hwn := newest_node hnw
        obtain ⟨f1, -, -, -, f5, -⟩ := canonOfVersion_fields sp db.S (lastSp db.S) w
        exact base2_add h1 hr (by rw [f1, hwn]) f5
          (Or.inl ⟨w, r, by rw [f1, hwn]; exact hwr, hrs, rfl, fun h => absurd (by rw [f1, hwn]) h⟩)
      | none =>
        rw [follow_old hnw, hu'] at htv
        have : lazyRoot sp db.S (lazySec sp db.S) =
            { (((lazySec sp db.S).addObj (canonOfVersion sp db.S (lastSp db.S) u)).1.setTable root
              (lazySec sp db.S).next) with root := (lazySec sp db.S).next } := by
          unfold lazyRoot; simp only [hv, Bool.false_eq_true, ↓reduceIte, hc, htv]; rfl
        rw [this]
        have hus : u.recNo < lastSp db.S := by
          apply Nat.lt_of_not_le
          intro hle
          have := (newest_eq_none_iff db.S (lastSp db.S) root).mp hnw u.recNo hle
          rw [hu'] at this; cases this
        obtain ⟨f1, -, -, -, f5, -⟩ := canonOfVersion_fields sp db.S (lastSp db.S) u
        exact base2_add h1 hr (by rw [f1, hun]) f5 (Or.inr (Or.inr ⟨hv, u, hu, hus, hnw, rfl⟩))
  · -- A virtual root.
    rw [lazyRoot_virt db.S _ hv]
    have hvi := hinv.vr hv
    have hr : (lazySec sp db.S).tableOf root = none := by
      cases ht : (lazySec sp db.S).tableOf root with
      | none => rfl
      | some h =>
        exfalso
        obtain ⟨-, o, ho, hon⟩ := h1.tbl root h ht
        obtain ⟨w, hn, -, -, -⟩ := h1.obj h o ho
        rw [hon] at hn
        obtain ⟨r, -, hwr⟩ := newest_some hn
        obtain ⟨R, hR, hwR, hwy⟩ := versionAt_spec hwr
        exact hvi.rootNV r R hR w hwR hwy
    have hon : (vRootObj sp db.S).node = root := rfl
    exact base2_add h1 hr hon rfl (Or.inr (Or.inl ⟨hv, rfl⟩))

end Root

/-! ### The canonical objects after the memory slots -/

section Link

variable {sp : Spec V T} {db dbK : DB V T} {k : Nat} {m2 : Mem V}

/-- A stream slot of a canonical object, after the memory slots: the same, or
a memory slot to the table's canonical object of its node. -/
theorem Base2.link_slot (hb : Base2 sp db m2) {o : Obj V} (hc : o.canonical = true) {y : NodeId}
    {r : Option Nat} (hsl : o.slot? y = some (Slot.stream r)) :
    ∃ sl, (linkObj m2 o).slot? y = some sl ∧
      (sl = Slot.stream r ∨ ∃ h0 o0, m2.linkCanonical.obj? h0 = some o0 ∧ o0.node = y ∧
        o0.canonical = true ∧ m2.linkCanonical.tableOf y = some h0 ∧ sl = Slot.mem h0) := by
  rw [linkObj_slot? m2 hc, hsl, Option.map_some]
  refine ⟨_, rfl, ?_⟩
  rcases linkQ_cases m2 y (Slot.stream r) with h | ⟨h0, o0, ht0, ho0, hc0, he⟩
  · exact Or.inl h
  · right
    obtain ⟨o', ho', hn'⟩ := hb.tbl y h0 ht0
    rw [ho0, Option.some.injEq] at ho'
    subst ho'
    refine ⟨h0, linkObj m2 o0, by rw [linkCanonical_obj?, ho0]; rfl, ?_, ?_, ?_, he⟩
    · rw [(linkObj_fields m2 o0).1, hn']
    · rw [(linkObj_fields m2 o0).2.2.2.2.1, hc0]
    · rw [linkCanonical_tableOf]; exact ht0

theorem Base2.link_good (hb : Base2 sp db m2) {o : Obj V} (hc : o.canonical = true) {y : NodeId}
    {r : Option Nat} (hsl : o.slot? y = some (Slot.stream r)) (K : Nat) {t : Time}
    (hg : m2.canonicalOf y ≠ none ∨ ∃ r' w, ruleRRef db.S (lastSp db.S) y r = some r' ∧
      db.S.versionAt r' y = some w ∧ good sp db.S db.P t w = true) :
    ∃ sl, (linkObj m2 o).slot? y = some sl ∧ SlotGood sp db m2.linkCanonical K t y sl := by
  obtain ⟨sl, hsl', hcases⟩ := hb.link_slot hc hsl
  refine ⟨sl, hsl', ?_⟩
  rcases hcases with rfl | ⟨h0, o0, ho0, hn0, hc0, -, rfl⟩
  · simp only [SlotGood, linkCanonical_canonicalOf]
    exact hg
  · exact ⟨o0, ho0, hn0, Or.inl hc0⟩

theorem Base2.link_fresh (hb : Base2 sp db m2) {o : Obj V} (hc : o.canonical = true) {y : NodeId}
    {r : Option Nat} (hsl : o.slot? y = some (Slot.stream r))
    (hf : m2.canonicalOf y ≠ none ∨
      (ruleRRef db.S (lastSp db.S) y r = (db.S.lv y).map (·.recNo) ∧ (db.S.lv y).isSome)) :
    ∃ sl, (linkObj m2 o).slot? y = some sl ∧ SlotFresh db m2.linkCanonical y sl := by
  obtain ⟨sl, hsl', hcases⟩ := hb.link_slot hc hsl
  refine ⟨sl, hsl', ?_⟩
  rcases hcases with rfl | ⟨h0, o0, ho0, -, hc0, -, rfl⟩
  · simp only [SlotFresh, linkCanonical_canonicalOf]
    rcases hf with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr h)
  · exact ⟨o0, ho0, Or.inl hc0⟩

/-- A stream slot that names the latest version of a node y reachable at t: good
for t, and fresh (MG, when y has no canonical object). -/
theorem fresh_slot (hcov : Cover db (lastSp db.S) m2.linkCanonical)
    (hk : KCtx sp db dbK (lastSp db.S)) (hctx : PCtx sp db k) {y : NodeId} {t : Time}
    (ht : t ≤ lastSp db.S) (hry : reachable sp db.P t y = true) :
    (m2.canonicalOf y ≠ none ∨ ∃ r' w, ruleRRef db.S (lastSp db.S) y ((db.S.lv y).map (·.recNo)) =
      some r' ∧ db.S.versionAt r' y = some w ∧ good sp db.S db.P t w = true) ∧
    (m2.canonicalOf y ≠ none ∨ (ruleRRef db.S (lastSp db.S) y ((db.S.lv y).map (·.recNo)) =
      (db.S.lv y).map (·.recNo) ∧ (db.S.lv y).isSome)) := by
  by_cases hc : m2.canonicalOf y = none
  · have hc3 : m2.linkCanonical.canonicalOf y = none := by rw [linkCanonical_canonicalOf]; exact hc
    obtain ⟨v, hv, hg⟩ := hcov.mg hk hctx hc3 ht hry
    rw [ruleR_lv, hv]
    exact ⟨Or.inr ⟨v.recNo, v, rfl, hctx.inv.lv_at hv, hg⟩, Or.inr ⟨rfl, rfl⟩⟩
  · exact ⟨Or.inl hc, Or.inl hc⟩

/-- A canonical object of the memory after steps 1 and 2 meets `CanonOK` after
the memory slots, if its slots are good and fresh before them. -/
theorem Base2.canon_of (hb : Base2 sp db m2) {h : Nat} {o : Obj V} (ho : m2.obj? h = some o)
    (hc : o.canonical = true) {n : Node V} (hn : db.P.get? o.node = some n)
    (hhist : o.hist = n.hist.upTo (lastSp db.S)) (hlev : o.level = n.level)
    (hdat : o.isData = n.isData) (hpos : ∀ p, o.pos = some p → (db.S.versionAt p o.node).isSome)
    (hgood : ∀ t ≤ lastSp db.S, reachable sp db.P t o.node = true → ∀ y ∈ sp.live (o.hist.upTo t),
      ∃ r, o.slot? y = some (Slot.stream r) ∧ (m2.canonicalOf y ≠ none ∨ ∃ r' w,
        ruleRRef db.S (lastSp db.S) y r = some r' ∧ db.S.versionAt r' y = some w ∧
        good sp db.S db.P t w = true))
    (hfresh : reachable sp db.P (lastSp db.S) o.node = true → ∀ y ∈ sp.live o.hist,
      ∃ r, o.slot? y = some (Slot.stream r) ∧ (m2.canonicalOf y ≠ none ∨
        (ruleRRef db.S (lastSp db.S) y r = (db.S.lv y).map (·.recNo) ∧ (db.S.lv y).isSome))) :
    CanonOK sp db m2.linkCanonical (lastSp db.S) h (linkObj m2 o) := by
  obtain ⟨l1, l2, l3, l4, -, l6⟩ := linkObj_fields m2 o
  refine ⟨?_, ⟨n, by rw [l1]; exact hn, by rw [l4]; exact hhist, by rw [l2]; exact hlev,
    by rw [l3]; exact hdat⟩, ?_, ?_, ?_⟩
  · rw [linkCanonical_tableOf, l1]; exact (hb.obj h o ho).1
  · intro p hp; rw [l6] at hp; rw [l1]; exact hpos p hp
  · intro t ht hr y hy
    rw [l1] at hr; rw [l4] at hy
    obtain ⟨r, hsl, hg⟩ := hgood t ht hr y hy
    exact hb.link_good hc hsl _ hg
  · intro hr y hy
    rw [l1] at hr; rw [l4] at hy
    obtain ⟨r, hsl, hf⟩ := hfresh hr y hy
    exact hb.link_fresh hc hsl hf

/-- An object of the memory after steps 1 and 2 whose slots name the latest
versions of the live children of its node. -/
theorem Base2.canon_of_lv (hb : Base2 sp db m2) (hcov : Cover db (lastSp db.S) m2.linkCanonical)
    (hk : KCtx sp db dbK (lastSp db.S)) (hctx : PCtx sp db k) {h : Nat} {o : Obj V}
    (ho : m2.obj? h = some o) (hc : o.canonical = true) {n : Node V} (hn : db.P.get? o.node = some n)
    (hhist : o.hist = n.hist.upTo (lastSp db.S)) (hlev : o.level = n.level)
    (hdat : o.isData = n.isData) (hpos : ∀ p, o.pos = some p → (db.S.versionAt p o.node).isSome)
    (hsl : ∀ t ≤ lastSp db.S, ∀ y ∈ sp.live (o.hist.upTo t),
      o.slot? y = some (Slot.stream ((db.S.lv y).map (·.recNo)))) :
    CanonOK sp db m2.linkCanonical (lastSp db.S) h (linkObj m2 o) := by
  have hls := hctx.ls
  -- A live child at t of a node reachable at t is reachable at t.
  have hreach : ∀ t ≤ lastSp db.S, reachable sp db.P t o.node = true → ∀ y ∈ sp.live (o.hist.upTo t),
      reachable sp db.P t y = true := by
    intro t ht hr y hy
    have hy' : y ∈ sp.live (n.hist.upTo t) := by rw [hhist, upTo_upTo _ ht] at hy; exact hy
    obtain ⟨e, he, hye⟩ := hls _ _ hy'
    obtain ⟨ny, hny, hlt⟩ := hctx.inv.ptrs o.node n hn e (mem_upTo.mp he).1 y hye
    rw [reachable_iff] at hr ⊢
    exact Reach.child hr hn hy' hny hlt
  apply hb.canon_of ho hc hn hhist hlev hdat hpos
  · intro t ht hr y hy
    exact ⟨_, hsl t ht y hy, (fresh_slot hcov hk hctx ht (hreach t ht hr y hy)).1⟩
  · intro hr y hy
    have hy' : y ∈ sp.live (o.hist.upTo (lastSp db.S)) := by
      rw [hhist, upTo_upTo _ (Nat.le_refl _)]; rw [hhist] at hy; exact hy
    exact ⟨_, hsl _ (Nat.le_refl _) y hy',
      (fresh_slot hcov hk hctx (Nat.le_refl _) (hreach _ (Nat.le_refl _) hr y hy')).2⟩

end Link

/-! ### The three kinds of objects -/

section Kinds

variable {sp : Spec V T} {db dbK : DB V T} {k : Nat} {m2 : Mem V}

theorem pointees_cutHist {w : Version V} {cut : Option Nat} {y : NodeId}
    (h : y ∈ pointees sp (cutHist w cut)) : y ∈ pointees sp w.hist := by
  unfold cutHist at h
  cases cut with
  | none => exact h
  | some s =>
    obtain ⟨e, he, hy⟩ := (mem_pointees sp _ y).mp h
    exact (mem_pointees sp _ y).mpr ⟨e, (mem_upTo.mp he).1, hy⟩

/-- The canonical object of a node, from its version of the section. -/
theorem Base2.canon_sec (hb : Base2 sp db m2) (hcov : Cover db (lastSp db.S) m2.linkCanonical)
    (hk : KCtx sp db dbK (lastSp db.S)) (hctx : PCtx sp db k) {h : Nat} {o : Obj V}
    (ho : m2.obj? h = some o) {w : Version V} {r : Nat} (hw : db.S.versionAt r o.node = some w)
    (hr : lastSp db.S ≤ r) (hoe : o = canonOfVersion sp db.S (lastSp db.S) w)
    (hne : o.node ≠ SIS.root → w.hist.upTo (lastSp db.S) ≠ []) :
    CanonOK sp db m2.linkCanonical (lastSp db.S) h (linkObj m2 o) := by
  have hinv := hctx.inv
  have hls := hctx.ls
  obtain ⟨-, hrec, n, hn, hwh, hwl, hwd⟩ := hinv.version_node hw
  obtain ⟨-, f2, f3, f4, f5, f6⟩ := canonOfVersion_fields sp db.S (lastSp db.S) w
  have hc : o.canonical = true := by rw [hoe]; exact f5
  have hborn : ∃ t ≤ lastSp db.S, reachable sp db.P t o.node = true := by
    by_cases hxr : o.node = SIS.root
    · obtain ⟨n0, h0⟩ := Option.isSome_iff_exists.mp hinv.rootIn
      exact ⟨0, Nat.zero_le _, by rw [hxr]; exact reachable_root h0 0⟩
    · obtain ⟨e, he⟩ := List.exists_mem_of_ne_nil _ (hne hxr)
      obtain ⟨he1, he2⟩ := mem_upTo.mp he
      have he' : e ∈ n.hist := by rw [hwh] at he1; exact (mem_upTo.mp he1).1
      exact ⟨e.time, he2, hinv.er o.node n hn e he'⟩
  have hhist : o.hist = n.hist.upTo (lastSp db.S) := by
    rw [hoe, f4]
    unfold cutHist
    cases hkl : isKeyLevel sp w.isData w.level
    · -- Not cut back: a data node or a root child, with its entries up to s.
      simp only [Bool.false_eq_true, ↓reduceIte]
      have hkl' : isKeyLevel sp n.isData n.level = false := by rw [← hwd, ← hwl]; exact hkl
      have hdr : n.isData = true ∨ o.node ≠ SIS.root := by
        cases hvv : sp.virt
        · left
          simpa [isKeyLevel, hvv] using hkl'
        · right
          intro hxr
          obtain ⟨R, hR, hwR, hwy⟩ := versionAt_spec hw
          exact (hinv.vr hvv).rootNV r R hR w hwR (by rw [hwy, hxr])
      have hfix := hk.fixedLe o.node n hn hkl' hdr hborn
      rw [hwh, upTo_of_forall _ _ (fun e he => Nat.le_trans (hfix e he) hr), upTo_of_forall _ _ hfix]
    · simp only [↓reduceIte]
      rw [hwh, upTo_upTo _ hr]
  apply hb.canon_of_lv hcov hk hctx ho hc hn hhist (by rw [hoe, f2, hwl]) (by rw [hoe, f3, hwd])
  · intro p hp
    rw [hoe, f6, Option.some.injEq] at hp
    rw [← hp, hrec, hw]; rfl
  · intro t _ y hy
    have hyp : y ∈ pointees sp o.hist := mem_pointees_of_live hls hy
    rw [hoe, f4] at hyp
    rw [hoe, canonOfVersion_slot?]
    simp only [hyp, ↓reduceIte]
    rw [hinv.ruleR_section hw hr (pointees_cutHist hyp)]

/-- The root children read at startup, with a virtual root (as in
`Inv.readAt_spec_virt`). -/
theorem Inv.topsRead_spec (hinv : Inv sp db k) (hv : sp.virt = true) :
    (∀ w ∈ topsRead sp db.S (lastSp db.S) true, TopRead sp db w) ∧
    (∀ y m c, TopAt sp db.P y m c → c ≤ lastSp db.S →
      ∃ w ∈ topsRead sp db.S (lastSp db.S) true, w.node = y) := by
  have hvi := hinv.vr hv
  obtain ⟨n0, h0⟩ := Option.isSome_iff_exists.mp hinv.rootIn
  rcases hinv.topVersion_virt hv h0 with ⟨hnil, htv⟩ | ⟨zs, ms, cs, us, hzt, hcs, hmax, hus, htv⟩
  · have : topsRead sp db.S (lastSp db.S) true = [] := by unfold topsRead; rw [htv]
    rw [this]
    refine ⟨by simp, ?_⟩
    intro y m c hyt hc
    have : (⟨c, sp.rootVal y⟩ : Entry V) ∈ n0.hist.upTo (lastSp db.S) :=
      mem_upTo.mpr ⟨hvi.topEntry y m c hyt n0 h0, hc⟩
    rw [hnil] at this; simp at this
  · obtain ⟨husn, -⟩ := hinv.version_node (hinv.lv_at hus)
    have hread : TopRead sp db us := ⟨ms, cs, by rw [husn]; exact hzt, hcs, by rw [husn]; exact hus⟩
    have htr : topsRead sp db.S (lastSp db.S) true = readTops sp db.S (lastSp db.S) true us := by
      unfold topsRead; rw [htv]
    rw [htr]
    refine ⟨hinv.readTops_read hv (us.level + 1) us (by omega) hread, ?_⟩
    intro y m c hyt hc
    rcases Nat.lt_or_ge c cs with hlt | hge
    · have hy := hvi.closed zs ms cs y m c hzt hyt hlt
      rw [← husn] at hzt hy
      exact hinv.readTops_all hv (ms.level + 1) us ms cs (by omega) hzt hcs (by rw [husn]; exact hus) y hy
    · have hc' : c = cs := Nat.le_antisymm (hmax y m c hyt hc) hge
      subst hc'
      have := hinv.topAt_unique hv hyt hzt
      subst this
      exact ⟨us, by rw [readTops_eq]; exact List.mem_cons_self, husn⟩

/-- The virtual root's canonical object. -/
theorem Base2.canon_vroot (hb : Base2 sp db m2) (hcov : Cover db (lastSp db.S) m2.linkCanonical)
    (hk : KCtx sp db dbK (lastSp db.S)) (hctx : PCtx sp db k) (hv : sp.virt = true) {h : Nat}
    (ho : m2.obj? h = some (vRootObj sp db.S)) :
    CanonOK sp db m2.linkCanonical (lastSp db.S) h (linkObj m2 (vRootObj sp db.S)) := by
  have hinv := hctx.inv
  have hls := hctx.ls
  have hvi := hinv.vr hv
  obtain ⟨n0, h0⟩ := Option.isSome_iff_exists.mp hinv.rootIn
  obtain ⟨hidx0, hlev0⟩ := hvi.rootIdx n0 h0
  obtain ⟨hws1, hws2⟩ := hinv.topsRead_spec hv
  have hvh := hinv.rootHist_virt hv h0 _ hws1 hws2
  have hhist : (vRootObj sp db.S).hist = n0.hist.upTo (lastSp db.S) := hvh
  have hcut : ∀ cut : Option Nat, (cut = some (lastSp db.S) ∨ cut = none) →
      cutHist (rootVersion sp (lastSp db.S) (topsRead sp db.S (lastSp db.S) true)) cut =
        n0.hist.upTo (lastSp db.S) := by
    intro cut hcut
    rcases hcut with rfl | rfl
    · simp only [cutHist, hvh, upTo_upTo _ (Nat.le_refl _)]
    · exact hvh
  apply hb.canon_of_lv hcov hk hctx ho rfl h0 hhist (by rw [hlev0]; rfl) (by rw [hidx0]; rfl)
    (fun p hp => by cases hp)
  intro t ht y hy
  rw [hhist, upTo_upTo _ ht] at hy
  obtain ⟨e, he, hye⟩ := hls _ _ hy
  obtain ⟨he1, he2⟩ := mem_upTo.mp he
  obtain ⟨z, m, hzt, hval⟩ := hvi.rootEntry n0 h0 e he1
  have hyz : y = z := by rw [hval, hvi.rootPtrs] at hye; simpa using hye
  subst hyz
  obtain ⟨u, hu⟩ := hinv.topAt_lv hzt (by omega)
  have href : (rootVersion sp (lastSp db.S) (topsRead sp db.S (lastSp db.S) true)).ref? y =
      some u.recNo := by
    unfold Version.ref?
    simp only [rootVersion]
    apply lookup_refs
    · exact hws2 y m e.time hzt (by omega)
    · intro w hw hwy
      obtain ⟨-, -, -, -, hlvw⟩ := hws1 w hw
      rw [hwy, hu] at hlvw
      exact (Option.some.inj hlvw).symm
  have hyp : y ∈ pointees sp (n0.hist.upTo (lastSp db.S)) :=
    (mem_pointees sp _ y).mpr ⟨e, mem_upTo.mpr ⟨he1, by omega⟩, hye⟩
  show (canonOfVersion sp db.S (lastSp db.S) _).slot? y = _
  rw [canonOfVersion_slot?, hcut _ (by split <;> simp), href]
  simp only [hyp, ↓reduceIte]
  have := ruleR_lv db.S (lastSp db.S) y
  rw [hu] at this
  rw [hu]
  exact congrArg (fun r => some (Slot.stream r)) this

/-- With a written root: the root's canonical object from its latest version,
written before s. -/
theorem Base2.canon_oldroot (hb : Base2 sp db m2) (hk : KCtx sp db dbK (lastSp db.S))
    (hctx : PCtx sp db k) (hv : sp.virt = false) {u : Version V} (hu : db.S.lv SIS.root = some u)
    (hus : u.recNo < lastSp db.S) (hnw : newest db.S (lastSp db.S) SIS.root = none) {h : Nat}
    (ho : m2.obj? h = some (canonOfVersion sp db.S (lastSp db.S) u)) :
    CanonOK sp db m2.linkCanonical (lastSp db.S) h (linkObj m2 (canonOfVersion sp db.S (lastSp db.S) u)) := by
  have hinv := hctx.inv
  have hls := hctx.ls
  have hu' := hinv.lv_at hu
  obtain ⟨hun, -, n, hn, huh, hul, hud⟩ := hinv.version_node hu'
  obtain ⟨f1, f2, f3, f4, f5, f6⟩ := canonOfVersion_fields sp db.S (lastSp db.S) u
  have hle : ∀ e ∈ u.hist, e.time ≤ u.recNo := by
    intro e he; rw [huh] at he; exact (mem_upTo.mp he).2
  have hus' : u.hist.upTo (lastSp db.S) = u.hist :=
    upTo_of_forall _ _ (fun e he => by have := hle e he; omega)
  have hcut : (canonOfVersion sp db.S (lastSp db.S) u).hist = u.hist := by
    rw [f4]
    cases isKeyLevel sp u.isData u.level
    · simp only [Bool.false_eq_true, ↓reduceIte, cutHist]
    · simp only [↓reduceIte, cutHist]; exact hus'
  have hnode : (canonOfVersion sp db.S (lastSp db.S) u).node = SIS.root := by rw [f1, hun]
  have hr : ∀ t, reachable sp db.P t SIS.root = true := by
    obtain ⟨n0, h0⟩ := Option.isSome_iff_exists.mp hinv.rootIn
    exact reachable_root h0
  have hg : ∀ t ≤ lastSp db.S, good sp db.S db.P t u = true :=
    fun t ht => hinv.lout hls hu (by omega) ht (hr t)
  have hhist : (canonOfVersion sp db.S (lastSp db.S) u).hist = n.hist.upTo (lastSp db.S) := by
    rw [hcut]
    obtain ⟨⟨n', hn', hc⟩, -⟩ := (good_iff _ _ _ _ _).mp (hg _ (Nat.le_refl _))
    rw [hun, hn, Option.some.injEq] at hn'
    subst hn'
    rw [← hc, hus']
  have hslot : ∀ y ∈ pointees sp u.hist, (canonOfVersion sp db.S (lastSp db.S) u).slot? y =
      some (Slot.stream (ruleRRef db.S (lastSp db.S) y (u.ref? y))) := by
    intro y hy
    rw [canonOfVersion_slot?, ← f4, hcut]
    simp only [hy, ↓reduceIte]
  apply hb.canon_of ho f5 (by rw [hnode]; exact hn) hhist (by rw [f2, hul]) (by rw [f3, hud])
  · intro p hp
    rw [f6, Option.some.injEq] at hp
    rw [← hp, hnode, hu']; rfl
  · intro t ht _ y hy
    rw [hcut] at hy
    have hyp : y ∈ pointees sp u.hist := mem_pointees_of_live hls hy
    refine ⟨_, hslot y hyp, Or.inr ?_⟩
    obtain ⟨-, hch⟩ := (good_iff _ _ _ _ _).mp (hg t ht)
    obtain ⟨r1, w1, hr1, hw1, hl1, hg1⟩ := hch y hy
    obtain ⟨r2, u2, h2, hv2, hle2⟩ := hinv.ruleR_ge hw1 (lastSp db.S)
    obtain ⟨r3, u3, h3, hv3, hle3⟩ := hinv.ruleR_ge hv2 (lastSp db.S)
    rw [hr1, h2, h3]
    exact ⟨r3, u3, rfl, hv3, hinv.newer hls (w1.level + 1) r1 r3 y w1 u3 (by omega) hw1 hv3
      (by omega) t hg1⟩
  · intro _ y hy
    rw [hcut] at hy
    have hyp : y ∈ pointees sp u.hist := mem_pointees_of_live (t := u.recNo) hls (by
      rw [upTo_of_forall _ _ hle]; exact hy)
    refine ⟨_, hslot y hyp, Or.inr ?_⟩
    have hDK : inD dbK.D SIS.root = false := by
      cases hD : inD dbK.D SIS.root
      · rfl
      · exfalso
        obtain ⟨d, hd⟩ := (inD_iff _ _).mp hD
        by_cases hds : d ≤ lastSp db.S
        · obtain ⟨r, w, hrs, hw⟩ := hk.dLater SIS.root d hd hds
          have := (newest_eq_none_iff db.S (lastSp db.S) SIS.root).mp hnw r (by omega)
          rw [hw] at this; cases this
        · obtain ⟨-, -, -, hdK⟩ := hk.dSec SIS.root d hd (by omega)
          omega
    have hvK : ∀ r w, lastSp db.S < r → db.S.versionAt r SIS.root = some w → False := by
      intro r w hr' hw
      have := (newest_eq_none_iff db.S (lastSp db.S) SIS.root).mp hnw r (by omega)
      rw [hw] at this; cases this
    obtain ⟨h1, h2⟩ := hk.fresh_ref hctx (Nat.le_refl _) hDK (by simp [written, hv]) (hr _) hu hvK hy
    rw [h1, ruleR_lv]
    exact ⟨rfl, h2⟩

end Kinds

/-! ### The memory before the rerun -/

section Assemble

variable {sp : Spec V T} {db dbK : DB V T} {k : Nat}

theorem Base2.stream_slots {m2 : Mem V} (hb : Base2 sp db m2) {h : Nat} {o : Obj V}
    (ho : m2.obj? h = some o) {y : NodeId} {sl : Slot} (hsl : o.slot? y = some sl) :
    ∃ r, sl = Slot.stream r := by
  obtain ⟨-, -, hsrc⟩ := hb.obj h o ho
  rcases hsrc with ⟨w, r, -, -, hoe, -⟩ | ⟨-, hoe⟩ | ⟨-, u, -, -, -, hoe⟩
  · rw [hoe] at hsl; exact canonOfVersion_stream sp _ _ w hsl
  · rw [hoe] at hsl; exact canonOfVersion_stream sp _ _ _ hsl
  · rw [hoe] at hsl; exact canonOfVersion_stream sp _ _ u hsl

/-- The memory before the rerun meets the invariant at the startup pos s. -/
theorem PCtx.base_ok (hctx : PCtx sp db k) (hk : KCtx sp db dbK (lastSp db.S)) :
    MemInv sp db (lastSp db.S) (lazyBase sp db.S) := by
  have hinv := hctx.inv
  have hb := hinv.base2 (sp := sp)
  unfold lazyBase
  generalize lazyRoot sp db.S (lazySec sp db.S) = m2 at hb
  obtain ⟨n0, h0⟩ := Option.isSome_iff_exists.mp hinv.rootIn
  have hcov : Cover db (lastSp db.S) m2.linkCanonical := by
    refine ⟨Nat.le_refl _, ?_, fun d R x h1 h2 => absurd h2 (by omega), ?_,
      fun x n e _ _ h1 h2 => absurd h2 (by omega)⟩
    · rw [linkCanonical_canonicalOf]
      obtain ⟨ht, o, ho, hc, -⟩ := hb.root
      rw [(m2.canonicalOf_eq_some SIS.root m2.root).mpr ⟨ht, o, ho, hc⟩]; simp
    · intro x w hw hd hne; rw [linkCanonical_canonicalOf]; exact hb.cover x w hw hd hne
  have hlink : ∀ h o, m2.linkCanonical.obj? h = some o → ∃ o2, m2.obj? h = some o2 ∧ o = linkObj m2 o2 := by
    intro h o ho
    rw [linkCanonical_obj?] at ho
    obtain ⟨o2, ho2, he⟩ := Option.map_eq_some_iff.mp ho
    exact ⟨o2, ho2, he.symm⟩
  refine ⟨by simp [hb.s], Nat.le_refl _, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hcov.coverGd, hcov.coverSec,
    hcov.coverNew⟩
  · -- No objects past the next handle.
    intro h hh; rw [linkCanonical_obj?, hb.fresh h (by simpa using hh)]; rfl
  · rw [linkCanonical_keys]; exact hb.nodup
  · -- The root.
    obtain ⟨ht, o, ho, hc, hn⟩ := hb.root
    refine ⟨by rw [linkCanonical_tableOf]; exact ht, linkObj m2 o,
      by rw [linkCanonical_obj?, linkCanonical_root, ho]; rfl, ?_, ?_⟩
    · rw [(linkObj_fields m2 o).2.2.2.2.1]; exact hc
    · rw [(linkObj_fields m2 o).1]; exact hn
  · -- The node table.
    intro y h ht
    rw [linkCanonical_tableOf] at ht
    obtain ⟨o, ho, hn⟩ := hb.tbl y h ht
    exact ⟨linkObj m2 o, by rw [linkCanonical_obj?, ho]; rfl, by rw [(linkObj_fields m2 o).1]; exact hn⟩
  · -- Every object's node is reachable by s.
    intro h o ho
    obtain ⟨o2, ho2, rfl⟩ := hlink h o ho
    rw [(linkObj_fields m2 o2).1]
    by_cases hxr : o2.node = SIS.root
    · exact ⟨0, Nat.zero_le _, by rw [hxr]; exact reachable_root h0 0⟩
    · obtain ⟨-, -, hsrc⟩ := hb.obj h o2 ho2
      rcases hsrc with ⟨w, r, hw, -, -, hne⟩ | ⟨-, hoe⟩ | ⟨-, u, hu, -, -, hoe⟩
      · obtain ⟨-, -, n, hn, hwh, -, -⟩ := hinv.version_node hw
        obtain ⟨e, he⟩ := List.exists_mem_of_ne_nil _ (hne hxr)
        obtain ⟨he1, he2⟩ := mem_upTo.mp he
        have he' : e ∈ n.hist := by rw [hwh] at he1; exact (mem_upTo.mp he1).1
        exact ⟨e.time, he2, hinv.er o2.node n hn e he'⟩
      · exact absurd (by rw [hoe]; rfl) hxr
      · exfalso; apply hxr
        rw [hoe, (canonOfVersion_fields sp _ _ u).1]
        exact (hinv.version_node (hinv.lv_at hu)).1
  · -- The canonical objects.
    intro h o ho _
    obtain ⟨o2, ho2, rfl⟩ := hlink h o ho
    obtain ⟨-, -, hsrc⟩ := hb.obj h o2 ho2
    rcases hsrc with ⟨w, r, hw, hr, hoe, hne⟩ | ⟨hv, hoe⟩ | ⟨hv, u, hu, hus, hnw, hoe⟩
    · exact hb.canon_sec hcov hk hctx ho2 hw hr hoe hne
    · subst hoe; exact hb.canon_vroot hcov hk hctx hv ho2
    · subst hoe; exact hb.canon_oldroot hk hctx hv hu hus hnw ho2
  · -- No snapshots.
    intro h o ho hc
    obtain ⟨o2, ho2, rfl⟩ := hlink h o ho
    obtain ⟨-, hc2, -⟩ := hb.obj h o2 ho2
    rw [(linkObj_fields m2 o2).2.2.2.2.1, hc2] at hc; cases hc
  · -- The memory slots: to the table's objects.
    intro h o y h' ho hsl
    obtain ⟨o2, ho2, rfl⟩ := hlink h o ho
    obtain ⟨-, hc2, -⟩ := hb.obj h o2 ho2
    rw [linkObj_slot? m2 hc2] at hsl
    obtain ⟨sl, hsl2, hq⟩ := Option.map_eq_some_iff.mp hsl
    obtain ⟨r, rfl⟩ := hb.stream_slots ho2 hsl2
    rcases linkQ_cases m2 y (Slot.stream r) with he | ⟨hh0, o0, ht0, ho0, hc0, he⟩
    · rw [he] at hq; cases hq
    · rw [he, Slot.mem.injEq] at hq
      subst hq
      obtain ⟨o', ho', hn'⟩ := hb.tbl y hh0 ht0
      exact ⟨linkObj m2 o', by rw [linkCanonical_obj?, ho']; rfl,
        by rw [(linkObj_fields m2 o').1]; exact hn', Or.inl (by rw [linkCanonical_tableOf]; exact ht0)⟩

end Assemble

end SIS
