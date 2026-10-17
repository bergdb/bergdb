/-
Proofs for stage 2 (bergdb item 001, WP E3), part 8: the change applied to the
canonical objects (`Mem.applyChange4`), the shapes of the objects after it (as
PhysApply.lean for stage 1, with `Mem.newSlot4`).
-/
import SIS.Proof.EvictRead

set_option linter.unusedSectionVars false

namespace SIS

variable {V T : Type} [DecidableEq V]

section Slots4

variable (sp : Spec V T) (P : Struct V) (j : Time)

/-- The copied slot, if there is a source (Level 4). -/
def srcSlot4 (m : Mem V) (y : NodeId) : Option Slot :=
  (m.objs.find? (srcOK4 sp P j y)).bind (fun p => p.2.slot? y)

/-- The new slot that does not depend on the object: to y's canonical object, or
copied from a source. -/
def NS4 (m : Mem V) (y : NodeId) : Option Slot :=
  ((m.canonicalOf y).map Slot.mem).or (srcSlot4 sp P j m y)

theorem newSlot4_eq (m : Mem V) (o : Obj V) (y : NodeId) :
    m.newSlot4 sp P j o y = (NS4 sp P j m y).or (o.slot? y) := by
  unfold Mem.newSlot4 NS4 srcSlot4
  cases hc : m.canonicalOf y with
  | some h => rfl
  | none =>
    simp only [Option.map_none, Option.none_or]
    cases hf : m.objs.find? (srcOK4 sp P j y) with
    | some p =>
      simp only [Option.bind_some]
      have hp := List.find?_some hf
      unfold srcOK4 at hp
      simp only [Bool.and_eq_true] at hp
      obtain ⟨sl, hsl⟩ := Option.isSome_iff_exists.mp hp.1.1.1.2
      rw [hsl]; rfl
    | none => rfl

/-- One pointer of a new entry: its slot. -/
def upd14 (m1 : Mem V) (o' : Obj V) (y : NodeId) : Obj V :=
  match m1.newSlot4 sp P j o' y with
  | some sl => o'.putSlot y sl
  | none => o'

theorem upd14_core (m1 : Mem V) (o' : Obj V) (y : NodeId) : (upd14 sp P j m1 o' y).core = o'.core := by
  unfold upd14
  split
  · obtain ⟨a, b, c, d, e, f⟩ := Obj.putSlot_fields o' y ‹_›
    unfold Obj.core; rw [a, b, c, d, e, f]
  · rfl

/-- The slot that a pointer gets: NS4, or the object's own slot. -/
def combo4 (m1 : Mem V) (o : Obj V) (y : NodeId) : Option Slot :=
  (NS4 sp P j m1 y).or (o.slot? y)

theorem upd14_slot (m1 : Mem V) (o' : Obj V) (y y' : NodeId) :
    (upd14 sp P j m1 o' y).slot? y' = if y' = y then combo4 sp P j m1 o' y else o'.slot? y' := by
  unfold upd14 combo4
  rw [newSlot4_eq]
  cases hc : (NS4 sp P j m1 y).or (o'.slot? y) with
  | none =>
    simp only
    split
    · rename_i hy; subst hy
      simp only [Option.or_eq_none_iff] at hc
      exact hc.2
    · rfl
  | some sl =>
    simp only
    rw [Obj.slot?_putSlot]

theorem combo4_idem (m1 : Mem V) (o : Obj V) (y : NodeId) (o' : Obj V)
    (h : o'.slot? y = combo4 sp P j m1 o y) : combo4 sp P j m1 o' y = combo4 sp P j m1 o y := by
  unfold combo4 at h ⊢
  rw [h]
  cases NS4 sp P j m1 y with
  | some _ => rfl
  | none => rfl

theorem foldl_upd14_slot (m1 : Mem V) (ys : List NodeId) : ∀ (o : Obj V) (y' : NodeId),
    (ys.foldl (upd14 sp P j m1) o).slot? y' = if y' ∈ ys then combo4 sp P j m1 o y' else o.slot? y' := by
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
        apply combo4_idem
        rw [upd14_slot]; simp
      · unfold combo4
        rw [upd14_slot]
        simp only [hyy, ↓reduceIte]
    · simp only [hy, ↓reduceIte, List.mem_cons, or_false]
      rw [upd14_slot]
      by_cases hyy : y' = y
      · subst hyy; simp
      · simp [hyy]

theorem foldl_upd14_core (m1 : Mem V) (ys : List NodeId) : ∀ (o : Obj V),
    (ys.foldl (upd14 sp P j m1) o).core = o.core := by
  induction ys with
  | nil => intro o; rfl
  | cons y ys ih => intro o; simp only [List.foldl_cons]; rw [ih, upd14_core]

theorem combo4_congr (m1 : Mem V) {o o' : Obj V} {y : NodeId} (h : o'.slot? y = o.slot? y) :
    combo4 sp P j m1 o' y = combo4 sp P j m1 o y := by
  unfold combo4; rw [h]

/-- One entry v of the transaction applied to the canonical object o. -/
def updObj4 (m1 : Mem V) (o : Obj V) (v : V) : Obj V :=
  (sp.ptrs v).foldl (upd14 sp P j m1) { o with hist := o.hist ++ [⟨j, v⟩] }

theorem updObj4_core (m1 : Mem V) (o : Obj V) (v : V) :
    (updObj4 sp P j m1 o v).node = o.node ∧ (updObj4 sp P j m1 o v).level = o.level ∧
    (updObj4 sp P j m1 o v).isData = o.isData ∧ (updObj4 sp P j m1 o v).hist = o.hist ++ [⟨j, v⟩] ∧
    (updObj4 sp P j m1 o v).canonical = o.canonical ∧ (updObj4 sp P j m1 o v).pos = o.pos := by
  have := foldl_upd14_core sp P j m1 (sp.ptrs v) { o with hist := o.hist ++ [⟨j, v⟩] }
  unfold updObj4
  simp only [Obj.core, Prod.mk.injEq] at this
  exact ⟨this.1, this.2.1, this.2.2.1, this.2.2.2.1, this.2.2.2.2.1, this.2.2.2.2.2⟩

theorem updObj4_slot (m1 : Mem V) (o : Obj V) (v : V) (y : NodeId) :
    (updObj4 sp P j m1 o v).slot? y = if y ∈ sp.ptrs v then combo4 sp P j m1 o y else o.slot? y := by
  unfold updObj4
  rw [foldl_upd14_slot]
  split
  · exact combo4_congr sp P j m1 rfl
  · rfl

/-- The entries of a list of adds, in turn. -/
def updAll4 (m1 : Mem V) (L : List (NodeId × V)) (o : Obj V) : Obj V :=
  L.foldl (fun o a => updObj4 sp P j m1 o a.2) o

theorem updAll4_core (m1 : Mem V) (L : List (NodeId × V)) : ∀ (o : Obj V),
    (updAll4 sp P j m1 L o).node = o.node ∧ (updAll4 sp P j m1 L o).level = o.level ∧
    (updAll4 sp P j m1 L o).isData = o.isData ∧
    (updAll4 sp P j m1 L o).hist = o.hist ++ L.map (fun a => (⟨j, a.2⟩ : Entry V)) ∧
    (updAll4 sp P j m1 L o).canonical = o.canonical ∧ (updAll4 sp P j m1 L o).pos = o.pos := by
  induction L with
  | nil => intro o; simp [updAll4]
  | cons a L ih =>
    intro o
    unfold updAll4 at ih ⊢
    simp only [List.foldl_cons]
    obtain ⟨a1, a2, a3, a4, a5, a6⟩ := ih (updObj4 sp P j m1 o a.2)
    obtain ⟨b1, b2, b3, b4, b5, b6⟩ := updObj4_core sp P j m1 o a.2
    refine ⟨by rw [a1, b1], by rw [a2, b2], by rw [a3, b3], by rw [a4, b4]; simp, by rw [a5, b5],
      by rw [a6, b6]⟩

theorem updAll4_slot (m1 : Mem V) (L : List (NodeId × V)) : ∀ (o : Obj V) (y : NodeId),
    (updAll4 sp P j m1 L o).slot? y =
      if y ∈ L.flatMap (fun a => sp.ptrs a.2) then combo4 sp P j m1 o y else o.slot? y := by
  induction L with
  | nil => intro o y; simp [updAll4]
  | cons a L ih =>
    intro o y
    unfold updAll4 at ih ⊢
    simp only [List.foldl_cons]
    rw [ih, List.flatMap_cons]
    by_cases h1 : y ∈ L.flatMap (fun a => sp.ptrs a.2)
    · simp only [h1, ↓reduceIte, List.mem_append, or_true]
      by_cases h2 : y ∈ sp.ptrs a.2
      · apply combo4_idem
        rw [updObj4_slot]; simp [h2]
      · apply combo4_congr
        rw [updObj4_slot]; simp [h2]
    · simp only [h1, ↓reduceIte, List.mem_append, or_false]
      rw [updObj4_slot]

/-- One add: the entry appended to its node's canonical object. -/
def addsStep4 (m1 : Mem V) (m : Mem V) (a : NodeId × V) : Mem V :=
  match m.canonicalOf a.1 with
  | none => m
  | some h =>
    match m.obj? h with
    | none => m
    | some o => m.setObj h (updObj4 sp P j m1 o a.2)

theorem applyChange4_eq (m : Mem V) (c : Changes V) :
    m.applyChange4 sp P j c =
      c.adds.foldl (addsStep4 sp P j (c.new.foldl addNew m)) (c.new.foldl addNew m) := rfl

end Slots4

/-- The objects after the adds: each canonical object of a changed node has its
node's adds, the others are as before. -/
theorem adds_fold4 (sp : Spec V T) (P : Struct V) (j : Time) (m1 : Mem V) (L : List (NodeId × V)) :
    ∀ (L0 : List (NodeId × V)) (m : Mem V),
    m.table = m1.table → m.next = m1.next → m.s = m1.s → m.root = m1.root →
    (∀ h, m.obj? h = (m1.obj? h).map
      (updAll4 sp P j m1 (L0.filter (fun a => m1.canonicalOf a.1 == some h)))) →
    (L.foldl (addsStep4 sp P j m1) m).table = m1.table ∧
    (L.foldl (addsStep4 sp P j m1) m).next = m1.next ∧
    (L.foldl (addsStep4 sp P j m1) m).s = m1.s ∧
    (L.foldl (addsStep4 sp P j m1) m).root = m1.root ∧
    (∀ h, (L.foldl (addsStep4 sp P j m1) m).obj? h = (m1.obj? h).map
      (updAll4 sp P j m1 ((L0 ++ L).filter (fun a => m1.canonicalOf a.1 == some h)))) ∧
    (((m.objs.map (·.1)).Nodup) → ((L.foldl (addsStep4 sp P j m1) m).objs.map (·.1)).Nodup) := by
  induction L with
  | nil => intro L0 m ht hn hs hr ho; simp only [List.foldl_nil, List.append_nil]; exact ⟨ht, hn, hs, hr, ho, id⟩
  | cons a L ih =>
    intro L0 m ht hn hs hr ho
    simp only [List.foldl_cons]
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
          rw [(updAll4_core sp P j m1 _ o1).2.2.2.2.1]
    have hstep : ∀ h, (addsStep4 sp P j m1 m a).obj? h = (m1.obj? h).map
        (updAll4 sp P j m1 ((L0 ++ [a]).filter (fun a => m1.canonicalOf a.1 == some h))) := by
      intro h
      unfold addsStep4
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
            unfold updAll4
            simp [hc, List.foldl_append]
          · rename_i hh
            rw [ho h, List.filter_append]
            have : (some h1 == some h) = false := by simp [Ne.symm hh]
            simp [hc, this]
    have hm' : (addsStep4 sp P j m1 m a).table = m1.table ∧ (addsStep4 sp P j m1 m a).next = m1.next ∧
        (addsStep4 sp P j m1 m a).s = m1.s ∧ (addsStep4 sp P j m1 m a).root = m1.root ∧
        (((m.objs.map (·.1)).Nodup) → ((addsStep4 sp P j m1 m a).objs.map (·.1)).Nodup) := by
      unfold addsStep4
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

/-! ## The memory after the change -/

structure ApplyFacts4 (sp : Spec V T) (P : Struct V) (j : Time) (c : Changes V) (m : Mem V) : Prop where
  table : (m.applyChange4 sp P j c).table = (c.new.foldl addNew m).table
  obj : ∀ h, (m.applyChange4 sp P j c).obj? h = ((c.new.foldl addNew m).obj? h).map
    (updAll4 sp P j (c.new.foldl addNew m)
      (c.adds.filter (fun a => (c.new.foldl addNew m).canonicalOf a.1 == some h)))
  next : (m.applyChange4 sp P j c).next = m.next + c.new.length
  s : (m.applyChange4 sp P j c).s = m.s
  root : (m.applyChange4 sp P j c).root = m.root
  nodup : ((c.new.foldl addNew m).objs.map (·.1)).Nodup →
    ((m.applyChange4 sp P j c).objs.map (·.1)).Nodup

theorem applyFacts4 (sp : Spec V T) (P : Struct V) (j : Time) (c : Changes V) (m : Mem V) :
    ApplyFacts4 sp P j c m := by
  have h := adds_fold4 sp P j (c.new.foldl addNew m) c.adds [] (c.new.foldl addNew m) rfl rfl rfl rfl
    (by intro h; cases (c.new.foldl addNew m).obj? h <;> rfl)
  rw [← applyChange4_eq] at h
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  obtain ⟨p1, p2⟩ := foldl_addNew_parts c.new m
  exact ⟨h1, fun h => by rw [h5 h]; rfl, by rw [h2, foldl_addNew_next], by rw [h3, p1], by rw [h4, p2], h6⟩

/-- The memory m3 after the adds, from m1 after the new nodes' objects. -/
structure ChangeFacts (sp : Spec V T) (P : Struct V) (j : Time) (c : Changes V) (m1 m3 : Mem V) : Prop where
  table : m3.table = m1.table
  obj : ∀ h, m3.obj? h = (m1.obj? h).map
    (updAll4 sp P j m1 (c.adds.filter (fun a => m1.canonicalOf a.1 == some h)))
  next : m3.next = m1.next
  s : m3.s = m1.s
  root : m3.root = m1.root
  nodup : (m1.objs.map (·.1)).Nodup → (m3.objs.map (·.1)).Nodup

theorem changeFacts (sp : Spec V T) (P : Struct V) (j : Time) (c : Changes V) (m : Mem V) :
    ChangeFacts sp P j c (c.new.foldl addNew m) (m.applyChange4 sp P j c) := by
  have hf := applyFacts4 sp P j c m
  obtain ⟨p1, p2⟩ := foldl_addNew_parts c.new m
  exact ⟨hf.table, hf.obj, by rw [hf.next, foldl_addNew_next], by rw [hf.s, p1], by rw [hf.root, p2], hf.nodup⟩

theorem ChangeFacts.canonicalOf {sp : Spec V T} {P : Struct V} {j : Time} {c : Changes V} {m1 m3 : Mem V}
    (hcf : ChangeFacts sp P j c m1 m3) (y : NodeId) : m3.canonicalOf y = m1.canonicalOf y := by
  unfold Mem.canonicalOf Mem.tableOf
  rw [hcf.table]
  cases List.lookup y m1.table with
  | none => rfl
  | some h =>
    simp only
    rw [hcf.obj h]
    cases m1.obj? h with
    | none => rfl
    | some o =>
      simp only [Option.map_some]
      rw [(updAll4_core sp P j _ _ o).2.2.2.2.1]

theorem applyChange4_canonicalOf (sp : Spec V T) (P : Struct V) (j : Time) (c : Changes V)
    (m : Mem V) (y : NodeId) :
    (m.applyChange4 sp P j c).canonicalOf y = (c.new.foldl addNew m).canonicalOf y := by
  have hf := applyFacts4 sp P j c m
  unfold Mem.canonicalOf Mem.tableOf
  rw [hf.table]
  cases List.lookup y (c.new.foldl addNew m).table with
  | none => rfl
  | some h =>
    simp only
    rw [hf.obj h]
    cases (c.new.foldl addNew m).obj? h with
    | none => rfl
    | some o =>
      simp only [Option.map_some]
      rw [(updAll4_core sp P j _ _ o).2.2.2.2.1]

theorem foldl_addNew_tblNodup (N : List NewNode) : ∀ (m : Mem V), (m.table.map (·.1)).Nodup →
    ((N.foldl addNew m).table.map (·.1)).Nodup := by
  induction N with
  | nil => intro m h; exact h
  | cons nn N ih =>
    intro m h
    simp only [List.foldl_cons]
    apply ih
    unfold addNew
    exact setTable_nodup _ _ _ h

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

/-- The memory m1 after the new nodes' objects: m's objects, and a canonical object
for each new node; m's canonical objects for the other nodes. -/
structure AddFacts (m m1 : Mem V) (c : Changes V) : Prop where
  old : ∀ h, h < m.next → m1.obj? h = m.obj? h
  cls : ∀ h o, m1.obj? h = some o → (h < m.next ∧ m.obj? h = some o) ∨
    (m.next ≤ h ∧ ∃ nn ∈ c.new, o = newObj nn ∧ m1.tableOf nn.id = some h)
  canOld : ∀ y, y ∉ c.new.map (·.id) → m1.canonicalOf y = m.canonicalOf y
  tabOld : ∀ y, y ∉ c.new.map (·.id) → m1.tableOf y = m.tableOf y
  canNew : ∀ nn ∈ c.new, ∃ h, m.next ≤ h ∧ m1.canonicalOf nn.id = some h ∧ m1.obj? h = some (newObj nn)
  fresh : ∀ h, m1.next ≤ h → m1.obj? h = none
  nodup : (m1.objs.map (·.1)).Nodup
  tnodup : (m1.table.map (·.1)).Nodup
  s : m1.s = m.s
  root : m1.root = m.root
  next : m1.next = m.next + c.new.length

theorem EInv.addFacts (hm : EInv sp db S0 k m) (hnd : (c.new.map (·.id)).Nodup) :
    AddFacts m (c.new.foldl addNew m) c :=
  ⟨fun h hh => foldl_addNew_old c.new m h hh,
   fun h o ho => foldl_addNew_obj c.new hnd m hm.fresh h o ho,
   fun y hy => addNew_canonicalOf_old m c.new hm.fresh (fun y h ht => by
     obtain ⟨o, ho, -⟩ := hm.tbl y h ht; simp [ho]) hy,
   fun y hy => foldl_addNew_table_old c.new m y hy,
   fun nn hnn => addNew_canonicalOf_new m c.new hnd hnn,
   foldl_addNew_fresh c.new m hm.fresh,
   foldl_addNew_nodup c.new m hm.fresh hm.objNodup,
   foldl_addNew_tblNodup c.new m hm.tblNodup,
   (foldl_addNew_parts c.new m).1, (foldl_addNew_parts c.new m).2, foldl_addNew_next c.new m⟩

/-- A node of the structure is not new. -/
theorem not_new_of_get? (hstep : StepOK sp db.P (k + 1) c) {y : NodeId} {n : Node V}
    (hn : db.P.get? y = some n) : y ∉ c.new.map (·.id) := by
  intro hy
  obtain ⟨nn, hnn, hid⟩ := List.mem_map.mp hy
  have := hstep.fresh nn hnn
  rw [hid, hn] at this; cases this

/-- With A-COPY's sources, the new slot of a pointer exists. -/
theorem EInv.NS4_some (hinv : Inv sp db k) (hm : EInv sp db S0 k m) {path : List NodeId}
    (hpd : ∀ x ∈ path, PathDone sp db.P k path m x) (hpath : ∀ p ∈ path, reachable sp db.P k p = true)
    (hpn : ∀ p ∈ path, (db.P.get? p).isSome) (hstep : StepOK sp db.P (k + 1) c) {y : NodeId}
    (hy : y ∈ c.new.map (·.id) ∨ y ∈ path ∨ ∃ z ∈ path, ∃ nz, db.P.get? z = some nz ∧
      y ∈ pointees sp nz.hist ∧ (written sp z = true ∨ y ∈ sp.live (nz.hist.upTo k))) :
    (NS4 sp db.P (k + 1) (c.new.foldl addNew m) y).isSome := by
  have haf := hm.addFacts hstep.distinct
  unfold NS4
  cases hc : (c.new.foldl addNew m).canonicalOf y with
  | some h => rfl
  | none =>
    simp only [Option.map_none, Option.none_or]
    rcases hy with hy | hy | ⟨z, hz, nz, hnz, hyz, hwl⟩
    · exfalso
      obtain ⟨nn, hnn, hid⟩ := List.mem_map.mp hy
      obtain ⟨h, -, hc', -⟩ := haf.canNew nn hnn
      rw [hid, hc] at hc'; cases hc'
    · exfalso
      obtain ⟨hcy, -⟩ := hpd y hy
      obtain ⟨ny, hny⟩ := Option.isSome_iff_exists.mp (hpn y hy)
      rw [haf.canOld y (not_new_of_get? hstep hny)] at hc
      rw [hc] at hcy; cases hcy
    · -- The canonical object of z, a node of the path, is a source.
      obtain ⟨hcz, -⟩ := hpd z hz
      obtain ⟨hz0, hz0e⟩ := Option.isSome_iff_exists.mp hcz
      obtain ⟨oz, hoz, hcoz, hnoz⟩ := hm.obj_of_canonicalOf hz0e
      obtain ⟨n', hn', hh', -, -⟩ := hm.cc hz0 oz hoz hcoz
      rw [hnoz, hnz, Option.some.injEq] at hn'
      subst hn'
      have hrz := hpath z hz
      have hsl : (oz.slot? y).isSome := by
        rcases hwl with hw | hl
        · obtain ⟨sl, hsl, -⟩ := hm.slots hz0 oz hoz
            ⟨hcoz, by rw [hnoz]; exact hw, Or.inl (by rw [hnoz]; exact hrz)⟩ y (by rw [hh']; exact hyz)
          rw [hsl]; rfl
        · have hyl : y ∈ sp.live oz.hist := by
            rw [hh', ← upTo_of_forall _ _ (hinv.times z nz hnz)]; exact hl
          obtain ⟨sl, hsl, -⟩ := hm.live hz0 oz hoz hcoz (by rw [hnoz]; exact hrz) y hyl
          rw [hsl]; rfl
      have hlt : hz0 < m.next := lt_next_of_obj? hm.fresh hoz
      have hmem : (hz0, oz) ∈ (c.new.foldl addNew m).objs := by
        apply mem_objs_of_obj?
        rw [haf.old hz0 hlt]; exact hoz
      have hsrc : srcOK4 sp db.P (k + 1) y (hz0, oz) = true := by
        unfold srcOK4
        simp only [Bool.and_eq_true, Bool.or_eq_true, hcoz, hsl, true_and]
        refine ⟨⟨List.contains_iff_mem.mpr (by rw [hh']; exact hyz), by
          rw [hnoz]; simpa using hrz⟩, ?_⟩
        rcases hwl with hw | hl
        · left; rw [hnoz]; exact hw
        · right; rw [hnoz, hnz]; simpa using hl
      have hfind := List.find?_isSome.mpr ⟨_, hmem, hsrc⟩
      unfold srcSlot4
      obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp hfind
      rw [hp]
      have hpp := List.find?_some hp
      unfold srcOK4 at hpp
      simp only [Bool.and_eq_true] at hpp
      simpa using hpp.1.1.1.2

/-- The new slot of a pointer: a memory slot to the pointee's canonical object;
or, for a pointee with none (so not in D, not new), a copy of a slot of m that
serializes its latest version. -/
theorem EInv.NS4_good (hinv : Inv sp db k) (hm : EInv sp db S0 k m) (hstep : StepOK sp db.P (k + 1) c)
    {y : NodeId} {sl : Slot} (hns : NS4 sp db.P (k + 1) (c.new.foldl addNew m) y = some sl) :
    (∃ h', sl = Slot.mem h' ∧ (c.new.foldl addNew m).canonicalOf y = some h') ∨
    ((c.new.foldl addNew m).canonicalOf y = none ∧ inD db.D y = false ∧ y ∉ c.new.map (·.id) ∧
      slotRefOf S0 m y sl = (db.S.lv y).map (·.recNo) ∧
      ∃ h0 o0, m.obj? h0 = some o0 ∧ o0.slot? y = some sl) := by
  have haf := hm.addFacts hstep.distinct
  unfold NS4 at hns
  cases hc : (c.new.foldl addNew m).canonicalOf y with
  | some h =>
    rw [hc] at hns
    simp only [Option.map_some, Option.some_or, Option.some.injEq] at hns
    exact Or.inl ⟨h, hns.symm, rfl⟩
  | none =>
    rw [hc] at hns
    simp only [Option.map_none, Option.none_or] at hns
    right
    have hyn : y ∉ c.new.map (·.id) := by
      intro hy
      obtain ⟨nn, hnn, hid⟩ := List.mem_map.mp hy
      obtain ⟨h, -, hc', -⟩ := haf.canNew nn hnn
      rw [hid, hc] at hc'; cases hc'
    have hcm : m.canonicalOf y = none := by rw [← haf.canOld y hyn]; exact hc
    have hyD : inD db.D y = false := by
      cases hyd : inD db.D y with
      | false => rfl
      | true => have := hm.dCanon y hyd; rw [hcm] at this; cases this
    unfold srcSlot4 at hns
    cases hf : (c.new.foldl addNew m).objs.find? (srcOK4 sp db.P (k + 1) y) with
    | none => rw [hf] at hns; cases hns
    | some p =>
      rw [hf] at hns
      simp only [Option.bind_some] at hns
      have hpp := List.find?_some hf
      have hpm := List.mem_of_find?_eq_some hf
      unfold srcOK4 at hpp
      simp only [Bool.and_eq_true, Bool.or_eq_true] at hpp
      obtain ⟨⟨⟨⟨hcan, -⟩, hyp⟩, hrp⟩, hwl⟩ := hpp
      have hpo1 := obj?_of_mem_objs haf.nodup hpm
      -- The source is an object of m: a new node's object has no slots.
      have hpo : m.obj? p.1 = some p.2 := by
        rcases haf.cls p.1 p.2 hpo1 with ⟨-, h2⟩ | ⟨-, nn, -, hon, -⟩
        · exact h2
        · exfalso; rw [hon] at hns; simp [newObj, Obj.slot?] at hns
      have hK1 : k + 1 - 1 = k := by omega
      rw [hK1] at hrp hwl
      refine ⟨rfl, hyD, hyn, ?_, p.1, p.2, hpo, hns⟩
      rcases hwl with hw | hl
      · obtain ⟨sl', hsl', hi⟩ := hm.slots p.1 p.2 hpo ⟨hcan, hw, Or.inl hrp⟩ y
          (List.contains_iff_mem.mp hyp)
        rw [hns, Option.some.injEq] at hsl'
        subst hsl'
        exact hi.1 hyD
      · obtain ⟨n, hn, hh, -, -⟩ := hm.cc p.1 p.2 hpo hcan
        rw [hn] at hl
        simp only [List.contains_iff_mem] at hl
        have hyl : y ∈ sp.live p.2.hist := by
          rw [hh, ← upTo_of_forall _ _ (hinv.times _ n hn)]; exact hl
        obtain ⟨sl', hsl', hi⟩ := hm.live p.1 p.2 hpo hcan hrp y hyl
        rw [hns, Option.some.injEq] at hsl'
        subst hsl'
        exact hi.2 hyD

/-- A node's canonical object after the new nodes: the adds for it are the
node's. -/
theorem EInv.adds_filter_node (hm : EInv sp db S0 k m) (hnd : (c.new.map (·.id)).Nodup) {x : NodeId}
    {h : Nat} (hx : (c.new.foldl addNew m).canonicalOf x = some h) :
    c.adds.filter (fun a => (c.new.foldl addNew m).canonicalOf a.1 == some h) =
      c.adds.filter (fun a => a.1 == x) := by
  apply List.filter_congr
  intro a _
  have hnode : ∀ z, (c.new.foldl addNew m).canonicalOf z = some h → ∃ o,
      (c.new.foldl addNew m).obj? h = some o ∧ o.node = z := by
    intro z hz
    obtain ⟨ht, o, ho, -⟩ := ((c.new.foldl addNew m).canonicalOf_eq_some z h).mp hz
    refine ⟨o, ho, ?_⟩
    rcases foldl_addNew_obj c.new hnd m hm.fresh h o ho with ⟨hlt, h2⟩ | ⟨hle, nn, hnn, hon, ht'⟩
    · by_cases hzn : z ∈ c.new.map (·.id)
      · exfalso
        obtain ⟨nn, hnn, hid⟩ := List.mem_map.mp hzn
        obtain ⟨h', hle', ht', -⟩ := foldl_addNew_new c.new hnd m nn hnn
        rw [hid, ht, Option.some.injEq] at ht'
        omega
      · rw [foldl_addNew_table_old c.new m z hzn] at ht
        obtain ⟨o', ho', hn'⟩ := hm.tbl z h ht
        rw [h2, Option.some.injEq] at ho'
        rw [ho', hn']
    · rw [hon]
      by_cases hz : z = nn.id
      · rw [hz]; rfl
      · exfalso
        by_cases hzn : z ∈ c.new.map (·.id)
        · obtain ⟨nn2, hnn2, hid2⟩ := List.mem_map.mp hzn
          obtain ⟨h2, -, ht2, ho2⟩ := foldl_addNew_new c.new hnd m nn2 hnn2
          rw [hid2, ht, Option.some.injEq] at ht2
          subst ht2
          rw [ho, Option.some.injEq] at ho2
          rw [hon] at ho2
          have : nn.id = nn2.id := by
            have := congrArg Obj.node ho2; simpa [newObj] using this
          rw [hid2] at this
          exact hz this.symm
        · rw [foldl_addNew_table_old c.new m z hzn] at ht
          obtain ⟨o', ho', -⟩ := hm.tbl z h ht
          have := lt_next_of_obj? hm.fresh ho'
          omega
  obtain ⟨o, ho, hon⟩ := hnode x hx
  cases hc : (c.new.foldl addNew m).canonicalOf a.1 == some h
  · simp only [Bool.false_eq, beq_eq_false_iff_ne, ne_eq]
    intro hax
    rw [hax] at hc
    simp [hx] at hc
  · simp only [beq_iff_eq] at hc
    obtain ⟨o', ho', hon'⟩ := hnode a.1 hc
    rw [ho, Option.some.injEq] at ho'
    subst ho'
    simp [← hon', hon]

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

/-- The memory after the change, before the writes (m3 in `evictTrans`), for the
state db at k, the change c of transaction k + 1 and its paths: CC for the new
structure, positions as before, and the slots of the objects that may be
written or read, against the old D. -/
structure AInv (sp : Spec V T) (db : DB V T) (S0 : Stream V T) (k : Nat) (c : Changes V)
    (path : List NodeId) (m : Mem V) : Prop where
  pre : S0 <+: db.S
  sEq : m.s = lastSp S0
  fresh : ∀ h, m.next ≤ h → m.obj? h = none
  objNodup : (m.objs.map (·.1)).Nodup
  root : ∃ o, m.obj? m.root = some o ∧ o.canonical = true ∧ o.node = root
  tblNodup : (m.table.map (·.1)).Nodup
  tbl : TableNode m
  slotsNode : SlotsNode m
  tblCanon : ∀ y h, m.tableOf y = some h → ∃ o, m.obj? h = some o ∧ o.canonical = true
  canonTbl : ∀ h o, m.obj? h = some o → o.canonical = true → m.tableOf o.node = some h
  cc : ∀ h o, m.obj? h = some o → o.canonical = true →
    ∃ n, (db.P.apply (k + 1) c).get? o.node = some n ∧ o.hist = n.hist ∧ o.level = n.level ∧
      o.isData = n.isData
  pos : PosOK db.S [] m
  canon : ∀ y, (inD db.D y = true ∨ y ∈ path ∨ y ∈ c.new.map (·.id)) → (m.canonicalOf y).isSome
  snap : ∀ h o, m.obj? h = some o → o.canonical = false → SnapExact sp S0 db m o
  slots : ∀ h o, m.obj? h = some o → o.canonical = true → written sp o.node = true →
    (reachable sp (db.P.apply (k + 1) c) (k + 1) o.node = true ∨ inD db.D o.node = true ∨
      reachable sp db.P k o.node = true) →
    ∀ y ∈ pointees sp o.hist, ∃ sl, o.slot? y = some sl ∧
      (inD db.D y = false → slotRefOf S0 m y sl = (db.S.lv y).map (·.recNo) ∧
        (y ∈ c.new.map (·.id) → ∃ h', sl = Slot.mem h' ∧ m.canonicalOf y = some h')) ∧
      (inD db.D y = true → (∃ h', sl = Slot.mem h' ∧ m.canonicalOf y = some h') ∨
        (inD db.D o.node = true ∧ ∃ a b, dOf db.D o.node = some a ∧ dOf db.D y = some b ∧ a ≤ b))
  live : ∀ h o, m.obj? h = some o → o.canonical = true →
    reachable sp (db.P.apply (k + 1) c) (k + 1) o.node = true →
    ∀ y ∈ sp.live o.hist, ∃ sl, o.slot? y = some sl ∧
      ((inD db.D y = true ∨ y ∈ path ∨ y ∈ c.new.map (·.id)) →
        ∃ h', sl = Slot.mem h' ∧ m.canonicalOf y = some h') ∧
      (inD db.D y = false → slotRefOf S0 m y sl = (db.S.lv y).map (·.recNo))

end SIS
