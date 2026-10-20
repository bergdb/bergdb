/-
Proofs about reclaim, part 18 (bergdb item 001, WP R5, T12 with eviction): a
memory with another object for the root (`Mem.withRoot`). After a restart from
a cut stream, the Level 4 memory is the one after the restart from the whole
stream but for the root's object: a virtual root rebuilt from the root children
that the cut stream still has. The physical writer and the cache operations do
the same on both while the two root objects agree from the first available
time on (`RootRel`).
-/
import SIS.Proof.CutLaterRead

set_option linter.unusedSectionVars false

namespace SIS

variable {V T : Type} [DecidableEq V]

/-! ## Another object for the root -/

/-- m with object oc for the root. -/
def Mem.withRoot (m : Mem V) (oc : Obj V) : Mem V :=
  { m with objs := m.objs.map (fun p => if p.1 == m.root then (m.root, oc) else p) }

section Basic

variable {m : Mem V} {oc : Obj V}

@[simp] theorem withRoot_table : (m.withRoot oc).table = m.table := rfl
@[simp] theorem withRoot_s : (m.withRoot oc).s = m.s := rfl
@[simp] theorem withRoot_root : (m.withRoot oc).root = m.root := rfl
@[simp] theorem withRoot_next : (m.withRoot oc).next = m.next := rfl

theorem withRoot_tableOf (y : NodeId) : (m.withRoot oc).tableOf y = m.tableOf y := rfl

theorem withRoot_obj? (h : Nat) :
    (m.withRoot oc).obj? h = if h = m.root then (m.obj? m.root).map (fun _ => oc) else m.obj? h := by
  unfold Mem.withRoot Mem.obj?
  exact lookup_map_set m.objs m.root h oc

theorem withRoot_obj?_ne {h : Nat} (hne : h ≠ m.root) : (m.withRoot oc).obj? h = m.obj? h := by
  rw [withRoot_obj?]; simp [hne]

theorem withRoot_obj?_root {oe : Obj V} (he : m.obj? m.root = some oe) :
    (m.withRoot oc).obj? m.root = some oc := by
  rw [withRoot_obj?]; simp [he]

/-- The filter of `setObj` and the map of `withRoot` commute: both keep the handles. -/
theorem filter_map_root (l : List (Nat × Obj V)) (r h : Nat) (oc : Obj V) :
    (l.map (fun p => if p.1 == r then (r, oc) else p)).filter (fun p => p.1 != h) =
      (l.filter (fun p => p.1 != h)).map (fun p => if p.1 == r then (r, oc) else p) := by
  rw [List.filter_map]
  congr 1
  apply List.filter_congr
  intro p _
  simp only [Function.comp]
  by_cases hp : p.1 = r
  · subst hp; simp
  · simp [hp]

theorem withRoot_setObj_ne {h : Nat} (hne : h ≠ m.root) (o : Obj V) :
    (m.withRoot oc).setObj h o = (m.setObj h o).withRoot oc := by
  unfold Mem.withRoot Mem.setObj
  simp only [List.map_cons, filter_map_root]
  have : (h == m.root) = false := by simp [hne]
  simp [this]

theorem withRoot_setObj_root (o o' : Obj V) :
    (m.withRoot oc).setObj m.root o = (m.setObj m.root o').withRoot o := by
  unfold Mem.withRoot Mem.setObj
  simp only [List.map_cons, filter_map_root, beq_self_eq_true, ↓reduceIte]
  congr 2
  apply List.map_congr_left
  intro p hp
  have hne : p.1 ≠ m.root := by
    have := (List.mem_filter.mp hp).2
    simpa using this
  simp [hne]

theorem withRoot_addObj (hne : m.next ≠ m.root) (o : Obj V) :
    (m.withRoot oc).addObj o = ((m.addObj o).1.withRoot oc, (m.addObj o).2) := by
  unfold Mem.withRoot Mem.addObj
  have : (m.next == m.root) = false := by simp [hne]
  simp only [List.map_cons, this, Bool.false_eq_true, ↓reduceIte]

theorem withRoot_setTable (y : NodeId) (h : Nat) :
    (m.withRoot oc).setTable y h = (m.setTable y h).withRoot oc := rfl

theorem withRoot_canonicalOf {oe : Obj V} (he : m.obj? m.root = some oe) (hc : oc.canonical = oe.canonical)
    (y : NodeId) : (m.withRoot oc).canonicalOf y = m.canonicalOf y := by
  unfold Mem.canonicalOf
  rw [withRoot_tableOf]
  cases m.tableOf y with
  | none => rfl
  | some h =>
    simp only
    by_cases hh : h = m.root
    · subst hh
      rw [withRoot_obj?_root he, he]
      simp [hc]
    · rw [withRoot_obj?_ne hh]

end Basic


/-! ## The two root objects -/

/-- The root's object after a restart from a cut stream (oc) and after the
restart from the whole stream (oe), each with the transactions since: the same
but for the history and the slots of the root children that only times before
f need. Without a virtual root, the same object. -/
structure RootRel (sp : Spec V T) (f : Time) (oc oe : Obj V) : Prop where
  nv : sp.virt = false → oc = oe
  node : oc.node = oe.node
  level : oc.level = oe.level
  isData : oc.isData = oe.isData
  canonical : oc.canonical = oe.canonical
  pos : oc.pos = oe.pos
  live : ∀ t, f ≤ t → sp.live (oc.hist.upTo t) = sp.live (oe.hist.upTo t)
  slots : ∀ y, y ∈ pointees sp oc.hist → oc.slot? y = oe.slot? y
  noSlot : sp.virt = true → ∀ y, y ∉ pointees sp oc.hist → oc.slot? y = none
  vals : sp.virt = true → ∀ e ∈ oc.hist, ∃ z, e.val = sp.rootVal z
  /-- oe has slots for pointees of its history only. -/
  keysE : sp.virt = true → ∀ y, (oe.slot? y).isSome = true → y ∈ pointees sp oe.hist

/-- Without a virtual root, an object and itself. -/
theorem RootRel.ofNV {sp : Spec V T} (hv : sp.virt = false) (f : Time) (o : Obj V) : RootRel sp f o o :=
  ⟨fun _ => rfl, rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl, fun _ _ => rfl,
    fun h => absurd h (by simp [hv]), fun h => absurd h (by simp [hv]), fun h => absurd h (by simp [hv])⟩

/-- Setting the slot for a pointee of oc's history the same in both. -/
theorem RootRel.setSlot {sp : Spec V T} {f : Time} {oc oe : Obj V} (hr : RootRel sp f oc oe) {y : NodeId}
    (hy : y ∈ pointees sp oc.hist ∨ sp.virt = false) (sl : Slot) :
    RootRel sp f (oc.setSlot y sl) (oe.setSlot y sl) where
  nv := fun hv => by rw [hr.nv hv]
  node := hr.node
  level := hr.level
  isData := hr.isData
  canonical := hr.canonical
  pos := hr.pos
  live := hr.live
  slots := by
    intro z hz
    rw [Obj.slot?_setSlot, Obj.slot?_setSlot]
    have hz' : z ∈ pointees sp oc.hist := hz
    split
    · rename_i he; subst he
      rcases hy with hy | hv
      · rw [hr.slots _ hy]
      · rw [hr.nv hv]
    · exact hr.slots z hz'
  noSlot := by
    intro hv z hz
    rw [Obj.slot?_setSlot]
    split
    · rename_i he; subst he
      rw [hr.noSlot hv _ hz]; rfl
    · exact hr.noSlot hv z hz
  vals := hr.vals
  keysE := by
    intro hv z hz
    rw [Obj.slot?_setSlot] at hz
    rw [Obj.setSlot_hist]
    split at hz
    · rename_i he; subst he
      cases h : oe.slot? z with
      | none => rw [h] at hz; cases hz
      | some _ => exact hr.keysE hv z (by rw [h]; rfl)
    · exact hr.keysE hv z hz

/-! ## The loader -/

section Loader

variable {sp : Spec V T} {S0 S : Stream V T} {m : Mem V} {oc oe : Obj V}

/-- The memories of the two runs, the same but for the root's object. -/
structure RootAt (m : Mem V) (oe : Obj V) : Prop where
  root : m.obj? m.root = some oe
  fresh : m.next ≠ m.root

theorem reached4_withRoot (hra : RootAt m oe) (hc : oc.canonical = oe.canonical) {hp : Nat} {y : NodeId}
    (hy : hp ≠ m.root ∨ oc.slot? y = oe.slot? y) :
    (m.withRoot oc).reached4 sp S0 S hp y = (m.reached4 sp S0 S hp y).map (fun p => (p.1.withRoot oc, p.2)) := by
  have hslot : ((m.withRoot oc).obj? hp).bind (·.slot? y) = (m.obj? hp).bind (·.slot? y) := by
    by_cases he : hp = m.root
    · subst he
      rw [withRoot_obj?_root hra.root, hra.root]
      rcases hy with hy | hy
      · exact absurd rfl hy
      · simp [hy]
    · rw [withRoot_obj?_ne he]
  unfold Mem.reached4
  rw [hslot]
  cases (m.obj? hp).bind (·.slot? y) with
  | none => rfl
  | some sl =>
    cases sl with
    | mem h =>
      simp only
      have : ((m.withRoot oc).obj? h).isSome = (m.obj? h).isSome := by
        rw [withRoot_obj?]
        split
        · rename_i he; subst he; rw [hra.root]; rfl
        · rfl
      rw [this]
      split <;> rfl
    | stream r =>
      simp only
      rw [withRoot_canonicalOf hra.root hc]
      cases m.canonicalOf y with
      | some h0 => rfl
      | none =>
        simp only [withRoot_s]
        cases ruleRRef S0 m.s y r with
        | none => rfl
        | some r' =>
          simp only
          cases S.versionAt r' y with
          | none => rfl
          | some w =>
            simp only [Option.map_some]
            rw [withRoot_addObj hra.fresh]

theorem swz_withRoot {hp : Nat} (y : NodeId) (h1 : Nat) (hra : RootAt m oe) :
    (m.withRoot oc).swz hp y h1 =
      (m.swz hp y h1).withRoot (if hp = m.root then oc.setSlot y (Slot.mem h1) else oc) := by
  unfold Mem.swz
  by_cases he : hp = m.root
  · subst he
    rw [withRoot_obj?_root hra.root, hra.root]
    simp only [↓reduceIte]
    exact withRoot_setObj_root _ _
  · rw [withRoot_obj?_ne he]
    simp only [he, ↓reduceIte]
    cases m.obj? hp with
    | none => rfl
    | some op => exact withRoot_setObj_ne he _


theorem promote_withRoot (hra : RootAt m oe) (hc : oc.canonical = oe.canonical) (hp : Nat) (y : NodeId)
    (h : Nat) (hpick : (m.canonicalOf y).getD h ≠ m.root) :
    (m.withRoot oc).promote hp y h =
      ((m.promote hp y h).1.withRoot
        (if hp = m.root then oc.setSlot y (Slot.mem ((m.canonicalOf y).getD h)) else oc),
        (m.promote hp y h).2) := by
  unfold Mem.promote
  dsimp only
  rw [withRoot_canonicalOf hra.root hc]
  generalize (m.canonicalOf y).getD h = pick at hpick ⊢
  rw [withRoot_obj?_ne hpick]
  cases hpo : m.obj? pick with
  | none =>
    simp only
    by_cases he : hp = m.root
    · subst he
      rw [withRoot_obj?_root hra.root, hra.root]
      simp only [↓reduceIte, Prod.mk.injEq, and_true]
      exact withRoot_setObj_root _ _
    · rw [withRoot_obj?_ne he]
      simp only [he, ↓reduceIte]
      cases m.obj? hp with
      | none => rfl
      | some op => simp only [withRoot_setObj_ne he]
  | some o =>
    simp only
    rw [withRoot_setObj_ne hpick, withRoot_setTable]
    have hra1 : ((m.setObj pick { o with canonical := true }).setTable y pick).obj? m.root = some oe := by
      rw [Mem.obj?_setTable, Mem.obj?_setObj]
      simp only [Ne.symm hpick, ↓reduceIte]
      exact hra.root
    have hr1 : ((m.setObj pick { o with canonical := true }).setTable y pick).root = m.root := rfl
    by_cases he : hp = m.root
    · subst he
      rw [← hr1, withRoot_obj?_root (by rw [hr1]; exact hra1), hr1, hra1]
      simp only [↓reduceIte, Prod.mk.injEq, and_true]
      rw [← hr1]
      exact withRoot_setObj_root _ _
    · have he1 : hp ≠ ((m.setObj pick { o with canonical := true }).setTable y pick).root := by
        rw [hr1]; exact he
      rw [withRoot_obj?_ne he1]
      simp only [he, ↓reduceIte]
      cases ((m.setObj pick { o with canonical := true }).setTable y pick).obj? hp with
      | none => rfl
      | some op => simp only [withRoot_setObj_ne he1]


theorem Obj.setSlot_setSlot (o : Obj V) (y : NodeId) (a b : Slot) :
    (o.setSlot y a).setSlot y b = o.setSlot y b := by
  unfold Obj.setSlot
  simp only [List.map_map]
  congr 1
  apply List.map_congr_left
  intro p _
  simp only [Function.comp]
  by_cases hp : p.1 == y
  · simp [hp]
  · simp [hp]

/-- The root's object after a swizzle, or after a promotion. -/
theorem swz_obj?_root (m : Mem V) (hp : Nat) (y : NodeId) (h1 : Nat) :
    (m.swz hp y h1).obj? m.root =
      if hp = m.root then (m.obj? m.root).map (·.setSlot y (Slot.mem h1)) else m.obj? m.root := by
  unfold Mem.swz
  by_cases he : hp = m.root
  · rw [he]
    cases ho : m.obj? m.root with
    | none => simp [ho]
    | some op => simp [Mem.obj?_setObj]
  · cases ho : m.obj? hp with
    | none => simp [he]
    | some op => simp [Mem.obj?_setObj, Ne.symm he, he]

theorem swz_root' (m : Mem V) (hp : Nat) (y : NodeId) (h1 : Nat) : (m.swz hp y h1).root = m.root := by
  unfold Mem.swz; split <;> rfl

theorem swz_next (m : Mem V) (hp : Nat) (y : NodeId) (h1 : Nat) : (m.swz hp y h1).next = m.next := by
  unfold Mem.swz; split <;> rfl

theorem promote_root (m : Mem V) (hp : Nat) (y : NodeId) (h : Nat) : (m.promote hp y h).1.root = m.root := by
  unfold Mem.promote; dsimp only; split <;> split <;> rfl

theorem promote_next (m : Mem V) (hp : Nat) (y : NodeId) (h : Nat) : (m.promote hp y h).1.next = m.next := by
  unfold Mem.promote; dsimp only; split <;> split <;> rfl

theorem promote_obj?_root (m : Mem V) (hp : Nat) (y : NodeId) (h : Nat) (hpick : (m.canonicalOf y).getD h ≠ m.root) :
    (m.promote hp y h).1.obj? m.root =
      if hp = m.root then (m.obj? m.root).map (·.setSlot y (Slot.mem (m.promote hp y h).2)) else m.obj? m.root := by
  unfold Mem.promote
  dsimp only
  generalize (m.canonicalOf y).getD h = pick at hpick ⊢
  cases hpo : m.obj? pick with
  | none =>
    simp only
    by_cases he : hp = m.root
    · rw [he]
      cases hmo : m.obj? m.root with
      | none => simp [hmo]
      | some op => simp [Mem.obj?_setObj]
    · cases hmo : m.obj? hp with
      | none => simp [he]
      | some op => simp [Mem.obj?_setObj, Ne.symm he, he]
  | some o =>
    simp only
    have he1 : ((m.setObj pick { o with canonical := true }).setTable y pick).obj? m.root = m.obj? m.root := by
      rw [Mem.obj?_setTable, Mem.obj?_setObj]
      simp [Ne.symm hpick]
    by_cases he : hp = m.root
    · rw [he, he1]
      cases hmo : m.obj? m.root with
      | none => simp [he1, hmo]
      | some op => simp [Mem.obj?_setObj]
    · cases hmo : ((m.setObj pick { o with canonical := true }).setTable y pick).obj? hp with
      | none => simp [he, he1]
      | some op => simp [Mem.obj?_setObj, Ne.symm he, he, he1]


/-- The root's object after a follow from hp for y with result r. -/
def rootAfter (hp root : Nat) (y : NodeId) (r : Option Nat) (o : Obj V) : Obj V :=
  if hp = root then (match r with | some h' => o.setSlot y (Slot.mem h') | none => o) else o

theorem RootRel.rootAfter {f : Time} (hr : RootRel sp f oc oe) {hp root : Nat} {y : NodeId}
    (hy : hp ≠ root ∨ y ∈ pointees sp oc.hist ∨ sp.virt = false) (r : Option Nat) :
    RootRel sp f (SIS.rootAfter hp root y r oc) (SIS.rootAfter hp root y r oe) := by
  unfold SIS.rootAfter
  by_cases he : hp = root
  · simp only [he, ↓reduceIte]
    cases r with
    | none => exact hr
    | some h' =>
      simp only
      rcases hy with hy | hy | hy
      · exact absurd he hy
      · exact hr.setSlot (Or.inl hy) _
      · exact hr.setSlot (Or.inr hy) _
  · simp only [he, ↓reduceIte]; exact hr

theorem rootAfter_none (hp root : Nat) (y : NodeId) (o : Obj V) : rootAfter hp root y none o = o := by
  unfold rootAfter; split <;> rfl

theorem rootAfter_canonical (hp root : Nat) (y : NodeId) (r : Option Nat) (o : Obj V) :
    (rootAfter hp root y r o).canonical = o.canonical := by
  unfold rootAfter; split
  · split <;> rfl
  · rfl

/-- The follow, for the reader or the writer, on the memory with the other root
object: the same, the root's object changed in the same way. -/
theorem follow4_withRoot (hra : RootAt m oe) (hc : oc.canonical = oe.canonical) {hp : Nat} {y : NodeId}
    (hsl : hp ≠ m.root ∨ oc.slot? y = oe.slot? y) (w : Bool)
    (hside : ∀ m1 h1, m.reached4 sp S0 S hp y = some (m1, h1) → m1.root = m.root ∧ m1.obj? m.root = some oe ∧
      m1.next ≠ m.root ∧ (w = true → ((m1.swz hp y h1).canonicalOf y).getD h1 ≠ m.root)) :
    (m.withRoot oc).follow4 sp S0 S hp y w =
      ((m.follow4 sp S0 S hp y w).1.withRoot (rootAfter hp m.root y (m.follow4 sp S0 S hp y w).2 oc),
        (m.follow4 sp S0 S hp y w).2) ∧
    (m.follow4 sp S0 S hp y w).1.obj? m.root = some (rootAfter hp m.root y (m.follow4 sp S0 S hp y w).2 oe) ∧
    (m.follow4 sp S0 S hp y w).1.root = m.root ∧ (m.follow4 sp S0 S hp y w).1.next ≠ m.root := by
  rw [follow4_eq, follow4_eq, reached4_withRoot hra hc hsl]
  cases hrc : m.reached4 sp S0 S hp y with
  | none =>
    dsimp only
    simp only [Option.map_none, rootAfter_none]
    exact ⟨trivial, hra.root, trivial, hra.fresh⟩
  | some p =>
    obtain ⟨m1, h1⟩ := p
    obtain ⟨hr1, hra1, hfr1, hpick⟩ := hside m1 h1 hrc
    have hra1' : RootAt m1 oe := ⟨by rw [hr1]; exact hra1, by rw [hr1]; exact hfr1⟩
    simp only [Option.map_some]
    rw [swz_withRoot y h1 hra1', hr1]
    have hroot2 : (m1.swz hp y h1).obj? (m1.swz hp y h1).root =
        some (if hp = m.root then oe.setSlot y (Slot.mem h1) else oe) := by
      rw [swz_root', swz_obj?_root, hra1'.root, hr1]
      split <;> rfl
    have hra2 : RootAt (m1.swz hp y h1) (if hp = m.root then oe.setSlot y (Slot.mem h1) else oe) :=
      ⟨hroot2, by simp only [swz_next, swz_root', hr1]; exact hfr1⟩
    have hc2 : (if hp = m.root then oc.setSlot y (Slot.mem h1) else oc).canonical =
        (if hp = m.root then oe.setSlot y (Slot.mem h1) else oe).canonical := by
      split <;> simp [Obj.setSlot, hc]
    have hsr : (m1.swz hp y h1).root = m.root := by rw [swz_root', hr1]
    cases w with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      refine ⟨?_, ?_, hsr, by rw [swz_next]; exact hfr1⟩
      · unfold rootAfter; split <;> rfl
      · have h2 := hroot2
        rw [hsr] at h2
        rw [h2]
        unfold rootAfter
        by_cases he : hp = m.root <;> simp [he]
    | true =>
      simp only [↓reduceIte]
      have hpick2 : ((m1.swz hp y h1).canonicalOf y).getD h1 ≠ (m1.swz hp y h1).root := by
        rw [hsr]; exact hpick rfl
      rw [promote_withRoot hra2 hc2 hp y h1 hpick2]
      refine ⟨?_, ?_, by rw [promote_root, hsr], by rw [promote_next, swz_next]; exact hfr1⟩
      · simp only [hsr, Prod.mk.injEq, and_true]
        congr 1
        unfold rootAfter Mem.promote
        by_cases he : hp = m.root
        · simp only [he, ↓reduceIte, Obj.setSlot_setSlot]
        · simp only [he, ↓reduceIte]
      · have h2 := hroot2
        rw [hsr] at h2
        have hpick3 : ((m1.swz hp y h1).canonicalOf y).getD h1 ≠ m.root := hpick rfl
        have h3 := promote_obj?_root (m1.swz hp y h1) hp y h1 hpick2
        rw [hsr] at h3
        rw [h3, h2]
        unfold rootAfter
        by_cases he : hp = m.root
        · simp only [he, ↓reduceIte, Option.map_some, Obj.setSlot_setSlot]
        · simp only [he, ↓reduceIte]


/-! ## The root apart from the other objects -/

/-- The root's object is of the root's node, at a handle below `next`; no
memory slot for another node, no table entry of another node and no history
names the root. The loader keeps it on any stream that has no version pointing
to the root (`StreamNR`). -/
structure RootSep (sp : Spec V T) (m : Mem V) : Prop where
  rootNode : ∀ o, m.obj? m.root = some o → o.node = root
  fresh : m.root < m.next
  slotsNR : ∀ h o y h', m.obj? h = some o → o.slot? y = some (Slot.mem h') → y ≠ root → h' ≠ m.root
  tableNR : ∀ y h, m.tableOf y = some h → y ≠ root → h ≠ m.root
  ptrsNR : ∀ h o, m.obj? h = some o → ∀ y ∈ pointees sp o.hist, y ≠ root

/-- No version of the stream points to the root. -/
def StreamNR (sp : Spec V T) (S : Stream V T) : Prop :=
  ∀ r y w, S.versionAt r y = some w → ∀ z ∈ pointees sp w.hist, z ≠ root

theorem versionAt_node {S : Stream V T} {r : Nat} {y : NodeId} {w : Version V}
    (h : S.versionAt r y = some w) : w.node = y := by
  unfold Stream.versionAt at h
  split at h
  · have := List.find?_some h
    simpa using this
  · cases h

theorem reached4_root {hp : Nat} {y : NodeId} {m1 : Mem V} {h1 : Nat}
    (h : m.reached4 sp S0 S hp y = some (m1, h1)) : m1.root = m.root := by
  obtain ⟨op, sl, -, -, hcase⟩ := reached4_cases h
  rcases hcase with ⟨-, rfl, -⟩ | ⟨-, -, -, rfl⟩ | ⟨-, -, -, -, -, -, -, rfl, -⟩ <;> rfl

theorem RootSep.reached4 (hrs : RootSep sp m) (hS : StreamNR sp S) {hp : Nat} {y : NodeId}
    (hy : y ≠ root) {m1 : Mem V} {h1 : Nat} (h : m.reached4 sp S0 S hp y = some (m1, h1)) :
    RootSep sp m1 ∧ h1 ≠ m.root ∧ m1.root = m.root ∧ m1.obj? m.root = m.obj? m.root ∧
      m1.next ≠ m.root ∧ m1.tableOf = m.tableOf := by
  obtain ⟨op, sl, hop, hsl, hcase⟩ := reached4_cases h
  have hnr : m.root ≠ m.next := by have := hrs.fresh; omega
  rcases hcase with ⟨hsl', hm1, -⟩ | ⟨r, hsl', hcy, hm1⟩ | ⟨r, r', w, hsl', hcy, hr, hw, hm1, hh1⟩
  · subst hsl' hm1
    exact ⟨hrs, hrs.slotsNR hp op y h1 hop hsl hy, rfl, rfl, Ne.symm hnr, rfl⟩
  · subst hsl' hm1
    obtain ⟨ht, -⟩ := (Mem.canonicalOf_eq_some _ y h1).mp hcy
    exact ⟨hrs, hrs.tableNR y h1 ht hy, rfl, rfl, Ne.symm hnr, rfl⟩
  · subst hm1 hh1
    have hobj : ∀ h', (m.addObj (Obj.ofVersion sp w none)).1.obj? h' =
        if h' = m.next then some (Obj.ofVersion sp w none) else m.obj? h' := Mem.obj?_addObj _ _
    obtain ⟨f1, -, -, f4, -, -⟩ := Obj.ofVersion_fields sp w none
    refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, Ne.symm hnr, rfl, ?_, ?_, rfl⟩
    · intro o ho
      rw [Mem.addObj_root, hobj] at ho
      simp only [hnr, ↓reduceIte] at ho
      exact hrs.rootNode o ho
    · show m.root < m.next + 1
      have := hrs.fresh; omega
    · intro h' o' z h'' ho' hz hzr
      rw [hobj] at ho'
      split at ho'
      · simp only [Option.some.injEq] at ho'
        subst ho'
        rw [Obj.ofVersion_slot?] at hz
        split at hz <;> simp at hz
      · exact hrs.slotsNR h' o' z h'' ho' hz hzr
    · intro z h' ht hz
      exact hrs.tableNR z h' (by rw [Mem.tableOf_addObj] at ht; exact ht) hz
    · intro h' o' ho' z hz
      rw [hobj] at ho'
      split at ho'
      · simp only [Option.some.injEq] at ho'
        subst ho'
        rw [f4] at hz
        exact hS r' y w hw z (by simpa [cutHist] using hz)
      · exact hrs.ptrsNR h' o' ho' z hz
    · rw [hobj]; simp [hnr]
    · show m.next + 1 ≠ m.root
      have := hrs.fresh; omega

theorem swz_canonicalOf (m : Mem V) (hp : Nat) (y : NodeId) (h1 : Nat) (z : NodeId) :
    (m.swz hp y h1).canonicalOf z = m.canonicalOf z := by
  unfold Mem.swz
  cases hop : m.obj? hp with
  | none => rfl
  | some op =>
    simp only
    unfold Mem.canonicalOf
    rw [Mem.tableOf_setObj]
    cases m.tableOf z with
    | none => rfl
    | some h =>
      simp only
      by_cases he : h = hp
      · subst he
        rw [Mem.obj?_setObj_self, hop]
        rfl
      · rw [Mem.obj?_setObj_ne _ _ he]

theorem RootSep.swz (hrs : RootSep sp m) {hp : Nat} {y : NodeId} {h1 : Nat}
    (hh1 : y ≠ root → h1 ≠ m.root) : RootSep sp (m.swz hp y h1) := by
  unfold Mem.swz
  cases hop : m.obj? hp with
  | none => exact hrs
  | some op =>
    simp only
    refine ⟨?_, hrs.fresh, ?_, hrs.tableNR, ?_⟩
    · intro o ho
      rw [Mem.setObj_root, Mem.obj?_setObj] at ho
      split at ho
      · rename_i he
        simp only [Option.some.injEq] at ho
        subst ho
        rw [Obj.setSlot_node]
        exact hrs.rootNode op (by rw [he]; exact hop)
      · exact hrs.rootNode o ho
    · intro h o z h' ho hz hzr
      rw [Mem.setObj_root]
      rw [Mem.obj?_setObj] at ho
      split at ho
      · simp only [Option.some.injEq] at ho
        subst ho
        rw [Obj.slot?_setSlot] at hz
        split at hz
        · rename_i hzy
          subst hzy
          cases hs : op.slot? z with
          | none => rw [hs] at hz; cases hz
          | some sl0 =>
            rw [hs] at hz
            simp only [Option.map_some, Option.some.injEq, Slot.mem.injEq] at hz
            subst hz
            exact hh1 hzr
        · exact hrs.slotsNR hp op z h' hop hz hzr
      · exact hrs.slotsNR h o z h' ho hz hzr
    · intro h o ho z hz
      rw [Mem.obj?_setObj] at ho
      split at ho
      · simp only [Option.some.injEq] at ho
        subst ho
        rw [Obj.setSlot_hist] at hz
        exact hrs.ptrsNR hp op hop z hz
      · exact hrs.ptrsNR h o ho z hz

theorem RootSep.promote (hrs : RootSep sp m) {hp : Nat} {y : NodeId} {h : Nat}
    (hpick : y ≠ root → (m.canonicalOf y).getD h ≠ m.root) :
    RootSep sp (m.promote hp y h).1 ∧ (y ≠ root → (m.promote hp y h).2 ≠ m.root) := by
  unfold Mem.promote
  dsimp only
  generalize hpk : (m.canonicalOf y).getD h = pick at hpick ⊢
  refine ⟨?_, fun hy => hpick hy⟩
  cases hpo : m.obj? pick with
  | none =>
    simp only
    exact (RootSep.swz hrs (hp := hp) (y := y) (h1 := pick) hpick : RootSep sp (Mem.swz m hp y pick))
  | some o =>
    simp only
    have hrs1 : RootSep sp ((m.setObj pick { o with canonical := true }).setTable y pick) := by
      refine ⟨?_, hrs.fresh, ?_, ?_, ?_⟩
      · intro o' ho'
        rw [Mem.setTable_root, Mem.setObj_root, Mem.obj?_setTable, Mem.obj?_setObj] at ho'
        split at ho'
        · rename_i he
          simp only [Option.some.injEq] at ho'
          subst ho'
          exact hrs.rootNode o (by rw [he]; exact hpo)
        · exact hrs.rootNode o' ho'
      · intro h' o' z h'' ho' hz hzr
        rw [Mem.obj?_setTable, Mem.obj?_setObj] at ho'
        split at ho'
        · simp only [Option.some.injEq] at ho'
          subst ho'
          exact hrs.slotsNR pick o z h'' hpo hz hzr
        · exact hrs.slotsNR h' o' z h'' ho' hz hzr
      · intro z h' ht hz
        rw [Mem.tableOf_setTable] at ht
        split at ht
        · rename_i hzy
          subst hzy
          simp only [Option.some.injEq] at ht
          subst ht
          exact hpick hz
        · exact hrs.tableNR z h' (by rw [Mem.tableOf_setObj] at ht; exact ht) hz
      · intro h' o' ho' z hz
        rw [Mem.obj?_setTable, Mem.obj?_setObj] at ho'
        split at ho'
        · simp only [Option.some.injEq] at ho'
          subst ho'
          exact hrs.ptrsNR pick o hpo z hz
        · exact hrs.ptrsNR h' o' ho' z hz
    exact (RootSep.swz hrs1 (hp := hp) (y := y) (h1 := pick) hpick :
      RootSep sp (Mem.swz ((m.setObj pick { o with canonical := true }).setTable y pick) hp y pick))

/-- What `follow4_withRoot` asks of the follow, from `RootSep`. -/
theorem RootSep.side (hrs : RootSep sp m) (hS : StreamNR sp S) {hp : Nat} {y : NodeId} (hy : y ≠ root)
    (hra : m.obj? m.root = some oe) (w : Bool) :
    ∀ m1 h1, m.reached4 sp S0 S hp y = some (m1, h1) → m1.root = m.root ∧ m1.obj? m.root = some oe ∧
      m1.next ≠ m.root ∧ (w = true → ((m1.swz hp y h1).canonicalOf y).getD h1 ≠ m.root) := by
  intro m1 h1 hrc
  obtain ⟨hrs1, hh1, hr1, ho1, hn1, ht1⟩ := hrs.reached4 hS hy hrc
  refine ⟨hr1, by rw [ho1]; exact hra, hn1, fun _ => ?_⟩
  rw [swz_canonicalOf]
  cases hc : m1.canonicalOf y with
  | none => exact hh1
  | some h0 =>
    simp only [Option.getD_some]
    obtain ⟨ht, -⟩ := (Mem.canonicalOf_eq_some _ y h0).mp hc
    have := hrs1.tableNR y h0 ht hy
    rw [hr1] at this
    exact this

/-- The follow keeps `RootSep`, and never gives the root's handle. -/
theorem RootSep.follow4 (hrs : RootSep sp m) (hS : StreamNR sp S) {hp : Nat} {y : NodeId} (hy : y ≠ root)
    (w : Bool) :
    RootSep sp (m.follow4 sp S0 S hp y w).1 ∧ (∀ h1, (m.follow4 sp S0 S hp y w).2 = some h1 → h1 ≠ m.root) ∧
      (m.follow4 sp S0 S hp y w).1.root = m.root := by
  rw [follow4_eq]
  cases hrc : m.reached4 sp S0 S hp y with
  | none =>
    simp only
    exact ⟨hrs, fun _ h => absurd h (by simp), trivial⟩
  | some p =>
    obtain ⟨m1, h1⟩ := p
    obtain ⟨hrs1, hh1, hr1, -, -, -⟩ := hrs.reached4 hS hy hrc
    have hrs2 := RootSep.swz hrs1 (hp := hp) (y := y) (h1 := h1) (fun _ => by rw [hr1]; exact hh1)
    have hr2 : (m1.swz hp y h1).root = m.root := by rw [swz_root', hr1]
    cases w with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact ⟨hrs2, fun h' he => by cases he; exact hh1, hr2⟩
    | true =>
      simp only [↓reduceIte]
      have hpick : y ≠ root → ((m1.swz hp y h1).canonicalOf y).getD h1 ≠ (m1.swz hp y h1).root := by
        intro _
        rw [swz_canonicalOf, hr2]
        cases hc : m1.canonicalOf y with
        | none => exact hh1
        | some h0 =>
          simp only [Option.getD_some]
          obtain ⟨ht, -⟩ := (Mem.canonicalOf_eq_some _ y h0).mp hc
          have := hrs1.tableNR y h0 ht hy
          rw [hr1] at this
          exact this
      obtain ⟨hrs3, hp3⟩ := hrs2.promote hpick
      refine ⟨hrs3, fun h' he => ?_, by rw [promote_root, hr2]⟩
      cases he
      have := hp3 hy
      rw [hr2] at this
      exact this

theorem rootAfter_ne {hp root : Nat} (hne : hp ≠ root) (y : NodeId) (r : Option Nat) (o : Obj V) :
    rootAfter hp root y r o = o := by
  unfold rootAfter; simp [hne]

theorem rootAfter_hist (hp root : Nat) (y : NodeId) (r : Option Nat) (o : Obj V) :
    (rootAfter hp root y r o).hist = o.hist := by
  unfold rootAfter; split
  · split <;> rfl
  · rfl

theorem readStep4_level (S0 S : Stream V T) (fuel : Nat) (t : Time) (h : Nat) {o o' : Obj V}
    (hl : o.level = o'.level) : readStep4 sp S0 S fuel t h o = readStep4 sp S0 S fuel t h o' := by
  funext acc y
  unfold readStep4
  rw [hl]

/-- A read from an object other than the root's, on the memory with the other
root object: the same, and the root's object stays. -/
theorem readAt4_withRoot (hls : LiveSub sp) (hS : StreamNR sp S) (hc : oc.canonical = oe.canonical) :
    ∀ (fuel : Nat) (m : Mem V) (t : Time) (h : Nat), RootSep sp m → m.obj? m.root = some oe → h ≠ m.root →
      (m.withRoot oc).readAt4 sp S0 S fuel t h =
        ((m.readAt4 sp S0 S fuel t h).1.withRoot oc, (m.readAt4 sp S0 S fuel t h).2) ∧
      RootSep sp (m.readAt4 sp S0 S fuel t h).1 ∧ (m.readAt4 sp S0 S fuel t h).1.obj? m.root = some oe ∧
      (m.readAt4 sp S0 S fuel t h).1.root = m.root := by
  intro fuel
  induction fuel with
  | zero =>
    intro m t h hrs hra _
    refine ⟨?_, hrs, ?_, ?_⟩ <;> simp [Mem.readAt4, hra]
  | succ fuel ih =>
    intro m t h hrs hra hne
    cases ho : m.obj? h with
    | none =>
      have ho' : (m.withRoot oc).obj? h = none := by rw [withRoot_obj?_ne hne, ho]
      simp only [Mem.readAt4, ho, ho']
      exact ⟨trivial, hrs, hra, trivial⟩
    | some o =>
      have ho' : (m.withRoot oc).obj? h = some o := by rw [withRoot_obj?_ne hne, ho]
      rw [readAt4_succ_eq sp S0 S fuel m t h ho, readAt4_succ_eq sp S0 S fuel (m.withRoot oc) t h ho']
      have hlive : ∀ y ∈ sp.live (o.hist.upTo t), y ≠ root :=
        fun y hy => hrs.ptrsNR h o ho y (mem_pointees_of_live hls hy)
      generalize sp.live (o.hist.upTo t) = L at hlive
      have key : ∀ (L : List NodeId), (∀ y ∈ L, y ≠ root) →
          ∀ (ma : Mem V) (l : List (NodeId × Node V)), RootSep sp ma → ma.obj? m.root = some oe →
            ma.root = m.root →
            L.foldl (readStep4 sp S0 S fuel t h o) (ma.withRoot oc, l) =
              ((L.foldl (readStep4 sp S0 S fuel t h o) (ma, l)).1.withRoot oc,
                (L.foldl (readStep4 sp S0 S fuel t h o) (ma, l)).2) ∧
            RootSep sp (L.foldl (readStep4 sp S0 S fuel t h o) (ma, l)).1 ∧
            (L.foldl (readStep4 sp S0 S fuel t h o) (ma, l)).1.obj? m.root = some oe ∧
            (L.foldl (readStep4 sp S0 S fuel t h o) (ma, l)).1.root = m.root := by
        intro L
        induction L with
        | nil => intro _ ma l hrs' hra' hr'; exact ⟨rfl, hrs', hra', hr'⟩
        | cons y L ihL =>
          intro hL ma l hrs' hra' hr'
          simp only [List.foldl_cons]
          have hy : y ≠ root := hL y List.mem_cons_self
          have hne' : h ≠ ma.root := by rw [hr']; exact hne
          have hra'' : ma.obj? ma.root = some oe := by rw [hr']; exact hra'
          obtain ⟨hf, hfo, hfr, -⟩ := follow4_withRoot (oc := oc) ⟨hra'', by have := hrs'.fresh; omega⟩ hc
            (Or.inl hne') false (hrs'.side hS hy hra'' false)
          obtain ⟨hrs1, hh1, hr1⟩ := hrs'.follow4 (S0 := S0) hS hy (hp := h) false
          rw [rootAfter_ne hne'] at hf hfo
          have hstep : readStep4 sp S0 S fuel t h o (ma.withRoot oc, l) y =
              ((readStep4 sp S0 S fuel t h o (ma, l) y).1.withRoot oc, (readStep4 sp S0 S fuel t h o (ma, l) y).2) ∧
              RootSep sp (readStep4 sp S0 S fuel t h o (ma, l) y).1 ∧
              (readStep4 sp S0 S fuel t h o (ma, l) y).1.obj? m.root = some oe ∧
              (readStep4 sp S0 S fuel t h o (ma, l) y).1.root = m.root := by
            unfold readStep4
            simp only
            rw [hf]
            rw [hr'] at hfo hh1
            generalize hF : ma.follow4 sp S0 S h y false = F at hfo hrs1 hh1 hr1
            obtain ⟨m1, r⟩ := F
            simp only at hfo hrs1 hh1 hr1 ⊢
            rw [hr'] at hr1
            cases r with
            | none => exact ⟨rfl, hrs1, hfo, hr1⟩
            | some h1 =>
              simp only
              have hh1' : h1 ≠ m1.root := by rw [hr1]; exact hh1 h1 rfl
              rw [withRoot_obj?_ne hh1']
              cases ho1 : m1.obj? h1 with
              | none => exact ⟨rfl, hrs1, hfo, hr1⟩
              | some o1 =>
                simp only
                split
                · have hfo' : m1.obj? m1.root = some oe := by rw [hr1]; exact hfo
                  obtain ⟨e1, e2, e3, e4⟩ := ih m1 t h1 hrs1 hfo' hh1'
                  rw [e1]
                  rw [hr1] at e3 e4
                  exact ⟨rfl, e2, e3, e4⟩
                · exact ⟨rfl, hrs1, hfo, hr1⟩
          obtain ⟨s1, s2, s3, s4⟩ := hstep
          rw [s1]
          exact ihL (fun z hz => hL z (List.mem_cons_of_mem _ hz)) _ _ s2 s3 s4
      exact key L hlive m _ hrs hra rfl

/-- A read from the root, from the first available time on, on the memory with
the other root object: the same reads below the root, and the root's node from
its own object; the two root objects change in the same way. -/
theorem read4_withRoot (hls : LiveSub sp) (hS : StreamNR sp S) {f t : Time} (hft : f ≤ t)
    (hrs : RootSep sp m) (hra : m.obj? m.root = some oe) (hr : RootRel sp f oc oe) :
    ∃ oc' oe', RootRel sp f oc' oe' ∧ oc'.hist = oc.hist ∧ oe'.hist = oe.hist ∧
      (m.read4 sp S0 S t).1.obj? m.root = some oe' ∧ RootSep sp (m.read4 sp S0 S t).1 ∧
      (m.read4 sp S0 S t).1.root = m.root ∧
      (m.withRoot oc).read4 sp S0 S t =
        ((m.read4 sp S0 S t).1.withRoot oc', (oc.node, oc.nodeAt t) :: (m.read4 sp S0 S t).2.tail) ∧
      (m.read4 sp S0 S t).2.head? = some (oe.node, oe.nodeAt t) := by
  have hoc : (m.withRoot oc).obj? (m.withRoot oc).root = some oc := by
    rw [withRoot_root]; exact withRoot_obj?_root hra
  have hra' : m.obj? m.root = some oe := hra
  unfold Mem.read4
  rw [hoc, hra']
  simp only
  rw [readAt4_succ_eq sp S0 S oc.level (m.withRoot oc) t _ hoc, readAt4_succ_eq sp S0 S oe.level m t _ hra',
    withRoot_root, hr.live t hft, hr.level, readStep4_level (sp := sp) S0 S oe.level t m.root hr.level]
  have hpts : ∀ y ∈ sp.live (oe.hist.upTo t), y ∈ pointees sp oc.hist ∧ y ≠ root := by
    intro y hy
    refine ⟨?_, hrs.ptrsNR m.root oe hra y (mem_pointees_of_live hls hy)⟩
    rw [← hr.live t hft] at hy
    exact mem_pointees_of_live hls hy
  generalize sp.live (oe.hist.upTo t) = L at hpts
  have key : ∀ (L : List NodeId), (∀ y ∈ L, y ∈ pointees sp oc.hist ∧ y ≠ root) →
      ∀ (ma : Mem V) (rest : List (NodeId × Node V)) (oc1 oe1 : Obj V), RootSep sp ma →
        ma.obj? m.root = some oe1 → ma.root = m.root → RootRel sp f oc1 oe1 → oc1.hist = oc.hist →
        oe1.hist = oe.hist →
        ∃ oc' oe', RootRel sp f oc' oe' ∧ oc'.hist = oc.hist ∧ oe'.hist = oe.hist ∧
          (L.foldl (readStep4 sp S0 S oe.level t m.root oe) (ma, (oe.node, oe.nodeAt t) :: rest)).1.obj? m.root =
            some oe' ∧
          RootSep sp (L.foldl (readStep4 sp S0 S oe.level t m.root oe) (ma, (oe.node, oe.nodeAt t) :: rest)).1 ∧
          (L.foldl (readStep4 sp S0 S oe.level t m.root oe) (ma, (oe.node, oe.nodeAt t) :: rest)).1.root = m.root ∧
          L.foldl (readStep4 sp S0 S oe.level t m.root oe) (ma.withRoot oc1, (oc.node, oc.nodeAt t) :: rest) =
            ((L.foldl (readStep4 sp S0 S oe.level t m.root oe) (ma, (oe.node, oe.nodeAt t) :: rest)).1.withRoot oc',
              (oc.node, oc.nodeAt t) ::
                (L.foldl (readStep4 sp S0 S oe.level t m.root oe) (ma, (oe.node, oe.nodeAt t) :: rest)).2.tail) ∧
          (L.foldl (readStep4 sp S0 S oe.level t m.root oe) (ma, (oe.node, oe.nodeAt t) :: rest)).2.head? =
            some (oe.node, oe.nodeAt t) := by
    intro L
    induction L with
    | nil =>
      intro _ ma rest oc1 oe1 hrs1 hra1 hr1 hrr1 hh1 hh1'
      exact ⟨oc1, oe1, hrr1, hh1, hh1', hra1, hrs1, hr1, rfl, rfl⟩
    | cons y L ihL =>
      intro hL ma rest oc1 oe1 hrs1 hra1 hr1 hrr1 hh1 hh1'
      simp only [List.foldl_cons]
      obtain ⟨hyp, hy⟩ := hL y List.mem_cons_self
      have hyp1 : y ∈ pointees sp oc1.hist := by rw [hh1]; exact hyp
      have hra1' : ma.obj? ma.root = some oe1 := by rw [hr1]; exact hra1
      obtain ⟨hf, hfo, hfr, -⟩ := follow4_withRoot (S0 := S0) (oc := oc1) ⟨hra1', by have := hrs1.fresh; omega⟩
        hrr1.canonical (Or.inr (hrr1.slots y hyp1)) false (hrs1.side (S0 := S0) hS hy hra1' false)
      obtain ⟨hrsF, hhF, hrF⟩ := hrs1.follow4 (S0 := S0) hS hy (hp := ma.root) false
      rw [hr1] at hf hfo hhF hrF hrsF
      generalize hF : ma.follow4 sp S0 S m.root y false = F at hf hfo hrsF hhF hrF
      obtain ⟨m1, r⟩ := F
      simp only at hf hfo hrsF hhF hrF
      have hrr2 : RootRel sp f (rootAfter m.root m.root y r oc1) (rootAfter m.root m.root y r oe1) :=
        hrr1.rootAfter (Or.inr (Or.inl hyp1)) r
      have hc2 : (rootAfter m.root m.root y r oc1).canonical = (rootAfter m.root m.root y r oe1).canonical := by
        rw [rootAfter_canonical, rootAfter_canonical]; exact hrr1.canonical
      have hh2 : (rootAfter m.root m.root y r oc1).hist = oc.hist := by rw [rootAfter_hist, hh1]
      have hh2' : (rootAfter m.root m.root y r oe1).hist = oe.hist := by rw [rootAfter_hist, hh1']
      have hstep : ∃ (ma2 : Mem V) (rest2 : List (NodeId × Node V)),
          readStep4 sp S0 S oe.level t m.root oe (ma, (oe.node, oe.nodeAt t) :: rest) y =
            (ma2, (oe.node, oe.nodeAt t) :: rest2) ∧
          readStep4 sp S0 S oe.level t m.root oe (ma.withRoot oc1, (oc.node, oc.nodeAt t) :: rest) y =
            (ma2.withRoot (rootAfter m.root m.root y r oc1), (oc.node, oc.nodeAt t) :: rest2) ∧
          RootSep sp ma2 ∧ ma2.obj? m.root = some (rootAfter m.root m.root y r oe1) ∧ ma2.root = m.root := by
        unfold readStep4
        rw [hf, hF]
        cases r with
        | none =>
          exact ⟨m1, rest, rfl, rfl, hrsF, hfo, hrF⟩
        | some h1 =>
          simp only
          have hh1ne : h1 ≠ m1.root := by rw [hrF]; exact hhF h1 rfl
          rw [withRoot_obj?_ne hh1ne]
          cases ho1 : m1.obj? h1 with
          | none => exact ⟨m1, rest, rfl, rfl, hrsF, hfo, hrF⟩
          | some o1 =>
            simp only
            split
            · have hfo' : m1.obj? m1.root = some (rootAfter m.root m.root y (some h1) oe1) := by
                rw [hrF]; exact hfo
              obtain ⟨e1, e2, e3, e4⟩ := readAt4_withRoot (S0 := S0) hls hS hc2 oe.level m1 t h1 hrsF hfo' hh1ne
              rw [e1]
              rw [hrF] at e3 e4
              exact ⟨_, rest ++ (m1.readAt4 sp S0 S oe.level t h1).2, rfl, rfl, e2, e3, e4⟩
            · exact ⟨m1, rest, rfl, rfl, hrsF, hfo, hrF⟩
      obtain ⟨ma2, rest2, e1, e2, e3, e4, e5⟩ := hstep
      rw [e1, e2]
      exact ihL (fun z hz => hL z (List.mem_cons_of_mem _ hz)) ma2 rest2 _ _ e3 e4 e5 hrr2 hh2 hh2'
  have := key L hpts m [] oc oe hrs hra rfl hr rfl rfl
  rw [hr.node] at this ⊢
  exact this

/-- The views of the two reads: the same but for the root's node. -/
theorem exec_rootSwap (hex : ExecRootOK sp) {tail : List (NodeId × Node V)} {nc ne : Node V}
    (hvc : sp.virt = true → ∀ e ∈ nc.hist, ∃ z, e.val = sp.rootVal z)
    (hve : sp.virt = true → ∀ e ∈ ne.hist, ∃ z, e.val = sp.rootVal z)
    (hl : sp.live nc.hist = sp.live ne.hist) (hnv : sp.virt = false → nc = ne) (tr : T) (i : Time) :
    sp.exec tr i (fun x => ((root, nc) :: tail).lookup x) = sp.exec tr i (fun x => ((root, ne) :: tail).lookup x) := by
  cases hv : sp.virt with
  | false => rw [hnv hv]
  | true =>
    apply hex hv tr i
    · intro n hn e he
      simp only [List.lookup, beq_self_eq_true, Option.some.injEq] at hn
      subst hn; exact hvc hv e he
    · intro n hn e he
      simp only [List.lookup, beq_self_eq_true, Option.some.injEq] at hn
      subst hn; exact hve hv e he
    · intro x hx
      have : (x == root) = false := by simp [hx]
      simp [List.lookup, this]
    · simp [List.lookup, hl]

theorem find?_congr_of_mem {α : Type} {l : List α} {p q : α → Bool} (h : ∀ a ∈ l, p a = q a) :
    l.find? p = l.find? q := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.find?_cons]
    rw [h a List.mem_cons_self, ih (fun b hb => h b (List.mem_cons_of_mem _ hb))]

/-- The writer reaches a node of its path the same way with a structure P' that
agrees with P on the live children of the path's nodes at j - 1. -/
theorem reachOnPath4_congrP {P P' : Struct V} {j : Time} {path : List NodeId}
    (hP : ∀ p ∈ path, (P'.get? p).map (fun n => sp.live (n.hist.upTo (j - 1))) =
      (P.get? p).map (fun n => sp.live (n.hist.upTo (j - 1)))) (m : Mem V) (x : NodeId) :
    m.reachOnPath4 sp S0 S P' j path x = m.reachOnPath4 sp S0 S P j path x := by
  unfold Mem.reachOnPath4
  simp only
  congr 1
  apply find?_congr_of_mem
  intro p hp
  have := hP p hp
  cases h1 : P'.get? p <;> cases h2 : P.get? p <;> rw [h1, h2] at this <;> simp at this
  all_goals first | rfl | (cases m.canonicalOf p <;> simp [this])

/-- The writer reaches a node of its path the same way on the memory with the
other root object. -/
theorem reachOnPath4_withRoot (hS : StreamNR sp S) {P : Struct V} {j f : Time} {path : List NodeId}
    (hPr : ∀ n, P.get? root = some n → ∀ x ∈ sp.live (n.hist.upTo (j - 1)), x ∈ pointees sp oc.hist)
    (hPnr : ∀ p n, P.get? p = some n → ∀ x ∈ sp.live (n.hist.upTo (j - 1)), x ≠ root)
    (hrs : RootSep sp m) (hra : m.obj? m.root = some oe) (hr : RootRel sp f oc oe) (x : NodeId) :
    ∃ oc' oe', RootRel sp f oc' oe' ∧ oc'.hist = oc.hist ∧ oe'.hist = oe.hist ∧
      (m.reachOnPath4 sp S0 S P j path x).obj? m.root = some oe' ∧ RootSep sp (m.reachOnPath4 sp S0 S P j path x) ∧
      (m.reachOnPath4 sp S0 S P j path x).root = m.root ∧
      (m.withRoot oc).reachOnPath4 sp S0 S P j path x = (m.reachOnPath4 sp S0 S P j path x).withRoot oc' := by
  have hcan : ∀ z, (m.withRoot oc).canonicalOf z = m.canonicalOf z := withRoot_canonicalOf hra hr.canonical
  unfold Mem.reachOnPath4
  simp only [hcan]
  split
  · rename_i p hfp
    have hpred := List.find?_some hfp
    split
    · rename_i hp hcp
      rw [hcp] at hpred
      cases hnp : P.get? p with
      | none => rw [hnp] at hpred; simp at hpred
      | some np =>
        rw [hnp] at hpred
        simp only [List.contains_iff_mem] at hpred
        have hx : x ≠ root := hPnr p np hnp x hpred
        obtain ⟨ht, -⟩ := (Mem.canonicalOf_eq_some _ p hp).mp hcp
        have hsl : hp ≠ m.root ∨ oc.slot? x = oe.slot? x ∧ x ∈ pointees sp oc.hist := by
          by_cases he : hp = m.root
          · right
            have hpr : p = root := by
              by_cases hne : p = root
              · exact hne
              · exact absurd he (hrs.tableNR p hp ht hne)
            subst hpr
            have hxo := hPr np hnp x hpred
            exact ⟨hr.slots x hxo, hxo⟩
          · left; exact he
        have hra' : RootAt m oe := ⟨hra, by have := hrs.fresh; omega⟩
        obtain ⟨hf, hfo, hfr, -⟩ := follow4_withRoot (S0 := S0) (oc := oc) hra' hr.canonical
          (hsl.imp id (fun h => h.1)) true (hrs.side (S0 := S0) hS hx hra true)
        obtain ⟨hrsF, -, hrF⟩ := hrs.follow4 (S0 := S0) hS hx (hp := hp) true
        refine ⟨_, _, hr.rootAfter (hsl.imp id (fun h => Or.inl h.2)) _, rootAfter_hist _ _ _ _ _,
          rootAfter_hist _ _ _ _ _, hfo, hrsF, hrF, ?_⟩
        rw [hf]
    · exact ⟨oc, oe, hr, rfl, rfl, hra, hrs, rfl, rfl⟩
  · exact ⟨oc, oe, hr, rfl, rfl, hra, hrs, rfl, rfl⟩

/-- The writer's walk on the memory with the other root object. -/
theorem reachPath4_withRoot (hS : StreamNR sp S) {P : Struct V} {j f : Time} {path : List NodeId}
    (hPnr : ∀ p n, P.get? p = some n → ∀ x ∈ sp.live (n.hist.upTo (j - 1)), x ≠ root) :
    ∀ (L : List NodeId) (m : Mem V) (oc oe : Obj V),
      (∀ n, P.get? root = some n → ∀ x ∈ sp.live (n.hist.upTo (j - 1)), x ∈ pointees sp oc.hist) →
      RootSep sp m → m.obj? m.root = some oe → RootRel sp f oc oe →
      ∃ oc' oe', RootRel sp f oc' oe' ∧ oc'.hist = oc.hist ∧ oe'.hist = oe.hist ∧
        (L.foldl (Mem.reachOnPath4 sp S0 S P j path) m).obj? m.root = some oe' ∧
        RootSep sp (L.foldl (Mem.reachOnPath4 sp S0 S P j path) m) ∧
        (L.foldl (Mem.reachOnPath4 sp S0 S P j path) m).root = m.root ∧
        L.foldl (Mem.reachOnPath4 sp S0 S P j path) (m.withRoot oc) =
          (L.foldl (Mem.reachOnPath4 sp S0 S P j path) m).withRoot oc' := by
  intro L
  induction L with
  | nil => intro m oc oe _ hrs hra hr; exact ⟨oc, oe, hr, rfl, rfl, hra, hrs, rfl, rfl⟩
  | cons x L ih =>
    intro m oc oe hPr hrs hra hr
    simp only [List.foldl_cons]
    obtain ⟨oc1, oe1, hr1, hh1, hh1', ho1, hrs1, hrt1, he1⟩ :=
      reachOnPath4_withRoot (S0 := S0) (path := path) hS hPr hPnr hrs hra hr x
    rw [he1]
    have hra1 : (m.reachOnPath4 sp S0 S P j path x).obj? (m.reachOnPath4 sp S0 S P j path x).root = some oe1 := by
      rw [hrt1]; exact ho1
    obtain ⟨oc2, oe2, hr2, hh2, hh2', ho2, hrs2, hrt2, he2⟩ :=
      ih _ oc1 oe1 (by rw [hh1]; exact hPr) hrs1 hra1 hr1
    rw [hrt1] at ho2 hrt2
    exact ⟨oc2, oe2, hr2, by rw [hh2, hh1], by rw [hh2', hh1'], ho2, hrs2, hrt2, he2⟩

theorem reachPath4_congrP {P P' : Struct V} {j : Time} {path : List NodeId}
    (hP : ∀ p ∈ path, (P'.get? p).map (fun n => sp.live (n.hist.upTo (j - 1))) =
      (P.get? p).map (fun n => sp.live (n.hist.upTo (j - 1)))) :
    ∀ (L : List NodeId) (m : Mem V),
      L.foldl (Mem.reachOnPath4 sp S0 S P' j path) m = L.foldl (Mem.reachOnPath4 sp S0 S P j path) m := by
  intro L
  induction L with
  | nil => intro m; rfl
  | cons x L ih =>
    intro m
    simp only [List.foldl_cons]
    rw [reachOnPath4_congrP hP m x, ih]

/-! ## The change -/

section Change

variable {P P' : Struct V} {j : Time}

theorem srcOK4_congrP (hReach : ∀ x, reachable sp P' (j - 1) x = reachable sp P (j - 1) x)
    (hProot : (P'.get? root).map (fun n => sp.live (n.hist.upTo (j - 1))) =
      (P.get? root).map (fun n => sp.live (n.hist.upTo (j - 1)))) (y : NodeId) (p : Nat × Obj V) :
    srcOK4 sp P' j y p = srcOK4 sp P j y p := by
  unfold srcOK4
  rw [hReach]
  by_cases hn : p.2.node = root
  · rw [hn]
    cases h1 : P'.get? root <;> cases h2 : P.get? root <;> rw [h1, h2] at hProot <;> simp at hProot
    all_goals first | rfl | simp [hProot]
  · simp [written_of_ne_root sp hn]

theorem srcOK4_rootRel {f : Time} (hReach : ∀ x, reachable sp P' (j - 1) x = reachable sp P (j - 1) x)
    (hProot : (P'.get? root).map (fun n => sp.live (n.hist.upTo (j - 1))) =
      (P.get? root).map (fun n => sp.live (n.hist.upTo (j - 1))))
    (hPr : ∀ n, P.get? root = some n → ∀ y ∈ sp.live (n.hist.upTo (j - 1)),
      y ∈ pointees sp oc.hist ∧ y ∈ pointees sp oe.hist)
    (hr : RootRel sp f oc oe) (hnode : oe.node = root) (y : NodeId) (r : Nat) :
    srcOK4 sp P' j y (r, oc) = srcOK4 sp P j y (r, oe) ∧
      (srcOK4 sp P j y (r, oe) = true → oc.slot? y = oe.slot? y) := by
  cases hv : sp.virt with
  | false =>
    rw [hr.nv hv]
    exact ⟨srcOK4_congrP hReach hProot y _, fun _ => rfl⟩
  | true =>
    have hnc : oc.node = root := by rw [hr.node]; exact hnode
    have hw : written sp root = false := by simp [written, hv]
    unfold srcOK4
    simp only [hnc, hnode, hw, Bool.false_or, hReach]
    cases h2 : P.get? root with
    | none =>
      have h1 : P'.get? root = none := by
        rw [h2] at hProot; cases h1 : P'.get? root <;> rw [h1] at hProot <;> simp at hProot ⊢
      rw [h1]; simp
    | some n =>
      obtain ⟨n', h1, hl⟩ : ∃ n', P'.get? root = some n' ∧
          sp.live (n'.hist.upTo (j - 1)) = sp.live (n.hist.upTo (j - 1)) := by
        rw [h2] at hProot
        cases h1 : P'.get? root <;> rw [h1] at hProot <;> simp at hProot
        exact ⟨_, rfl, hProot⟩
      rw [h1]
      simp only [hl]
      by_cases hy : y ∈ sp.live (n.hist.upTo (j - 1))
      · obtain ⟨hyc, hye⟩ := hPr n h2 y hy
        have hs := hr.slots y hyc
        refine ⟨?_, fun _ => hs⟩
        rw [hs, hr.canonical]
        simp [hyc, hye]
      · exact ⟨by simp [hy], fun h => by simp [hy] at h⟩

theorem srcSlot4_withRoot {f : Time} (hReach : ∀ x, reachable sp P' (j - 1) x = reachable sp P (j - 1) x)
    (hProot : (P'.get? root).map (fun n => sp.live (n.hist.upTo (j - 1))) =
      (P.get? root).map (fun n => sp.live (n.hist.upTo (j - 1))))
    (hPr : ∀ n, P.get? root = some n → ∀ y ∈ sp.live (n.hist.upTo (j - 1)),
      y ∈ pointees sp oc.hist ∧ y ∈ pointees sp oe.hist)
    (hnd : (m.objs.map (·.1)).Nodup) (hra : m.obj? m.root = some oe) (hr : RootRel sp f oc oe)
    (hnode : oe.node = root) (y : NodeId) :
    srcSlot4 sp P' j (m.withRoot oc) y = srcSlot4 sp P j m y := by
  unfold srcSlot4 Mem.withRoot
  simp only
  rw [List.find?_map]
  have hcongr : m.objs.find? (srcOK4 sp P' j y ∘ (fun p => if p.1 == m.root then (m.root, oc) else p)) =
      m.objs.find? (srcOK4 sp P j y) := by
    apply find?_congr_of_mem
    intro p hp
    simp only [Function.comp]
    by_cases he : p.1 = m.root
    · have hpo : p.2 = oe := by
        have := obj?_of_mem_objs hnd hp
        rw [he, hra] at this
        exact (Option.some.inj this).symm
      obtain ⟨a, b⟩ := p
      simp only at he hpo
      subst he hpo
      simp only [beq_self_eq_true, ↓reduceIte]
      exact (srcOK4_rootRel hReach hProot hPr hr hnode y _).1
    · have : (p.1 == m.root) = false := by simp [he]
      simp only [this, Bool.false_eq_true, ↓reduceIte]
      exact srcOK4_congrP hReach hProot y p
  rw [hcongr]
  cases hf : m.objs.find? (srcOK4 sp P j y) with
  | none => rfl
  | some p =>
    simp only [Option.map_some, Option.bind_some]
    by_cases he : p.1 = m.root
    · have hp := List.mem_of_find?_eq_some hf
      have hpo : p.2 = oe := by
        have := obj?_of_mem_objs hnd hp
        rw [he, hra] at this
        exact (Option.some.inj this).symm
      have hsrc := List.find?_some hf
      obtain ⟨a, b⟩ := p
      simp only at he hpo hsrc
      subst he hpo
      simp only [beq_self_eq_true, ↓reduceIte]
      exact (srcOK4_rootRel hReach hProot hPr hr hnode y _).2 hsrc
    · have : (p.1 == m.root) = false := by simp [he]
      simp only [this, Bool.false_eq_true, ↓reduceIte]

theorem NS4_withRoot {f : Time} (hReach : ∀ x, reachable sp P' (j - 1) x = reachable sp P (j - 1) x)
    (hProot : (P'.get? root).map (fun n => sp.live (n.hist.upTo (j - 1))) =
      (P.get? root).map (fun n => sp.live (n.hist.upTo (j - 1))))
    (hPr : ∀ n, P.get? root = some n → ∀ y ∈ sp.live (n.hist.upTo (j - 1)),
      y ∈ pointees sp oc.hist ∧ y ∈ pointees sp oe.hist)
    (hnd : (m.objs.map (·.1)).Nodup) (hra : m.obj? m.root = some oe) (hr : RootRel sp f oc oe)
    (hnode : oe.node = root) (y : NodeId) :
    NS4 sp P' j (m.withRoot oc) y = NS4 sp P j m y := by
  unfold NS4
  rw [withRoot_canonicalOf hra hr.canonical, srcSlot4_withRoot hReach hProot hPr hnd hra hr hnode]

theorem updObj4_congr {m1 m1' : Mem V} (hns : ∀ y, NS4 sp P' j m1' y = NS4 sp P j m1 y) (o : Obj V) (v : V) :
    updObj4 sp P' j m1' o v = updObj4 sp P j m1 o v := by
  unfold updObj4
  generalize ({ o with hist := o.hist ++ [⟨j, v⟩] } : Obj V) = o1
  induction (sp.ptrs v) generalizing o1 with
  | nil => rfl
  | cons y L ih =>
    simp only [List.foldl_cons]
    have : upd14 sp P' j m1' o1 y = upd14 sp P j m1 o1 y := by
      unfold upd14
      rw [newSlot4_eq, newSlot4_eq, hns y]
    rw [this, ih]

theorem addNew_withRoot (hne : m.next ≠ m.root) (nn : NewNode) :
    addNew (m.withRoot oc) nn = (addNew m nn).withRoot oc := by
  unfold addNew
  rw [withRoot_addObj hne]
  simp only [withRoot_next]
  rfl

theorem foldl_addNew_withRoot (N : List NewNode) :
    ∀ (m : Mem V), m.root < m.next → N.foldl addNew (m.withRoot oc) = (N.foldl addNew m).withRoot oc := by
  induction N with
  | nil => intro m _; rfl
  | cons nn N ih =>
    intro m hlt
    simp only [List.foldl_cons]
    rw [addNew_withRoot (by omega)]
    exact ih _ (by show m.root < m.next + 1; omega)

theorem foldl_addNew_root (N : List NewNode) : ∀ (m : Mem V), (N.foldl addNew m).root = m.root := by
  induction N with
  | nil => intro m; rfl
  | cons nn N ih => intro m; simp only [List.foldl_cons]; rw [ih]; rfl

/-- A virtual root's new entry, for a new root child z, with the slot to z's
object, the same in both. -/
theorem RootRel.addRoot (hvl : VirtLiveOK sp) (hv : sp.virt = true) {f : Time} (hr : RootRel sp f oc oe)
    (hvalsE : ∀ e ∈ oe.hist, ∃ z, e.val = sp.rootVal z) {e : Entry V} {z : NodeId}
    (hez : e.val = sp.rootVal z) (hptr : sp.ptrs (sp.rootVal z) = [z]) (sl : Slot) :
    RootRel sp f ({ oc with hist := oc.hist ++ [e] }.putSlot z sl) ({ oe with hist := oe.hist ++ [e] }.putSlot z sl) := by
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := Obj.putSlot_fields ({ oc with hist := oc.hist ++ [e] }) z sl
  obtain ⟨b1, b2, b3, b4, b5, b6⟩ := Obj.putSlot_fields ({ oe with hist := oe.hist ++ [e] }) z sl
  have hmem : ∀ y, y ∈ pointees sp (oc.hist ++ [e]) → y ∈ pointees sp oc.hist ∨ y = z := by
    intro y hy
    rcases pointees_append_mem hy with h | h
    · exact Or.inl h
    · rw [mem_pointees] at h
      obtain ⟨e', he', hy'⟩ := h
      rw [List.mem_singleton.mp he', hez, hptr] at hy'
      exact Or.inr (List.mem_singleton.mp hy')
  refine ⟨fun h => absurd h (by simp [hv]), by rw [a1, b1]; exact hr.node, by rw [a2, b2]; exact hr.level,
    by rw [a3, b3]; exact hr.isData, by rw [a5, b5]; exact hr.canonical, by rw [a6, b6]; exact hr.pos, ?_, ?_,
    ?_, ?_, ?_⟩
  · intro t ht
    rw [a4, b4]
    simp only
    rw [upTo_append, upTo_append]
    by_cases het : e.time ≤ t
    · have h1 : History.upTo [e] t = [e] := by simp [History.upTo, het]
      rw [h1]
      have hvc : ∀ e' ∈ oc.hist.upTo t ++ [e], ∃ z, e'.val = sp.rootVal z := by
        intro e' he'
        rcases List.mem_append.mp he' with h | h
        · exact hr.vals hv e' (mem_upTo.mp h).1
        · rw [List.mem_singleton.mp h]; exact ⟨z, hez⟩
      have hve : ∀ e' ∈ oe.hist.upTo t ++ [e], ∃ z, e'.val = sp.rootVal z := by
        intro e' he'
        rcases List.mem_append.mp he' with h | h
        · exact hvalsE e' (mem_upTo.mp h).1
        · rw [List.mem_singleton.mp h]; exact ⟨z, hez⟩
      rw [hvl hv _ hvc, hvl hv _ hve]
      simp
    · have h1 : History.upTo [e] t = [] := by simp [History.upTo, het]
      rw [h1, List.append_nil, List.append_nil]
      exact hr.live t ht
  · intro y hy
    rw [a4] at hy
    simp only at hy
    rw [Obj.slot?_putSlot, Obj.slot?_putSlot]
    split
    · rfl
    · rename_i hyz
      rcases hmem y hy with h | h
      · exact hr.slots y h
      · exact absurd h hyz
  · intro _ y hy
    rw [a4] at hy
    simp only at hy
    rw [Obj.slot?_putSlot]
    split
    · rename_i hyz
      subst hyz
      exact absurd (by rw [mem_pointees]; exact ⟨e, by simp, by rw [hez, hptr]; simp⟩) hy
    · have : y ∉ pointees sp oc.hist := fun h =>
        hy (by rw [mem_pointees] at h ⊢; obtain ⟨e', he', h'⟩ := h; exact ⟨e', by simp [he'], h'⟩)
      exact hr.noSlot hv y this
  · intro _ e' he'
    rw [a4] at he'
    simp only at he'
    rcases List.mem_append.mp he' with h | h
    · exact hr.vals hv e' h
    · rw [List.mem_singleton.mp h]; exact ⟨z, hez⟩
  · intro _ y hy
    rw [b4]
    simp only
    rw [Obj.slot?_putSlot] at hy
    split at hy
    · rename_i hyz
      subst hyz
      rw [mem_pointees]; exact ⟨e, by simp, by rw [hez, hptr]; simp⟩
    · have := hr.keysE hv y hy
      rw [mem_pointees] at this ⊢
      obtain ⟨e', he', h'⟩ := this
      exact ⟨e', by simp [he'], h'⟩

/-- The change of a transaction on the memory with the other root object: the
same, and the root objects change in the same way. P' agrees with P on what is
reachable at j - 1 and on the root's live children then; with a virtual root,
the root's new entries are for new root children (`VirtStep`). -/
theorem applyChange4_withRoot (hvl : VirtLiveOK sp) {f : Time} {c : Changes V}
    (hReach : ∀ x, reachable sp P' (j - 1) x = reachable sp P (j - 1) x)
    (hProot : (P'.get? root).map (fun n => sp.live (n.hist.upTo (j - 1))) =
      (P.get? root).map (fun n => sp.live (n.hist.upTo (j - 1))))
    (hPr : ∀ n, P.get? root = some n → ∀ y ∈ sp.live (n.hist.upTo (j - 1)),
      y ∈ pointees sp oc.hist ∧ y ∈ pointees sp oe.hist)
    (hnd : (c.new.map (·.id)).Nodup)
    (hradds : sp.virt = true → ∀ a ∈ c.adds, a.1 = root → ∃ nn ∈ c.new, a.2 = sp.rootVal nn.id)
    (hptrs : sp.virt = true → ∀ z, sp.ptrs (sp.rootVal z) = [z])
    (hrs : RootSep sp m) (hnd' : (m.objs.map (·.1)).Nodup) (hfr : ∀ h, m.next ≤ h → m.obj? h = none)
    (hra : m.obj? m.root = some oe) (hr : RootRel sp f oc oe) (hnode : oe.node = root)
    (hvalsE : sp.virt = true → ∀ e ∈ oe.hist, ∃ z, e.val = sp.rootVal z) :
    ∃ oc' oe', RootRel sp f oc' oe' ∧ (m.applyChange4 sp P j c).obj? m.root = some oe' ∧
      (m.applyChange4 sp P j c).root = m.root ∧ oe'.node = root ∧
      (sp.virt = true → ∀ e ∈ oe'.hist, ∃ z, e.val = sp.rootVal z) ∧
      (∃ X, oc'.hist = oc.hist ++ X ∧ oe'.hist = oe.hist ++ X) ∧
      (m.withRoot oc).applyChange4 sp P' j c = (m.applyChange4 sp P j c).withRoot oc' := by
  rw [applyChange4_eq, applyChange4_eq, foldl_addNew_withRoot c.new m hrs.fresh]
  have hr1 : (c.new.foldl addNew m).root = m.root := foldl_addNew_root c.new m
  have hra1 : (c.new.foldl addNew m).obj? (c.new.foldl addNew m).root = some oe := by
    rw [hr1, foldl_addNew_old c.new m m.root hrs.fresh]; exact hra
  have hnd1 : ((c.new.foldl addNew m).objs.map (·.1)).Nodup := foldl_addNew_nodup c.new m hfr hnd'
  have htbl1 : ∀ y h, (c.new.foldl addNew m).tableOf y = some h → y ≠ root → h ≠ m.root := by
    intro y h ht hy
    by_cases hyn : y ∈ c.new.map (·.id)
    · obtain ⟨nn, hnn, rfl⟩ := List.mem_map.mp hyn
      obtain ⟨h', hle, ht', -⟩ := foldl_addNew_new c.new hnd m nn hnn
      rw [ht] at ht'
      cases ht'
      have := hrs.fresh; omega
    · rw [foldl_addNew_table_old c.new m y hyn] at ht
      exact hrs.tableNR y h ht hy
  have hns : ∀ y, NS4 sp P' j ((c.new.foldl addNew m).withRoot oc) y = NS4 sp P j (c.new.foldl addNew m) y :=
    NS4_withRoot hReach hProot hPr hnd1 hra1 hr hnode
  generalize hm1 : c.new.foldl addNew m = m1 at hr1 hra1 hnd1 htbl1 hns
  have hcanNew : ∀ nn ∈ c.new, ∃ hn, m1.canonicalOf nn.id = some hn := by
    intro nn hnn
    obtain ⟨hn, -, hc, -⟩ := addNew_canonicalOf_new m c.new hnd hnn
    rw [hm1] at hc
    exact ⟨hn, hc⟩
  have key : ∀ (L : List (NodeId × V)), (∀ a ∈ L, a ∈ c.adds) →
      ∀ (ma : Mem V) (oc1 oe1 : Obj V), ma.obj? m.root = some oe1 → ma.root = m.root → ma.table = m1.table →
        RootRel sp f oc1 oe1 → oe1.node = root → (sp.virt = true → ∀ e ∈ oe1.hist, ∃ z, e.val = sp.rootVal z) →
        ∃ oc' oe', RootRel sp f oc' oe' ∧ (L.foldl (addsStep4 sp P j m1) ma).obj? m.root = some oe' ∧
          (L.foldl (addsStep4 sp P j m1) ma).root = m.root ∧ oe'.node = root ∧
          (sp.virt = true → ∀ e ∈ oe'.hist, ∃ z, e.val = sp.rootVal z) ∧
          (∃ X, oc'.hist = oc1.hist ++ X ∧ oe'.hist = oe1.hist ++ X) ∧
          L.foldl (addsStep4 sp P' j (m1.withRoot oc)) (ma.withRoot oc1) =
            (L.foldl (addsStep4 sp P j m1) ma).withRoot oc' := by
    intro L
    induction L with
    | nil =>
      intro _ ma oc1 oe1 hra' hrt' _ hrr hn' hv'
      exact ⟨oc1, oe1, hrr, hra', hrt', hn', hv', ⟨[], by simp, by simp⟩, rfl⟩
    | cons a L ih =>
      intro hL ma oc1 oe1 hra' hrt' htb hrr hn' hv'
      simp only [List.foldl_cons]
      have hra'' : ma.obj? ma.root = some oe1 := by rw [hrt']; exact hra'
      have hstep : ∃ oc2 oe2, RootRel sp f oc2 oe2 ∧ (addsStep4 sp P j m1 ma a).obj? m.root = some oe2 ∧
          (addsStep4 sp P j m1 ma a).root = m.root ∧ (addsStep4 sp P j m1 ma a).table = m1.table ∧
          oe2.node = root ∧ (sp.virt = true → ∀ e ∈ oe2.hist, ∃ z, e.val = sp.rootVal z) ∧
          (∃ X, oc2.hist = oc1.hist ++ X ∧ oe2.hist = oe1.hist ++ X) ∧
          addsStep4 sp P' j (m1.withRoot oc) (ma.withRoot oc1) a = (addsStep4 sp P j m1 ma a).withRoot oc2 := by
        unfold addsStep4
        rw [withRoot_canonicalOf hra'' hrr.canonical]
        cases hca : ma.canonicalOf a.1 with
        | none => exact ⟨oc1, oe1, hrr, hra', hrt', htb, hn', hv', ⟨[], by simp, by simp⟩, rfl⟩
        | some h =>
          simp only
          by_cases hh : h = m.root
          · subst hh
            rw [← hrt', withRoot_obj?_root hra'', hra'']
            simp only
            rw [withRoot_setObj_root _ (updObj4 sp P j m1 oe1 a.2)]
            rw [updObj4_congr hns]
            have hroot' : (ma.setObj ma.root (updObj4 sp P j m1 oe1 a.2)).obj? ma.root =
                some (updObj4 sp P j m1 oe1 a.2) := Mem.obj?_setObj_self _ _ _
            obtain ⟨u1, -, -, u4, -, -⟩ := updObj4_core sp P j m1 oe1 a.2
            cases hv : sp.virt with
            | false =>
              rw [hrr.nv hv]
              exact ⟨_, _, RootRel.ofNV hv f _, hroot', rfl, by rw [Mem.setObj_table, htb],
                by rw [u1, hn'], fun h => absurd h (by simp), ⟨[⟨j, a.2⟩], u4, u4⟩, rfl⟩
            | true =>
              have ha1 : a.1 = root := by
                obtain ⟨ht, -⟩ := (Mem.canonicalOf_eq_some _ a.1 _).mp hca
                rw [Mem.tableOf, htb] at ht
                by_cases hne : a.1 = root
                · exact hne
                · exact absurd rfl (htbl1 a.1 _ ht hne)
              obtain ⟨nn, hnn, ha2⟩ := hradds hv a (hL a List.mem_cons_self) ha1
              obtain ⟨hn, hcn⟩ := hcanNew nn hnn
              have hpz := hptrs hv nn.id
              have hupd : ∀ o : Obj V, updObj4 sp P j m1 o a.2 =
                  ({ o with hist := o.hist ++ [⟨j, a.2⟩] } : Obj V).putSlot nn.id (Slot.mem hn) := by
                intro o
                unfold updObj4
                rw [ha2, hpz]
                simp only [List.foldl_cons, List.foldl_nil]
                unfold upd14
                rw [newSlot4_eq]
                unfold NS4
                rw [hcn]
                rfl
              rw [hupd oc1, hupd oe1]
              rw [hupd oe1] at hroot' u1 u4
              have hrr2 := hrr.addRoot hvl hv (hv' hv) (e := ⟨j, a.2⟩) (z := nn.id) ha2 hpz (Slot.mem hn)
              refine ⟨_, _, hrr2, hroot', rfl, by rw [Mem.setObj_table, htb], by rw [u1]; exact hn', ?_,
                ⟨[⟨j, a.2⟩], (Obj.putSlot_fields _ _ _).2.2.2.1, u4⟩, rfl⟩
              intro _ e he
              rw [u4] at he
              rcases List.mem_append.mp he with h1 | h1
              · exact hv' hv e h1
              · rw [List.mem_singleton.mp h1]; exact ⟨nn.id, ha2⟩
          · have hh' : h ≠ ma.root := by rw [hrt']; exact hh
            rw [withRoot_obj?_ne hh']
            cases hoh : ma.obj? h with
            | none => exact ⟨oc1, oe1, hrr, hra', hrt', htb, hn', hv', ⟨[], by simp, by simp⟩, rfl⟩
            | some o =>
              simp only
              rw [updObj4_congr hns, withRoot_setObj_ne hh']
              refine ⟨oc1, oe1, hrr, ?_, by rw [Mem.setObj_root, hrt'], by rw [Mem.setObj_table, htb], hn', hv',
                ⟨[], by simp, by simp⟩, rfl⟩
              rw [Mem.obj?_setObj_ne _ _ (fun he => hh he.symm)]
              exact hra'
      obtain ⟨oc2, oe2, hrr2, hra2, hrt2, htb2, hn2, hv2, ⟨X1, hx1, hx1'⟩, he2⟩ := hstep
      rw [he2]
      obtain ⟨oc3, oe3, h1, h2, h3, h4, h5, ⟨X2, hx2, hx2'⟩, h6⟩ :=
        ih (fun b hb => hL b (List.mem_cons_of_mem _ hb)) _ oc2 oe2 hra2 hrt2 htb2 hrr2 hn2 hv2
      exact ⟨oc3, oe3, h1, h2, h3, h4, h5, ⟨X1 ++ X2, by rw [hx2, hx1, List.append_assoc],
        by rw [hx2', hx1', List.append_assoc]⟩, h6⟩
  have hra1' : m1.obj? m.root = some oe := by rw [← hr1]; exact hra1
  exact key c.adds (fun a ha => ha) m1 oc oe hra1' hr1 rfl hr hnode hvalsE

/-! ## The physical writer -/

theorem refOf_withRoot {S0 : Stream V T} {D : Dirty} (hra : m.obj? m.root = some oe)
    (hpos : oc.pos = oe.pos) (hc : oc.canonical = oe.canonical) (o : Obj V) (y : NodeId) :
    (m.withRoot oc).refOf S0 D o y = m.refOf S0 D o y := by
  have hp : ∀ h', ((m.withRoot oc).obj? h').bind (·.pos) = (m.obj? h').bind (·.pos) := by
    intro h'
    by_cases he : h' = m.root
    · subst he; rw [withRoot_obj?_root hra, hra]; simp [hpos]
    · rw [withRoot_obj?_ne he]
  unfold Mem.refOf
  simp only [hp, withRoot_canonicalOf hra hc, withRoot_s]

theorem RootSep.writeNode (hrs : RootSep sp m) (S0 : Stream V T) (D : Dirty) (i : Nat) (x : NodeId) :
    RootSep sp (m.writeNode sp S0 D i x).1 := by
  cases hcx : m.canonicalOf x with
  | none => unfold Mem.writeNode; rw [hcx]; exact hrs
  | some h =>
    cases hoh : m.obj? h with
    | none => unfold Mem.writeNode; rw [hcx]; simp only [hoh]; exact hrs
    | some o =>
      rw [writeNode_shape sp S0 D i hcx hoh]
      simp only
      refine ⟨?_, hrs.fresh, ?_, hrs.tableNR, ?_⟩
      · intro o' ho'
        rw [Mem.setObj_root, Mem.obj?_setObj] at ho'
        split at ho'
        · rename_i he
          simp only [Option.some.injEq] at ho'
          subst ho'
          exact hrs.rootNode o (by rw [he]; exact hoh)
        · exact hrs.rootNode o' ho'
      · intro h' o' z h'' ho' hz hzr
        rw [Mem.setObj_root]
        rw [Mem.obj?_setObj] at ho'
        split at ho'
        · simp only [Option.some.injEq] at ho'
          subst ho'
          rw [slot?_of_pinSlots m D o rfl z] at hz
          cases hoz : o.slot? z with
          | none => rw [hoz] at hz; cases hz
          | some sl =>
            rw [hoz] at hz
            simp only [Option.map_some, Option.some.injEq] at hz
            split at hz
            · cases hcz : m.canonicalOf z with
              | none =>
                rw [hcz] at hz
                simp only at hz
                subst hz
                exact hrs.slotsNR h o z h'' hoh hoz hzr
              | some h0 =>
                rw [hcz] at hz
                simp only [Slot.mem.injEq] at hz
                subst hz
                obtain ⟨ht, -⟩ := (Mem.canonicalOf_eq_some _ z h0).mp hcz
                exact hrs.tableNR z h0 ht hzr
            · subst hz
              exact hrs.slotsNR h o z h'' hoh hoz hzr
        · exact hrs.slotsNR h' o' z h'' ho' hz hzr
      · intro h' o' ho' z hz
        rw [Mem.obj?_setObj] at ho'
        split at ho'
        · simp only [Option.some.injEq] at ho'
          subst ho'
          exact hrs.ptrsNR h o hoh z hz
        · exact hrs.ptrsNR h' o' ho' z hz

/-- Writing a node on the memory with the other root object: the same version,
and the same memory but for the root's object (written too, without a virtual
root). -/
theorem writeNode_withRoot {f : Time} {S0 : Stream V T} {D : Dirty} {i : Nat} (hrs : RootSep sp m)
    (hra : m.obj? m.root = some oe) (hr : RootRel sp f oc oe) {x : NodeId} (hx : x ≠ root ∨ sp.virt = false) :
    ∃ oc' oe', RootRel sp f oc' oe' ∧ oc'.hist = oc.hist ∧ oe'.hist = oe.hist ∧
      (m.writeNode sp S0 D i x).1.obj? m.root = some oe' ∧ (m.writeNode sp S0 D i x).1.root = m.root ∧
      (m.withRoot oc).writeNode sp S0 D i x =
        ((m.writeNode sp S0 D i x).1.withRoot oc', (m.writeNode sp S0 D i x).2) := by
  have hcan : ∀ z, (m.withRoot oc).canonicalOf z = m.canonicalOf z := withRoot_canonicalOf hra hr.canonical
  cases hcx : m.canonicalOf x with
  | none =>
    have hcx' : (m.withRoot oc).canonicalOf x = none := by rw [hcan]; exact hcx
    unfold Mem.writeNode
    rw [hcx, hcx']
    exact ⟨oc, oe, hr, rfl, rfl, hra, rfl, rfl⟩
  | some h =>
    have hcx' : (m.withRoot oc).canonicalOf x = some h := by rw [hcan]; exact hcx
    by_cases hh : h = m.root
    · subst hh
      have hxr : x = root := by
        obtain ⟨ht, -⟩ := (Mem.canonicalOf_eq_some _ x _).mp hcx
        by_cases hne : x = root
        · exact hne
        · exact absurd rfl (hrs.tableNR x _ ht hne)
      have hv : sp.virt = false := by
        rcases hx with hx | hv
        · exact absurd hxr hx
        · exact hv
      obtain rfl := hr.nv hv
      have hoc : (m.withRoot oc).obj? m.root = some oc := withRoot_obj?_root hra
      rw [writeNode_shape sp S0 D i hcx' hoc, writeNode_shape sp S0 D i hcx hra]
      simp only
      refine ⟨{ oc with pos := some i, slots := m.pinSlots D oc }, { oc with pos := some i, slots := m.pinSlots D oc },
        RootRel.ofNV hv f _, rfl, rfl, Mem.obj?_setObj_self _ _ _, rfl, ?_⟩
      have hpin : (m.withRoot oc).pinSlots D oc = m.pinSlots D oc := by
        unfold Mem.pinSlots; simp only [hcan]
      have hver : (m.withRoot oc).verOf sp S0 D i x oc = m.verOf sp S0 D i x oc := by
        unfold Mem.verOf; simp only [refOf_withRoot hra hr.pos hr.canonical]
      rw [hpin, hver, withRoot_setObj_root _ { oc with pos := some i, slots := m.pinSlots D oc }]
    · have hoh' : (m.withRoot oc).obj? h = m.obj? h := withRoot_obj?_ne hh
      cases hoh : m.obj? h with
      | none =>
        unfold Mem.writeNode
        rw [hcx, hcx']
        dsimp only
        rw [hoh', hoh]
        exact ⟨oc, oe, hr, rfl, rfl, hra, rfl, rfl⟩
      | some o =>
        rw [hoh] at hoh'
        rw [writeNode_shape sp S0 D i hcx' hoh', writeNode_shape sp S0 D i hcx hoh]
        simp only
        refine ⟨oc, oe, hr, rfl, rfl, by rw [Mem.obj?_setObj_ne _ _ (Ne.symm hh)]; exact hra, rfl, ?_⟩
        have hpin : (m.withRoot oc).pinSlots D o = m.pinSlots D o := by
          unfold Mem.pinSlots; simp only [hcan]
        have hver : (m.withRoot oc).verOf sp S0 D i x o = m.verOf sp S0 D i x o := by
          unfold Mem.verOf; simp only [refOf_withRoot hra hr.pos hr.canonical]
        rw [hpin, hver, withRoot_setObj_ne hh]

/-- The physical writer's loop on the memory with the other root object. -/
theorem writeNodes_withRoot {f : Time} {S0 : Stream V T} {D : Dirty} {i : Nat} :
    ∀ (xs : List NodeId) (m : Mem V) (L : List (Version V)) (oc oe : Obj V), RootSep sp m →
      m.obj? m.root = some oe → RootRel sp f oc oe → (∀ x ∈ xs, x ≠ root ∨ sp.virt = false) →
      ∃ oc' oe', RootRel sp f oc' oe' ∧ oc'.hist = oc.hist ∧ oe'.hist = oe.hist ∧
        (xs.foldl (wnStep sp S0 D i) (m, L)).1.obj? m.root = some oe' ∧
        (xs.foldl (wnStep sp S0 D i) (m, L)).1.root = m.root ∧
        RootSep sp (xs.foldl (wnStep sp S0 D i) (m, L)).1 ∧
        xs.foldl (wnStep sp S0 D i) (m.withRoot oc, L) =
          ((xs.foldl (wnStep sp S0 D i) (m, L)).1.withRoot oc', (xs.foldl (wnStep sp S0 D i) (m, L)).2) := by
  intro xs
  induction xs with
  | nil => intro m L oc oe hrs hra hr _; exact ⟨oc, oe, hr, rfl, rfl, hra, rfl, hrs, rfl⟩
  | cons x xs ih =>
    intro m L oc oe hrs hra hr hxs
    simp only [List.foldl_cons]
    obtain ⟨oc1, oe1, hr1, hh1, hh1', ho1, hrt1, he1⟩ :=
      writeNode_withRoot (S0 := S0) (D := D) (i := i) hrs hra hr (hxs x List.mem_cons_self)
    have hrs1 := hrs.writeNode S0 D i x
    have hstep : wnStep sp S0 D i (m.withRoot oc, L) x =
        ((wnStep sp S0 D i (m, L) x).1.withRoot oc1, (wnStep sp S0 D i (m, L) x).2) ∧
        (wnStep sp S0 D i (m, L) x).1 = (m.writeNode sp S0 D i x).1 := by
      unfold wnStep
      dsimp only
      rw [he1]
      cases hw : m.writeNode sp S0 D i x with
      | mk m' ov => cases ov <;> exact ⟨rfl, rfl⟩
    rw [hstep.1]
    have hra1 : (wnStep sp S0 D i (m, L) x).1.obj? (wnStep sp S0 D i (m, L) x).1.root = some oe1 := by
      rw [hstep.2, hrt1]; exact ho1
    have hrs1' : RootSep sp (wnStep sp S0 D i (m, L) x).1 := by rw [hstep.2]; exact hrs1
    obtain ⟨oc2, oe2, hr2, hh2, hh2', ho2, hrt2, hrs2, he2⟩ :=
      ih _ (wnStep sp S0 D i (m, L) x).2 oc1 oe1 hrs1' hra1 hr1 (fun z hz => hxs z (List.mem_cons_of_mem _ hz))
    have hrt1' : (wnStep sp S0 D i (m, L) x).1.root = m.root := by rw [hstep.2, hrt1]
    rw [hrt1'] at ho2 hrt2
    exact ⟨oc2, oe2, hr2, by rw [hh2, hh1], by rw [hh2', hh1'], ho2, hrt2, hrs2, he2⟩

theorem writeNode_s (S0 : Stream V T) (D : Dirty) (i : Nat) (m : Mem V) (x : NodeId) :
    (m.writeNode sp S0 D i x).1.s = m.s := by
  unfold Mem.writeNode
  cases m.canonicalOf x with
  | none => rfl
  | some h =>
    dsimp only
    cases m.obj? h with
    | none => rfl
    | some o => rfl

theorem wnStep_fst (S0 : Stream V T) (D : Dirty) (i : Nat) (acc : Mem V × List (Version V)) (x : NodeId) :
    (wnStep sp S0 D i acc x).1 = (acc.1.writeNode sp S0 D i x).1 := by
  unfold wnStep
  cases acc.1.writeNode sp S0 D i x with
  | mk m' ov => cases ov <;> rfl

theorem writeNode_cutS0 {c : Nat} {S0 : Stream V T} {D : Dirty} {i : Nat} (hc : c ≤ m.s) (x : NodeId) :
    m.writeNode sp (cutStream c S0) D i x = m.writeNode sp S0 D i x := by
  unfold Mem.writeNode Mem.refOf
  simp only [ruleRRef_cut hc]

theorem writeNodes_cutS0 {c : Nat} {S0 : Stream V T} {D : Dirty} {i : Nat} :
    ∀ (xs : List NodeId) (m : Mem V) (L : List (Version V)), c ≤ m.s →
      xs.foldl (wnStep sp (cutStream c S0) D i) (m, L) = xs.foldl (wnStep sp S0 D i) (m, L) := by
  intro xs
  induction xs with
  | nil => intro m L _; rfl
  | cons x xs ih =>
    intro m L hc
    simp only [List.foldl_cons]
    have h1 : wnStep sp (cutStream c S0) D i (m, L) x = wnStep sp S0 D i (m, L) x := by
      unfold wnStep; rw [writeNode_cutS0 hc]
    rw [h1]
    have hs : (wnStep sp S0 D i (m, L) x).1.s = m.s := by rw [wnStep_fst, writeNode_s]
    generalize wnStep sp S0 D i (m, L) x = acc at hs
    obtain ⟨m', L'⟩ := acc
    exact ih m' L' (by simp only at hs; rw [hs]; exact hc)

end Change

end Loader

/-! ## The writer's paths on structures that agree -/

section Paths

variable {sp : Spec V T} {f k : Time} {P P' : Struct V}

theorem mergeSort_congr {α : Type} {l : List α} {r s : α → α → Bool} (h : ∀ a ∈ l, ∀ b ∈ l, r a b = s a b) :
    l.mergeSort r = l.mergeSort s := by
  have := List.map_mergeSort (f := id) (s := s) (l := l) (r := r) h
  simpa using this

/-- The nodes below a node reachable at a time from f to k, in structures that
agree: the same. -/
theorem CutAgree.reachFrom_same (h : CutAgree sp f k P P') (hls : LiveSub sp) (hp : PtrsOK sp P) {t : Time}
    (h1 : f ≤ t) (h2 : t ≤ k) {x : NodeId} (hx : reachable sp P t x = true) {n n' : Node V}
    (hn : P.get? x = some n) (hn' : P'.get? x = some n') : reachFrom sp P' t x n' = reachFrom sp P t x n := by
  have hnodes : ∀ y, Reach sp P t y → y ≠ root → P'.get? y = P.get? y :=
    fun y hy hyr => h.nodes y t h1 h2 (fun _ => hyr) ((reachable_iff _ _ _ _).mpr hy)
  by_cases hxr : sp.virt = true ∧ x = root
  · obtain ⟨hv, rfl⟩ := hxr
    obtain ⟨hlev, hlive⟩ := h.rootLive hv n n' hn hn'
    rw [SIS.reachFrom_eq, SIS.reachFrom_eq, ← hlive t h1 h2, ← hlev]
    congr 1
    apply flatMap_congr_mem
    intro y hy
    obtain ⟨e, he, hye⟩ := hls _ _ hy
    obtain ⟨m, hm, hlt⟩ := hp root n hn e (mem_upTo.mp he).1 y hye
    have hRy : Reach sp P t y := Reach.child (Reach.root n hn) hn hy hm hlt
    have hyr : y ≠ root := by
      intro hyr; subst hyr; rw [hn, Option.some.injEq] at hm; subst hm; omega
    rw [hnodes y hRy hyr, hm]
    simp only [hlt, ↓reduceIte]
    exact reachFrom_agree hls hp h.rootP hnodes (m.level + 1) y m (by omega) hm hRy
  · have hx' : P'.get? x = P.get? x :=
      h.nodes x t h1 h2 (fun hv hx0 => hxr ⟨hv, hx0⟩) hx
    rw [hn', hn, Option.some.injEq] at hx'
    subst hx'
    exact reachFrom_agree hls hp h.rootP hnodes (n'.level + 1) x n' (by omega) hn ((reachable_iff _ _ _ _).mp hx)

theorem CutAgree.reachList_eq (h : CutAgree sp f k P P') (hls : LiveSub sp) (hp : PtrsOK sp P) {t : Time}
    (h1 : f ≤ t) (h2 : t ≤ k) : reachList sp P' t = reachList sp P t := by
  obtain ⟨n0, h0⟩ := Option.isSome_iff_exists.mp h.rootP
  obtain ⟨n0', h0'⟩ := Option.isSome_iff_exists.mp h.rootP'
  unfold reachList
  rw [h0, h0']
  exact h.reachFrom_same hls hp h1 h2 (reachable_root h0 t) h0 h0'

/-- The writer's paths are the same on structures that agree, before and after
the change. -/
theorem CutAgree.pathOf_eq (h : CutAgree sp f k P P') {c : Changes V}
    (h' : CutAgree sp f (k + 1) (P.apply (k + 1) c) (P'.apply (k + 1) c)) (hls : LiveSub sp)
    (hp : PtrsOK sp P) (hp' : PtrsOK sp (P.apply (k + 1) c)) (hfk : f ≤ k) :
    pathOf sp P' c (k + 1) = pathOf sp P c (k + 1) := by
  unfold pathOf
  simp only [Nat.add_sub_cancel]
  rw [h.reachList_eq hls hp hfk (Nat.le_refl _)]
  apply List.filter_congr
  intro x hx
  have hxr : reachable sp P k x = true := by
    simp only [reachable, List.contains_iff_mem]
    exact List.mem_eraseDups.mp hx
  have ht : ∀ z, (changed c z || c.touch.contains z ||
      (reachable sp P' k z && !reachable sp (P'.apply (k + 1) c) (k + 1) z)) =
      (changed c z || c.touch.contains z ||
      (reachable sp P k z && !reachable sp (P.apply (k + 1) c) (k + 1) z)) := by
    intro z
    rw [h.reachable_eq hls hp hfk (Nat.le_refl _) z, h'.reachable_eq hls hp' (by omega) (Nat.le_refl _) z]
  cases hn : P.get? x with
  | none =>
    have : P'.get? x = none := by
      cases h1 : P'.get? x with
      | none => rfl
      | some n' => have := h.ids x (by rw [h1]; rfl); rw [hn] at this; cases this
    rw [this]
  | some n =>
    obtain ⟨n', hn'⟩ : ∃ n', P'.get? x = some n' := by
      cases h1 : P'.get? x with
      | some n' => exact ⟨n', rfl⟩
      | none =>
        exfalso
        have hR := (reachable_iff _ _ _ _).mp hxr
        have := (h.reach hfk (Nat.le_refl _) hR)
        rw [← reachable_iff] at this
        by_cases hv : sp.virt = true ∧ x = root
        · obtain ⟨-, rfl⟩ := hv
          have := h.rootP'; rw [h1] at this; cases this
        · have := h.nodes x k hfk (Nat.le_refl _) (fun hv' hx0 => hv ⟨hv', hx0⟩) hxr
          rw [h1, hn] at this; cases this
    rw [hn']
    simp only
    rw [h.reachFrom_same hls hp hfk (Nat.le_refl _) hxr hn hn']
    congr 1
    funext z
    exact ht z

/-- The levels of the nodes reachable at a time from f to k agree. -/
theorem CutAgree.lev_eq (h : CutAgree sp f k P P') {t : Time} (h1 : f ≤ t) (h2 : t ≤ k) {x : NodeId}
    (hx : reachable sp P t x = true) : lev P' x = lev P x := by
  unfold lev
  by_cases hv : sp.virt = true ∧ x = root
  · obtain ⟨hv, rfl⟩ := hv
    obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp h.rootP
    obtain ⟨n', hn'⟩ := Option.isSome_iff_exists.mp h.rootP'
    rw [hn, hn']
    simp only [Option.map_some, Option.getD_some]
    exact ((h.rootLive hv n n' hn hn').1).symm
  · rw [h.nodes x t h1 h2 (fun hv' hx0 => hv ⟨hv', hx0⟩) hx]

/-- The live children at a time from f to k of the nodes reachable then agree. -/
theorem CutAgree.live_eq (h : CutAgree sp f k P P') {t : Time} (h1 : f ≤ t) (h2 : t ≤ k) {x : NodeId}
    (hx : reachable sp P t x = true) :
    (P'.get? x).map (fun n => sp.live (n.hist.upTo t)) = (P.get? x).map (fun n => sp.live (n.hist.upTo t)) := by
  by_cases hv : sp.virt = true ∧ x = root
  · obtain ⟨hv, rfl⟩ := hv
    obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp h.rootP
    obtain ⟨n', hn'⟩ := Option.isSome_iff_exists.mp h.rootP'
    rw [hn, hn']
    simp only [Option.map_some, Option.some.injEq]
    exact ((h.rootLive hv n n' hn hn').2 t h1 h2).symm
  · rw [h.nodes x t h1 h2 (fun hv' hx0 => hv ⟨hv', hx0⟩) hx]

end Paths

end SIS
