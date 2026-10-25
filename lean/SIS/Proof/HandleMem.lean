/-
Proofs about the physical layer with handles (bergdb item 009, step 2d), part 1:
the memory's operations, one at a time: what the objects, the handles and the
table are after setting an object, a handle, a table entry or a pointer's
reference, after a resolve, a load, a promote and an eviction.
-/
import SIS.HandleTheorems
import SIS.Proof.EvictInv
import SIS.Proof.Recon
import SIS.Proof.PhysRun

set_option linter.unusedSectionVars false

namespace SIS

variable {V T : Type} [DecidableEq V]

/-! ## Objects, handles, the table -/

theorem HMem.obj?_setObj (m : HMem V) (a a' : Nat) (o : HObj V) :
    (m.setObj a o).obj? a' = if a' = a then some o else m.obj? a' := by
  unfold HMem.setObj HMem.obj?
  simp only
  rw [lookup_cons_eq]
  split
  · rfl
  · rename_i hne
    exact lookup_filter_ne a a' m.objs hne

theorem HMem.obj?_setObj_self (m : HMem V) (a : Nat) (o : HObj V) : (m.setObj a o).obj? a = some o := by
  rw [HMem.obj?_setObj]; simp

theorem HMem.obj?_setObj_ne (m : HMem V) {a a' : Nat} (o : HObj V) (hne : a' ≠ a) :
    (m.setObj a o).obj? a' = m.obj? a' := by
  rw [HMem.obj?_setObj]; simp only [hne, ↓reduceIte]

@[simp] theorem HMem.setObj_handles (m : HMem V) (a : Nat) (o : HObj V) :
    (m.setObj a o).handles = m.handles := rfl
@[simp] theorem HMem.setObj_table (m : HMem V) (a : Nat) (o : HObj V) :
    (m.setObj a o).table = m.table := rfl
@[simp] theorem HMem.setObj_s (m : HMem V) (a : Nat) (o : HObj V) : (m.setObj a o).s = m.s := rfl
@[simp] theorem HMem.setObj_root (m : HMem V) (a : Nat) (o : HObj V) : (m.setObj a o).root = m.root := rfl
@[simp] theorem HMem.setObj_nextObj (m : HMem V) (a : Nat) (o : HObj V) :
    (m.setObj a o).nextObj = m.nextObj := rfl
@[simp] theorem HMem.setObj_nextHandle (m : HMem V) (a : Nat) (o : HObj V) :
    (m.setObj a o).nextHandle = m.nextHandle := rfl

theorem HMem.handle?_setObj (m : HMem V) (a : Nat) (o : HObj V) (n : Nat) :
    (m.setObj a o).handle? n = m.handle? n := rfl
theorem HMem.tableOf_setObj (m : HMem V) (a : Nat) (o : HObj V) (y : NodeId) :
    (m.setObj a o).tableOf y = m.tableOf y := rfl

/-- Handle n' after handle n is set. -/
theorem HMem.handle?_setHandle (m : HMem V) (n n' : Nat) (hd : Handle) :
    (m.setHandle n hd).handle? n' = if n' = n then some hd else m.handle? n' := by
  unfold HMem.setHandle HMem.handle?
  simp only
  rw [lookup_cons_eq]
  split
  · rfl
  · rename_i hne
    exact lookup_filter_ne n n' m.handles hne

@[simp] theorem HMem.setHandle_objs (m : HMem V) (n : Nat) (hd : Handle) :
    (m.setHandle n hd).objs = m.objs := rfl
@[simp] theorem HMem.setHandle_table (m : HMem V) (n : Nat) (hd : Handle) :
    (m.setHandle n hd).table = m.table := rfl
@[simp] theorem HMem.setHandle_s (m : HMem V) (n : Nat) (hd : Handle) : (m.setHandle n hd).s = m.s := rfl
@[simp] theorem HMem.setHandle_root (m : HMem V) (n : Nat) (hd : Handle) :
    (m.setHandle n hd).root = m.root := rfl
@[simp] theorem HMem.setHandle_nextObj (m : HMem V) (n : Nat) (hd : Handle) :
    (m.setHandle n hd).nextObj = m.nextObj := rfl
@[simp] theorem HMem.setHandle_nextHandle (m : HMem V) (n : Nat) (hd : Handle) :
    (m.setHandle n hd).nextHandle = m.nextHandle := rfl

theorem HMem.obj?_setHandle (m : HMem V) (n : Nat) (hd : Handle) (a : Nat) :
    (m.setHandle n hd).obj? a = m.obj? a := rfl
theorem HMem.tableOf_setHandle (m : HMem V) (n : Nat) (hd : Handle) (y : NodeId) :
    (m.setHandle n hd).tableOf y = m.tableOf y := rfl

theorem HMem.tableOf_setTable (m : HMem V) (y y' : NodeId) (n : Nat) :
    (m.setTable y n).tableOf y' = if y' = y then some n else m.tableOf y' := by
  unfold HMem.setTable HMem.tableOf
  simp only
  rw [lookup_cons_eq]
  split
  · rfl
  · rename_i hne
    exact lookup_filter_ne y y' m.table hne

@[simp] theorem HMem.setTable_objs (m : HMem V) (y : NodeId) (n : Nat) :
    (m.setTable y n).objs = m.objs := rfl
@[simp] theorem HMem.setTable_handles (m : HMem V) (y : NodeId) (n : Nat) :
    (m.setTable y n).handles = m.handles := rfl
@[simp] theorem HMem.setTable_s (m : HMem V) (y : NodeId) (n : Nat) : (m.setTable y n).s = m.s := rfl
@[simp] theorem HMem.setTable_root (m : HMem V) (y : NodeId) (n : Nat) :
    (m.setTable y n).root = m.root := rfl
@[simp] theorem HMem.setTable_nextObj (m : HMem V) (y : NodeId) (n : Nat) :
    (m.setTable y n).nextObj = m.nextObj := rfl
@[simp] theorem HMem.setTable_nextHandle (m : HMem V) (y : NodeId) (n : Nat) :
    (m.setTable y n).nextHandle = m.nextHandle := rfl

theorem HMem.obj?_setTable (m : HMem V) (y : NodeId) (n a : Nat) : (m.setTable y n).obj? a = m.obj? a := rfl
theorem HMem.handle?_setTable (m : HMem V) (y : NodeId) (n n' : Nat) :
    (m.setTable y n).handle? n' = m.handle? n' := rfl

theorem HMem.obj?_dropObj (m : HMem V) (a a' : Nat) :
    (m.dropObj a).obj? a' = if a' = a then none else m.obj? a' := by
  unfold HMem.dropObj HMem.obj?
  simp only
  split
  · rename_i h; subst h; exact lookup_filter_self m.objs a'
  · rename_i h; exact lookup_filter_ne a a' m.objs h

@[simp] theorem HMem.dropObj_handles (m : HMem V) (a : Nat) : (m.dropObj a).handles = m.handles := rfl
@[simp] theorem HMem.dropObj_table (m : HMem V) (a : Nat) : (m.dropObj a).table = m.table := rfl
@[simp] theorem HMem.dropObj_s (m : HMem V) (a : Nat) : (m.dropObj a).s = m.s := rfl
@[simp] theorem HMem.dropObj_root (m : HMem V) (a : Nat) : (m.dropObj a).root = m.root := rfl
@[simp] theorem HMem.dropObj_nextObj (m : HMem V) (a : Nat) : (m.dropObj a).nextObj = m.nextObj := rfl
@[simp] theorem HMem.dropObj_nextHandle (m : HMem V) (a : Nat) :
    (m.dropObj a).nextHandle = m.nextHandle := rfl

/-! ## Pointers -/

theorem HObj.ptr?_setPtr (o : HObj V) (y : NodeId) (p : HPtr) (y' : NodeId) :
    (o.setPtr y p).ptr? y' = if y' = y then (o.ptr? y).map (fun _ => p) else o.ptr? y' := by
  unfold HObj.setPtr HObj.ptr?
  exact lookup_map_set o.ptrs y y' p

theorem HObj.ptr?_setPtr_of {o : HObj V} {y : NodeId} {p0 : HPtr} (h : o.ptr? y = some p0) (p : HPtr)
    (y' : NodeId) : (o.setPtr y p).ptr? y' = if y' = y then some p else o.ptr? y' := by
  rw [HObj.ptr?_setPtr]
  split
  · rename_i hy; subst hy; rw [h]; rfl
  · rfl

theorem HObj.ptr?_putPtr (o : HObj V) (y : NodeId) (p : HPtr) (y' : NodeId) :
    (o.putPtr y p).ptr? y' = if y' = y then some p else o.ptr? y' := by
  unfold HObj.putPtr
  split
  · rename_i h
    obtain ⟨p0, hp0⟩ := Option.isSome_iff_exists.mp h
    exact HObj.ptr?_setPtr_of hp0 p y'
  · rename_i h
    unfold HObj.ptr?
    simp only
    rw [List.lookup_append]
    split
    · rename_i hy
      subst hy
      have hn : List.lookup y' o.ptrs = none := by
        cases hl : List.lookup y' o.ptrs with
        | none => rfl
        | some _ => exfalso; apply h; unfold HObj.ptr?; rw [hl]; rfl
      rw [hn]
      simp
    · rename_i hy
      cases hl : List.lookup y' o.ptrs with
      | some _ => rfl
      | none =>
        simp only [Option.none_or]
        have : (y' == y) = false := by simp [hy]
        simp [List.lookup, this]

/-- What an object is without its pointers. -/
def HObj.core (o : HObj V) : NodeId × Nat × Bool × History V × Bool × Option Nat :=
  (o.node, o.level, o.isData, o.hist, o.canonical, o.pos)

@[simp] theorem HObj.setPtr_core (o : HObj V) (y : NodeId) (p : HPtr) : (o.setPtr y p).core = o.core := rfl
@[simp] theorem HObj.putPtr_core (o : HObj V) (y : NodeId) (p : HPtr) : (o.putPtr y p).core = o.core := by
  unfold HObj.putPtr; split <;> rfl

@[simp] theorem HObj.setPtr_node (o : HObj V) (y : NodeId) (p : HPtr) : (o.setPtr y p).node = o.node := rfl
@[simp] theorem HObj.setPtr_level (o : HObj V) (y : NodeId) (p : HPtr) : (o.setPtr y p).level = o.level := rfl
@[simp] theorem HObj.setPtr_isData (o : HObj V) (y : NodeId) (p : HPtr) :
    (o.setPtr y p).isData = o.isData := rfl
@[simp] theorem HObj.setPtr_hist (o : HObj V) (y : NodeId) (p : HPtr) : (o.setPtr y p).hist = o.hist := rfl
@[simp] theorem HObj.setPtr_canonical (o : HObj V) (y : NodeId) (p : HPtr) :
    (o.setPtr y p).canonical = o.canonical := rfl
@[simp] theorem HObj.setPtr_pos (o : HObj V) (y : NodeId) (p : HPtr) : (o.setPtr y p).pos = o.pos := rfl

/-- Setting a pointer's reference, when the object and the pointer exist. -/
theorem HMem.setRef_eq {m : HMem V} {a : Nat} {y : NodeId} {o : HObj V} {p : HPtr}
    (ho : m.obj? a = some o) (hp : o.ptr? y = some p) (r : Option Nat) :
    m.setRef a y r = m.setObj a (o.setPtr y { p with ref := r }) := by
  unfold HMem.setRef
  rw [ho]
  simp only [hp]

@[simp] theorem HMem.setRef_handles (m : HMem V) (a : Nat) (y : NodeId) (r : Option Nat) :
    (m.setRef a y r).handles = m.handles := by
  unfold HMem.setRef; split
  · split <;> rfl
  · rfl
@[simp] theorem HMem.setRef_table (m : HMem V) (a : Nat) (y : NodeId) (r : Option Nat) :
    (m.setRef a y r).table = m.table := by
  unfold HMem.setRef; split
  · split <;> rfl
  · rfl
@[simp] theorem HMem.setRef_s (m : HMem V) (a : Nat) (y : NodeId) (r : Option Nat) :
    (m.setRef a y r).s = m.s := by
  unfold HMem.setRef; split
  · split <;> rfl
  · rfl
@[simp] theorem HMem.setRef_root (m : HMem V) (a : Nat) (y : NodeId) (r : Option Nat) :
    (m.setRef a y r).root = m.root := by
  unfold HMem.setRef; split
  · split <;> rfl
  · rfl
@[simp] theorem HMem.setRef_nextObj (m : HMem V) (a : Nat) (y : NodeId) (r : Option Nat) :
    (m.setRef a y r).nextObj = m.nextObj := by
  unfold HMem.setRef; split
  · split <;> rfl
  · rfl
@[simp] theorem HMem.setRef_nextHandle (m : HMem V) (a : Nat) (y : NodeId) (r : Option Nat) :
    (m.setRef a y r).nextHandle = m.nextHandle := by
  unfold HMem.setRef; split
  · split <;> rfl
  · rfl

/-! ## maxRef -/

/-- The larger of a reference and none (no written position) is the reference. -/
theorem maxRef_none (r : Option Nat) : maxRef r none = r := by
  cases r <;> rfl

/-- A position at least as large as r is the larger of r and it. -/
theorem maxRef_le {r : Option Nat} {q : Nat} (h : ∀ x, r = some x → x ≤ q) :
    maxRef r (some q) = some q := by
  cases r with
  | none => rfl
  | some x =>
    have := h x rfl
    simp only [maxRef, Option.some.injEq]
    omega

theorem maxRef_idem (r w : Option Nat) : maxRef (maxRef r w) w = maxRef r w := by
  cases r <;> cases w <;> simp [maxRef]

theorem maxRef_ge_left {r w : Option Nat} {x : Nat} (h : r = some x) :
    ∃ y, maxRef r w = some y ∧ x ≤ y := by
  subst h
  cases w with
  | none => exact ⟨x, rfl, Nat.le_refl x⟩
  | some w => exact ⟨max x w, rfl, Nat.le_max_left x w⟩

theorem maxRef_ge_right {r w : Option Nat} {x : Nat} (h : w = some x) :
    ∃ y, maxRef r w = some y ∧ x ≤ y := by
  subst h
  cases r with
  | none => exact ⟨x, rfl, Nat.le_refl x⟩
  | some r => exact ⟨max r x, rfl, Nat.le_max_right r x⟩

/-- The larger of two references is one of them. -/
theorem maxRef_cases (r w : Option Nat) (x : Nat) (h : maxRef r w = some x) : r = some x ∨ w = some x := by
  cases r with
  | none => right; simpa [maxRef] using h
  | some r =>
    cases w with
    | none => left; simpa [maxRef] using h
    | some w =>
      simp only [maxRef, Option.some.injEq] at h
      by_cases hrw : r ≤ w
      · right; rw [← h]; simp [Nat.max_eq_right hrw]
      · left; rw [← h]; simp [Nat.max_eq_left (by omega : w ≤ r)]

/-! ## Rule R -/

/-- Rule R of a reference that Rule R already gave changes nothing. -/
theorem ruleRRef_idem (S0 : Stream V T) (s : Nat) (y : NodeId) (r : Option Nat) :
    ruleRRef S0 s y (ruleRRef S0 s y r) = ruleRRef S0 s y r := by
  unfold ruleRRef
  cases hn : newest S0 s y with
  | none => rfl
  | some w =>
    cases r with
    | none => simp
    | some r =>
      by_cases hr : r < w.recNo
      · simp [hr]
      · simp [hr]

/-- Rule R of the larger of a reference after Rule R and another reference is
that larger one. -/
theorem ruleRRef_maxRef (S0 : Stream V T) (s : Nat) (y : NodeId) (r w : Option Nat) :
    ruleRRef S0 s y (maxRef (ruleRRef S0 s y r) w) = maxRef (ruleRRef S0 s y r) w := by
  unfold ruleRRef
  cases hn : newest S0 s y with
  | none => rfl
  | some nw =>
    simp only
    cases r with
    | none =>
      cases w with
      | none => simp [maxRef]
      | some w =>
        simp only [maxRef]
        split
        · rename_i h; omega
        · rfl
    | some r =>
      simp only
      by_cases hr : r < nw.recNo
      · simp only [hr, ↓reduceIte]
        cases w with
        | none => simp [maxRef]
        | some w =>
          simp only [maxRef]
          split
          · rename_i h; omega
          · rfl
      · simp only [hr, ↓reduceIte]
        cases w with
        | none => simp [maxRef, hr]
        | some w =>
          simp only [maxRef]
          split
          · rename_i h; omega
          · rfl

/-- Rule R never makes a reference older. -/
theorem ruleRRef_ge {S0 : Stream V T} {s : Nat} {y : NodeId} {r : Option Nat} {x : Nat} (h : r = some x) :
    ∃ x', ruleRRef S0 s y r = some x' ∧ x ≤ x' := by
  subst h
  unfold ruleRRef
  cases newest S0 s y with
  | none => exact ⟨x, rfl, Nat.le_refl x⟩
  | some w =>
    simp only
    split
    · rename_i h; exact ⟨w.recNo, rfl, by omega⟩
    · exact ⟨x, rfl, Nat.le_refl x⟩

/-- Rule R gives a reference at least as new as the newest version in the
section, if there is one. -/
theorem ruleRRef_ge_newest {S0 : Stream V T} {s : Nat} {y : NodeId} {w : Version V}
    (hn : newest S0 s y = some w) (r : Option Nat) :
    ∃ x, ruleRRef S0 s y r = some x ∧ w.recNo ≤ x := by
  unfold ruleRRef
  rw [hn]
  simp only
  cases r with
  | none => exact ⟨w.recNo, rfl, Nat.le_refl _⟩
  | some r =>
    simp only
    split
    · exact ⟨w.recNo, rfl, Nat.le_refl _⟩
    · rename_i h; exact ⟨r, rfl, by omega⟩

/-! ## The fast path's test -/

/-- Open point 1 of 02, given the invariants: if the table and the handles are
as `HTableOK` says, every snapshot in a handle is at least as new as its node's
newest version in the startup section (`HRuleROK`), and live handles have no
written position (`HLiveWrittenOK`), then for a pointer whose reference is a
position, the fast path's test with that reference and the slow path's test,
with the reference after Rule R raised to the handle's written position, agree
(`HFastOK`). -/
theorem hFastOK_of {S0 : Stream V T} {m : HMem V} (ht : HTableOK m) (hr : HRuleROK S0 m)
    (hw : HLiveWrittenOK m) : HFastOK S0 m := by
  intro a o y p n hd b ob r ha hp hn hh hb hob hpr
  obtain ⟨-, -, -, h4, -, hptr⟩ := ht
  obtain ⟨hd', hh', hnode⟩ := hptr a o y p n ha hp hn
  rw [hh] at hh'
  cases hh'
  -- A handle that holds an object is live, so it has no written position.
  have hlive : hd.dead = false := by
    cases hdk : hd.dead with
    | false => rfl
    | true => rw [h4 n hd hh hdk] at hb; cases hb
  rw [hw n hd hh hlive, maxRef_none, hpr]
  unfold HObj.usable
  cases hc : ob.canonical with
  | true => simp
  | false =>
    simp only [Bool.false_or]
    unfold ruleRRef
    cases hnw : newest S0 m.s y with
    | none => rfl
    | some wn =>
      obtain ⟨q, hq, hle⟩ := hr n hd b ob wn hh hb hob hc (by rw [hnode]; exact hnw)
      rw [hq]
      by_cases hlt : r < wn.recNo
      · simp only [hlt, ite_true, decide_eq_decide]
        omega
      · simp only [hlt, ite_false]

/-! ## Eviction is local for records -/

/-- The written position that `HMem.evict` gives handle n, whose object is at
address a. -/
def HMem.evictWritten (m : HMem V) (hd : Handle) (a : Nat) : Option Nat :=
  match m.obj? a with
  | some o => if o.canonical then o.pos else hd.written
  | none => hd.written

/-- The handles after an eviction of handle n: n is dead, with no object and
the written position of `evictWritten`; the others are as they were. -/
theorem HMem.evict_handle? {m : HMem V} {D : Dirty} {n : Nat} {hd : Handle} {a : Nat}
    (hev : m.evictable D n = true) (hh : m.handle? n = some hd) (ha : hd.obj = some a) (n' : Nat) :
    (m.evict D n).handle? n' =
      if n' = n then some { hd with obj := none, written := m.evictWritten hd a, dead := true }
      else m.handle? n' := by
  unfold HMem.evict
  simp only [hev, ↓reduceIte, hh, ha]
  exact HMem.handle?_setHandle m n n' _

/-- The objects after an eviction of handle n, whose object is at address a:
a has left memory; the others are as they were. -/
theorem HMem.evict_obj? {m : HMem V} {D : Dirty} {n : Nat} {hd : Handle} {a : Nat}
    (hev : m.evictable D n = true) (hh : m.handle? n = some hd) (ha : hd.obj = some a) (b : Nat) :
    (m.evict D n).obj? b = if b = a then none else m.obj? b := by
  unfold HMem.evict
  simp only [hev, ↓reduceIte, hh, ha]
  unfold HMem.obj?
  simp only [HMem.setHandle]
  split
  · rename_i hb
    subst hb
    exact lookup_filter_self m.objs b
  · rename_i hb
    exact lookup_filter_ne a b m.objs hb

/-- An eviction keeps Rule R's startup pos. -/
theorem HMem.evict_s (m : HMem V) (D : Dirty) (n : Nat) : (m.evict D n).s = m.s := by
  unfold HMem.evict
  split
  · split
    · split <;> rfl
    · rfl
  · rfl

/-- Evicting a handle is local for records (02, 4.7): it changes the record
rule's reference of no pointer (`HMem.ptrRef`), whichever handle the pointer
holds, if only handle n holds its object, and a pointer that holds handle n does
not name, after Rule R, a version newer than n's canonical object. -/
theorem HMem.ptrRef_evict {S0 : Stream V T} {m : HMem V} {D : Dirty} {n : Nat} {y : NodeId}
    {p : HPtr}
    (huniq : ∀ n' hd' a, m.handle? n' = some hd' → hd'.obj = some a → m.objOf n = some a → n' = n)
    (hle : p.handle = some n → ∀ a o q r, m.objOf n = some a → m.obj? a = some o →
      o.canonical = true → o.pos = some q → ruleRRef S0 m.s y p.ref = some r → r ≤ q) :
    (m.evict D n).ptrRef S0 y p = m.ptrRef S0 y p := by
  by_cases hev : m.evictable D n = true
  · -- The evicted handle and its object.
    cases hh : m.handle? n with
    | none => simp [HMem.evictable, hh] at hev
    | some hd =>
      cases ha : hd.obj with
      | none => simp [HMem.evictable, hh, ha] at hev
      | some a =>
        cases ho : m.obj? a with
        | none => simp [HMem.evictable, hh, ha, ho] at hev
        | some o =>
          have hpos : o.pos.isSome = true := by
            have h := hev
            simp only [HMem.evictable, hh, ha, ho, Bool.and_eq_true] at h
            exact h.2.2
          have hobj : m.objOf n = some a := by simp [HMem.objOf, hh, ha]
          unfold HMem.ptrRef
          rw [HMem.evict_s]
          cases hp : p.handle with
          | none => rfl
          | some n' =>
            simp only [Option.bind_some]
            rw [HMem.evict_handle? hev hh ha n']
            by_cases hn : n' = n
            · subst hn
              simp only [↓reduceIte, hh, ha, Option.bind_some, ho, Option.bind_none]
              unfold HMem.evictWritten
              rw [ho]
              cases hc : o.canonical with
              | true =>
                simp only [hc, ↓reduceIte]
                cases hq : o.pos with
                | none => rw [hq] at hpos; simp at hpos
                | some q =>
                  exact maxRef_le (fun r hr => hle hp a o q r hobj ho hc hq hr)
              | false => simp only [hc, Bool.false_eq_true, ↓reduceIte]
            · simp only [hn, ↓reduceIte]
              cases hh2 : m.handle? n' with
              | none => rfl
              | some hd2 =>
                dsimp only
                cases hb : hd2.obj with
                | none => rfl
                | some b =>
                  simp only [Option.bind_some]
                  rw [HMem.evict_obj? hev hh ha b]
                  have hba : ¬ b = a := by
                    intro hba
                    subst hba
                    exact hn (huniq n' hd2 b hh2 hb hobj)
                  simp only [hba, ↓reduceIte]
  · unfold HMem.evict
    simp only [hev]
    rfl

/-- Only one handle holds an object: by `HTableOK`, a handle that holds an
object is live, so it is its node's entry in the table, and the object is of
that node. -/
theorem HTableOK.uniq {m : HMem V} (ht : HTableOK m) {n n' : Nat} {hd' : Handle} {a : Nat}
    (hh' : m.handle? n' = some hd') (ha' : hd'.obj = some a) (hobj : m.objOf n = some a) :
    n' = n := by
  obtain ⟨h1, -, h3, h4, -, -⟩ := ht
  -- Handle n holds a, so it is live.
  cases hh : m.handle? n with
  | none => simp [HMem.objOf, hh] at hobj
  | some hd =>
    have ha : hd.obj = some a := by simpa [HMem.objOf, hh] using hobj
    have hlive : ∀ k e, m.handle? k = some e → e.obj = some a → e.dead = false := by
      intro k e hk he
      cases hdk : e.dead with
      | false => rfl
      | true => rw [h4 k e hk hdk] at he; cases he
    have ht' := h3 n' hd' hh' (hlive n' hd' hh' ha')
    have ht := h3 n hd hh (hlive n hd hh ha)
    obtain ⟨e', b', o', he', -, hn', hb', ho', hon'⟩ := h1 hd'.node n' ht'
    obtain ⟨e, b, o, he, -, hn, hb, ho, hon⟩ := h1 hd.node n ht
    rw [hh'] at he'; cases he'
    rw [hh] at he; cases he
    rw [ha'] at hb'; cases hb'
    rw [ha] at hb; cases hb
    rw [ho'] at ho; cases ho
    -- Both handles are their node's entry, and both nodes are the object's.
    have : hd'.node = hd.node := by rw [← hon', hon]
    rw [this, ht] at ht'
    exact (Option.some.inj ht').symm

/-- Eviction is local for records, given the invariants: in a memory with the
table and the handles as `HTableOK` says, canonical objects at their nodes'
latest records (`HCanOK`) and references that name versions (`HWrittenOK`),
evicting a handle changes the record rule's reference of no pointer of any
object (`HMem.ptrRef`). The two stream facts hold in every run: a version is in
the record of its number, and no version of a node is after its latest. -/
theorem HMem.ptrRef_evict_of {S0 : Stream V T} {db : DB V T} {m : HMem V} {D : Dirty} {n : Nat}
    (ht : HTableOK m) (hc : HCanOK db m) (hw : HWrittenOK db m) (hpre : S0 <+: db.S)
    (hidx : ∀ r y w, db.S.versionAt r y = some w → w.recNo = r)
    (hrec : ∀ r y w, db.S.versionAt r y = some w → ∃ v, db.S.lv y = some v ∧ r ≤ v.recNo)
    {a : Nat} {o : HObj V} {y : NodeId} {p : HPtr} (ha : m.obj? a = some o)
    (hp : o.ptr? y = some p) :
    (m.evict D n).ptrRef S0 y p = m.ptrRef S0 y p := by
  apply HMem.ptrRef_evict
  · intro n' hd' b hh' hb hobj
    exact ht.uniq hh' hb hobj
  · intro hpn b ob q r hobj hob hcan hq hr
    -- The handle n is of node y, and so is its object.
    obtain ⟨h1, -, h3, h4, -, h6⟩ := ht
    obtain ⟨hd, hh, hnode⟩ := h6 a o y p n ha hp hpn
    have hb : hd.obj = some b := by simpa [HMem.objOf, hh] using hobj
    have hlive : hd.dead = false := by
      cases hdk : hd.dead with
      | false => rfl
      | true => rw [h4 n hd hh hdk] at hb; cases hb
    obtain ⟨e, b', o', he, -, -, hb', ho', hon⟩ := h1 hd.node n (h3 n hd hh hlive)
    rw [hh] at he; cases he
    rw [hb] at hb'; cases hb'
    rw [hob] at ho'; cases ho'
    -- Its position is y's latest record.
    have hpos := (hc.1 b ob hob hcan).2.2
    rw [hq, hon, hnode] at hpos
    -- Every record that Rule R gives names a version of y.
    have hver : ∃ u, db.S.versionAt r y = some u := by
      unfold ruleRRef at hr
      cases hnw : newest S0 m.s y with
      | none =>
        rw [hnw] at hr
        simp only at hr
        obtain ⟨u, hu⟩ := Option.isSome_iff_exists.mp (hw.2 a o y p r ha hp hr)
        exact ⟨u, hu⟩
      | some w =>
        rw [hnw] at hr
        obtain ⟨r0, -, hr0⟩ := newest_some hnw
        have hr0' := versionAt_prefix hpre hr0
        have hrec0 := hidx r0 y w hr0'
        cases hpr : p.ref with
        | none =>
          rw [hpr] at hr
          simp only [Option.some.injEq] at hr
          subst hr
          rw [hrec0]; exact ⟨w, hr0'⟩
        | some r1 =>
          rw [hpr] at hr
          simp only at hr
          split at hr
          · simp only [Option.some.injEq] at hr
            subst hr
            rw [hrec0]; exact ⟨w, hr0'⟩
          · simp only [Option.some.injEq] at hr
            subst hr
            obtain ⟨u, hu⟩ := Option.isSome_iff_exists.mp (hw.2 a o y p r1 ha hp hpr)
            exact ⟨u, hu⟩
    obtain ⟨u, hu⟩ := hver
    obtain ⟨v, hv, hle⟩ := hrec r y u hu
    rw [hv] at hpos
    simp only [Option.map_some, Option.some.injEq] at hpos
    omega

end SIS
