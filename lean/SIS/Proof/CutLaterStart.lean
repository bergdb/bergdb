/-
Proofs about reclaim, part 21 (bergdb item 001, WP R5, T12 with eviction): the
Level 4 startup from a stream cut safely is the startup from the whole stream
but for the root's object: with a virtual root, the root rebuilt from the root
children that the cut stream still has.
-/
import SIS.Proof.CutLaterTrans

set_option linter.unusedSectionVars false

namespace SIS

variable {V T : Type} [DecidableEq V]

/-! ## The section and the root -/

section Base

variable {sp : Spec V T} {S : Stream V T} {c : Nat}

theorem drop_cutStream {s : Nat} (h : c ≤ s) : (cutStream c S).drop s = S.drop s := by
  apply List.ext_getElem?
  intro i
  rw [List.getElem?_drop, List.getElem?_drop, cutStream_getElem?_ge (by omega)]

theorem sectionNodes_cut {s : Nat} (h : c ≤ s) : sectionNodes (cutStream c S) s = sectionNodes S s := by
  unfold sectionNodes; rw [drop_cutStream h]

theorem canonOfVersion_cut {s : Nat} (h : c ≤ s) (w : Version V) :
    canonOfVersion sp (cutStream c S) s w = canonOfVersion sp S s w := by
  unfold canonOfVersion; simp only [ruleRRef_cut h]

theorem secStep_cut (h : c ≤ lastSp S) (m : Mem V) (x : NodeId) :
    secStep sp (cutStream c S) m x = secStep sp S m x := by
  unfold secStep
  rw [lastSp_cut, newest_cut h]
  simp only [canonOfVersion_cut h]

theorem lazySec_cut (h : c ≤ lastSp S) : lazySec sp (cutStream c S) = lazySec sp S := by
  unfold lazySec mem0
  rw [lastSp_cut, sectionNodes_cut h]
  congr 1
  funext m x
  exact secStep_cut h m x

theorem map_withRoot_none (l : List (Nat × Obj V)) (r : Nat) (oc : Obj V) (h : ∀ p ∈ l, p.1 ≠ r) :
    l.map (fun p => if p.1 == r then (r, oc) else p) = l := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    simp only [List.map_cons]
    have hp : (p.1 == r) = false := by simp [h p List.mem_cons_self]
    rw [hp, ih (fun q hq => h q (List.mem_cons_of_mem _ hq))]
    rfl

theorem lazySec_fresh (sp : Spec V T) (S : Stream V T) :
    ∀ h, (lazySec sp S).next ≤ h → (lazySec sp S).obj? h = none := by
  unfold lazySec
  have key : ∀ (L : List NodeId) (m : Mem V), (∀ h, m.next ≤ h → m.obj? h = none) →
      ∀ h, (L.foldl (secStep sp S) m).next ≤ h → (L.foldl (secStep sp S) m).obj? h = none := by
    intro L
    induction L with
    | nil => intro m hm; exact hm
    | cons x L ih =>
      intro m hm
      simp only [List.foldl_cons]
      apply ih
      unfold secStep
      cases newest S (lastSp S) x with
      | none => exact hm
      | some w =>
        simp only
        split
        · exact hm
        · intro h hh
          simp only [Mem.setTable_next, Mem.addObj_next] at hh
          rw [Mem.obj?_setTable, Mem.obj?_addObj]
          simp only [show h ≠ m.next by omega, ↓reduceIte]
          exact hm h (by omega)
  exact key _ _ (fun h _ => by simp [mem0, Mem.obj?])

/-- The root's step of the startup from the cut stream: with a virtual root, the
root rebuilt from the root children of the cut stream. -/
theorem lazyRoot_cut_virt (hv : sp.virt = true) (h : c ≤ lastSp S) (m1 : Mem V)
    (hfr : ∀ h, m1.next ≤ h → m1.obj? h = none) :
    lazyRoot sp (cutStream c S) m1 = (lazyRoot sp S m1).withRoot
      { (canonOfVersion sp S (lastSp S) (rootVersion sp (lastSp S) (topsRead sp (cutStream c S) (lastSp S) true)))
        with hist := (rootVersion sp (lastSp S) (topsRead sp (cutStream c S) (lastSp S) true)).hist, pos := none } := by
  unfold lazyRoot
  simp only [hv, ↓reduceIte, lastSp_cut, canonOfVersion_cut h]
  unfold Mem.withRoot Mem.addObj Mem.setTable
  simp only [List.map_cons, beq_self_eq_true, ↓reduceIte]
  congr 2
  rw [map_withRoot_none]
  intro p hp hpe
  have h1 : m1.obj? m1.next = none := hfr m1.next (Nat.le_refl _)
  have h2 := lookup_isSome_of_mem (l := m1.objs) (a := m1.next) (by rw [← hpe]; exact List.mem_map_of_mem hp)
  unfold Mem.obj? at h1
  rw [h1] at h2
  cases h2

/-- The objects' maps of the startup's last steps, on the memory with the other
root object. -/
theorem map_withRoot_comm (l : List (Nat × Obj V)) (r : Nat) (oc : Obj V) (F G : Obj V → Obj V)
    (hFG : ∀ o, F o = G o) :
    (l.map (fun p => if p.1 == r then (r, oc) else p)).map (fun p => (p.1, F p.2)) =
      (l.map (fun p => (p.1, G p.2))).map (fun p => if p.1 == r then (r, G oc) else p) := by
  simp only [List.map_map]
  apply List.map_congr_left
  intro p _
  simp only [Function.comp]
  by_cases hp : p.1 = r
  · simp [hp, hFG]
  · have : (p.1 == r) = false := by simp [hp]
    simp [this, hFG]

theorem linkCanonical_withRoot {m : Mem V} {oc oe : Obj V} (hra : m.obj? m.root = some oe)
    (hc : oc.canonical = oe.canonical) (hpos : oc.pos = oe.pos) :
    (m.withRoot oc).linkCanonical = m.linkCanonical.withRoot (linkObj m oc) := by
  have hq : ∀ q, linkQ (m.withRoot oc) q = linkQ m q := by
    intro q
    unfold linkQ
    rw [withRoot_tableOf]
    split
    · split
      · rename_i h0 _
        by_cases he : h0 = m.root
        · subst he
          rw [withRoot_obj?_root hra, hra]
          simp only [hc, hpos]
        · rw [withRoot_obj?_ne he]
      · rfl
    · rfl
  have hq' : linkQ (m.withRoot oc) = linkQ m := funext hq
  have hlo : ∀ o, linkObj (m.withRoot oc) o = linkObj m o := by
    intro o; unfold linkObj; rw [hq']
  rw [linkCanonical_eq, linkCanonical_eq]
  simp only [hlo]
  unfold Mem.withRoot
  simp only
  congr 1
  exact map_withRoot_comm _ _ _ _ _ (fun _ => rfl)

/-- What `sectionPos` makes of object o. -/
def secObj (S : Stream V T) (s : Nat) (o : Obj V) : Obj V :=
  if !o.canonical then o else match newest S s o.node with
    | some w => { o with pos := some w.recNo }
    | none => o

theorem sectionPos_eq (m : Mem V) (S : Stream V T) :
    m.sectionPos S = { m with objs := m.objs.map (fun p => (p.1, secObj S m.s p.2)) } := by
  unfold Mem.sectionPos secObj
  congr 1
  apply List.map_congr_left
  intro p _
  cases hc : p.2.canonical
  · simp
  · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    cases newest S m.s p.2.node <;> simp [hc]

theorem sectionPos_withRoot {m : Mem V} {oc : Obj V} {S' : Stream V T}
    (hS : ∀ y, newest S' m.s y = newest S m.s y) :
    (m.withRoot oc).sectionPos S' = (m.sectionPos S).withRoot (secObj S m.s oc) := by
  have hso : ∀ o, secObj S' (m.withRoot oc).s o = secObj S m.s o := by
    intro o; unfold secObj; rw [withRoot_s, hS]
  rw [sectionPos_eq, sectionPos_eq]
  simp only [hso]
  unfold Mem.withRoot
  simp only
  congr 1
  exact map_withRoot_comm _ _ _ _ _ (fun _ => rfl)

theorem linkD_eq (m : Mem V) (D : Dirty) :
    m.linkD D = { m with objs := m.objs.map (fun p => (p.1, linkObjD m D p.1 p.2)) } := by
  unfold Mem.linkD linkObjD
  congr 1
  apply List.map_congr_left
  intro p _
  cases (!(p.2.canonical && (inD D p.2.node || p.1 == m.root)))
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rfl
  · simp only [↓reduceIte]

theorem linkD_withRoot {m : Mem V} {oc oe : Obj V} (hra : m.obj? m.root = some oe)
    (hc : oc.canonical = oe.canonical) (D : Dirty) :
    (m.withRoot oc).linkD D = (m.linkD D).withRoot (linkObjD m D m.root oc) := by
  have hls : ∀ q, linkSlot (m.withRoot oc) q = linkSlot m q := by
    intro q; unfold linkSlot; rw [withRoot_canonicalOf hra hc]
  have hls' : linkSlot (m.withRoot oc) = linkSlot m := funext hls
  have hlo : ∀ h o, linkObjD (m.withRoot oc) D h o = linkObjD m D h o := by
    intro h o; unfold linkObjD; rw [hls', withRoot_root]
  rw [linkD_eq, linkD_eq]
  simp only [hlo]
  unfold Mem.withRoot
  simp only
  congr 1
  simp only [List.map_map]
  apply List.map_congr_left
  intro p _
  simp only [Function.comp]
  by_cases hp : p.1 = m.root
  · have : (p.1 == m.root) = true := by simp [hp]
    simp only [this, ↓reduceIte]
  · have : (p.1 == m.root) = false := by simp [hp]
    simp only [this, Bool.false_eq_true, ↓reduceIte]

end Base

/-! ## The rerun's loader on the memory with the other root object -/

section Loader1

variable {sp : Spec V T} {m : Mem V} {oc oe : Obj V}

theorem register_withRoot {h1 : Nat} (hh1 : h1 ≠ m.root)
    (htbl : ∀ o, m.obj? h1 = some o → ∀ h0, m.tableOf o.node = some h0 → h0 ≠ m.root) :
    (m.withRoot oc).register h1 = ((m.register h1).1.withRoot oc, (m.register h1).2) := by
  unfold Mem.register
  rw [withRoot_obj?_ne hh1]
  cases ho : m.obj? h1 with
  | none => rfl
  | some o =>
    simp only
    rw [withRoot_tableOf]
    cases ht : m.tableOf o.node with
    | none => rfl
    | some h0 =>
      simp only
      split
      · rfl
      · rw [withRoot_obj?_ne (htbl o ho h0 ht)]
        cases m.obj? h0 with
        | none => rfl
        | some o0 => simp only; split <;> rfl

/-- The object that `makeCanonical` picks. -/
def mcPick (m : Mem V) (y : NodeId) (h : Nat) : Nat :=
  match m.tableOf y with
  | none => h
  | some h0 =>
    if h0 == h then h else
    match m.obj? h0, m.obj? h with
    | some o0, some o =>
      if o0.canonical then h0 else
      match o0.pos, o.pos with
      | some p0, some p => if p < p0 then h0 else h
      | some _, none => h0
      | _, _ => h
    | _, _ => h

/-- The pick made canonical and the table's, and the slot of hp for y naming it. -/
def pickTail (m : Mem V) (hp : Nat) (y : NodeId) (pick : Nat) : Mem V × Nat :=
  let m1 := match m.obj? pick with
    | some o => (m.setObj pick { o with canonical := true }).setTable y pick
    | none => m
  let m2 := match m1.obj? hp with
    | some op => m1.setObj hp (op.setSlot y (Slot.mem pick))
    | none => m1
  (m2, pick)

theorem makeCanonical_eq (m : Mem V) (hp : Nat) (y : NodeId) (h : Nat) :
    m.makeCanonical hp y h = pickTail m hp y (mcPick m y h) := rfl

theorem mcPick_withRoot {y : NodeId} {h : Nat} (hh : h ≠ m.root) (htbl : ∀ h0, m.tableOf y = some h0 → h0 ≠ m.root) :
    mcPick (m.withRoot oc) y h = mcPick m y h := by
  unfold mcPick
  rw [withRoot_tableOf]
  cases ht : m.tableOf y with
  | none => rfl
  | some h0 =>
    simp only
    rw [withRoot_obj?_ne (htbl h0 ht), withRoot_obj?_ne hh]

theorem mcPick_ne {y : NodeId} {h : Nat} (hh : h ≠ m.root) (htbl : ∀ h0, m.tableOf y = some h0 → h0 ≠ m.root) :
    mcPick m y h ≠ m.root := by
  unfold mcPick
  cases ht : m.tableOf y with
  | none => exact hh
  | some h0 =>
    simp only
    have := htbl h0 ht
    split
    · exact hh
    · split
      · split
        · exact this
        · split <;> (try split) <;> assumption
      · exact hh

theorem pickTail_withRoot (hra : m.obj? m.root = some oe) {hp : Nat} {y : NodeId} {pick : Nat}
    (hpick : pick ≠ m.root) :
    pickTail (m.withRoot oc) hp y pick =
      ((pickTail m hp y pick).1.withRoot (if hp = m.root then oc.setSlot y (Slot.mem pick) else oc), pick) ∧
    (pickTail m hp y pick).1.obj? m.root = some (if hp = m.root then oe.setSlot y (Slot.mem pick) else oe) ∧
    (pickTail m hp y pick).1.root = m.root := by
  unfold pickTail
  dsimp only
  rw [withRoot_obj?_ne hpick]
  cases hpo : m.obj? pick with
  | none =>
    simp only
    by_cases he : hp = m.root
    · subst he
      rw [withRoot_obj?_root hra, hra]
      simp only [↓reduceIte]
      exact ⟨by rw [withRoot_setObj_root _ (oe.setSlot y (Slot.mem pick))], Mem.obj?_setObj_self _ _ _, rfl⟩
    · rw [withRoot_obj?_ne he]
      simp only [he, ↓reduceIte]
      cases m.obj? hp with
      | none => exact ⟨rfl, hra, rfl⟩
      | some op =>
        refine ⟨by simp only [withRoot_setObj_ne he], ?_, rfl⟩
        rw [Mem.obj?_setObj_ne _ _ (Ne.symm he)]; exact hra
  | some o =>
    simp only
    rw [withRoot_setObj_ne hpick, withRoot_setTable]
    have hra1 : ((m.setObj pick { o with canonical := true }).setTable y pick).obj? m.root = some oe := by
      rw [Mem.obj?_setTable, Mem.obj?_setObj]
      simp only [Ne.symm hpick, ↓reduceIte]
      exact hra
    have hr1 : ((m.setObj pick { o with canonical := true }).setTable y pick).root = m.root := rfl
    by_cases he : hp = m.root
    · subst he
      rw [← hr1, withRoot_obj?_root (by rw [hr1]; exact hra1), hr1, hra1]
      simp only [↓reduceIte]
      refine ⟨?_, ?_, rfl⟩
      · rw [← hr1]; exact congrArg (fun x => (x, pick)) (withRoot_setObj_root _ _)
      · exact Mem.obj?_setObj_self _ _ _
    · have he1 : hp ≠ ((m.setObj pick { o with canonical := true }).setTable y pick).root := by
        rw [hr1]; exact he
      rw [withRoot_obj?_ne he1]
      simp only [he, ↓reduceIte]
      cases ((m.setObj pick { o with canonical := true }).setTable y pick).obj? hp with
      | none => exact ⟨rfl, hra1, rfl⟩
      | some op =>
        refine ⟨by simp only [withRoot_setObj_ne he1], ?_, rfl⟩
        rw [Mem.obj?_setObj_ne _ _ (Ne.symm he)]; exact hra1

/-- The table's object for a stream slot, if usable (stage 1). -/
def fromTable1 (S : Stream V T) (m : Mem V) (y : NodeId) (r : Option Nat) : Option Nat :=
  match m.tableOf y with
  | some h0 => match m.obj? h0 with
    | some o0 => if o0.usable (ruleRRef S m.s y r) then some h0 else none
    | none => none
  | none => none

/-- The version read for a stream slot, stage 1, registered. -/
def load1 (sp : Spec V T) (S : Stream V T) (m : Mem V) (y : NodeId) (r : Option Nat) : Option (Mem V × Nat) :=
  match ruleRRef S m.s y r with
  | none => none
  | some r'' =>
    match S.versionAt r'' y with
    | none => none
    | some w =>
      some ((m.addObj (Obj.ofVersion sp w
        (if m.s ≤ r'' && isKeyLevel sp w.isData w.level then some m.s else none))).1.register
        (m.addObj (Obj.ofVersion sp w
          (if m.s ≤ r'' && isKeyLevel sp w.isData w.level then some m.s else none))).2)

/-- The first touch of a stream slot, stage 1: the table's object if usable,
else the version read and registered. -/
def loaded1 (sp : Spec V T) (S : Stream V T) (m : Mem V) (y : NodeId) (r : Option Nat) : Option (Mem V × Nat) :=
  match fromTable1 S m y r with
  | some h0 => some (m, h0)
  | none => load1 sp S m y r

/-- After the first touch: the slot names the object, and the writer makes it
canonical. -/
def after1 (m1 : Mem V) (hp : Nat) (y : NodeId) (h1 : Nat) (writer : Bool) : Mem V × Option Nat :=
  match (m1.swz hp y h1).obj? h1 with
  | some o1 => if writer && !o1.canonical then
      ((m1.swz hp y h1).makeCanonical hp y h1).1 |> fun m => (m, some ((m1.swz hp y h1).makeCanonical hp y h1).2)
    else (m1.swz hp y h1, some h1)
  | none => (m1.swz hp y h1, some h1)

theorem follow_eq1 (sp : Spec V T) (S : Stream V T) (m : Mem V) (hp : Nat) (y : NodeId) (w : Bool) :
    m.follow sp S hp y w = match (m.obj? hp).bind (·.slot? y) with
      | none => (m, none)
      | some (Slot.mem h) =>
        match m.obj? h with
        | some o => if w && !o.canonical then ((m.makeCanonical hp y h).1, some (m.makeCanonical hp y h).2)
          else (m, some h)
        | none => (m, none)
      | some (Slot.stream r) =>
        match loaded1 sp S m y r with
        | none => (m, none)
        | some (m1, h1) => after1 m1 hp y h1 w := by
  unfold Mem.follow loaded1 fromTable1 load1 after1 Mem.swz
  rfl

/-- What the first touch of stage 1 leaves: the memory with the same objects
and root, and a handle and table entries other than the root's. -/
theorem loaded1_facts {S : Stream V T} (hrs : RootSep sp m) {y : NodeId} (hy : y ≠ root) {r : Option Nat}
    {m1 : Mem V} {h1 : Nat} (h : loaded1 sp S m y r = some (m1, h1)) :
    m1.root = m.root ∧ m1.obj? m.root = m.obj? m.root ∧ h1 ≠ m.root ∧ m1.next ≠ m.root ∧
      (∀ h0, m1.tableOf y = some h0 → h0 ≠ m.root) ∧ m1.s = m.s := by
  have hnr : m.next ≠ m.root := by have := hrs.fresh; omega
  have htb : ∀ h0, m.tableOf y = some h0 → h0 ≠ m.root := fun h0 ht => hrs.tableNR y h0 ht hy
  unfold loaded1 fromTable1 load1 at h
  split at h
  · rename_i h0 hft
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨rfl, rfl, ?_, hnr, htb, rfl⟩
    split at hft
    · rename_i h0' ht
      split at hft
      · split at hft
        · simp only [Option.some.injEq] at hft; subst hft; exact htb _ ht
        · cases hft
      · cases hft
    · cases hft
  · split at h
    · cases h
    · rename_i r'' _
      split at h
      · cases h
      · rename_i w hw
        simp only [Option.some.injEq] at h
        have hwn := versionAt_node hw
        generalize hob : Obj.ofVersion sp w (if m.s ≤ r'' && isKeyLevel sp w.isData w.level then some m.s else none) = ob at h
        have hon : ob.node = y := by
          rw [← hob]; rw [(Obj.ofVersion_fields sp w _).1, hwn]
        have hobj : (m.addObj ob).1.obj? m.next = some ob := by rw [Mem.obj?_addObj]; simp
        unfold Mem.register at h
        rw [Mem.addObj_snd, hobj] at h
        simp only [hon, Mem.tableOf_addObj] at h
        cases ht : m.tableOf y with
        | none =>
          rw [ht] at h
          simp only [Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          refine ⟨rfl, ?_, Ne.symm (Ne.symm hnr), by simp only [Mem.setTable_next, Mem.addObj_next]; have := hrs.fresh; omega, ?_, rfl⟩
          · rw [Mem.obj?_setTable, Mem.obj?_addObj]; simp [Ne.symm hnr]
          · intro h0 ht0
            rw [Mem.tableOf_setTable] at ht0
            simp only [↓reduceIte, Option.some.injEq] at ht0
            subst ht0; exact hnr
        | some h0 =>
          rw [ht] at h
          simp only at h
          split at h
          · simp only [Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            refine ⟨rfl, ?_, hnr, by simp only [Mem.addObj_next]; have := hrs.fresh; omega, ?_, rfl⟩
            · rw [Mem.obj?_addObj]; simp [Ne.symm hnr]
            · intro h0' ht0; rw [Mem.tableOf_addObj] at ht0; exact htb h0' ht0
          · rw [Mem.obj?_addObj] at h
            have hne0 : h0 ≠ m.next := by
              intro he; subst he
              rename_i hne
              exact hne (by simp)
            simp only [hne0, ↓reduceIte] at h
            cases hx : m.obj? h0 with
            | none =>
              rw [hx] at h
              simp only [Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              refine ⟨rfl, ?_, hnr, by simp only [Mem.setTable_next, Mem.addObj_next]; have := hrs.fresh; omega, ?_, rfl⟩
              · rw [Mem.obj?_setTable, Mem.obj?_addObj]; simp [Ne.symm hnr]
              · intro h0' ht0
                rw [Mem.tableOf_setTable] at ht0
                simp only [↓reduceIte, Option.some.injEq] at ht0
                subst ht0; exact hnr
            | some o0 =>
              rw [hx] at h
              simp only at h
              split at h
              · simp only [Prod.mk.injEq] at h
                obtain ⟨rfl, rfl⟩ := h
                refine ⟨rfl, ?_, hnr, by simp only [Mem.setTable_next, Mem.addObj_next]; have := hrs.fresh; omega, ?_, rfl⟩
                · rw [Mem.obj?_setTable, Mem.obj?_addObj]; simp [Ne.symm hnr]
                · intro h0' ht0
                  rw [Mem.tableOf_setTable] at ht0
                  simp only [↓reduceIte, Option.some.injEq] at ht0
                  subst ht0; exact hnr
              · simp only [Prod.mk.injEq] at h
                obtain ⟨rfl, rfl⟩ := h
                refine ⟨rfl, ?_, htb h0 ht, by simp only [Mem.addObj_next]; have := hrs.fresh; omega, ?_, rfl⟩
                · rw [Mem.obj?_addObj]; simp [Ne.symm hnr]
                · intro h0' ht0; rw [Mem.tableOf_addObj] at ht0; exact htb h0' ht0

theorem fromTable1_withRoot {S S' : Stream V T} (hrs : RootSep sp m) {y : NodeId} (hy : y ≠ root)
    {r : Option Nat} (hrule : ruleRRef S' m.s y r = ruleRRef S m.s y r) :
    fromTable1 S' (m.withRoot oc) y r = fromTable1 S m y r := by
  unfold fromTable1
  rw [withRoot_tableOf, withRoot_s, hrule]
  cases ht : m.tableOf y with
  | none => rfl
  | some h0 => simp only; rw [withRoot_obj?_ne (hrs.tableNR y h0 ht hy)]

theorem load1_withRoot {S S' : Stream V T} (hrs : RootSep sp m) {y : NodeId} (hy : y ≠ root)
    {r : Option Nat} (hrule : ruleRRef S' m.s y r = ruleRRef S m.s y r)
    (hload : ∀ r'', ruleRRef S m.s y r = some r'' → S'.versionAt r'' y = S.versionAt r'' y) :
    load1 sp S' (m.withRoot oc) y r = (load1 sp S m y r).map (fun p => (p.1.withRoot oc, p.2)) := by
  have hnr : m.next ≠ m.root := by have := hrs.fresh; omega
  have htb : ∀ h0, m.tableOf y = some h0 → h0 ≠ m.root := fun h0 ht => hrs.tableNR y h0 ht hy
  unfold load1
  rw [withRoot_s, hrule]
  cases hr' : ruleRRef S m.s y r with
  | none => rfl
  | some r'' =>
    simp only
    rw [hload r'' hr']
    cases hw : S.versionAt r'' y with
    | none => rfl
    | some w =>
      simp only [Option.map_some]
      rw [withRoot_addObj hnr]
      simp only
      have hwn := versionAt_node hw
      congr 1
      rw [register_withRoot (by rw [Mem.addObj_root, Mem.addObj_snd]; exact Ne.symm (Ne.symm hnr))]
      intro o ho h0 ht
      rw [Mem.addObj_snd, Mem.obj?_addObj] at ho
      simp only [↓reduceIte, Option.some.injEq] at ho
      subst ho
      rw [(Obj.ofVersion_fields sp w _).1, hwn, Mem.tableOf_addObj] at ht
      rw [Mem.addObj_root]
      exact htb h0 ht

theorem loaded1_withRoot {S S' : Stream V T} (hrs : RootSep sp m) {y : NodeId} (hy : y ≠ root)
    {r : Option Nat} (hrule : ruleRRef S' m.s y r = ruleRRef S m.s y r)
    (hload : ∀ r'', ruleRRef S m.s y r = some r'' → S'.versionAt r'' y = S.versionAt r'' y) :
    loaded1 sp S' (m.withRoot oc) y r = (loaded1 sp S m y r).map (fun p => (p.1.withRoot oc, p.2)) := by
  unfold loaded1
  rw [fromTable1_withRoot hrs hy hrule]
  cases fromTable1 S m y r with
  | some h0 => rfl
  | none => exact load1_withRoot hrs hy hrule hload

theorem after1_withRoot {f : Time} {m1 : Mem V} (hra1 : m1.obj? m1.root = some oe) (hfr1 : m1.next ≠ m1.root)
    {hp : Nat} {y : NodeId} {h1 : Nat} (hh1 : h1 ≠ m1.root) (htbl1 : ∀ h0, m1.tableOf y = some h0 → h0 ≠ m1.root)
    (hr : RootRel sp f oc oe) (hrc : hp = m1.root → y ∈ pointees sp oc.hist ∨ sp.virt = false) (w : Bool) :
    ∃ oc' oe', RootRel sp f oc' oe' ∧ oc'.hist = oc.hist ∧ oe'.hist = oe.hist ∧
      (after1 m1 hp y h1 w).1.obj? m1.root = some oe' ∧ (after1 m1 hp y h1 w).1.root = m1.root ∧
      after1 (m1.withRoot oc) hp y h1 w = ((after1 m1 hp y h1 w).1.withRoot oc', (after1 m1 hp y h1 w).2) := by
  unfold after1
  rw [swz_withRoot y h1 ⟨hra1, hfr1⟩]
  have hr2 : (m1.swz hp y h1).root = m1.root := swz_root' _ _ _ _
  have hro2 : (m1.swz hp y h1).obj? m1.root =
      some (if hp = m1.root then oe.setSlot y (Slot.mem h1) else oe) := by
    rw [swz_obj?_root, hra1]; split <;> rfl
  have hrr2 : RootRel sp f (if hp = m1.root then oc.setSlot y (Slot.mem h1) else oc)
      (if hp = m1.root then oe.setSlot y (Slot.mem h1) else oe) := by
    by_cases he : hp = m1.root
    · simp only [he, ↓reduceIte]; exact hr.setSlot (hrc he) _
    · simp only [he, ↓reduceIte]; exact hr
  have hh2 : (if hp = m1.root then oc.setSlot y (Slot.mem h1) else oc).hist = oc.hist := by split <;> rfl
  have hh2' : (if hp = m1.root then oe.setSlot y (Slot.mem h1) else oe).hist = oe.hist := by split <;> rfl
  generalize (if hp = m1.root then oc.setSlot y (Slot.mem h1) else oc) = oc2 at hrr2 hh2 ⊢
  generalize (if hp = m1.root then oe.setSlot y (Slot.mem h1) else oe) = oe2 at hrr2 hh2' hro2 ⊢
  have hh1' : h1 ≠ (m1.swz hp y h1).root := by rw [hr2]; exact hh1
  rw [withRoot_obj?_ne hh1']
  cases ho1 : (m1.swz hp y h1).obj? h1 with
  | none => exact ⟨oc2, oe2, hrr2, hh2, hh2', hro2, hr2, rfl⟩
  | some o1 =>
    simp only
    split
    · have htbl2 : ∀ h0, (m1.swz hp y h1).tableOf y = some h0 → h0 ≠ (m1.swz hp y h1).root := by
        intro h0 ht; rw [hr2]
        have : (m1.swz hp y h1).tableOf y = m1.tableOf y := by unfold Mem.swz; split <;> rfl
        rw [this] at ht; exact htbl1 h0 ht
      have hra2 : (m1.swz hp y h1).obj? (m1.swz hp y h1).root = some oe2 := by rw [hr2]; exact hro2
      rw [makeCanonical_eq, makeCanonical_eq, mcPick_withRoot hh1' htbl2]
      obtain ⟨p1, p2, p3⟩ := pickTail_withRoot (oc := oc2) hra2 (hp := hp) (y := y) (mcPick_ne hh1' htbl2)
      rw [p1]
      rw [hr2] at p2 p3
      refine ⟨_, _, ?_, ?_, ?_, p2, by rw [p3], rfl⟩
      · by_cases he : hp = m1.root
        · simp only [swz_root', he, ↓reduceIte]
          exact hrr2.setSlot (by
            rcases hrc he with h | h
            · left; rw [show oc2.hist = oc.hist from hh2]; exact h
            · right; exact h) _
        · simp only [swz_root', he, ↓reduceIte]; exact hrr2
      · split <;> simp [hh2]
      · split <;> simp [hh2']
    · exact ⟨oc2, oe2, hrr2, hh2, hh2', hro2, hr2, rfl⟩

/-- The writer's follow, stage 1, on the memory with the other root object. -/
theorem follow_withRoot {f : Time} {S S' : Stream V T} (hrs : RootSep sp m) (hra : m.obj? m.root = some oe)
    (hr : RootRel sp f oc oe) {hp : Nat} {y : NodeId} (hy : y ≠ root)
    (hsl : hp ≠ m.root ∨ y ∈ pointees sp oc.hist ∨ sp.virt = false)
    (hrule : ∀ r, ruleRRef S' m.s y r = ruleRRef S m.s y r)
    (hload : ∀ r r'', (m.obj? hp).bind (·.slot? y) = some (Slot.stream r) → ruleRRef S m.s y r = some r'' →
      S'.versionAt r'' y = S.versionAt r'' y) (w : Bool) :
    ∃ oc' oe', RootRel sp f oc' oe' ∧ oc'.hist = oc.hist ∧ oe'.hist = oe.hist ∧
      (m.follow sp S hp y w).1.obj? m.root = some oe' ∧ (m.follow sp S hp y w).1.root = m.root ∧
      (m.withRoot oc).follow sp S' hp y w = ((m.follow sp S hp y w).1.withRoot oc', (m.follow sp S hp y w).2) := by
  have hnr : m.next ≠ m.root := by have := hrs.fresh; omega
  have htb : ∀ h0, m.tableOf y = some h0 → h0 ≠ m.root := fun h0 ht => hrs.tableNR y h0 ht hy
  have hslot : ((m.withRoot oc).obj? hp).bind (·.slot? y) = (m.obj? hp).bind (·.slot? y) := by
    by_cases he : hp = m.root
    · subst he
      rw [withRoot_obj?_root hra, hra]
      simp only [Option.bind_some]
      rcases hsl with hsl | hsl | hsl
      · exact absurd rfl hsl
      · exact hr.slots y hsl
      · rw [hr.nv hsl]
    · rw [withRoot_obj?_ne he]
  have hrc : hp = m.root → y ∈ pointees sp oc.hist ∨ sp.virt = false := by
    intro he; rcases hsl with h | h
    · exact absurd he h
    · exact h
  rw [follow_eq1, follow_eq1, hslot]
  cases hsy : (m.obj? hp).bind (·.slot? y) with
  | none => exact ⟨oc, oe, hr, rfl, rfl, hra, rfl, rfl⟩
  | some sl =>
    cases sl with
    | mem h =>
      simp only
      have hh : h ≠ m.root := by
        cases hop : m.obj? hp with
        | none => rw [hop] at hsy; cases hsy
        | some op =>
          rw [hop] at hsy
          exact hrs.slotsNR hp op y h hop hsy hy
      rw [withRoot_obj?_ne hh]
      cases ho : m.obj? h with
      | none => exact ⟨oc, oe, hr, rfl, rfl, hra, rfl, rfl⟩
      | some o =>
        simp only
        split
        · rw [makeCanonical_eq, makeCanonical_eq, mcPick_withRoot hh htb]
          obtain ⟨p1, p2, p3⟩ := pickTail_withRoot (oc := oc) hra (hp := hp) (y := y) (mcPick_ne hh htb)
          rw [p1]
          refine ⟨_, _, ?_, ?_, ?_, p2, p3, rfl⟩
          · by_cases he : hp = m.root
            · simp only [he, ↓reduceIte]; exact hr.setSlot (hrc he) _
            · simp only [he, ↓reduceIte]; exact hr
          · split <;> rfl
          · split <;> rfl
        · exact ⟨oc, oe, hr, rfl, rfl, hra, rfl, rfl⟩
    | stream r =>
      simp only
      rw [loaded1_withRoot hrs hy (hrule r) (fun r'' h => hload r r'' hsy h)]
      cases hl : loaded1 sp S m y r with
      | none => exact ⟨oc, oe, hr, rfl, rfl, hra, rfl, rfl⟩
      | some p =>
        obtain ⟨m1, h1⟩ := p
        simp only [Option.map_some]
        obtain ⟨hr1, ho1, hh1, hn1, ht1, -⟩ := loaded1_facts hrs hy hl
        have hra1 : m1.obj? m1.root = some oe := by rw [hr1, ho1]; exact hra
        obtain ⟨oc', oe', h1', h2', h3', h4', h5', h6'⟩ := after1_withRoot (sp := sp) (oc := oc) hra1
          (by rw [hr1]; exact hn1) (y := y) (hp := hp) (by rw [hr1]; exact hh1) (by rw [hr1]; exact ht1) hr
          (by rw [hr1]; exact hrc) w
        rw [hr1] at h4' h5'
        exact ⟨oc', oe', h1', h2', h3', h4', h5', h6'⟩

end Loader1

/-! ## The rerun's change on the memory with the other root object -/

section Change1

variable {sp : Spec V T} {P P' : Struct V} {j : Time} {m : Mem V} {oc oe : Obj V}

theorem srcOK_congrP (hReach : ∀ x, reachable sp P' (j - 1) x = reachable sp P (j - 1) x)
    (hPn : ∀ x, reachable sp P (j - 1) x = true →
      (P'.get? x).map (fun n => sp.live (n.hist.upTo (j - 1))) = (P.get? x).map (fun n => sp.live (n.hist.upTo (j - 1))))
    (y : NodeId) (p : Nat × Obj V) : srcOK sp P' j y p = srcOK sp P j y p := by
  unfold srcOK
  rw [hReach]
  cases hr : reachable sp P (j - 1) p.2.node
  · simp
  · have := hPn p.2.node hr
    cases h1 : P'.get? p.2.node <;> cases h2 : P.get? p.2.node <;> rw [h1, h2] at this <;> simp at this
    all_goals first | rfl | simp [this]

theorem srcOK_rootRel {f : Time} (hReach : ∀ x, reachable sp P' (j - 1) x = reachable sp P (j - 1) x)
    (hPn : ∀ x, reachable sp P (j - 1) x = true →
      (P'.get? x).map (fun n => sp.live (n.hist.upTo (j - 1))) = (P.get? x).map (fun n => sp.live (n.hist.upTo (j - 1))))
    (hPr : ∀ n, P.get? root = some n → ∀ y ∈ sp.live (n.hist.upTo (j - 1)), y ∈ pointees sp oc.hist)
    (hr : RootRel sp f oc oe) (hnode : oe.node = root) (y : NodeId) (r : Nat) :
    srcOK sp P' j y (r, oc) = srcOK sp P j y (r, oe) ∧
      (srcOK sp P j y (r, oe) = true → oc.slot? y = oe.slot? y) := by
  cases hv : sp.virt with
  | false =>
    rw [hr.nv hv]
    exact ⟨srcOK_congrP hReach hPn y _, fun _ => rfl⟩
  | true =>
    have hnc : oc.node = root := by rw [hr.node]; exact hnode
    unfold srcOK
    simp only [hnc, hnode, hReach]
    cases hrr : reachable sp P (j - 1) root
    · simp
    · have := hPn root hrr
      cases h2 : P.get? root with
      | none =>
        rw [h2] at this
        have h1 : P'.get? root = none := by
          cases h1 : P'.get? root <;> rw [h1] at this <;> simp at this ⊢
        rw [h1]; simp
      | some n =>
        obtain ⟨n', h1, hl⟩ : ∃ n', P'.get? root = some n' ∧
            sp.live (n'.hist.upTo (j - 1)) = sp.live (n.hist.upTo (j - 1)) := by
          rw [h2] at this
          cases h1 : P'.get? root <;> rw [h1] at this <;> simp at this
          exact ⟨_, rfl, this⟩
        rw [h1]
        simp only [hl]
        by_cases hy : y ∈ sp.live (n.hist.upTo (j - 1))
        · have hyc := hPr n h2 y hy
          have hs := hr.slots y hyc
          refine ⟨?_, fun _ => hs⟩
          rw [hs, hr.canonical]
        · exact ⟨by simp [hy], fun h => by simp [hy] at h⟩

theorem srcSlot1_withRoot {f : Time} (hReach : ∀ x, reachable sp P' (j - 1) x = reachable sp P (j - 1) x)
    (hPn : ∀ x, reachable sp P (j - 1) x = true →
      (P'.get? x).map (fun n => sp.live (n.hist.upTo (j - 1))) = (P.get? x).map (fun n => sp.live (n.hist.upTo (j - 1))))
    (hPr : ∀ n, P.get? root = some n → ∀ y ∈ sp.live (n.hist.upTo (j - 1)), y ∈ pointees sp oc.hist)
    (hnd : (m.objs.map (·.1)).Nodup) (hra : m.obj? m.root = some oe) (hr : RootRel sp f oc oe)
    (hnode : oe.node = root) (y : NodeId) :
    srcSlot sp P' j (m.withRoot oc) y = srcSlot sp P j m y := by
  unfold srcSlot Mem.withRoot
  simp only
  rw [List.find?_map]
  have hcongr : m.objs.find? (srcOK sp P' j y ∘ (fun p => if p.1 == m.root then (m.root, oc) else p)) =
      m.objs.find? (srcOK sp P j y) := by
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
      exact (srcOK_rootRel hReach hPn hPr hr hnode y _).1
    · have : (p.1 == m.root) = false := by simp [he]
      simp only [this, Bool.false_eq_true, ↓reduceIte]
      exact srcOK_congrP hReach hPn y p
  rw [hcongr]
  cases hf : m.objs.find? (srcOK sp P j y) with
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
      exact (srcOK_rootRel hReach hPn hPr hr hnode y _).2 hsrc
    · have : (p.1 == m.root) = false := by simp [he]
      simp only [this, Bool.false_eq_true, ↓reduceIte]

theorem NS1_withRoot {f : Time} (hReach : ∀ x, reachable sp P' (j - 1) x = reachable sp P (j - 1) x)
    (hPn : ∀ x, reachable sp P (j - 1) x = true →
      (P'.get? x).map (fun n => sp.live (n.hist.upTo (j - 1))) = (P.get? x).map (fun n => sp.live (n.hist.upTo (j - 1))))
    (hPr : ∀ n, P.get? root = some n → ∀ y ∈ sp.live (n.hist.upTo (j - 1)), y ∈ pointees sp oc.hist)
    (hnd : (m.objs.map (·.1)).Nodup) (hra : m.obj? m.root = some oe) (hr : RootRel sp f oc oe)
    (hnode : oe.node = root) (y : NodeId) :
    NS1 sp P' j (m.withRoot oc) y = NS1 sp P j m y := by
  unfold NS1
  rw [withRoot_canonicalOf hra hr.canonical, srcSlot1_withRoot hReach hPn hPr hnd hra hr hnode]

/-- Any canonical object's slot for y, on the memory with the other root object:
the same when both root objects have the same slot for y. -/
theorem anySlot_withRoot (hnd : (m.objs.map (·.1)).Nodup) (hra : m.obj? m.root = some oe)
    (hc : oc.canonical = oe.canonical) {y : NodeId} (hsl : oc.slot? y = oe.slot? y) :
    anySlot (m.withRoot oc) y = anySlot m y := by
  unfold anySlot Mem.withRoot
  simp only
  rw [List.find?_map]
  have hcongr : m.objs.find? ((fun p => p.2.canonical && (p.2.slot? y).isSome) ∘
      (fun p => if p.1 == m.root then (m.root, oc) else p)) =
      m.objs.find? (fun p => p.2.canonical && (p.2.slot? y).isSome) := by
    apply find?_congr_of_mem
    intro p hp
    simp only [Function.comp]
    by_cases he : p.1 = m.root
    · have hpo : p.2 = oe := by
        have := obj?_of_mem_objs hnd hp
        rw [he, hra] at this
        exact (Option.some.inj this).symm
      have : (p.1 == m.root) = true := by simp [he]
      simp only [this, ↓reduceIte, hpo, hc, hsl]
    · have : (p.1 == m.root) = false := by simp [he]
      simp only [this, Bool.false_eq_true, ↓reduceIte]
  rw [hcongr]
  cases hf : m.objs.find? (fun p => p.2.canonical && (p.2.slot? y).isSome) with
  | none => rfl
  | some p =>
    simp only [Option.map_some, Option.bind_some]
    by_cases he : p.1 = m.root
    · have hp := List.mem_of_find?_eq_some hf
      have hpo : p.2 = oe := by
        have := obj?_of_mem_objs hnd hp
        rw [he, hra] at this
        exact (Option.some.inj this).symm
      have : (p.1 == m.root) = true := by simp [he]
      simp only [this, ↓reduceIte, hpo, hsl]
    · have : (p.1 == m.root) = false := by simp [he]
      simp only [this, Bool.false_eq_true, ↓reduceIte]

theorem updObj1_congr {m1 m1' : Mem V} (hns : ∀ y, NS1 sp P' j m1' y = NS1 sp P j m1 y) {v : V}
    (hany : ∀ y ∈ sp.ptrs v, NS1 sp P j m1 y = none → anySlot m1' y = anySlot m1 y) (o : Obj V) :
    updObj sp P' j m1' o v = updObj sp P j m1 o v := by
  unfold updObj
  generalize ({ o with hist := o.hist ++ [⟨j, v⟩] } : Obj V) = o1
  generalize sp.ptrs v = L at hany ⊢
  induction L generalizing o1 with
  | nil => rfl
  | cons y L ih =>
    simp only [List.foldl_cons]
    have : upd1 sp P' j m1' o1 y = upd1 sp P j m1 o1 y := by
      unfold upd1
      rw [newSlot_eq, newSlot_eq, hns y]
      cases hn : NS1 sp P j m1 y with
      | some sl => rfl
      | none => simp only [Option.none_or]; rw [hany y List.mem_cons_self hn]
    rw [this, ih (upd1 sp P j m1 o1 y) (fun z hz => hany z (List.mem_cons_of_mem _ hz))]

theorem applyChange1_withRoot (hvl : VirtLiveOK sp) {f : Time} {c : Changes V}
    (hReach : ∀ x, reachable sp P' (j - 1) x = reachable sp P (j - 1) x)
    (hPn : ∀ x, reachable sp P (j - 1) x = true →
      (P'.get? x).map (fun n => sp.live (n.hist.upTo (j - 1))) = (P.get? x).map (fun n => sp.live (n.hist.upTo (j - 1))))
    (hPr : ∀ n, P.get? root = some n → ∀ y ∈ sp.live (n.hist.upTo (j - 1)), y ∈ pointees sp oc.hist)
    (hnd : (c.new.map (·.id)).Nodup)
    (hradds : sp.virt = true → ∀ a ∈ c.adds, a.1 = root → ∃ nn ∈ c.new, a.2 = sp.rootVal nn.id)
    (hptrs : sp.virt = true → ∀ z, sp.ptrs (sp.rootVal z) = [z])
    (hrs : RootSep sp m) (hnd' : (m.objs.map (·.1)).Nodup) (hfr : ∀ h, m.next ≤ h → m.obj? h = none)
    (hra : m.obj? m.root = some oe) (hr : RootRel sp f oc oe) (hnode : oe.node = root)
    (hvalsE : sp.virt = true → ∀ e ∈ oe.hist, ∃ z, e.val = sp.rootVal z)
    (hany : ∀ a ∈ c.adds, ∀ y ∈ sp.ptrs a.2, NS1 sp P j (c.new.foldl addNew m) y = none →
      anySlot ((c.new.foldl addNew m).withRoot oc) y = anySlot (c.new.foldl addNew m) y) :
    ∃ oc' oe', RootRel sp f oc' oe' ∧ (m.applyChange sp P j c).obj? m.root = some oe' ∧
      (m.applyChange sp P j c).root = m.root ∧ oe'.node = root ∧
      (sp.virt = true → ∀ e ∈ oe'.hist, ∃ z, e.val = sp.rootVal z) ∧
      (∃ X, oc'.hist = oc.hist ++ X ∧ oe'.hist = oe.hist ++ X) ∧
      (m.withRoot oc).applyChange sp P' j c = (m.applyChange sp P j c).withRoot oc' := by
  rw [applyChange_eq, applyChange_eq, foldl_addNew_withRoot c.new m hrs.fresh]
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
  have hns : ∀ y, NS1 sp P' j ((c.new.foldl addNew m).withRoot oc) y = NS1 sp P j (c.new.foldl addNew m) y :=
    NS1_withRoot hReach hPn hPr hnd1 hra1 hr hnode
  generalize hm1 : c.new.foldl addNew m = m1 at hr1 hra1 hnd1 htbl1 hns hany
  have hcanNew : ∀ nn ∈ c.new, ∃ hn, m1.canonicalOf nn.id = some hn := by
    intro nn hnn
    obtain ⟨hn, -, hc, -⟩ := addNew_canonicalOf_new m c.new hnd hnn
    rw [hm1] at hc
    exact ⟨hn, hc⟩
  have key : ∀ (L : List (NodeId × V)), (∀ a ∈ L, a ∈ c.adds) →
      ∀ (ma : Mem V) (oc1 oe1 : Obj V), ma.obj? m.root = some oe1 → ma.root = m.root → ma.table = m1.table →
        RootRel sp f oc1 oe1 → oe1.node = root → (sp.virt = true → ∀ e ∈ oe1.hist, ∃ z, e.val = sp.rootVal z) →
        ∃ oc' oe', RootRel sp f oc' oe' ∧ (L.foldl (addsStep sp P j m1) ma).obj? m.root = some oe' ∧
          (L.foldl (addsStep sp P j m1) ma).root = m.root ∧ oe'.node = root ∧
          (sp.virt = true → ∀ e ∈ oe'.hist, ∃ z, e.val = sp.rootVal z) ∧
          (∃ X, oc'.hist = oc1.hist ++ X ∧ oe'.hist = oe1.hist ++ X) ∧
          L.foldl (addsStep sp P' j (m1.withRoot oc)) (ma.withRoot oc1) =
            (L.foldl (addsStep sp P j m1) ma).withRoot oc' := by
    intro L
    induction L with
    | nil =>
      intro _ ma oc1 oe1 hra' hrt' _ hrr hn' hv'
      exact ⟨oc1, oe1, hrr, hra', hrt', hn', hv', ⟨[], by simp, by simp⟩, rfl⟩
    | cons a L ih =>
      intro hL ma oc1 oe1 hra' hrt' htb hrr hn' hv'
      simp only [List.foldl_cons]
      have hra'' : ma.obj? ma.root = some oe1 := by rw [hrt']; exact hra'
      have hany' := hany a (hL a List.mem_cons_self)
      have hstep : ∃ oc2 oe2, RootRel sp f oc2 oe2 ∧ (addsStep sp P j m1 ma a).obj? m.root = some oe2 ∧
          (addsStep sp P j m1 ma a).root = m.root ∧ (addsStep sp P j m1 ma a).table = m1.table ∧
          oe2.node = root ∧ (sp.virt = true → ∀ e ∈ oe2.hist, ∃ z, e.val = sp.rootVal z) ∧
          (∃ X, oc2.hist = oc1.hist ++ X ∧ oe2.hist = oe1.hist ++ X) ∧
          addsStep sp P' j (m1.withRoot oc) (ma.withRoot oc1) a = (addsStep sp P j m1 ma a).withRoot oc2 := by
        unfold addsStep
        rw [withRoot_canonicalOf hra'' hrr.canonical]
        cases hca : ma.canonicalOf a.1 with
        | none => exact ⟨oc1, oe1, hrr, hra', hrt', htb, hn', hv', ⟨[], by simp, by simp⟩, rfl⟩
        | some h =>
          simp only
          by_cases hh : h = m.root
          · subst hh
            rw [← hrt', withRoot_obj?_root hra'', hra'']
            simp only
            rw [withRoot_setObj_root _ (updObj sp P j m1 oe1 a.2)]
            rw [updObj1_congr hns hany']
            have hroot' : (ma.setObj ma.root (updObj sp P j m1 oe1 a.2)).obj? ma.root =
                some (updObj sp P j m1 oe1 a.2) := Mem.obj?_setObj_self _ _ _
            obtain ⟨u1, -, -, u4, -, -⟩ := updObj_core sp P j m1 oe1 a.2
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
              have hupd : ∀ o : Obj V, updObj sp P j m1 o a.2 =
                  ({ o with hist := o.hist ++ [⟨j, a.2⟩] } : Obj V).putSlot nn.id (Slot.mem hn) := by
                intro o
                unfold updObj
                rw [ha2, hpz]
                simp only [List.foldl_cons, List.foldl_nil]
                unfold upd1
                rw [newSlot_eq]
                unfold NS1
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
              rw [updObj1_congr hns hany', withRoot_setObj_ne hh']
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

end Change1

/-! ## The rerun's walk on the memory with the other root object -/

section Walk1

variable {sp : Spec V T} {m : Mem V} {oc oe : Obj V}

theorem reachOnPath1_congrP {S : Stream V T} {P P' : Struct V} {j : Time} {path : List NodeId}
    (hP : ∀ p ∈ path, (P'.get? p).map (fun n => sp.live (n.hist.upTo (j - 1))) =
      (P.get? p).map (fun n => sp.live (n.hist.upTo (j - 1)))) (m : Mem V) (x : NodeId) :
    m.reachOnPath sp S P' j path x = m.reachOnPath sp S P j path x := by
  unfold Mem.reachOnPath
  split
  · rfl
  · simp only
    congr 1
    apply find?_congr_of_mem
    intro p hp
    have := hP p hp
    cases h1 : P'.get? p <;> cases h2 : P.get? p <;> rw [h1, h2] at this <;> simp at this
    all_goals first | rfl | (cases m.canonicalOf p <;> simp [this])

theorem RootSep.of_rerun {db : DB V T} {K k : Nat} {S : Stream V T} (hinv : Inv sp db k)
    (hm : MemInv sp db K m) (hr : RInv sp S m) : RootSep sp m := by
  obtain ⟨-, o0, ho0, -, hn0⟩ := hm.root
  refine RootSep.mk' ⟨o0, ho0, hn0⟩ hm.fresh hm.tbl ?_ ?_
  · intro h o ho y h' hs
    obtain ⟨o', ho', hn', -⟩ := hm.memSlot h o y h' ho hs
    exact ⟨o', ho', hn'⟩
  · intro h o ho y hy
    obtain ⟨-, ⟨n, hn, hh, -⟩, -⟩ := hm.canon h o ho (hr.canon h o ho)
    rw [hh, mem_pointees] at hy
    obtain ⟨e, he, hye⟩ := hy
    exact hinv.ptr_ne_root hn (mem_upTo.mp he).1 hye

/-- The writer reaches a node of its path the same way on the memory with the
other root object, the cut stream for the startup's stream. -/
theorem reachOnPath1_withRoot {f : Time} {S S' : Stream V T} {P : Struct V} {j : Time} {path : List NodeId}
    (hPr : ∀ n, P.get? root = some n → ∀ x ∈ sp.live (n.hist.upTo (j - 1)), x ∈ pointees sp oc.hist)
    (hPnr : ∀ p n, P.get? p = some n → ∀ x ∈ sp.live (n.hist.upTo (j - 1)), x ≠ root)
    (hrs : RootSep sp m) (hra : m.obj? m.root = some oe) (hr : RootRel sp f oc oe)
    (hrule : ∀ y r, ruleRRef S' m.s y r = ruleRRef S m.s y r) (x : NodeId)
    (hload : ∀ h o r r'', m.obj? h = some o → o.slot? x = some (Slot.stream r) → ruleRRef S m.s x r = some r'' →
      S'.versionAt r'' x = S.versionAt r'' x) :
    ∃ oc' oe', RootRel sp f oc' oe' ∧ oc'.hist = oc.hist ∧ oe'.hist = oe.hist ∧
      (m.reachOnPath sp S P j path x).obj? m.root = some oe' ∧ (m.reachOnPath sp S P j path x).root = m.root ∧
      (m.withRoot oc).reachOnPath sp S' P j path x = (m.reachOnPath sp S P j path x).withRoot oc' := by
  have hcan : ∀ z, (m.withRoot oc).canonicalOf z = m.canonicalOf z := withRoot_canonicalOf hra hr.canonical
  unfold Mem.reachOnPath
  simp only [hcan]
  split
  · exact ⟨oc, oe, hr, rfl, rfl, hra, rfl, rfl⟩
  · split
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
          have hsl : hp ≠ m.root ∨ x ∈ pointees sp oc.hist ∨ sp.virt = false := by
            by_cases he : hp = m.root
            · right; left
              have hpr : p = root := by
                by_cases hne : p = root
                · exact hne
                · exact absurd he (hrs.tableNR p hp ht hne)
              subst hpr
              exact hPr np hnp x hpred
            · left; exact he
          obtain ⟨oc', oe', h1, h2, h3, h4, h5, h6⟩ := follow_withRoot (S := S) (S' := S') hrs hra hr hx hsl
            (hrule x) (fun r r'' hs hr'' => by
              cases hop : m.obj? hp with
              | none => rw [hop] at hs; cases hs
              | some op => rw [hop] at hs; exact hload hp op r r'' hop hs hr'') true
          refine ⟨oc', oe', h1, h2, h3, h4, h5, ?_⟩
          rw [h6]
      · exact ⟨oc, oe, hr, rfl, rfl, hra, rfl, rfl⟩
    · exact ⟨oc, oe, hr, rfl, rfl, hra, rfl, rfl⟩

end Walk1

/-! ## The rerun's transactions on the memory with the other root object -/

section Rerun1

variable {sp : Spec V T} {al : Algo V T} {ts : List T}

/-- The writer's walk of a transaction of the rerun, on the memory with the
other root object and the cut stream: the walk on the startup's memory from the
whole stream, with the other root object. -/
theorem walk1_sim (hok : RunOK sp al ts) (hj : al.stillDirty = javaTest sp) (hmk : al.mark = true)
    (hev : EvictRunOK sp al ts) {k K c : Nat} (hk : k ≤ ts.length) (hKk : K < k)
    (hsK : lastSp (st sp al ts k).S ≤ K) (hcs : c ≤ lastSp (st sp al ts k).S)
    (hcK : ∀ x v, reachable sp (st sp al ts k).P K x = true → (st sp al ts k).S.lv x = some v → c ≤ v.recNo)
    {P : Struct V} (hP : SameNodes P (st sp al ts K).P)
    {path : List NodeId} (hpath : ∀ p ∈ path, reachable sp (st sp al ts k).P K p = true) {f : Time} :
    ∀ (L : List NodeId), (∀ x ∈ L, x ∈ path) → ∀ (m : Mem V) (oc oe : Obj V),
      RInv sp (st sp al ts k).S m → MemInv sp (st sp al ts k) K m →
      m.obj? m.root = some oe → RootRel sp f oc oe →
      (∀ n, P.get? root = some n → ∀ x ∈ sp.live (n.hist.upTo K), x ∈ pointees sp oc.hist) →
      ∃ oc' oe', RootRel sp f oc' oe' ∧ oc'.hist = oc.hist ∧ oe'.hist = oe.hist ∧
        (L.foldl (Mem.reachOnPath sp (st sp al ts k).S P (K + 1) path) m).obj? m.root = some oe' ∧
        (L.foldl (Mem.reachOnPath sp (st sp al ts k).S P (K + 1) path) m).root = m.root ∧
        L.foldl (Mem.reachOnPath sp (cutStream c (st sp al ts k).S) P (K + 1) path) (m.withRoot oc) =
          (L.foldl (Mem.reachOnPath sp (st sp al ts k).S P (K + 1) path) m).withRoot oc' := by
  have hst : AlgOK sp al := algOK_of sp al (Or.inl hj)
  have hls : LiveSub sp := hok.1.liveSub
  have hinvk := inv_st sp al ts hok hst k hk
  have hinvK := inv_st sp al ts hok hst K (by omega)
  have hctx := pctx_st hok hst hk
  have hkK := kctx_st sp al ts hok hj (Nat.le_of_lt hKk) hk
  have hPnr : ∀ p n, P.get? p = some n → ∀ x ∈ sp.live (n.hist.upTo (K + 1 - 1)), x ≠ root := by
    intro p n hn x hx
    rw [Nat.add_sub_cancel] at hx
    obtain ⟨e, he, hxe⟩ := hls _ _ hx
    rw [hP p] at hn
    exact hinvK.ptr_ne_root hn (mem_upTo.mp he).1 hxe
  intro L
  induction L with
  | nil => intro _ m oc oe _ _ hra hr _; exact ⟨oc, oe, hr, rfl, rfl, hra, rfl, rfl⟩
  | cons x L ih =>
    intro hL m oc oe hr hm hra hrr hPr
    simp only [List.foldl_cons]
    have hrs := RootSep.of_rerun hinvk hm hr
    have hxp : x ∈ path := hL x List.mem_cons_self
    obtain ⟨oc1, oe1, h1, h2, h3, h4, h5, h6⟩ := reachOnPath1_withRoot (S := (st sp al ts k).S)
      (S' := cutStream c (st sp al ts k).S) (j := K + 1) (path := path)
      (fun n hn y hy => by rw [Nat.add_sub_cancel] at hy; exact hPr n hn y hy) hPnr hrs hra hrr
      (fun y r => by rw [hm.sEq]; exact ruleRRef_cut hcs y r) x
      (fun h o r r'' ho hs hr'' => by
        have hf := hr.fresh h o ho x r hs
        rw [hm.sEq, hf] at hr''
        obtain ⟨v, hv, hvr⟩ := Option.map_eq_some_iff.mp hr''
        subst hvr
        exact versionAt_cut_ge (hcK x v (hpath x hxp) hv) x)
    have hr' := hr.reachOnPath hok hj hmk hev hk hKk hsK hm hP hpath x
    have hm' := (hm.reachOnPath_ok hctx hkK hP hpath x).1
    obtain ⟨oc2, oe2, g1, g2, g3, g4, g5, g6⟩ := ih (fun y hy => hL y (List.mem_cons_of_mem _ hy)) _ oc1 oe1
      hr' hm' (by rw [h5]; exact h4) h1 (by rw [h2]; exact hPr)
    rw [h5] at g4 g5
    refine ⟨oc2, oe2, g1, by rw [g2, h2], by rw [g3, h3], g4, g5, ?_⟩
    rw [h6, g6]

/-- The last resort finds the slot that every object with a slot for y has. -/
theorem anySlot_uniform {m : Mem V} {y : NodeId} {sl : Slot}
    (hu : ∀ p ∈ m.objs, p.2.slot? y = none ∨ p.2.slot? y = some sl)
    (hex : ∃ p ∈ m.objs, p.2.canonical = true ∧ (p.2.slot? y).isSome = true) :
    anySlot m y = some sl := by
  unfold anySlot
  obtain ⟨p0, hp0, hc0, hs0⟩ := hex
  cases hf : m.objs.find? (fun p => p.2.canonical && (p.2.slot? y).isSome) with
  | none =>
    exfalso
    have := List.find?_eq_none.mp hf p0 hp0
    simp [hc0, hs0] at this
  | some p =>
    have hp := List.mem_of_find?_eq_some hf
    have hpr := List.find?_some hf
    simp only [Bool.and_eq_true] at hpr
    simp only [Option.bind_some]
    rcases hu p hp with h | h
    · rw [h] at hpr; simp at hpr
    · exact h

/-- The rerun's last resort for a pointee y of a new entry that has no canonical
object and no source (`NS1` none) is the same on the memory with the other root
object. Either both root objects have the same slot for y; or, with a virtual
root, y is a root child that only the startup's root from the whole stream
still points to: its entry is from before the startup pos, so y has no version
in the section (it would have a canonical object), every slot for it is the
same stream slot, to its latest version, and A-COPY gives an object other than
the root's with one (a written node that points to y, whose pointer is dead
since y has no source). -/
theorem anySlot_sim (hok : RunOK sp al ts) (hj : al.stillDirty = javaTest sp) {k K : Nat}
    (hk : k ≤ ts.length) (hKk : K < k) {P : Struct V} (hP : SameNodes P (st sp al ts K).P)
    {c : Changes V} (hnd : (c.new.map (·.id)).Nodup) (hcopy : CopyStep sp (st sp al ts K).P (K + 1) c)
    {mw : Mem V} (hr : RInv sp (st sp al ts k).S mw) (hm : MemInv sp (st sp al ts k) K mw)
    (hcan : ∀ x ∈ pathOf sp (st sp al ts K).P c (K + 1), mw.canonicalOf x ≠ none)
    {f : Time} {oc oe : Obj V} (hra : mw.obj? mw.root = some oe) (hrr : RootRel sp f oc oe)
    (hoe : ∀ e ∈ oe.hist, ∃ n, (st sp al ts k).P.get? root = some n ∧ e ∈ n.hist)
    (hafter : ∀ e ∈ oe.hist, lastSp (st sp al ts k).S < e.time → e ∈ oc.hist)
    {a : NodeId × V} (ha : a ∈ c.adds) {y : NodeId} (hy : y ∈ sp.ptrs a.2)
    (hns : NS1 sp P (K + 1) (c.new.foldl addNew mw) y = none) :
    anySlot ((c.new.foldl addNew mw).withRoot oc) y = anySlot (c.new.foldl addNew mw) y := by
  have hst : AlgOK sp al := algOK_of sp al (Or.inl hj)
  have hinvk := inv_st sp al ts hok hst k hk
  have hinvK := inv_st sp al ts hok hst K (by omega)
  have hkK := kctx_st sp al ts hok hj (Nat.le_of_lt hKk) hk
  have hnd1 := foldl_addNew_nodup c.new mw hm.fresh hm.nodup
  have hra1 : (c.new.foldl addNew mw).obj? (c.new.foldl addNew mw).root = some oe := by
    rw [foldl_addNew_root, foldl_addNew_old c.new mw mw.root (lt_next_of_obj? hm.fresh hra)]; exact hra
  by_cases hsl : oc.slot? y = oe.slot? y
  · exact anySlot_withRoot hnd1 hra1 hrr.canonical hsl
  have hv : sp.virt = true := by
    cases hv : sp.virt with
    | false => exact absurd (by rw [hrr.nv hv]) hsl
    | true => rfl
  have hyc : y ∉ pointees sp oc.hist := fun h => hsl (hrr.slots y h)
  have hnoC := hrr.noSlot hv y hyc
  have hsomeE : (oe.slot? y).isSome = true := by
    cases h : oe.slot? y with
    | none => rw [hnoC, h] at hsl; exact absurd rfl hsl
    | some _ => rfl
  obtain ⟨e, he, hye⟩ := (mem_pointees sp _ _).mp (hrr.keysE hv y hsomeE)
  obtain ⟨nR, hnR, heR⟩ := hoe e he
  obtain ⟨z, mz, htop, hez⟩ := (hinvk.vr hv).rootEntry nR hnR e heR
  have hyz : y = z := by
    rw [hez, (hinvk.vr hv).rootPtrs z] at hye; simpa using hye
  subst hyz
  have hes : e.time ≤ lastSp (st sp al ts k).S := by
    by_cases h : lastSp (st sp al ts k).S < e.time
    · exact absurd ((mem_pointees sp _ _).mpr ⟨e, hafter e he h, by
        rw [hez, (hinvk.vr hv).rootPtrs y]; exact List.mem_singleton_self y⟩) hyc
    · omega
  -- y has no canonical object.
  have hcanY : (c.new.foldl addNew mw).canonicalOf y = none := by
    unfold NS1 at hns
    cases h : (c.new.foldl addNew mw).canonicalOf y with
    | none => rfl
    | some _ => rw [h] at hns; simp at hns
  have hyn : y ∉ c.new.map (·.id) := by
    intro hyn
    obtain ⟨nn, hnn, hnny⟩ := List.mem_map.mp hyn
    obtain ⟨h0, -, hc0, -⟩ := addNew_canonicalOf_new mw c.new hnd hnn
    rw [hnny, hcanY] at hc0; cases hc0
  have htbl : ∀ y h, mw.tableOf y = some h → (mw.obj? h).isSome := by
    intro y h ht; obtain ⟨o, ho, -⟩ := hm.tbl y h ht; rw [ho]; rfl
  have hcanW : mw.canonicalOf y = none := by
    rw [← addNew_canonicalOf_old mw c.new hm.fresh htbl hyn]; exact hcanY
  -- y has no version in the section.
  have hnew : newest (st sp al ts k).S (lastSp (st sp al ts k).S) y = none := by
    cases hw : newest (st sp al ts k).S (lastSp (st sp al ts k).S) y with
    | none => rfl
    | some w =>
      exfalso
      obtain ⟨r, -, hwr⟩ := newest_some hw
      obtain ⟨-, -, ny, hny, -, -, hwd⟩ := hinvk.version_node hwr
      rw [htop.1, Option.some.injEq] at hny
      subst hny
      have hwh := (hinvk.vr hv).topVers y mz e.time htop r w hwr
      apply hm.coverSec y w hw (by rw [hwd]; exact htop.2.2.2.1)
      rw [hwh, upTo_of_forall _ _ (fun e' he' => by rw [htop.2.2.2.2.2 e' he']; exact hes)]
      exact htop.2.2.2.2.1
      exact hcanW
  -- Every slot for y is the same stream slot.
  have hu1 : ∀ h o, (c.new.foldl addNew mw).obj? h = some o → o.slot? y = none ∨
      o.slot? y = some (Slot.stream (((st sp al ts k).S.lv y).map (·.recNo))) := by
    intro h o ho
    rcases foldl_addNew_obj c.new hnd mw hm.fresh h o ho with ⟨-, ho'⟩ | ⟨-, nn, -, rfl, -⟩
    · cases hs : o.slot? y with
      | none => exact Or.inl rfl
      | some sl =>
        right
        cases sl with
        | mem h' =>
          exfalso
          obtain ⟨o', ho1, -, hto⟩ := hm.memSlot h o y h' ho' hs
          rcases hto with ht | ⟨hc', -⟩
          · rw [(Mem.canonicalOf_eq_some _ y h').mpr ⟨ht, o', ho1, hr.canon h' o' ho1⟩] at hcanW
            cases hcanW
          · rw [hr.canon h' o' ho1] at hc'; cases hc'
        | stream r =>
          have := hr.fresh h o ho' y r hs
          unfold ruleRRef at this
          rw [hnew] at this
          simp only at this
          rw [this]
    · left; simp [newObj, Obj.slot?]
  have hu : ∀ p ∈ (c.new.foldl addNew mw).objs, p.2.slot? y = none ∨
      p.2.slot? y = some (Slot.stream (((st sp al ts k).S.lv y).map (·.recNo))) :=
    fun p hp => hu1 p.1 p.2 (obj?_of_mem_objs hnd1 hp)
  have huC : ∀ p ∈ ((c.new.foldl addNew mw).withRoot oc).objs, p.2.slot? y = none ∨
      p.2.slot? y = some (Slot.stream (((st sp al ts k).S.lv y).map (·.recNo))) := by
    intro p hp
    unfold Mem.withRoot at hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    by_cases hqr : q.1 = (c.new.foldl addNew mw).root
    · have : (q.1 == (c.new.foldl addNew mw).root) = true := by simp [hqr]
      simp only [this, ↓reduceIte]
      exact Or.inl hnoC
    · have : (q.1 == (c.new.foldl addNew mw).root) = false := by simp [hqr]
      simp only [this, Bool.false_eq_true, ↓reduceIte]
      exact hu q hq
  -- An object other than the root's with a slot for y.
  obtain ⟨hz0, oz, hzr, hoz, hcoz, hslz⟩ : ∃ hz0 oz, hz0 ≠ mw.root ∧ mw.obj? hz0 = some oz ∧
      oz.canonical = true ∧ (oz.slot? y).isSome = true := by
    rcases hcopy a ha y hy hyn with hyp | ⟨z, hz, nz, hnz, hyz, hwz⟩
    · exact absurd hcanW (hcan y hyp)
    · obtain ⟨hz0, hcz⟩ := Option.ne_none_iff_exists'.mp (hcan z hz)
      obtain ⟨htz, oz, hoz, hcoz⟩ := (Mem.canonicalOf_eq_some _ z hz0).mp hcz
      obtain ⟨oz', hoz', hnoz⟩ := hm.tbl z hz0 htz
      rw [hoz, Option.some.injEq] at hoz'
      subst hoz'
      obtain ⟨-, ⟨nk, hnk, hhk, -, -⟩, -⟩ := hm.canon hz0 oz hoz hcoz
      rw [hnoz] at hnk
      obtain ⟨nk', hnk', -, -, hup⟩ := hkK.grow z nz hnz
      rw [hnk, Option.some.injEq] at hnk'
      subst hnk'
      have hzh : oz.hist = nz.hist := by
        rw [hhk, hup, upTo_of_forall _ _ (hinvK.times z nz hnz)]
      have hslz := hr.slotsAll hz0 oz hoz y (by rw [hzh]; exact hyz)
      have hzroot : z ≠ root := by
        rcases hwz with hw | hl
        · intro hzr; rw [hzr] at hw; simp [written, hv] at hw
        · -- a live pointer: z's object is a source, so NS1 is not none
          exfalso
          have hsrc : srcOK sp P (K + 1) y (hz0, oz) = true := by
            unfold srcOK
            simp only [hcoz, hslz, Bool.true_and, Nat.add_sub_cancel, hnoz, hP.reachable, hP z, hnz]
            rw [Nat.add_sub_cancel] at hl
            have := (mem_pathOf hz).1
            rw [Nat.add_sub_cancel] at this
            simp [this, hl]
          have hmem : (hz0, oz) ∈ (c.new.foldl addNew mw).objs := by
            apply mem_objs_of_obj?
            rw [foldl_addNew_old c.new mw hz0 (lt_next_of_obj? hm.fresh hoz)]; exact hoz
          unfold NS1 srcSlot at hns
          rw [hcanY] at hns
          simp only [Option.map_none, Option.none_or] at hns
          cases hf : (c.new.foldl addNew mw).objs.find? (srcOK sp P (K + 1) y) with
          | none =>
            exact List.find?_eq_none.mp hf _ hmem hsrc
          | some p =>
            rw [hf] at hns
            have hpr := List.find?_some hf
            unfold srcOK at hpr
            simp only [Bool.and_eq_true] at hpr
            simp only [Option.bind_some] at hns
            rw [hns] at hpr
            simp at hpr
      refine ⟨hz0, oz, ?_, hoz, hcoz, hslz⟩
      intro he0
      rw [he0, hra, Option.some.injEq] at hoz
      subst hoz
      obtain ⟨-, o0, ho0, -, hn0⟩ := hm.root
      rw [hra, Option.some.injEq] at ho0
      subst ho0
      exact hzroot (by rw [← hnoz, hn0])
  have hoz1 : (c.new.foldl addNew mw).obj? hz0 = some oz := by
    rw [foldl_addNew_old c.new mw hz0 (lt_next_of_obj? hm.fresh hoz)]; exact hoz
  have hzr1 : hz0 ≠ (c.new.foldl addNew mw).root := by rw [foldl_addNew_root]; exact hzr
  rw [anySlot_uniform hu ⟨(hz0, oz), mem_objs_of_obj? hoz1, hcoz, hslz⟩,
    anySlot_uniform huC ⟨(hz0, oz), mem_objs_of_obj? (by rw [withRoot_obj?_ne hzr1]; exact hoz1), hcoz, hslz⟩]

/-- One transaction of the rerun, on the memory with the other root object, the
cut stream, and the structure of the logical startup from the cut stream: the
transaction on the startup's memory from the whole stream, with the other root
object, which holds the root's history of that structure. -/
theorem rerunStep_sim (hok : RunOK sp al ts) (hph : PhysRunOK sp al ts) (hj : al.stillDirty = javaTest sp)
    (hmk : al.mark = true) (hev : EvictRunOK sp al ts) (hex : ExecRootOK sp) (hvl : VirtLiveOK sp)
    {k K c : Nat} (hk : k ≤ ts.length) (hsK : lastSp (st sp al ts k).S ≤ K) (hKk : K < k)
    (hcut : CutOK sp c (st sp al ts k) k)
    {accE accC : Mem V × Struct V} {oc oe : Obj V}
    (hr : RInv sp (st sp al ts k).S accE.1) (hm : MemInv sp (st sp al ts k) K accE.1)
    (hP : SameNodes accE.2 (st sp al ts K).P)
    (hag : CutAgree sp (lastFa (st sp al ts k).S) K (st sp al ts K).P accC.2)
    (hmC : accC.1 = accE.1.withRoot oc) (hra : accE.1.obj? accE.1.root = some oe)
    (hrr : RootRel sp (lastFa (st sp al ts k).S) oc oe)
    (hoc : ∀ n, accC.2.get? root = some n → oc.hist = n.hist)
    (hafter : ∀ e ∈ oe.hist, lastSp (st sp al ts k).S < e.time → e ∈ oc.hist) :
    ∃ oc' oe', (rerunStep sp (cutStream c (st sp al ts k).S) accC (K + 1)).1 =
        (rerunStep sp (st sp al ts k).S accE (K + 1)).1.withRoot oc' ∧
      (rerunStep sp (st sp al ts k).S accE (K + 1)).1.obj? (rerunStep sp (st sp al ts k).S accE (K + 1)).1.root =
        some oe' ∧
      RootRel sp (lastFa (st sp al ts k).S) oc' oe' ∧
      CutAgree sp (lastFa (st sp al ts k).S) (K + 1) (st sp al ts (K + 1)).P
        (rerunStep sp (cutStream c (st sp al ts k).S) accC (K + 1)).2 ∧
      (∀ n, (rerunStep sp (cutStream c (st sp al ts k).S) accC (K + 1)).2.get? root = some n →
        oc'.hist = n.hist) ∧
      (∀ e ∈ oe'.hist, lastSp (st sp al ts k).S < e.time → e ∈ oc'.hist) := by
  have hst : AlgOK sp al := algOK_of sp al (Or.inl hj)
  have hKt : K < ts.length := by omega
  have hls : LiveSub sp := hok.1.liveSub
  have hinvk := inv_st sp al ts hok hst k hk
  have hinvK := inv_st sp al ts hok hst K (by omega)
  have hinvK1 := inv_st sp al ts hok hst (K + 1) (by omega)
  have hctx := pctx_st hok hst hk
  have hkK := kctx_st sp al ts hok hj (Nat.le_of_lt hKk) hk
  have hkK1 := kctx_st sp al ts hok hj (K := K + 1) (by omega) hk
  have hfs := st_fa_le sp al ts hk
  have hcs : c ≤ lastSp (st sp al ts k).S := Nat.le_trans hcut.1 hfs
  have hfK : lastFa (st sp al ts k).S ≤ K := by omega
  -- Record K + 1 and its transaction, the same in the cut stream.
  have htr := st_trans sp al ts hok hst (j := K + 1) (k := k) (by omega) (by omega) hk
  simp only [Nat.add_sub_cancel] at htr
  obtain ⟨R, hR, hRt⟩ : ∃ R, (st sp al ts k).S[K + 1]? = some R ∧ R.trans = some ts[K] := by
    cases h : (st sp al ts k).S[K + 1]? with
    | none => rw [h] at htr; cases htr
    | some R => rw [h] at htr; exact ⟨R, rfl, htr⟩
  have hR' : (cutStream c (st sp al ts k).S)[K + 1]? = some R := by
    rw [cutStream_getElem?_ge (by omega)]; exact hR
  rw [rerunStep_eq sp _ accE hR hRt, rerunStep_eq sp _ accC hR' hRt]
  simp only [Nat.add_sub_cancel]
  -- The change, the same in both.
  have hlenK := st_len sp al ts hok hst (j := K) (by omega)
  have hroot : sp.virt = true → ∀ n, (st sp al ts K).P.get? root = some n → ∀ e ∈ n.hist,
      ∃ z, e.val = sp.rootVal z := by
    intro hv n hn e he
    obtain ⟨z, -, -, hval⟩ := (hinvK.vr hv).rootEntry n hn e he
    exact ⟨z, hval⟩
  have hcE : sp.exec ts[K] (K + 1) (view sp accE.2 K) = (parts sp al (st sp al ts K) ts[K]).c := by
    rw [parts_c, hlenK, Nat.add_sub_cancel, hP.view K]
  have hcC : sp.exec ts[K] (K + 1) (view sp accC.2 K) = (parts sp al (st sp al ts K) ts[K]).c := by
    rw [exec_cutAgree hex hag hfK hls hinvK.ptrs hroot, parts_c, hlenK, Nat.add_sub_cancel]
  have hstep : StepOK sp (st sp al ts K).P (K + 1) (parts sp al (st sp al ts K) ts[K]).c := by
    rw [parts_c, hlenK, Nat.add_sub_cancel]
    exact hok.2 K hKt
  have hcopy : CopyStep sp (st sp al ts K).P (K + 1) (parts sp al (st sp al ts K) ts[K]).c := by
    rw [parts_c, hlenK, Nat.add_sub_cancel]; exact hev.2 K hKt
  have hm2 := rerun_apply_ok hok hph hj hk hKk hm hP (tr := ts[K]) (List.getElem?_eq_getElem hKt)
  rw [hcE] at hm2
  have hP1 : (st sp al ts (K + 1)).P = (st sp al ts K).P.apply (K + 1) (parts sp al (st sp al ts K) ts[K]).c := by
    rw [st_P_succ sp al ts hok hst hKt, parts_c, hlenK, Nat.add_sub_cancel]
  rw [hcC, hcE]
  generalize (parts sp al (st sp al ts K) ts[K]).c = ch at hstep hcopy hm2 hP1
  -- The paths and their order, the same in both.
  have hadds : sp.virt = true → ∀ a ∈ ch.adds, a.1 = root → ∃ z, a.2 = sp.rootVal z :=
    fun hv => (hstep.virt hv).root_adds
  have hag1 : CutAgree sp (lastFa (st sp al ts k).S) (K + 1) ((st sp al ts K).P.apply (K + 1) ch)
      (accC.2.apply (K + 1) ch) :=
    hag.apply hfK hls hinvK.ptrs hinvK.times hstep hvl hroot hadds
  have hp' : PtrsOK sp ((st sp al ts K).P.apply (K + 1) ch) := by rw [← hP1]; exact hinvK1.ptrs
  have hpathC : pathOf sp accC.2 ch (K + 1) = pathOf sp accE.2 ch (K + 1) := by
    rw [hag.pathOf_eq hag1 hls hinvK.ptrs hp' hfK, pathOf_congr hP]
  have hpr : ∀ p ∈ pathOf sp accE.2 ch (K + 1), reachable sp (st sp al ts K).P K p = true := by
    intro p hp
    have := (mem_pathOf hp).1
    rw [Nat.add_sub_cancel, hP.reachable] at this
    exact this
  have hpath : ∀ p ∈ pathOf sp accE.2 ch (K + 1), reachable sp (st sp al ts k).P K p = true := by
    intro p hp
    rw [hkK.reachable_eq hls (Nat.le_refl K)]
    exact hpr p hp
  have hsortC : (pathOf sp accE.2 ch (K + 1)).mergeSort (fun a b => decide (lev accC.2 b ≤ lev accC.2 a)) =
      (pathOf sp accE.2 ch (K + 1)).mergeSort (fun a b => decide (lev accE.2 b ≤ lev accE.2 a)) := by
    apply mergeSort_congr
    intro a ha b hb
    have ea : lev accE.2 a = lev (st sp al ts K).P a := by unfold lev; rw [hP a]
    have eb : lev accE.2 b = lev (st sp al ts K).P b := by unfold lev; rw [hP b]
    rw [hag.lev_eq hfK (Nat.le_refl _) (hpr a ha), hag.lev_eq hfK (Nat.le_refl _) (hpr b hb), ea, eb]
  have hwalkP : Mem.reachOnPath sp (cutStream c (st sp al ts k).S) accC.2 (K + 1) (pathOf sp accE.2 ch (K + 1)) =
      Mem.reachOnPath sp (cutStream c (st sp al ts k).S) accE.2 (K + 1) (pathOf sp accE.2 ch (K + 1)) := by
    funext m x
    apply reachOnPath1_congrP
    intro p hp
    rw [Nat.add_sub_cancel, hag.live_eq hfK (Nat.le_refl _) (hpr p hp), hP p]
  rw [hpathC, hsortC, hwalkP, hmC]
  -- The root's object of E.
  obtain ⟨-, o0, ho0, hc0, hn0⟩ := hm.root
  rw [hra, Option.some.injEq] at ho0
  subst ho0
  obtain ⟨-, ⟨nk, hnk, hhk, -, -⟩, -⟩ := hm.canon _ oe hra hc0
  rw [hn0] at hnk
  obtain ⟨nK, hnK⟩ := Option.isSome_iff_exists.mp hinvK.rootIn
  obtain ⟨nk', hnk', -, -, hup⟩ := hkK.grow root nK hnK
  rw [hnk, Option.some.injEq] at hnk'
  subst hnk'
  have hoeh : oe.hist = nK.hist := by rw [hhk, hup, upTo_of_forall _ _ (hinvK.times root nK hnK)]
  have hPr0 : ∀ n, accE.2.get? root = some n → ∀ x ∈ sp.live (n.hist.upTo K), x ∈ pointees sp oc.hist := by
    intro n hn x hx
    rw [hP root, hnK, Option.some.injEq] at hn
    subst hn
    rw [← hoeh, ← hrr.live K hfK] at hx
    exact mem_pointees_of_live hls hx
  have hcK : ∀ x v, reachable sp (st sp al ts k).P K x = true → (st sp al ts k).S.lv x = some v → c ≤ v.recNo :=
    fun x v hx hv => hcut.2.1 K v hfK (by omega) (ReadsPhys.latest x v hx hv)
  -- The walk.
  obtain ⟨oc1, oe1, hr1, hh1, hh1', hra1, hrt1, hw1⟩ := walk1_sim hok hj hmk hev hk hKk hsK hcs hcK hP hpath
    ((pathOf sp accE.2 ch (K + 1)).mergeSort (fun a b => decide (lev accE.2 b ≤ lev accE.2 a)))
    (fun x hx => (List.mergeSort_perm _ _).mem_iff.mp hx) accE.1 oc oe hr hm hra hrr hPr0
  rw [hw1]
  obtain ⟨hrW, hmW⟩ := RInv.reachPath hok hj hmk hev hk hKk hsK hP hpath
    ((pathOf sp accE.2 ch (K + 1)).mergeSort (fun a b => decide (lev accE.2 b ≤ lev accE.2 a))) accE.1 hr hm
  have hparent : ∀ x ∈ pathOf sp accE.2 ch (K + 1), x ≠ SIS.root →
      ∃ p ∈ pathOf sp accE.2 ch (K + 1), ∃ np nx, accE.2.get? p = some np ∧ accE.2.get? x = some nx ∧
        nx.level < np.level ∧ x ∈ sp.live (np.hist.upTo K) := by
    intro x hx hxr
    obtain ⟨p, np, nx, hrp, hnp, hnx, hlt, hxl⟩ := reach_parent (mem_pathOf hx).1 hxr
    refine ⟨p, pathOf_parent hx hrp hnp hxl hnx hlt, np, nx, hnp, hnx, hlt, ?_⟩
    simpa using hxl
  obtain ⟨-, -, hcan1⟩ := MemInv.reachPath_ok hctx hkK hP hpath hparent
    ((pathOf sp accE.2 ch (K + 1)).mergeSort (fun a b => decide (lev accE.2 b ≤ lev accE.2 a))) [] accE.1 hm
    (by simp) (fun x => by rw [List.nil_append]; exact (List.mergeSort_perm _ _).mem_iff)
    (by rw [List.nil_append]; exact pairwise_byLevelDesc _ _)
  generalize ((pathOf sp accE.2 ch (K + 1)).mergeSort (fun a b => decide (lev accE.2 b ≤ lev accE.2 a))).foldl
      (Mem.reachOnPath sp (st sp al ts k).S accE.2 (K + 1) (pathOf sp accE.2 ch (K + 1))) accE.1 = mw
    at hra1 hrt1 hrW hmW hcan1 hm2 ⊢
  -- The change.
  have hraW : mw.obj? mw.root = some oe1 := by rw [hrt1]; exact hra1
  have hrsW := RootSep.of_rerun hinvk hmW hrW
  have hnodeW : oe1.node = root := hrsW.rootNode oe1 hraW
  have hReach : ∀ x, reachable sp accC.2 (K + 1 - 1) x = reachable sp accE.2 (K + 1 - 1) x := by
    intro x; rw [Nat.add_sub_cancel, hag.reachable_eq hls hinvK.ptrs hfK (Nat.le_refl _) x, hP.reachable]
  have hPn : ∀ x, reachable sp accE.2 (K + 1 - 1) x = true →
      (accC.2.get? x).map (fun n => sp.live (n.hist.upTo (K + 1 - 1))) =
        (accE.2.get? x).map (fun n => sp.live (n.hist.upTo (K + 1 - 1))) := by
    intro x hx
    rw [Nat.add_sub_cancel] at hx ⊢
    rw [hP.reachable] at hx
    rw [hag.live_eq hfK (Nat.le_refl _) hx, hP x]
  have hPr1 : ∀ n, accE.2.get? root = some n → ∀ y ∈ sp.live (n.hist.upTo (K + 1 - 1)),
      y ∈ pointees sp oc1.hist := by
    intro n hn y hy; rw [Nat.add_sub_cancel] at hy; rw [hh1]; exact hPr0 n hn y hy
  have hradds : sp.virt = true → ∀ a ∈ ch.adds, a.1 = root → ∃ nn ∈ ch.new, a.2 = sp.rootVal nn.id := by
    intro hv a ha ha1
    have hmem : a ∈ ch.adds.filter (fun a => a.1 == root) := List.mem_filter.mpr ⟨ha, by simp [ha1]⟩
    rw [(hstep.virt hv).rootAdds] at hmem
    obtain ⟨nn, hnn, hnne⟩ := List.mem_map.mp hmem
    exact ⟨nn, (List.mem_filter.mp hnn).1, by rw [← hnne]⟩
  have hvalsE : sp.virt = true → ∀ e ∈ oe1.hist, ∃ z, e.val = sp.rootVal z := by
    intro hv e he; rw [hh1', hoeh] at he; exact hroot hv nK hnK e he
  have hoe1 : ∀ e ∈ oe1.hist, ∃ n, (st sp al ts k).P.get? root = some n ∧ e ∈ n.hist := by
    intro e he; rw [hh1', hhk] at he; exact ⟨nk, hnk, (mem_upTo.mp he).1⟩
  have hafter1 : ∀ e ∈ oe1.hist, lastSp (st sp al ts k).S < e.time → e ∈ oc1.hist := by
    intro e he h; rw [hh1]; rw [hh1'] at he; exact hafter e he h
  obtain ⟨oc2, oe2, hr2, ho2, hrt2, hn2, -, ⟨X, hX, hX'⟩, he2⟩ :=
    applyChange1_withRoot (P' := accC.2) (P := accE.2) (j := K + 1) (c := ch) hvl hReach hPn hPr1 hstep.distinct
      hradds (fun hv => (hinvk.vr hv).rootPtrs) hrsW hmW.nodup hmW.fresh hraW hr1 hnodeW hvalsE
      (fun a ha y hy hns => anySlot_sim hok hj hk hKk hP hstep.distinct hcopy hrW hmW
        (fun x hx => hcan1 x (by rw [pathOf_congr hP]; exact hx)) hraW hr1 hoe1 hafter1 ha hy hns)
  rw [he2]
  -- The nodes of gd(K + 1) have canonical objects already.
  have hraA : (mw.applyChange sp accE.2 (K + 1) ch).obj? (mw.applyChange sp accE.2 (K + 1) ch).root = some oe2 := by
    rw [hrt2]; exact ho2
  have hcov : ∀ x ∈ R.gd, (mw.applyChange sp accE.2 (K + 1) ch).canonicalOf x ≠ none :=
    fun x hx => hm2.coverGd (K + 1) R x (by omega) (Nat.le_refl _) hR hx
  rw [foldl_canonicalNode_noop sp _ _ R.gd hcov,
    foldl_canonicalNode_noop sp _ _ R.gd (fun x hx => by
      rw [withRoot_canonicalOf hraA hr2.canonical]; exact hcov x hx)]
  -- The root's new entries are the change's for it.
  have hXadds : X = addsFor ch (K + 1) root := by
    obtain ⟨-, o2, ho2', hc2, -⟩ := hm2.root
    rw [hraA, Option.some.injEq] at ho2'
    subst ho2'
    obtain ⟨-, ⟨nk2, hnk2, hhk2, -, -⟩, -⟩ := hm2.canon _ oe2 hraA hc2
    rw [hn2, hnk, Option.some.injEq] at hnk2
    subst hnk2
    have hn1 : (st sp al ts (K + 1)).P.get? root = some { nK with hist := nK.hist ++ addsFor ch (K + 1) root } := by
      rw [hP1, get?_apply_of_get? hnK]
    obtain ⟨n1', hn1', -, -, hup1⟩ := hkK1.grow root _ hn1
    rw [hnk, Option.some.injEq] at hn1'
    subst hn1'
    have h1 : oe2.hist = nK.hist ++ addsFor ch (K + 1) root := by
      rw [hhk2, hup1, upTo_of_forall _ _ (hinvK1.times root _ hn1)]
    rw [hX', hh1', hoeh] at h1
    exact List.append_cancel_left h1
  refine ⟨oc2, oe2, rfl, hraA, hr2, by rw [hP1]; exact hag1, ?_, ?_⟩
  · intro n hn
    obtain ⟨nC, hnC⟩ := Option.isSome_iff_exists.mp hag.rootP'
    rw [get?_apply_of_get? hnC, Option.some.injEq] at hn
    subst hn
    rw [hX, hh1, hoc nC hnC, hXadds]
  · intro e he h
    rw [hX', hh1'] at he
    rw [hX, hh1]
    rcases List.mem_append.mp he with h1 | h1
    · exact List.mem_append_left _ (hafter e h1 h)
    · exact List.mem_append_right _ h1

end Rerun1

/-! ## The startup's root objects, and the last steps -/

section Root

variable {sp : Spec V T}

/-- A cut at 0 is safe. -/
theorem CutOK.zero (sp : Spec V T) (db : DB V T) (k : Nat) : CutOK sp 0 db k :=
  ⟨Nat.zero_le _, fun _ _ _ _ _ => Nat.zero_le _, fun _ _ _ _ => ⟨Nat.zero_le _, fun _ _ _ h => absurd h (by omega)⟩,
    fun _ _ _ _ _ => Nat.zero_le _⟩

/-- The same change of slots, slot by slot, to both root objects. -/
theorem RootRel.mapSlots {f : Time} {oc oe : Obj V} (hr : RootRel sp f oc oe) (g : NodeId × Slot → NodeId × Slot)
    (hg : ∀ q, (g q).1 = q.1) :
    RootRel sp f { oc with slots := oc.slots.map g } { oe with slots := oe.slots.map g } := by
  have hs : ∀ (o : Obj V) y, ({ o with slots := o.slots.map g } : Obj V).slot? y =
      (o.slot? y).map (fun b => (g (y, b)).2) := fun o y => lookup_map_key g hg y o.slots
  refine ⟨fun hv => by rw [hr.nv hv], hr.node, hr.level, hr.isData, hr.canonical, hr.pos, hr.live, ?_, ?_,
    hr.vals, ?_⟩
  · intro y hy; rw [hs, hs, hr.slots y hy]
  · intro hv y hy; rw [hs, hr.noSlot hv y hy]; rfl
  · intro hv y hy; rw [hs, Option.isSome_map] at hy; exact hr.keysE hv y hy

/-- `linkCanonical` keeps the relation of the root objects. -/
theorem RootRel.link {f : Time} {oc oe : Obj V} (hr : RootRel sp f oc oe) (m : Mem V) :
    RootRel sp f (SIS.linkObj m oc) (SIS.linkObj m oe) := by
  unfold SIS.linkObj
  have hc : oc.canonical = oe.canonical := hr.canonical
  split <;> split
  · exact hr
  · rename_i h1 h2; rw [hc] at h1; exact absurd h1 h2
  · rename_i h1 h2; rw [hc] at h1; exact absurd h2 h1
  · exact hr.mapSlots _ (linkQ_fst m)

/-- Rule 4 keeps the relation of the root objects. -/
theorem RootRel.linkD {f : Time} {oc oe : Obj V} (hr : RootRel sp f oc oe) (m : Mem V) (D : Dirty) (h : Nat) :
    RootRel sp f (linkObjD m D h oc) (linkObjD m D h oe) := by
  unfold linkObjD
  have hcond : (oc.canonical && (inD D oc.node || h == m.root)) =
      (oe.canonical && (inD D oe.node || h == m.root)) := by rw [hr.canonical, hr.node]
  split <;> split
  · exact hr
  · rename_i h1 h2; rw [hcond] at h1; exact absurd h1 h2
  · rename_i h1 h2; rw [hcond] at h1; exact absurd h2 h1
  · exact hr.mapSlots _ (linkSlot_fst m)

theorem secObj_eq (S : Stream V T) (s : Nat) (o : Obj V) :
    secObj S s o = { o with pos := if o.canonical then
      (match newest S s o.node with | some w => some w.recNo | none => o.pos) else o.pos } := by
  obtain ⟨nd, lv, dt, hs, cn, ps, sl⟩ := o
  unfold secObj
  cases cn
  · rfl
  · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    cases newest S s nd <;> rfl

theorem RootRel.withPos {f : Time} {oc oe : Obj V} (hr : RootRel sp f oc oe) {p p' : Option Nat} (hp : p = p') :
    RootRel sp f { oc with pos := p } { oe with pos := p' } :=
  ⟨fun hv => by rw [hr.nv hv, hp], hr.node, hr.level, hr.isData, hr.canonical, hp, hr.live, hr.slots,
    hr.noSlot, hr.vals, hr.keysE⟩

/-- `sectionPos` keeps the relation of the root objects. -/
theorem RootRel.secPos {f : Time} {oc oe : Obj V} (hr : RootRel sp f oc oe) (S : Stream V T) (s : Nat) :
    RootRel sp f (secObj S s oc) (secObj S s oe) := by
  rw [secObj_eq, secObj_eq]
  exact hr.withPos (by rw [hr.canonical, hr.node, hr.pos])

theorem secObj_hist (S : Stream V T) (s : Nat) (o : Obj V) : (secObj S s o).hist = o.hist := by
  unfold secObj
  split
  · rfl
  · split <;> rfl

theorem linkObjD_hist (m : Mem V) (D : Dirty) (h : Nat) (o : Obj V) : (linkObjD m D h o).hist = o.hist := by
  unfold linkObjD
  split <;> rfl

theorem map_withRoot_self (l : List (Nat × Obj V)) (r : Nat) (o : Obj V) (h : ∀ p ∈ l, p.1 = r → p.2 = o) :
    l.map (fun p => if p.1 == r then (r, o) else p) = l := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    simp only [List.map_cons]
    rw [ih (fun q hq => h q (List.mem_cons_of_mem _ hq))]
    by_cases hp : p.1 = r
    · have h2 := h p List.mem_cons_self hp
      obtain ⟨a, b⟩ := p
      simp only at hp h2
      subst hp h2
      simp
    · have : (p.1 == r) = false := by simp [hp]
      simp [this]

/-- The memory with its own root object. -/
theorem withRoot_self {m : Mem V} {o : Obj V} (hnd : (m.objs.map (·.1)).Nodup) (hra : m.obj? m.root = some o) :
    m.withRoot o = m := by
  unfold Mem.withRoot
  rw [map_withRoot_self]
  intro p hp he
  have := obj?_of_mem_objs hnd hp
  rw [he, hra] at this
  exact (Option.some.inj this).symm

/-- The structure part of the rerun of the lazy startup: the logical rerun's. -/
theorem foldl_rerunStep_snd (sp : Spec V T) (S : Stream V T) :
    ∀ (L : List Nat) (acc : Mem V × Struct V), (L.foldl (rerunStep sp S) acc).2 =
      L.foldl (fun P j => match S[j]?.bind (·.trans) with
        | some tr => P.apply j (sp.exec tr j (view sp P (j - 1)))
        | none => P) acc.2 := by
  intro L
  induction L with
  | nil => intro acc; rfl
  | cons j L ih =>
    intro acc
    simp only [List.foldl_cons]
    rw [ih]
    congr 1
    unfold rerunStep
    cases h : S[j]? with
    | none => rfl
    | some R =>
      cases ht : R.trans with
      | none => simp [ht]
      | some tr => simp [ht]

/-- Without a virtual root, the root's step of the startup is the same from a
stream cut safely. -/
theorem lazyRoot_cut_nv {db : DB V T} {k c : Nat} (hv : sp.virt = false) (hcut : CutOK sp c db k)
    (hcs : c ≤ lastSp db.S) (m1 : Mem V) :
    lazyRoot sp (cutStream c db.S) m1 = lazyRoot sp db.S m1 := by
  unfold lazyRoot
  simp only [hv, Bool.false_eq_true, ↓reduceIte, lastSp_cut, topVersion_cut hcut hcs, canonOfVersion_cut hcs]

/-- The object that startup makes for a virtual root from root children ws. -/
def rootObjOf (sp : Spec V T) (S : Stream V T) (s : Nat) (ws : List (Version V)) : Obj V :=
  { canonOfVersion sp S s (rootVersion sp s ws) with hist := (rootVersion sp s ws).hist, pos := none }

theorem rootObjOf_slot? (sp : Spec V T) (S : Stream V T) (s : Nat) (ws : List (Version V)) (y : NodeId) :
    (rootObjOf sp S s ws).slot? y = if y ∈ pointees sp (rootVersion sp s ws).hist then
      some (Slot.stream (ruleRRef S s y ((rootVersion sp s ws).ref? y))) else none := by
  show (canonOfVersion sp S s (rootVersion sp s ws)).slot? y = _
  rw [canonOfVersion_slot?]
  have : cutHist (rootVersion sp s ws)
      (if isKeyLevel sp (rootVersion sp s ws).isData (rootVersion sp s ws).level then some s else none) =
      (rootVersion sp s ws).hist := by
    by_cases hk : isKeyLevel sp (rootVersion sp s ws).isData (rootVersion sp s ws).level = true
    · simp only [hk, ↓reduceIte, cutHist]
      exact upTo_of_forall _ _ (rootVersion_times sp s ws)
    · simp only [hk, Bool.false_eq_true, ↓reduceIte, cutHist]
  rw [this]

theorem lazyRoot_virt_obj (hv : sp.virt = true) (S : Stream V T) (m1 : Mem V) :
    (lazyRoot sp S m1).root = m1.next ∧
      (lazyRoot sp S m1).obj? m1.next = some (rootObjOf sp S (lastSp S) (topsRead sp S (lastSp S) true)) := by
  unfold lazyRoot
  simp only [hv, ↓reduceIte]
  refine ⟨rfl, ?_⟩
  show ((m1.addObj _).1.setTable root m1.next).obj? m1.next = _
  rw [Mem.obj?_setTable, Mem.obj?_addObj]
  simp only [↓reduceIte]
  rfl

/-- With a virtual root: the root's objects that startup makes from a stream cut
safely and from the whole stream. Both are canonical, with no record; the root
rebuilt from the cut stream has the entries of the other at the times of the
root children that the cut stream still has, which include the root's live
children from f on, and the same references to them, those children's latest
versions. -/
theorem rootObj_rel {db : DB V T} {k : Nat} (hinv : Inv sp db k) (hv : sp.virt = true) (hvl : VirtLiveOK sp)
    {c : Nat} (hcut : CutOK sp c db k) (hfs : lastFa db.S ≤ lastSp db.S) :
    RootRel sp (lastFa db.S) (rootObjOf sp db.S (lastSp db.S) (topsRead sp (cutStream c db.S) (lastSp db.S) true))
      (rootObjOf sp db.S (lastSp db.S) (topsRead sp db.S (lastSp db.S) true)) := by
  have hvi := hinv.vr hv
  have hcs : c ≤ lastSp db.S := Nat.le_trans hcut.1 hfs
  obtain ⟨n0, h0⟩ := Option.isSome_iff_exists.mp hinv.rootIn
  have hspec := hinv.topsRead_spec hv
  have hcutR := topsRead_cut hcut hcs
  have hE0 := hinv.cutRoot_hist hv (CutOK.zero sp db k) (Nat.zero_le _) h0
  have hC0 := hinv.cutRoot_hist hv hcut hcs h0
  have hlC := fun t (h1 : lastFa db.S ≤ t) (h2 : t ≤ lastSp db.S) => hinv.cutRoot_live hv hvl hcut hfs h0 h1 h2
  have hlE := fun t (h1 : lastFa db.S ≤ t) (h2 : t ≤ lastSp db.S) =>
    hinv.cutRoot_live hv hvl (CutOK.zero sp db k) hfs h0 h1 h2
  simp only [cutStream_zero] at hE0 hlE
  generalize lastSp db.S = s at hspec hcutR hE0 hC0 hlC hlE hfs hcs ⊢
  generalize topsRead sp (cutStream c db.S) s true = wsC at hcutR hC0 hlC ⊢
  generalize topsRead sp db.S s true = wsE at hspec hcutR hE0 hlE ⊢
  -- The root's entries of the cut stream's root are the whole stream's.
  have hsub : ∀ e ∈ (rootVersion sp s wsC).hist, e ∈ (rootVersion sp s wsE).hist := by
    intro e he
    rw [hC0, List.mem_filter] at he
    rw [hE0, List.mem_filter]
    refine ⟨he.1, ?_⟩
    obtain ⟨w', hw', hw't⟩ := List.any_eq_true.mp he.2
    obtain ⟨w, hw, hww⟩ := hcutR w' hw'
    rcases hww with rfl | rfl
    · exact List.any_eq_true.mpr ⟨w', hw, hw't⟩
    · simp [Version.stub] at hw't
  have hpsub : ∀ y, y ∈ pointees sp (rootVersion sp s wsC).hist → y ∈ pointees sp (rootVersion sp s wsE).hist := by
    intro y hy
    obtain ⟨e, he, hye⟩ := (mem_pointees sp _ _).mp hy
    exact (mem_pointees sp _ _).mpr ⟨e, hsub e he, hye⟩
  -- The same references to the root children.
  have href : ∀ y, y ∈ pointees sp (rootVersion sp s wsC).hist →
      (rootVersion sp s wsC).ref? y = (rootVersion sp s wsE).ref? y := by
    intro y hy
    obtain ⟨e, he, hye⟩ := (mem_pointees sp _ _).mp hy
    have he' := he
    rw [hC0, List.mem_filter] at he'
    obtain ⟨z, mz, hzt, hez⟩ := hvi.rootEntry n0 h0 e (mem_upTo.mp he'.1).1
    have hyz : y = z := by rw [hez, hvi.rootPtrs z] at hye; simpa using hye
    subst hyz
    obtain ⟨w', hw', hw't⟩ := List.any_eq_true.mp he'.2
    obtain ⟨w, hw, hww⟩ := hcutR w' hw'
    rcases hww with rfl | rfl
    · obtain ⟨m', c', htop', -, hlv⟩ := hspec.1 w' hw
      have hwh := hvi.topVers w'.node m' c' htop' w'.recNo w' (hinv.lv_at hlv)
      obtain ⟨e', he'', he't⟩ := List.any_eq_true.mp hw't
      rw [hwh] at he''
      have hc' : c' = e.time := by rw [← htop'.time_of_mem he'']; simpa using he't
      rw [hc'] at htop'
      have hwy : w'.node = y := hinv.topAt_unique hv htop' hzt
      rw [hwy] at hlv
      have hallE : ∀ w2 ∈ wsE, w2.node = y → w2.recNo = w'.recNo := by
        intro w2 hw2 hw2y
        obtain ⟨-, -, -, -, hlv2⟩ := hspec.1 w2 hw2
        rw [hw2y, hlv, Option.some.injEq] at hlv2
        rw [hlv2]
      have hallC : ∀ w2 ∈ wsC, w2.node = y → w2.recNo = w'.recNo := by
        intro w2 hw2 hw2y
        obtain ⟨w3, hw3, hw23⟩ := hcutR w2 hw2
        have h3 : w3.node = y ∧ w2.recNo = w3.recNo := by
          rcases hw23 with rfl | rfl
          · exact ⟨hw2y, rfl⟩
          · exact ⟨hw2y, rfl⟩
        rw [h3.2]
        exact hallE w3 hw3 h3.1
      show List.lookup y (wsC.map (fun w => (w.node, w.recNo))) = List.lookup y (wsE.map (fun w => (w.node, w.recNo)))
      rw [lookup_refs_rec ⟨w', hw', hwy⟩ hallC, lookup_refs_rec ⟨w', hw, hwy⟩ hallE]
    · simp [Version.stub] at hw't
  refine ⟨fun h => absurd (hv.symm.trans h) (by simp), rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · -- The live children from f on.
    intro t ht
    show sp.live ((rootVersion sp s wsC).hist.upTo t) = sp.live ((rootVersion sp s wsE).hist.upTo t)
    by_cases hts : t ≤ s
    · rw [hlC t ht hts, hlE t ht hts]
    · have e1 : (rootVersion sp s wsC).hist.upTo t = (rootVersion sp s wsC).hist.upTo s := by
        rw [upTo_of_forall _ t (fun e he => by have := rootVersion_times sp s wsC e he; omega),
          upTo_of_forall _ s (rootVersion_times sp s wsC)]
      have e2 : (rootVersion sp s wsE).hist.upTo t = (rootVersion sp s wsE).hist.upTo s := by
        rw [upTo_of_forall _ t (fun e he => by have := rootVersion_times sp s wsE e he; omega),
          upTo_of_forall _ s (rootVersion_times sp s wsE)]
      rw [e1, e2, hlC s hfs (Nat.le_refl _), hlE s hfs (Nat.le_refl _)]
  · intro y hy
    rw [rootObjOf_slot?, rootObjOf_slot?]
    have hy' : y ∈ pointees sp (rootVersion sp s wsC).hist := hy
    simp only [hy', hpsub y hy', ↓reduceIte, href y hy']
  · intro _ y hy
    rw [rootObjOf_slot?]
    have hy' : y ∉ pointees sp (rootVersion sp s wsC).hist := hy
    simp only [hy', ↓reduceIte]
  · intro _ e he
    exact rootVersion_vals sp s wsC e he
  · intro _ y hy
    rw [rootObjOf_slot?] at hy
    show y ∈ pointees sp (rootVersion sp s wsE).hist
    by_cases h : y ∈ pointees sp (rootVersion sp s wsE).hist
    · exact h
    · simp only [h, ↓reduceIte] at hy; cases hy

end Root

section Start

variable {sp : Spec V T} {al : Algo V T} {ts : List T}

/-- The rerun from the memory before it with the other root object, the cut
stream, and the logical startup's structure from it: the rerun from the whole
stream, with the other root object, which holds the root's history of the
logical rerun from the cut stream. -/
theorem rerun_sim (hok : RunOK sp al ts) (hph : PhysRunOK sp al ts) (hj : al.stillDirty = javaTest sp)
    (hmk : al.mark = true) (hev : EvictRunOK sp al ts) (hex : ExecRootOK sp) (hvl : VirtLiveOK sp)
    {k c : Nat} (hk : k ≤ ts.length) (hcut : CutOK sp c (st sp al ts k) k)
    {m0 : Mem V} {oc0 oe0 : Obj V}
    (hr0 : RInv sp (st sp al ts k).S m0) (hm0 : MemInv sp (st sp al ts k) (lastSp (st sp al ts k).S) m0)
    (hra0 : m0.obj? m0.root = some oe0) (hrr0 : RootRel sp (lastFa (st sp al ts k).S) oc0 oe0)
    (hoc0 : ∀ n, (baseStruct sp (cutStream c (st sp al ts k).S) (lastSp (st sp al ts k).S) true).get? root =
      some n → oc0.hist = n.hist)
    (hafter0 : ∀ e ∈ oe0.hist, lastSp (st sp al ts k).S < e.time → e ∈ oc0.hist) :
    ∃ oc oe,
      ((sectionIdx (cutStream c (st sp al ts k).S) (lastSp (st sp al ts k).S)).foldl
          (rerunStep sp (cutStream c (st sp al ts k).S))
          (m0.withRoot oc0, baseStruct sp (cutStream c (st sp al ts k).S) (lastSp (st sp al ts k).S) true)).1 =
        ((sectionIdx (st sp al ts k).S (lastSp (st sp al ts k).S)).foldl (rerunStep sp (st sp al ts k).S)
          (m0, baseStruct sp (st sp al ts k).S (lastSp (st sp al ts k).S) true)).1.withRoot oc ∧
      ((sectionIdx (st sp al ts k).S (lastSp (st sp al ts k).S)).foldl (rerunStep sp (st sp al ts k).S)
          (m0, baseStruct sp (st sp al ts k).S (lastSp (st sp al ts k).S) true)).1.obj?
        ((sectionIdx (st sp al ts k).S (lastSp (st sp al ts k).S)).foldl (rerunStep sp (st sp al ts k).S)
          (m0, baseStruct sp (st sp al ts k).S (lastSp (st sp al ts k).S) true)).1.root = some oe ∧
      RootRel sp (lastFa (st sp al ts k).S) oc oe ∧
      ∀ n, ((sectionIdx (cutStream c (st sp al ts k).S) (lastSp (st sp al ts k).S)).foldl
          (rerunStep sp (cutStream c (st sp al ts k).S))
          (m0.withRoot oc0, baseStruct sp (cutStream c (st sp al ts k).S) (lastSp (st sp al ts k).S) true)).2.get?
          root = some n → oc.hist = n.hist := by
  have hst : AlgOK sp al := algOK_of sp al (Or.inl hj)
  have hinv := inv_st sp al ts hok hst k hk
  have hsk : lastSp (st sp al ts k).S ≤ k := by have := hinv.spLt; omega
  have hP0 := base_sameNodes sp al ts hok hst hk
  have hag0 := base_cutAgree sp al ts hok hst hk hvl hcut
  generalize hs : lastSp (st sp al ts k).S = s at hm0 hP0 hsk hag0 hoc0 hafter0 ⊢
  have hidx : sectionIdx (st sp al ts k).S s = List.range' (s + 1) (k - s) := by
    simp [sectionIdx, hinv.len]
  have hidx' : sectionIdx (cutStream c (st sp al ts k).S) s = List.range' (s + 1) (k - s) := by
    simp [sectionIdx, cutStream_length, hinv.len]
  rw [hidx, hidx']
  have key : ∀ n, n ≤ k - s → ∃ oc oe,
      ((List.range' (s + 1) n).foldl (rerunStep sp (cutStream c (st sp al ts k).S))
          (m0.withRoot oc0, baseStruct sp (cutStream c (st sp al ts k).S) s true)).1 =
        ((List.range' (s + 1) n).foldl (rerunStep sp (st sp al ts k).S)
          (m0, baseStruct sp (st sp al ts k).S s true)).1.withRoot oc ∧
      ((List.range' (s + 1) n).foldl (rerunStep sp (st sp al ts k).S) (m0, baseStruct sp (st sp al ts k).S s true)).1.obj?
        ((List.range' (s + 1) n).foldl (rerunStep sp (st sp al ts k).S)
          (m0, baseStruct sp (st sp al ts k).S s true)).1.root = some oe ∧
      RootRel sp (lastFa (st sp al ts k).S) oc oe ∧
      CutAgree sp (lastFa (st sp al ts k).S) (s + n) (st sp al ts (s + n)).P
        ((List.range' (s + 1) n).foldl (rerunStep sp (cutStream c (st sp al ts k).S))
          (m0.withRoot oc0, baseStruct sp (cutStream c (st sp al ts k).S) s true)).2 ∧
      (∀ nd, ((List.range' (s + 1) n).foldl (rerunStep sp (cutStream c (st sp al ts k).S))
          (m0.withRoot oc0, baseStruct sp (cutStream c (st sp al ts k).S) s true)).2.get? root = some nd →
        oc.hist = nd.hist) ∧
      (∀ e ∈ oe.hist, s < e.time → e ∈ oc.hist) ∧
      RInv sp (st sp al ts k).S ((List.range' (s + 1) n).foldl (rerunStep sp (st sp al ts k).S)
          (m0, baseStruct sp (st sp al ts k).S s true)).1 ∧
      MemInv sp (st sp al ts k) (s + n) ((List.range' (s + 1) n).foldl (rerunStep sp (st sp al ts k).S)
          (m0, baseStruct sp (st sp al ts k).S s true)).1 ∧
      SameNodes ((List.range' (s + 1) n).foldl (rerunStep sp (st sp al ts k).S)
          (m0, baseStruct sp (st sp al ts k).S s true)).2 (st sp al ts (s + n)).P := by
    intro n
    induction n with
    | zero => intro _; exact ⟨oc0, oe0, rfl, hra0, hrr0, hag0, hoc0, hafter0, hr0, hm0, hP0⟩
    | succ n ih =>
      intro hn
      obtain ⟨oc, oe, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := ih (by omega)
      rw [List.range'_concat, List.foldl_append, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil, Nat.one_mul]
      rw [show s + 1 + n = s + n + 1 by omega, show s + (n + 1) = s + n + 1 by omega]
      have hsK : lastSp (st sp al ts k).S ≤ s + n := by rw [hs]; omega
      obtain ⟨oc', oe', g1, g2, g3, g4, g5, g6⟩ := rerunStep_sim hok hph hj hmk hev hex hvl hk hsK (by omega) hcut
        h7 h8 h9 h4 h1 h2 h3 h5 (by rw [hs]; exact h6)
      have hE := rerunStep_ok hok hph hj hk (K := s + n) hsK (by omega) h8 h9
      have hR := RInv.rerunStep hok hph hj hmk hev hk (K := s + n) hsK (by omega) h7 h8 h9
      rw [hs] at g6
      exact ⟨oc', oe', g1, g2, g3, g4, g5, g6, hR, hE.1, hE.2⟩
  obtain ⟨oc, oe, h1, h2, h3, -, h5, -⟩ := key (k - s) (Nat.le_refl _)
  exact ⟨oc, oe, h1, h2, h3, h5⟩

/-- The startup from a stream cut safely: the memory of the startup from the
whole stream but for the root's object, which holds the root's history of the
logical startup from the cut stream. -/
theorem startup_sim (hok : RunOK sp al ts) (hph : PhysRunOK sp al ts) (hev : EvictRunOK sp al ts)
    (hj : al.stillDirty = javaTest sp) (hmk : al.mark = true) (hex : ExecRootOK sp) (hvl : VirtLiveOK sp)
    {k c : Nat} (hk : k ≤ ts.length) (hcut : CutOK sp c (st sp al ts k) k) :
    ∃ oc oe, SimC sp (lastFa (st sp al ts k).S) (evictStartup sp (cutStream c (st sp al ts k).S))
        (evictStartup sp (st sp al ts k).S) oc oe ∧
      ∀ n, (startup sp (cutStream c (st sp al ts k).S)).P.get? root = some n → oc.hist = n.hist := by
  have hst : AlgOK sp al := algOK_of sp al (Or.inl hj)
  have hinv := inv_st sp al ts hok hst k hk
  have hctx := pctx_st hok hst hk
  have hfs := st_fa_le sp al ts hk
  have hcs : c ≤ lastSp (st sp al ts k).S := Nat.le_trans hcut.1 hfs
  have hsk : lastSp (st sp al ts k).S ≤ k := by have := hinv.spLt; omega
  have hkS := kctx_st sp al ts hok hj hsk hk
  have hm0 := hctx.base_ok hkS
  have hr0 := rinv_lazyBase hok hj hmk hev hk
  have hinvs := inv_st sp al ts hok hst _ (Nat.le_trans hsk hk)
  -- The memory before the rerun.
  obtain ⟨-, oe0, hra0, hc0, hn0⟩ := hm0.root
  have hbase : ∃ oc0, lazyBase sp (cutStream c (st sp al ts k).S) = (lazyBase sp (st sp al ts k).S).withRoot oc0 ∧
      RootRel sp (lastFa (st sp al ts k).S) oc0 oe0 ∧
      (∀ n, (baseStruct sp (cutStream c (st sp al ts k).S) (lastSp (st sp al ts k).S) true).get? root = some n →
        oc0.hist = n.hist) ∧
      (∀ e ∈ oe0.hist, lastSp (st sp al ts k).S < e.time → e ∈ oc0.hist) := by
    cases hv : sp.virt with
    | false =>
      refine ⟨oe0, ?_, RootRel.ofNV hv _ oe0, ?_, fun e he _ => he⟩
      · unfold lazyBase
        rw [lazySec_cut hcs, lazyRoot_cut_nv hv hcut hcs]
        exact (withRoot_self hm0.nodup hra0).symm
      · intro n hn
        rw [(base_cutAgree sp al ts hok hst hk hvl hcut).root_eq hv hfs] at hn
        obtain ⟨-, ⟨nk, hnk, hhk, -, -⟩, -⟩ := hm0.canon _ oe0 hra0 hc0
        rw [hn0] at hnk
        obtain ⟨nk', hnk', -, -, hup⟩ := hkS.grow root n hn
        rw [hnk, Option.some.injEq] at hnk'
        subst hnk'
        rw [hhk, hup, upTo_of_forall _ _ (hinvs.times root n hn)]
    | true =>
      obtain ⟨hrt1, hro1⟩ := lazyRoot_virt_obj hv (st sp al ts k).S (lazySec sp (st sp al ts k).S)
      have hra1 : (lazyRoot sp (st sp al ts k).S (lazySec sp (st sp al ts k).S)).obj?
          (lazyRoot sp (st sp al ts k).S (lazySec sp (st sp al ts k).S)).root =
          some (rootObjOf sp (st sp al ts k).S (lastSp (st sp al ts k).S)
            (topsRead sp (st sp al ts k).S (lastSp (st sp al ts k).S) true)) := by rw [hrt1]; exact hro1
      have hoe0 : oe0 = SIS.linkObj (lazyRoot sp (st sp al ts k).S (lazySec sp (st sp al ts k).S))
          (rootObjOf sp (st sp al ts k).S (lastSp (st sp al ts k).S)
            (topsRead sp (st sp al ts k).S (lastSp (st sp al ts k).S) true)) := by
        unfold lazyBase at hra0
        rw [linkCanonical_obj?] at hra0
        have : (lazyRoot sp (st sp al ts k).S (lazySec sp (st sp al ts k).S)).linkCanonical.root =
            (lazyRoot sp (st sp al ts k).S (lazySec sp (st sp al ts k).S)).root := rfl
        rw [this, hra1] at hra0
        exact (Option.some.inj hra0).symm
      have hrel := rootObj_rel hinv hv hvl hcut hfs
      refine ⟨SIS.linkObj (lazyRoot sp (st sp al ts k).S (lazySec sp (st sp al ts k).S))
        (rootObjOf sp (st sp al ts k).S (lastSp (st sp al ts k).S)
          (topsRead sp (cutStream c (st sp al ts k).S) (lastSp (st sp al ts k).S) true)), ?_, ?_, ?_, ?_⟩
      · unfold lazyBase
        rw [lazySec_cut hcs, lazyRoot_cut_virt hv hcs _ (lazySec_fresh sp _)]
        exact linkCanonical_withRoot hra1 rfl rfl
      · rw [hoe0]; exact hrel.link _
      · intro n hn
        rw [hinv.baseCut_root hv hcs, Option.some.injEq] at hn
        subst hn
        rw [(linkObj_fields _ _).2.2.2.1]
        show (rootVersion sp (lastSp (st sp al ts k).S)
            (topsRead sp (cutStream c (st sp al ts k).S) (lastSp (st sp al ts k).S) true)).hist =
          History.upTo (rootVersion sp (lastSp (st sp al ts k).S)
            (topsRead sp (cutStream c (st sp al ts k).S) (lastSp (st sp al ts k).S) true)).hist
            (lastSp (st sp al ts k).S)
        rw [upTo_of_forall _ _ (rootVersion_times sp _ _)]
      · intro e he h
        rw [hoe0, (linkObj_fields _ _).2.2.2.1] at he
        have := rootVersion_times sp _ _ e he
        omega
  obtain ⟨oc0, hb, hrr0, hoc0, hafter0⟩ := hbase
  -- The rerun.
  obtain ⟨oc, oe, h1, h2, h3, h4⟩ := rerun_sim hok hph hj hmk hev hex hvl hk hcut hr0 hm0 hra0 hrr0 hoc0 hafter0
  have hlazy : lazyStartup sp (cutStream c (st sp al ts k).S) =
      (lazyStartup sp (st sp al ts k).S).withRoot oc := by
    rw [lazyStartup_eq, lazyStartup_eq, lastSp_cut, hb]
    exact h1
  have hraL : (lazyStartup sp (st sp al ts k).S).obj? (lazyStartup sp (st sp al ts k).S).root = some oe := by
    rw [lazyStartup_eq]; exact h2
  have hPC : (startup sp (cutStream c (st sp al ts k).S)).P =
      ((sectionIdx (cutStream c (st sp al ts k).S) (lastSp (st sp al ts k).S)).foldl
        (rerunStep sp (cutStream c (st sp al ts k).S))
        ((lazyBase sp (st sp al ts k).S).withRoot oc0,
          baseStruct sp (cutStream c (st sp al ts k).S) (lastSp (st sp al ts k).S) true)).2 := by
    rw [foldl_rerunStep_snd]
    show rerun sp (cutStream c (st sp al ts k).S) (lastSp (cutStream c (st sp al ts k).S))
      (baseStruct sp (cutStream c (st sp al ts k).S) (lastSp (cutStream c (st sp al ts k).S)) true) = _
    rw [lastSp_cut]
    rfl
  -- The positions and rule 4.
  have hmL := lazy_ok hok hph hj hk
  have hsL : (lazyStartup sp (st sp al ts k).S).s = lastSp (st sp al ts k).S := hmL.sEq
  have hD : (startup sp (cutStream c (st sp al ts k).S)).D = (startup sp (st sp al ts k).S).D := by
    rw [startup, startup, startup_D, startup_D, sectionD_cut hcs]
  have hraP : ((lazyStartup sp (st sp al ts k).S).sectionPos (st sp al ts k).S).obj?
      ((lazyStartup sp (st sp al ts k).S).sectionPos (st sp al ts k).S).root =
      some (secObj (st sp al ts k).S (lazyStartup sp (st sp al ts k).S).s oe) := by
    show ((lazyStartup sp (st sp al ts k).S).sectionPos (st sp al ts k).S).obj? (lazyStartup sp (st sp al ts k).S).root = _
    rw [Mem.sectionPos_obj?, hraL]
    rfl
  have hrr := h3.secPos (st sp al ts k).S (lazyStartup sp (st sp al ts k).S).s
  have hev' : evictStartup sp (cutStream c (st sp al ts k).S) =
      (evictStartup sp (st sp al ts k).S).withRoot
        (linkObjD ((lazyStartup sp (st sp al ts k).S).sectionPos (st sp al ts k).S) (startup sp (st sp al ts k).S).D
          ((lazyStartup sp (st sp al ts k).S).sectionPos (st sp al ts k).S).root
          (secObj (st sp al ts k).S (lazyStartup sp (st sp al ts k).S).s oc)) := by
    unfold evictStartup
    rw [hlazy, sectionPos_withRoot (S := (st sp al ts k).S) (fun y => by rw [hsL]; exact newest_cut hcs y), hD,
      linkD_withRoot hraP hrr.canonical]
  have hraF : (evictStartup sp (st sp al ts k).S).obj? (evictStartup sp (st sp al ts k).S).root =
      some (linkObjD ((lazyStartup sp (st sp al ts k).S).sectionPos (st sp al ts k).S) (startup sp (st sp al ts k).S).D
        ((lazyStartup sp (st sp al ts k).S).sectionPos (st sp al ts k).S).root
        (secObj (st sp al ts k).S (lazyStartup sp (st sp al ts k).S).s oe)) := by
    show (((lazyStartup sp (st sp al ts k).S).sectionPos (st sp al ts k).S).linkD (startup sp (st sp al ts k).S).D).obj?
      ((lazyStartup sp (st sp al ts k).S).sectionPos (st sp al ts k).S).root = _
    rw [Mem.linkD_obj?, hraP]
    rfl
  have hE := einv_startup hok hph hj hmk hev hk
  refine ⟨_, _, ⟨?_, fun _ => hev', hraF, hrr.linkD _ _ _⟩, ?_⟩
  · rw [hev']
    exact RootPerm.refl_withRoot hE.objNodup hE.fresh hraF
  · intro n hn
    rw [linkObjD_hist, secObj_hist]
    rw [hPC] at hn
    exact h4 n hn

end Start

end SIS
