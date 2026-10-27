/-
Proofs about reclaim with handles (bergdb 005-62), part 3 of T12 over handles:
the operations on a memory with handles with another root object
(`HMem.withRoot`). Following a pointer of another object than the root's
changes the root's object in neither memory; following one of the root's, for a
pointee that both root objects have the same pointer for, sets it the same in
both. CutLaterSim.lean does this for Evict.lean's memory.
-/
import SIS.Proof.HandleCutStart

set_option linter.unusedSectionVars false

namespace SIS

variable {V T : Type} [DecidableEq V]

/-! ## The elementary operations -/

section Elem

variable {m : HMem V} {oc : HObj V}

theorem filter_map_rootH (l : List (Nat × HObj V)) (r a : Nat) (oc : HObj V) :
    (l.map (fun p => if p.1 == r then (r, oc) else p)).filter (fun p => p.1 != a) =
      (l.filter (fun p => p.1 != a)).map (fun p => if p.1 == r then (r, oc) else p) := by
  rw [List.filter_map]
  congr 1
  apply List.filter_congr
  intro p _
  simp only [Function.comp]
  by_cases hp : p.1 = r
  · subst hp; simp
  · simp [hp]

theorem HMem.withRoot_setObj_ne {a : Nat} (hne : a ≠ m.root) (o : HObj V) :
    (m.withRoot oc).setObj a o = (m.setObj a o).withRoot oc := by
  unfold HMem.withRoot HMem.setObj
  simp only [List.map_cons, filter_map_rootH]
  have : (a == m.root) = false := by simp [hne]
  simp [this]

theorem HMem.withRoot_setObj_root (o o' : HObj V) :
    (m.withRoot oc).setObj m.root o = (m.setObj m.root o').withRoot o := by
  unfold HMem.withRoot HMem.setObj
  simp only [List.map_cons, filter_map_rootH, beq_self_eq_true, ↓reduceIte]
  congr 2
  apply List.map_congr_left
  intro p hp
  have hne : p.1 ≠ m.root := by
    have := (List.mem_filter.mp hp).2
    simpa using this
  simp [hne]

theorem HMem.withRoot_dropObj (a : Nat) :
    (m.withRoot oc).dropObj a = (m.dropObj a).withRoot oc := by
  unfold HMem.withRoot HMem.dropObj
  simp only [filter_map_rootH]

theorem HMem.withRoot_setHandle (n : Nat) (hd : Handle) :
    (m.withRoot oc).setHandle n hd = (m.setHandle n hd).withRoot oc := rfl

theorem HMem.withRoot_setTable (y : NodeId) (n : Nat) :
    (m.withRoot oc).setTable y n = (m.setTable y n).withRoot oc := rfl

theorem HMem.withRoot_handle? (n : Nat) : (m.withRoot oc).handle? n = m.handle? n := rfl

theorem HMem.withRoot_tableOf (y : NodeId) : (m.withRoot oc).tableOf y = m.tableOf y := rfl

theorem HMem.withRoot_objOf (n : Nat) : (m.withRoot oc).objOf n = m.objOf n := rfl

theorem HMem.withRoot_nextH (n : Nat) :
    ({ m.withRoot oc with nextHandle := n } : HMem V) = ({ m with nextHandle := n } : HMem V).withRoot oc := rfl

theorem HMem.withRoot_withRoot (oc oc' : HObj V) : (m.withRoot oc).withRoot oc' = m.withRoot oc' := by
  unfold HMem.withRoot
  simp only [List.map_map]
  congr 1
  apply List.map_congr_left
  intro p _
  by_cases hp : p.1 = m.root
  · simp [Function.comp, hp]
  · simp [Function.comp, hp]

theorem HMem.withRoot_emptyHandle (y : NodeId) : (m.withRoot oc).emptyHandle y = (m.emptyHandle y).withRoot oc :=
  rfl

/-- A new object at an address that is not the root's, then a handle set: the
same with another root object. -/
theorem HMem.withRoot_install (M : HMem V) (b : Nat) (hb : b ≠ M.root) (x : HObj V) (n : Nat) (hd : Handle) :
    ({ M.withRoot oc with objs := (b, x) :: (M.withRoot oc).objs, nextObj := b + 1 } : HMem V).setHandle n hd =
      (({ M with objs := (b, x) :: M.objs, nextObj := b + 1 } : HMem V).setHandle n hd).withRoot oc := by
  unfold HMem.setHandle HMem.withRoot
  have hbr : (b == M.root) = false := by simp [hb]
  simp only [List.map_cons, hbr, Bool.false_eq_true, ↓reduceIte]

/-- The load, on a handle that holds no root object, with the next address not
the root's: the same, and the root's object stays. -/
theorem HMem.withRoot_load (sp : Spec V T) (S : Stream V T) (n : Nat) (r : Option Nat)
    (hn : ∀ hd b, m.handle? n = some hd → hd.obj = some b → b ≠ m.root) (hnext : m.nextObj ≠ m.root) :
    (m.withRoot oc).load sp S n r = ((m.load sp S n r).1.withRoot oc, (m.load sp S n r).2) := by
  unfold HMem.load
  simp only [HMem.withRoot_handle?]
  cases hh : m.handle? n with
  | none => rfl
  | some hd =>
    simp only
    cases hb : hd.obj with
    | none =>
      simp only
      cases r with
      | none => rfl
      | some q =>
        simp only
        cases hw : S.versionAt q hd.node with
        | none => rfl
        | some w =>
          simp only [HMem.withRoot_nextObj]
          exact congrArg (fun z => (z, some m.nextObj)) (HMem.withRoot_install m m.nextObj hnext _ n _)
    | some b =>
      have hbr := hn hd b hh hb
      simp only [HMem.withRoot_obj?_ne hbr]
      cases hob : m.obj? b with
      | none =>
        simp only
        cases r with
        | none => rfl
        | some q =>
          simp only
          cases hw : S.versionAt q hd.node with
          | none => rfl
          | some w =>
            simp only [HMem.withRoot_nextObj, HMem.withRoot_dropObj]
            exact congrArg (fun z => (z, some m.nextObj))
              (HMem.withRoot_install (m.dropObj b) m.nextObj hnext _ n _)
      | some ob =>
        simp only
        cases hu : ob.usable r with
        | true => simp
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          cases r with
          | none => rfl
          | some q =>
            simp only
            cases hw : S.versionAt q hd.node with
            | none => rfl
            | some w =>
              simp only [HMem.withRoot_nextObj, HMem.withRoot_dropObj]
              exact congrArg (fun z => (z, some m.nextObj))
                (HMem.withRoot_install (m.dropObj b) m.nextObj hnext _ n _)

/-- The load leaves every object but the handle's old one and the new one. -/
theorem HMem.load_obj?_ne (sp : Spec V T) (S : Stream V T) (n : Nat) (r : Option Nat) {x : Nat}
    (hn : ∀ hd, m.handle? n = some hd → hd.obj ≠ some x) (hnext : m.nextObj ≠ x) :
    (m.load sp S n r).1.obj? x = m.obj? x := by
  unfold HMem.load
  cases hh : m.handle? n with
  | none => rfl
  | some hd =>
    have hx := hn hd hh
    simp only
    cases hb : hd.obj with
    | none =>
      simp only
      cases r with
      | none => rfl
      | some q =>
        simp only
        cases hw : S.versionAt q hd.node with
        | none => rfl
        | some w =>
          simp only
          unfold HMem.setHandle HMem.obj?
          simp only [List.lookup_cons]
          have : (x == m.nextObj) = false := by simp [Ne.symm hnext]
          simp [this]
    | some b =>
      have hbx : b ≠ x := fun he => hx (by rw [hb, he])
      simp only
      cases hob : m.obj? b with
      | none =>
        simp only
        cases r with
        | none => rfl
        | some q =>
          simp only
          cases hw : S.versionAt q hd.node with
          | none => rfl
          | some w =>
            simp only
            unfold HMem.setHandle HMem.obj? HMem.dropObj
            simp only [List.lookup_cons]
            have : (x == m.nextObj) = false := by simp [Ne.symm hnext]
            simp only [this]
            exact lookup_filter_ne b x m.objs (Ne.symm hbx)
      | some ob =>
        simp only
        cases hu : ob.usable r with
        | true => simp
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          cases r with
          | none => rfl
          | some q =>
            simp only
            cases hw : S.versionAt q hd.node with
            | none => rfl
            | some w =>
              simp only
              unfold HMem.setHandle HMem.obj? HMem.dropObj
              simp only [List.lookup_cons]
              have : (x == m.nextObj) = false := by simp [Ne.symm hnext]
              simp only [this]
              exact lookup_filter_ne b x m.objs (Ne.symm hbx)

end Elem

/-! ## The two root objects under the operations -/

section RootRel

variable {sp : Spec V T} {f : Time}

/-- Setting the pointer for a pointee of oc's history the same in both, where both
had the same pointer for it. -/
theorem RootRelH.setPtr {oc oe : HObj V} (hr : RootRelH sp f oc oe) {y : NodeId}
    (hy : y ∈ pointees sp oc.hist) (p : HPtr) : RootRelH sp f (oc.setPtr y p) (oe.setPtr y p) := by
  have hsame := hr.ptrs y hy
  refine ⟨fun hv => by rw [hr.nv hv], hr.node, hr.level, hr.isData, hr.canonical, hr.pos, hr.live,
    fun y' hy' => ?_, fun hv y' hy' => ?_, hr.vals, fun hv y' hy' => ?_⟩
  · rw [HObj.ptr?_setPtr, HObj.ptr?_setPtr, hsame]
    split
    · rfl
    · exact hr.ptrs y' hy'
  · have hne : y' ≠ y := fun he => hy' (by rw [he]; exact hy)
    rw [HObj.ptr?_setPtr]
    simp only [hne, ↓reduceIte]
    exact hr.noPtr hv y' hy'
  · rw [HObj.ptr?_setPtr] at hy'
    show y' ∈ pointees sp oe.hist
    split at hy'
    · rename_i he
      subst he
      apply hr.keysE hv y'
      cases hq : oe.ptr? y' with
      | none => rw [hq] at hy'; cases hy'
      | some _ => rfl
    · exact hr.keysE hv y' hy'

end RootRel

/-! ## The follow on a memory with another root object -/

section Follow

variable {sp : Spec V T} {f : Time} {db : DB V T} {S0 : Stream V T} {k : Nat} {m : HMem V}

/-- Setting the object at address a, which is the root's object or another: with
another root object, the same, and the two root objects still related. -/
theorem HMem.withRoot_setObj_rel {oc oe : HObj V} (hra : m.obj? m.root = some oe) (hr : RootRelH sp f oc oe)
    {a : Nat} {o o' : HObj V} (ho : m.obj? a = some o) (ho' : (m.withRoot oc).obj? a = some o') {y : NodeId}
    (hroot : a = m.root → y ∈ pointees sp oc.hist) (p : HPtr) :
    ∃ oc' oe', (m.withRoot oc).setObj a (o'.setPtr y p) = (m.setObj a (o.setPtr y p)).withRoot oc' ∧
      (m.setObj a (o.setPtr y p)).obj? m.root = some oe' ∧ RootRelH sp f oc' oe' ∧ oc'.hist = oc.hist ∧
      oe'.node = oe.node := by
  by_cases ha : a = m.root
  · subst ha
    rw [hra, Option.some.injEq] at ho
    subst ho
    rw [HMem.withRoot_obj?_root hra, Option.some.injEq] at ho'
    subst ho'
    refine ⟨oc.setPtr y p, oe.setPtr y p, ?_, HMem.obj?_setObj_self _ _ _, hr.setPtr (hroot rfl) p, rfl, rfl⟩
    exact HMem.withRoot_setObj_root _ _
  · rw [HMem.withRoot_obj?_ne ha, ho, Option.some.injEq] at ho'
    subst ho'
    refine ⟨oc, oe, HMem.withRoot_setObj_ne ha _, ?_, hr, rfl, rfl⟩
    rw [HMem.obj?_setObj_ne _ _ (Ne.symm ha)]
    exact hra

/-- The object at address a in the memory with another root object: the root
object there, another object as it is; its pointer for y is the same, if a is
the root's address and y a pointee of oc's history. -/
theorem HMem.withRoot_objAt {oc oe : HObj V} (hra : m.obj? m.root = some oe) (hr : RootRelH sp f oc oe)
    {a : Nat} {o : HObj V} (ho : m.obj? a = some o) {y : NodeId} {p : HPtr} (hp : o.ptr? y = some p)
    (hroot : a = m.root → y ∈ pointees sp oc.hist) :
    ∃ o', (m.withRoot oc).obj? a = some o' ∧ o'.ptr? y = some p := by
  by_cases ha : a = m.root
  · subst ha
    rw [hra, Option.some.injEq] at ho
    subst ho
    exact ⟨oc, HMem.withRoot_obj?_root hra, by rw [hr.ptrs y (hroot rfl)]; exact hp⟩
  · exact ⟨o, by rw [HMem.withRoot_obj?_ne ha]; exact ho, hp⟩

/-- The slow path's live handle on the memory with another root object: the same,
and the two root objects still related. -/
theorem HMem.withRoot_resolve {oc oe : HObj V} (hra : m.obj? m.root = some oe) (hr : RootRelH sp f oc oe)
    {a : Nat} {y : NodeId} {o : HObj V} {p : HPtr} (ho : m.obj? a = some o) (hp : o.ptr? y = some p)
    (hroot : a = m.root → y ∈ pointees sp oc.hist) :
    ∃ oc' oe', (m.withRoot oc).resolve a y = ((m.resolve a y).1.withRoot oc', (m.resolve a y).2) ∧
      (m.resolve a y).1.obj? m.root = some oe' ∧ RootRelH sp f oc' oe' ∧ oc'.hist = oc.hist ∧
      oe'.node = oe.node := by
  obtain ⟨o', ho', hp'⟩ := HMem.withRoot_objAt hra hr ho hp hroot
  by_cases hlive : ∃ n hd, p.handle = some n ∧ m.handle? n = some hd ∧ hd.dead = false
  · obtain ⟨n, hd, hn, hh, hl⟩ := hlive
    rw [HMem.resolve_live ho hp hn hh hl, HMem.resolve_live ho' hp' hn (by rw [HMem.withRoot_handle?]; exact hh) hl]
    exact ⟨oc, oe, rfl, hra, hr, rfl, rfl⟩
  · have hnl : ∀ n0 hd0, p.handle = some n0 → m.handle? n0 = some hd0 → hd0.dead = true := by
      intro n0 hd0 h1 h2
      cases hd' : hd0.dead with
      | true => rfl
      | false => exact absurd ⟨n0, hd0, h1, h2, hd'⟩ hlive
    cases ht : m.tableOf y with
    | some n =>
      rw [HMem.resolve_table ho hp hnl ht,
        HMem.resolve_table ho' hp' hnl (by rw [HMem.withRoot_tableOf]; exact ht)]
      obtain ⟨oc', oe', h1, h2, h3, h4, h5⟩ := HMem.withRoot_setObj_rel hra hr ho ho' hroot
        { p with handle := some n }
      exact ⟨oc', oe', by rw [h1], h2, h3, h4, h5⟩
    | none =>
      rw [HMem.resolve_new ho hp hnl ht,
        HMem.resolve_new ho' hp' hnl (by rw [HMem.withRoot_tableOf]; exact ht), HMem.withRoot_emptyHandle]
      have hraE : (m.emptyHandle y).obj? (m.emptyHandle y).root = some oe := hra
      have hoE : (m.emptyHandle y).obj? a = some o := ho
      have hoE' : ((m.emptyHandle y).withRoot oc).obj? a = some o' := ho'
      obtain ⟨oc', oe', h1, h2, h3, h4, h5⟩ := HMem.withRoot_setObj_rel hraE hr hoE hoE' hroot
        { p with handle := some m.nextHandle }
      exact ⟨oc', oe', by rw [HMem.withRoot_nextHandle, h1], h2, h3, h4, h5⟩

/-- The slow path's live handle is an old handle, or a new one with no object. -/
theorem HMem.resolve_handle_old {M : HMem V} {a : Nat} {y : NodeId} {o : HObj V} {p : HPtr}
    (ho : M.obj? a = some o) (hp : o.ptr? y = some p) {hd : Handle}
    (hh : (M.resolve a y).1.handle? (M.resolve a y).2 = some hd) :
    hd.obj = none ∨ M.handle? (M.resolve a y).2 = some hd := by
  by_cases hlive : ∃ n hd0, p.handle = some n ∧ M.handle? n = some hd0 ∧ hd0.dead = false
  · obtain ⟨n, hd0, hn, hh0, hl⟩ := hlive
    rw [HMem.resolve_live ho hp hn hh0 hl] at hh ⊢
    exact Or.inr hh
  · have hnl : ∀ n0 hd0, p.handle = some n0 → M.handle? n0 = some hd0 → hd0.dead = true := by
      intro n0 hd0 h1 h2
      cases hd' : hd0.dead with
      | true => rfl
      | false => exact absurd ⟨n0, hd0, h1, h2, hd'⟩ hlive
    cases ht : M.tableOf y with
    | some n =>
      rw [HMem.resolve_table ho hp hnl ht] at hh ⊢
      exact Or.inr hh
    | none =>
      rw [HMem.resolve_new ho hp hnl ht] at hh
      left
      have e : ((M.emptyHandle y).setObj a (o.setPtr y { p with handle := some M.nextHandle })).handle?
          M.nextHandle = some { node := y, obj := none, written := none, dead := false } := by
        unfold HMem.handle? HMem.emptyHandle HMem.setObj HMem.setTable HMem.setHandle
        simp
      rw [e, Option.some.injEq] at hh
      rw [← hh]

/-- The readers' follow on the memory with another root object, of a pointer of
another object than the root's, or of one of the root's for a pointee of oc's
history: the same, and the two root objects still related. -/
theorem HMem.withRoot_followR (S0' S' : Stream V T) (hm : HEInv sp db S0 k m)
    {oc oe : HObj V} (hra : m.obj? m.root = some oe) (hr : RootRelH sp f oc oe)
    {a : Nat} {y : NodeId} {o : HObj V} {p : HPtr} (ho : m.obj? a = some o) (hp : o.ptr? y = some p)
    (hroot : a = m.root → y ∈ pointees sp oc.hist) (hy : y ≠ SIS.root) :
    (m.followR sp S0' S' a y = none → (m.withRoot oc).followR sp S0' S' a y = none) ∧
      ∀ m' n b, m.followR sp S0' S' a y = some (m', n, b) →
        ∃ oc' oe', (m.withRoot oc).followR sp S0' S' a y = some (m'.withRoot oc', n, b) ∧
          m'.obj? m'.root = some oe' ∧ RootRelH sp f oc' oe' := by
  obtain ⟨o', ho', hp'⟩ := HMem.withRoot_objAt hra hr ho hp hroot
  obtain ⟨o0, ho0, -, hn0⟩ := hm.root
  rw [hra, Option.some.injEq] at ho0
  subst ho0
  -- An object of a handle of node y is not at the root's address.
  have hnotRoot : ∀ (M : HMem V) n hd b (orr : HObj V), HTableOK M → M.obj? m.root = some orr →
      orr.node = SIS.root → M.handle? n = some hd → hd.node = y → hd.obj = some b → b ≠ m.root := by
    intro M n hd b orr ht hMra hon0 hh hnd hb he
    subst he
    obtain ⟨-, ob, hob, hon⟩ := ht.obj_of_handle hh hb
    rw [hMra, Option.some.injEq] at hob
    subst hob
    exact hy (by rw [← hnd, ← hon, hon0])
  have hnext : m.nextObj ≠ m.root := by
    intro he
    have := hm.freshO m.root (Nat.le_of_eq he)
    rw [hra] at this; cases this
  by_cases hfast : ∃ n0 b0 ob0, p.handle = some n0 ∧ m.objOf n0 = some b0 ∧ m.obj? b0 = some ob0 ∧
      ob0.usable p.ref = true
  · obtain ⟨n0, b0, ob0, hn0', hb0, hob0, hu0⟩ := hfast
    have hb0r : b0 ≠ m.root := by
      obtain ⟨hd0, hh0, hnd0⟩ := hm.tbl.ptrNode ho hp hn0'
      have hb0' : hd0.obj = some b0 := by
        unfold HMem.objOf at hb0; rw [hh0] at hb0; exact hb0
      exact hnotRoot m n0 hd0 b0 oe hm.tbl hra hn0 hh0 hnd0 hb0'
    have e1 := HMem.followR_fast sp S0' S' ho hp hn0' hb0 hob0 hu0
    have e2 := HMem.followR_fast sp S0' S' ho' hp' hn0' (by rw [HMem.withRoot_objOf]; exact hb0)
      (by rw [HMem.withRoot_obj?_ne hb0r]; exact hob0) hu0
    refine ⟨fun h => (by rw [e1] at h; cases h), fun m' n b h => ?_⟩
    rw [e1, Option.some.injEq, Prod.mk.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨oc, oe, e2, hra, hr⟩
  · have hnf : ∀ n0 b0 ob0, p.handle = some n0 → m.objOf n0 = some b0 → m.obj? b0 = some ob0 →
        ob0.usable p.ref = false := by
      intro n0 b0 ob0 h1 h2 h3
      cases hu : ob0.usable p.ref with
      | false => rfl
      | true => exact absurd ⟨n0, b0, ob0, h1, h2, h3, hu⟩ hfast
    have hnf' : ∀ n0 b0 ob0, p.handle = some n0 → (m.withRoot oc).objOf n0 = some b0 →
        (m.withRoot oc).obj? b0 = some ob0 → ob0.usable p.ref = false := by
      intro n0 b0 ob0 h1 h2 h3
      rw [HMem.withRoot_objOf] at h2
      have hb0r : b0 ≠ m.root := by
        obtain ⟨hd0, hh0, hnd0⟩ := hm.tbl.ptrNode ho hp h1
        have hb0' : hd0.obj = some b0 := by
          unfold HMem.objOf at h2; rw [hh0] at h2; exact h2
        exact hnotRoot m n0 hd0 b0 oe hm.tbl hra hn0 hh0 hnd0 hb0'
      rw [HMem.withRoot_obj?_ne hb0r] at h3
      exact hnf n0 b0 ob0 h1 h2 h3
    rw [HMem.followR_slow sp S0' S' ho hp hnf, HMem.followR_slow sp S0' S' ho' hp' hnf']
    have hsr : (m.withRoot oc).slowRef S0' y p = m.slowRef S0' y p := rfl
    rw [hsr, HMem.setRef_eq ho hp, HMem.setRef_eq ho' hp']
    -- The write-back.
    obtain ⟨oc1, oe1, h1, h2, h3, h4, h5⟩ := HMem.withRoot_setObj_rel hra hr ho ho' hroot
      { p with ref := m.slowRef S0' y p }
    rw [h1]
    have hoM1 : (m.setObj a (o.setPtr y { p with ref := m.slowRef S0' y p })).obj? a =
        some (o.setPtr y { p with ref := m.slowRef S0' y p }) := HMem.obj?_setObj_self _ _ _
    have hpM1 : (o.setPtr y { p with ref := m.slowRef S0' y p }).ptr? y =
        some { p with ref := m.slowRef S0' y p } := by
      rw [HObj.ptr?_setPtr_of hp]; simp
    have ht1 : HTableOK (m.setObj a (o.setPtr y { p with ref := m.slowRef S0' y p })) := by
      refine HTableOK.setObj hm.tbl ho rfl ?_
      intro z q n hq hqn
      rw [HObj.ptr?_setPtr_of hp] at hq
      split at hq
      · rename_i hz
        subst hz
        rw [Option.some.injEq] at hq
        subst hq
        exact hm.tbl.ptrNode ho hp hqn
      · exact hm.tbl.ptrNode ho hq hqn
    generalize hM1 : m.setObj a (o.setPtr y { p with ref := m.slowRef S0' y p }) = M1 at h2 hoM1 ht1 ⊢
    have hM1r : M1.root = m.root := by rw [← hM1]; rfl
    have hM1n : M1.nextObj = m.nextObj := by rw [← hM1]; rfl
    -- The live handle.
    obtain ⟨oc2, oe2, g1, g2, g3, g4, g5⟩ := HMem.withRoot_resolve (by rw [hM1r]; exact h2) h3 hoM1 hpM1
      (fun ha => by rw [h4]; exact hroot (by rw [← hM1r]; exact ha))
    rw [g1]
    obtain ⟨hdn, hhn, hndn⟩ := HMem.resolve_handle ht1 hoM1 hpM1
    have hM2r : (M1.resolve a y).1.root = m.root := by rw [HMem.resolve_root, hM1r]
    have hM2n : (M1.resolve a y).1.nextObj = m.nextObj := by
      rw [← hM1n]
      by_cases hlive : ∃ n hd, ({ p with ref := m.slowRef S0' y p } : HPtr).handle = some n ∧
          M1.handle? n = some hd ∧ hd.dead = false
      · obtain ⟨n, hd, hn, hh, hl⟩ := hlive
        rw [HMem.resolve_live hoM1 hpM1 hn hh hl]
      · have hnl : ∀ n0 hd0, ({ p with ref := m.slowRef S0' y p } : HPtr).handle = some n0 →
            M1.handle? n0 = some hd0 → hd0.dead = true := by
          intro n0 hd0 h1' h2'
          cases hd' : hd0.dead with
          | true => rfl
          | false => exact absurd ⟨n0, hd0, h1', h2', hd'⟩ hlive
        cases ht : M1.tableOf y with
        | some n => rw [HMem.resolve_table hoM1 hpM1 hnl ht]; rfl
        | none => rw [HMem.resolve_new hoM1 hpM1 hnl ht]; rfl
    -- The handle's object is not the root's.
    have hobjR : ∀ hd b, (M1.resolve a y).1.handle? (M1.resolve a y).2 = some hd → hd.obj = some b →
        b ≠ (M1.resolve a y).1.root := by
      intro hd b hh hb
      rw [hM2r]
      rw [hhn, Option.some.injEq] at hh
      subst hh
      rcases HMem.resolve_handle_old hoM1 hpM1 hhn with h0 | h0
      · rw [h0] at hb; cases hb
      · exact hnotRoot M1 _ hdn b oe1 ht1 h2 (by rw [h5]; exact hn0) h0 hndn hb
    have hnext2 : (M1.resolve a y).1.nextObj ≠ (M1.resolve a y).1.root := by rw [hM2n, hM2r]; exact hnext
    rw [HMem.withRoot_load sp S' _ _ hobjR hnext2]
    -- The root's object after the load.
    have hroot3 : ((M1.resolve a y).1.load sp S' (M1.resolve a y).2 (m.slowRef S0' y p)).1.obj? m.root =
        some oe2 := by
      rw [HMem.load_obj?_ne sp S' _ _ (fun hd hh hb => hobjR hd m.root hh hb hM2r.symm)
        (by rw [hM2n]; exact hnext)]
      rw [← hM1r]
      exact g2
    have hroot3' : ((M1.resolve a y).1.load sp S' (M1.resolve a y).2 (m.slowRef S0' y p)).1.root = m.root := by
      rw [HMem.load_root, hM2r]
    constructor
    · intro hnone
      generalize hL : (M1.resolve a y).1.load sp S' (M1.resolve a y).2 (m.slowRef S0' y p) = L at hnone ⊢
      obtain ⟨L1, L2⟩ := L
      cases L2 with
      | none => rfl
      | some b => simp at hnone
    · intro m' n b hsome
      generalize hL : (M1.resolve a y).1.load sp S' (M1.resolve a y).2 (m.slowRef S0' y p) = L at hsome hroot3 hroot3' ⊢
      obtain ⟨L1, L2⟩ := L
      cases L2 with
      | none => simp at hsome
      | some b' =>
        simp only [Option.some.injEq, Prod.mk.injEq] at hsome
        obtain ⟨rfl, rfl, rfl⟩ := hsome
        exact ⟨oc2, oe2, rfl, by rw [hroot3']; exact hroot3, g3⟩

end Follow

/-! ## Reads after a restart from a cut stream, against the whole stream's -/

section ReadSim

variable {sp : Spec V T} {db1 db : DB V T} {j1 j : Nat} {m : HMem V}

/-- C's follow, on the memory with another root object and the cut streams,
against E's on the whole streams: the same, and the root objects still
related. -/
theorem HEInv.followR_sim (hL : Later sp db1 db j1 j) (hm : HEInv sp db db1.S j m) {c : Nat}
    (hcut : CutOK sp c db1 j1) {t : Time} (hft : lastFa db1.S ≤ t) {f : Time} {oc oe : HObj V}
    (hra : m.obj? m.root = some oe) (hr : RootRelH sp f oc oe) {a : Nat} {o : HObj V}
    (ho : m.obj? a = some o) {y : NodeId} {p : HPtr} (hp : o.ptr? y = some p)
    (hroot : a = m.root → y ∈ pointees sp oc.hist) (hy : y ≠ SIS.root)
    (hg : HPtrLaterT sp db1.S db1 j1 db m t y p) :
    (m.followR sp db1.S db.S a y = none →
        (m.withRoot oc).followR sp (cutStream c db1.S) (cutStream c db.S) a y = none) ∧
      ∀ m' n b, m.followR sp db1.S db.S a y = some (m', n, b) →
        ∃ oc' oe', (m.withRoot oc).followR sp (cutStream c db1.S) (cutStream c db.S) a y =
            some (m'.withRoot oc', n, b) ∧ m'.obj? m'.root = some oe' ∧ RootRelH sp f oc' oe' := by
  have he := hm.followR_later hL hcut hft ho hp hg
  obtain ⟨h1, h2⟩ := HMem.withRoot_followR (cutStream c db1.S) (cutStream c db.S) hm hra hr ho hp hroot hy
  rw [he] at h1 h2
  exact ⟨h1, h2⟩

/-- The reader's follow (`HMem.follow` with `false`), likewise. -/
theorem HEInv.follow_sim (hL : Later sp db1 db j1 j) (hm : HEInv sp db db1.S j m) {c : Nat}
    (hcut : CutOK sp c db1 j1) {t : Time} (hft : lastFa db1.S ≤ t) {f : Time} {oc oe : HObj V}
    (hra : m.obj? m.root = some oe) (hr : RootRelH sp f oc oe) {a : Nat} {o : HObj V}
    (ho : m.obj? a = some o) {y : NodeId} {p : HPtr} (hp : o.ptr? y = some p)
    (hroot : a = m.root → y ∈ pointees sp oc.hist) (hy : y ≠ SIS.root)
    (hg : HPtrLaterT sp db1.S db1 j1 db m t y p) {m1 : HMem V} {b : Nat}
    (hf : m.follow sp db1.S db.S a y false = (m1, some b)) :
    ∃ oc' oe', (m.withRoot oc).follow sp (cutStream c db1.S) (cutStream c db.S) a y false =
        (m1.withRoot oc', some b) ∧ m1.obj? m1.root = some oe' ∧ RootRelH sp f oc' oe' := by
  obtain ⟨-, h2⟩ := hm.followR_sim hL hcut hft hra hr ho hp hroot hy hg
  unfold HMem.follow at hf ⊢
  cases hfr : m.followR sp db1.S db.S a y with
  | none => rw [hfr] at hf; simp at hf
  | some r =>
    obtain ⟨m2, n2, b2⟩ := r
    rw [hfr] at hf
    simp only [Bool.false_eq_true, ↓reduceIte, Prod.mk.injEq, Option.some.injEq] at hf
    obtain ⟨rfl, rfl⟩ := hf
    obtain ⟨oc', oe', e1, e2, e3⟩ := h2 m2 n2 b2 hfr
    rw [e1]
    exact ⟨oc', oe', rfl, e2, e3⟩

/-- C's read below an object that is not the root's, on the memory with another
root object and the cut streams, against E's on the whole streams: the same
nodes, and the root objects still related; E's invariants are kept. -/
theorem CInvH.readAt_sim (hL : Later sp db1 db j1 j) (hls : LiveSub sp) {c : Nat}
    (hcut : CutOK sp c db1 j1) {t : Time} (hft : lastFa db1.S ≤ t) (htj : t ≤ j) {f : Time} :
    ∀ (fuel : Nat) (m : HMem V) (b : Nat) (y : NodeId) (n : Node V), HEInv sp db db1.S j m →
      HInvH sp db db1.S j m → CInvH sp db db1.S m → HReadableT sp db m t b y →
      HLaterSafeT sp db1 j1 db m t b y →
      db.P.get? y = some n → reachable sp db.P t y = true → n.level < fuel → y ≠ SIS.root →
      ∀ oc oe, m.obj? m.root = some oe → RootRelH sp f oc oe →
      ∃ oc' oe', (m.withRoot oc).readAt sp (cutStream c db1.S) (cutStream c db.S) fuel t b =
          ((m.readAt sp db1.S db.S fuel t b).1.withRoot oc', (m.readAt sp db1.S db.S fuel t b).2) ∧
        (m.readAt sp db1.S db.S fuel t b).1.obj? (m.readAt sp db1.S db.S fuel t b).1.root = some oe' ∧
        RootRelH sp f oc' oe' := by
  have hinv := hL.inv
  intro fuel
  induction fuel with
  | zero => intro m b y n _ _ _ _ _ _ _ hlt; omega
  | succ fuel ih =>
    intro m b y n hm hh hc hrd hcs hn hr hlt hyr oc oe hra hrr
    obtain ⟨o, ho, hoy, hoh, hol, hod⟩ := hm.readableT_facts hinv hrd hn
    -- b is not the root's address: its object is of y.
    have hbr : b ≠ m.root := by
      intro he
      obtain ⟨o0, ho0, -, hn0⟩ := hm.root
      rw [← he, ho, Option.some.injEq] at ho0
      subst ho0
      exact hyr (by rw [← hoy, hn0])
    have ho' : (m.withRoot oc).obj? b = some o := by rw [HMem.withRoot_obj?_ne hbr]; exact ho
    rw [readAt_succ_eqH sp (cutStream c db1.S) (cutStream c db.S) fuel (m.withRoot oc) t b ho',
      readAt_succ_eqH sp db1.S db.S fuel m t b ho]
    have hkeepB : ∀ m', HKeepFrom db.P n.level m m' → ∃ o', m'.obj? b = some o' ∧ o'.core = o.core := by
      intro m' hk
      exact hk b o ho (fun nn hnn => by
        rw [hoy, hn, Option.some.injEq] at hnn; subst hnn; exact Nat.le_refl _)
    have hlive : sp.live (o.hist.upTo t) = sp.live (n.hist.upTo t) := by rw [hoh]
    -- The fold, with the relation and E's invariants.
    let I : (HMem V × List (NodeId × Node V)) → (HMem V × List (NodeId × Node V)) → Prop :=
      fun accC accE => HEInv sp db db1.S j accE.1 ∧ HInvH sp db db1.S j accE.1 ∧ CInvH sp db db1.S accE.1 ∧
        HKeepFrom db.P n.level m accE.1 ∧ accE.1.root = m.root ∧ accC.2 = accE.2 ∧
        ∃ oc1 oe1, accC.1 = accE.1.withRoot oc1 ∧ accE.1.obj? accE.1.root = some oe1 ∧ RootRelH sp f oc1 oe1
    have hstep : ∀ (accC accE : HMem V × List (NodeId × Node V)) z, z ∈ sp.live (o.hist.upTo t) → I accC accE →
        I (readStepH sp (cutStream c db1.S) (cutStream c db.S) fuel t b o accC z)
          (readStepH sp db1.S db.S fuel t b o accE z) := by
      intro accC accE z hz ⟨hmA, hhA, hcA, hkcA, hrA, hlA, oc1, oe1, hCA, hraA, hrrA⟩
      obtain ⟨o', ho1', hc'⟩ := hkeepB accE.1 hkcA
      have e4 : o'.hist = o.hist := congrArg (fun c => c.2.2.2.1) hc'
      have hz' : z ∈ sp.live (o'.hist.upTo t) := by rw [e4]; exact hz
      have hrdA := hrd.keep ho ho1' hc'
      have hcsA := hcs.keep ho ho1' hc'
      obtain ⟨p, hp, hg⟩ := hmA.readableT_ptr hinv hls hhA htj hrdA hr ho1' hz'
      have hgc := hmA.laterPtr hL hls hcA htj hrdA hcsA hr ho1' hz' hp
      have hz2 : z ∈ sp.live (n.hist.upTo t) := by rw [← hlive]; exact hz
      obtain ⟨hrz, hzr, nz, hnz, hlvl⟩ := hinv.reach_child hls hn hr hz2
      have hne : o'.node ≠ z := by
        have e1 : o'.node = o.node := congrArg (fun c => c.1) hc'
        intro he
        rw [e1, hoy] at he
        rw [← he, hn, Option.some.injEq] at hnz
        rw [← hnz] at hlvl
        omega
      obtain ⟨m1, n1, b1, hf1, hF1, hrd1⟩ := hmA.follow_goodT hinv hls ho1' hp hg hne
      have hbrA : b ≠ accE.1.root := by rw [hrA]; exact hbr
      obtain ⟨oc2, oe2, g1, g2, g3⟩ := hmA.follow_sim hL hcut hft hraA hrrA ho1' hp
        (fun h => absurd h hbrA) hzr hgc hf1
      have hh1 : HInvH sp db db1.S j m1 := by
        have := hhA.follow_reader hinv hmA b z
        rw [hf1] at this
        exact this
      have hroot1 : m1.root = accE.1.root := HMem.follow_root sp db1.S db.S hf1
      have hc1 : CInvH sp db db1.S m1 := hcA.followed hmA ho1' hp hF1 hroot1
      have hcs1 : HLaterSafeT sp db1 j1 db m1 t b1 z := hF1.laterSafe hmA ho1' hp hne hgc
      obtain ⟨o1, ho1, -, -, hol1, -⟩ := hF1.inv.readableT_facts hinv hrd1 hnz
      have hb1r : b1 ≠ m1.root := by
        intro he
        obtain ⟨o0, ho0, -, hn0⟩ := hF1.inv.root
        obtain ⟨o2, ho2, ho2n, -⟩ := hrd1
        rw [← he, ho2, Option.some.injEq] at ho0
        subst ho0
        exact hzr (by rw [← ho2n, hn0])
      have ho1C : (m1.withRoot oc2).obj? b1 = some o1 := by rw [HMem.withRoot_obj?_ne hb1r]; exact ho1
      obtain ⟨oc3, oe3, f1, f2, f3⟩ := ih m1 b1 z nz hF1.inv hh1 hc1 hrd1 hcs1 hnz hrz (by omega) hzr oc2 oe2 g2 g3
      obtain ⟨-, hI2, hH2, hC2, hkc2, hr2⟩ := CInvH.readAtT_later hL hls hcut hft htj fuel m1 b1 z nz hF1.inv hh1 hc1
        hrd1 hcs1 hnz hrz (by omega)
      have hstE : readStepH sp db1.S db.S fuel t b o accE z =
          ((HMem.readAt sp db1.S db.S fuel m1 t b1).1, accE.2 ++ (HMem.readAt sp db1.S db.S fuel m1 t b1).2) := by
        unfold readStepH
        rw [hf1]
        simp only [ho1, hol1, hol, hlvl, ↓reduceIte]
      have hstC : readStepH sp (cutStream c db1.S) (cutStream c db.S) fuel t b o accC z =
          ((HMem.readAt sp (cutStream c db1.S) (cutStream c db.S) fuel (m1.withRoot oc2) t b1).1,
            accC.2 ++ (HMem.readAt sp (cutStream c db1.S) (cutStream c db.S) fuel (m1.withRoot oc2) t b1).2) := by
        unfold readStepH
        rw [hCA, g1]
        simp only [ho1C, hol1, hol, hlvl, ↓reduceIte]
      rw [hstE, hstC, f1]
      refine ⟨hI2, hH2, hC2, ?_, by rw [hr2, hroot1, hrA], by rw [hlA], oc3, oe3, rfl, f2, f3⟩
      refine hkcA.trans (HKeepFrom.trans ?_ (hkc2.mono (Nat.le_of_lt hlvl)))
      intro x ox hx hlev
      apply hF1.frame x ox hx
      intro hxz
      have := hlev nz (by rw [hxz]; exact hnz)
      omega
    have hfold : ∀ (L : List NodeId), (∀ z ∈ L, z ∈ sp.live (o.hist.upTo t)) →
        ∀ accC accE, I accC accE →
          I (L.foldl (readStepH sp (cutStream c db1.S) (cutStream c db.S) fuel t b o) accC)
            (L.foldl (readStepH sp db1.S db.S fuel t b o) accE) := by
      intro L
      induction L with
      | nil => intro _ accC accE h; exact h
      | cons z L ihL =>
        intro hL' accC accE h
        simp only [List.foldl_cons]
        exact ihL (fun z' hz' => hL' z' (List.mem_cons_of_mem _ hz')) _ _
          (hstep accC accE z (hL' z List.mem_cons_self) h)
    obtain ⟨-, -, -, -, -, hl, oc', oe', h1, h2, h3⟩ := hfold (sp.live (o.hist.upTo t)) (fun z hz => hz)
      ((m.withRoot oc), [(o.node, o.nodeAt t)]) (m, [(o.node, o.nodeAt t)])
      ⟨hm, hh, hc, HKeepFrom.refl _ _ m, rfl, rfl, oc, oe, rfl, hra, hrr⟩
    exact ⟨oc', oe', Prod.ext h1 hl, h2, h3⟩

/-- C's read at a time from the first available time on, from the root's object,
on the memory with another root object and the cut streams, against E's on the
whole streams: the same nodes but the root's own, and the root objects still
related. -/
theorem CInvH.read_sim (hL : Later sp db1 db j1 j) (hls : LiveSub sp) (hm : HEInv sp db db1.S j m)
    (hh : HInvH sp db db1.S j m) (hc : CInvH sp db db1.S m) {c : Nat} (hcut : CutOK sp c db1 j1) {t : Time}
    (hft : lastFa db1.S ≤ t) (htj : t ≤ j) {f : Time} (hf : f ≤ t) {oc oe : HObj V}
    (hra : m.obj? m.root = some oe) (hr : RootRelH sp f oc oe) :
    ∃ oc' oe' tail, (m.withRoot oc).read sp (cutStream c db1.S) (cutStream c db.S) t =
        ((m.read sp db1.S db.S t).1.withRoot oc', (SIS.root, oc.nodeAt t) :: tail) ∧
      (m.read sp db1.S db.S t).2 = (SIS.root, oe.nodeAt t) :: tail ∧
      (m.read sp db1.S db.S t).1.obj? (m.read sp db1.S db.S t).1.root = some oe' ∧ RootRelH sp f oc' oe' := by
  have hinv := hL.inv
  obtain ⟨o0, ho0, hco, hn0⟩ := hm.root
  rw [hra, Option.some.injEq] at ho0
  subst ho0
  obtain ⟨n0, hnr⟩ := Option.isSome_iff_exists.mp hinv.rootIn
  have hrd : HReadableT sp db m t m.root SIS.root := ⟨oe, hra, hn0, Or.inl hco⟩
  have hcs : HLaterSafeT sp db1 j1 db m t m.root SIS.root := ⟨oe, hra, hn0, Or.inl hco⟩
  obtain ⟨o', ho', -, hoh, hol, -⟩ := hm.readableT_facts hinv hrd hnr
  rw [hra, Option.some.injEq] at ho'
  subst ho'
  have hraC : (m.withRoot oc).obj? (m.withRoot oc).root = some oc := HMem.withRoot_obj?_root hra
  have hlev : oc.level = oe.level := hr.level
  unfold HMem.read
  rw [hraC, hra]
  simp only
  rw [show (m.withRoot oc).root = m.root from rfl]
  rw [hlev, readAt_succ_eqH sp (cutStream c db1.S) (cutStream c db.S) (oe.level) (m.withRoot oc) t m.root hraC,
    readAt_succ_eqH sp db1.S db.S (oe.level) m t m.root hra]
  have hrr : reachable sp db.P t SIS.root = true := reachable_root hnr t
  have hliveEq : sp.live (oc.hist.upTo t) = sp.live (oe.hist.upTo t) := hr.live t hf
  rw [hliveEq]
  have hkeepB : ∀ m', HKeepFrom db.P n0.level m m' → ∃ o2, m'.obj? m.root = some o2 ∧ o2.core = oe.core := by
    intro m' hk
    exact hk m.root oe hra (fun nn hnn => by
      rw [hn0, hnr, Option.some.injEq] at hnn; subst hnn; exact Nat.le_refl _)
  have hlive : sp.live (oe.hist.upTo t) = sp.live (n0.hist.upTo t) := by rw [hoh]
  -- The fold, with the relation and E's invariants.
  let I : (HMem V × List (NodeId × Node V)) → (HMem V × List (NodeId × Node V)) → Prop :=
    fun accC accE => HEInv sp db db1.S j accE.1 ∧ HInvH sp db db1.S j accE.1 ∧ CInvH sp db db1.S accE.1 ∧
      HKeepFrom db.P n0.level m accE.1 ∧ accE.1.root = m.root ∧
      (∃ tail, accC.2 = (oc.node, oc.nodeAt t) :: tail ∧ accE.2 = (oe.node, oe.nodeAt t) :: tail) ∧
      ∃ oc1 oe1, accC.1 = accE.1.withRoot oc1 ∧ accE.1.obj? accE.1.root = some oe1 ∧ RootRelH sp f oc1 oe1
  have hstep : ∀ (accC accE : HMem V × List (NodeId × Node V)) z, z ∈ sp.live (oe.hist.upTo t) → I accC accE →
      I (readStepH sp (cutStream c db1.S) (cutStream c db.S) oe.level t m.root oc accC z)
        (readStepH sp db1.S db.S oe.level t m.root oe accE z) := by
    intro accC accE z hz ⟨hmA, hhA, hcA, hkcA, hrA, ⟨tl, hlC, hlE⟩, oc1, oe1, hCA, hraA, hrrA⟩
    obtain ⟨o2, ho2, hc2⟩ := hkeepB accE.1 hkcA
    have e4 : o2.hist = oe.hist := congrArg (fun c => c.2.2.2.1) hc2
    have hz' : z ∈ sp.live (o2.hist.upTo t) := by rw [e4]; exact hz
    rw [← hrA] at ho2
    rw [hraA, Option.some.injEq] at ho2
    subst ho2
    have hrdA := hrd.keep hra (by rw [← hrA]; exact hraA) hc2
    have hcsA := hcs.keep hra (by rw [← hrA]; exact hraA) hc2
    have hraA' : accE.1.obj? m.root = some oe1 := by rw [← hrA]; exact hraA
    obtain ⟨p, hp, hg⟩ := hmA.readableT_ptr hinv hls hhA htj hrdA hrr hraA' hz'
    have hgc := hmA.laterPtr hL hls hcA htj hrdA hcsA hrr hraA' hz' hp
    have hz2 : z ∈ sp.live (n0.hist.upTo t) := by rw [← hlive]; exact hz
    obtain ⟨hrz, hzr, nz, hnz, hlvl⟩ := hinv.reach_child hls hnr hrr hz2
    have hne : oe1.node ≠ z := by
      have e1 : oe1.node = oe.node := congrArg (fun c => c.1) hc2
      intro he
      exact hzr (by rw [← he, e1, hn0])
    obtain ⟨m1, n1, b1, hf1, hF1, hrd1⟩ := hmA.follow_goodT hinv hls hraA' hp hg hne
    -- z is a pointee of C's root object too.
    have hzc : z ∈ pointees sp oc1.hist := by
      apply mem_pointees_of_live hls (t := t)
      rw [hrrA.live t hf, e4]
      exact hz
    obtain ⟨oc2, oe2, g1, g2, g3⟩ := hmA.follow_sim hL hcut hft hraA hrrA hraA' hp
      (fun _ => hzc) hzr hgc hf1
    have hh1 : HInvH sp db db1.S j m1 := by
      have := hhA.follow_reader hinv hmA m.root z
      rw [hf1] at this
      exact this
    have hroot1 : m1.root = accE.1.root := HMem.follow_root sp db1.S db.S hf1
    have hc1 : CInvH sp db db1.S m1 := hcA.followed hmA hraA' hp hF1 hroot1
    have hcs1 : HLaterSafeT sp db1 j1 db m1 t b1 z := hF1.laterSafe hmA hraA' hp hne hgc
    obtain ⟨o1, ho1, -, -, hol1, -⟩ := hF1.inv.readableT_facts hinv hrd1 hnz
    have hb1r : b1 ≠ m1.root := by
      intro he
      obtain ⟨o0', ho0', -, hn0'⟩ := hF1.inv.root
      obtain ⟨o3, ho3, ho3n, -⟩ := hrd1
      rw [← he, ho3, Option.some.injEq] at ho0'
      subst ho0'
      exact hzr (by rw [← ho3n, hn0'])
    have ho1C : (m1.withRoot oc2).obj? b1 = some o1 := by rw [HMem.withRoot_obj?_ne hb1r]; exact ho1
    have hlvl' : nz.level < oe.level := by rw [hol]; exact hlvl
    obtain ⟨oc3, oe3, f1, f2, f3⟩ := CInvH.readAt_sim hL hls hcut hft htj oe.level m1 b1 z nz hF1.inv hh1 hc1 hrd1
      hcs1 hnz hrz (by omega) hzr oc2 oe2 g2 g3
    obtain ⟨-, hI2, hH2, hC2, hkc2, hr2⟩ := CInvH.readAtT_later hL hls hcut hft htj oe.level m1 b1 z nz hF1.inv hh1
      hc1 hrd1 hcs1 hnz hrz (by omega)
    have hstE : readStepH sp db1.S db.S oe.level t m.root oe accE z =
        ((HMem.readAt sp db1.S db.S oe.level m1 t b1).1, accE.2 ++ (HMem.readAt sp db1.S db.S oe.level m1 t b1).2) := by
      unfold readStepH
      rw [hf1]
      simp only [ho1, hol1, hlvl', ↓reduceIte]
    have hstC : readStepH sp (cutStream c db1.S) (cutStream c db.S) oe.level t m.root oc accC z =
        ((HMem.readAt sp (cutStream c db1.S) (cutStream c db.S) oe.level (m1.withRoot oc2) t b1).1,
          accC.2 ++ (HMem.readAt sp (cutStream c db1.S) (cutStream c db.S) oe.level (m1.withRoot oc2) t b1).2) := by
      unfold readStepH
      rw [hCA, g1]
      simp only [ho1C, hol1, hlev, hlvl', ↓reduceIte]
    rw [hstE, hstC, f1]
    refine ⟨hI2, hH2, hC2, ?_, by rw [hr2, hroot1, hrA], ⟨tl ++ (HMem.readAt sp db1.S db.S oe.level m1 t b1).2,
      by rw [hlC]; rfl, by rw [hlE]; rfl⟩, oc3, oe3, rfl, f2, f3⟩
    refine hkcA.trans (HKeepFrom.trans ?_ (hkc2.mono (by rw [← hol]; exact Nat.le_of_lt hlvl')))
    intro x ox hx hlev'
    apply hF1.frame x ox hx
    intro hxz
    have := hlev' nz (by rw [hxz]; exact hnz)
    omega
  have hfold : ∀ (L : List NodeId), (∀ z ∈ L, z ∈ sp.live (oe.hist.upTo t)) →
      ∀ accC accE, I accC accE →
        I (L.foldl (readStepH sp (cutStream c db1.S) (cutStream c db.S) oe.level t m.root oc) accC)
          (L.foldl (readStepH sp db1.S db.S oe.level t m.root oe) accE) := by
    intro L
    induction L with
    | nil => intro _ accC accE h; exact h
    | cons z L ihL =>
      intro hL' accC accE h
      simp only [List.foldl_cons]
      exact ihL (fun z' hz' => hL' z' (List.mem_cons_of_mem _ hz')) _ _
        (hstep accC accE z (hL' z List.mem_cons_self) h)
  obtain ⟨-, -, -, -, -, ⟨tl, hlC, hlE⟩, oc', oe', h1, h2, h3⟩ := hfold (sp.live (oe.hist.upTo t)) (fun z hz => hz)
    ((m.withRoot oc), [(oc.node, oc.nodeAt t)]) (m, [(oe.node, oe.nodeAt t)])
    ⟨hm, hh, hc, HKeepFrom.refl _ _ m, rfl, ⟨[], rfl, rfl⟩, oc, oe, rfl, hra, hr⟩
  have hnc : oc.node = SIS.root := by rw [hr.node, hn0]
  refine ⟨oc', oe', tl, Prod.ext h1 (by rw [hlC, hnc]), by rw [hlE, hn0], h2, h3⟩

end ReadSim

end SIS
