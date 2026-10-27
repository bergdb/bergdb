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

end SIS
