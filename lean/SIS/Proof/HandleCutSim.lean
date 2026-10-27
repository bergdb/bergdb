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
          m'.obj? m'.root = some oe' ∧ RootRelH sp f oc' oe' ∧ oc'.hist = oc.hist := by
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
    exact ⟨oc, oe, e2, hra, hr, rfl⟩
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
        exact ⟨oc2, oe2, rfl, by rw [hroot3']; exact hroot3, g3, by rw [g4, h4]⟩

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
            some (m'.withRoot oc', n, b) ∧ m'.obj? m'.root = some oe' ∧ RootRelH sp f oc' oe' ∧
            oc'.hist = oc.hist := by
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
        (m1.withRoot oc', some b) ∧ m1.obj? m1.root = some oe' ∧ RootRelH sp f oc' oe' ∧
        oc'.hist = oc.hist := by
  obtain ⟨-, h2⟩ := hm.followR_sim hL hcut hft hra hr ho hp hroot hy hg
  unfold HMem.follow at hf ⊢
  cases hfr : m.followR sp db1.S db.S a y with
  | none => rw [hfr] at hf; simp at hf
  | some r =>
    obtain ⟨m2, n2, b2⟩ := r
    rw [hfr] at hf
    simp only [Bool.false_eq_true, ↓reduceIte, Prod.mk.injEq, Option.some.injEq] at hf
    obtain ⟨rfl, rfl⟩ := hf
    obtain ⟨oc', oe', e1, e2, e3, e4⟩ := h2 m2 n2 b2 hfr
    rw [e1]
    exact ⟨oc', oe', rfl, e2, e3, e4⟩

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
      obtain ⟨oc2, oe2, g1, g2, g3, -⟩ := hmA.follow_sim hL hcut hft hraA hrrA ho1' hp
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
    obtain ⟨oc2, oe2, g1, g2, g3, -⟩ := hmA.follow_sim hL hcut hft hraA hrrA hraA' hp
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

/-! ## The writer's walk after a restart from a cut stream -/

section WalkSim

variable {sp : Spec V T} {db1 db : DB V T} {j1 j : Nat} {m : HMem V}

/-- The writer's promote of an object that is not the root's: the same with
another root object. -/
theorem HMem.withRoot_promote {oc : HObj V} {n : Nat} (hn : ∀ b, m.objOf n = some b → b ≠ m.root) :
    (m.withRoot oc).promote n = ((m.promote n).1.withRoot oc, (m.promote n).2) := by
  unfold HMem.promote
  rw [HMem.withRoot_objOf]
  cases hb : m.objOf n with
  | none => rfl
  | some b =>
    simp only
    rw [HMem.withRoot_obj?_ne (hn b hb)]
    cases m.obj? b with
    | none => rfl
    | some o => simp only [HMem.withRoot_setObj_ne (hn b hb)]

/-- The promote leaves every object but the promoted one. -/
theorem HMem.promote_obj?_ne {n x : Nat} (hn : ∀ b, m.objOf n = some b → b ≠ x) :
    (m.promote n).1.obj? x = m.obj? x := by
  unfold HMem.promote
  cases hb : m.objOf n with
  | none => rfl
  | some b =>
    simp only
    cases m.obj? b with
    | none => rfl
    | some o => exact HMem.obj?_setObj_ne _ _ (Ne.symm (hn b hb))

theorem HMem.promote_root (n : Nat) : (m.promote n).1.root = m.root := by
  unfold HMem.promote
  split
  · split <;> rfl
  · rfl

/-- C's writer's follow of a live pointer of the canonical object of a current
node, on the memory with another root object and the cut streams, against E's
on the whole streams: the same, and the root objects still related. -/
theorem HEInv.followW_sim (hL : Later sp db1 db j1 j) (hls : LiveSub sp) (hm : HEInv sp db db1.S j m)
    {c : Nat} (hcut : CutOK sp c db1 j1) {f : Time} {oc oe : HObj V} (hra : m.obj? m.root = some oe)
    (hr : RootRelH sp f oc oe) {a : Nat} {op : HObj V} (hop : m.obj? a = some op)
    (hco : op.canonical = true) (hrp : reachable sp db.P j op.node = true) {x : NodeId}
    (hx : x ∈ sp.live op.hist) (hroot : a = m.root → x ∈ pointees sp oc.hist) :
    ∃ oc' oe', (m.withRoot oc).follow sp (cutStream c db1.S) (cutStream c db.S) a x true =
        ((m.follow sp db1.S db.S a x true).1.withRoot oc', (m.follow sp db1.S db.S a x true).2) ∧
      (m.follow sp db1.S db.S a x true).1.obj? (m.follow sp db1.S db.S a x true).1.root = some oe' ∧
      RootRelH sp f oc' oe' ∧ oc'.hist = oc.hist := by
  have hinv := hL.inv
  have hfj : lastFa db1.S ≤ j := by
    have h1 := hL.fa1
    have h2 := hL.inv1.spLt
    have h3 := hL.le
    have h4 := hL.inv1.len
    omega
  obtain ⟨n, hn, hhist, -, -⟩ := hm.cc a op hop hco
  have hx' : x ∈ sp.live (n.hist.upTo j) := by
    rw [upTo_of_forall _ _ (hinv.times _ n hn), ← hhist]; exact hx
  obtain ⟨e, he, hxe⟩ := hls _ _ hx'
  obtain ⟨nx, hnx, hlt⟩ := hinv.ptrs op.node n hn e (mem_upTo.mp he).1 x hxe
  have hxroot : x ≠ SIS.root := hinv.ptr_ne_root hn (mem_upTo.mp he).1 hxe
  have hxw : written sp x = true := written_of_ne_root sp hxroot
  have hrx : reachable sp db.P j x = true := by
    rw [reachable_iff] at hrp ⊢; exact Reach.child hrp hn hx' hnx hlt
  obtain ⟨p, hp, hli1, hli2⟩ := hm.live a op hop hco hrp x hx
  have hg : HPtrLaterT sp db1.S db1 j1 db m j x p := by
    cases hxD : inD db.D x with
    | true =>
      obtain ⟨-, -, -, hcs⟩ := hli1 hxD
      exact Or.inl hcs
    | false =>
      cases hhc : m.holdsCanonical p with
      | true =>
        obtain ⟨-, -, -, hcs⟩ := HMem.holdsLive_of_holdsCanonical hm.tbl (hm.tbl.ptr_nodes hop hp) hhc
        exact Or.inl hcs
      | false =>
        right
        have he' := hli2 hxD
        rw [HMem.slowRef_of_not_holds hhc] at he'
        obtain ⟨u, hu, hgu⟩ := hinv.clean_good hls hxD hxw (Nat.le_refl _) hrx
        rw [hu] at he'
        refine ⟨u.recNo, u, hinv.lv_at hu, hL.VOK_ok (Nat.le_refl _) hrx (hinv.VOK_lv hL.pre hu)
          (hinv.lv_at hu), hgu, fun r hr' => ?_⟩
        rw [he', Option.map_some, Option.some.injEq] at hr'
        omega
  obtain ⟨h1, h2⟩ := hm.followR_sim hL hcut hfj hra hr hop hp hroot hxroot hg
  unfold HMem.follow
  cases hfr : m.followR sp db1.S db.S a x with
  | none =>
    rw [h1 hfr]
    exact ⟨oc, oe, rfl, hra, hr, rfl⟩
  | some res =>
    obtain ⟨m1, n1, b1⟩ := res
    obtain ⟨oc', oe', e1, e2, e3, e4⟩ := h2 m1 n1 b1 hfr
    rw [e1]
    simp only [↓reduceIte]
    have hF := hm.followR_ok hinv hop hfr
    -- the promoted object is x's, not the root's
    have hnr : ∀ b, m1.objOf n1 = some b → b ≠ m1.root := by
      intro b hb he
      rw [hF.objOf, Option.some.injEq] at hb
      subst hb
      obtain ⟨ob, hob, hobn⟩ := hF.obj
      obtain ⟨o0, ho0, -, hn0⟩ := hF.inv.root
      rw [← he, hob, Option.some.injEq] at ho0
      subst ho0
      exact hxroot (by rw [← hobn, hn0])
    rw [HMem.withRoot_promote hnr]
    refine ⟨oc', oe', rfl, ?_, e3, e4⟩
    rw [HMem.promote_root, HMem.promote_obj?_ne hnr]
    exact e2

theorem HMem.follow_root_any (sp : Spec V T) (S0 S : Stream V T) (a : Nat) (y : NodeId) (w : Bool) :
    (m.follow sp S0 S a y w).1.root = m.root := by
  unfold HMem.follow
  cases hf : m.followR sp S0 S a y with
  | none => rfl
  | some r =>
    obtain ⟨m1, n, b⟩ := r
    simp only
    have := HMem.followR_root sp S0 S hf
    cases w with
    | true => simp only [↓reduceIte]; rw [HMem.promote_root, this]
    | false => simp only [Bool.false_eq_true, ↓reduceIte]; exact this

theorem HMem.reachOnPath_root (sp : Spec V T) (S0 S : Stream V T) (P : Struct V) (j : Time)
    (path : List NodeId) (x : NodeId) : (m.reachOnPath sp S0 S P j path x).root = m.root := by
  unfold HMem.reachOnPath
  simp only
  cases List.find? (fun p => match P.get? p, m.canonicalOf p with
      | some n, some _ => (sp.live (n.hist.upTo (j - 1))).contains x
      | _, _ => false) path with
  | none => rfl
  | some p =>
    simp only
    cases m.canonicalOf p with
    | none => rfl
    | some a => exact HMem.follow_root_any sp S0 S _ x true

/-- The writer reaches a node of its path the same way with a structure P' that
agrees with P on the live children of the path's nodes at j - 1. -/
theorem HMem.reachOnPath_congrP {P P' : Struct V} {jj : Time} {path : List NodeId}
    (hP : ∀ p ∈ path, (P'.get? p).map (fun n => sp.live (n.hist.upTo (jj - 1))) =
      (P.get? p).map (fun n => sp.live (n.hist.upTo (jj - 1)))) (S0 S : Stream V T) (m : HMem V) (x : NodeId) :
    m.reachOnPath sp S0 S P' jj path x = m.reachOnPath sp S0 S P jj path x := by
  unfold HMem.reachOnPath
  simp only
  congr 1
  apply find?_congr_of_mem
  intro p hp
  have := hP p hp
  cases h1 : P'.get? p <;> cases h2 : P.get? p <;> rw [h1, h2] at this <;> simp at this
  all_goals first | rfl | (cases m.canonicalOf p <;> simp [this])

/-- C's writer reaches a node of its path, on the memory with another root object
and the cut streams, as E's on the whole streams. -/
theorem HEInv.reachOnPath_sim (hL : Later sp db1 db j1 j) (hls : LiveSub sp) (hm : HEInv sp db db1.S j m)
    {c : Nat} (hcut : CutOK sp c db1 j1) {f : Time} {oc oe : HObj V} (hra : m.obj? m.root = some oe)
    (hr : RootRelH sp f oc oe) {path : List NodeId} (hpath : ∀ p ∈ path, reachable sp db.P j p = true)
    (hPr : ∀ n, db.P.get? SIS.root = some n → ∀ x ∈ sp.live (n.hist.upTo j), x ∈ pointees sp oc.hist)
    (x : NodeId) :
    ∃ oc' oe', (m.withRoot oc).reachOnPath sp (cutStream c db1.S) (cutStream c db.S) db.P (j + 1) path x =
        (m.reachOnPath sp db1.S db.S db.P (j + 1) path x).withRoot oc' ∧
      (m.reachOnPath sp db1.S db.S db.P (j + 1) path x).obj? m.root = some oe' ∧
      RootRelH sp f oc' oe' ∧ oc'.hist = oc.hist := by
  have hinv := hL.inv
  have hcan : ∀ z, (m.withRoot oc).canonicalOf z = m.canonicalOf z := HMem.withRoot_canonicalOf hra hr.canonical
  have hK1 : j + 1 - 1 = j := by omega
  unfold HMem.reachOnPath
  simp only [hcan]
  cases hf : path.find? (fun p => match db.P.get? p, m.canonicalOf p with
      | some n, some _ => (sp.live (n.hist.upTo (j + 1 - 1))).contains x
      | _, _ => false) with
  | none => exact ⟨oc, oe, rfl, hra, hr, rfl⟩
  | some p =>
    simp only
    have hpp := List.find?_some hf
    have hpm := List.mem_of_find?_eq_some hf
    cases hnp : db.P.get? p with
    | none => rw [hnp] at hpp; simp at hpp
    | some np =>
      cases hcp : m.canonicalOf p with
      | none => exact ⟨oc, oe, rfl, hra, hr, rfl⟩
      | some bp =>
        simp only
        rw [hnp, hcp] at hpp
        simp only [hK1, List.contains_iff_mem] at hpp
        obtain ⟨op, hop, hco, hnode⟩ := hm.obj_of_canonicalOf hcp
        obtain ⟨nf, hnf, hh', -, -⟩ := hm.cc bp op hop hco
        rw [hnode, hnp, Option.some.injEq] at hnf
        subst hnf
        have hxop : x ∈ sp.live op.hist := by
          rw [hh', ← upTo_of_forall _ _ (hinv.times p np hnp)]; exact hpp
        have hroot : bp = m.root → x ∈ pointees sp oc.hist := by
          intro he
          obtain ⟨o0, ho0, -, hn0⟩ := hm.root
          rw [← he, hop, Option.some.injEq] at ho0
          subst ho0
          rw [hnode] at hn0
          subst hn0
          exact hPr np hnp x hpp
        obtain ⟨oc', oe', e1, e2, e3, e4⟩ := hm.followW_sim hL hls hcut hra hr hop hco
          (by rw [hnode]; exact hpath p hpm) hxop hroot
        rw [e1]
        refine ⟨oc', oe', rfl, ?_, e3, e4⟩
        rw [← HMem.follow_root_any sp db1.S db.S bp x true]
        exact e2

/-- C's writer's walk, on the memory with another root object and the cut streams,
as E's on the whole streams. -/
theorem HEInv.reachPath_sim (hL : Later sp db1 db j1 j) (hls : LiveSub sp) (hev : EvLogic sp db j)
    {c : Nat} (hcut : CutOK sp c db1 j1) {f : Time} {path : List NodeId}
    (hpath : ∀ p ∈ path, reachable sp db.P j p = true) :
    ∀ (L : List NodeId) (m : HMem V) (oc oe : HObj V), HEInv sp db db1.S j m →
      m.obj? m.root = some oe → RootRelH sp f oc oe →
      (∀ n, db.P.get? SIS.root = some n → ∀ x ∈ sp.live (n.hist.upTo j), x ∈ pointees sp oc.hist) →
      ∃ oc' oe', L.foldl (HMem.reachOnPath sp (cutStream c db1.S) (cutStream c db.S) db.P (j + 1) path)
          (m.withRoot oc) = (L.foldl (HMem.reachOnPath sp db1.S db.S db.P (j + 1) path) m).withRoot oc' ∧
        (L.foldl (HMem.reachOnPath sp db1.S db.S db.P (j + 1) path) m).obj?
          (L.foldl (HMem.reachOnPath sp db1.S db.S db.P (j + 1) path) m).root = some oe' ∧
        RootRelH sp f oc' oe' ∧ oc'.hist = oc.hist := by
  have hinv := hL.inv
  intro L
  induction L with
  | nil => intro m oc oe _ hra hr _; exact ⟨oc, oe, rfl, hra, hr, rfl⟩
  | cons x L ih =>
    intro m oc oe hm hra hr hPr
    simp only [List.foldl_cons]
    obtain ⟨oc1, oe1, e1, e2, e3, e4⟩ := hm.reachOnPath_sim hL hls hcut hra hr hpath hPr x
    rw [e1]
    have hm1 := (hm.reachOnPath_ok hinv hls hev hpath x).1
    have hra1 : (m.reachOnPath sp db1.S db.S db.P (j + 1) path x).obj?
        (m.reachOnPath sp db1.S db.S db.P (j + 1) path x).root = some oe1 := by
      rw [HMem.reachOnPath_root]; exact e2
    obtain ⟨oc2, oe2, f1, f2, f3, f4⟩ := ih _ oc1 oe1 hm1 hra1 e3 (by rw [e4]; exact hPr)
    exact ⟨oc2, oe2, f1, f2, f3, by rw [f4, e4]⟩

end WalkSim

/-! ## Evictions on a memory with another root object -/

section EvictSim

variable {m : HMem V}

theorem HMem.withRoot_pinned {oc : HObj V} (D : Dirty) (a : Nat) : (m.withRoot oc).pinned D a = m.pinned D a := by
  unfold HMem.pinned
  simp only [HMem.withRoot_root]
  by_cases ha : a = m.root
  · subst ha
    simp
  · rw [HMem.withRoot_obj?_ne ha]

theorem HMem.withRoot_evictable {oc oe : HObj V} (hra : m.obj? m.root = some oe) (D : Dirty) (n : Nat) :
    (m.withRoot oc).evictable D n = m.evictable D n := by
  unfold HMem.evictable
  simp only [HMem.withRoot_handle?]
  cases m.handle? n with
  | none => rfl
  | some hd =>
    simp only
    cases hd.obj with
    | none => rfl
    | some a =>
      simp only
      by_cases ha : a = m.root
      · subst ha
        rw [HMem.withRoot_obj?_root hra, hra]
        simp [HMem.pinned]
      · rw [HMem.withRoot_obj?_ne ha, HMem.withRoot_pinned D a]

/-- An eviction on the memory with another root object: the same; the root's
object is never evicted. -/
theorem HMem.withRoot_evict {oc oe : HObj V} (hra : m.obj? m.root = some oe) (D : Dirty) (n : Nat) :
    (m.withRoot oc).evict D n = (m.evict D n).withRoot oc := by
  have hev := HMem.withRoot_evictable (oc := oc) hra D n
  unfold HMem.evict
  rw [hev]
  cases hev' : m.evictable D n with
  | false => rfl
  | true =>
    simp only [↓reduceIte, HMem.withRoot_handle?]
    obtain ⟨hd, b, ob, hh, -, hb, hob, hpin, -⟩ := HMem.evictable_some hev'
    have hbr : b ≠ m.root := by
      intro he
      unfold HMem.pinned at hpin
      simp [he] at hpin
    rw [hh]
    simp only [hb]
    rw [HMem.withRoot_obj?_ne hbr]
    unfold HMem.withRoot HMem.setHandle
    simp only [filter_map_rootH]

end EvictSim

/-! ## The change on a memory with another root object -/

section ChangeSim

variable {sp : Spec V T} {P P' : Struct V} {j : Time} {m : HMem V} {oc oe : HObj V}

theorem srcOKH_congrP (hReach : ∀ x, reachable sp P' (j - 1) x = reachable sp P (j - 1) x)
    (hProot : (P'.get? root).map (fun n => sp.live (n.hist.upTo (j - 1))) =
      (P.get? root).map (fun n => sp.live (n.hist.upTo (j - 1)))) (y : NodeId) (p : Nat × HObj V) :
    srcOKH sp P' j y p = srcOKH sp P j y p := by
  unfold srcOKH
  rw [hReach]
  by_cases hn : p.2.node = root
  · rw [hn]
    cases h1 : P'.get? root <;> cases h2 : P.get? root <;> rw [h1, h2] at hProot <;> simp at hProot
    all_goals first | rfl | simp [hProot]
  · simp [written_of_ne_root sp hn]

theorem srcOKH_rootRel {f : Time} (hReach : ∀ x, reachable sp P' (j - 1) x = reachable sp P (j - 1) x)
    (hProot : (P'.get? root).map (fun n => sp.live (n.hist.upTo (j - 1))) =
      (P.get? root).map (fun n => sp.live (n.hist.upTo (j - 1))))
    (hPr : ∀ n, P.get? root = some n → ∀ y ∈ sp.live (n.hist.upTo (j - 1)),
      y ∈ pointees sp oc.hist ∧ y ∈ pointees sp oe.hist)
    (hr : RootRelH sp f oc oe) (hnode : oe.node = root) (y : NodeId) (r : Nat) :
    srcOKH sp P' j y (r, oc) = srcOKH sp P j y (r, oe) ∧
      (srcOKH sp P j y (r, oe) = true → oc.ptr? y = oe.ptr? y) := by
  cases hv : sp.virt with
  | false =>
    rw [hr.nv hv]
    exact ⟨srcOKH_congrP hReach hProot y _, fun _ => rfl⟩
  | true =>
    have hnc : oc.node = root := by rw [hr.node]; exact hnode
    have hw : written sp root = false := by simp [written, hv]
    unfold srcOKH
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
        have hs := hr.ptrs y hyc
        refine ⟨?_, fun _ => hs⟩
        rw [hs, hr.canonical]
        simp [hyc, hye]
      · exact ⟨by simp [hy], fun h => by simp [hy] at h⟩

theorem srcPtrH_withRoot {f : Time} (hReach : ∀ x, reachable sp P' (j - 1) x = reachable sp P (j - 1) x)
    (hProot : (P'.get? root).map (fun n => sp.live (n.hist.upTo (j - 1))) =
      (P.get? root).map (fun n => sp.live (n.hist.upTo (j - 1))))
    (hPr : ∀ n, P.get? root = some n → ∀ y ∈ sp.live (n.hist.upTo (j - 1)),
      y ∈ pointees sp oc.hist ∧ y ∈ pointees sp oe.hist)
    (hnd : (m.objs.map (·.1)).Nodup) (hra : m.obj? m.root = some oe) (hr : RootRelH sp f oc oe)
    (hnode : oe.node = root) (y : NodeId) :
    srcPtrH sp P' j (m.withRoot oc) y = srcPtrH sp P j m y := by
  unfold srcPtrH HMem.withRoot
  simp only
  rw [List.find?_map]
  have hcongr : m.objs.find? (srcOKH sp P' j y ∘ (fun p => if p.1 == m.root then (m.root, oc) else p)) =
      m.objs.find? (srcOKH sp P j y) := by
    apply find?_congr_of_mem
    intro p hp
    simp only [Function.comp]
    by_cases he : p.1 = m.root
    · have hpo : p.2 = oe := by
        have := lookup_of_mem m.objs hnd p hp
        rw [he] at this
        exact Option.some.inj (this.symm.trans hra)
      obtain ⟨a, b⟩ := p
      simp only at he hpo
      subst he hpo
      simp only [beq_self_eq_true, ↓reduceIte]
      exact (srcOKH_rootRel hReach hProot hPr hr hnode y _).1
    · have : (p.1 == m.root) = false := by simp [he]
      simp only [this, Bool.false_eq_true, ↓reduceIte]
      exact srcOKH_congrP hReach hProot y p
  rw [hcongr]
  cases hf : m.objs.find? (srcOKH sp P j y) with
  | none => rfl
  | some p =>
    simp only [Option.map_some, Option.bind_some]
    by_cases he : p.1 = m.root
    · have hp := List.mem_of_find?_eq_some hf
      have hpo : p.2 = oe := by
        have := lookup_of_mem m.objs hnd p hp
        rw [he] at this
        exact Option.some.inj (this.symm.trans hra)
      have hsrc := List.find?_some hf
      obtain ⟨a, b⟩ := p
      simp only at he hpo hsrc
      subst he hpo
      simp only [beq_self_eq_true, ↓reduceIte]
      exact (srcOKH_rootRel hReach hProot hPr hr hnode y _).2 hsrc
    · have : (p.1 == m.root) = false := by simp [he]
      simp only [this, Bool.false_eq_true, ↓reduceIte]

theorem canPtrH_withRoot (hra : m.obj? m.root = some oe) (hc : oc.canonical = oe.canonical)
    (hpos : oc.pos = oe.pos) (y : NodeId) : canPtrH (m.withRoot oc) y = canPtrH m y := by
  unfold canPtrH
  rw [HMem.withRoot_canonicalOf hra hc]
  cases m.canonicalOf y with
  | none => rfl
  | some b =>
    simp only [Option.map_some, HMem.withRoot_tableOf]
    by_cases hb : b = m.root
    · subst hb; rw [HMem.withRoot_obj?_root hra, hra]; simp [hpos]
    · rw [HMem.withRoot_obj?_ne hb]

theorem NSH_withRoot {f : Time} (hReach : ∀ x, reachable sp P' (j - 1) x = reachable sp P (j - 1) x)
    (hProot : (P'.get? root).map (fun n => sp.live (n.hist.upTo (j - 1))) =
      (P.get? root).map (fun n => sp.live (n.hist.upTo (j - 1))))
    (hPr : ∀ n, P.get? root = some n → ∀ y ∈ sp.live (n.hist.upTo (j - 1)),
      y ∈ pointees sp oc.hist ∧ y ∈ pointees sp oe.hist)
    (hnd : (m.objs.map (·.1)).Nodup) (hra : m.obj? m.root = some oe) (hr : RootRelH sp f oc oe)
    (hnode : oe.node = root) (y : NodeId) :
    NSH sp P' j (m.withRoot oc) y = NSH sp P j m y := by
  unfold NSH
  rw [canPtrH_withRoot hra hr.canonical hr.pos, srcPtrH_withRoot hReach hProot hPr hnd hra hr hnode]

theorem updObjH_congr {m1 m1' : HMem V} (hns : ∀ y, NSH sp P' j m1' y = NSH sp P j m1 y) (o : HObj V) (v : V) :
    updObjH sp P' j m1' o v = updObjH sp P j m1 o v := by
  unfold updObjH
  generalize ({ o with hist := o.hist ++ [⟨j, v⟩] } : HObj V) = o1
  induction (sp.ptrs v) generalizing o1 with
  | nil => rfl
  | cons y L ih =>
    simp only [List.foldl_cons]
    have : upd1H sp P' j m1' o1 y = upd1H sp P j m1 o1 y := by
      unfold upd1H
      rw [newPtr_eq, newPtr_eq, hns y]
    rw [this, ih]

theorem addNewH_withRoot (hne : m.nextObj ≠ m.root) (nn : NewNode) :
    addNewH (m.withRoot oc) nn = (addNewH m nn).withRoot oc := by
  unfold addNewH addNewH0 HMem.withRoot HMem.setHandle HMem.setTable
  have : (m.nextObj == m.root) = false := by simp [hne]
  simp only [List.map_cons, this, Bool.false_eq_true, ↓reduceIte]

theorem foldl_addNewH_withRoot (N : List NewNode) :
    ∀ (m : HMem V), m.root < m.nextObj → N.foldl addNewH (m.withRoot oc) = (N.foldl addNewH m).withRoot oc := by
  induction N with
  | nil => intro m _; rfl
  | cons nn N ih =>
    intro m hlt
    simp only [List.foldl_cons]
    rw [addNewH_withRoot (by omega)]
    exact ih _ (by show m.root < m.nextObj + 1; omega)

/-- A virtual root's new entry, for a new root child z, with the pointer to z's
object, the same in both. -/
theorem RootRelH.addRoot (hvl : VirtLiveOK sp) (hv : sp.virt = true) {f : Time} (hr : RootRelH sp f oc oe)
    (hvalsE : ∀ e ∈ oe.hist, ∃ z, e.val = sp.rootVal z) {e : Entry V} {z : NodeId}
    (hez : e.val = sp.rootVal z) (hptr : sp.ptrs (sp.rootVal z) = [z]) (p : HPtr) :
    RootRelH sp f ({ oc with hist := oc.hist ++ [e] }.putPtr z p) ({ oe with hist := oe.hist ++ [e] }.putPtr z p) := by
  have hcore : ∀ o : HObj V, (o.putPtr z p).core = o.core := fun o => HObj.putPtr_core o z p
  have hhist : ∀ o : HObj V, (o.putPtr z p).hist = o.hist := fun o => congrArg (fun c => c.2.2.2.1) (hcore o)
  have hnode : ∀ o : HObj V, (o.putPtr z p).node = o.node := fun o => congrArg (fun c => c.1) (hcore o)
  have hlevel : ∀ o : HObj V, (o.putPtr z p).level = o.level := fun o => congrArg (fun c => c.2.1) (hcore o)
  have hdata : ∀ o : HObj V, (o.putPtr z p).isData = o.isData := fun o => congrArg (fun c => c.2.2.1) (hcore o)
  have hcan : ∀ o : HObj V, (o.putPtr z p).canonical = o.canonical :=
    fun o => congrArg (fun c => c.2.2.2.2.1) (hcore o)
  have hpos : ∀ o : HObj V, (o.putPtr z p).pos = o.pos := fun o => congrArg (fun c => c.2.2.2.2.2) (hcore o)
  have hmem : ∀ y, y ∈ pointees sp (oc.hist ++ [e]) → y ∈ pointees sp oc.hist ∨ y = z := by
    intro y hy
    rcases pointees_append_mem hy with h | h
    · exact Or.inl h
    · rw [mem_pointees] at h
      obtain ⟨e', he', hy'⟩ := h
      rw [List.mem_singleton.mp he', hez, hptr] at hy'
      exact Or.inr (List.mem_singleton.mp hy')
  refine ⟨fun h => absurd h (by simp [hv]), by rw [hnode, hnode]; exact hr.node,
    by rw [hlevel, hlevel]; exact hr.level, by rw [hdata, hdata]; exact hr.isData,
    by rw [hcan, hcan]; exact hr.canonical, by rw [hpos, hpos]; exact hr.pos, ?_, ?_, ?_, ?_, ?_⟩
  · intro t ht
    rw [hhist, hhist]
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
    rw [hhist] at hy
    simp only at hy
    rw [HObj.ptr?_putPtr, HObj.ptr?_putPtr]
    split
    · rfl
    · rename_i hyz
      rcases hmem y hy with h | h
      · exact hr.ptrs y h
      · exact absurd h hyz
  · intro _ y hy
    rw [hhist] at hy
    simp only at hy
    rw [HObj.ptr?_putPtr]
    split
    · rename_i hyz
      subst hyz
      exact absurd (by rw [mem_pointees]; exact ⟨e, by simp, by rw [hez, hptr]; simp⟩) hy
    · have : y ∉ pointees sp oc.hist := fun h =>
        hy (by rw [mem_pointees] at h ⊢; obtain ⟨e', he', h'⟩ := h; exact ⟨e', by simp [he'], h'⟩)
      exact hr.noPtr hv y this
  · intro _ e' he'
    rw [hhist] at he'
    simp only at he'
    rcases List.mem_append.mp he' with h | h
    · exact hr.vals hv e' h
    · rw [List.mem_singleton.mp h]; exact ⟨z, hez⟩
  · intro _ y hy
    rw [hhist]
    simp only
    rw [HObj.ptr?_putPtr] at hy
    split at hy
    · rename_i hyz
      subst hyz
      rw [mem_pointees]; exact ⟨e, by simp, by rw [hez, hptr]; simp⟩
    · have := hr.keysE hv y hy
      rw [mem_pointees] at this ⊢
      obtain ⟨e', he', h'⟩ := this
      exact ⟨e', by simp [he'], h'⟩

/-- Without a virtual root, an object and itself. -/
theorem RootRelH.ofNV (hv : sp.virt = false) (f : Time) (o : HObj V) : RootRelH sp f o o :=
  ⟨fun _ => rfl, rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl, fun _ _ => rfl,
    fun h => absurd h (by simp [hv]), fun h => absurd h (by simp [hv]), fun h => absurd h (by simp [hv])⟩

/-- Setting an object as canonical as the old one keeps every node's canonical
object. -/
theorem HMem.canonicalOf_setObj_can {a : Nat} {o o' : HObj V} (ho : m.obj? a = some o)
    (hc : o'.canonical = o.canonical) (y : NodeId) : (m.setObj a o').canonicalOf y = m.canonicalOf y := by
  unfold HMem.canonicalOf HMem.tableOf HMem.objOf HMem.handle?
  simp only [HMem.setObj_table, HMem.setObj_handles]
  cases (m.table.lookup y).bind (fun n => (m.handles.lookup n).bind (·.obj)) with
  | none => rfl
  | some b =>
    simp only
    by_cases hb : b = a
    · subst hb
      rw [HMem.obj?_setObj_self, ho]
      simp [hc]
    · rw [HMem.obj?_setObj_ne _ _ hb]

/-- The change of a transaction on the memory with another root object, with a
structure P' that agrees with P on what is reachable at the last time and on
the root's live children then: the same, and the root objects change the same
way (with a virtual root, the root's new entries are for new root children). -/
theorem HMem.withRoot_applyChange {db : DB V T} {S0 : Stream V T} {k : Nat} (hvl : VirtLiveOK sp)
    (hinv : Inv sp db k) (hm : HEInv sp db S0 k m) {f : Time} {c : Changes V}
    (hstep : StepOK sp db.P (k + 1) c)
    (hReach : ∀ x, reachable sp P' (k + 1 - 1) x = reachable sp db.P (k + 1 - 1) x)
    (hProot : (P'.get? SIS.root).map (fun n => sp.live (n.hist.upTo (k + 1 - 1))) =
      (db.P.get? SIS.root).map (fun n => sp.live (n.hist.upTo (k + 1 - 1))))
    (hPr : ∀ n, db.P.get? SIS.root = some n → ∀ y ∈ sp.live (n.hist.upTo (k + 1 - 1)),
      y ∈ pointees sp oc.hist ∧ y ∈ pointees sp oe.hist)
    (hradds : sp.virt = true → ∀ a ∈ c.adds, a.1 = SIS.root → ∃ nn ∈ c.new, a.2 = sp.rootVal nn.id)
    (hptrs : sp.virt = true → ∀ z, sp.ptrs (sp.rootVal z) = [z])
    (hra : m.obj? m.root = some oe) (hr : RootRelH sp f oc oe)
    (hvalsE : sp.virt = true → ∀ e ∈ oe.hist, ∃ z, e.val = sp.rootVal z) :
    ∃ oc' oe', RootRelH sp f oc' oe' ∧ (m.applyChange sp db.P (k + 1) c).obj? m.root = some oe' ∧
      (sp.virt = true → ∀ e ∈ oe'.hist, ∃ z, e.val = sp.rootVal z) ∧
      (∃ X, oc'.hist = oc.hist ++ X ∧ oe'.hist = oe.hist ++ X) ∧
      (m.withRoot oc).applyChange sp P' (k + 1) c = (m.applyChange sp db.P (k + 1) c).withRoot oc' := by
  have haf := hm.addFactsH hinv hstep
  obtain ⟨o0, ho0, -, hn0⟩ := hm.root
  rw [hra, Option.some.injEq] at ho0
  subst ho0
  have hlt : m.root < m.nextObj := Nat.lt_of_not_le (fun hle => by rw [hm.freshO _ hle] at hra; cases hra)
  rw [applyChangeH_eq, applyChangeH_eq, foldl_addNewH_withRoot c.new m hlt]
  have hr1 : (c.new.foldl addNewH m).root = m.root := haf.root
  have hra1 : (c.new.foldl addNewH m).obj? m.root = some oe := by rw [haf.old _ hlt]; exact hra
  have hnd1 := haf.nodup
  have hns : ∀ y, NSH sp P' (k + 1) ((c.new.foldl addNewH m).withRoot oc) y =
      NSH sp db.P (k + 1) (c.new.foldl addNewH m) y :=
    NSH_withRoot hReach hProot hPr hnd1 (by rw [hr1]; exact hra1) hr hn0
  have htbl1 : ∀ y b, (c.new.foldl addNewH m).canonicalOf y = some b → b = m.root → y = SIS.root := by
    intro y b hc he
    obtain ⟨o, ho, hon, -⟩ := haf.tbl.canonicalOf_node hc
    rw [he, hra1, Option.some.injEq] at ho
    subst ho
    rw [← hon, hn0]
  have hcanNew : ∀ nn ∈ c.new, ∃ hn, (c.new.foldl addNewH m).canonicalOf nn.id = some hn := by
    intro nn hnn
    obtain ⟨a, n, -, -, -, hc, -⟩ := haf.canNew nn hnn
    exact ⟨a, hc⟩
  generalize hm1 : c.new.foldl addNewH m = m1 at hr1 hra1 hnd1 hns htbl1 hcanNew
  have key : ∀ (L : List (NodeId × V)), (∀ a ∈ L, a ∈ c.adds) →
      ∀ (ma : HMem V) (oc1 oe1 : HObj V), ma.obj? m.root = some oe1 → ma.root = m.root →
        (∀ y, ma.canonicalOf y = m1.canonicalOf y) →
        RootRelH sp f oc1 oe1 → oe1.node = SIS.root → (sp.virt = true → ∀ e ∈ oe1.hist, ∃ z, e.val = sp.rootVal z) →
        ∃ oc' oe', RootRelH sp f oc' oe' ∧ (L.foldl (addsStepH sp db.P (k + 1) m1) ma).obj? m.root = some oe' ∧
          (sp.virt = true → ∀ e ∈ oe'.hist, ∃ z, e.val = sp.rootVal z) ∧
          (∃ X, oc'.hist = oc1.hist ++ X ∧ oe'.hist = oe1.hist ++ X) ∧
          L.foldl (addsStepH sp P' (k + 1) (m1.withRoot oc)) (ma.withRoot oc1) =
            (L.foldl (addsStepH sp db.P (k + 1) m1) ma).withRoot oc' := by
    intro L
    induction L with
    | nil =>
      intro _ ma oc1 oe1 hra' _ _ hrr _ hv'
      exact ⟨oc1, oe1, hrr, hra', hv', ⟨[], by simp, by simp⟩, rfl⟩
    | cons a L ih =>
      intro hL ma oc1 oe1 hra' hrt' hcan hrr hn' hv'
      simp only [List.foldl_cons]
      have hra'' : ma.obj? ma.root = some oe1 := by rw [hrt']; exact hra'
      have hstep' : ∃ oc2 oe2, RootRelH sp f oc2 oe2 ∧ (addsStepH sp db.P (k + 1) m1 ma a).obj? m.root = some oe2 ∧
          (addsStepH sp db.P (k + 1) m1 ma a).root = m.root ∧
          (∀ y, (addsStepH sp db.P (k + 1) m1 ma a).canonicalOf y = m1.canonicalOf y) ∧
          oe2.node = SIS.root ∧ (sp.virt = true → ∀ e ∈ oe2.hist, ∃ z, e.val = sp.rootVal z) ∧
          (∃ X, oc2.hist = oc1.hist ++ X ∧ oe2.hist = oe1.hist ++ X) ∧
          addsStepH sp P' (k + 1) (m1.withRoot oc) (ma.withRoot oc1) a =
            (addsStepH sp db.P (k + 1) m1 ma a).withRoot oc2 := by
        unfold addsStepH
        rw [HMem.withRoot_canonicalOf hra'' hrr.canonical]
        cases hca : ma.canonicalOf a.1 with
        | none => exact ⟨oc1, oe1, hrr, hra', hrt', hcan, hn', hv', ⟨[], by simp, by simp⟩, rfl⟩
        | some h =>
          simp only
          by_cases hh : h = m.root
          · subst hh
            rw [← hrt', HMem.withRoot_obj?_root hra'', hra'']
            simp only
            rw [HMem.withRoot_setObj_root _ (updObjH sp db.P (k + 1) m1 oe1 a.2), updObjH_congr hns]
            have hroot' : (ma.setObj ma.root (updObjH sp db.P (k + 1) m1 oe1 a.2)).obj? ma.root =
                some (updObjH sp db.P (k + 1) m1 oe1 a.2) := HMem.obj?_setObj_self _ _ _
            obtain ⟨u1, -, -, u4, u5, -⟩ := updObjH_core sp db.P (k + 1) m1 oe1 a.2
            have hcan' : ∀ y, (ma.setObj ma.root (updObjH sp db.P (k + 1) m1 oe1 a.2)).canonicalOf y =
                m1.canonicalOf y := by
              intro y
              rw [HMem.canonicalOf_setObj_can hra'' u5, hcan]
            cases hv : sp.virt with
            | false =>
              rw [hrr.nv hv]
              exact ⟨_, _, RootRelH.ofNV hv f _, hroot', by rw [HMem.setObj_root, hrt'],
                hcan', by rw [u1, hn'], fun h => absurd h (by simp), ⟨[⟨k + 1, a.2⟩], u4, u4⟩, rfl⟩
            | true =>
              have ha1 : a.1 = SIS.root := htbl1 a.1 m.root (by rw [← hcan]; exact hca) rfl
              obtain ⟨nn, hnn, ha2⟩ := hradds hv a (hL a List.mem_cons_self) ha1
              obtain ⟨hn, hcn⟩ := hcanNew nn hnn
              have hpz := hptrs hv nn.id
              have hupd : ∀ o : HObj V, updObjH sp db.P (k + 1) m1 o a.2 =
                  ({ o with hist := o.hist ++ [⟨k + 1, a.2⟩] } : HObj V).putPtr nn.id
                    { ref := (m1.obj? hn).bind (·.pos), handle := m1.tableOf nn.id } := by
                intro o
                unfold updObjH
                rw [ha2, hpz]
                simp only [List.foldl_cons, List.foldl_nil]
                unfold upd1H
                rw [newPtr_eq]
                unfold NSH canPtrH
                rw [hcn]
                rfl
              rw [hupd oc1, hupd oe1]
              rw [hupd oe1] at hroot' u1 u4
              have hrr2 := hrr.addRoot hvl hv (hv' hv) (e := ⟨k + 1, a.2⟩) (z := nn.id) ha2 hpz
                { ref := (m1.obj? hn).bind (·.pos), handle := m1.tableOf nn.id }
              refine ⟨_, _, hrr2, hroot', by rw [HMem.setObj_root, hrt'], ?_,
                by rw [u1]; exact hn', ?_, ⟨[⟨k + 1, a.2⟩], ?_, u4⟩, rfl⟩
              · intro y
                rw [HMem.canonicalOf_setObj_can hra'' (by rw [← hupd oe1]; exact u5), hcan]
              · intro _ e he
                rw [u4] at he
                rcases List.mem_append.mp he with h1 | h1
                · exact hv' hv e h1
                · rw [List.mem_singleton.mp h1]; exact ⟨nn.id, ha2⟩
              · have := HObj.putPtr_core ({ oc1 with hist := oc1.hist ++ [⟨k + 1, a.2⟩] } : HObj V) nn.id
                  { ref := (m1.obj? hn).bind (·.pos), handle := m1.tableOf nn.id }
                exact congrArg (fun c => c.2.2.2.1) this
          · have hh' : h ≠ ma.root := by rw [hrt']; exact hh
            rw [HMem.withRoot_obj?_ne hh']
            cases hoh : ma.obj? h with
            | none => exact ⟨oc1, oe1, hrr, hra', hrt', hcan, hn', hv', ⟨[], by simp, by simp⟩, rfl⟩
            | some o =>
              simp only
              rw [updObjH_congr hns, HMem.withRoot_setObj_ne hh']
              obtain ⟨-, -, -, -, u5, -⟩ := updObjH_core sp db.P (k + 1) m1 o a.2
              refine ⟨oc1, oe1, hrr, ?_, by rw [HMem.setObj_root, hrt'], fun y => ?_, hn', hv',
                ⟨[], by simp, by simp⟩, rfl⟩
              · rw [HMem.obj?_setObj_ne _ _ (fun he => hh he.symm)]
                exact hra'
              · rw [HMem.canonicalOf_setObj_can hoh u5, hcan]
      obtain ⟨oc2, oe2, hrr2, hra2, hrt2, hcan2, hn2, hv2, ⟨X1, hx1, hx1'⟩, he2⟩ := hstep'
      rw [he2]
      obtain ⟨oc3, oe3, h1, h2, h3, ⟨X2, hx2, hx2'⟩, h4⟩ :=
        ih (fun b hb => hL b (List.mem_cons_of_mem _ hb)) _ oc2 oe2 hra2 hrt2 hcan2 hrr2 hn2 hv2
      exact ⟨oc3, oe3, h1, h2, h3, ⟨X1 ++ X2, by rw [hx2, hx1, List.append_assoc],
        by rw [hx2', hx1', List.append_assoc]⟩, h4⟩
  exact key c.adds (fun a ha => ha) m1 oc oe hra1 hr1 (fun _ => rfl) hr hn0 hvalsE

end ChangeSim

end SIS
