/-
Proofs about the physical layer with handles (bergdb item 009, step 2d), part 8:
the physical writer's loop writes the model's versions (`HMem.writeNodes` against
`writeAll`), given, for each node it writes, its canonical object with the
node's whole history; the positions of the canonical objects at the latest
versions so far; and for each pointee that is not pinned, a pointer that holds
its live handle with its canonical object, or whose record is its latest
version, as SIS/Proof/EvictWrite.lean shows for Evict.lean. And what the loop
changes: the positions of the objects it writes, and their pointers as
`resolvePointers` leaves them.
-/
import SIS.Proof.HandleApplyInv

set_option linter.unusedSectionVars false

namespace SIS

variable {V T : Type} [DecidableEq V]

/-! ## One object changed, its flag kept -/

theorem HMem.canonicalOf_setObj_flag {m : HMem V} {a : Nat} {o o' : HObj V} (ho : m.obj? a = some o)
    (hc : o'.canonical = o.canonical) (y : NodeId) : (m.setObj a o').canonicalOf y = m.canonicalOf y := by
  apply HMem.canonicalOf_congr (fun y => HMem.tableOf_setObj m a o' y) (fun n => HMem.handle?_setObj m a o' n)
  intro b
  rw [HMem.obj?_setObj]
  split
  · rename_i h; subst h; rw [ho]; simp [hc]
  · rfl

theorem HMem.holdsCanonical_setObj_flag {m : HMem V} {a : Nat} {o o' : HObj V} (ho : m.obj? a = some o)
    (hc : o'.canonical = o.canonical) (p : HPtr) : (m.setObj a o').holdsCanonical p = m.holdsCanonical p := by
  unfold HMem.holdsCanonical
  rw [HMem.objOf_setObj_fun]
  cases p.handle.bind m.objOf with
  | none => rfl
  | some b =>
    simp only [Option.bind_some]
    rw [HMem.obj?_setObj]
    by_cases hba : b = a
    · subst hba; simp [ho, hc]
    · simp only [hba, ↓reduceIte]

/-- The table and the handles after an object is replaced by one of the same
node, whose pointers hold handles of their pointees. -/
theorem HTableOK.setObj {m : HMem V} (ht : HTableOK m) {a : Nat} {o o' : HObj V} (ho : m.obj? a = some o)
    (hn : o'.node = o.node)
    (hp : ∀ y q n, o'.ptr? y = some q → q.handle = some n → ∃ hd, m.handle? n = some hd ∧ hd.node = y) :
    HTableOK (m.setObj a o') := by
  have hobj : ∀ x, (m.setObj a o').obj? x = if x = a then some o' else m.obj? x :=
    fun x => HMem.obj?_setObj m a x o'
  refine ⟨?_, ht.nodup, fun n hd hh hl => ht.liveIn hh hl, fun n hd hh hdd => ht.deadNone hh hdd, ?_, ?_⟩
  · intro y n hy
    obtain ⟨hd, b, ob, hh, hl, hny, hb, hob, hon⟩ := ht.entry hy
    by_cases hba : b = a
    · subst hba
      rw [ho, Option.some.injEq] at hob
      subst hob
      exact ⟨hd, b, o', hh, hl, hny, hb, by rw [hobj]; simp, by rw [hn]; exact hon⟩
    · exact ⟨hd, b, ob, hh, hl, hny, hb, by rw [hobj]; simp [hba]; exact hob, hon⟩
  · intro x ox hx
    rw [hobj] at hx
    split at hx
    · rename_i hxa
      simp only [Option.some.injEq] at hx
      subst hx
      obtain ⟨n, htn, hob⟩ := ht.held ho
      exact ⟨n, by rw [HMem.tableOf_setObj, hn]; exact htn, by rw [hxa]; exact hob⟩
    · exact ht.held hx
  · intro x ox y q n hx hq hqn
    rw [hobj] at hx
    split at hx
    · simp only [Option.some.injEq] at hx; subst hx; exact hp y q n hq hqn
    · exact ht.ptrNode hx hq hqn

/-- The record rule after an object is replaced, for a pointer whose handle does
not hold it. -/
theorem HMem.ptrRef_setObj_other {m : HMem V} (S0 : Stream V T) {a : Nat} (o' : HObj V) {p : HPtr}
    (h : ∀ hd, p.handle.bind m.handle? = some hd → hd.obj ≠ some a) (y : NodeId) :
    (m.setObj a o').ptrRef S0 y p = m.ptrRef S0 y p := by
  apply HMem.ptrRef_congr S0 (HMem.setObj_s m a o') (by rfl)
  intro hd b hph hb
  rw [HMem.obj?_setObj]
  have hba : b ≠ a := by intro he; subst he; exact h hd hph hb
  simp only [hba, ↓reduceIte]

/-- The record rule for a pointer that holds y's live handle, with y's canonical
object: that object's position. -/
theorem HMem.ptrRef_of_holdsLive {m : HMem V} (S0 : Stream V T) {y : NodeId} {p : HPtr}
    (h : m.HoldsLive y p) :
    ∃ b o, m.canonicalOf y = some b ∧ m.obj? b = some o ∧ o.canonical = true ∧ m.ptrRef S0 y p = o.pos := by
  obtain ⟨n, hpn, htn, hcs⟩ := h
  obtain ⟨b, hcb⟩ := Option.isSome_iff_exists.mp hcs
  obtain ⟨n', o, htn', hob, ho, hc⟩ := (m.canonicalOf_eq_some y b).mp hcb
  rw [htn, Option.some.injEq] at htn'
  subst htn'
  refine ⟨b, o, hcb, ho, hc, ?_⟩
  unfold HMem.objOf at hob
  unfold HMem.ptrRef
  cases hh : m.handle? n with
  | none => rw [hh] at hob; cases hob
  | some hd =>
    rw [hh] at hob
    simp only [Option.bind_some] at hob
    simp only [hpn, Option.bind_some, hh, hob, ho, hc, ↓reduceIte]

/-- A pointer that holds y's live handle with y's canonical object holds a
canonical object. -/
theorem HMem.holdsCanonical_of_holdsLive {m : HMem V} {y : NodeId} {p : HPtr} (h : m.HoldsLive y p) :
    m.holdsCanonical p = true := by
  obtain ⟨n, hpn, htn, hcs⟩ := h
  obtain ⟨b, hcb⟩ := Option.isSome_iff_exists.mp hcs
  obtain ⟨n', o, htn', hob, ho, hc⟩ := (m.canonicalOf_eq_some y b).mp hcb
  rw [htn, Option.some.injEq] at htn'
  subst htn'
  unfold HMem.holdsCanonical
  simp only [hpn, Option.bind_some, hob, ho, hc]

/-! ## The pointers of a written object -/

/-- What `resolvePointers` makes of pointer q to z of the object written
(`HMem.writeNode`): q itself if its handle holds a canonical object; for a
pinned z with a canonical object, z's live handle, by node id; else q with its
reference after Rule R. -/
def HMem.resolveP (S0 : Stream V T) (m : HMem V) (D : Dirty) (z : NodeId) (q : HPtr) : HPtr :=
  if m.holdsCanonical q then q
  else if inD D z && (m.canonicalOf z).isSome then { q with handle := m.tableOf z }
  else { q with ref := ruleRRef S0 m.s z q.ref }

/-- `resolvePointers` on one pair of the object written, word for word as in
`HMem.writeNode`. -/
def HMem.resolvePtr (S0 : Stream V T) (m : HMem V) (D : Dirty) (q : NodeId × HPtr) : NodeId × HPtr :=
  if m.holdsCanonical q.2 then q
  else if inD D q.1 && (m.canonicalOf q.1).isSome then (q.1, { q.2 with handle := m.tableOf q.1 })
  else (q.1, { q.2 with ref := ruleRRef S0 m.s q.1 q.2.ref })

theorem HMem.resolvePtr_eq (S0 : Stream V T) (m : HMem V) (D : Dirty) (q : NodeId × HPtr) :
    m.resolvePtr S0 D q = (q.1, m.resolveP S0 D q.1 q.2) := by
  unfold HMem.resolvePtr HMem.resolveP
  by_cases h1 : m.holdsCanonical q.2 = true
  · simp [h1]
  · by_cases h2 : (inD D q.1 && (m.canonicalOf q.1).isSome) = true
    · simp [h1, h2]
    · simp [h1, h2]

/-- The pointer of the object written, for z. -/
theorem HMem.ptr?_resolve (S0 : Stream V T) (m : HMem V) (D : Dirty) (ps : List (NodeId × HPtr)) (z : NodeId) :
    (ps.map (m.resolvePtr S0 D)).lookup z = (ps.lookup z).map (m.resolveP S0 D z) := by
  have h : ps.map (m.resolvePtr S0 D) = ps.map (fun q => (q.1, m.resolveP S0 D q.1 q.2)) := by
    apply List.map_congr_left
    intro q _
    exact HMem.resolvePtr_eq S0 m D q
  rw [h]
  exact lookup_map_val (m.resolveP S0 D) ps z

/-- What `resolvePointers` makes of a pointer, case by case. -/
theorem HMem.resolveP_cases (S0 : Stream V T) (m : HMem V) (D : Dirty) (z : NodeId) (q : HPtr) :
    (m.holdsCanonical q = true ∧ m.resolveP S0 D z q = q) ∨
    (m.holdsCanonical q = false ∧ inD D z = true ∧ (m.canonicalOf z).isSome = true ∧
      m.resolveP S0 D z q = { q with handle := m.tableOf z }) ∨
    (m.holdsCanonical q = false ∧ ¬ (inD D z = true ∧ (m.canonicalOf z).isSome = true) ∧
      m.resolveP S0 D z q = { q with ref := ruleRRef S0 m.s z q.ref }) := by
  unfold HMem.resolveP
  by_cases h1 : m.holdsCanonical q = true
  · left; exact ⟨h1, by simp [h1]⟩
  · have h1' : m.holdsCanonical q = false := by simpa using h1
    by_cases h2 : inD D z = true ∧ (m.canonicalOf z).isSome = true
    · right; left
      exact ⟨h1', h2.1, h2.2, by simp [h1', h2.1, h2.2]⟩
    · right; right
      refine ⟨h1', h2, ?_⟩
      have h3 : (inD D z && (m.canonicalOf z).isSome) = false := by
        cases h4 : inD D z
        · rfl
        · cases h5 : (m.canonicalOf z).isSome
          · rfl
          · exact absurd ⟨h4, h5⟩ h2
      simp [h1', h3]

/-- A pointer's reference raised by Rule R gives the same record (Rule R applied
twice gives what it gives once). -/
theorem HMem.ptrRef_ruleR (S0 : Stream V T) (m : HMem V) (z : NodeId) (q : HPtr) :
    m.ptrRef S0 z { q with ref := ruleRRef S0 m.s z q.ref } = m.ptrRef S0 z q := by
  unfold HMem.ptrRef
  simp only [ruleRRef_idem]

/-! ## Writing nodes -/

/-- The canonical objects' positions are the latest versions so far: in the
stream S followed by the versions vs of the record being written. -/
def HPosOK (S : Stream V T) (vs : List (Version V)) (m : HMem V) : Prop :=
  ∀ a o, m.obj? a = some o → o.canonical = true → o.pos = ((S.building vs).lv o.node).map (·.recNo)

/-- What the writer needs of node x: a canonical object with the node's whole
history, level and kind; and for each pointee that is not pinned, a pointer
that holds its live handle with its canonical object, or whose record is its
latest version in S, of a node the record does not write. -/
def HWriteOK (sp : Spec V T) (S0 S : Stream V T) (P : Struct V) (D : Dirty) (wr : List NodeId)
    (m : HMem V) (x : NodeId) : Prop :=
  ∃ a o n, m.canonicalOf x = some a ∧ m.obj? a = some o ∧ P.get? x = some n ∧
    o.node = x ∧ o.hist = n.hist ∧ o.level = n.level ∧ o.isData = n.isData ∧
    ∀ y ∈ pointees sp n.hist, inD D y = false → ∃ p, o.ptr? y = some p ∧
      (m.HoldsLive y p ∨ (m.ptrRef S0 y p = (S.lv y).map (·.recNo) ∧ y ∉ wr))

/-- The version that `HMem.writeNode` writes for node x from object o. -/
def HMem.verOf (sp : Spec V T) (S0 : Stream V T) (m : HMem V) (D : Dirty) (i : Nat) (x : NodeId)
    (o : HObj V) : Version V :=
  { node := x, recNo := i, level := o.level, isData := o.isData, hist := o.hist,
    refs := (pointees sp o.hist).filterMap (fun y => (m.refOf S0 D o y).map (fun r => (y, r))) }

section

variable (sp : Spec V T) (S0 S : Stream V T) (P : Struct V) (D : Dirty) (i : Nat)

/-- Writing node x changes only x's canonical object. -/
theorem HMem.writeNode_shape {m : HMem V} {x : NodeId} {a : Nat} {o : HObj V}
    (hc : m.canonicalOf x = some a) (ho : m.obj? a = some o) :
    m.writeNode sp S0 D i x =
      (m.setObj a { o with pos := some i, ptrs := o.ptrs.map (m.resolvePtr S0 D) },
        some (m.verOf sp S0 D i x o)) := by
  unfold HMem.writeNode
  rw [hc]
  simp only [ho]
  rfl

/-- The loop of `writeNodes` from an accumulator. -/
def hwnStep (acc : HMem V × List (Version V)) (x : NodeId) : HMem V × List (Version V) :=
  match acc.1.writeNode sp S0 D i x with
  | (m', some v) => (m', acc.2 ++ [v])
  | (m', none) => (m', acc.2)

theorem writeNodesH_eq_foldl (m : HMem V) (xs : List NodeId) :
    m.writeNodes sp S0 D i xs = xs.foldl (hwnStep sp S0 D i) (m, []) := rfl

theorem hwnStep_some {m : HMem V} {L : List (Version V)} {x : NodeId} {m' : HMem V} {v : Version V}
    (hw : m.writeNode sp S0 D i x = (m', some v)) : hwnStep sp S0 D i (m, L) x = (m', L ++ [v]) := by
  simp [hwnStep, hw]

theorem hwnStep_none {m : HMem V} {L : List (Version V)} {x : NodeId} {m' : HMem V}
    (hw : m.writeNode sp S0 D i x = (m', none)) : hwnStep sp S0 D i (m, L) x = (m', L) := by
  simp [hwnStep, hw]

theorem foldl_hwnStep_prefix :
    ∀ (xs : List NodeId) (m : HMem V) (L : List (Version V)),
      xs.foldl (hwnStep sp S0 D i) (m, L) =
        ((xs.foldl (hwnStep sp S0 D i) (m, [])).1, L ++ (xs.foldl (hwnStep sp S0 D i) (m, [])).2) := by
  intro xs
  induction xs with
  | nil => intro m L; simp
  | cons x xs ih =>
    intro m L
    simp only [List.foldl_cons]
    cases hw : m.writeNode sp S0 D i x with
    | mk m' ov =>
      cases ov with
      | none =>
        rw [hwnStep_none sp S0 D i hw, hwnStep_none sp S0 D i hw]
        exact ih m' L
      | some v =>
        rw [hwnStep_some sp S0 D i hw, hwnStep_some sp S0 D i hw, ih m' (L ++ [v]), ih m' ([] ++ [v])]
        simp

/-- The pointers of the written object hold handles of their pointees. -/
theorem HTableOK.resolve_node {m : HMem V} (ht : HTableOK m) {a : Nat} {o : HObj V}
    (ho : m.obj? a = some o) :
    ∀ y q n, ({ o with pos := some i, ptrs := o.ptrs.map (m.resolvePtr S0 D) } : HObj V).ptr? y = some q →
      q.handle = some n → ∃ hd, m.handle? n = some hd ∧ hd.node = y := by
  intro y q n hq hqn
  have hq' : (o.ptr? y).map (m.resolveP S0 D y) = some q := by
    have h1 : ({ o with pos := some i, ptrs := o.ptrs.map (m.resolvePtr S0 D) } : HObj V).ptr? y =
        (o.ptr? y).map (m.resolveP S0 D y) := HMem.ptr?_resolve S0 m D o.ptrs y
    rw [← h1]; exact hq
  cases hy : o.ptr? y with
  | none => rw [hy] at hq'; cases hq'
  | some q0 =>
    rw [hy] at hq'
    simp only [Option.map_some, Option.some.injEq] at hq'
    subst hq'
    rcases HMem.resolveP_cases S0 m D y q0 with ⟨-, h⟩ | ⟨-, -, -, h⟩ | ⟨-, -, h⟩
    · rw [h] at hqn; exact ht.ptrNode ho hy hqn
    · rw [h] at hqn
      simp only at hqn
      obtain ⟨hd, -, -, hh, -, hny, -⟩ := ht.entry hqn
      exact ⟨hd, hh, hny⟩
    · rw [h] at hqn; exact ht.ptrNode ho hy hqn

/-- The physical writer's loop writes the model's versions. -/
theorem writeNodesH_eq :
    ∀ (xs : List NodeId) (acc : List (Version V)) (m : HMem V) (wr : List NodeId),
      HTableOK m →
      (∀ y, inD D y = true → (m.canonicalOf y).isSome) →
      HPosOK S acc m →
      (∀ x ∈ xs, HWriteOK sp S0 S P D wr m x) →
      (∀ v ∈ acc, v.node ∈ wr) → (∀ x ∈ xs, x ∈ wr) →
      xs.Nodup → (∀ x ∈ xs, ∀ v ∈ acc, v.node ≠ x) →
      acc ++ (m.writeNodes sp S0 D i xs).2 = writeAll sp S i P xs acc ∧
        HPosOK S (writeAll sp S i P xs acc) (m.writeNodes sp S0 D i xs).1 ∧
        HTableOK (m.writeNodes sp S0 D i xs).1 ∧
        (∀ y, (m.writeNodes sp S0 D i xs).1.canonicalOf y = m.canonicalOf y) := by
  intro xs
  induction xs with
  | nil =>
    intro acc m wr htb _ hpos _ _ _ _ _
    exact ⟨by simp [writeNodesH_eq_foldl, writeAll], by simpa [writeNodesH_eq_foldl, writeAll] using hpos,
      by simpa [writeNodesH_eq_foldl] using htb, fun _ => rfl⟩
  | cons x xs ih =>
    intro acc m wr htb hD hpos hok hacc hwr hnd hfresh
    obtain ⟨a, o, n, hc, ho, hn, hnode, hhist, hlev, hdat, hptrs⟩ := hok x List.mem_cons_self
    have hcan : o.canonical = true := by
      obtain ⟨-, o2, -, -, ho2, hc2⟩ := (m.canonicalOf_eq_some x a).mp hc
      rw [ho] at ho2; cases ho2; exact hc2
    -- The references of x's version are the latest versions so far.
    have href : ∀ y ∈ pointees sp o.hist,
        m.refOf S0 D o y = ((S.building acc).lv y).map (·.recNo) := by
      intro y hy
      unfold HMem.refOf
      rw [hhist] at hy
      by_cases hyD : inD D y = true
      · simp only [hyD, ↓reduceIte]
        obtain ⟨b, hcy⟩ := Option.isSome_iff_exists.mp (hD y hyD)
        rw [hcy]
        obtain ⟨oy, hoy, hnoy, hcoy⟩ := htb.canonicalOf_node hcy
        simp only [hoy, Option.bind_some]
        rw [hpos b oy hoy hcoy, hnoy]
      · simp only [hyD, Bool.false_eq_true, ↓reduceIte]
        have hyD' : inD D y = false := by simpa using hyD
        obtain ⟨p, hp, hcase⟩ := hptrs y hy hyD'
        rw [hp]
        simp only [Option.bind_some]
        rcases hcase with hhl | ⟨hser, hywr⟩
        · obtain ⟨b, ob, hcb, hob, hcob, hpr⟩ := HMem.ptrRef_of_holdsLive S0 hhl
          rw [hpr]
          obtain ⟨ob', hob', hnob', -⟩ := htb.canonicalOf_node hcb
          rw [hob, Option.some.injEq] at hob'
          subst hob'
          rw [hpos b ob hob hcob, hnob']
        · rw [hser, lv_building]
          have : acc.find? (fun v => v.node == y) = none := by
            rw [List.find?_eq_none]
            intro v hv hvy
            apply hywr
            have h1 := hacc v hv
            have h2 : v.node = y := by simpa using hvy
            rw [← h2]; exact h1
          rw [this, Option.none_or]
    -- x's version is mkVersion's.
    have hvx : m.verOf sp S0 D i x o = mkVersion sp (S.building acc) i x n := by
      unfold mkVersion HMem.verOf
      rw [hlev, hdat, hhist]
      congr 1
      apply filterMap_congr_mem
      intro y hy
      rw [href y (by rw [hhist]; exact hy), Option.map_map]
      rfl
    obtain ⟨o', ho'⟩ : ∃ o', o' = { o with pos := some i, ptrs := o.ptrs.map (m.resolvePtr S0 D) } :=
      ⟨_, rfl⟩
    have hw := HMem.writeNode_shape sp S0 D i hc ho
    rw [← ho', hvx] at hw
    have hco' : o'.canonical = o.canonical := by rw [ho']
    have hcan1 : ∀ y, (m.setObj a o').canonicalOf y = m.canonicalOf y :=
      HMem.canonicalOf_setObj_flag ho hco'
    -- The loop: x's version, then the rest from m.setObj a o'.
    have hloop : m.writeNodes sp S0 D i (x :: xs) =
        (((m.setObj a o').writeNodes sp S0 D i xs).1,
          mkVersion sp (S.building acc) i x n :: ((m.setObj a o').writeNodes sp S0 D i xs).2) := by
      rw [writeNodesH_eq_foldl, List.foldl_cons, hwnStep_some sp S0 D i hw, foldl_hwnStep_prefix,
        ← writeNodesH_eq_foldl]
      rfl
    have hwa : writeAll sp S i P (x :: xs) acc =
        writeAll sp S i P xs (acc ++ [mkVersion sp (S.building acc) i x n]) := by
      rw [writeAll_cons]; simp only [hn]
    -- The facts for m.setObj a o' and acc ++ [x's version].
    have hxacc : ∀ v ∈ acc, v.node ≠ x := hfresh x List.mem_cons_self
    have hlvx : (S.building (acc ++ [mkVersion sp (S.building acc) i x n])).lv x =
        some (mkVersion sp (S.building acc) i x n) := by
      rw [lv_building]
      have h1 : acc.find? (fun v => v.node == x) = none := by
        rw [List.find?_eq_none]
        intro v hv hvx'
        exact hxacc v hv (by simpa using hvx')
      rw [List.find?_append, h1, Option.none_or]
      simp [mkVersion]
    have hpos1 : HPosOK S (acc ++ [mkVersion sp (S.building acc) i x n]) (m.setObj a o') := by
      intro b ob hob hcb
      rw [HMem.obj?_setObj] at hob
      split at hob
      · simp only [Option.some.injEq] at hob
        subst hob
        rw [ho']
        simp only
        rw [hnode, hlvx]
        simp [mkVersion]
      · rename_i hba
        have hcb' : ob.canonical = true := hcb
        rw [hpos b ob hob hcb', lv_building, lv_building, List.find?_append]
        have hzx : ob.node ≠ x := by
          intro hzx
          have h1 := htb.canonicalOf_of hob hcb'
          rw [hzx, hc, Option.some.injEq] at h1
          exact hba h1.symm
        have : [mkVersion sp (S.building acc) i x n].find? (fun v => v.node == ob.node) = none := by
          simp [mkVersion, Ne.symm hzx]
        rw [this, Option.or_none]
    have htb1 : HTableOK (m.setObj a o') := by
      apply htb.setObj ho (by rw [ho'])
      intro y q n' hq hqn
      rw [ho'] at hq
      exact htb.resolve_node S0 D i ho y q n' hq hqn
    have hD1 : ∀ y, inD D y = true → ((m.setObj a o').canonicalOf y).isSome := by
      intro y hy; rw [hcan1]; exact hD y hy
    have hxs : x ∉ xs := (List.nodup_cons.mp hnd).1
    have hok1 : ∀ x' ∈ xs, HWriteOK sp S0 S P D wr (m.setObj a o') x' := by
      intro x' hx'
      obtain ⟨a2, o2, n2, hc2, ho2, hn2, hnode2, hhist2, hlev2, hdat2, hptrs2⟩ :=
        hok x' (List.mem_cons_of_mem x hx')
      have hne : a2 ≠ a := by
        intro hh; subst hh
        rw [ho] at ho2; cases ho2
        have hxx : x = x' := by rw [← hnode, hnode2]
        exact hxs (hxx ▸ hx')
      refine ⟨a2, o2, n2, by rw [hcan1]; exact hc2, by rw [HMem.obj?_setObj_ne _ _ hne]; exact ho2,
        hn2, hnode2, hhist2, hlev2, hdat2, ?_⟩
      intro y hy hyD
      obtain ⟨p, hp, hcase⟩ := hptrs2 y hy hyD
      refine ⟨p, hp, ?_⟩
      rcases hcase with hhl | ⟨hser, hywr⟩
      · left
        obtain ⟨n0, h1, h2, h3⟩ := hhl
        exact ⟨n0, h1, by rw [HMem.tableOf_setObj]; exact h2, by rw [hcan1]; exact h3⟩
      · right
        refine ⟨?_, hywr⟩
        rw [← hser]
        apply HMem.ptrRef_setObj_other S0 o'
        -- p's handle, of node y, does not hold x's object: y is not written in this record
        intro hd hph hb
        cases hpn : p.handle with
        | none => rw [hpn] at hph; cases hph
        | some n0 =>
          rw [hpn] at hph
          simp only [Option.bind_some] at hph
          obtain ⟨hd', hh', hy'⟩ := htb.ptrNode ho2 hp hpn
          rw [hph, Option.some.injEq] at hh'
          subst hh'
          obtain ⟨-, oa, hoa, hona⟩ := htb.obj_of_handle hph hb
          rw [ho, Option.some.injEq] at hoa
          subst hoa
          exact hywr (by rw [← hy', ← hona, hnode]; exact hwr x List.mem_cons_self)
    have hacc1 : ∀ v ∈ acc ++ [mkVersion sp (S.building acc) i x n], v.node ∈ wr := by
      intro v hv
      rcases List.mem_append.mp hv with hv | hv
      · exact hacc v hv
      · rw [List.mem_singleton] at hv
        subst hv
        simp only [mkVersion]
        exact hwr x List.mem_cons_self
    have hfresh1 : ∀ x' ∈ xs, ∀ v ∈ acc ++ [mkVersion sp (S.building acc) i x n], v.node ≠ x' := by
      intro x' hx' v hv
      rcases List.mem_append.mp hv with hv | hv
      · exact hfresh x' (List.mem_cons_of_mem x hx') v hv
      · rw [List.mem_singleton] at hv
        subst hv
        simp only [mkVersion]
        intro hh; subst hh; exact hxs hx'
    obtain ⟨h1, h2, h3, h4⟩ := ih (acc ++ [mkVersion sp (S.building acc) i x n]) (m.setObj a o') wr
      htb1 hD1 hpos1 hok1 hacc1 (fun x' hx' => hwr x' (List.mem_cons_of_mem x hx'))
      (List.nodup_cons.mp hnd).2 hfresh1
    rw [hloop, hwa]
    refine ⟨?_, h2, h3, fun y => by rw [h4 y, hcan1]⟩
    rw [← h1]
    simp

end

end SIS
