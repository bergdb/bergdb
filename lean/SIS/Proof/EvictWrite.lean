/-
Proofs for stage 2 (bergdb item 001, WP E3), part 2: the physical writer's loop
writes the model's versions (`Mem.writeNodes` against `writeAll`), given, for
each node it writes, its canonical object with the node's whole history; the
positions of the canonical objects at the latest versions so far; and slots that
serialize the latest versions of the pointees that are not pinned.
-/
import SIS.Proof.EvictLogic
import SIS.Proof.PhysMem
import SIS.Proof.VRead

set_option linter.unusedSectionVars false

namespace SIS

variable {V T : Type} [DecidableEq V]

/-- The canonical objects' positions are the latest versions so far: in the
stream S followed by the versions vs of the record being written. -/
def PosOK (S : Stream V T) (vs : List (Version V)) (m : Mem V) : Prop :=
  ∀ z h o, m.canonicalOf z = some h → m.obj? h = some o →
    o.pos = ((S.building vs).lv z).map (·.recNo)

/-- The node table names objects of their node. -/
def TableNode (m : Mem V) : Prop :=
  ∀ y h, m.tableOf y = some h → ∃ o, m.obj? h = some o ∧ o.node = y

/-- A memory slot for y names an object of node y. -/
def SlotsNode (m : Mem V) : Prop :=
  ∀ h o, m.obj? h = some o → ∀ y h', o.slot? y = some (Slot.mem h') →
    ∃ o', m.obj? h' = some o' ∧ o'.node = y

/-- The reference that a slot of object o for y serializes (a stream slot's
after Rule R). -/
def Mem.slotRef (S0 : Stream V T) (m : Mem V) (o : Obj V) (y : NodeId) : Option Nat :=
  match o.slot? y with
  | some (Slot.mem h) => (m.obj? h).bind (·.pos)
  | some (Slot.stream r) => ruleRRef S0 m.s y r
  | none => none

/-- What the writer needs of node x: a canonical object with the node's whole
history, level and kind; and for each pointee that is not pinned, a memory slot
to its canonical object, or a slot that serializes its latest version in S, of
a node the record does not write. -/
def WriteOK (sp : Spec V T) (S0 S : Stream V T) (P : Struct V) (D : Dirty) (wr : List NodeId)
    (m : Mem V) (x : NodeId) : Prop :=
  ∃ h o n, m.canonicalOf x = some h ∧ m.obj? h = some o ∧ P.get? x = some n ∧
    o.node = x ∧ o.hist = n.hist ∧ o.level = n.level ∧ o.isData = n.isData ∧
    ∀ y ∈ pointees sp n.hist, inD D y = false →
      (∃ h', o.slot? y = some (Slot.mem h') ∧ m.canonicalOf y = some h') ∨
      (m.slotRef S0 o y = (S.lv y).map (·.recNo) ∧ y ∉ wr)

theorem Mem.refOf_eq (S0 : Stream V T) (m : Mem V) (D : Dirty) (o : Obj V) (y : NodeId) :
    m.refOf S0 D o y = if inD D y then
      (match m.canonicalOf y with
       | some h => (m.obj? h).bind (·.pos)
       | none => m.slotRef S0 o y)
    else m.slotRef S0 o y := rfl

theorem canonicalOf_setObj_same {m : Mem V} {h : Nat} {o o' : Obj V} (ho : m.obj? h = some o)
    (hcan : o'.canonical = o.canonical) (y : NodeId) :
    (m.setObj h o').canonicalOf y = m.canonicalOf y := by
  unfold Mem.canonicalOf
  rw [Mem.tableOf_setObj]
  cases ht : m.tableOf y with
  | none => rfl
  | some h' =>
    simp only
    by_cases hh : h' = h
    · subst hh
      rw [Mem.obj?_setObj_self, ho]
      simp only [hcan]
    · rw [Mem.obj?_setObj_ne _ _ hh]

/-- The slots of object o after its node is written (`Mem.writeNode`): its slots
to pinned pointees become memory slots to their canonical objects. -/
def Mem.pinSlots (m : Mem V) (D : Dirty) (o : Obj V) : List (NodeId × Slot) :=
  o.slots.map (fun q =>
    if inD D q.1 then
      match m.canonicalOf q.1 with
      | some h0 => (q.1, Slot.mem h0)
      | none => q
    else q)

/-- The version that `Mem.writeNode` writes for node x from object o. -/
def Mem.verOf (sp : Spec V T) (S0 : Stream V T) (m : Mem V) (D : Dirty) (i : Nat) (x : NodeId)
    (o : Obj V) : Version V :=
  ⟨x, i, o.level, o.isData, o.hist,
    (pointees sp o.hist).filterMap (fun y => (m.refOf S0 D o y).map (fun r => (y, r)))⟩

theorem lookup_map_val {β : Type} (g : NodeId → β → β) :
    ∀ (l : List (NodeId × β)) (y : NodeId),
      (l.map (fun q => (q.1, g q.1 q.2))).lookup y = (l.lookup y).map (g y)
  | [], _ => rfl
  | (a, b) :: l, y => by
    simp only [List.map_cons, List.lookup_cons]
    by_cases hya : y = a
    · subst hya; simp
    · have : (y == a) = false := by simp [hya]
      simp only [this]
      exact lookup_map_val g l y

/-- The slot of a written object for y: the old one, or for a pinned y a memory
slot to its canonical object. -/
theorem slot?_of_pinSlots (m : Mem V) (D : Dirty) (o : Obj V) {o' : Obj V}
    (hs : o'.slots = m.pinSlots D o) (y : NodeId) :
    o'.slot? y =
      (o.slot? y).map (fun sl => if inD D y then
        (match m.canonicalOf y with
         | some h0 => Slot.mem h0
         | none => sl) else sl) := by
  have hps : m.pinSlots D o = o.slots.map (fun q => (q.1, (fun (z : NodeId) (sl : Slot) =>
      if inD D z then (match m.canonicalOf z with
        | some h0 => Slot.mem h0
        | none => sl) else sl) q.1 q.2)) := by
    unfold Mem.pinSlots
    apply List.map_congr_left
    intro q _
    obtain ⟨z, sl⟩ := q
    simp only
    by_cases hz : inD D z = true
    · simp only [hz, ↓reduceIte]
      cases m.canonicalOf z <;> rfl
    · simp only [hz, Bool.false_eq_true, ↓reduceIte]
  unfold Obj.slot?
  rw [hs, hps]
  exact lookup_map_val (fun (z : NodeId) (sl : Slot) => if inD D z then (match m.canonicalOf z with
    | some h0 => Slot.mem h0
    | none => sl) else sl) o.slots y

section

variable (sp : Spec V T) (S0 S : Stream V T) (P : Struct V) (D : Dirty) (i : Nat)

/-- Writing node x changes only x's canonical object, and keeps the node table
and every canonical flag. -/
theorem writeNode_shape {m : Mem V} {x : NodeId} {h : Nat} {o : Obj V}
    (hc : m.canonicalOf x = some h) (ho : m.obj? h = some o) :
    (m.writeNode sp S0 D i x) =
      (m.setObj h { o with pos := some i, slots := m.pinSlots D o }, some (m.verOf sp S0 D i x o)) := by
  unfold Mem.writeNode
  rw [hc]
  simp only [ho]
  rfl

/-- The loop of `writeNodes` from an accumulator. -/
def wnStep (m : Mem V × List (Version V)) (x : NodeId) : Mem V × List (Version V) :=
  match m.1.writeNode sp S0 D i x with
  | (m', some v) => (m', m.2 ++ [v])
  | (m', none) => (m', m.2)

theorem writeNodes_eq_foldl (m : Mem V) (xs : List NodeId) :
    m.writeNodes sp S0 D i xs = xs.foldl (wnStep sp S0 D i) (m, []) := rfl

theorem wnStep_some {m : Mem V} {L : List (Version V)} {x : NodeId} {m' : Mem V} {v : Version V}
    (hw : m.writeNode sp S0 D i x = (m', some v)) : wnStep sp S0 D i (m, L) x = (m', L ++ [v]) := by
  simp [wnStep, hw]

theorem wnStep_none {m : Mem V} {L : List (Version V)} {x : NodeId} {m' : Mem V}
    (hw : m.writeNode sp S0 D i x = (m', none)) : wnStep sp S0 D i (m, L) x = (m', L) := by
  simp [wnStep, hw]

theorem foldl_wnStep_prefix :
    ∀ (xs : List NodeId) (m : Mem V) (L : List (Version V)),
      xs.foldl (wnStep sp S0 D i) (m, L) =
        ((xs.foldl (wnStep sp S0 D i) (m, [])).1, L ++ (xs.foldl (wnStep sp S0 D i) (m, [])).2) := by
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
        rw [wnStep_none sp S0 D i hw, wnStep_none sp S0 D i hw]
        exact ih m' L
      | some v =>
        rw [wnStep_some sp S0 D i hw, wnStep_some sp S0 D i hw, ih m' (L ++ [v]), ih m' ([] ++ [v])]
        simp

/-- The physical writer's loop writes the model's versions. -/
theorem writeNodes_eq :
    ∀ (xs : List NodeId) (acc : List (Version V)) (m : Mem V) (wr : List NodeId),
      TableNode m → SlotsNode m →
      (∀ y, inD D y = true → (m.canonicalOf y).isSome) →
      PosOK S acc m →
      (∀ x ∈ xs, WriteOK sp S0 S P D wr m x) →
      (∀ v ∈ acc, v.node ∈ wr) → (∀ x ∈ xs, x ∈ wr) →
      xs.Nodup → (∀ x ∈ xs, ∀ v ∈ acc, v.node ≠ x) →
      acc ++ (m.writeNodes sp S0 D i xs).2 = writeAll sp S i P xs acc ∧
        PosOK S (writeAll sp S i P xs acc) (m.writeNodes sp S0 D i xs).1 ∧
        TableNode (m.writeNodes sp S0 D i xs).1 ∧ SlotsNode (m.writeNodes sp S0 D i xs).1 ∧
        (∀ y, inD D y = true → ((m.writeNodes sp S0 D i xs).1.canonicalOf y).isSome) ∧
        (∀ y, (m.writeNodes sp S0 D i xs).1.canonicalOf y = m.canonicalOf y) := by
  intro xs
  induction xs with
  | nil =>
    intro acc m wr htn hsn hD hpos _ _ _ _ _
    exact ⟨by simp [writeNodes_eq_foldl, writeAll], by simpa [writeNodes_eq_foldl, writeAll] using hpos,
      by simpa [writeNodes_eq_foldl] using htn, by simpa [writeNodes_eq_foldl] using hsn,
      by simpa [writeNodes_eq_foldl] using hD, fun _ => rfl⟩
  | cons x xs ih =>
    intro acc m wr htn hsn hD hpos hok hacc hwr hnd hfresh
    obtain ⟨h, o, n, hc, ho, hn, hnode, hhist, hlev, hdat, hslots⟩ := hok x (List.mem_cons_self)
    have hcan : o.canonical = true := by
      obtain ⟨-, o2, ho2, hc2⟩ := (m.canonicalOf_eq_some x h).mp hc
      rw [ho] at ho2; cases ho2; exact hc2
    -- The references of x's version are the latest versions so far.
    have href : ∀ y ∈ pointees sp o.hist,
        m.refOf S0 D o y = ((S.building acc).lv y).map (·.recNo) := by
      intro y hy
      rw [Mem.refOf_eq]
      rw [hhist] at hy
      by_cases hyD : inD D y = true
      · simp only [hyD, ↓reduceIte]
        obtain ⟨hy', hcy⟩ := Option.isSome_iff_exists.mp (hD y hyD)
        rw [hcy]
        obtain ⟨-, oy, hoy, -⟩ := (m.canonicalOf_eq_some y hy').mp hcy
        simp only [hoy, Option.bind_some]
        exact hpos y hy' oy hcy hoy
      · simp only [hyD, Bool.false_eq_true, ↓reduceIte]
        have hyD' : inD D y = false := by simpa using hyD
        rcases hslots y hy hyD' with ⟨h', hsl, hcy⟩ | ⟨hser, hywr⟩
        · unfold Mem.slotRef
          rw [hsl]
          obtain ⟨-, oy, hoy, -⟩ := (m.canonicalOf_eq_some y h').mp hcy
          simp only [hoy, Option.bind_some]
          exact hpos y h' oy hcy hoy
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
      unfold mkVersion Mem.verOf
      rw [hlev, hdat, hhist]
      congr 1
      apply filterMap_congr_mem
      intro y hy
      rw [href y (by rw [hhist]; exact hy), Option.map_map]
      rfl
    obtain ⟨o', ho'⟩ : ∃ o', o' = { o with pos := some i, slots := m.pinSlots D o } := ⟨_, rfl⟩
    have hw := writeNode_shape sp S0 D i hc ho
    rw [← ho', hvx] at hw
    let m1 := m.setObj h o'
    have hcan1 : ∀ y, m1.canonicalOf y = m.canonicalOf y :=
      canonicalOf_setObj_same ho (by rw [ho'])
    -- The loop: x's version, then the rest from m1.
    have hloop : m.writeNodes sp S0 D i (x :: xs) =
        ((m1.writeNodes sp S0 D i xs).1,
          mkVersion sp (S.building acc) i x n :: (m1.writeNodes sp S0 D i xs).2) := by
      rw [writeNodes_eq_foldl, List.foldl_cons, wnStep_some sp S0 D i hw, foldl_wnStep_prefix,
        ← writeNodes_eq_foldl]
      rfl
    have hwa : writeAll sp S i P (x :: xs) acc =
        writeAll sp S i P xs (acc ++ [mkVersion sp (S.building acc) i x n]) := by
      rw [writeAll_cons]; simp only [hn]
    -- The facts for m1 and acc ++ [x's version].
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
    have hpos1 : PosOK S (acc ++ [mkVersion sp (S.building acc) i x n]) m1 := by
      intro z h1 o1 hcz ho1
      rw [hcan1] at hcz
      by_cases hh : h1 = h
      · subst hh
        -- z is x: one canonical object per handle, of its node.
        have hzx : z = x := by
          obtain ⟨ht, -⟩ := (m.canonicalOf_eq_some z h1).mp hcz
          obtain ⟨o2, ho2, hn2⟩ := htn z h1 ht
          rw [ho] at ho2; cases ho2
          rw [← hn2, hnode]
        subst hzx
        rw [Mem.obj?_setObj_self] at ho1
        cases ho1
        rw [hlvx, ho']
        simp [mkVersion]
      · rw [Mem.obj?_setObj_ne _ _ hh] at ho1
        rw [hpos z h1 o1 hcz ho1, lv_building, lv_building, List.find?_append]
        have hzx : z ≠ x := by
          intro hzx; subst hzx; rw [hc] at hcz; cases hcz; exact hh rfl
        have : [mkVersion sp (S.building acc) i x n].find? (fun v => v.node == z) = none := by
          simp [mkVersion, Ne.symm hzx]
        rw [this, Option.or_none]
    have htn1 : TableNode m1 := by
      intro y h1 ht
      rw [Mem.tableOf_setObj] at ht
      obtain ⟨o2, ho2, hn2⟩ := htn y h1 ht
      by_cases hh : h1 = h
      · subst hh
        rw [Mem.obj?_setObj_self]
        rw [ho] at ho2; cases ho2
        exact ⟨o', rfl, by rw [ho']; exact hn2⟩
      · rw [Mem.obj?_setObj_ne _ _ hh]; exact ⟨o2, ho2, hn2⟩
    have hsn1 : SlotsNode m1 := by
      intro h1 o1 ho1 y h' hsl
      -- The target in m1: the same object, or o' (of node x) if it is h.
      have htarget : ∀ o2, m.obj? h' = some o2 → o2.node = y → ∃ o3, m1.obj? h' = some o3 ∧ o3.node = y := by
        intro o2 ho2 hn2
        by_cases hh : h' = h
        · subst hh
          rw [ho] at ho2; cases ho2
          exact ⟨o', Mem.obj?_setObj_self _ _ _, by rw [ho']; exact hn2⟩
        · exact ⟨o2, by rw [Mem.obj?_setObj_ne _ _ hh]; exact ho2, hn2⟩
      by_cases hh : h1 = h
      · subst hh
        rw [Mem.obj?_setObj_self] at ho1
        cases ho1
        rw [slot?_of_pinSlots m D o (o' := o') (by rw [ho'])] at hsl
        -- A slot of o': one of o's, or a memory slot to a canonical object.
        cases hos : o.slot? y with
        | none => rw [hos] at hsl; simp at hsl
        | some sl =>
          rw [hos] at hsl
          simp only [Option.map_some, Option.some.injEq] at hsl
          by_cases hyD : inD D y = true
          · simp only [hyD, ↓reduceIte] at hsl
            cases hcy : m.canonicalOf y with
            | none =>
              rw [hcy] at hsl
              simp only at hsl
              subst hsl
              obtain ⟨o2, ho2, hn2⟩ := hsn _ o ho y h' hos
              exact htarget o2 ho2 hn2
            | some h0 =>
              rw [hcy] at hsl
              simp only [Slot.mem.injEq] at hsl
              subst hsl
              obtain ⟨ht, -⟩ := (m.canonicalOf_eq_some y h0).mp hcy
              obtain ⟨o2, ho2, hn2⟩ := htn y h0 ht
              exact htarget o2 ho2 hn2
          · simp only [hyD, Bool.false_eq_true, ↓reduceIte] at hsl
            subst hsl
            obtain ⟨o2, ho2, hn2⟩ := hsn _ o ho y h' hos
            exact htarget o2 ho2 hn2
      · rw [Mem.obj?_setObj_ne _ _ hh] at ho1
        obtain ⟨o2, ho2, hn2⟩ := hsn h1 o1 ho1 y h' hsl
        exact htarget o2 ho2 hn2
    have hD1 : ∀ y, inD D y = true → (m1.canonicalOf y).isSome := by
      intro y hy; rw [hcan1]; exact hD y hy
    have hxs : x ∉ xs := (List.nodup_cons.mp hnd).1
    have hok1 : ∀ x' ∈ xs, WriteOK sp S0 S P D wr m1 x' := by
      intro x' hx'
      obtain ⟨h2, o2, n2, hc2, ho2, hn2, hnode2, hhist2, hlev2, hdat2, hslots2⟩ :=
        hok x' (List.mem_cons_of_mem x hx')
      have hne : h2 ≠ h := by
        intro hh; subst hh
        rw [ho] at ho2; cases ho2
        have hxx : x = x' := by rw [← hnode, hnode2]
        exact hxs (hxx ▸ hx')
      refine ⟨h2, o2, n2, by rw [hcan1]; exact hc2, by rw [Mem.obj?_setObj_ne _ _ hne]; exact ho2,
        hn2, hnode2, hhist2, hlev2, hdat2, ?_⟩
      intro y hy hyD
      rcases hslots2 y hy hyD with ⟨h', hsl, hcy⟩ | ⟨hser, hywr⟩
      · exact Or.inl ⟨h', hsl, by rw [hcan1]; exact hcy⟩
      · right
        refine ⟨?_, hywr⟩
        rw [← hser]
        unfold Mem.slotRef
        cases hs : o2.slot? y with
        | none => rfl
        | some sl =>
          cases sl with
          | stream r => rfl
          | mem h3 =>
            simp only
            -- Not x's object: that one is of node x, which the record writes.
            have hne3 : h3 ≠ h := by
              intro hh; subst hh
              obtain ⟨o3, ho3, hn3⟩ := hsn h2 o2 ho2 y h3 hs
              rw [ho] at ho3; cases ho3
              exact hywr (by rw [← hn3, hnode]; exact hwr x List.mem_cons_self)
            rw [Mem.obj?_setObj_ne _ _ hne3]
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
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := ih (acc ++ [mkVersion sp (S.building acc) i x n]) m1 wr
      htn1 hsn1 hD1 hpos1 hok1 hacc1 (fun x' hx' => hwr x' (List.mem_cons_of_mem x hx'))
      (List.nodup_cons.mp hnd).2 hfresh1
    rw [hloop, hwa]
    refine ⟨?_, h2, h3, h4, h5, fun y => by rw [h6 y, hcan1]⟩
    rw [← h1]
    simp

end

end SIS
