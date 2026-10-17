/-
Proofs for stage 2 (bergdb item 001, WP E3), part 4: the Level 4 loader keeps the
invariant. A reader's follow (`Mem.follow4`) of any slot and a read at any time
(`Mem.read4`); the writer's follow (with `Mem.promote`) is in EvictPromote.lean.
-/
import SIS.Proof.EvictInv

set_option linter.unusedSectionVars false

namespace SIS

variable {V T : Type} [DecidableEq V]

/-! ## Memories with the same lookups -/

/-- m' has m's objects and node table, by lookup, and m's startup pos, root and
next handle. -/
def Mem.Same (m m' : Mem V) : Prop :=
  (∀ h, m'.obj? h = m.obj? h) ∧ (∀ y, m'.tableOf y = m.tableOf y) ∧ m'.s = m.s ∧
    m'.root = m.root ∧ m'.next = m.next

section Same

variable {sp : Spec V T} {db : DB V T} {S0 : Stream V T} {k : Nat} {m m' : Mem V}

theorem Mem.Same.canonicalOf (hs : m.Same m') (y : NodeId) : m'.canonicalOf y = m.canonicalOf y := by
  unfold Mem.canonicalOf
  rw [hs.2.1 y]
  cases m.tableOf y with
  | none => rfl
  | some h => simp only [hs.1 h]

theorem Mem.Same.coreEq (hs : m.Same m') : m.CoreEq m' :=
  ⟨fun h => by rw [hs.1 h], hs.canonicalOf, hs.2.2.1⟩

/-- The invariant depends on the memory only through its lookups (and the node
table's keys having no repeats). -/
theorem EInv.same (hm : EInv sp db S0 k m) (hs : m.Same m') (hnd : (m'.table.map (·.1)).Nodup)
    (hnd2 : (m'.objs.map (·.1)).Nodup) : EInv sp db S0 k m' := by
  have hce := hs.coreEq
  refine ⟨hm.len, hm.pre, by rw [hs.2.2.1]; exact hm.sEq, fun h hh => by
      rw [hs.1 h]; exact hm.fresh h (by rw [← hs.2.2.2.2]; exact hh), hnd2, ?_, hnd, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨o, ho, hc, hn⟩ := hm.root
    exact ⟨o, by rw [hs.2.2.2.1, hs.1]; exact ho, hc, hn⟩
  · intro y h ht
    rw [hs.2.1] at ht
    obtain ⟨o, ho, hn⟩ := hm.tbl y h ht
    exact ⟨o, by rw [hs.1]; exact ho, hn⟩
  · intro h o ho y h' hy
    rw [hs.1] at ho
    obtain ⟨o', ho', hn⟩ := hm.slotsNode h o ho y h' hy
    exact ⟨o', by rw [hs.1]; exact ho', hn⟩
  · intro y h ht
    rw [hs.2.1] at ht
    obtain ⟨o, ho, hc⟩ := hm.tblCanon y h ht
    exact ⟨o, by rw [hs.1]; exact ho, hc⟩
  · intro h o ho hc
    rw [hs.1] at ho
    rw [hs.2.1]; exact hm.canonTbl h o ho hc
  · intro h o ho hc
    rw [hs.1] at ho
    exact hm.cc h o ho hc
  · intro z h o hz ho
    rw [hs.canonicalOf] at hz
    rw [hs.1] at ho
    exact hm.pos z h o hz ho
  · intro y hy
    rw [hs.canonicalOf]; exact hm.dCanon y hy
  · intro h o ho hc
    rw [hs.1] at ho
    exact (hm.snap h o ho hc).congr hce
  · intro h o ho hr y hy
    rw [hs.1] at ho
    obtain ⟨sl, hsl, hi⟩ := hm.slots h o ho hr y hy
    exact ⟨sl, hsl, hi.congr hce⟩
  · intro h o ho hc hr y hy
    rw [hs.1] at ho
    obtain ⟨sl, hsl, hi⟩ := hm.live h o ho hc hr y hy
    exact ⟨sl, hsl, hi.congr hce⟩

end Same

/-! ## Slots that change in place -/

section Slots

variable {sp : Spec V T} {db : DB V T} {S0 : Stream V T} {k : Nat} {m : Mem V}

/-- Replacing an object by one with the same core and the same slots (by
lookup) keeps the invariant. -/
theorem EInv.setObj_sameSlots (hm : EInv sp db S0 k m) {hp : Nat} {op op' : Obj V}
    (hop : m.obj? hp = some op) (hc : op'.core = op.core) (hs : ∀ z, op'.slot? z = op.slot? z) :
    EInv sp db S0 k (m.setObj hp op') := by
  have e1 : op'.node = op.node := congrArg (fun c => c.1) hc
  have e2 : op'.level = op.level := congrArg (fun c => c.2.1) hc
  have e3 : op'.isData = op.isData := congrArg (fun c => c.2.2.1) hc
  have e4 : op'.hist = op.hist := congrArg (fun c => c.2.2.2.1) hc
  have e6 : op'.pos = op.pos := congrArg (fun c => c.2.2.2.2.2) hc
  apply hm.setObj_core hop hc
  · intro y h' hy; rw [hs] at hy; exact hm.slotsNode hp op hop y h' hy
  · intro hco
    obtain ⟨r, w, h1, h2, h3, h4, h5, h6, h7⟩ := hm.snap hp op hop hco
    exact ⟨r, w, by rw [e6]; exact h1, by rw [e1]; exact h2, by rw [e4]; exact h3,
      by rw [e2]; exact h4, by rw [e3]; exact h5,
      fun z hz => by rw [hs]; exact h6 z (by rw [← e4]; exact hz),
      fun z sl hz => h7 z sl (by rw [← hs]; exact hz)⟩
  · intro hr z hz
    obtain ⟨sl, hsl, hi⟩ := hm.slots hp op hop hr z hz
    exact ⟨sl, by rw [hs]; exact hsl, hi⟩
  · intro hco hr z hz
    obtain ⟨sl, hsl, hi⟩ := hm.live hp op hop hco hr z hz
    exact ⟨sl, by rw [hs]; exact hsl, hi⟩

theorem slot?_setSlot_of {o : Obj V} {y : NodeId} {sl0 : Slot} (h : o.slot? y = some sl0) (sl : Slot)
    (z : NodeId) : (o.setSlot y sl).slot? z = if z = y then some sl else o.slot? z := by
  rw [Obj.slot?_setSlot]
  split
  · rename_i hz; subst hz; rw [h]; rfl
  · rfl

/-- Setting a slot for y that exists to a memory slot to y's canonical object keeps
the invariant: it serializes y's latest version if y is not in D (INV-CAN), and
it is what INV-SLOT asks for y in D. -/
theorem EInv.setSlot_canon (hm : EInv sp db S0 k m) {hp : Nat} {op : Obj V}
    (hop : m.obj? hp = some op) {y : NodeId} {sl0 : Slot} (hsl : op.slot? y = some sl0) {h0 : Nat}
    (hc : m.canonicalOf y = some h0) :
    EInv sp db S0 k (m.setObj hp (op.setSlot y (Slot.mem h0))) := by
  obtain ⟨o0, ho0, hc0, hn0⟩ := hm.obj_of_canonicalOf hc
  have hpos := hm.pos.lv0 hc ho0
  have hinv0 : SlotInv S0 db m op y (Slot.mem h0) ∧ LiveInv S0 db m y (Slot.mem h0) := by
    refine ⟨⟨fun _ => ?_, fun _ => Or.inl ⟨h0, rfl, hc⟩⟩, fun _ => ⟨h0, rfl, hc⟩, fun _ => ?_⟩
    · simp only [slotRefOf, ho0, Option.bind_some]; exact hpos
    · simp only [slotRefOf, ho0, Option.bind_some]; exact hpos
  have hs := slot?_setSlot_of hsl (Slot.mem h0)
  apply hm.setObj_core hop (setSlot_core op y _)
  · intro z h' hz
    rw [hs] at hz
    split at hz
    · rename_i hzy; subst hzy
      simp only [Option.some.injEq, Slot.mem.injEq] at hz
      subst hz
      exact ⟨o0, ho0, hn0⟩
    · exact hm.slotsNode hp op hop z h' hz
  · intro hco
    obtain ⟨r, w, h1, h2, h3, h4, h5, h6, h7⟩ := hm.snap hp op hop hco
    refine ⟨r, w, h1, h2, h3, h4, h5, fun z hz => ?_, fun z sl hz => ?_⟩
    · rw [hs]; split
      · rfl
      · exact h6 z hz
    · rw [hs] at hz
      split at hz
      · rename_i hzy; subst hzy
        simp only [Option.some.injEq] at hz
        subst hz
        exact Or.inr (Or.inr ⟨h0, o0, rfl, ho0, hn0, Or.inl hc0⟩)
      · exact h7 z sl hz
  · intro hr z hz
    obtain ⟨sl, hsl1, hi⟩ := hm.slots hp op hop hr z hz
    rw [hs]
    split
    · rename_i hzy; subst hzy; exact ⟨_, rfl, hinv0.1⟩
    · exact ⟨sl, hsl1, hi⟩
  · intro hco hr z hz
    obtain ⟨sl, hsl1, hi⟩ := hm.live hp op hop hco hr z hz
    rw [hs]
    split
    · rename_i hzy; subst hzy; exact ⟨_, rfl, hinv0.2⟩
    · exact ⟨sl, hsl1, hi⟩

end Slots

/-! ## A snapshot read from the stream -/

section AddSnap

variable {sp : Spec V T} {db : DB V T} {S0 : Stream V T} {k : Nat} {m : Mem V}

/-- Adding a snapshot of a version of the stream keeps the invariant. -/
theorem EInv.addSnap (hinv : Inv sp db k) (hm : EInv sp db S0 k m) {r : Nat} {y : NodeId}
    {w : Version V} (hw : db.S.versionAt r y = some w) :
    EInv sp db S0 k (m.addObj (Obj.ofVersion sp w none)).1 := by
  obtain ⟨f1, f2, f3, f4, f5, f6⟩ := Obj.ofVersion_fields sp w none
  obtain ⟨hwn, hwr, -⟩ := hinv.version_node hw
  generalize hodef : Obj.ofVersion sp w none = o at f1 f2 f3 f4 f5 f6 ⊢
  have hobj : ∀ h', (m.addObj o).1.obj? h' = if h' = m.next then some o else m.obj? h' := Mem.obj?_addObj m o
  have hold : ∀ h' o', m.obj? h' = some o' → (m.addObj o).1.obj? h' = some o' := by
    intro h' o' ho'
    rw [hobj]
    have : h' ≠ m.next := by
      intro he; subst he; rw [hm.fresh _ (Nat.le_refl _)] at ho'; cases ho'
    simp only [this, ↓reduceIte]; exact ho'
  have hnew : ∀ h' o', (m.addObj o).1.obj? h' = some o' → (h' = m.next ∧ o' = o) ∨ m.obj? h' = some o' := by
    intro h' o' ho'
    rw [hobj] at ho'
    split at ho'
    · rename_i he; exact Or.inl ⟨he, (Option.some.injEq _ _ ▸ ho').symm⟩
    · exact Or.inr ho'
  have hcan : ∀ z, (m.addObj o).1.canonicalOf z = m.canonicalOf z := by
    intro z
    unfold Mem.canonicalOf
    rw [Mem.tableOf_addObj]
    cases ht : m.tableOf z with
    | none => rfl
    | some h' =>
      obtain ⟨o', ho', -⟩ := hm.tbl z h' ht
      simp only [hold h' o' ho', ho']
  have hs1 : (m.addObj o).1.s = m.s := rfl
  have hce : ∀ h' o', m.obj? h' = some o' → ∀ z sl, o'.slot? z = some sl →
      slotRefOf S0 (m.addObj o).1 z sl = slotRefOf S0 m z sl := by
    intro h' o' ho' z sl hz
    cases sl with
    | mem h2 =>
      obtain ⟨o2, ho2, -⟩ := hm.slotsNode h' o' ho' z h2 hz
      simp only [slotRefOf, hold h2 o2 ho2, ho2]
    | stream r => rfl
  have hsnapSlot : ∀ h' o', m.obj? h' = some o' → ∀ w' z sl, o'.slot? z = some sl →
      SnapSlot S0 db m w' z sl → SnapSlot S0 db (m.addObj o).1 w' z sl := by
    intro h' o' ho' w' z sl hz hs
    unfold SnapSlot at hs ⊢
    rw [hs1]
    rcases hs with hs | hs | ⟨h2, o2, hsl, ho2, hn, hc⟩
    · exact Or.inl hs
    · exact Or.inr (Or.inl hs)
    · exact Or.inr (Or.inr ⟨h2, o2, hsl, hold h2 o2 ho2, hn, hc⟩)
  have hslotInv : ∀ h' o', m.obj? h' = some o' → ∀ z sl, o'.slot? z = some sl →
      SlotInv S0 db m o' z sl → SlotInv S0 db (m.addObj o).1 o' z sl := by
    intro h' o' ho' z sl hz hs
    refine ⟨fun hzD => by rw [hce h' o' ho' z sl hz]; exact hs.1 hzD, fun hzD => ?_⟩
    rcases hs.2 hzD with ⟨h2, hsl, hc⟩ | h3
    · exact Or.inl ⟨h2, hsl, by rw [hcan]; exact hc⟩
    · exact Or.inr h3
  have hliveInv : ∀ h' o', m.obj? h' = some o' → ∀ z sl, o'.slot? z = some sl →
      LiveInv S0 db m z sl → LiveInv S0 db (m.addObj o).1 z sl := by
    intro h' o' ho' z sl hz hs
    refine ⟨fun hzD => ?_, fun hzD => by rw [hce h' o' ho' z sl hz]; exact hs.2 hzD⟩
    obtain ⟨h2, hsl, hc⟩ := hs.1 hzD
    exact ⟨h2, hsl, by rw [hcan]; exact hc⟩
  refine ⟨hm.len, hm.pre, hm.sEq, ?_, nodup_addObj_keys m o hm.objNodup hm.fresh, ?_, hm.tblNodup, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h' hh
    rw [hobj]
    have hh' : m.next + 1 ≤ h' := by simpa using hh
    have h1 : h' ≠ m.next := by omega
    have h2 : m.next ≤ h' := by omega
    simp only [h1, ↓reduceIte]; exact hm.fresh h' h2
  · obtain ⟨o', ho', hc, hn⟩ := hm.root
    exact ⟨o', hold _ _ ho', hc, hn⟩
  · intro z h' ht
    obtain ⟨o', ho', hn⟩ := hm.tbl z h' ht
    exact ⟨o', hold _ _ ho', hn⟩
  · intro h' o' ho' z h2 hz
    rcases hnew h' o' ho' with ⟨-, rfl⟩ | ho'
    · rw [← hodef, Obj.ofVersion_slot?] at hz
      split at hz <;> cases hz
    · obtain ⟨o2, ho2, hn⟩ := hm.slotsNode h' o' ho' z h2 hz
      exact ⟨o2, hold _ _ ho2, hn⟩
  · intro z h' ht
    obtain ⟨o', ho', hc⟩ := hm.tblCanon z h' ht
    exact ⟨o', hold _ _ ho', hc⟩
  · intro h' o' ho' hc
    rcases hnew h' o' ho' with ⟨-, rfl⟩ | ho'
    · rw [f5] at hc; cases hc
    · exact hm.canonTbl h' o' ho' hc
  · intro h' o' ho' hc
    rcases hnew h' o' ho' with ⟨-, rfl⟩ | ho'
    · rw [f5] at hc; cases hc
    · exact hm.cc h' o' ho' hc
  · intro z h' o' hz ho'
    rw [hcan] at hz
    rcases hnew h' o' ho' with ⟨rfl, rfl⟩ | ho'
    · obtain ⟨o2, ho2, hc2, -⟩ := hm.obj_of_canonicalOf hz
      rw [hm.fresh _ (Nat.le_refl _)] at ho2; cases ho2
    · exact hm.pos z h' o' hz ho'
  · intro z hz
    rw [hcan]; exact hm.dCanon z hz
  · intro h' o' ho' hc
    rcases hnew h' o' ho' with ⟨-, rfl⟩ | ho'
    · refine ⟨r, w, by rw [f6, hwr], by rw [f1, hwn]; exact hw, by rw [f4]; rfl, f2, f3,
        fun z hz => ?_, fun z sl hz => ?_⟩
      · rw [← hodef, Obj.ofVersion_slot?]
        rw [f4] at hz
        simp only [cutHist] at hz ⊢
        simp [hz]
      · rw [← hodef, Obj.ofVersion_slot?] at hz
        split at hz
        · simp only [Option.some.injEq] at hz
          exact Or.inl hz.symm
        · cases hz
    · obtain ⟨r1, w1, h1, h2, h3, h4, h5, h6, h7⟩ := hm.snap h' o' ho' hc
      exact ⟨r1, w1, h1, h2, h3, h4, h5, h6,
        fun z sl hz => hsnapSlot h' o' ho' w1 z sl hz (h7 z sl hz)⟩
  · intro h' o' ho' hr z hz
    rcases hnew h' o' ho' with ⟨-, rfl⟩ | ho'
    · have := hr.1; rw [f5] at this; cases this
    · obtain ⟨sl, hsl, hi⟩ := hm.slots h' o' ho' hr z hz
      exact ⟨sl, hsl, hslotInv h' o' ho' z sl hsl hi⟩
  · intro h' o' ho' hc hr z hz
    rcases hnew h' o' ho' with ⟨-, rfl⟩ | ho'
    · rw [f5] at hc; cases hc
    · obtain ⟨sl, hsl, hi⟩ := hm.live h' o' ho' hc hr z hz
      exact ⟨sl, hsl, hliveInv h' o' ho' z sl hsl hi⟩

end AddSnap

/-! ## The reader's follow -/

/-- What `Mem.follow4` reaches through the slot of object hp for y, and the memory
then (before the slot names it). -/
def Mem.reached4 (sp : Spec V T) (S0 S : Stream V T) (m : Mem V) (hp : Nat) (y : NodeId) :
    Option (Mem V × Nat) :=
  match (m.obj? hp).bind (·.slot? y) with
  | none => none
  | some (Slot.mem h) => if (m.obj? h).isSome then some (m, h) else none
  | some (Slot.stream r) =>
    match m.canonicalOf y with
    | some h0 => some (m, h0)
    | none =>
      match ruleRRef S0 m.s y r with
      | none => none
      | some r' =>
        match S.versionAt r' y with
        | none => none
        | some w => some (m.addObj (Obj.ofVersion sp w none))

/-- The slot of object hp for y names object h1. -/
def Mem.swz (m : Mem V) (hp : Nat) (y : NodeId) (h1 : Nat) : Mem V :=
  match m.obj? hp with
  | some op => m.setObj hp (op.setSlot y (Slot.mem h1))
  | none => m

theorem follow4_eq (sp : Spec V T) (S0 S : Stream V T) (m : Mem V) (hp : Nat) (y : NodeId)
    (w : Bool) :
    m.follow4 sp S0 S hp y w = match m.reached4 sp S0 S hp y with
      | none => (m, none)
      | some (m1, h1) =>
        if w then (((m1.swz hp y h1).promote hp y h1).1, some ((m1.swz hp y h1).promote hp y h1).2)
        else (m1.swz hp y h1, some h1) := by
  unfold Mem.follow4 Mem.reached4 Mem.swz
  rfl

theorem reached4_cases {sp : Spec V T} {S0 S : Stream V T} {m : Mem V} {hp : Nat} {y : NodeId}
    {m1 : Mem V} {h1 : Nat} (h : m.reached4 sp S0 S hp y = some (m1, h1)) :
    ∃ op sl, m.obj? hp = some op ∧ op.slot? y = some sl ∧
      ((sl = Slot.mem h1 ∧ m1 = m ∧ (m.obj? h1).isSome) ∨
       (∃ r, sl = Slot.stream r ∧ m.canonicalOf y = some h1 ∧ m1 = m) ∨
       (∃ r r' w, sl = Slot.stream r ∧ m.canonicalOf y = none ∧ ruleRRef S0 m.s y r = some r' ∧
         S.versionAt r' y = some w ∧ m1 = (m.addObj (Obj.ofVersion sp w none)).1 ∧ h1 = m.next)) := by
  unfold Mem.reached4 at h
  cases hop : m.obj? hp with
  | none => rw [hop] at h; cases h
  | some op =>
    rw [hop] at h
    simp only [Option.bind_some] at h
    cases hsl : op.slot? y with
    | none => rw [hsl] at h; cases h
    | some sl =>
      rw [hsl] at h
      refine ⟨op, sl, rfl, hsl, ?_⟩
      cases sl with
      | mem h0 =>
        simp only at h
        split at h
        · rename_i hs
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact Or.inl ⟨rfl, rfl, hs⟩
        · cases h
      | stream r =>
        simp only at h
        cases hc : m.canonicalOf y with
        | some h0 =>
          rw [hc] at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact Or.inr (Or.inl ⟨r, rfl, rfl, rfl⟩)
        | none =>
          rw [hc] at h
          simp only at h
          cases hr : ruleRRef S0 m.s y r with
          | none => rw [hr] at h; cases h
          | some r' =>
            rw [hr] at h
            simp only at h
            cases hw : S.versionAt r' y with
            | none => rw [hw] at h; cases h
            | some w =>
              rw [hw] at h
              simp only [Option.some.injEq] at h
              have e1 : m1 = (m.addObj (Obj.ofVersion sp w none)).1 := by rw [h]
              have e2 : h1 = m.next := by
                have := congrArg Prod.snd h
                simp only [Mem.addObj_snd] at this
                exact this.symm
              exact Or.inr (Or.inr ⟨r, r', w, rfl, rfl, hr, hw, e1, e2⟩)

section Reader

variable {sp : Spec V T} {db : DB V T} {S0 : Stream V T} {k : Nat} {m : Mem V}

/-- A stream slot for a node without a canonical object names, after the first
touch, the snapshot read at the record that Rule R gives: the invariant is kept. -/
theorem EInv.swizzle_load (hinv : Inv sp db k) (hm : EInv sp db S0 k m) {hp : Nat} {op : Obj V}
    (hop : m.obj? hp = some op) {y : NodeId} {r : Option Nat} (hsl : op.slot? y = some (Slot.stream r))
    (hc : m.canonicalOf y = none) {r' : Nat} (hr : ruleRRef S0 m.s y r = some r') {w : Version V}
    (hw : db.S.versionAt r' y = some w) :
    EInv sp db S0 k ((m.addObj (Obj.ofVersion sp w none)).1.setObj hp
      (op.setSlot y (Slot.mem m.next))) := by
  have hm1 := hm.addSnap hinv hw
  obtain ⟨f1, -, -, -, f5, f6⟩ := Obj.ofVersion_fields sp w none
  obtain ⟨hwn, hwr, -⟩ := hinv.version_node hw
  have hpn : hp ≠ m.next := by
    intro he; subst he; rw [hm.fresh _ (Nat.le_refl _)] at hop; cases hop
  have hop1 : (m.addObj (Obj.ofVersion sp w none)).1.obj? hp = some op := by
    rw [Mem.obj?_addObj]; simp only [hpn, ↓reduceIte]; exact hop
  have hnew : (m.addObj (Obj.ofVersion sp w none)).1.obj? m.next = some (Obj.ofVersion sp w none) := by
    rw [Mem.obj?_addObj]; simp
  have hyD : inD db.D y = false := by
    cases hy : inD db.D y with
    | false => rfl
    | true => have := hm.dCanon y hy; rw [hc] at this; cases this
  have hs := slot?_setSlot_of hsl (Slot.mem m.next)
  have hval : slotRefOf S0 (m.addObj (Obj.ofVersion sp w none)).1 y (Slot.mem m.next) =
      slotRefOf S0 (m.addObj (Obj.ofVersion sp w none)).1 y (Slot.stream r) := by
    simp only [slotRefOf, hnew, Option.bind_some, f6, hwr, Mem.addObj_s, hr]
  apply hm1.setObj_core hop1 (setSlot_core op y _)
  · intro z h' hz
    rw [hs] at hz
    split at hz
    · rename_i hzy; subst hzy
      simp only [Option.some.injEq, Slot.mem.injEq] at hz
      subst hz
      exact ⟨_, hnew, by rw [f1, hwn]⟩
    · exact hm1.slotsNode hp op hop1 z h' hz
  · intro hco
    obtain ⟨r0, w0, h1, h2, h3, h4, h5, h6, h7⟩ := hm1.snap hp op hop1 hco
    refine ⟨r0, w0, h1, h2, h3, h4, h5, fun z hz => ?_, fun z sl hz => ?_⟩
    · rw [hs]; split
      · rfl
      · exact h6 z hz
    · rw [hs] at hz
      split at hz
      · rename_i hzy; subst hzy
        simp only [Option.some.injEq] at hz
        subst hz
        refine Or.inr (Or.inr ⟨m.next, _, rfl, hnew, by rw [f1, hwn], Or.inr ⟨r', by rw [f6, hwr],
          fun r0' hr0' => ?_⟩⟩)
        rw [Mem.addObj_s] at hr0'
        rcases h7 z (Slot.stream r) hsl with hold | ⟨p, u, hold, -, hle⟩ | ⟨h'', o'', hold, -⟩
        · simp only [Slot.stream.injEq] at hold
          rw [← hold, hr, Option.some.injEq] at hr0'
          omega
        · simp only [Slot.stream.injEq] at hold
          subst hold
          have := ruleRRef_some_ge hr
          have := hle r0' (by rw [Mem.addObj_s]; exact hr0')
          omega
        · cases hold
      · exact h7 z sl hz
  · intro hrel z hz
    obtain ⟨sl, hsl1, hi⟩ := hm1.slots hp op hop1 hrel z hz
    rw [hs]
    split
    · rename_i hzy; subst hzy
      rw [hsl, Option.some.injEq] at hsl1
      subst hsl1
      refine ⟨_, rfl, fun _ => by rw [hval]; exact hi.1 hyD, fun h => ?_⟩
      rw [hyD] at h; cases h
    · exact ⟨sl, hsl1, hi⟩
  · intro hco hrr z hz
    obtain ⟨sl, hsl1, hi⟩ := hm1.live hp op hop1 hco hrr z hz
    rw [hs]
    split
    · rename_i hzy; subst hzy
      rw [hsl, Option.some.injEq] at hsl1
      subst hsl1
      refine ⟨_, rfl, fun h => ?_, fun _ => by rw [hval]; exact hi.2 hyD⟩
      rw [hyD] at h; cases h
    · exact ⟨sl, hsl1, hi⟩

/-- The memory after the reader's follow of any slot, before the writer's
promotion: the invariant is kept. -/
theorem EInv.reached4 (hinv : Inv sp db k) (hm : EInv sp db S0 k m) {hp : Nat} {y : NodeId}
    {m1 : Mem V} {h1 : Nat} (h : m.reached4 sp S0 db.S hp y = some (m1, h1)) :
    EInv sp db S0 k (m1.swz hp y h1) := by
  obtain ⟨op, sl, hop, hsl, hcase⟩ := reached4_cases h
  rcases hcase with ⟨rfl, rfl, -⟩ | ⟨r, rfl, hc, rfl⟩ | ⟨r, r', w, rfl, hc, hr, hw, rfl, rfl⟩
  · unfold Mem.swz
    rw [hop]
    exact hm.setObj_sameSlots hop (setSlot_core op y _) (fun z => by
      rw [slot?_setSlot_of hsl]; split
      · rename_i hz; subst hz; rw [hsl]
      · rfl)
  · unfold Mem.swz
    rw [hop]
    exact hm.setSlot_canon hop hsl hc
  · unfold Mem.swz
    have hpn : hp ≠ m.next := by
      intro he; subst he; rw [hm.fresh _ (Nat.le_refl _)] at hop; cases hop
    have hop1 : (m.addObj (Obj.ofVersion sp w none)).1.obj? hp = some op := by
      rw [Mem.obj?_addObj]; simp only [hpn, ↓reduceIte]; exact hop
    rw [hop1]
    exact hm.swizzle_load hinv hop hsl hc hr hw

/-- A reader's follow of any slot keeps the invariant. -/
theorem EInv.follow4_reader (hinv : Inv sp db k) (hm : EInv sp db S0 k m) (hp : Nat) (y : NodeId) :
    EInv sp db S0 k (m.follow4 sp S0 db.S hp y false).1 := by
  rw [follow4_eq]
  cases h : m.reached4 sp S0 db.S hp y with
  | none => exact hm
  | some p =>
    obtain ⟨m1, h1⟩ := p
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact hm.reached4 hinv h

theorem foldl_inv1 {α β γ : Type} (f : α × β → γ → α × β) (I : α → Prop)
    (hf : ∀ acc z, I acc.1 → I (f acc z).1) : ∀ (l : List γ) (acc : α × β), I acc.1 → I (l.foldl f acc).1
  | [], _, h => h
  | z :: l, acc, h => foldl_inv1 f I hf l (f acc z) (hf acc z h)

/-- A read at any time, from any object, keeps the invariant. -/
theorem EInv.readAt4 (hinv : Inv sp db k) :
    ∀ (fuel : Nat) (m : Mem V) (t : Time) (h : Nat), EInv sp db S0 k m →
      EInv sp db S0 k (m.readAt4 sp S0 db.S fuel t h).1 := by
  intro fuel
  induction fuel with
  | zero => intro m t h hm; exact hm
  | succ fuel ih =>
    intro m t h hm
    unfold Mem.readAt4
    cases ho : m.obj? h with
    | none => exact hm
    | some o =>
      simp only
      apply foldl_inv1 _ (EInv sp db S0 k) _ _ _ hm
      intro acc z hacc
      have hf := hacc.follow4_reader hinv h z
      generalize acc.1.follow4 sp S0 db.S h z false = res at hf ⊢
      obtain ⟨m1, oh⟩ := res
      cases oh with
      | none => exact hf
      | some h1 =>
        simp only
        cases ho1 : m1.obj? h1 with
        | none => exact hf
        | some o1 =>
          simp only
          split
          · exact ih m1 t h1 hf
          · exact hf

theorem EInv.read4 (hinv : Inv sp db k) (hm : EInv sp db S0 k m) (t : Time) :
    EInv sp db S0 k (m.read4 sp S0 db.S t).1 := by
  unfold Mem.read4
  cases m.obj? m.root with
  | none => exact hm
  | some o => exact EInv.readAt4 hinv _ m t _ hm

/-- Every cache operation keeps the invariant. -/
theorem EInv.cacheOp (hinv : Inv sp db k) (hm : EInv sp db S0 k m) (op : CacheOp) :
    EInv sp db S0 k (m.cacheOp sp S0 db.S db.D op) := by
  cases op with
  | read t => exact hm.read4 hinv t
  | unswizzle h y => exact hm.unswizzle hinv h y
  | release h => exact hm.release h

theorem EInv.cacheOps (hinv : Inv sp db k) (ops : List CacheOp) :
    ∀ m, EInv sp db S0 k m → EInv sp db S0 k (ops.foldl (Mem.cacheOp sp S0 db.S db.D) m) := by
  induction ops with
  | nil => intro m hm; exact hm
  | cons op ops ih => intro m hm; exact ih _ (hm.cacheOp hinv op)

end Reader

end SIS
