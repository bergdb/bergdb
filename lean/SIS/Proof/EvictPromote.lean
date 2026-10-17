/-
Proofs for stage 2 (bergdb item 001, WP E3), part 5: the writer's follow. Through
a live slot of the canonical object of a current node, the writer reaches its
child's canonical object, or the snapshot of the child's latest version, which
it makes canonical (`Mem.promote`); the invariant is kept.
-/
import SIS.Proof.EvictFollow

set_option linter.unusedSectionVars false

namespace SIS

variable {V T : Type} [DecidableEq V]

theorem mem_pointees_of_live' {sp : Spec V T} (hls : LiveSub sp) {h : History V} {y : NodeId}
    (hy : y ∈ sp.live h) : y ∈ pointees sp h := by
  obtain ⟨e, he, hye⟩ := hls _ _ hy
  simp only [pointees, List.mem_eraseDups, List.mem_flatMap]
  exact ⟨e, he, hye⟩

section Clean

variable {sp : Spec V T} {db : DB V T} {S0 : Stream V T} {k : Nat} {m : Mem V}

/-- A snapshot's slot for a pointee whose reference in the version is the
pointee's latest version serializes that latest version. -/
theorem EInv.snapSlot_clean (hinv : Inv sp db k) (hm : EInv sp db S0 k m) {w : Version V} {z : NodeId}
    {sl : Slot} (hss : SnapSlot S0 db m w z sl) (hw : w.ref? z = (db.S.lv z).map (·.recNo)) :
    slotRefOf S0 m z sl = (db.S.lv z).map (·.recNo) := by
  have hR := hinv.ruleR_lv0 hm.pre m.s z
  rcases hss with rfl | ⟨p, u, rfl, hu, hle⟩ | ⟨h', o', rfl, ho', hn', hc'⟩
  · simp only [slotRefOf]; rw [hw]; exact hR
  · rw [hw, hR] at hle
    obtain ⟨v, hv, hpv⟩ := hinv.le_lv hu
    rw [hv] at hle
    have := hle v.recNo rfl
    have hp : p = v.recNo := by omega
    simp only [slotRefOf]
    rw [hp]
    have := hinv.ruleR_lv0 hm.pre m.s z
    rw [hv] at this ⊢
    exact this
  · simp only [slotRefOf, ho', Option.bind_some]
    rcases hc' with hc' | ⟨p, hp, hle⟩
    · have hcz := hm.canonicalOf_of ho' hc'
      rw [hn'] at hcz
      exact hm.pos.lv0 hcz ho'
    · rw [hw, hR] at hle
      cases hco : o'.canonical with
      | true =>
        have hcz := hm.canonicalOf_of ho' hco
        rw [hn'] at hcz
        exact hm.pos.lv0 hcz ho'
      | false =>
        obtain ⟨r1, w1, h1, h2, -⟩ := hm.snap h' o' ho' hco
        rw [hp, Option.some.injEq] at h1
        subst h1
        rw [hn'] at h2
        obtain ⟨v, hv, hpv⟩ := hinv.le_lv h2
        rw [hv] at hle
        have := hle v.recNo rfl
        rw [hp, hv]
        simp only [Option.map_some, Option.some.injEq]
        omega

end Clean

/-! ## Promotion of a snapshot -/

section Promote

variable {sp : Spec V T} {db : DB V T} {S0 : Stream V T} {k : Nat} {m : Mem V}

theorem setTable_nodup (m : Mem V) (y : NodeId) (h : Nat) (hnd : (m.table.map (·.1)).Nodup) :
    ((m.setTable y h).table.map (·.1)).Nodup := by
  unfold Mem.setTable
  simp only [List.map_cons, List.nodup_cons]
  refine ⟨?_, (List.Sublist.map _ List.filter_sublist).nodup hnd⟩
  intro hm
  obtain ⟨p, hp, hpy⟩ := List.mem_map.mp hm
  have := (List.mem_filter.mp hp).2
  rw [hpy] at this
  simp at this

/-- The snapshot h1 of y's latest version becomes y's canonical object, when y has
none: it holds y's whole history and latest position, and its slots serialize
the latest versions of its pointees, which are not in D. The invariant is kept. -/
theorem EInv.promote_new (hls : LiveSub sp) (hm : EInv sp db S0 k m) {y : NodeId} {h1 : Nat}
    {o1 : Obj V} (hc : m.canonicalOf y = none) (ho1 : m.obj? h1 = some o1) (hn1 : o1.node = y)
    (hnc : o1.canonical = false)
    (hcc : ∃ n, db.P.get? y = some n ∧ o1.hist = n.hist ∧ o1.level = n.level ∧ o1.isData = n.isData)
    (hpos1 : o1.pos = (db.S.lv y).map (·.recNo))
    (hslots1 : ∀ z ∈ pointees sp o1.hist, ∃ sl, o1.slot? z = some sl ∧ inD db.D z = false ∧
      slotRefOf S0 m z sl = (db.S.lv z).map (·.recNo)) :
    EInv sp db S0 k ((m.setObj h1 { o1 with canonical := true }).setTable y h1) := by
  let o1c : Obj V := { o1 with canonical := true }
  let m3 := (m.setObj h1 o1c).setTable y h1
  have hobj : ∀ h, m3.obj? h = if h = h1 then some o1c else m.obj? h := by
    intro h; show (m.setObj h1 o1c).obj? h = _; rw [Mem.obj?_setObj]
  have htab : ∀ z, m3.tableOf z = if z = y then some h1 else m.tableOf z := by
    intro z; show ((m.setObj h1 o1c).setTable y h1).tableOf z = _
    rw [Mem.tableOf_setTable, Mem.tableOf_setObj]
  have hyD : inD db.D y = false := by
    cases hy : inD db.D y with
    | false => rfl
    | true => have := hm.dCanon y hy; rw [hc] at this; cases this
  -- A table entry of another node names another object than h1.
  have htne : ∀ z h, z ≠ y → m.tableOf z = some h → h ≠ h1 := by
    intro z h hz ht he
    subst he
    obtain ⟨o, ho, hn⟩ := hm.tbl z h ht
    rw [ho1, Option.some.injEq] at ho
    subst ho
    exact hz (hn.symm.trans hn1)
  have hcan : ∀ z, m3.canonicalOf z = if z = y then some h1 else m.canonicalOf z := by
    intro z
    unfold Mem.canonicalOf
    rw [htab z]
    by_cases hz : z = y
    · simp only [hz, ↓reduceIte, hobj]
      rfl
    · simp only [hz, ↓reduceIte]
      cases ht : m.tableOf z with
      | none => rfl
      | some h =>
        simp only [hobj, htne z h hz ht, ↓reduceIte]
  -- Objects of m3: h1 upgraded, others as in m.
  have hcases : ∀ h o, m3.obj? h = some o → (h = h1 ∧ o = o1c) ∨ (h ≠ h1 ∧ m.obj? h = some o) := by
    intro h o ho
    rw [hobj] at ho
    split at ho
    · rename_i he; exact Or.inl ⟨he, (Option.some.injEq _ _ ▸ ho).symm⟩
    · rename_i he; exact Or.inr ⟨he, ho⟩
  have hup : ∀ h o, m.obj? h = some o → ∃ o', m3.obj? h = some o' ∧ o'.node = o.node ∧
      o'.pos = o.pos ∧ (o.canonical = true → o'.canonical = true) := by
    intro h o ho
    rw [hobj]
    by_cases he : h = h1
    · subst he; rw [ho1, Option.some.injEq] at ho; subst ho
      exact ⟨o1c, by simp, rfl, rfl, fun _ => rfl⟩
    · simp only [he, ↓reduceIte]; exact ⟨o, ho, rfl, rfl, id⟩
  have hs3 : m3.s = m.s := rfl
  have hslotRef : ∀ z sl, slotRefOf S0 m3 z sl = slotRefOf S0 m z sl := by
    intro z sl
    cases sl with
    | mem h =>
      simp only [slotRefOf]
      cases ho : m.obj? h with
      | none =>
        rw [hobj]
        by_cases he : h = h1
        · subst he; rw [ho1] at ho; cases ho
        · simp only [he, ↓reduceIte, ho]
      | some o =>
        obtain ⟨o', ho', -, hp', -⟩ := hup h o ho
        rw [ho']; simp [hp']
    | stream r => rfl
  have hcanUp : ∀ z h, m.canonicalOf z = some h → m3.canonicalOf z = some h := by
    intro z h hz
    rw [hcan z]
    by_cases he : z = y
    · subst he; rw [hc] at hz; cases hz
    · simp only [he, ↓reduceIte]; exact hz
  have hSnapSlot : ∀ w z sl, SnapSlot S0 db m w z sl → SnapSlot S0 db m3 w z sl := by
    intro w z sl hs
    unfold SnapSlot at hs ⊢
    rw [hs3]
    rcases hs with hs | hs | ⟨h', o', hsl, ho', hn, hcc'⟩
    · exact Or.inl hs
    · exact Or.inr (Or.inl hs)
    · obtain ⟨o'', ho'', e1, e2, e3⟩ := hup h' o' ho'
      refine Or.inr (Or.inr ⟨h', o'', hsl, ho'', by rw [e1, hn], ?_⟩)
      rcases hcc' with hcc' | ⟨p, hp, hle⟩
      · exact Or.inl (e3 hcc')
      · exact Or.inr ⟨p, by rw [e2, hp], hle⟩
  have hSlotInv : ∀ o z sl, SlotInv S0 db m o z sl → SlotInv S0 db m3 o z sl := by
    intro o z sl hs
    refine ⟨fun hz => by rw [hslotRef]; exact hs.1 hz, fun hz => ?_⟩
    rcases hs.2 hz with ⟨h', hsl, hcz⟩ | h2
    · exact Or.inl ⟨h', hsl, hcanUp z h' hcz⟩
    · exact Or.inr h2
  have hLiveInv : ∀ z sl, LiveInv S0 db m z sl → LiveInv S0 db m3 z sl := by
    intro z sl hs
    refine ⟨fun hz => ?_, fun hz => by rw [hslotRef]; exact hs.2 hz⟩
    obtain ⟨h', hsl, hcz⟩ := hs.1 hz
    exact ⟨h', hsl, hcanUp z h' hcz⟩
  have hroot1 : m.root ≠ h1 := by
    intro he
    obtain ⟨o, ho, hco, -⟩ := hm.root
    rw [he, ho1, Option.some.injEq] at ho
    subst ho
    rw [hnc] at hco; cases hco
  refine ⟨hm.len, hm.pre, hm.sEq, ?_, nodup_setObj_keys m h1 o1c hm.objNodup, ?_,
    setTable_nodup _ _ _ hm.tblNodup, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h hh
    rw [hobj]
    have : h ≠ h1 := by
      intro he; subst he; rw [hm.fresh _ hh] at ho1; cases ho1
    simp only [this, ↓reduceIte]
    exact hm.fresh h hh
  · obtain ⟨o, ho, hco, hn⟩ := hm.root
    refine ⟨o, ?_, hco, hn⟩
    show m3.obj? m.root = some o
    rw [hobj]; simp only [hroot1, ↓reduceIte]; exact ho
  · intro z h ht
    rw [htab] at ht
    split at ht
    · rename_i hz; subst hz
      simp only [Option.some.injEq] at ht
      subst ht
      exact ⟨o1c, by rw [hobj]; simp, hn1⟩
    · rename_i hz
      obtain ⟨o, ho, hn⟩ := hm.tbl z h ht
      obtain ⟨o', ho', e1, -⟩ := hup h o ho
      exact ⟨o', ho', by rw [e1, hn]⟩
  · intro h o ho z h' hz
    have hsl : ∃ o0, m.obj? h = some o0 ∧ o0.slot? z = some (Slot.mem h') := by
      rcases hcases h o ho with ⟨rfl, rfl⟩ | ⟨-, ho⟩
      · exact ⟨o1, ho1, hz⟩
      · exact ⟨o, ho, hz⟩
    obtain ⟨o0, ho0, hz0⟩ := hsl
    obtain ⟨o2, ho2, hn2⟩ := hm.slotsNode h o0 ho0 z h' hz0
    obtain ⟨o3, ho3, e1, -⟩ := hup h' o2 ho2
    exact ⟨o3, ho3, by rw [e1, hn2]⟩
  · intro z h ht
    rw [htab] at ht
    split at ht
    · simp only [Option.some.injEq] at ht
      subst ht
      exact ⟨o1c, by rw [hobj]; simp, rfl⟩
    · obtain ⟨o, ho, hco⟩ := hm.tblCanon z h ht
      obtain ⟨o', ho', -, -, e3⟩ := hup h o ho
      exact ⟨o', ho', e3 hco⟩
  · intro h o ho hco
    rcases hcases h o ho with ⟨rfl, rfl⟩ | ⟨hne, ho⟩
    · rw [htab]; simp [o1c, hn1]
    · have ht := hm.canonTbl h o ho hco
      have hny : o.node ≠ y := by
        intro he
        have := hm.canonicalOf_of ho hco
        rw [he, hc] at this; cases this
      rw [htab]; simp only [hny, ↓reduceIte]; exact ht
  · intro h o ho hco
    rcases hcases h o ho with ⟨rfl, rfl⟩ | ⟨-, ho⟩
    · obtain ⟨n, hn, e1, e2, e3⟩ := hcc
      exact ⟨n, by simp only [o1c, hn1]; exact hn, e1, e2, e3⟩
    · exact hm.cc h o ho hco
  · intro z h o hz ho
    rw [hcan] at hz
    split at hz
    · rename_i he; subst he
      simp only [Option.some.injEq] at hz
      subst hz
      rw [hobj] at ho
      simp only [↓reduceIte, Option.some.injEq] at ho
      subst ho
      show o1.pos = _
      rw [hpos1, lv_building]; rfl
    · rcases hcases h o ho with ⟨rfl, rfl⟩ | ⟨-, ho⟩
      · obtain ⟨o2, ho2, hc2, -⟩ := hm.obj_of_canonicalOf hz
        rw [ho1, Option.some.injEq] at ho2; subst ho2
        rw [hnc] at hc2; cases hc2
      · exact hm.pos z h o hz ho
  · intro z hz
    rw [hcan]
    split
    · rfl
    · exact hm.dCanon z hz
  · intro h o ho hco
    rcases hcases h o ho with ⟨rfl, rfl⟩ | ⟨-, ho⟩
    · simp [o1c] at hco
    · obtain ⟨r, w, e1, e2, e3, e4, e5, e6, e7⟩ := hm.snap h o ho hco
      exact ⟨r, w, e1, e2, e3, e4, e5, e6, fun z sl hz => hSnapSlot w z sl (e7 z sl hz)⟩
  · intro h o ho hr z hz
    rcases hcases h o ho with ⟨rfl, rfl⟩ | ⟨-, ho⟩
    · obtain ⟨sl, hsl, hzD, hval⟩ := hslots1 z hz
      refine ⟨sl, hsl, fun _ => by rw [hslotRef]; exact hval, fun h => ?_⟩
      rw [hzD] at h; cases h
    · obtain ⟨sl, hsl, hi⟩ := hm.slots h o ho hr z hz
      exact ⟨sl, hsl, hSlotInv o z sl hi⟩
  · intro h o ho hco hr z hz
    rcases hcases h o ho with ⟨rfl, rfl⟩ | ⟨-, ho⟩
    · obtain ⟨sl, hsl, hzD, hval⟩ := hslots1 z (mem_pointees_of_live' hls hz)
      refine ⟨sl, hsl, fun h => ?_, fun _ => by rw [hslotRef]; exact hval⟩
      rw [hzD] at h; cases h
    · obtain ⟨sl, hsl, hi⟩ := hm.live h o ho hco hr z hz
      exact ⟨sl, hsl, hLiveInv z sl hi⟩

end Promote

/-! ## The writer's follow -/

/-- What the writer's follow of the slot of object hp for y leaves, from m to m':
y's canonical object h', named by that slot; the canonical objects of m stay;
every object of m stays, with its node, history, level, kind and position, still
canonical if it was, and with its other slots. -/
structure WFollow (m m' : Mem V) (hp : Nat) (y : NodeId) (h' : Nat) : Prop where
  can : m'.canonicalOf y = some h'
  slot : ∃ op', m'.obj? hp = some op' ∧ op'.slot? y = some (Slot.mem h')
  mono : ∀ z h, m.canonicalOf z = some h → m'.canonicalOf z = some h
  frame : ∀ h o, m.obj? h = some o → ∃ o', m'.obj? h = some o' ∧ o'.node = o.node ∧
    o'.hist = o.hist ∧ o'.level = o.level ∧ o'.isData = o.isData ∧ o'.pos = o.pos ∧
    (o.canonical = true → o'.canonical = true) ∧ ∀ z, (h ≠ hp ∨ z ≠ y) → o'.slot? z = o.slot? z

/-- The frame of an object kept as it is. -/
theorem frame_refl {o : Obj V} : o.node = o.node ∧ o.hist = o.hist ∧ o.level = o.level ∧
    o.isData = o.isData ∧ o.pos = o.pos ∧ (o.canonical = true → o.canonical = true) :=
  ⟨rfl, rfl, rfl, rfl, rfl, id⟩

theorem obj_with_canonical_true {o : Obj V} (h : o.canonical = true) : { o with canonical := true } = o := by
  cases o; simp only at h; subst h; rfl

section Writer

variable {sp : Spec V T} {db : DB V T} {S0 : Stream V T} {k : Nat} {m : Mem V}

/-- Promotion after the writer's follow: the slot of hp (the canonical object of a
current node) for its live child y names object h1 of y. -/
theorem EInv.promote_step (hinv : Inv sp db k) (hls : LiveSub sp) (hev : EvLogic sp db k)
    (hm : EInv sp db S0 k m) {hp : Nat} {op : Obj V} (hop : m.obj? hp = some op)
    (hco : op.canonical = true) (hr : reachable sp db.P k op.node = true) {y : NodeId}
    (hy : y ∈ sp.live op.hist) (hyw : written sp y = true) (hry : reachable sp db.P k y = true)
    (hyne : y ≠ op.node) {h1 : Nat} (hsl : op.slot? y = some (Slot.mem h1)) :
    EInv sp db S0 k (m.promote hp y h1).1 ∧ WFollow m (m.promote hp y h1).1 hp y (m.promote hp y h1).2 := by
  obtain ⟨o1, ho1, hn1⟩ := hm.slotsNode hp op hop y h1 hsl
  have hp1 : hp ≠ h1 := by
    intro he; subst he; rw [hop, Option.some.injEq] at ho1; subst ho1; exact hyne hn1.symm
  cases hc : m.canonicalOf y with
  | some h0 =>
    obtain ⟨o0, ho0, hc0, hn0⟩ := hm.obj_of_canonicalOf hc
    have hpe : m.promote hp y h1 = (match ((m.setObj h0 { o0 with canonical := true }).setTable y h0).obj? hp with
        | some op3 => ((m.setObj h0 { o0 with canonical := true }).setTable y h0).setObj hp
            (op3.setSlot y (Slot.mem h0))
        | none => (m.setObj h0 { o0 with canonical := true }).setTable y h0, h0) := by
      unfold Mem.promote; simp only [hc, Option.getD_some, ho0]; rfl
    rw [hpe, obj_with_canonical_true hc0]
    rw [obj_with_canonical_true hc0] at hpe
    -- The node table and the object were y's already.
    have ht0 : m.tableOf y = some h0 := ((m.canonicalOf_eq_some y h0).mp hc).1
    have hsame : m.Same ((m.setObj h0 o0).setTable y h0) := by
      refine ⟨fun h => ?_, fun z => ?_, rfl, rfl, rfl⟩
      · show (m.setObj h0 o0).obj? h = m.obj? h
        rw [Mem.obj?_setObj]; split
        · rename_i he; subst he; exact ho0.symm
        · rfl
      · rw [Mem.tableOf_setTable, Mem.tableOf_setObj]; split
        · rename_i he; subst he; exact ht0.symm
        · rfl
    have hm3 := hm.same hsame (setTable_nodup _ _ _ hm.tblNodup) (nodup_setObj_keys m h0 o0 hm.objNodup)
    have hop3 : ((m.setObj h0 o0).setTable y h0).obj? hp = some op := by rw [hsame.1]; exact hop
    simp only [hop3]
    have hc3 : ((m.setObj h0 o0).setTable y h0).canonicalOf y = some h0 := by rw [hsame.canonicalOf]; exact hc
    refine ⟨hm3.setSlot_canon hop3 hsl hc3, ?_, ?_, ?_, ?_⟩
    · rw [(setObj_sameCore _ hop3 (setSlot_core op y _)).canonicalOf]; exact hc3
    · refine ⟨op.setSlot y (Slot.mem h0), Mem.obj?_setObj_self _ _ _, ?_⟩
      rw [slot?_setSlot_of hsl]; simp
    · intro z h hz
      rw [(setObj_sameCore _ hop3 (setSlot_core op y _)).canonicalOf, hsame.canonicalOf]; exact hz
    · intro h o ho
      rw [Mem.obj?_setObj]
      split
      · rename_i he; subst he
        rw [hop, Option.some.injEq] at ho; subst ho
        refine ⟨op.setSlot y (Slot.mem h0), rfl, rfl, rfl, rfl, rfl, rfl, id, fun z hz => ?_⟩
        rw [slot?_setSlot_of hsl]
        rcases hz with hz | hz
        · exact absurd rfl hz
        · simp [hz]
      · rw [hsame.1]
        exact ⟨o, ho, rfl, rfl, rfl, rfl, rfl, id, fun _ _ => rfl⟩
  | none =>
    have hnc : o1.canonical = false := by
      cases hc1 : o1.canonical with
      | false => rfl
      | true =>
        have := hm.canonicalOf_of ho1 hc1
        rw [hn1, hc] at this; cases this
    have hyD : inD db.D y = false := by
      cases hyd : inD db.D y with
      | false => rfl
      | true => have := hm.dCanon y hyd; rw [hc] at this; cases this
    -- The object reached: the snapshot of y's latest version.
    obtain ⟨sl', hsl', hli⟩ := hm.live hp op hop hco hr y hy
    rw [hsl, Option.some.injEq] at hsl'
    subst hsl'
    have hpos1 : o1.pos = (db.S.lv y).map (·.recNo) := by
      have := hli.2 hyD
      simp only [slotRefOf, ho1, Option.bind_some] at this
      exact this
    obtain ⟨n, hn, hvh⟩ : ∃ n, db.P.get? y = some n ∧ True := by
      obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp (Reach.isSome ((reachable_iff _ _ _ _).mp hry))
      exact ⟨n, hn, trivial⟩
    obtain ⟨v, hv, hvhist, hvlev, hvdat⟩ := hinv.lv_whole hn hyw hyD hry
    obtain ⟨r1, w1, e1, e2, e3, e4, e5, e6, e7⟩ := hm.snap h1 o1 ho1 hnc
    have hw1 : w1 = v := by
      rw [hpos1, hv] at e1
      simp only [Option.map_some, Option.some.injEq] at e1
      rw [← e1, hn1, hinv.lv_at hv, Option.some.injEq] at e2
      exact e2.symm
    subst hw1
    have hcc : ∃ n, db.P.get? y = some n ∧ o1.hist = n.hist ∧ o1.level = n.level ∧ o1.isData = n.isData :=
      ⟨n, hn, by rw [e3, hvhist], by rw [e4, hvlev], by rw [e5, hvdat]⟩
    have hclean := hev.clean y n hyw hry hn hyD
    have hslots1 : ∀ z ∈ pointees sp o1.hist, ∃ sl, o1.slot? z = some sl ∧ inD db.D z = false ∧
        slotRefOf S0 m z sl = (db.S.lv z).map (·.recNo) := by
      intro z hz
      have hz' : z ∈ pointees sp n.hist := by rw [← hvhist, ← e3]; exact hz
      obtain ⟨hzD, v', hv', href⟩ := hclean z hz'
      rw [hv, Option.some.injEq] at hv'
      subst hv'
      obtain ⟨sl, hsl1⟩ := Option.isSome_iff_exists.mp (e6 z hz)
      exact ⟨sl, hsl1, hzD, hm.snapSlot_clean hinv (e7 z sl hsl1) href⟩
    have hm3 := hm.promote_new hls hc ho1 hn1 hnc hcc hpos1 hslots1
    have hpe : m.promote hp y h1 = (match ((m.setObj h1 { o1 with canonical := true }).setTable y h1).obj? hp with
        | some op3 => ((m.setObj h1 { o1 with canonical := true }).setTable y h1).setObj hp
            (op3.setSlot y (Slot.mem h1))
        | none => (m.setObj h1 { o1 with canonical := true }).setTable y h1, h1) := by
      unfold Mem.promote; simp only [hc, Option.getD_none, ho1]; rfl
    rw [hpe]
    have hop3 : ((m.setObj h1 { o1 with canonical := true }).setTable y h1).obj? hp = some op := by
      rw [Mem.obj?_setTable, Mem.obj?_setObj]; simp only [hp1, ↓reduceIte]; exact hop
    simp only [hop3]
    have hss : ∀ z, (op.setSlot y (Slot.mem h1)).slot? z = op.slot? z := by
      intro z; rw [slot?_setSlot_of hsl]; split
      · rename_i hz; subst hz; rw [hsl]
      · rfl
    have hcan3 : ∀ z, ((m.setObj h1 { o1 with canonical := true }).setTable y h1).canonicalOf z =
        if z = y then some h1 else m.canonicalOf z := by
      intro z
      unfold Mem.canonicalOf
      rw [Mem.tableOf_setTable, Mem.tableOf_setObj]
      by_cases hz : z = y
      · simp only [hz, ↓reduceIte, Mem.obj?_setTable, Mem.obj?_setObj_self]
      · simp only [hz, ↓reduceIte]
        cases ht : m.tableOf z with
        | none => rfl
        | some h =>
          have hh1 : h ≠ h1 := by
            intro he; subst he
            obtain ⟨o, ho, hno⟩ := hm.tbl z h ht
            rw [ho1, Option.some.injEq] at ho; subst ho
            exact hz (hno.symm.trans hn1)
          simp only [Mem.obj?_setTable, Mem.obj?_setObj, hh1, ↓reduceIte]
    have hsc := setObj_sameCore ((m.setObj h1 { o1 with canonical := true }).setTable y h1) hop3
      (setSlot_core op y (Slot.mem h1))
    refine ⟨hm3.setObj_sameSlots hop3 (setSlot_core op y _) hss, ?_, ?_, ?_, ?_⟩
    · rw [hsc.canonicalOf, hcan3]; simp
    · exact ⟨op.setSlot y (Slot.mem h1), Mem.obj?_setObj_self _ _ _, by rw [hss]; exact hsl⟩
    · intro z h hz
      rw [hsc.canonicalOf, hcan3]
      split
      · rename_i he; subst he; rw [hc] at hz; cases hz
      · exact hz
    · intro h o ho
      rw [Mem.obj?_setObj]
      split
      · rename_i he; subst he
        rw [hop, Option.some.injEq] at ho; subst ho
        exact ⟨op.setSlot y (Slot.mem h1), rfl, rfl, rfl, rfl, rfl, rfl, id, fun z _ => hss z⟩
      · rw [Mem.obj?_setTable, Mem.obj?_setObj]
        split
        · rename_i he; subst he
          rw [ho1, Option.some.injEq] at ho; subst ho
          exact ⟨_, rfl, rfl, rfl, rfl, rfl, rfl, fun _ => rfl, fun _ _ => rfl⟩
        · exact ⟨o, ho, rfl, rfl, rfl, rfl, rfl, id, fun _ _ => rfl⟩

/-- The memory after the follow, before the promotion: objects keep their cores,
and their slots but hp's for y, which names h1; the canonical objects stay. -/
theorem EInv.reached4_frame (hm : EInv sp db S0 k m) {hp : Nat} {op : Obj V}
    (hop : m.obj? hp = some op) {y : NodeId} {m1 : Mem V} {h1 : Nat}
    (h : m.reached4 sp S0 db.S hp y = some (m1, h1)) :
    (m1.swz hp y h1).obj? hp = some (op.setSlot y (Slot.mem h1)) ∧
    (∀ z, (m1.swz hp y h1).canonicalOf z = m.canonicalOf z) ∧
    ∀ h o, m.obj? h = some o → ∃ o', (m1.swz hp y h1).obj? h = some o' ∧ o'.node = o.node ∧
      o'.hist = o.hist ∧ o'.level = o.level ∧ o'.isData = o.isData ∧ o'.pos = o.pos ∧
      (o.canonical = true → o'.canonical = true) ∧ ∀ z, (h ≠ hp ∨ z ≠ y) → o'.slot? z = o.slot? z := by
  obtain ⟨op0, sl, hop0, hsl, hcase⟩ := reached4_cases h
  rw [hop, Option.some.injEq] at hop0
  subst hop0
  -- In every case, m1 has m's objects (and maybe a new one) and m's canonical objects.
  have hm1 : (∀ h o, m.obj? h = some o → m1.obj? h = some o) ∧ (∀ z, m1.canonicalOf z = m.canonicalOf z) := by
    rcases hcase with ⟨-, rfl, -⟩ | ⟨r, -, -, rfl⟩ | ⟨r, r', w, -, -, -, -, rfl, -⟩
    · exact ⟨fun _ _ h => h, fun _ => rfl⟩
    · exact ⟨fun _ _ h => h, fun _ => rfl⟩
    · refine ⟨fun h o ho => ?_, fun z => ?_⟩
      · rw [Mem.obj?_addObj]
        have : h ≠ m.next := by
          intro he; subst he; rw [hm.fresh _ (Nat.le_refl _)] at ho; cases ho
        simp only [this, ↓reduceIte]; exact ho
      · unfold Mem.canonicalOf
        rw [Mem.tableOf_addObj]
        cases ht : m.tableOf z with
        | none => rfl
        | some h' =>
          obtain ⟨o', ho', -⟩ := hm.tbl z h' ht
          have : h' ≠ m.next := by
            intro he; subst he; rw [hm.fresh _ (Nat.le_refl _)] at ho'; cases ho'
          simp only [Mem.obj?_addObj, this, ↓reduceIte]
  have hop1 := hm1.1 hp op hop
  unfold Mem.swz
  rw [hop1]
  have hsc := setObj_sameCore m1 hop1 (setSlot_core op y (Slot.mem h1))
  refine ⟨Mem.obj?_setObj_self _ _ _, fun z => by rw [hsc.canonicalOf, hm1.2], fun h o ho => ?_⟩
  rw [Mem.obj?_setObj]
  split
  · rename_i he; subst he
    rw [hop, Option.some.injEq] at ho; subst ho
    refine ⟨op.setSlot y (Slot.mem h1), rfl, rfl, rfl, rfl, rfl, rfl, id, fun z hz => ?_⟩
    rw [slot?_setSlot_of hsl]
    rcases hz with hz | hz
    · exact absurd rfl hz
    · simp [hz]
  · exact ⟨o, hm1.1 h o ho, rfl, rfl, rfl, rfl, rfl, id, fun _ _ => rfl⟩

/-- The writer's follow of a live slot of the canonical object of a current node
keeps the invariant, and leaves the slot naming the child's canonical object. -/
theorem EInv.follow4_writer (hinv : Inv sp db k) (hls : LiveSub sp) (hev : EvLogic sp db k)
    (hm : EInv sp db S0 k m) {hp : Nat} {op : Obj V} (hop : m.obj? hp = some op)
    (hco : op.canonical = true) (hr : reachable sp db.P k op.node = true) {y : NodeId}
    (hy : y ∈ sp.live op.hist) :
    EInv sp db S0 k (m.follow4 sp S0 db.S hp y true).1 ∧
      ∃ h', (m.follow4 sp S0 db.S hp y true).2 = some h' ∧
        WFollow m (m.follow4 sp S0 db.S hp y true).1 hp y h' := by
  -- y: a live child at k, so a current written node below op's.
  obtain ⟨n, hn, hhist, -, -⟩ := hm.cc hp op hop hco
  have hy' : y ∈ sp.live (n.hist.upTo k) := by
    rw [upTo_of_forall _ _ (hinv.times _ n hn), ← hhist]; exact hy
  obtain ⟨e, he, hye⟩ := hls _ _ hy'
  obtain ⟨ny, hny, hlt⟩ := hinv.ptrs op.node n hn e (mem_upTo.mp he).1 y hye
  have hyroot : y ≠ SIS.root := hinv.ptr_ne_root hn (mem_upTo.mp he).1 hye
  have hyw : written sp y = true := written_of_ne_root sp hyroot
  have hry : reachable sp db.P k y = true := by
    rw [reachable_iff] at hr ⊢; exact Reach.child hr hn hy' hny hlt
  have hyne : y ≠ op.node := by
    intro he; rw [he, hn, Option.some.injEq] at hny; subst hny; omega
  obtain ⟨sl, hsl, hli⟩ := hm.live hp op hop hco hr y hy
  -- The follow reaches an object.
  have hreach : ∃ m1 h1, m.reached4 sp S0 db.S hp y = some (m1, h1) := by
    unfold Mem.reached4
    rw [hop]
    simp only [Option.bind_some, hsl]
    cases sl with
    | mem h =>
      obtain ⟨o, ho, -⟩ := hm.slotsNode hp op hop y h hsl
      simp only [ho, Option.isSome_some, ↓reduceIte]
      exact ⟨m, h, rfl⟩
    | stream r =>
      simp only
      cases hc : m.canonicalOf y with
      | some h0 => exact ⟨m, h0, rfl⟩
      | none =>
        have hyD : inD db.D y = false := by
          cases hyd : inD db.D y with
          | false => rfl
          | true => have := hm.dCanon y hyd; rw [hc] at this; cases this
        have h2 := hli.2 hyD
        simp only [slotRefOf] at h2
        obtain ⟨v, hv, -⟩ := hinv.lv_whole hny hyw hyD hry
        rw [hv] at h2
        simp only [Option.map_some] at h2
        simp only [h2, hinv.lv_at hv]
        exact ⟨_, _, rfl⟩
  obtain ⟨m1, h1, hrc⟩ := hreach
  obtain ⟨hop2, hcan2, hfr2⟩ := hm.reached4_frame hop hrc
  have hm2 := hm.reached4 hinv hrc
  rw [follow4_eq, hrc]
  simp only [↓reduceIte]
  have hsl2 : (op.setSlot y (Slot.mem h1)).slot? y = some (Slot.mem h1) := by
    rw [slot?_setSlot_of hsl]; simp
  obtain ⟨hm4, hwf⟩ := hm2.promote_step hinv hls hev hop2 hco hr hy hyw hry hyne hsl2
  refine ⟨hm4, _, rfl, hwf.can, hwf.slot, fun z h hz => hwf.mono z h (by rw [hcan2]; exact hz),
    fun h o ho => ?_⟩
  obtain ⟨o2, ho2, f1, f2, f3, f4, f5, f6, f7⟩ := hfr2 h o ho
  obtain ⟨o3, ho3, g1, g2, g3, g4, g5, g6, g7⟩ := hwf.frame h o2 ho2
  exact ⟨o3, ho3, by rw [g1, f1], by rw [g2, f2], by rw [g3, f3], by rw [g4, f4], by rw [g5, f5],
    fun hc => g6 (f6 hc), fun z hz => by rw [g7 z hz, f7 z hz]⟩

end Writer

end SIS
