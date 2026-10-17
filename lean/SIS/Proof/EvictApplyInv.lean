/-
Proofs for stage 2 (bergdb item 001, WP E3), part 9: after the writer's paths,
the change applied to the canonical objects gives `AInv`.
-/
import SIS.Proof.EvictApply

set_option linter.unusedSectionVars false

namespace SIS

variable {V T : Type} [DecidableEq V]

theorem pointees_append_mem {sp : Spec V T} {h1 h2 : History V} {y : NodeId}
    (hy : y ∈ pointees sp (h1 ++ h2)) : y ∈ pointees sp h1 ∨ y ∈ pointees sp h2 := by
  rw [mem_pointees] at hy
  obtain ⟨e, he, hye⟩ := hy
  rcases List.mem_append.mp he with he | he
  · exact Or.inl ((mem_pointees sp h1 y).mpr ⟨e, he, hye⟩)
  · exact Or.inr ((mem_pointees sp h2 y).mpr ⟨e, he, hye⟩)

theorem pointees_adds_mem {sp : Spec V T} {L : List (NodeId × V)} {j : Time} {y : NodeId}
    (hy : y ∈ pointees sp (L.map (fun a => (⟨j, a.2⟩ : Entry V)))) :
    ∃ a ∈ L, y ∈ sp.ptrs a.2 := by
  rw [mem_pointees] at hy
  obtain ⟨e, he, hye⟩ := hy
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp he
  exact ⟨a, ha, hye⟩

section ApplyInv

variable {sp : Spec V T} {db : DB V T} {S0 : Stream V T} {k : Nat} {m : Mem V} {c : Changes V}

/-- The change applied after the writer's paths, from the memory m1 after the new
nodes' objects to the memory m3 after the adds: `AInv`. -/
theorem EInv.applyChange4_core (hinv : Inv sp db k) (hls : LiveSub sp) (hm : EInv sp db S0 k m)
    {path : List NodeId} (hpd : ∀ x ∈ path, PathDone sp db.P k path m x)
    (hpr : ∀ p ∈ path, reachable sp db.P k p = true) (hpn : ∀ p ∈ path, (db.P.get? p).isSome)
    (hstep : StepOK sp db.P (k + 1) c) (hphys : PhysStep sp db.P (k + 1) c) (htree : treeAt sp db.P k)
    {m1 m3 : Mem V} (haf : AddFacts m m1 c) (hcf : ChangeFacts sp db.P (k + 1) c m1 m3)
    (hfilt : ∀ {x h}, m1.canonicalOf x = some h →
      c.adds.filter (fun a => m1.canonicalOf a.1 == some h) = c.adds.filter (fun a => a.1 == x))
    (hcopyNS : ∀ a ∈ c.adds, ∀ y ∈ sp.ptrs a.2, (NS4 sp db.P (k + 1) m1 y).isSome)
    (hgood : ∀ {y sl}, NS4 sp db.P (k + 1) m1 y = some sl →
      (∃ h', sl = Slot.mem h' ∧ m1.canonicalOf y = some h') ∨
      (m1.canonicalOf y = none ∧ inD db.D y = false ∧ y ∉ c.new.map (·.id) ∧
        slotRefOf S0 m y sl = (db.S.lv y).map (·.recNo) ∧
        ∃ h0 o0, m.obj? h0 = some o0 ∧ o0.slot? y = some sl)) :
    AInv sp db S0 k c path m3 := by
  have hK1 : k + 1 - 1 = k := by omega
  have hcan3 := hcf.canonicalOf
  have htab3 : ∀ y, m3.tableOf y = m1.tableOf y := by intro y; unfold Mem.tableOf; rw [hcf.table]
  -- Old objects stay, with their adds.
  have hold3 : ∀ h o, m.obj? h = some o → m3.obj? h = some (updAll4 sp db.P (k + 1) m1
      (c.adds.filter (fun a => m1.canonicalOf a.1 == some h)) o) := by
    intro h o ho
    rw [hcf.obj h, haf.old h (lt_next_of_obj? hm.fresh ho), ho]; rfl
  have hnotnew : ∀ y n, db.P.get? y = some n → y ∉ c.new.map (·.id) := fun y n hn => not_new_of_get? hstep hn
  have hfilt_old : ∀ h o, m.obj? h = some o →
      c.adds.filter (fun a => m1.canonicalOf a.1 == some h) =
        if o.canonical then c.adds.filter (fun a => a.1 == o.node) else [] := by
    intro h o ho
    cases hco : o.canonical with
    | true =>
      simp only [↓reduceIte]
      apply hfilt
      obtain ⟨n, hn', -⟩ := hm.cc h o ho hco
      rw [haf.canOld o.node (hnotnew _ _ hn')]
      exact hm.canonicalOf_of ho hco
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      apply List.filter_eq_nil_iff.mpr
      intro a _ ha
      simp only [beq_iff_eq] at ha
      obtain ⟨-, o', ho', hc'⟩ := (m1.canonicalOf_eq_some a.1 h).mp ha
      rw [haf.old h (lt_next_of_obj? hm.fresh ho), ho, Option.some.injEq] at ho'
      subst ho'
      rw [hco] at hc'; cases hc'
  -- The objects of m3: an old snapshot, an old canonical object with its node's adds, or
  -- a new node's object with its adds.
  have hcls : ∀ h o3, m3.obj? h = some o3 →
      (∃ o, m.obj? h = some o ∧ ((o.canonical = false ∧ o3 = o) ∨
        (o.canonical = true ∧ o3 = updAll4 sp db.P (k + 1) m1 (c.adds.filter (fun a => a.1 == o.node)) o))) ∨
      (m.next ≤ h ∧ ∃ nn ∈ c.new, m1.canonicalOf nn.id = some h ∧ m1.obj? h = some (newObj nn) ∧
        o3 = updAll4 sp db.P (k + 1) m1 (c.adds.filter (fun a => a.1 == nn.id)) (newObj nn)) := by
    intro h o3 ho3
    rw [hcf.obj h] at ho3
    cases h1 : m1.obj? h with
    | none => rw [h1] at ho3; cases ho3
    | some o1 =>
      rw [h1] at ho3
      simp only [Option.map_some, Option.some.injEq] at ho3
      rcases haf.cls h o1 h1 with ⟨-, h2⟩ | ⟨hle, nn, hnn, hon, ht⟩
      · left
        refine ⟨o1, h2, ?_⟩
        rw [hfilt_old h o1 h2] at ho3
        cases hco : o1.canonical with
        | false =>
          left
          rw [hco] at ho3
          simp only [Bool.false_eq_true, ↓reduceIte] at ho3
          exact ⟨rfl, by rw [← ho3]; rfl⟩
        | true =>
          right
          rw [hco] at ho3
          simp only [↓reduceIte] at ho3
          exact ⟨rfl, ho3.symm⟩
      · right
        have hc : m1.canonicalOf nn.id = some h := (m1.canonicalOf_eq_some nn.id h).mpr
          ⟨ht, o1, h1, by rw [hon]; rfl⟩
        rw [hfilt hc, hon] at ho3
        exact ⟨hle, nn, hnn, hc, by rw [hon], ho3.symm⟩
  -- Every object of m keeps its node, kind, level and position.
  have hkeep : ∀ h o, m.obj? h = some o → ∃ o3, m3.obj? h = some o3 ∧ o3.node = o.node ∧
      o3.level = o.level ∧ o3.isData = o.isData ∧ o3.canonical = o.canonical ∧ o3.pos = o.pos := by
    intro h o ho
    obtain ⟨a1, a2, a3, -, a5, a6⟩ := updAll4_core sp db.P (k + 1) m1
      (c.adds.filter (fun a => m1.canonicalOf a.1 == some h)) o
    exact ⟨_, hold3 h o ho, a1, a2, a3, a5, a6⟩
  -- The canonical objects of m1.
  have hcan1 : ∀ y h, m1.canonicalOf y = some h →
      (y ∉ c.new.map (·.id) ∧ m.canonicalOf y = some h) ∨
      (∃ nn ∈ c.new, nn.id = y ∧ m1.obj? h = some (newObj nn)) := by
    intro y h hy
    by_cases hyn : y ∈ c.new.map (·.id)
    · obtain ⟨nn, hnn, hid⟩ := List.mem_map.mp hyn
      obtain ⟨h', -, hc', ho'⟩ := haf.canNew nn hnn
      rw [hid, hy, Option.some.injEq] at hc'
      subst hc'
      exact Or.inr ⟨nn, hnn, hid, ho'⟩
    · left; exact ⟨hyn, by rw [← haf.canOld y hyn]; exact hy⟩
  -- The position of a canonical object of m1 in m3: its node's latest version, before.
  have hposc : ∀ y h, m1.canonicalOf y = some h →
      (m3.obj? h).bind (·.pos) = (db.S.lv y).map (·.recNo) := by
    intro y h hy
    rcases hcan1 y h hy with ⟨-, hc⟩ | ⟨nn, hnn, hid, ho1⟩
    · obtain ⟨o, ho, -, -⟩ := hm.obj_of_canonicalOf hc
      obtain ⟨o3, ho3, -, -, -, -, hp3⟩ := hkeep h o ho
      rw [ho3]; simp only [Option.bind_some, hp3]
      exact hm.pos.lv0 hc ho
    · rw [hcf.obj h, ho1]
      simp only [Option.map_some, Option.bind_some, (updAll4_core sp db.P (k + 1) _ _ _).2.2.2.2.2]
      simp only [newObj]
      cases hl : db.S.lv y with
      | none => rfl
      | some v =>
        exfalso
        obtain ⟨-, -, n, hn, -⟩ := hinv.version_node (hinv.lv_at hl)
        exact hnotnew y n hn (by rw [← hid]; exact List.mem_map.mpr ⟨nn, hnn, rfl⟩)
  -- The serialized reference of a slot of m: the same in m3.
  have hsref : ∀ h0 o0, m.obj? h0 = some o0 → ∀ z sl, o0.slot? z = some sl →
      slotRefOf S0 m3 z sl = slotRefOf S0 m z sl := by
    intro h0 o0 ho0 z sl hz
    cases sl with
    | mem h' =>
      obtain ⟨o', ho', -⟩ := hm.slotsNode h0 o0 ho0 z h' hz
      obtain ⟨o3, ho3, -, -, -, -, hp3⟩ := hkeep h' o' ho'
      simp only [slotRefOf, ho3, ho', Option.bind_some, hp3]
    | stream r => simp only [slotRefOf, hcf.s, haf.s]
  -- The new slot of a pointer, in m3.
  have hns3 : ∀ y sl, NS4 sp db.P (k + 1) m1 y = some sl →
      ((∃ h', sl = Slot.mem h' ∧ m3.canonicalOf y = some h') ∧
        slotRefOf S0 m3 y sl = (db.S.lv y).map (·.recNo)) ∨
      (m3.canonicalOf y = none ∧ inD db.D y = false ∧ y ∉ c.new.map (·.id) ∧
        slotRefOf S0 m3 y sl = (db.S.lv y).map (·.recNo)) := by
    intro y sl hns
    rcases hgood hns with ⟨h', rfl, hc⟩ | ⟨hc, hyD, hyn, hval, h0, o0, ho0, hsl0⟩
    · left
      exact ⟨⟨h', rfl, by rw [hcan3]; exact hc⟩, hposc y h' hc⟩
    · right
      exact ⟨by rw [hcan3]; exact hc, hyD, hyn, by rw [hsref h0 o0 ho0 y sl hsl0]; exact hval⟩
  -- The slots of a canonical object of m3: from the adds (new slots), or as before.
  have hslot_upd : ∀ (L : List (NodeId × V)) (o : Obj V) (z : NodeId), (∀ a ∈ L, a ∈ c.adds) →
      z ∈ L.flatMap (fun a => sp.ptrs a.2) →
      ∃ sl, (updAll4 sp db.P (k + 1) m1 L o).slot? z = some sl ∧ NS4 sp db.P (k + 1) m1 z = some sl := by
    intro L o z hL hz
    obtain ⟨a, ha, hza⟩ := List.mem_flatMap.mp hz
    obtain ⟨sl, hsl⟩ := Option.isSome_iff_exists.mp (hcopyNS a (hL a ha) z hza)
    refine ⟨sl, ?_, hsl⟩
    rw [updAll4_slot]
    simp only [hz, ↓reduceIte]
    unfold combo4; rw [hsl]; rfl
  -- Where a slot of m3 comes from: a slot of an object of m, or a memory slot to a
  -- canonical object of m1.
  have hLadds : ∀ (x : NodeId), ∀ a ∈ c.adds.filter (fun a => a.1 == x), a ∈ c.adds :=
    fun x a ha => (List.mem_filter.mp ha).1
  have hslot3 : ∀ h o3 z sl, m3.obj? h = some o3 → o3.slot? z = some sl →
      (∃ h0 o0, m.obj? h0 = some o0 ∧ o0.slot? z = some sl) ∨
      (∃ h', sl = Slot.mem h' ∧ m1.canonicalOf z = some h') := by
    intro h o3 z sl ho3 hz
    have hupd : ∀ (L : List (NodeId × V)) (o : Obj V), (∀ a ∈ L, a ∈ c.adds) →
        (updAll4 sp db.P (k + 1) m1 L o).slot? z = some sl →
        o.slot? z = some sl ∨ NS4 sp db.P (k + 1) m1 z = some sl := by
      intro L o hL hz'
      by_cases hin : z ∈ L.flatMap (fun a => sp.ptrs a.2)
      · obtain ⟨sl', hsl', hns⟩ := hslot_upd L o z hL hin
        rw [hsl', Option.some.injEq] at hz'
        subst hz'
        exact Or.inr hns
      · rw [updAll4_slot] at hz'
        simp only [hin, ↓reduceIte] at hz'
        exact Or.inl hz'
    have hns_case : NS4 sp db.P (k + 1) m1 z = some sl →
        (∃ h0 o0, m.obj? h0 = some o0 ∧ o0.slot? z = some sl) ∨
        (∃ h', sl = Slot.mem h' ∧ m1.canonicalOf z = some h') := by
      intro hns
      rcases hgood hns with ⟨h', rfl, hc⟩ | ⟨-, -, -, -, h0, o0, ho0, hsl0⟩
      · exact Or.inr ⟨h', rfl, hc⟩
      · exact Or.inl ⟨h0, o0, ho0, hsl0⟩
    rcases hcls h o3 ho3 with ⟨o, ho, ⟨-, rfl⟩ | ⟨-, rfl⟩⟩ | ⟨-, nn, -, -, -, rfl⟩
    · exact Or.inl ⟨h, o3, ho, hz⟩
    · rcases hupd _ o (hLadds o.node) hz with h1 | h1
      · exact Or.inl ⟨h, o, ho, h1⟩
      · exact hns_case h1
    · rcases hupd _ (newObj nn) (hLadds nn.id) hz with h1 | h1
      · simp [newObj, Obj.slot?] at h1
      · exact hns_case h1
  -- A canonical object of m1 is an object of m3, of its node, canonical.
  have hcanobj : ∀ y h, m1.canonicalOf y = some h → ∃ o3, m3.obj? h = some o3 ∧ o3.node = y ∧
      o3.canonical = true := by
    intro y h hy
    rcases hcan1 y h hy with ⟨-, hc⟩ | ⟨nn, hnn, hid, ho1⟩
    · obtain ⟨o, ho, hco, hno⟩ := hm.obj_of_canonicalOf hc
      obtain ⟨o3, ho3, e1, -, -, e5, -⟩ := hkeep h o ho
      exact ⟨o3, ho3, by rw [e1, hno], by rw [e5, hco]⟩
    · rw [hcf.obj h, ho1]
      obtain ⟨a1, -, -, -, a5, -⟩ := updAll4_core sp db.P (k + 1) m1
        (c.adds.filter (fun a => m1.canonicalOf a.1 == some h)) (newObj nn)
      exact ⟨_, rfl, by rw [a1, ← hid]; rfl, by rw [a5]; rfl⟩
  -- CC after the change.
  have hcc3 : ∀ h o3, m3.obj? h = some o3 → o3.canonical = true →
      ∃ n, (db.P.apply (k + 1) c).get? o3.node = some n ∧ o3.hist = n.hist ∧ o3.level = n.level ∧
        o3.isData = n.isData := by
    intro h o3 ho3 hc3
    rcases hcls h o3 ho3 with ⟨o, ho, ⟨hco, rfl⟩ | ⟨hco, rfl⟩⟩ | ⟨-, nn, hnn, -, -, rfl⟩
    · rw [hco] at hc3; cases hc3
    · obtain ⟨n, hn, h1, h2, h3⟩ := hm.cc h o ho hco
      obtain ⟨a1, a2, a3, a4, -, -⟩ := updAll4_core sp db.P (k + 1) m1 (c.adds.filter (fun a => a.1 == o.node)) o
      refine ⟨_, by rw [a1]; exact get?_apply_of_get? hn, ?_, by rw [a2, h2], by rw [a3, h3]⟩
      rw [a4, h1]; rfl
    · obtain ⟨a1, a2, a3, a4, -, -⟩ := updAll4_core sp db.P (k + 1) m1 (c.adds.filter (fun a => a.1 == nn.id))
        (newObj nn)
      obtain ⟨m0, hm0⟩ := Option.isSome_iff_exists.mp (newNodeOf_isSome (V := V) hnn)
      obtain ⟨nn', hnn', hid', hm0e⟩ := newNodeOf_some hm0
      have hnn'' : nn' = nn := new_unique hstep.distinct hnn' hnn hid'
      subst hnn''
      have hget : (db.P.apply (k + 1) c).get? nn'.id = some { m0 with hist := m0.hist ++ addsFor c (k + 1) nn'.id } := by
        rw [get?_apply, hstep.fresh nn' hnn', hm0]; rfl
      refine ⟨_, by rw [a1]; exact hget, ?_, ?_, ?_⟩
      · rw [a4, hm0e]; rfl
      · rw [a2, hm0e]; rfl
      · rw [a3, hm0e]; rfl
  -- Old nodes: P's at k, so not new.
  have hold_node : ∀ h o, m.obj? h = some o → ∃ n, db.P.get? o.node = some n := by
    intro h o ho
    cases hco : o.canonical with
    | true => obtain ⟨n, hn, -⟩ := hm.cc h o ho hco; exact ⟨n, hn⟩
    | false =>
      obtain ⟨r, w, -, hw, -⟩ := hm.snap h o ho hco
      obtain ⟨-, -, n, hn, -⟩ := hinv.version_node hw
      exact ⟨n, hn⟩
  have hpdm : ∀ y ∈ path, m.canonicalOf y ≠ none := by
    intro y hy; obtain ⟨hc, -⟩ := hpd y hy; intro h; rw [h] at hc; cases hc
  have hold_can : ∀ y, y ∉ c.new.map (·.id) → m3.canonicalOf y = m.canonicalOf y := by
    intro y hy; rw [hcan3, haf.canOld y hy]
  -- The histories of P after the change end at k + 1.
  have htimes' : ∀ x n, (db.P.apply (k + 1) c).get? x = some n → ∀ e ∈ n.hist, e.time ≤ k + 1 := by
    intro x n hn e he
    rw [get?_apply] at hn
    cases h0 : db.P.get? x with
    | some n0 =>
      rw [h0] at hn
      simp only [Option.some_or, Option.map_some, Option.some.injEq] at hn
      subst hn
      rcases List.mem_append.mp he with he | he
      · have := hinv.times x n0 h0 e he; omega
      · have := (mem_addsFor.mp he).1; omega
    | none =>
      rw [h0] at hn
      simp only [Option.none_or] at hn
      cases h1 : newNodeOf c x with
      | none => rw [h1] at hn; cases hn
      | some n1 =>
        rw [h1] at hn
        simp only [Option.map_some, Option.some.injEq] at hn
        subst hn
        obtain ⟨nn, -, -, hn1⟩ := newNodeOf_some h1
        subst hn1
        simp only [List.nil_append] at he
        have := (mem_addsFor.mp he).1; omega
  refine ⟨hm.pre, by rw [hcf.s, haf.s]; exact hm.sEq, ?_, hcf.nodup haf.nodup, ?_,
    by rw [hcf.table]; exact haf.tnodup, ?_, ?_, ?_, ?_, hcc3, ?_, ?_, ?_, ?_, ?_⟩
  · -- fresh
    intro h hh
    rw [hcf.obj h, haf.fresh h (by rw [← hcf.next]; exact hh)]; rfl
  · -- root
    obtain ⟨o, ho, hc, hn⟩ := hm.root
    obtain ⟨o3, ho3, e1, -, -, e5, -⟩ := hkeep _ o ho
    exact ⟨o3, by rw [hcf.root, haf.root]; exact ho3, by rw [e5, hc], by rw [e1, hn]⟩
  · -- tbl
    intro y h ht
    rw [htab3] at ht
    by_cases hyn : y ∈ c.new.map (·.id)
    · obtain ⟨nn, hnn, hid⟩ := List.mem_map.mp hyn
      obtain ⟨h', -, hc', -⟩ := haf.canNew nn hnn
      have ht' := ((m1.canonicalOf_eq_some nn.id h').mp hc').1
      rw [hid, ht, Option.some.injEq] at ht'
      subst ht'
      obtain ⟨o3, ho3, hn3, -⟩ := hcanobj y h (by rw [← hid]; exact hc')
      exact ⟨o3, ho3, hn3⟩
    · rw [haf.tabOld y hyn] at ht
      obtain ⟨o, ho, hn⟩ := hm.tbl y h ht
      obtain ⟨o3, ho3, e1, -⟩ := hkeep h o ho
      exact ⟨o3, ho3, by rw [e1, hn]⟩
  · -- slotsNode
    intro h o3 ho3 z h' hz
    rcases hslot3 h o3 z _ ho3 hz with ⟨h0, o0, ho0, hsl0⟩ | ⟨h'', he, hc⟩
    · obtain ⟨o', ho', hn'⟩ := hm.slotsNode h0 o0 ho0 z h' hsl0
      obtain ⟨o3', ho3', e1, -⟩ := hkeep h' o' ho'
      exact ⟨o3', ho3', by rw [e1, hn']⟩
    · simp only [Slot.mem.injEq] at he
      subst he
      obtain ⟨o3', ho3', hn', -⟩ := hcanobj z h' hc
      exact ⟨o3', ho3', hn'⟩
  · -- tblCanon
    intro y h ht
    rw [htab3] at ht
    by_cases hyn : y ∈ c.new.map (·.id)
    · obtain ⟨nn, hnn, hid⟩ := List.mem_map.mp hyn
      obtain ⟨h', -, hc', -⟩ := haf.canNew nn hnn
      have ht' := ((m1.canonicalOf_eq_some nn.id h').mp hc').1
      rw [hid, ht, Option.some.injEq] at ht'
      subst ht'
      obtain ⟨o3, ho3, -, hc3⟩ := hcanobj y h (by rw [← hid]; exact hc')
      exact ⟨o3, ho3, hc3⟩
    · rw [haf.tabOld y hyn] at ht
      obtain ⟨o, ho, hc⟩ := hm.tblCanon y h ht
      obtain ⟨o3, ho3, -, -, -, e5, -⟩ := hkeep h o ho
      exact ⟨o3, ho3, by rw [e5, hc]⟩
  · -- canonTbl
    intro h o3 ho3 hc3
    rcases hcls h o3 ho3 with ⟨o, ho, ⟨hco, rfl⟩ | ⟨hco, rfl⟩⟩ | ⟨-, nn, hnn, hc, -, rfl⟩
    · rw [hco] at hc3; cases hc3
    · obtain ⟨n, hn, -⟩ := hm.cc h o ho hco
      rw [(updAll4_core sp db.P (k + 1) m1 _ o).1, htab3, haf.tabOld o.node (hnotnew _ _ hn)]
      exact hm.canonTbl h o ho hco
    · rw [(updAll4_core sp db.P (k + 1) m1 _ (newObj nn)).1, htab3]
      exact ((m1.canonicalOf_eq_some nn.id h).mp hc).1
  · -- pos
    intro z h o3 hz ho3
    rw [hcan3] at hz
    have := hposc z h hz
    rw [ho3] at this
    simp only [Option.bind_some] at this
    rw [this, lv_building]; rfl
  · -- canon
    intro y hy
    rcases hy with hy | hy | hy
    · obtain ⟨d, hd⟩ := (inD_iff db.D y).mp hy
      have hix := hinv.dIndex (y, d) hd
      simp only [isIndex] at hix
      cases hn : db.P.get? y with
      | none => rw [hn] at hix; cases hix
      | some n => rw [hold_can y (hnotnew y n hn)]; exact hm.dCanon y hy
    · obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp (hpn y hy)
      rw [hold_can y (hnotnew y n hn)]
      obtain ⟨hc, -⟩ := hpd y hy
      exact hc
    · obtain ⟨nn, hnn, hid⟩ := List.mem_map.mp hy
      obtain ⟨h', -, hc', -⟩ := haf.canNew nn hnn
      rw [hcan3, ← hid, hc']; rfl
  · -- snap
    intro h o3 ho3 hc3
    rcases hcls h o3 ho3 with ⟨o, ho, ⟨hco, rfl⟩ | ⟨hco, rfl⟩⟩ | ⟨-, nn, -, -, -, rfl⟩
    · obtain ⟨r, w, e1, e2, e3, e4, e5, e6, e7⟩ := hm.snap h o3 ho hco
      refine ⟨r, w, e1, e2, e3, e4, e5, e6, fun z sl hz => ?_⟩
      have hs := e7 z sl hz
      unfold SnapSlot at hs ⊢
      rw [hcf.s, haf.s]
      rcases hs with hs | hs | ⟨h', o', hsl, ho', hn, hcc'⟩
      · exact Or.inl hs
      · exact Or.inr (Or.inl hs)
      · obtain ⟨o3', ho3', f1, -, -, f5, f6⟩ := hkeep h' o' ho'
        refine Or.inr (Or.inr ⟨h', o3', hsl, ho3', by rw [f1, hn], ?_⟩)
        rw [f5, f6]; exact hcc'
    · rw [(updAll4_core sp db.P (k + 1) m1 _ o).2.2.2.2.1, hco] at hc3; cases hc3
    · rw [(updAll4_core sp db.P (k + 1) m1 _ (newObj nn)).2.2.2.2.1] at hc3; cases hc3
  · -- slots
    intro h o3 ho3 hc3 hw3 hrel3 z hz
    -- The new slot of a pointer, as INV-SLOT asks after the change.
    have hnsok : ∀ sl, NS4 sp db.P (k + 1) m1 z = some sl →
        (inD db.D z = false → slotRefOf S0 m3 z sl = (db.S.lv z).map (·.recNo) ∧
          (z ∈ c.new.map (·.id) → ∃ h', sl = Slot.mem h' ∧ m3.canonicalOf z = some h')) ∧
        (inD db.D z = true → (∃ h', sl = Slot.mem h' ∧ m3.canonicalOf z = some h') ∨
          (inD db.D o3.node = true ∧ ∃ a b, dOf db.D o3.node = some a ∧ dOf db.D z = some b ∧ a ≤ b)) := by
      intro sl hns
      rcases hns3 z sl hns with ⟨⟨h', rfl, hc⟩, hval⟩ | ⟨-, hzD, hzn, hval⟩
      · exact ⟨fun _ => ⟨hval, fun _ => ⟨h', rfl, hc⟩⟩, fun _ => Or.inl ⟨h', rfl, hc⟩⟩
      · refine ⟨fun _ => ⟨hval, fun h => absurd h hzn⟩, fun h => ?_⟩
        rw [hzD] at h; cases h
    rcases hcls h o3 ho3 with ⟨o, ho, ⟨hco, rfl⟩ | ⟨hco, rfl⟩⟩ | ⟨-, nn, hnn, -, -, rfl⟩
    · rw [hco] at hc3; cases hc3
    · -- an old canonical object
      obtain ⟨a1, -, -, a4, -, -⟩ := updAll4_core sp db.P (k + 1) m1 (c.adds.filter (fun a => a.1 == o.node)) o
      rw [a1] at hw3 hrel3 ⊢
      obtain ⟨n, hn, -⟩ := hm.cc h o ho hco
      have hrel : Relevant sp db k o := by
        refine ⟨hco, hw3, ?_⟩
        rcases hrel3 with hr | hd
        · rcases hstep.noRes o.node hr with hr' | hnew
          · rw [hK1] at hr'; exact Or.inl hr'
          · exact absurd hnew (hnotnew _ _ hn)
        · exact Or.inr hd
      by_cases hin : z ∈ (c.adds.filter (fun a => a.1 == o.node)).flatMap (fun a => sp.ptrs a.2)
      · obtain ⟨sl, hsl, hns⟩ := hslot_upd _ o z (hLadds o.node) hin
        have := hnsok sl hns
        rw [a1] at this
        exact ⟨sl, hsl, this⟩
      · have hzo : z ∈ pointees sp o.hist := by
          rw [a4] at hz
          rcases pointees_append_mem hz with hz | hz
          · exact hz
          · obtain ⟨a, ha, hza⟩ := pointees_adds_mem hz
            exact absurd (List.mem_flatMap.mpr ⟨a, ha, hza⟩) hin
        obtain ⟨sl, hsl, hi⟩ := hm.slots h o ho hrel z hzo
        have hsl3 : (updAll4 sp db.P (k + 1) m1 (c.adds.filter (fun a => a.1 == o.node)) o).slot? z = some sl := by
          rw [updAll4_slot]; simp only [hin, ↓reduceIte]; exact hsl
        -- z is a node of P: not new
        have hzP : ∃ nz, db.P.get? z = some nz := by
          rw [mem_pointees] at hzo
          obtain ⟨e, he, hze⟩ := hzo
          obtain ⟨n0, hn0, hh0, -, -⟩ := hm.cc h o ho hco
          obtain ⟨nz, hnz, -⟩ := hinv.ptrs o.node n0 hn0 e (by rw [← hh0]; exact he) z hze
          exact ⟨nz, hnz⟩
        obtain ⟨nz, hnz⟩ := hzP
        refine ⟨sl, hsl3, fun hzD => ⟨by rw [hsref h o ho z sl hsl]; exact hi.1 hzD,
          fun h' => absurd h' (hnotnew z nz hnz)⟩, fun hzD => ?_⟩
        rcases hi.2 hzD with ⟨h', hh', hc'⟩ | h2
        · exact Or.inl ⟨h', hh', by rw [hold_can z (hnotnew z nz hnz)]; exact hc'⟩
        · exact Or.inr h2
    · -- a new node's object
      obtain ⟨a1, -, -, a4, -, -⟩ := updAll4_core sp db.P (k + 1) m1 (c.adds.filter (fun a => a.1 == nn.id))
        (newObj nn)
      rw [a1]
      have hin : z ∈ (c.adds.filter (fun a => a.1 == nn.id)).flatMap (fun a => sp.ptrs a.2) := by
        rw [a4] at hz
        rcases pointees_append_mem hz with hz | hz
        · simp [newObj, pointees] at hz
        · obtain ⟨a, ha, hza⟩ := pointees_adds_mem hz
          exact List.mem_flatMap.mpr ⟨a, ha, hza⟩
      obtain ⟨sl, hsl, hns⟩ := hslot_upd _ (newObj nn) z (hLadds nn.id) hin
      have := hnsok sl hns
      rw [(updAll4_core sp db.P (k + 1) m1 _ (newObj nn)).1] at this
      exact ⟨sl, hsl, this⟩
  · -- live
    intro h o3 ho3 hc3 hr3 z hz
    obtain ⟨n', hn', hh', -, -⟩ := hcc3 h o3 ho3 hc3
    have hz' : z ∈ sp.live (n'.hist.upTo (k + 1)) := by
      rw [upTo_of_forall _ _ (htimes' _ n' hn'), ← hh']; exact hz
    -- The new slot of a pointer, as the live slots ask after the change.
    have hnsok : ∀ sl, NS4 sp db.P (k + 1) m1 z = some sl →
        ((inD db.D z = true ∨ z ∈ path ∨ z ∈ c.new.map (·.id)) →
          ∃ h', sl = Slot.mem h' ∧ m3.canonicalOf z = some h') ∧
        (inD db.D z = false → slotRefOf S0 m3 z sl = (db.S.lv z).map (·.recNo)) := by
      intro sl hns
      rcases hns3 z sl hns with ⟨⟨h', rfl, hc⟩, hval⟩ | ⟨hc, hzD, hzn, hval⟩
      · exact ⟨fun _ => ⟨h', rfl, hc⟩, fun _ => hval⟩
      · refine ⟨fun hcase => ?_, fun _ => hval⟩
        exfalso
        rcases hcase with hcase | hcase | hcase
        · rw [hzD] at hcase; cases hcase
        · obtain ⟨nz, hnz⟩ := Option.isSome_iff_exists.mp (hpn z hcase)
          rw [hold_can z (hnotnew z nz hnz)] at hc
          exact hpdm z hcase hc
        · exact hzn hcase
    rcases hphys.liveNew o3.node n' hn' z hz' with ⟨n0, hn0, hzl0⟩ | ⟨a, ha, hax, hza⟩
    · -- live at k already
      rw [hK1] at hzl0
      rcases hcls h o3 ho3 with ⟨o, ho, ⟨hco, rfl⟩ | ⟨hco, rfl⟩⟩ | ⟨-, nn, hnn, -, -, rfl⟩
      · rw [hco] at hc3; cases hc3
      · obtain ⟨a1, -, -, -, -, -⟩ := updAll4_core sp db.P (k + 1) m1 (c.adds.filter (fun a => a.1 == o.node)) o
        rw [a1] at hn0 hr3
        by_cases hin : z ∈ (c.adds.filter (fun a => a.1 == o.node)).flatMap (fun a => sp.ptrs a.2)
        · obtain ⟨sl, hsl, hns⟩ := hslot_upd _ o z (hLadds o.node) hin
          exact ⟨sl, hsl, hnsok sl hns⟩
        · obtain ⟨n, hn, hhn, -, -⟩ := hm.cc h o ho hco
          rw [hn, Option.some.injEq] at hn0
          subst hn0
          have hrk : reachable sp db.P k o.node = true := by
            rcases hstep.noRes o.node hr3 with hr' | hnew
            · rw [hK1] at hr'; exact hr'
            · exact absurd hnew (hnotnew _ _ hn)
          have hzo : z ∈ sp.live o.hist := by
            rw [hhn, ← upTo_of_forall _ _ (hinv.times _ n hn)]; exact hzl0
          obtain ⟨sl, hsl, hli⟩ := hm.live h o ho hco hrk z hzo
          have hsl3 : (updAll4 sp db.P (k + 1) m1 (c.adds.filter (fun a => a.1 == o.node)) o).slot? z = some sl := by
            rw [updAll4_slot]; simp only [hin, ↓reduceIte]; exact hsl
          -- z is a node of P, below o's node
          obtain ⟨e, he, hze⟩ := hls _ _ hzl0
          obtain ⟨nz, hnz, hlt⟩ := hinv.ptrs o.node n hn e (mem_upTo.mp he).1 z hze
          have hzr : z ≠ SIS.root := hinv.ptr_ne_root hn (mem_upTo.mp he).1 hze
          have hrz : reachable sp db.P k z = true := by
            rw [reachable_iff] at hrk ⊢; exact Reach.child hrk hn hzl0 hnz hlt
          refine ⟨sl, hsl3, fun hcase => ?_, fun hzD => by rw [hsref h o ho z sl hsl]; exact hli.2 hzD⟩
          rcases hcase with hcase | hcase | hcase
          · obtain ⟨h', hh', hc'⟩ := hli.1 hcase
            exact ⟨h', hh', by rw [hold_can z (hnotnew z nz hnz)]; exact hc'⟩
          · -- z is on the path: its parent's slot on the path names its canonical
            -- object, and by TREE that parent is o's node.
            obtain ⟨-, hpz⟩ := hpd z hcase
            obtain ⟨p, hp, np, hp0, op, hz0, hnp, hzp, hcp, hop, hslp, hcz⟩ := hpz hzr
            have hxp : o.node = p := treeAt_unique htree hrz hzr hrk (hpr p hp) hn hnp hzl0 hzp
            have hco' := hm.canonicalOf_of ho hco
            rw [hxp, hcp, Option.some.injEq] at hco'
            subst hco'
            rw [ho, Option.some.injEq] at hop
            subst hop
            rw [hsl, Option.some.injEq] at hslp
            subst hslp
            exact ⟨hz0, rfl, by rw [hold_can z (hnotnew z nz hnz)]; exact hcz⟩
          · exact absurd hcase (hnotnew z nz hnz)
      · -- a new node has no live child but from its entries
        exfalso
        rw [(updAll4_core sp db.P (k + 1) m1 _ (newObj nn)).1] at hn0
        have := hstep.fresh nn hnn
        simp only [newObj] at hn0
        rw [hn0] at this; cases this
    · -- a pointer of an entry of this transaction
      have hin : ∀ x, o3.node = x → z ∈ (c.adds.filter (fun a => a.1 == x)).flatMap (fun a => sp.ptrs a.2) := by
        intro x hx
        exact List.mem_flatMap.mpr ⟨a, List.mem_filter.mpr ⟨ha, by simp [hax, hx]⟩, hza⟩
      rcases hcls h o3 ho3 with ⟨o, ho, ⟨hco, rfl⟩ | ⟨hco, rfl⟩⟩ | ⟨-, nn, hnn, -, -, rfl⟩
      · rw [hco] at hc3; cases hc3
      · obtain ⟨a1, -, -, -, -, -⟩ := updAll4_core sp db.P (k + 1) m1 (c.adds.filter (fun a => a.1 == o.node)) o
        obtain ⟨sl, hsl, hns⟩ := hslot_upd _ o z (hLadds o.node) (hin o.node a1)
        exact ⟨sl, hsl, hnsok sl hns⟩
      · obtain ⟨a1, -, -, -, -, -⟩ := updAll4_core sp db.P (k + 1) m1 (c.adds.filter (fun a => a.1 == nn.id))
          (newObj nn)
        obtain ⟨sl, hsl, hns⟩ := hslot_upd _ (newObj nn) z (hLadds nn.id) (hin nn.id a1)
        exact ⟨sl, hsl, hnsok sl hns⟩

/-- The change applied after the writer's paths: `AInv`. -/
theorem EInv.applyChange4_ok (hinv : Inv sp db k) (hls : LiveSub sp) (hm : EInv sp db S0 k m)
    (hpd : ∀ x ∈ pathOf sp db.P c (k + 1), PathDone sp db.P k (pathOf sp db.P c (k + 1)) m x)
    (hstep : StepOK sp db.P (k + 1) c) (hphys : PhysStep sp db.P (k + 1) c)
    (hcopy : CopyStep sp db.P (k + 1) c) (htree : treeAt sp db.P k) :
    AInv sp db S0 k c (pathOf sp db.P c (k + 1)) (m.applyChange4 sp db.P (k + 1) c) := by
  have hK1 : k + 1 - 1 = k := by omega
  have hpr : ∀ p ∈ pathOf sp db.P c (k + 1), reachable sp db.P k p = true := by
    intro p hp; have := (mem_pathOf hp).1; rw [hK1] at this; exact this
  have hpn : ∀ p ∈ pathOf sp db.P c (k + 1), (db.P.get? p).isSome := by
    intro p hp; obtain ⟨-, n, hn, -⟩ := mem_pathOf hp; rw [hn]; rfl
  refine hm.applyChange4_core hinv hls hpd hpr hpn hstep hphys htree (hm.addFacts hstep.distinct)
    (changeFacts sp db.P (k + 1) c m) (fun hx => hm.adds_filter_node hstep.distinct hx) ?_
    (fun hns => hm.NS4_good hinv hstep hns)
  intro a ha y hy
  by_cases hyn : y ∈ c.new.map (·.id)
  · exact hm.NS4_some hinv hpd hpr hpn hstep (Or.inl hyn)
  · rcases hcopy a ha y hy hyn with h | ⟨z, hz, nz, hnz, hyz, hwl⟩
    · exact hm.NS4_some hinv hpd hpr hpn hstep (Or.inr (Or.inl h))
    · rw [hK1] at hwl
      exact hm.NS4_some hinv hpd hpr hpn hstep (Or.inr (Or.inr ⟨z, hz, nz, hnz, hyz, hwl⟩))

end ApplyInv

end SIS
