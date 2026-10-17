/-
Proofs for stage 2 (bergdb item 001, WP E3), part 11: after the record, the
memory has the invariant of the next state (INV-SLOT across D's changes).
-/
import SIS.Proof.EvictWrites

set_option linter.unusedSectionVars false

namespace SIS

variable {V T : Type} [DecidableEq V]

section Final

variable {sp : Spec V T} {al : Algo V T} {db : DB V T} {tr : T} {S0 : Stream V T} {k : Nat}

theorem AInv.canonicalOf_of' {sp : Spec V T} {db : DB V T} {S0 : Stream V T} {k : Nat} {c : Changes V}
    {path : List NodeId} {m : Mem V} (ha : AInv sp db S0 k c path m) {h : Nat} {o : Obj V}
    (ho : m.obj? h = some o) (hc : o.canonical = true) : m.canonicalOf o.node = some h :=
  (m.canonicalOf_eq_some o.node h).mpr ⟨ha.canonTbl h o ho hc, o, ho, hc⟩

theorem Inv.D_le {sp : Spec V T} {db : DB V T} {k : Nat} (hinv : Inv sp db k) {x : NodeId} {d : Nat}
    (h : (x, d) ∈ db.D) : d ≤ k := by
  rw [hinv.inv1] at h
  have := (sectionD_mem h).2.1
  rw [hinv.len] at this
  omega

/-- After the two loops, the memory has the invariant of the state after the
transaction. -/
theorem AInv.final_ok (hsp : SpecOK sp) (hinv : Inv sp db k) (hmk : al.mark = true)
    (hstep : StepOK sp db.P (k + 1) (parts sp al db tr).c) (hinv' : Inv sp (step sp al db tr) (k + 1))
    (hev' : EvLogic sp (step sp al db tr) (k + 1)) {m3 m6 : Mem V}
    (ha : AInv sp db S0 k (parts sp al db tr).c (pathOf sp db.P (parts sp al db tr).c (k + 1)) m3)
    (hfr : LoopsFrame db.D (parts sp al db tr).D1 (dataIds sp al db tr) (parts sp al db tr).taken (k + 1)
      m3 m6)
    (hpos6 : PosOK db.S (parts sp al db tr).vs m6) :
    EInv sp (step sp al db tr) S0 (k + 1) m6 := by
  have hP : (parts sp al db tr).P = db.P.apply (k + 1) (parts sp al db tr).c := parts_P' sp al db tr hinv.len
  have hP' : (step sp al db tr).P = (parts sp al db tr).P := rfl
  have hS' : (step sp al db tr).S = Snew sp al db tr := rfl
  have hD' : (step sp al db tr).D = (parts sp al db tr).r7.1 := rfl
  -- Objects of m6 come from m3.
  have hback : ∀ h o6, m6.obj? h = some o6 → ∃ o3, m3.obj? h = some o3 := by
    intro h o6 ho6
    cases ho3 : m3.obj? h with
    | none => rw [hfr.none h ho3] at ho6; cases ho6
    | some o3 => exact ⟨o3, rfl⟩
  have hobj : ∀ h o6, m6.obj? h = some o6 → ∃ o3, m3.obj? h = some o3 ∧ o6.node = o3.node ∧
      o6.level = o3.level ∧ o6.isData = o3.isData ∧ o6.hist = o3.hist ∧ o6.canonical = o3.canonical ∧
      (∀ z, o6.slot? z = o3.slot? z ∨ ((inD db.D z = true ∨ inD (parts sp al db tr).D1 z = true) ∧
        ∃ sl h0, o3.slot? z = some sl ∧ m3.canonicalOf z = some h0 ∧ o6.slot? z = some (Slot.mem h0))) ∧
      ((o3.node ∈ (parts sp al db tr).taken ∧ m3.canonicalOf o3.node = some h) → ∀ z sl h0,
        o3.slot? z = some sl → inD (parts sp al db tr).D1 z = true → m3.canonicalOf z = some h0 →
        o6.slot? z = some (Slot.mem h0)) ∧
      (¬ ((o3.node ∈ dataIds sp al db tr ∨ o3.node ∈ (parts sp al db tr).taken) ∧
        m3.canonicalOf o3.node = some h) → o6.pos = o3.pos ∧ ∀ z, o6.slot? z = o3.slot? z) := by
    intro h o6 ho6
    obtain ⟨o3, ho3⟩ := hback h o6 ho6
    obtain ⟨o6', ho6', rest⟩ := hfr.obj h o3 ho3
    rw [ho6, Option.some.injEq] at ho6'
    subst ho6'
    exact ⟨o3, ho3, rest⟩
  have hcan6 := hfr.canon
  -- D after the transaction.
  have hD1D : ∀ y, inD db.D y = true → inD (parts sp al db tr).D1 y = true := by
    intro y hy
    obtain ⟨d, hd⟩ := (inD_iff _ _).mp hy
    exact (inD_iff _ _).mpr ⟨d, (step_D1_mem sp al db tr hinv.len _).mpr (Or.inl hd)⟩
  have hD'D1 : ∀ y, inD (parts sp al db tr).r7.1 y = true → inD (parts sp al db tr).D1 y = true :=
    fun y hy => step_r7_D1 sp al db tr hinv hy
  -- A node of D1 is in D, on the writer's paths, or new.
  have hD1cases : ∀ y, inD (parts sp al db tr).D1 y = true →
      inD db.D y = true ∨ y ∈ pathOf sp db.P (parts sp al db tr).c (k + 1) ∨
        y ∈ (parts sp al db tr).c.new.map (·.id) := by
    intro y hy
    rcases step_D1_cases sp al db tr hmk hinv hy with h | h | h
    · exact Or.inl h
    · by_cases hn : y ∈ (parts sp al db tr).c.new.map (·.id)
      · exact Or.inr (Or.inr hn)
      · rw [hP] at h
        exact Or.inr (Or.inl (step_marked_path sp al db tr hsp hinv hstep h hn))
    · exact Or.inr (Or.inl (step_touched_path sp al db tr hstep h))
  -- A node of D1 is in D, which is relevant, or reachable at k + 1 (marked), or
  -- at k (touched).
  have hD1rel : ∀ y, inD (parts sp al db tr).D1 y = true →
      reachable sp (db.P.apply (k + 1) (parts sp al db tr).c) (k + 1) y = true ∨ inD db.D y = true ∨
        reachable sp db.P k y = true := by
    intro y hy
    rcases step_D1_cases sp al db tr hmk hinv hy with h | h | h
    · exact Or.inr (Or.inl h)
    · left; rw [hP] at h; unfold marked at h; simp only [Bool.and_eq_true] at h; exact h.1
    · right; right; have := hstep.touchReach y h; simpa using this
  -- Written in the record: a new data node or a taken node.
  have hnotw : ∀ z, z ∉ dataIds sp al db tr → z ∉ (parts sp al db tr).taken →
      (Snew sp al db tr).lv z = db.S.lv z := by
    intro z h1 h2
    apply lv_Snew_not_written
    intro w hw hwz
    have := (step_written_iff sp al db tr hinv hstep z).mp ⟨w, hw, hwz⟩
    rcases this with h | h
    · exact h1 h
    · exact h2 h
  have htakenD : ∀ x ∈ (parts sp al db tr).taken, ∃ d, (x, d) ∈ db.D ∧ d ≤ (parts sp al db tr).s :=
    fun x hx => step_taken_inD (al := al) (tr := tr) hinv hx
  have hdnew : ∀ x ∈ dataIds sp al db tr, x ∈ (parts sp al db tr).c.new.map (·.id) := by
    intro x hx
    simp only [dataIds, List.mem_map, List.mem_filter] at hx
    obtain ⟨nn, ⟨hnn, -⟩, rfl⟩ := hx
    exact List.mem_map.mpr ⟨nn, hnn, rfl⟩
  -- A node not in D1 and not written keeps its latest version; a node of D1 not
  -- taken stays in D.
  have hD2 : ∀ z, inD (parts sp al db tr).D1 z = true → z ∉ (parts sp al db tr).taken →
      inD (parts sp al db tr).r7.1 z = true := by
    intro z hz hzt
    obtain ⟨d, hd⟩ := (inD_iff _ _).mp hz
    have h2 := step_D2_of_not_taken sp al db tr hd hzt
    obtain ⟨d2, hd2⟩ := (inD_iff _ _).mp h2
    rw [(step_r7_shape sp al db tr hinv.len).1]
    exact (inD_iff _ _).mpr ⟨d2, List.mem_append_left _ hd2⟩
  -- PosOK for the new stream.
  have hpos : PosOK (step sp al db tr).S [] m6 := by
    intro z h o hz ho
    rw [hpos6 z h o hz ho, lv_building_Snew, lv_building]
    rfl
  -- The serialized reference of a slot of an object of m3, after the record.
  have hsref : ∀ h3 o3, m3.obj? h3 = some o3 → ∀ z sl, o3.slot? z = some sl →
      z ∉ dataIds sp al db tr → z ∉ (parts sp al db tr).taken →
      slotRefOf S0 m6 z sl = slotRefOf S0 m3 z sl := by
    intro h3 o3 ho3 z sl hz hzd hzt
    cases sl with
    | mem h' =>
      obtain ⟨o', ho', hn'⟩ := ha.slotsNode h3 o3 ho3 z h' hz
      obtain ⟨o6, ho6, e1, -, -, -, -, -, -, e9⟩ := hfr.obj h' o' ho'
      have hp : o6.pos = o'.pos := by
        refine (e9 ?_).1
        rintro ⟨h1, -⟩
        rw [hn'] at h1
        rcases h1 with h1 | h1
        · exact hzd h1
        · exact hzt h1
      simp only [slotRefOf, ho6, ho', Option.bind_some, hp]
    | stream r => simp only [slotRefOf, hfr.s]
  -- The position of the canonical object of a node, after the record: its latest
  -- version then.
  have hcanpos : ∀ z h0, m3.canonicalOf z = some h0 →
      slotRefOf S0 m6 z (Slot.mem h0) = ((step sp al db tr).S.lv z).map (·.recNo) := by
    intro z h0 hc
    rw [← hcan6] at hc
    obtain ⟨-, o, ho, -⟩ := (m6.canonicalOf_eq_some z h0).mp hc
    simp only [slotRefOf, ho, Option.bind_some]
    exact hpos.lv0 hc ho
  refine ⟨hinv'.len, ?_, ?_, ?_, hfr.nodup ha.objNodup, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hpos, ?_, ?_,
    ?_, ?_⟩
  · -- pre
    exact ha.pre.trans (List.prefix_append _ _)
  · -- sEq
    rw [hfr.s]; exact ha.sEq
  · -- fresh
    intro h hh
    cases ho : m6.obj? h with
    | none => rfl
    | some o6 =>
      obtain ⟨o3, ho3⟩ := hback h o6 ho
      rw [ha.fresh h (by rw [← hfr.next]; exact hh)] at ho3; cases ho3
  · -- root
    obtain ⟨o, ho, hc, hn⟩ := ha.root
    obtain ⟨o6, ho6, e1, -, -, -, e5, -⟩ := hfr.obj _ o ho
    exact ⟨o6, by rw [hfr.root]; exact ho6, by rw [e5, hc], by rw [e1, hn]⟩
  · -- tblNodup
    rw [hfr.table]; exact ha.tblNodup
  · -- tbl
    intro y h ht
    rw [show m6.tableOf y = m3.tableOf y by unfold Mem.tableOf; rw [hfr.table]] at ht
    obtain ⟨o, ho, hn⟩ := ha.tbl y h ht
    obtain ⟨o6, ho6, e1, -⟩ := hfr.obj h o ho
    exact ⟨o6, ho6, by rw [e1, hn]⟩
  · -- slotsNode
    intro h o6 ho6 z h' hz
    obtain ⟨o3, ho3, -, -, -, -, -, hsl, -, -⟩ := hobj h o6 ho6
    rcases hsl z with hs | ⟨-, sl, h0, -, hc0, hs⟩
    · rw [hs] at hz
      obtain ⟨o', ho', hn'⟩ := ha.slotsNode h o3 ho3 z h' hz
      obtain ⟨o6', ho6', e1, -⟩ := hfr.obj h' o' ho'
      exact ⟨o6', ho6', by rw [e1, hn']⟩
    · rw [hs, Option.some.injEq, Slot.mem.injEq] at hz
      subst hz
      obtain ⟨ht, -⟩ := (m3.canonicalOf_eq_some z h0).mp hc0
      obtain ⟨o', ho', hn'⟩ := ha.tbl z h0 ht
      obtain ⟨o6', ho6', e1, -⟩ := hfr.obj h0 o' ho'
      exact ⟨o6', ho6', by rw [e1, hn']⟩
  · -- tblCanon
    intro y h ht
    rw [show m6.tableOf y = m3.tableOf y by unfold Mem.tableOf; rw [hfr.table]] at ht
    obtain ⟨o, ho, hc⟩ := ha.tblCanon y h ht
    obtain ⟨o6, ho6, -, -, -, -, e5, -⟩ := hfr.obj h o ho
    exact ⟨o6, ho6, by rw [e5, hc]⟩
  · -- canonTbl
    intro h o6 ho6 hc6
    obtain ⟨o3, ho3, e1, -, -, -, e5, -⟩ := hobj h o6 ho6
    rw [show m6.tableOf o6.node = m3.tableOf o6.node by unfold Mem.tableOf; rw [hfr.table], e1]
    exact ha.canonTbl h o3 ho3 (by rw [← e5]; exact hc6)
  · -- cc
    intro h o6 ho6 hc6
    obtain ⟨o3, ho3, e1, e2, e3, e4, e5, -⟩ := hobj h o6 ho6
    obtain ⟨n, hn, h1, h2, h3⟩ := ha.cc h o3 ho3 (by rw [← e5]; exact hc6)
    exact ⟨n, by rw [hP', hP, e1]; exact hn, by rw [e4, h1], by rw [e2, h2], by rw [e3, h3]⟩
  · -- dCanon
    intro y hy
    rw [hcan6]
    exact ha.canon_D1 hsp hinv hmk hstep (hD'D1 y hy)
  · -- snap
    intro h o6 ho6 hc6
    obtain ⟨o3, ho3, e1, e2, e3, e4, e5, hsl, -, hp⟩ := hobj h o6 ho6
    have hc3 : o3.canonical = false := by rw [← e5]; exact hc6
    obtain ⟨r, w, s1, s2, s3, s4, s5, s6, s7⟩ := ha.snap h o3 ho3 hc3
    -- a snapshot is not written: same position and slots
    have hnc : ¬ ((o3.node ∈ dataIds sp al db tr ∨ o3.node ∈ (parts sp al db tr).taken) ∧
        m3.canonicalOf o3.node = some h) := by
      rintro ⟨-, hc⟩
      obtain ⟨-, o', ho', hco⟩ := (m3.canonicalOf_eq_some _ h).mp hc
      rw [ho3, Option.some.injEq] at ho'; subst ho'
      rw [hc3] at hco; cases hco
    have hslots : ∀ z, o6.slot? z = o3.slot? z := (hp hnc).2
    have hSn : Snew sp al db tr = db.S ++ [(parts sp al db tr).R] := rfl
    refine ⟨r, w, by rw [(hp hnc).1]; exact s1, ?_, by rw [e4]; exact s3, by rw [e2]; exact s4,
      by rw [e3]; exact s5, fun z hz => by rw [hslots z]; exact s6 z (by rw [← e4]; exact hz),
      fun z sl hz => ?_⟩
    · rw [e1, hS', hSn]; exact versionAt_prefix (List.prefix_append _ _) s2
    rw [hslots z] at hz
    have hss := s7 z sl hz
    unfold SnapSlot at hss ⊢
    rw [hfr.s]
    rcases hss with hss | ⟨p, u, hp1, hu, hle⟩ | ⟨h', o', hsl', ho', hn', hcc⟩
    · exact Or.inl hss
    · refine Or.inr (Or.inl ⟨p, u, hp1, ?_, hle⟩)
      rw [hS', hSn]
      exact versionAt_prefix (List.prefix_append _ _) hu
    · obtain ⟨o6', ho6', f1, -, -, -, f5, -, -, f9⟩ := hfr.obj h' o' ho'
      refine Or.inr (Or.inr ⟨h', o6', hsl', ho6', by rw [f1, hn'], ?_⟩)
      rcases hcc with hcc | ⟨p, hp', hle⟩
      · exact Or.inl (by rw [f5, hcc])
      · cases hco' : o'.canonical with
        | true => exact Or.inl (by rw [f5, hco'])
        | false =>
          refine Or.inr ⟨p, ?_, hle⟩
          rw [(f9 (by
            rintro ⟨-, hc⟩
            obtain ⟨-, o'', ho'', hco''⟩ := (m3.canonicalOf_eq_some _ h').mp hc
            rw [ho', Option.some.injEq] at ho''; subst ho''
            rw [hco'] at hco''; cases hco'')).1]
          exact hp'
  · -- slots
    intro h o6 ho6 hrel z hz
    obtain ⟨o3, ho3, e1, e2, e3, e4, e5, hsl, hpin, hun⟩ := hobj h o6 ho6
    obtain ⟨hc6, hw6, hr6⟩ := hrel
    have hc3 : o3.canonical = true := by rw [← e5]; exact hc6
    have hcx : m3.canonicalOf o3.node = some h := ha.canonicalOf_of' ho3 hc3
    have hrel3 : reachable sp (db.P.apply (k + 1) (parts sp al db tr).c) (k + 1) o3.node = true ∨
        inD db.D o3.node = true ∨ reachable sp db.P k o3.node = true := by
      rcases hr6 with hr | hd
      · left; rw [← hP, ← hP', ← e1]; exact hr
      · rw [e1] at hd; exact hD1rel _ (hD'D1 _ hd)
    obtain ⟨sl3, hsl3, hA1, hA2⟩ := ha.slots h o3 ho3 hc3 (by rw [← e1]; exact hw6) hrel3 z (by rw [← e4]; exact hz)
    -- The slot after the record: as before, or a memory slot to z's canonical object.
    have hsl6 : ∃ sl6, o6.slot? z = some sl6 ∧ (sl6 = sl3 ∨ ∃ h0, sl6 = Slot.mem h0 ∧ m3.canonicalOf z = some h0) := by
      rcases hsl z with hs | ⟨-, sl, h0, hs3, hc0, hs6⟩
      · exact ⟨sl3, by rw [hs, hsl3], Or.inl rfl⟩
      · exact ⟨Slot.mem h0, hs6, Or.inr ⟨h0, rfl, hc0⟩⟩
    obtain ⟨sl6, hs6, hcase⟩ := hsl6
    -- When o's node is taken, its slots to D1 are memory slots to the canonical objects.
    have hpinned : ∀ h0, o3.node ∈ (parts sp al db tr).taken → inD (parts sp al db tr).D1 z = true →
        m3.canonicalOf z = some h0 → sl6 = Slot.mem h0 := by
      intro h0 hxt hzD1 hc0
      have := hpin ⟨hxt, hcx⟩ z sl3 h0 hsl3 hzD1 hc0
      rw [hs6, Option.some.injEq] at this
      exact this
    refine ⟨sl6, hs6, fun hzD' => ?_, fun hzD' => ?_⟩
    · -- z not in D after: its latest version.
      rw [hD'] at hzD'
      by_cases hzw : z ∈ dataIds sp al db tr ∨ z ∈ (parts sp al db tr).taken
      · -- written in the record: sl6 names z's canonical object
        have hmem : ∃ h0, sl6 = Slot.mem h0 ∧ m3.canonicalOf z = some h0 := by
          rcases hcase with rfl | hmem
          · rcases hzw with hzd | hzt
            · have hzn := hdnew z hzd
              have hzD : inD db.D z = false := by
                cases hzd' : inD db.D z with
                | false => rfl
                | true =>
                  exfalso
                  obtain ⟨d, hd⟩ := (inD_iff _ _).mp hzd'
                  have hix := hinv.dIndex (z, d) hd
                  obtain ⟨hnone, -⟩ := step_dataIds_spec sp al db tr hinv hstep hzd
                  simp [isIndex, hnone] at hix
              exact (hA1 hzD).2 hzn
            · obtain ⟨dz, hdz, hdzs⟩ := htakenD z hzt
              have hzD : inD db.D z = true := (inD_iff _ _).mpr ⟨dz, hdz⟩
              rcases hA2 hzD with hmem | ⟨hxD, a, b, ha', hb, hab⟩
              · exact hmem
              · -- o's node got dirty no later than z: taken too, so written with z pinned
                have hb' : b = dz := by
                  rw [dOf_of_mem hinv.dNodup hdz, Option.some.injEq] at hb; exact hb.symm
                have hxt : o3.node ∈ (parts sp al db tr).taken := by
                  have hxa := mem_of_dOf ha'
                  exact (step_taken_mem sp al db tr _).mpr ⟨a, (step_D1_mem sp al db tr hinv.len _).mpr
                    (Or.inl hxa), by omega⟩
                obtain ⟨h0, hc0⟩ := Option.isSome_iff_exists.mp (ha.canon z (Or.inl hzD))
                exact ⟨h0, hpinned h0 hxt (hD1D z hzD) hc0, hc0⟩
          · exact hmem
        obtain ⟨h0, rfl, hc0⟩ := hmem
        exact hcanpos z h0 hc0
      · -- not written: not in D1, so the slot is as before, and so is z's latest version
        rw [not_or] at hzw
        have hzD1 : inD (parts sp al db tr).D1 z = false := by
          cases hz1 : inD (parts sp al db tr).D1 z with
          | false => rfl
          | true => rw [hD2 z hz1 hzw.2] at hzD'; cases hzD'
        have hzD : inD db.D z = false := by
          cases hzd : inD db.D z with
          | false => rfl
          | true => rw [hD1D z hzd] at hzD1; cases hzD1
        have hsame : sl6 = sl3 := by
          rcases hcase with h1 | ⟨h0, -, -⟩
          · exact h1
          · rcases hsl z with hs | ⟨hzin, -⟩
            · rw [hs, hsl3, Option.some.injEq] at hs6; exact hs6.symm
            · rcases hzin with h1 | h1
              · rw [hzD] at h1; cases h1
              · rw [hzD1] at h1; cases h1
        subst hsame
        rw [hsref h o3 ho3 z sl6 hsl3 hzw.1 hzw.2, (hA1 hzD).1, hS', hnotw z hzw.1 hzw.2]
    · -- z in D after
      rw [hD'] at hzD'
      obtain ⟨dz, hdz⟩ := dOf_inD hzD'
      have hdzm := mem_of_dOf hdz
      have hD'nd : ((parts sp al db tr).r7.1.map (·.1)).Nodup := hinv'.dNodup
      rcases step_D'_entry (al := al) (tr := tr) hinv hdzm with hdk | ⟨hzdb, hsdz⟩
      · -- z got dirty in this transaction: o's node is in D after it too
        right
        have hxD' : inD (parts sp al db tr).r7.1 o6.node = true := by
          rcases hr6 with hr | hd
          · cases hxd : inD (parts sp al db tr).r7.1 o6.node with
            | true => rfl
            | false =>
              exfalso
              obtain ⟨n', hn', hh', -, -⟩ := ha.cc h o3 ho3 hc3
              have hn'' : (step sp al db tr).P.get? o6.node = some n' := by rw [hP', hP, e1]; exact hn'
              have := (hev'.clean o6.node n' hw6 hr hn'' hxd z (by rw [← hh', ← e4]; exact hz)).1
              rw [hD'] at this
              rw [this] at hzD'; cases hzD'
          · exact hd
        obtain ⟨a, ha'⟩ := dOf_inD hxD'
        have hxa := mem_of_dOf ha'
        refine ⟨hxD', a, dz, ha', hdz, ?_⟩
        rcases step_D'_entry (al := al) (tr := tr) hinv hxa with h1 | ⟨h1, -⟩
        · omega
        · have := hinv.D_le h1; omega
      · -- z was in D and is not taken
        have hzD : inD db.D z = true := (inD_iff _ _).mpr ⟨dz, hzdb⟩
        rcases hA2 hzD with ⟨h0, rfl, hc0⟩ | ⟨hxD, a, b, ha', hb, hab⟩
        · left
          rcases hcase with h1 | ⟨h0', h2, hc0'⟩
          · exact ⟨h0, h1, by rw [hcan6]; exact hc0⟩
          · exact ⟨h0', h2, by rw [hcan6]; exact hc0'⟩
        · have hb' : b = dz := by
            rw [dOf_of_mem hinv.dNodup hzdb, Option.some.injEq] at hb; exact hb.symm
          subst hb'
          have hxa := mem_of_dOf ha'
          by_cases has : a ≤ (parts sp al db tr).s
          · -- o's node is taken: its slot for z is pinned
            left
            have hxt : o3.node ∈ (parts sp al db tr).taken :=
              (step_taken_mem sp al db tr _).mpr ⟨a, (step_D1_mem sp al db tr hinv.len _).mpr (Or.inl hxa), has⟩
            obtain ⟨h0, hc0⟩ := Option.isSome_iff_exists.mp (ha.canon z (Or.inl hzD))
            exact ⟨h0, hpinned h0 hxt (hD1D z hzD) hc0, by rw [hcan6]; exact hc0⟩
          · -- o's node stays in D, with its index
            right
            have hxD2 : (o3.node, a) ∈ (parts sp al db tr).D2 :=
              (step_D2_mem sp al db tr _).mpr ⟨(step_D1_mem sp al db tr hinv.len _).mpr (Or.inl hxa), by
                simp only; omega⟩
            have hxD' : (o3.node, a) ∈ (parts sp al db tr).r7.1 := by
              rw [(step_r7_shape sp al db tr hinv.len).1]; exact List.mem_append_left _ hxD2
            rw [e1]
            exact ⟨(inD_iff _ _).mpr ⟨a, hxD'⟩, a, b, dOf_of_mem hD'nd hxD', hdz, hab⟩
  · -- live
    intro h o6 ho6 hc6 hr6 z hz
    obtain ⟨o3, ho3, e1, e2, e3, e4, e5, hsl, hpin, hun⟩ := hobj h o6 ho6
    have hc3 : o3.canonical = true := by rw [← e5]; exact hc6
    obtain ⟨sl3, hsl3, hL1, hL2⟩ := ha.live h o3 ho3 hc3 (by rw [← hP, ← hP', ← e1]; exact hr6) z
      (by rw [← e4]; exact hz)
    have hsl6 : ∃ sl6, o6.slot? z = some sl6 ∧ (sl6 = sl3 ∨ ∃ h0, sl6 = Slot.mem h0 ∧ m3.canonicalOf z = some h0) := by
      rcases hsl z with hs | ⟨-, sl, h0, hs3, hc0, hs6⟩
      · exact ⟨sl3, by rw [hs, hsl3], Or.inl rfl⟩
      · exact ⟨Slot.mem h0, hs6, Or.inr ⟨h0, rfl, hc0⟩⟩
    obtain ⟨sl6, hs6, hcase⟩ := hsl6
    -- For a pointee of D1 or a new one, both name its canonical object.
    have hcan : (inD db.D z = true ∨ z ∈ pathOf sp db.P (parts sp al db tr).c (k + 1) ∨
        z ∈ (parts sp al db tr).c.new.map (·.id)) → ∃ h0, sl6 = Slot.mem h0 ∧ m3.canonicalOf z = some h0 := by
      intro hzc
      obtain ⟨h0, rfl, hc0⟩ := hL1 hzc
      rcases hcase with h1 | h2
      · exact ⟨h0, h1, hc0⟩
      · exact h2
    refine ⟨sl6, hs6, fun hzD' => ?_, fun hzD' => ?_⟩
    · rw [hD'] at hzD'
      obtain ⟨h0, h1, hc0⟩ := hcan (hD1cases z (hD'D1 z hzD'))
      exact ⟨h0, h1, by rw [hcan6]; exact hc0⟩
    · rw [hD'] at hzD'
      by_cases hzw : z ∈ dataIds sp al db tr ∨ z ∈ (parts sp al db tr).taken
      · have hzc : inD db.D z = true ∨ z ∈ pathOf sp db.P (parts sp al db tr).c (k + 1) ∨
            z ∈ (parts sp al db tr).c.new.map (·.id) := by
          rcases hzw with hzd | hzt
          · exact Or.inr (Or.inr (hdnew z hzd))
          · obtain ⟨dz, hdz, -⟩ := htakenD z hzt
            exact Or.inl ((inD_iff _ _).mpr ⟨dz, hdz⟩)
        obtain ⟨h0, rfl, hc0⟩ := hcan hzc
        exact hcanpos z h0 hc0
      · rw [not_or] at hzw
        have hzD1 : inD (parts sp al db tr).D1 z = false := by
          cases hz1 : inD (parts sp al db tr).D1 z with
          | false => rfl
          | true => rw [hD2 z hz1 hzw.2] at hzD'; cases hzD'
        have hzD : inD db.D z = false := by
          cases hzd : inD db.D z with
          | false => rfl
          | true => rw [hD1D z hzd] at hzD1; cases hzD1
        have hsame : sl6 = sl3 := by
          rcases hcase with h1 | ⟨h0, -, -⟩
          · exact h1
          · rcases hsl z with hs | ⟨hzin, -⟩
            · rw [hs, hsl3, Option.some.injEq] at hs6; exact hs6.symm
            · rcases hzin with h1 | h1
              · rw [hzD] at h1; cases h1
              · rw [hzD1] at h1; cases h1
        subst hsame
        rw [hsref h o3 ho3 z sl6 hsl3 hzw.1 hzw.2, hL2 hzD, hS', hnotw z hzw.1 hzw.2]

end Final

end SIS
