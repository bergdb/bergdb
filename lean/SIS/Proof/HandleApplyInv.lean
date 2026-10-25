/-
Proofs about the physical layer with handles (bergdb item 009, step 2d), part 7:
after the writer's paths, the change applied to the canonical objects gives
`HAInv`, as SIS/Proof/EvictApplyInv.lean shows `AInv` for Evict.lean.
-/
import SIS.Proof.HandleApply

set_option linter.unusedSectionVars false

namespace SIS

variable {V T : Type} [DecidableEq V]

/-- The memory with handles after the change, before the writes (m3 in
`handleTrans`), for the state db at k, the change c of transaction k + 1 and its
paths: the table and the handles, CC for the new structure, positions as
before, the snapshots, and the pointers of the objects that may be written or
read, against the old D. -/
structure HAInv (sp : Spec V T) (db : DB V T) (S0 : Stream V T) (k : Nat) (c : Changes V)
    (path : List NodeId) (m : HMem V) : Prop where
  pre : S0 <+: db.S
  sEq : m.s = lastSp S0
  freshO : ∀ a, m.nextObj ≤ a → m.obj? a = none
  freshH : ∀ n, m.nextHandle ≤ n → m.handle? n = none
  objNodup : (m.objs.map (·.1)).Nodup
  hNodup : (m.handles.map (·.1)).Nodup
  root : ∃ o, m.obj? m.root = some o ∧ o.canonical = true ∧ o.node = root
  tbl : HTableOK m
  liveW : HLiveWrittenOK m
  cc : ∀ a o, m.obj? a = some o → o.canonical = true →
    ∃ n, (db.P.apply (k + 1) c).get? o.node = some n ∧ o.hist = n.hist ∧ o.level = n.level ∧
      o.isData = n.isData
  pos : ∀ a o, m.obj? a = some o → o.canonical = true → o.pos = (db.S.lv o.node).map (·.recNo)
  canon : ∀ y, (inD db.D y = true ∨ y ∈ path ∨ y ∈ c.new.map (·.id)) → (m.canonicalOf y).isSome
  snap : ∀ a o, m.obj? a = some o → o.canonical = false → HSnapExact sp S0 db m o
  ruleR : HRuleROK S0 m
  wver : ∀ n hd w, m.handle? n = some hd → hd.written = some w → ∃ u, db.S.versionAt w hd.node = some u
  rver : ∀ a o y p r, m.obj? a = some o → o.ptr? y = some p → p.ref = some r →
    ∃ u, db.S.versionAt r y = some u
  slots : ∀ a o, m.obj? a = some o → o.canonical = true → written sp o.node = true →
    (reachable sp (db.P.apply (k + 1) c) (k + 1) o.node = true ∨ inD db.D o.node = true ∨
      reachable sp db.P k o.node = true) →
    ∀ y ∈ pointees sp o.hist, ∃ p, o.ptr? y = some p ∧
      (inD db.D y = false → m.ptrRef S0 y p = (db.S.lv y).map (·.recNo) ∧
        (y ∈ c.new.map (·.id) → m.HoldsLive y p)) ∧
      (inD db.D y = true → m.HoldsLive y p ∨
        (inD db.D o.node = true ∧ ∃ a b, dOf db.D o.node = some a ∧ dOf db.D y = some b ∧ a ≤ b))
  live : ∀ a o, m.obj? a = some o → o.canonical = true →
    reachable sp (db.P.apply (k + 1) c) (k + 1) o.node = true →
    ∀ y ∈ sp.live o.hist, ∃ p, o.ptr? y = some p ∧
      ((inD db.D y = true ∨ y ∈ path ∨ y ∈ c.new.map (·.id)) → m.HoldsLive y p) ∧
      (inD db.D y = false → m.ptrRef S0 y p = (db.S.lv y).map (·.recNo))

section ApplyInv

variable {sp : Spec V T} {db : DB V T} {S0 : Stream V T} {k : Nat} {m : HMem V} {c : Changes V}

/-- The change applied after the writer's paths, from the memory m1 after the new
nodes' objects to the memory m3 after the adds: `HAInv`. -/
theorem HEInv.applyChange_core (hinv : Inv sp db k) (hls : LiveSub sp) (hm : HEInv sp db S0 k m)
    {path : List NodeId} (hpd : ∀ x ∈ path, HPathDone sp db.P k path m x)
    (hpr : ∀ p ∈ path, reachable sp db.P k p = true) (hpn : ∀ p ∈ path, (db.P.get? p).isSome)
    (hstep : StepOK sp db.P (k + 1) c) (hphys : PhysStep sp db.P (k + 1) c) (htree : treeAt sp db.P k)
    {m1 m3 : HMem V} (haf : HAddFacts m m1 c) (hcf : ChangeFactsH sp db.P (k + 1) c m1 m3)
    (hcopyNS : ∀ e ∈ c.adds, ∀ y ∈ sp.ptrs e.2, (NSH sp db.P (k + 1) m1 y).isSome)
    (hgood : ∀ {y p}, NSH sp db.P (k + 1) m1 y = some p →
      (∃ b, m1.canonicalOf y = some b ∧ p = { ref := (m1.obj? b).bind (·.pos), handle := m1.tableOf y }) ∨
      (m1.canonicalOf y = none ∧ inD db.D y = false ∧ y ∉ c.new.map (·.id) ∧
        m.ptrRef S0 y p = (db.S.lv y).map (·.recNo) ∧
        ∃ a0 o0, m.obj? a0 = some o0 ∧ o0.ptr? y = some p)) :
    HAInv sp db S0 k c path m3 := by
  have hK1 : k + 1 - 1 = k := by omega
  have hcan3 := hcf.canonicalOf
  have htab3 := hcf.tableOf
  have hfilt : ∀ {x b}, m1.canonicalOf x = some b →
      c.adds.filter (fun e => m1.canonicalOf e.1 == some b) = c.adds.filter (fun e => e.1 == x) :=
    fun hx => adds_filter_nodeH haf.tbl hx
  have holt : ∀ a o, m.obj? a = some o → a < m.nextObj := fun a o h =>
    Nat.lt_of_not_le (fun hle => by rw [hm.freshO a hle] at h; cases h)
  have hhlt : ∀ n hd, m.handle? n = some hd → n < m.nextHandle := fun n hd h =>
    Nat.lt_of_not_le (fun hle => by rw [hm.freshH n hle] at h; cases h)
  -- Old objects stay, with their adds.
  have hold3 : ∀ a o, m.obj? a = some o → m3.obj? a = some (updAllH sp db.P (k + 1) m1
      (c.adds.filter (fun e => m1.canonicalOf e.1 == some a)) o) := by
    intro a o ho
    rw [hcf.obj a, haf.old a (holt a o ho), ho]; rfl
  have hobj3 : ∀ b o1, m1.obj? b = some o1 → ∃ o3, m3.obj? b = some o3 ∧ o3.node = o1.node ∧
      o3.canonical = o1.canonical ∧ o3.pos = o1.pos := by
    intro b o1 h1
    obtain ⟨a1, -, -, -, a5, a6⟩ := updAllH_core sp db.P (k + 1) m1
      (c.adds.filter (fun e => m1.canonicalOf e.1 == some b)) o1
    exact ⟨_, by rw [hcf.obj b, h1]; rfl, a1, a5, a6⟩
  have hnotnew : ∀ y n, db.P.get? y = some n → y ∉ c.new.map (·.id) := fun y n hn => not_new_of_get? hstep hn
  have hfilt_old : ∀ a o, m.obj? a = some o →
      c.adds.filter (fun e => m1.canonicalOf e.1 == some a) =
        if o.canonical then c.adds.filter (fun e => e.1 == o.node) else [] := by
    intro a o ho
    cases hco : o.canonical with
    | true =>
      simp only [↓reduceIte]
      apply hfilt
      obtain ⟨n, hn', -⟩ := hm.cc a o ho hco
      rw [haf.canOld o.node (hnotnew _ _ hn')]
      exact hm.canonicalOf_of ho hco
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      apply List.filter_eq_nil_iff.mpr
      intro e _ he
      simp only [beq_iff_eq] at he
      obtain ⟨o', ho', -, hc'⟩ := haf.tbl.canonicalOf_node he
      rw [haf.old a (holt a o ho), ho, Option.some.injEq] at ho'
      subst ho'
      rw [hco] at hc'; cases hc'
  -- The objects of m3: an old snapshot, an old canonical object with its node's adds, or
  -- a new node's object with its adds.
  have hcls : ∀ a o3, m3.obj? a = some o3 →
      (∃ o, m.obj? a = some o ∧ ((o.canonical = false ∧ o3 = o) ∨
        (o.canonical = true ∧ o3 = updAllH sp db.P (k + 1) m1 (c.adds.filter (fun e => e.1 == o.node)) o))) ∨
      (m.nextObj ≤ a ∧ ∃ nn ∈ c.new, m1.canonicalOf nn.id = some a ∧ m1.obj? a = some (hnewObj nn) ∧
        o3 = updAllH sp db.P (k + 1) m1 (c.adds.filter (fun e => e.1 == nn.id)) (hnewObj nn)) := by
    intro a o3 ho3
    rw [hcf.obj a] at ho3
    cases h1 : m1.obj? a with
    | none => rw [h1] at ho3; cases ho3
    | some o1 =>
      rw [h1] at ho3
      simp only [Option.map_some, Option.some.injEq] at ho3
      rcases haf.cls a o1 h1 with ⟨-, h2⟩ | ⟨hle, nn, hnn, hon, hc⟩
      · left
        refine ⟨o1, h2, ?_⟩
        rw [hfilt_old a o1 h2] at ho3
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
        rw [hfilt hc, hon] at ho3
        exact ⟨hle, nn, hnn, hc, by rw [hon], ho3.symm⟩
  -- Every object of m keeps its node, kind, level, flag and position.
  have hkeep : ∀ a o, m.obj? a = some o → ∃ o3, m3.obj? a = some o3 ∧ o3.node = o.node ∧
      o3.level = o.level ∧ o3.isData = o.isData ∧ o3.canonical = o.canonical ∧ o3.pos = o.pos := by
    intro a o ho
    obtain ⟨a1, a2, a3, -, a5, a6⟩ := updAllH_core sp db.P (k + 1) m1
      (c.adds.filter (fun e => m1.canonicalOf e.1 == some a)) o
    exact ⟨_, hold3 a o ho, a1, a2, a3, a5, a6⟩
  -- The canonical objects of m1.
  have hcan1 : ∀ y b, m1.canonicalOf y = some b →
      (y ∉ c.new.map (·.id) ∧ m.canonicalOf y = some b) ∨
      (∃ nn ∈ c.new, nn.id = y ∧ m1.obj? b = some (hnewObj nn)) := by
    intro y b hy
    by_cases hyn : y ∈ c.new.map (·.id)
    · obtain ⟨nn, hnn, hid⟩ := List.mem_map.mp hyn
      obtain ⟨b', n', -, -, -, hc', ho'⟩ := haf.canNew nn hnn
      rw [hid, hy, Option.some.injEq] at hc'
      subst hc'
      exact Or.inr ⟨nn, hnn, hid, ho'⟩
    · left; exact ⟨hyn, by rw [← haf.canOld y hyn]; exact hy⟩
  -- The position of a canonical object of m1 in m3: its node's latest version, before.
  have hposc : ∀ y b, m1.canonicalOf y = some b →
      (m3.obj? b).bind (·.pos) = (db.S.lv y).map (·.recNo) := by
    intro y b hy
    rcases hcan1 y b hy with ⟨-, hc⟩ | ⟨nn, hnn, hid, ho1⟩
    · obtain ⟨o, ho, hco, hno⟩ := hm.obj_of_canonicalOf hc
      obtain ⟨o3, ho3, -, -, -, -, hp3⟩ := hkeep b o ho
      rw [ho3]; simp only [Option.bind_some, hp3]
      rw [← hno]; exact hm.pos b o ho hco
    · rw [hcf.obj b, ho1]
      simp only [Option.map_some, Option.bind_some, (updAllH_core sp db.P (k + 1) _ _ _).2.2.2.2.2]
      simp only [hnewObj]
      cases hl : db.S.lv y with
      | none => rfl
      | some v =>
        exfalso
        obtain ⟨-, -, n, hn, -⟩ := hinv.version_node (hinv.lv_at hl)
        exact hnotnew y n hn (by rw [← hid]; exact List.mem_map.mpr ⟨nn, hnn, rfl⟩)
  -- The record rule for a pointer of an object of m: the same in m3.
  have hpref3 : ∀ a0 o0, m.obj? a0 = some o0 → ∀ z p, o0.ptr? z = some p →
      m3.ptrRef S0 z p = m.ptrRef S0 z p := by
    intro a0 o0 ho0 z p hp
    apply HMem.ptrRef_congr S0 (by rw [hcf.s, haf.s])
    · cases hpn : p.handle with
      | none => rfl
      | some n =>
        obtain ⟨hd, hh, -⟩ := hm.tbl.ptrNode ho0 hp hpn
        simp only [Option.bind_some]
        rw [hcf.handle?, haf.hold n (hhlt n hd hh)]
    · intro hd b hph hb
      have hob : ∃ ob, m.obj? b = some ob := by
        cases hpn : p.handle with
        | none => rw [hpn] at hph; cases hph
        | some n =>
          rw [hpn] at hph
          simp only [Option.bind_some] at hph
          obtain ⟨-, ob, hob, -⟩ := hm.tbl.obj_of_handle hph hb
          exact ⟨ob, hob⟩
      obtain ⟨ob, hob⟩ := hob
      obtain ⟨o3, ho3, -, -, -, e5, e6⟩ := hkeep b ob hob
      rw [ho3, hob]
      simp only [Option.map_some, e5, e6]
  -- That a pointer holds a node's live handle, for a node that is not new: the same in m3.
  have hhl3 : ∀ y p, y ∉ c.new.map (·.id) → (m3.HoldsLive y p ↔ m.HoldsLive y p) := by
    intro y p hy
    unfold HMem.HoldsLive
    rw [htab3, hcan3, haf.tabOld y hy, haf.canOld y hy]
  -- The new pointer of a pointee, in m3.
  have hns3 : ∀ y p, NSH sp db.P (k + 1) m1 y = some p →
      (m3.HoldsLive y p ∧ m3.ptrRef S0 y p = (db.S.lv y).map (·.recNo)) ∨
      (m3.canonicalOf y = none ∧ inD db.D y = false ∧ y ∉ c.new.map (·.id) ∧
        m3.ptrRef S0 y p = (db.S.lv y).map (·.recNo)) := by
    intro y p hns
    rcases hgood hns with ⟨b, hc, rfl⟩ | ⟨hc, hyD, hyn, hval, a0, o0, ho0, hp0⟩
    · left
      obtain ⟨n, ob, ht1, hob1, ho1, hco1⟩ := (m1.canonicalOf_eq_some y b).mp hc
      obtain ⟨hd, hh1, hb1⟩ : ∃ hd, m1.handle? n = some hd ∧ hd.obj = some b := by
        unfold HMem.objOf at hob1
        cases h : m1.handle? n with
        | none => rw [h] at hob1; cases hob1
        | some hd => rw [h] at hob1; exact ⟨hd, rfl, hob1⟩
      obtain ⟨o3, ho3, -, hc3, -⟩ := hobj3 b ob ho1
      refine ⟨⟨n, by simp only [ht1], by rw [htab3]; exact ht1, by simp [hcan3, hc]⟩, ?_⟩
      have hpr : m3.ptrRef S0 y { ref := (m1.obj? b).bind (·.pos), handle := m1.tableOf y } = o3.pos := by
        unfold HMem.ptrRef
        simp only [ht1, Option.bind_some, hcf.handle? n, hh1, hb1, ho3, hc3, hco1, ↓reduceIte]
      rw [hpr]
      have := hposc y b hc
      rw [ho3] at this
      exact this
    · right
      exact ⟨by rw [hcan3]; exact hc, hyD, hyn, by rw [hpref3 a0 o0 ho0 y p hp0]; exact hval⟩
  -- The pointers of a canonical object of m3: from the adds (new pointers), or as before.
  have hslot_upd : ∀ (L : List (NodeId × V)) (o : HObj V) (z : NodeId), (∀ e ∈ L, e ∈ c.adds) →
      z ∈ L.flatMap (fun e => sp.ptrs e.2) →
      ∃ p, (updAllH sp db.P (k + 1) m1 L o).ptr? z = some p ∧ NSH sp db.P (k + 1) m1 z = some p := by
    intro L o z hL hz
    obtain ⟨e, he, hze⟩ := List.mem_flatMap.mp hz
    obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp (hcopyNS e (hL e he) z hze)
    refine ⟨p, ?_, hp⟩
    rw [updAllH_ptr]
    simp only [hz, ↓reduceIte]
    unfold comboH; rw [hp]; rfl
  have hLadds : ∀ (x : NodeId), ∀ e ∈ c.adds.filter (fun e => e.1 == x), e ∈ c.adds :=
    fun x e he => (List.mem_filter.mp he).1
  -- Where a pointer of m3 comes from: a pointer of an object of m, or a new pointer to a
  -- canonical object of m1.
  have hslot3 : ∀ a o3 z p, m3.obj? a = some o3 → o3.ptr? z = some p →
      (∃ a0 o0, m.obj? a0 = some o0 ∧ o0.ptr? z = some p) ∨
      (∃ b, m1.canonicalOf z = some b ∧ p = { ref := (m1.obj? b).bind (·.pos), handle := m1.tableOf z }) := by
    intro a o3 z p ho3 hz
    have hupd : ∀ (L : List (NodeId × V)) (o : HObj V), (∀ e ∈ L, e ∈ c.adds) →
        (updAllH sp db.P (k + 1) m1 L o).ptr? z = some p →
        o.ptr? z = some p ∨ NSH sp db.P (k + 1) m1 z = some p := by
      intro L o hL hz'
      by_cases hin : z ∈ L.flatMap (fun e => sp.ptrs e.2)
      · obtain ⟨p', hp', hns⟩ := hslot_upd L o z hL hin
        rw [hp', Option.some.injEq] at hz'
        subst hz'
        exact Or.inr hns
      · rw [updAllH_ptr] at hz'
        simp only [hin, ↓reduceIte] at hz'
        exact Or.inl hz'
    have hns_case : NSH sp db.P (k + 1) m1 z = some p →
        (∃ a0 o0, m.obj? a0 = some o0 ∧ o0.ptr? z = some p) ∨
        (∃ b, m1.canonicalOf z = some b ∧ p = { ref := (m1.obj? b).bind (·.pos), handle := m1.tableOf z }) := by
      intro hns
      rcases hgood hns with ⟨b, hc, hpe⟩ | ⟨-, -, -, -, a0, o0, ho0, hp0⟩
      · exact Or.inr ⟨b, hc, hpe⟩
      · exact Or.inl ⟨a0, o0, ho0, hp0⟩
    rcases hcls a o3 ho3 with ⟨o, ho, ⟨-, rfl⟩ | ⟨-, rfl⟩⟩ | ⟨-, nn, -, -, -, rfl⟩
    · exact Or.inl ⟨a, o3, ho, hz⟩
    · rcases hupd _ o (hLadds o.node) hz with h1 | h1
      · exact Or.inl ⟨a, o, ho, h1⟩
      · exact hns_case h1
    · rcases hupd _ (hnewObj nn) (hLadds nn.id) hz with h1 | h1
      · simp [hnewObj, HObj.ptr?] at h1
      · exact hns_case h1
  -- CC after the change.
  have hcc3 : ∀ a o3, m3.obj? a = some o3 → o3.canonical = true →
      ∃ n, (db.P.apply (k + 1) c).get? o3.node = some n ∧ o3.hist = n.hist ∧ o3.level = n.level ∧
        o3.isData = n.isData := by
    intro a o3 ho3 hc3
    rcases hcls a o3 ho3 with ⟨o, ho, ⟨hco, rfl⟩ | ⟨hco, rfl⟩⟩ | ⟨-, nn, hnn, -, -, rfl⟩
    · rw [hco] at hc3; cases hc3
    · obtain ⟨n, hn, h1, h2, h3⟩ := hm.cc a o ho hco
      obtain ⟨a1, a2, a3, a4, -, -⟩ := updAllH_core sp db.P (k + 1) m1
        (c.adds.filter (fun e => e.1 == o.node)) o
      refine ⟨_, by rw [a1]; exact get?_apply_of_get? hn, ?_, by rw [a2, h2], by rw [a3, h3]⟩
      rw [a4, h1]; rfl
    · obtain ⟨a1, a2, a3, a4, -, -⟩ := updAllH_core sp db.P (k + 1) m1
        (c.adds.filter (fun e => e.1 == nn.id)) (hnewObj nn)
      obtain ⟨m0, hm0⟩ := Option.isSome_iff_exists.mp (newNodeOf_isSome (V := V) hnn)
      obtain ⟨nn', hnn', hid', hm0e⟩ := newNodeOf_some hm0
      have hnn'' : nn' = nn := new_unique hstep.distinct hnn' hnn hid'
      subst hnn''
      have hget : (db.P.apply (k + 1) c).get? nn'.id =
          some { m0 with hist := m0.hist ++ addsFor c (k + 1) nn'.id } := by
        rw [get?_apply, hstep.fresh nn' hnn', hm0]; rfl
      refine ⟨_, by rw [a1]; exact hget, ?_, ?_, ?_⟩
      · rw [a4, hm0e]; rfl
      · rw [a2, hm0e]; rfl
      · rw [a3, hm0e]; rfl
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
  refine
    { pre := hm.pre
      sEq := by rw [hcf.s, haf.s]; exact hm.sEq
      freshO := fun a ha => by
        rw [hcf.obj a, haf.freshO a (by rw [← hcf.nextObj]; exact ha)]; rfl
      freshH := fun n hn => by
        rw [hcf.handle? n]; exact haf.freshH n (by rw [← hcf.nextHandle]; exact hn)
      objNodup := hcf.nodup haf.nodup
      hNodup := by rw [hcf.handles]; exact haf.hnodup
      root := ?_
      tbl := ?_
      liveW := ?_
      cc := hcc3
      pos := ?_
      canon := ?_
      snap := ?_
      ruleR := ?_
      wver := ?_
      rver := ?_
      slots := ?_
      live := ?_ }
  · -- root
    obtain ⟨o, ho, hc, hn⟩ := hm.root
    obtain ⟨o3, ho3, e1, -, -, e5, -⟩ := hkeep _ o ho
    exact ⟨o3, by rw [hcf.root, haf.root]; exact ho3, by rw [e5, hc], by rw [e1, hn]⟩
  · -- the table and the handles
    have ht1 := haf.tbl
    refine ⟨fun y n hy => ?_, by rw [hcf.table]; exact ht1.nodup, fun n hd hh hl => ?_,
      fun n hd hh hdd => ?_, fun a o3 ho3 => ?_, fun a o3 y p n ho3 hp hpn => ?_⟩
    · rw [htab3] at hy
      obtain ⟨hd, b, o1, hh, hl, hny, hb, ho1, hon⟩ := ht1.entry hy
      obtain ⟨o3, ho3, e1, -⟩ := hobj3 b o1 ho1
      exact ⟨hd, b, o3, by rw [hcf.handle?]; exact hh, hl, hny, hb, ho3, by rw [e1, hon]⟩
    · rw [hcf.handle?] at hh; rw [htab3]; exact ht1.liveIn hh hl
    · rw [hcf.handle?] at hh; exact ht1.deadNone hh hdd
    · rw [hcf.obj a] at ho3
      cases h1 : m1.obj? a with
      | none => rw [h1] at ho3; cases ho3
      | some o1 =>
        rw [h1] at ho3
        simp only [Option.map_some, Option.some.injEq] at ho3
        subst ho3
        obtain ⟨n, htn, hob⟩ := ht1.held h1
        exact ⟨n, by rw [htab3, (updAllH_core sp db.P (k + 1) m1 _ o1).1]; exact htn,
          by rw [hcf.objOf]; exact hob⟩
    · rcases hslot3 a o3 y p ho3 hp with ⟨a0, o0, ho0, hp0⟩ | ⟨b, hc, rfl⟩
      · obtain ⟨hd, hh, hy⟩ := hm.tbl.ptrNode ho0 hp0 hpn
        exact ⟨hd, by rw [hcf.handle?, haf.hold n (hhlt n hd hh)]; exact hh, hy⟩
      · obtain ⟨n', ob, ht', -, -, -⟩ := (m1.canonicalOf_eq_some y b).mp hc
        simp only at hpn
        rw [ht', Option.some.injEq] at hpn
        subst hpn
        obtain ⟨hd, -, -, hh, -, hny, -⟩ := ht1.entry ht'
        exact ⟨hd, by rw [hcf.handle?]; exact hh, hny⟩
  · -- live handles have no written position
    intro n hd hh hl
    rw [hcf.handle?] at hh
    rcases haf.hcls n hd hh with ⟨-, hh'⟩ | ⟨-, nn, -, a, -, rfl, -, -⟩
    · exact hm.liveW n hd hh' hl
    · rfl
  · -- positions
    intro a o3 ho3 hc3
    rcases hcls a o3 ho3 with ⟨o, ho, ⟨hco, rfl⟩ | ⟨hco, rfl⟩⟩ | ⟨-, nn, hnn, -, -, rfl⟩
    · rw [hco] at hc3; cases hc3
    · obtain ⟨a1, -, -, -, -, a6⟩ := updAllH_core sp db.P (k + 1) m1
        (c.adds.filter (fun e => e.1 == o.node)) o
      rw [a1, a6]; exact hm.pos a o ho hco
    · obtain ⟨a1, -, -, -, -, a6⟩ := updAllH_core sp db.P (k + 1) m1
        (c.adds.filter (fun e => e.1 == nn.id)) (hnewObj nn)
      rw [a1, a6]
      simp only [hnewObj]
      cases hl : db.S.lv nn.id with
      | none => rfl
      | some v =>
        exfalso
        obtain ⟨-, -, n, hn, -⟩ := hinv.version_node (hinv.lv_at hl)
        rw [hstep.fresh nn hnn] at hn; cases hn
  · -- canonical objects
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
      obtain ⟨a, n, -, -, -, hc', -⟩ := haf.canNew nn hnn
      rw [hcan3, ← hid, hc']; rfl
  · -- snapshots
    intro a o3 ho3 hc3
    rcases hcls a o3 ho3 with ⟨o, ho, ⟨hco, rfl⟩ | ⟨hco, rfl⟩⟩ | ⟨-, nn, -, -, -, rfl⟩
    · exact (hm.snap a o3 ho hco).of_s (by rw [hcf.s, haf.s])
    · rw [(updAllH_core sp db.P (k + 1) m1 _ o).2.2.2.2.1, hco] at hc3; cases hc3
    · rw [(updAllH_core sp db.P (k + 1) m1 _ (hnewObj nn)).2.2.2.2.1] at hc3; cases hc3
  · -- the snapshots against Rule R
    intro n hd b o3 w hh hb ho3 hc3 hw
    rw [hcf.handle?] at hh
    rw [hcf.s, haf.s] at hw
    rcases hcls b o3 ho3 with ⟨o, ho, ⟨hco, rfl⟩ | ⟨hco, rfl⟩⟩ | ⟨-, nn, -, -, -, rfl⟩
    · rcases haf.hcls n hd hh with ⟨-, hh'⟩ | ⟨-, nn, -, a, hla, rfl, -, -⟩
      · exact hm.ruleR n hd b o3 w hh' hb ho hco hw
      · exfalso
        simp only [hnewHandle, Option.some.injEq] at hb
        have := holt b o3 ho
        omega
    · rw [(updAllH_core sp db.P (k + 1) m1 _ o).2.2.2.2.1, hco] at hc3; cases hc3
    · rw [(updAllH_core sp db.P (k + 1) m1 _ (hnewObj nn)).2.2.2.2.1] at hc3; cases hc3
  · -- written positions name versions
    intro n hd w hh hw
    rw [hcf.handle?] at hh
    rcases haf.hcls n hd hh with ⟨-, hh'⟩ | ⟨-, nn, -, a, -, rfl, -, -⟩
    · exact hm.wver n hd w hh' hw
    · cases hw
  · -- references name versions
    intro a o3 y p r ho3 hp hr
    rcases hslot3 a o3 y p ho3 hp with ⟨a0, o0, ho0, hp0⟩ | ⟨b, hc, rfl⟩
    · exact hm.rver a0 o0 y p r ho0 hp0 hr
    · simp only at hr
      rcases hcan1 y b hc with ⟨-, hcm⟩ | ⟨nn, -, -, ho1⟩
      · obtain ⟨ob, hob, hcob, hnob⟩ := hm.obj_of_canonicalOf hcm
        rw [haf.old b (holt b ob hob), hob] at hr
        simp only [Option.bind_some] at hr
        rw [hm.pos b ob hob hcob, hnob] at hr
        cases hl : db.S.lv y with
        | none => rw [hl] at hr; cases hr
        | some v =>
          rw [hl] at hr
          simp only [Option.map_some, Option.some.injEq] at hr
          subst hr
          exact ⟨v, hinv.lv_at hl⟩
      · rw [ho1] at hr; simp [hnewObj] at hr
  · -- the pointers that records need
    intro a o3 ho3 hc3 hw3 hrel3 z hz
    -- The new pointer of a pointee, as the record rule asks after the change.
    have hnsok : ∀ p, NSH sp db.P (k + 1) m1 z = some p →
        (inD db.D z = false → m3.ptrRef S0 z p = (db.S.lv z).map (·.recNo) ∧
          (z ∈ c.new.map (·.id) → m3.HoldsLive z p)) ∧
        (inD db.D z = true → m3.HoldsLive z p ∨
          (inD db.D o3.node = true ∧ ∃ a b, dOf db.D o3.node = some a ∧ dOf db.D z = some b ∧ a ≤ b)) := by
      intro p hns
      rcases hns3 z p hns with ⟨hhl, hval⟩ | ⟨-, hzD, hzn, hval⟩
      · exact ⟨fun _ => ⟨hval, fun _ => hhl⟩, fun _ => Or.inl hhl⟩
      · refine ⟨fun _ => ⟨hval, fun h => absurd h hzn⟩, fun h => ?_⟩
        rw [hzD] at h; cases h
    rcases hcls a o3 ho3 with ⟨o, ho, ⟨hco, rfl⟩ | ⟨hco, rfl⟩⟩ | ⟨-, nn, hnn, -, -, rfl⟩
    · rw [hco] at hc3; cases hc3
    · -- an old canonical object
      obtain ⟨a1, -, -, a4, -, -⟩ := updAllH_core sp db.P (k + 1) m1
        (c.adds.filter (fun e => e.1 == o.node)) o
      rw [a1] at hw3 hrel3 ⊢
      obtain ⟨n, hn, -⟩ := hm.cc a o ho hco
      have hrel : HRelevant sp db k o := by
        refine ⟨hco, hw3, ?_⟩
        rcases hrel3 with hr | hd | hr
        · rcases hstep.noRes o.node hr with hr' | hnew
          · rw [hK1] at hr'; exact Or.inl hr'
          · exact absurd hnew (hnotnew _ _ hn)
        · exact Or.inr hd
        · exact Or.inl hr
      by_cases hin : z ∈ (c.adds.filter (fun e => e.1 == o.node)).flatMap (fun e => sp.ptrs e.2)
      · obtain ⟨p, hp, hns⟩ := hslot_upd _ o z (hLadds o.node) hin
        have := hnsok p hns
        rw [a1] at this
        exact ⟨p, hp, this⟩
      · have hzo : z ∈ pointees sp o.hist := by
          rw [a4] at hz
          rcases pointees_append_mem hz with hz | hz
          · exact hz
          · obtain ⟨e, he, hze⟩ := pointees_adds_mem hz
            exact absurd (List.mem_flatMap.mpr ⟨e, he, hze⟩) hin
        obtain ⟨p, hp, hi⟩ := hm.slots a o ho hrel z hzo
        have hp3 : (updAllH sp db.P (k + 1) m1 (c.adds.filter (fun e => e.1 == o.node)) o).ptr? z = some p := by
          rw [updAllH_ptr]; simp only [hin, ↓reduceIte]; exact hp
        -- z is a node of P: not new
        have hzP : ∃ nz, db.P.get? z = some nz := by
          rw [mem_pointees] at hzo
          obtain ⟨e, he, hze⟩ := hzo
          obtain ⟨n0, hn0, hh0, -, -⟩ := hm.cc a o ho hco
          obtain ⟨nz, hnz, -⟩ := hinv.ptrs o.node n0 hn0 e (by rw [← hh0]; exact he) z hze
          exact ⟨nz, hnz⟩
        obtain ⟨nz, hnz⟩ := hzP
        refine ⟨p, hp3, fun hzD => ⟨by rw [hpref3 a o ho z p hp]; exact hi.1 hzD,
          fun h' => absurd h' (hnotnew z nz hnz)⟩, fun hzD => ?_⟩
        rcases hi.2 hzD with h' | h2
        · exact Or.inl ((hhl3 z p (hnotnew z nz hnz)).mpr h')
        · exact Or.inr h2
    · -- a new node's object
      obtain ⟨a1, -, -, a4, -, -⟩ := updAllH_core sp db.P (k + 1) m1
        (c.adds.filter (fun e => e.1 == nn.id)) (hnewObj nn)
      rw [a1]
      have hin : z ∈ (c.adds.filter (fun e => e.1 == nn.id)).flatMap (fun e => sp.ptrs e.2) := by
        rw [a4] at hz
        rcases pointees_append_mem hz with hz | hz
        · simp [hnewObj, pointees] at hz
        · obtain ⟨e, he, hze⟩ := pointees_adds_mem hz
          exact List.mem_flatMap.mpr ⟨e, he, hze⟩
      obtain ⟨p, hp, hns⟩ := hslot_upd _ (hnewObj nn) z (hLadds nn.id) hin
      have := hnsok p hns
      rw [(updAllH_core sp db.P (k + 1) m1 _ (hnewObj nn)).1] at this
      exact ⟨p, hp, this⟩
  · -- the live pointers that reads and the writer's walk need
    intro a o3 ho3 hc3 hr3 z hz
    obtain ⟨n', hn', hh', -, -⟩ := hcc3 a o3 ho3 hc3
    have hz' : z ∈ sp.live (n'.hist.upTo (k + 1)) := by
      rw [upTo_of_forall _ _ (htimes' _ n' hn'), ← hh']; exact hz
    -- The new pointer of a pointee, as the live pointers ask after the change.
    have hnsok : ∀ p, NSH sp db.P (k + 1) m1 z = some p →
        ((inD db.D z = true ∨ z ∈ path ∨ z ∈ c.new.map (·.id)) → m3.HoldsLive z p) ∧
        (inD db.D z = false → m3.ptrRef S0 z p = (db.S.lv z).map (·.recNo)) := by
      intro p hns
      rcases hns3 z p hns with ⟨hhl, hval⟩ | ⟨hc, hzD, hzn, hval⟩
      · exact ⟨fun _ => hhl, fun _ => hval⟩
      · refine ⟨fun hcase => ?_, fun _ => hval⟩
        exfalso
        rcases hcase with hcase | hcase | hcase
        · rw [hzD] at hcase; cases hcase
        · obtain ⟨nz, hnz⟩ := Option.isSome_iff_exists.mp (hpn z hcase)
          rw [hold_can z (hnotnew z nz hnz)] at hc
          exact hpdm z hcase hc
        · exact hzn hcase
    rcases hphys.liveNew o3.node n' hn' z hz' with ⟨n0, hn0, hzl0⟩ | ⟨e, he, hex, hze⟩
    · -- live at k already
      rw [hK1] at hzl0
      rcases hcls a o3 ho3 with ⟨o, ho, ⟨hco, rfl⟩ | ⟨hco, rfl⟩⟩ | ⟨-, nn, hnn, -, -, rfl⟩
      · rw [hco] at hc3; cases hc3
      · obtain ⟨a1, -, -, -, -, -⟩ := updAllH_core sp db.P (k + 1) m1
          (c.adds.filter (fun e => e.1 == o.node)) o
        rw [a1] at hn0 hr3
        by_cases hin : z ∈ (c.adds.filter (fun e => e.1 == o.node)).flatMap (fun e => sp.ptrs e.2)
        · obtain ⟨p, hp, hns⟩ := hslot_upd _ o z (hLadds o.node) hin
          exact ⟨p, hp, hnsok p hns⟩
        · obtain ⟨n, hn, hhn, -, -⟩ := hm.cc a o ho hco
          rw [hn, Option.some.injEq] at hn0
          subst hn0
          have hrk : reachable sp db.P k o.node = true := by
            rcases hstep.noRes o.node hr3 with hr' | hnew
            · rw [hK1] at hr'; exact hr'
            · exact absurd hnew (hnotnew _ _ hn)
          have hzo : z ∈ sp.live o.hist := by
            rw [hhn, ← upTo_of_forall _ _ (hinv.times _ n hn)]; exact hzl0
          obtain ⟨p, hp, hli1, hli2⟩ := hm.live a o ho hco hrk z hzo
          have hp3 : (updAllH sp db.P (k + 1) m1 (c.adds.filter (fun e => e.1 == o.node)) o).ptr? z = some p := by
            rw [updAllH_ptr]; simp only [hin, ↓reduceIte]; exact hp
          -- z is a node of P, below o's node
          obtain ⟨e, he, hze⟩ := hls _ _ hzl0
          obtain ⟨nz, hnz, hlt⟩ := hinv.ptrs o.node n hn e (mem_upTo.mp he).1 z hze
          have hzr : z ≠ SIS.root := hinv.ptr_ne_root hn (mem_upTo.mp he).1 hze
          have hrz : reachable sp db.P k z = true := by
            rw [reachable_iff] at hrk ⊢; exact Reach.child hrk hn hzl0 hnz hlt
          refine ⟨p, hp3, fun hcase => ?_, fun hzD => by rw [hpref3 a o ho z p hp]; exact hli2 hzD⟩
          rcases hcase with hcase | hcase | hcase
          · exact (hhl3 z p (hnotnew z nz hnz)).mpr (hli1 hcase)
          · -- z is on the path: its parent's pointer on the path holds its live handle,
            -- and by TREE that parent is o's node.
            obtain ⟨-, hpz⟩ := hpd z hcase
            obtain ⟨q, hq, nq, bq, oq, ptr, hnq, hzq, hcq, hoq, hptr, hhl⟩ := hpz hzr
            have hxq : o.node = q := treeAt_unique htree hrz hzr hrk (hpr q hq) hn hnq hzl0 hzq
            have hco' := hm.canonicalOf_of ho hco
            rw [hxq, hcq, Option.some.injEq] at hco'
            subst hco'
            rw [ho, Option.some.injEq] at hoq
            subst hoq
            rw [hp, Option.some.injEq] at hptr
            subst hptr
            exact (hhl3 z p (hnotnew z nz hnz)).mpr hhl
          · exact absurd hcase (hnotnew z nz hnz)
      · -- a new node has no live child but from its entries
        exfalso
        rw [(updAllH_core sp db.P (k + 1) m1 _ (hnewObj nn)).1] at hn0
        have := hstep.fresh nn hnn
        simp only [hnewObj] at hn0
        rw [hn0] at this; cases this
    · -- a pointer of an entry of this transaction
      have hin : ∀ x, o3.node = x → z ∈ (c.adds.filter (fun e => e.1 == x)).flatMap (fun e => sp.ptrs e.2) := by
        intro x hx
        exact List.mem_flatMap.mpr ⟨e, List.mem_filter.mpr ⟨he, by simp [hex, hx]⟩, hze⟩
      rcases hcls a o3 ho3 with ⟨o, ho, ⟨hco, rfl⟩ | ⟨hco, rfl⟩⟩ | ⟨-, nn, hnn, -, -, rfl⟩
      · rw [hco] at hc3; cases hc3
      · obtain ⟨a1, -, -, -, -, -⟩ := updAllH_core sp db.P (k + 1) m1
          (c.adds.filter (fun e => e.1 == o.node)) o
        obtain ⟨p, hp, hns⟩ := hslot_upd _ o z (hLadds o.node) (hin o.node a1)
        exact ⟨p, hp, hnsok p hns⟩
      · obtain ⟨a1, -, -, -, -, -⟩ := updAllH_core sp db.P (k + 1) m1
          (c.adds.filter (fun e => e.1 == nn.id)) (hnewObj nn)
        obtain ⟨p, hp, hns⟩ := hslot_upd _ (hnewObj nn) z (hLadds nn.id) (hin nn.id a1)
        exact ⟨p, hp, hnsok p hns⟩

/-- The change applied after the writer's paths: `HAInv`. -/
theorem HEInv.applyChange_ok (hinv : Inv sp db k) (hls : LiveSub sp) (hm : HEInv sp db S0 k m)
    (hpd : ∀ x ∈ pathOf sp db.P c (k + 1), HPathDone sp db.P k (pathOf sp db.P c (k + 1)) m x)
    (hstep : StepOK sp db.P (k + 1) c) (hphys : PhysStep sp db.P (k + 1) c)
    (hcopy : CopyStep sp db.P (k + 1) c) (htree : treeAt sp db.P k) :
    HAInv sp db S0 k c (pathOf sp db.P c (k + 1)) (m.applyChange sp db.P (k + 1) c) := by
  have hK1 : k + 1 - 1 = k := by omega
  have hpr : ∀ p ∈ pathOf sp db.P c (k + 1), reachable sp db.P k p = true := by
    intro p hp; have := (mem_pathOf hp).1; rw [hK1] at this; exact this
  have hpn : ∀ p ∈ pathOf sp db.P c (k + 1), (db.P.get? p).isSome := by
    intro p hp; obtain ⟨-, n, hn, -⟩ := mem_pathOf hp; rw [hn]; rfl
  refine hm.applyChange_core hinv hls hpd hpr hpn hstep hphys htree (hm.addFactsH hinv hstep)
    (changeFactsH sp db.P (k + 1) c m) ?_ (fun hns => hm.NSH_good hinv hstep hns)
  intro e he y hy
  by_cases hyn : y ∈ c.new.map (·.id)
  · exact hm.NSH_some hinv hpd hpr hpn hstep (Or.inl hyn)
  · rcases hcopy e he y hy hyn with h | ⟨z, hz, nz, hnz, hyz, hwl⟩
    · exact hm.NSH_some hinv hpd hpr hpn hstep (Or.inr (Or.inl h))
    · rw [hK1] at hwl
      exact hm.NSH_some hinv hpd hpr hpn hstep (Or.inr (Or.inr ⟨z, hz, nz, hnz, hyz, hwl⟩))

end ApplyInv

end SIS
