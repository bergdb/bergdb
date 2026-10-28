/-
Proofs about the physical layer with handles (bergdb item 009, step 2d), part
10: after the record, the memory with handles has the invariant of the next
state (INV-SLOT across D's changes).
-/
import SIS.Proof.HandleWrites

set_option linter.unusedSectionVars false

namespace SIS

variable {V T : Type} [DecidableEq V]

/-! ## Pointers after the writes -/

/-- A pointer to z (its handle, if any, is of node z) that holds a canonical
object holds z's live handle, which holds z's canonical object. -/
theorem HMem.holdsLive_of_holdsCanonical {m : HMem V} (ht : HTableOK m) {z : NodeId} {q : HPtr}
    (hq : ∀ n hd, q.handle = some n → m.handle? n = some hd → hd.node = z) (h : m.holdsCanonical q = true) :
    m.HoldsLive z q := by
  unfold HMem.holdsCanonical at h
  cases hqn : q.handle with
  | none => rw [hqn] at h; simp at h
  | some n =>
    rw [hqn] at h
    simp only [Option.bind_some] at h
    unfold HMem.objOf at h
    cases hh : m.handle? n with
    | none => rw [hh] at h; simp at h
    | some hd =>
      rw [hh] at h
      simp only [Option.bind_some] at h
      cases hb : hd.obj with
      | none => rw [hb] at h; simp at h
      | some b =>
        rw [hb] at h
        simp only [Option.bind_some] at h
        cases ho : m.obj? b with
        | none => rw [ho] at h; simp at h
        | some o =>
          rw [ho] at h
          simp only at h
          have hz := hq n hd hqn hh
          have htn : m.tableOf z = some n := by
            rw [← hz]; exact ht.liveIn hh (ht.live_of_obj hh hb)
          refine ⟨n, hqn, htn, ?_⟩
          have hcz : m.canonicalOf z = some b :=
            (m.canonicalOf_eq_some z b).mpr ⟨n, o, htn, by unfold HMem.objOf; rw [hh]; exact hb, ho, h⟩
          simp [hcz]

/-- The record rule for a pointer to z that holds a canonical object: that
object's position, an object of z. -/
theorem HMem.ptrRef_of_holdsCanonical {m : HMem V} (S0 : Stream V T) (ht : HTableOK m) {z : NodeId}
    {q : HPtr} (hq : ∀ n hd, q.handle = some n → m.handle? n = some hd → hd.node = z)
    (h : m.holdsCanonical q = true) :
    ∃ b o, m.obj? b = some o ∧ o.canonical = true ∧ o.node = z ∧ m.ptrRef S0 z q = o.pos := by
  unfold HMem.holdsCanonical at h
  cases hqn : q.handle with
  | none => rw [hqn] at h; simp at h
  | some n =>
    rw [hqn] at h
    simp only [Option.bind_some] at h
    unfold HMem.objOf at h
    cases hh : m.handle? n with
    | none => rw [hh] at h; simp at h
    | some hd =>
      rw [hh] at h
      simp only [Option.bind_some] at h
      cases hb : hd.obj with
      | none => rw [hb] at h; simp at h
      | some b =>
        rw [hb] at h
        simp only [Option.bind_some] at h
        cases ho : m.obj? b with
        | none => rw [ho] at h; simp at h
        | some o =>
          rw [ho] at h
          simp only at h
          obtain ⟨-, o', ho', hon'⟩ := ht.obj_of_handle hh hb
          rw [ho, Option.some.injEq] at ho'
          subst ho'
          refine ⟨b, o, ho, h, by rw [hon', hq n hd hqn hh], ?_⟩
          unfold HMem.ptrRef
          simp only [hqn, Option.bind_some, hh, hb, ho, h, ↓reduceIte]

/-- The record rule for a pointer that holds no canonical object: the slow
path's reference. -/
theorem HMem.ptrRef_not_canonical {m : HMem V} (S0 : Stream V T) {z : NodeId} {q : HPtr}
    (h : m.holdsCanonical q = false) : m.ptrRef S0 z q = m.slowRef S0 z q := by
  apply HMem.ptrRef_eq_slowRef
  intro hd b ob hph hb hob
  unfold HMem.holdsCanonical at h
  cases hqn : q.handle with
  | none => rw [hqn] at hph; cases hph
  | some n =>
    rw [hqn] at hph h
    simp only [Option.bind_some] at hph h
    unfold HMem.objOf at h
    rw [hph] at h
    simp only [Option.bind_some, hb, hob] at h
    exact h

theorem HMem.slowRef_congr {m m' : HMem V} (S0 : Stream V T) (hs : m'.s = m.s)
    (hh : ∀ n, m'.handle? n = m.handle? n) (z : NodeId) (q : HPtr) :
    m'.slowRef S0 z q = m.slowRef S0 z q := by
  have hhf : m'.handle? = m.handle? := funext hh
  unfold HMem.slowRef
  rw [hs, hhf]

theorem HMem.slowRef_ruleR (S0 : Stream V T) (m : HMem V) (z : NodeId) (q : HPtr) :
    m.slowRef S0 z { q with ref := ruleRRef S0 m.s z q.ref } = m.slowRef S0 z q := by
  unfold HMem.slowRef
  simp only [ruleRRef_idem]

/-- The pointer that takes z's live handle, z having a canonical object, holds
a canonical object, and z's live handle. -/
theorem HMem.holdsCanonical_tableOf {m : HMem V} {z : NodeId} (q : HPtr) (h : (m.canonicalOf z).isSome = true) :
    m.holdsCanonical { q with handle := m.tableOf z } = true := by
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp h
  obtain ⟨n, o, htn, hob, ho, hc⟩ := (m.canonicalOf_eq_some z b).mp hb
  unfold HMem.holdsCanonical
  simp only [htn, Option.bind_some, hob, ho, hc]

theorem HMem.holdsLive_tableOf {m : HMem V} {z : NodeId} (q : HPtr) (h : (m.canonicalOf z).isSome = true) :
    m.HoldsLive z { q with handle := m.tableOf z } := by
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp h
  obtain ⟨n, o, htn, -, -, -⟩ := (m.canonicalOf_eq_some z b).mp hb
  exact ⟨n, by simp [htn], htn, h⟩

theorem HMem.resolveP_keep (S0 : Stream V T) (m : HMem V) (D : Dirty) (z : NodeId) {q : HPtr}
    (h : m.holdsCanonical q = true) : m.resolveP S0 D z q = q := by
  unfold HMem.resolveP; simp [h]

/-- `resolvePointers` gives a pinned pointee's pointer its live handle. -/
theorem HMem.resolveP_pinned (S0 : Stream V T) {m : HMem V} (ht : HTableOK m) {D : Dirty} {z : NodeId}
    {q : HPtr} (hq : ∀ n hd, q.handle = some n → m.handle? n = some hd → hd.node = z)
    (hD : inD D z = true) (hc : (m.canonicalOf z).isSome = true) : m.HoldsLive z (m.resolveP S0 D z q) := by
  rcases HMem.resolveP_cases S0 m D z q with ⟨h1, h2⟩ | ⟨-, -, -, h2⟩ | ⟨-, h3, -⟩
  · rw [h2]; exact HMem.holdsLive_of_holdsCanonical ht hq h1
  · rw [h2]; exact HMem.holdsLive_tableOf q hc
  · exact absurd ⟨hD, hc⟩ h3

/-! ## The invariant after the record -/

section Final

variable {sp : Spec V T} {al : Algo V T} {db : DB V T} {tr : T} {S0 : Stream V T} {k : Nat}

/-- After the two loops, the memory with handles has the invariant of the state
after the transaction. -/
theorem HAInv.final_ok (hsp : SpecOK sp) (hinv : Inv sp db k) (hmk : al.mark = true)
    (hstep : StepOK sp db.P (k + 1) (parts sp al db tr).c) (hinv' : Inv sp (step sp al db tr) (k + 1))
    (hev' : EvLogic sp (step sp al db tr) (k + 1)) {m3 m6 : HMem V}
    (ha : HAInv sp db S0 k (parts sp al db tr).c (pathOf sp db.P (parts sp al db tr).c (k + 1)) m3)
    (hfr : LoopsFrameH S0 db.D (parts sp al db tr).D1 (dataIds sp al db tr) (parts sp al db tr).taken (k + 1)
      m3 m6)
    (hpos6 : HPosOK db.S (parts sp al db tr).vs m6) :
    HEInv sp (step sp al db tr) S0 (k + 1) m6 := by
  have hP : (parts sp al db tr).P = db.P.apply (k + 1) (parts sp al db tr).c := parts_P' sp al db tr hinv.len
  have hP' : (step sp al db tr).P = (parts sp al db tr).P := rfl
  have hS' : (step sp al db tr).S = Snew sp al db tr := rfl
  have hD' : (step sp al db tr).D = (parts sp al db tr).r7.1 := rfl
  have hSn : Snew sp al db tr = db.S ++ [(parts sp al db tr).R] := rfl
  have hpre : db.S <+: (step sp al db tr).S := List.prefix_append _ _
  -- Objects of m6 come from m3.
  have hback : ∀ a o6, m6.obj? a = some o6 → ∃ o3, m3.obj? a = some o3 := by
    intro a o6 ho6
    cases ho3 : m3.obj? a with
    | none => rw [hfr.none a ho3] at ho6; cases ho6
    | some o3 => exact ⟨o3, rfl⟩
  have hobj : ∀ a o6, m6.obj? a = some o6 → ∃ o3, m3.obj? a = some o3 ∧ o6.node = o3.node ∧
      o6.level = o3.level ∧ o6.isData = o3.isData ∧ o6.hist = o3.hist ∧ o6.canonical = o3.canonical ∧
      (∀ z, o6.ptr? z = o3.ptr? z ∨ o6.ptr? z = (o3.ptr? z).map (m3.resolveP S0 db.D z) ∨
        o6.ptr? z = (o3.ptr? z).map (m3.resolveP S0 (parts sp al db tr).D1 z)) ∧
      ((o3.node ∈ (parts sp al db tr).taken ∧ m3.canonicalOf o3.node = some a) →
        ∀ z, o6.ptr? z = (o3.ptr? z).map (m3.resolveP S0 (parts sp al db tr).D1 z)) ∧
      (¬ ((o3.node ∈ dataIds sp al db tr ∨ o3.node ∈ (parts sp al db tr).taken) ∧
        m3.canonicalOf o3.node = some a) → o6.pos = o3.pos ∧ ∀ z, o6.ptr? z = o3.ptr? z) := by
    intro a o6 ho6
    obtain ⟨o3, ho3⟩ := hback a o6 ho6
    obtain ⟨o6', ho6', rest⟩ := hfr.obj a o3 ho3
    rw [ho6, Option.some.injEq] at ho6'
    subst ho6'
    exact ⟨o3, ho3, rest⟩
  have hcan6 := hfr.canon
  have htab6 : ∀ y, m6.tableOf y = m3.tableOf y := by intro y; unfold HMem.tableOf; rw [hfr.table]
  have hh6 : ∀ n, m6.handle? n = m3.handle? n := by intro n; unfold HMem.handle?; rw [hfr.handles]
  -- D after the transaction.
  have hD1D : ∀ y, inD db.D y = true → inD (parts sp al db tr).D1 y = true := by
    intro y hy
    obtain ⟨d, hd⟩ := (inD_iff _ _).mp hy
    exact (inD_iff _ _).mpr ⟨d, (step_D1_mem sp al db tr hinv.len _).mpr (Or.inl hd)⟩
  have hD'D1 : ∀ y, inD (parts sp al db tr).r7.1 y = true → inD (parts sp al db tr).D1 y = true :=
    fun y hy => step_r7_D1 sp al db tr hinv hy
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
  have hD1rel : ∀ y, inD (parts sp al db tr).D1 y = true →
      reachable sp (db.P.apply (k + 1) (parts sp al db tr).c) (k + 1) y = true ∨ inD db.D y = true ∨
        reachable sp db.P k y = true := by
    intro y hy
    rcases step_D1_cases sp al db tr hmk hinv hy with h | h | h
    · exact Or.inr (Or.inl h)
    · left; rw [hP] at h; unfold marked at h; simp only [Bool.and_eq_true] at h; exact h.1
    · right; right; have := hstep.touchReach y h; simpa using this
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
  have hD2 : ∀ z, inD (parts sp al db tr).D1 z = true → z ∉ (parts sp al db tr).taken →
      inD (parts sp al db tr).r7.1 z = true := by
    intro z hz hzt
    obtain ⟨d, hd⟩ := (inD_iff _ _).mp hz
    have h2 := step_D2_of_not_taken sp al db tr hd hzt
    obtain ⟨d2, hd2⟩ := (inD_iff _ _).mp h2
    rw [(step_r7_shape sp al db tr hinv.len).1]
    exact (inD_iff _ _).mpr ⟨d2, List.mem_append_left _ hd2⟩
  -- The positions: the latest versions of the new stream.
  have hpos : ∀ a o, m6.obj? a = some o → o.canonical = true →
      o.pos = ((step sp al db tr).S.lv o.node).map (·.recNo) := by
    intro a o ho hc
    rw [hpos6 a o ho hc, lv_building_Snew]
    rfl
  -- The record rule after the record, for a pointer that holds a canonical object.
  have hpr6c : ∀ z q, (∀ n hd, q.handle = some n → m6.handle? n = some hd → hd.node = z) →
      m6.holdsCanonical q = true → m6.ptrRef S0 z q = ((step sp al db tr).S.lv z).map (·.recNo) := by
    intro z q hq hc
    obtain ⟨b, o, ho, hco, hon, hpr⟩ := HMem.ptrRef_of_holdsCanonical S0 hfr.tbl hq hc
    rw [hpr, hpos b o ho hco, hon]
  -- And for a pointer that holds none: the record of the pointer it comes from.
  have hq6 : ∀ z q3 q6, (q6 = q3 ∨ q6 = m3.resolveP S0 db.D z q3 ∨
      q6 = m3.resolveP S0 (parts sp al db tr).D1 z q3) →
      m6.holdsCanonical q6 = false → m3.holdsCanonical q3 = false ∧ m6.ptrRef S0 z q6 = m3.ptrRef S0 z q3 := by
    intro z q3 q6 hq hc6
    have hc6' : m3.holdsCanonical q6 = false := by rw [← hfr.hc]; exact hc6
    have hres : ∀ D, q6 = m3.resolveP S0 D z q3 →
        m3.holdsCanonical q3 = false ∧ m3.slowRef S0 z q6 = m3.slowRef S0 z q3 := by
      intro D hqD
      rcases HMem.resolveP_cases S0 m3 D z q3 with ⟨h1, h2⟩ | ⟨-, -, h3, h2⟩ | ⟨h1, -, h2⟩
      · rw [hqD, h2, h1] at hc6'; cases hc6'
      · rw [hqD, h2, HMem.holdsCanonical_tableOf q3 h3] at hc6'; cases hc6'
      · exact ⟨h1, by rw [hqD, h2, HMem.slowRef_ruleR]⟩
    have hbase : m3.holdsCanonical q3 = false ∧ m3.slowRef S0 z q6 = m3.slowRef S0 z q3 := by
      rcases hq with hq | hq | hq
      · subst hq; exact ⟨hc6', rfl⟩
      · exact hres _ hq
      · exact hres _ hq
    refine ⟨hbase.1, ?_⟩
    rw [HMem.ptrRef_not_canonical S0 hc6, HMem.slowRef_congr S0 hfr.s hh6, hbase.2,
      ← HMem.ptrRef_not_canonical S0 hbase.1]
  -- That a pointer holds a node's live handle: the same after the record.
  have hhl6 : ∀ z q, m3.HoldsLive z q → m6.HoldsLive z q := by
    intro z q ⟨n, h1, h2, h3⟩
    exact ⟨n, h1, by rw [htab6]; exact h2, by rw [hcan6]; exact h3⟩
  -- The pointer of an object of m6 for z, from that of its object of m3.
  have hptr6 : ∀ a o6 o3 z q3, m6.obj? a = some o6 → m3.obj? a = some o3 →
      (∀ z, o6.ptr? z = o3.ptr? z ∨ o6.ptr? z = (o3.ptr? z).map (m3.resolveP S0 db.D z) ∨
        o6.ptr? z = (o3.ptr? z).map (m3.resolveP S0 (parts sp al db tr).D1 z)) →
      o3.ptr? z = some q3 →
      ∃ q6, o6.ptr? z = some q6 ∧ (q6 = q3 ∨ q6 = m3.resolveP S0 db.D z q3 ∨
        q6 = m3.resolveP S0 (parts sp al db tr).D1 z q3) ∧
        (∀ n hd, q6.handle = some n → m6.handle? n = some hd → hd.node = z) ∧
        (∀ n hd, q3.handle = some n → m3.handle? n = some hd → hd.node = z) ∧
        (m3.HoldsLive z q3 → m6.HoldsLive z q6) := by
    intro a o6 o3 z q3 ho6 ho3 hpt hq3
    obtain ⟨q6, hq6', hcase⟩ : ∃ q6, o6.ptr? z = some q6 ∧ (q6 = q3 ∨ q6 = m3.resolveP S0 db.D z q3 ∨
        q6 = m3.resolveP S0 (parts sp al db tr).D1 z q3) := by
      rcases hpt z with h | h | h
      · exact ⟨q3, by rw [h, hq3], Or.inl rfl⟩
      · exact ⟨_, by rw [h, hq3]; rfl, Or.inr (Or.inl rfl)⟩
      · exact ⟨_, by rw [h, hq3]; rfl, Or.inr (Or.inr rfl)⟩
    have hqn6 : ∀ n hd, q6.handle = some n → m6.handle? n = some hd → hd.node = z := by
      intro n hd h1 h2
      obtain ⟨hd', h3, h4⟩ := hfr.tbl.ptrNode ho6 hq6' h1
      rw [h2, Option.some.injEq] at h3; subst h3; exact h4
    have hqn3 : ∀ n hd, q3.handle = some n → m3.handle? n = some hd → hd.node = z := by
      intro n hd h1 h2
      obtain ⟨hd', h3, h4⟩ := ha.tbl.ptrNode ho3 hq3 h1
      rw [h2, Option.some.injEq] at h3; subst h3; exact h4
    refine ⟨q6, hq6', hcase, hqn6, hqn3, fun hhl => ?_⟩
    have hq : q6 = q3 := by
      have hc := HMem.holdsCanonical_of_holdsLive hhl
      rcases hcase with h | h | h
      · exact h
      · rw [h]; exact HMem.resolveP_keep S0 m3 _ z hc
      · rw [h]; exact HMem.resolveP_keep S0 m3 _ z hc
    rw [hq]; exact hhl6 z q3 hhl
  refine
    { len := hinv'.len
      pre := ha.pre.trans hpre
      sEq := by rw [hfr.s]; exact ha.sEq
      freshO := ?_
      freshH := fun n hn => by
        rw [hh6]; exact ha.freshH n (by rw [← hfr.nextHandle]; exact hn)
      objNodup := hfr.nodup ha.objNodup
      hNodup := by rw [hfr.handles]; exact ha.hNodup
      root := ?_
      tbl := hfr.tbl
      liveW := fun n hd hh hl => ha.liveW n hd (by rw [← hh6]; exact hh) hl
      cc := ?_
      pos := hpos
      dCanon := fun y hy => by rw [hcan6]; exact ha.canon_D1 hsp hinv hmk hstep (hD'D1 y hy)
      snap := ?_
      ruleR := ?_
      wver := ?_
      rver := ?_
      slots := ?_
      live := ?_ }
  · -- fresh
    intro a ha'
    cases ho : m6.obj? a with
    | none => rfl
    | some o6 =>
      obtain ⟨o3, ho3⟩ := hback a o6 ho
      rw [ha.freshO a (by rw [← hfr.nextObj]; exact ha')] at ho3; cases ho3
  · -- root
    obtain ⟨o, ho, hc, hn⟩ := ha.root
    obtain ⟨o6, ho6, e1, -, -, -, e5, -⟩ := hfr.obj _ o ho
    exact ⟨o6, by rw [hfr.root]; exact ho6, by rw [e5, hc], by rw [e1, hn]⟩
  · -- cc
    intro a o6 ho6 hc6
    obtain ⟨o3, ho3, e1, e2, e3, e4, e5, -⟩ := hobj a o6 ho6
    obtain ⟨n, hn, h1, h2, h3⟩ := ha.cc a o3 ho3 (by rw [← e5]; exact hc6)
    exact ⟨n, by rw [hP', hP, e1]; exact hn, by rw [e4, h1], by rw [e2, h2], by rw [e3, h3]⟩
  · -- snap
    intro a o6 ho6 hc6
    obtain ⟨o3, ho3, e1, e2, e3, e4, e5, -, -, hp⟩ := hobj a o6 ho6
    have hc3 : o3.canonical = false := by rw [← e5]; exact hc6
    obtain ⟨r, w, s1, s2, s3, s4, s5, s6, s7⟩ := ha.snap a o3 ho3 hc3
    -- a snapshot is not written: same position and pointers
    have hnc : ¬ ((o3.node ∈ dataIds sp al db tr ∨ o3.node ∈ (parts sp al db tr).taken) ∧
        m3.canonicalOf o3.node = some a) := by
      rintro ⟨-, hc⟩
      obtain ⟨o', ho', -, hco⟩ := ha.tbl.canonicalOf_node hc
      rw [ho3, Option.some.injEq] at ho'; subst ho'
      rw [hc3] at hco; cases hco
    have hptrs : ∀ z, o6.ptr? z = o3.ptr? z := (hp hnc).2
    refine ⟨r, w, by rw [(hp hnc).1]; exact s1, ?_, by rw [e4]; exact s3, by rw [e2]; exact s4,
      by rw [e3]; exact s5, fun z hz => by rw [hptrs z]; exact s6 z (by rw [← e4]; exact hz),
      fun z q hq => ?_⟩
    · rw [e1]; exact versionAt_prefix hpre s2
    · rw [hptrs z] at hq
      have h7 := s7 z q hq
      intro r0 h0
      rw [hfr.s] at h0 ⊢
      exact h7 r0 h0
  · -- the snapshots against Rule R
    intro n hd b o6 w hh hb ho6 hc6 hw
    rw [hh6] at hh
    rw [hfr.s] at hw
    obtain ⟨o3, ho3, -, -, -, -, e5, -, -, hp⟩ := hobj b o6 ho6
    have hc3 : o3.canonical = false := by rw [← e5]; exact hc6
    have hnc : ¬ ((o3.node ∈ dataIds sp al db tr ∨ o3.node ∈ (parts sp al db tr).taken) ∧
        m3.canonicalOf o3.node = some b) := by
      rintro ⟨-, hc⟩
      obtain ⟨o', ho', -, hco⟩ := ha.tbl.canonicalOf_node hc
      rw [ho3, Option.some.injEq] at ho'; subst ho'
      rw [hc3] at hco; cases hco
    rw [(hp hnc).1]
    exact ha.ruleR n hd b o3 w hh hb ho3 hc3 hw
  · -- written positions name versions
    intro n hd w hh hw
    rw [hh6] at hh
    obtain ⟨u, hu⟩ := ha.wver n hd w hh hw
    exact ⟨u, versionAt_prefix hpre hu⟩
  · -- references name versions
    intro a o6 z q6 r ho6 hq6 hr
    obtain ⟨o3, ho3, -, -, -, -, -, hpt, -, -⟩ := hobj a o6 ho6
    have hres_ver : ∀ D q3, o3.ptr? z = some q3 → (m3.resolveP S0 D z q3).ref = some r →
        ∃ u, db.S.versionAt r z = some u := by
      intro D q3 hq3 hr3
      rcases HMem.resolveP_cases S0 m3 D z q3 with ⟨-, h2⟩ | ⟨-, -, -, h2⟩ | ⟨-, -, h2⟩
      · rw [h2] at hr3; exact ha.rver a o3 z q3 r ho3 hq3 hr3
      · rw [h2] at hr3; exact ha.rver a o3 z q3 r ho3 hq3 hr3
      · rw [h2] at hr3
        exact (hinv.ruleR_bound ha.pre m3.s (fun r' h' => ha.rver a o3 z q3 r' ho3 hq3 h') hr3).1
    have hver : ∃ u, db.S.versionAt r z = some u := by
      rcases hpt z with h | h | h
      · rw [h] at hq6; exact ha.rver a o3 z q6 r ho3 hq6 hr
      · rw [h] at hq6
        cases hq3 : o3.ptr? z with
        | none => rw [hq3] at hq6; cases hq6
        | some q3 =>
          rw [hq3] at hq6
          simp only [Option.map_some, Option.some.injEq] at hq6
          subst hq6
          exact hres_ver _ q3 hq3 hr
      · rw [h] at hq6
        cases hq3 : o3.ptr? z with
        | none => rw [hq3] at hq6; cases hq6
        | some q3 =>
          rw [hq3] at hq6
          simp only [Option.map_some, Option.some.injEq] at hq6
          subst hq6
          exact hres_ver _ q3 hq3 hr
    obtain ⟨u, hu⟩ := hver
    exact ⟨u, versionAt_prefix hpre hu⟩
  · -- slots
    intro a o6 ho6 hrel z hz
    obtain ⟨o3, ho3, e1, e2, e3, e4, e5, hpt, hpin, hun⟩ := hobj a o6 ho6
    obtain ⟨hc6, hw6, hr6⟩ := hrel
    have hc3 : o3.canonical = true := by rw [← e5]; exact hc6
    have hcx : m3.canonicalOf o3.node = some a := ha.tbl.canonicalOf_of ho3 hc3
    have hrel3 : reachable sp (db.P.apply (k + 1) (parts sp al db tr).c) (k + 1) o3.node = true ∨
        inD db.D o3.node = true ∨ reachable sp db.P k o3.node = true := by
      rcases hr6 with hr | hd
      · left; rw [← hP, ← hP', ← e1]; exact hr
      · rw [e1] at hd; exact hD1rel _ (hD'D1 _ hd)
    obtain ⟨q3, hq3, hA1, hA2⟩ := ha.slots a o3 ho3 hc3 (by rw [← e1]; exact hw6) hrel3 z
      (by rw [← e4]; exact hz)
    obtain ⟨q6, hq6', hcase, hqn6, hqn3, hheld⟩ := hptr6 a o6 o3 z q3 ho6 ho3 hpt hq3
    -- When o's node is taken, its pointers to D1 nodes with canonical objects hold their live
    -- handles.
    have hpinned : o3.node ∈ (parts sp al db tr).taken → inD (parts sp al db tr).D1 z = true →
        (m3.canonicalOf z).isSome = true → m6.HoldsLive z q6 := by
      intro hxt hzD1 hcz
      have h := hpin ⟨hxt, hcx⟩ z
      rw [hq3, hq6'] at h
      simp only [Option.map_some, Option.some.injEq] at h
      rw [h]
      exact hhl6 z _ (HMem.resolveP_pinned S0 ha.tbl hqn3 hzD1 hcz)
    have hval6 : m6.HoldsLive z q6 → m6.ptrRef S0 z q6 = ((step sp al db tr).S.lv z).map (·.recNo) :=
      fun h => hpr6c z q6 hqn6 (HMem.holdsCanonical_of_holdsLive h)
    refine ⟨q6, hq6', fun hzD' => ?_, fun hzD' => ?_⟩
    · -- z not in D after: its latest version.
      rw [hD'] at hzD'
      by_cases hzw : z ∈ dataIds sp al db tr ∨ z ∈ (parts sp al db tr).taken
      · -- written in the record: the pointer holds z's live handle
        apply hval6
        rcases hzw with hzd | hzt
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
          exact hheld ((hA1 hzD).2 hzn)
        · obtain ⟨dz, hdz, hdzs⟩ := htakenD z hzt
          have hzD : inD db.D z = true := (inD_iff _ _).mpr ⟨dz, hdz⟩
          rcases hA2 hzD with hhl | ⟨hxD, a', b', ha', hb, hab⟩
          · exact hheld hhl
          · -- o's node got dirty no later than z: taken too, so written with z pinned
            have hb' : b' = dz := by
              rw [dOf_of_mem hinv.dNodup hdz, Option.some.injEq] at hb; exact hb.symm
            have hxt : o3.node ∈ (parts sp al db tr).taken := by
              have hxa := mem_of_dOf ha'
              exact (step_taken_mem sp al db tr _).mpr ⟨a', (step_D1_mem sp al db tr hinv.len _).mpr
                (Or.inl hxa), by omega⟩
            exact hpinned hxt (hD1D z hzD) (ha.canon z (Or.inl hzD))
      · -- not written: not in D1, so the pointer is as before, maybe with its reference raised
        rw [not_or] at hzw
        have hzD1 : inD (parts sp al db tr).D1 z = false := by
          cases hz1 : inD (parts sp al db tr).D1 z with
          | false => rfl
          | true => rw [hD2 z hz1 hzw.2] at hzD'; cases hzD'
        have hzD : inD db.D z = false := by
          cases hzd : inD db.D z with
          | false => rfl
          | true => rw [hD1D z hzd] at hzD1; cases hzD1
        cases hc6q : m6.holdsCanonical q6 with
        | true => exact hpr6c z q6 hqn6 hc6q
        | false =>
          obtain ⟨-, hpr⟩ := hq6 z q3 q6 hcase hc6q
          rw [hpr, (hA1 hzD).1, hS', hnotw z hzw.1 hzw.2]
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
              obtain ⟨n', hn', hh', -, -⟩ := ha.cc a o3 ho3 hc3
              have hn'' : (step sp al db tr).P.get? o6.node = some n' := by rw [hP', hP, e1]; exact hn'
              have := (hev'.clean o6.node n' hw6 hr hn'' hxd z (by rw [← hh', ← e4]; exact hz)).1
              rw [hD'] at this
              rw [this] at hzD'; cases hzD'
          · exact hd
        obtain ⟨a', ha'⟩ := dOf_inD hxD'
        have hxa := mem_of_dOf ha'
        refine ⟨hxD', a', dz, ha', hdz, ?_⟩
        rcases step_D'_entry (al := al) (tr := tr) hinv hxa with h1 | ⟨h1, -⟩
        · omega
        · have := hinv.D_le h1; omega
      · -- z was in D and is not taken
        have hzD : inD db.D z = true := (inD_iff _ _).mpr ⟨dz, hzdb⟩
        rcases hA2 hzD with hhl | ⟨hxD, a', b', ha', hb, hab⟩
        · left; exact hheld hhl
        · have hb' : b' = dz := by
            rw [dOf_of_mem hinv.dNodup hzdb, Option.some.injEq] at hb; exact hb.symm
          subst hb'
          have hxa := mem_of_dOf ha'
          by_cases has : a' ≤ (parts sp al db tr).s
          · -- o's node is taken: its pointer for z holds z's live handle
            left
            have hxt : o3.node ∈ (parts sp al db tr).taken :=
              (step_taken_mem sp al db tr _).mpr ⟨a', (step_D1_mem sp al db tr hinv.len _).mpr (Or.inl hxa),
                has⟩
            exact hpinned hxt (hD1D z hzD) (ha.canon z (Or.inl hzD))
          · -- o's node stays in D, with its index
            right
            have hxD2 : (o3.node, a') ∈ (parts sp al db tr).D2 :=
              (step_D2_mem sp al db tr _).mpr ⟨(step_D1_mem sp al db tr hinv.len _).mpr (Or.inl hxa), by
                simp only; omega⟩
            have hxD' : (o3.node, a') ∈ (parts sp al db tr).r7.1 := by
              rw [(step_r7_shape sp al db tr hinv.len).1]; exact List.mem_append_left _ hxD2
            rw [e1]
            exact ⟨(inD_iff _ _).mpr ⟨a', hxD'⟩, a', b', dOf_of_mem hD'nd hxD', hdz, hab⟩
  · -- live
    intro a o6 ho6 hc6 hr6 z hz
    obtain ⟨o3, ho3, e1, e2, e3, e4, e5, hpt, -, -⟩ := hobj a o6 ho6
    have hc3 : o3.canonical = true := by rw [← e5]; exact hc6
    obtain ⟨q3, hq3, hL1, hL2⟩ := ha.live a o3 ho3 hc3 (by rw [← hP, ← hP', ← e1]; exact hr6) z
      (by rw [← e4]; exact hz)
    obtain ⟨q6, hq6', hcase, hqn6, -, hheld⟩ := hptr6 a o6 o3 z q3 ho6 ho3 hpt hq3
    refine ⟨q6, hq6', fun hzD' => ?_, fun hzD' => ?_⟩
    · rw [hD'] at hzD'
      exact hheld (hL1 (hD1cases z (hD'D1 z hzD')))
    · rw [hD'] at hzD'
      by_cases hzw : z ∈ dataIds sp al db tr ∨ z ∈ (parts sp al db tr).taken
      · have hzc : inD db.D z = true ∨ z ∈ pathOf sp db.P (parts sp al db tr).c (k + 1) ∨
            z ∈ (parts sp al db tr).c.new.map (·.id) := by
          rcases hzw with hzd | hzt
          · exact Or.inr (Or.inr (hdnew z hzd))
          · obtain ⟨dz, hdz, -⟩ := htakenD z hzt
            exact Or.inl ((inD_iff _ _).mpr ⟨dz, hdz⟩)
        exact hpr6c z q6 hqn6 (HMem.holdsCanonical_of_holdsLive (hheld (hL1 hzc)))
      · rw [not_or] at hzw
        have hzD1 : inD (parts sp al db tr).D1 z = false := by
          cases hz1 : inD (parts sp al db tr).D1 z with
          | false => rfl
          | true => rw [hD2 z hz1 hzw.2] at hzD'; cases hzD'
        have hzD : inD db.D z = false := by
          cases hzd : inD db.D z with
          | false => rfl
          | true => rw [hD1D z hzd] at hzD1; cases hzD1
        cases hc6q : m6.holdsCanonical q6 with
        | true => exact hpr6c z q6 hqn6 hc6q
        | false =>
          obtain ⟨-, hpr⟩ := hq6 z q3 q6 hcase hc6q
          rw [hpr, hL2 hzD, hS', hnotw z hzw.1 hzw.2]

end Final

end SIS
