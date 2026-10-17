/-
Proofs for stage 2 (bergdb item 001, WP E3), part 10: the physical writer's two
loops (the new data nodes, then the taken nodes) write the model's record, and
leave the invariant of the next state.
-/
import SIS.Proof.EvictApplyInv

set_option linter.unusedSectionVars false

namespace SIS

variable {V T : Type} [DecidableEq V]

/-! ## What the writer's loop changes -/

/-- The slots of object o after its node is written with the pinned set D, from
memory m: the slots to pinned pointees made memory slots to their canonical
objects. -/
def pinnedSlot (m : Mem V) (D : Dirty) (o : Obj V) (z : NodeId) : Option Slot :=
  (o.slot? z).map (fun sl => if inD D z then
    (match m.canonicalOf z with
     | some h0 => Slot.mem h0
     | none => sl) else sl)

/-- Object o' at handle h is object o after the loop that writes the nodes xs with
the pinned set D, from memory m: the same node, level, kind, history and flag;
record i and pinned slots if o is the canonical object of a node of xs, the
same position and slots otherwise. -/
def WrittenAt (m : Mem V) (D : Dirty) (i : Nat) (xs : List NodeId) (h : Nat) (o o' : Obj V) : Prop :=
  o'.node = o.node ∧ o'.level = o.level ∧ o'.isData = o.isData ∧ o'.hist = o.hist ∧
    o'.canonical = o.canonical ∧
    ((o.node ∈ xs ∧ m.canonicalOf o.node = some h ∧ o'.pos = some i ∧
       ∀ z, o'.slot? z = pinnedSlot m D o z) ∨
     (¬ (o.node ∈ xs ∧ m.canonicalOf o.node = some h) ∧ o'.pos = o.pos ∧ ∀ z, o'.slot? z = o.slot? z))

section Loop

variable (sp : Spec V T) (S0 : Stream V T) (D : Dirty) (i : Nat)

theorem writeNodes_frame : ∀ (xs : List NodeId) (m : Mem V), xs.Nodup → TableNode m →
    (m.writeNodes sp S0 D i xs).1.table = m.table ∧ (m.writeNodes sp S0 D i xs).1.s = m.s ∧
    (m.writeNodes sp S0 D i xs).1.root = m.root ∧ (m.writeNodes sp S0 D i xs).1.next = m.next ∧
    (∀ y, (m.writeNodes sp S0 D i xs).1.canonicalOf y = m.canonicalOf y) ∧
    (∀ h o, m.obj? h = some o → ∃ o', (m.writeNodes sp S0 D i xs).1.obj? h = some o' ∧
      WrittenAt m D i xs h o o') ∧
    (∀ h, m.obj? h = none → (m.writeNodes sp S0 D i xs).1.obj? h = none) ∧
    ((m.objs.map (·.1)).Nodup → ((m.writeNodes sp S0 D i xs).1.objs.map (·.1)).Nodup) := by
  intro xs
  induction xs with
  | nil =>
    intro m _ _
    have h0 : m.writeNodes sp S0 D i [] = (m, []) := rfl
    rw [h0]
    refine ⟨rfl, rfl, rfl, rfl, fun _ => rfl, fun h o ho => ⟨o, ho, rfl, rfl, rfl, rfl, rfl,
      Or.inr ⟨fun h => by simp at h, rfl, fun _ => rfl⟩⟩, fun _ h => h, id⟩
  | cons x xs ih =>
    intro m hnd htn
    simp only [List.nodup_cons] at hnd
    rw [writeNodes_eq_foldl, List.foldl_cons]
    -- One write: x's canonical object, if any.
    have hone : ∃ m1 : Mem V, (wnStep sp S0 D i (m, []) x).1 = m1 ∧
        (xs.foldl (wnStep sp S0 D i) (wnStep sp S0 D i (m, []) x)).1 = (m1.writeNodes sp S0 D i xs).1 ∧
        m1.table = m.table ∧ m1.s = m.s ∧ m1.root = m.root ∧ m1.next = m.next ∧
        (∀ y, m1.canonicalOf y = m.canonicalOf y) ∧
        (∀ h o, m.obj? h = some o → ∃ o1, m1.obj? h = some o1 ∧ WrittenAt m D i [x] h o o1) ∧
        (∀ h, m.obj? h = none → m1.obj? h = none) ∧
        ((m.objs.map (·.1)).Nodup → (m1.objs.map (·.1)).Nodup) := by
      cases hc : m.canonicalOf x with
      | none =>
        have hw : m.writeNode sp S0 D i x = (m, none) := by unfold Mem.writeNode; rw [hc]
        refine ⟨m, by rw [wnStep_none sp S0 D i hw], ?_, rfl, rfl, rfl, rfl, fun _ => rfl,
          fun h o ho => ⟨o, ho, rfl, rfl, rfl, rfl, rfl, Or.inr ⟨fun ⟨h1, h2⟩ => ?_, rfl, fun _ => rfl⟩⟩,
          fun _ h => h, id⟩
        · rw [wnStep_none sp S0 D i hw, foldl_wnStep_prefix, writeNodes_eq_foldl]
        · simp only [List.mem_singleton] at h1
          rw [h1, hc] at h2; cases h2
      | some h =>
        cases ho : m.obj? h with
        | none =>
          have hw : m.writeNode sp S0 D i x = (m, none) := by unfold Mem.writeNode; rw [hc]; simp [ho]
          refine ⟨m, by rw [wnStep_none sp S0 D i hw], ?_, rfl, rfl, rfl, rfl, fun _ => rfl,
            fun h' o ho' => ⟨o, ho', rfl, rfl, rfl, rfl, rfl, Or.inr ⟨fun ⟨h1, h2⟩ => ?_, rfl, fun _ => rfl⟩⟩,
            fun _ h => h, id⟩
          · rw [wnStep_none sp S0 D i hw, foldl_wnStep_prefix, writeNodes_eq_foldl]
          · simp only [List.mem_singleton] at h1
            rw [h1, hc, Option.some.injEq] at h2
            subst h2
            rw [ho] at ho'; cases ho'
        | some o =>
          have hw := writeNode_shape sp S0 D i hc ho
          have hnode : o.node = x := by
            obtain ⟨ht, -⟩ := (m.canonicalOf_eq_some x h).mp hc
            obtain ⟨o2, ho2, hn2⟩ := htn x h ht
            rw [ho] at ho2; cases ho2; exact hn2
          refine ⟨m.setObj h { o with pos := some i, slots := m.pinSlots D o }, by
            rw [wnStep_some sp S0 D i hw], by
            rw [wnStep_some sp S0 D i hw, foldl_wnStep_prefix, writeNodes_eq_foldl], rfl, rfl, rfl, rfl,
            canonicalOf_setObj_same ho rfl, fun h' o' ho' => ?_, fun h' hn => ?_,
            fun hnd' => nodup_setObj_keys m h _ hnd'⟩
          · rw [Mem.obj?_setObj]
            split
            · rename_i he; subst he
              rw [ho, Option.some.injEq] at ho'; subst ho'
              refine ⟨_, rfl, rfl, rfl, rfl, rfl, rfl,
                Or.inl ⟨by simp [hnode], by rw [hnode]; exact hc, rfl, fun z => ?_⟩⟩
              exact slot?_of_pinSlots m D o rfl z
            · rename_i hne
              refine ⟨o', ho', rfl, rfl, rfl, rfl, rfl, Or.inr ⟨fun ⟨h1, h2⟩ => ?_, rfl, fun _ => rfl⟩⟩
              simp only [List.mem_singleton] at h1
              rw [h1, hc, Option.some.injEq] at h2
              exact hne h2.symm
          · rw [Mem.obj?_setObj]
            split
            · rename_i he; subst he; rw [ho] at hn; cases hn
            · exact hn
    obtain ⟨m1, hm1, hfold, ht1, hs1, hr1, hn1, hc1, hobj1, hnone1, hnd1⟩ := hone
    rw [hfold]
    have htn1 : TableNode m1 := by
      intro y h ht
      rw [show m1.tableOf y = m.tableOf y by unfold Mem.tableOf; rw [ht1]] at ht
      obtain ⟨o, ho, hno⟩ := htn y h ht
      obtain ⟨o1, ho1, e1, -⟩ := hobj1 h o ho
      exact ⟨o1, ho1, by rw [e1, hno]⟩
    obtain ⟨t1, t2, t3, t4, t5, t6, t7, t8⟩ := ih m1 hnd.2 htn1
    refine ⟨by rw [t1, ht1], by rw [t2, hs1], by rw [t3, hr1], by rw [t4, hn1],
      fun y => by rw [t5, hc1], fun h o ho => ?_, fun h hn => t7 h (hnone1 h hn), fun hnd' => t8 (hnd1 hnd')⟩
    obtain ⟨o1, ho1, a1, a2, a3, a4, a5, a6⟩ := hobj1 h o ho
    obtain ⟨o', ho', b1, b2, b3, b4, b5, b6⟩ := t6 h o1 ho1
    refine ⟨o', ho', by rw [b1, a1], by rw [b2, a2], by rw [b3, a3], by rw [b4, a4], by rw [b5, a5], ?_⟩
    have hpin : ∀ (D' : Dirty) z, pinnedSlot m1 D' o1 z = pinnedSlot m D' o1 z := by
      intro D' z; unfold pinnedSlot; simp only [hc1]
    rcases a6 with ⟨x1, c1, p1, s1⟩ | ⟨n1, p1, s1⟩ <;> rcases b6 with ⟨x2, c2, p2, s2⟩ | ⟨n2, p2, s2⟩
    · exfalso
      simp only [List.mem_singleton] at x1
      rw [a1, x1] at x2
      exact hnd.1 x2
    · -- written now, not again
      refine Or.inl ⟨by simp only [List.mem_singleton] at x1; rw [x1]; exact List.mem_cons_self, c1,
        by rw [p2, p1], fun z => by rw [s2 z, s1 z]⟩
    · -- written later
      refine Or.inl ⟨by rw [← a1]; exact List.mem_cons_of_mem _ x2, by rw [← a1, ← hc1]; exact c2, p2,
        fun z => ?_⟩
      rw [s2 z, hpin]
      unfold pinnedSlot
      rw [s1 z]
    · refine Or.inr ⟨fun ⟨h1, h2⟩ => ?_, by rw [p2, p1], fun z => by rw [s2 z, s1 z]⟩
      rcases List.mem_cons.mp h1 with h1 | h1
      · exact n1 ⟨by rw [h1]; exact List.mem_singleton_self _, h2⟩
      · exact n2 ⟨by rw [a1]; exact h1, by rw [a1, hc1]; exact h2⟩

end Loop

/-! ## The two loops of a transaction -/

section Writes

variable {sp : Spec V T} {al : Algo V T} {db : DB V T} {tr : T} {S0 : Stream V T} {k : Nat}

/-- The nodes taken are in D. -/
theorem step_taken_inD {k : Nat} (hinv : Inv sp db k) {x : NodeId}
    (hx : x ∈ (parts sp al db tr).taken) : ∃ d, (x, d) ∈ db.D ∧ d ≤ (parts sp al db tr).s := by
  obtain ⟨d, hd, hds⟩ := (step_taken_mem sp al db tr x).mp hx
  rcases (step_D1_mem sp al db tr hinv.len _).mp hd with h | ⟨h, -⟩
  · exact ⟨d, h, hds⟩
  · exfalso; simp only at h; have := step_s_le sp al db tr hinv.len; omega

/-- The nodes of D1 have canonical objects after the change: they are in D, or
marked (on the writer's paths, or new). -/
theorem AInv.canon_D1 (hsp : SpecOK sp) (hinv : Inv sp db k) (hmk : al.mark = true)
    (hstep : StepOK sp db.P (k + 1) (parts sp al db tr).c) {m3 : Mem V}
    (ha : AInv sp db S0 k (parts sp al db tr).c (pathOf sp db.P (parts sp al db tr).c (k + 1)) m3)
    {y : NodeId} (hy : inD (parts sp al db tr).D1 y = true) : (m3.canonicalOf y).isSome := by
  rcases step_D1_cases sp al db tr hmk hinv hy with h | h | h
  · exact ha.canon y (Or.inl h)
  · by_cases hn : y ∈ (parts sp al db tr).c.new.map (·.id)
    · exact ha.canon y (Or.inr (Or.inr hn))
    · have hP : (parts sp al db tr).P = db.P.apply (k + 1) (parts sp al db tr).c :=
        parts_P' sp al db tr hinv.len
      rw [hP] at h
      exact ha.canon y (Or.inr (Or.inl (step_marked_path sp al db tr hsp hinv hstep h hn)))
  · exact ha.canon y (Or.inr (Or.inl (step_touched_path sp al db tr hstep h)))

/-- The two loops write the model's versions of the record. -/
theorem AInv.loops_vs (hsp : SpecOK sp) (hinv : Inv sp db k) (hmk : al.mark = true)
    (hstep : StepOK sp db.P (k + 1) (parts sp al db tr).c) (hinv' : Inv sp (step sp al db tr) (k + 1))
    {m3 : Mem V}
    (ha : AInv sp db S0 k (parts sp al db tr).c (pathOf sp db.P (parts sp al db tr).c (k + 1)) m3) :
    (m3.writeNodes sp S0 db.D (k + 1) (dataIds sp al db tr)).2 = (parts sp al db tr).vs0 ∧
    PosOK db.S (parts sp al db tr).vs0 (m3.writeNodes sp S0 db.D (k + 1) (dataIds sp al db tr)).1 ∧
    (m3.writeNodes sp S0 db.D (k + 1) (dataIds sp al db tr)).2 ++
      ((m3.writeNodes sp S0 db.D (k + 1) (dataIds sp al db tr)).1.writeNodes sp S0 (parts sp al db tr).D1
        (k + 1) (parts sp al db tr).taken).2 = (parts sp al db tr).vs ∧
    PosOK db.S (parts sp al db tr).vs ((m3.writeNodes sp S0 db.D (k + 1) (dataIds sp al db tr)).1.writeNodes
        sp S0 (parts sp al db tr).D1 (k + 1) (parts sp al db tr).taken).1 := by
  have hP : (parts sp al db tr).P = db.P.apply (k + 1) (parts sp al db tr).c := parts_P' sp al db tr hinv.len
  have hvs0 : (parts sp al db tr).vs0 = writeAll sp db.S (k + 1) (parts sp al db tr).P (dataIds sp al db tr) [] := by
    rw [parts_vs0, hinv.len]; rfl
  have hvs : (parts sp al db tr).vs = writeAll sp db.S (k + 1) (parts sp al db tr).P (parts sp al db tr).taken
      (parts sp al db tr).vs0 := by rw [parts_vs, hinv.len]
  -- The nodes the record writes.
  let wr := dataIds sp al db tr ++ (parts sp al db tr).taken
  have hdnd : (dataIds sp al db tr).Nodup := (List.Sublist.map _ List.filter_sublist).nodup hstep.distinct
  have hdnew : ∀ x ∈ dataIds sp al db tr, x ∈ (parts sp al db tr).c.new.map (·.id) := by
    intro x hx
    simp only [dataIds, List.mem_map, List.mem_filter] at hx
    obtain ⟨nn, ⟨hnn, -⟩, rfl⟩ := hx
    exact List.mem_map.mpr ⟨nn, hnn, rfl⟩
  -- The new data nodes: canonical objects with their whole history, no pointees.
  have hok1 : ∀ x ∈ dataIds sp al db tr, WriteOK sp S0 db.S (parts sp al db tr).P db.D wr m3 x := by
    intro x hx
    obtain ⟨h, hc⟩ := Option.isSome_iff_exists.mp (ha.canon x (Or.inr (Or.inr (hdnew x hx))))
    obtain ⟨ht, o, ho, hco⟩ := (m3.canonicalOf_eq_some x h).mp hc
    obtain ⟨o2, ho2, hn2⟩ := ha.tbl x h ht
    rw [ho, Option.some.injEq] at ho2; subst ho2
    obtain ⟨n, hn, hh, hl, hd⟩ := ha.cc h o ho hco
    rw [hn2, ← hP] at hn
    obtain ⟨-, n', hn', hdat⟩ := step_dataIds_spec sp al db tr hinv hstep hx
    rw [hn, Option.some.injEq] at hn'; subst hn'
    refine ⟨h, o, n, hc, ho, hn, hn2, hh, hl, hd, fun y hy => ?_⟩
    exfalso
    rw [mem_pointees] at hy
    obtain ⟨e, he, hye⟩ := hy
    have := hinv'.data x n (by rw [step_P]; exact hn) hdat e he
    rw [this] at hye; cases hye
  obtain ⟨e1, e2, e3, e4, e5, e6⟩ := writeNodes_eq sp S0 db.S (parts sp al db tr).P db.D (k + 1)
    (dataIds sp al db tr) [] m3 wr ha.tbl ha.slotsNode (fun y hy => ha.canon y (Or.inl hy)) ha.pos hok1
    (fun v hv => by cases hv) (fun x hx => List.mem_append_left _ hx) hdnd (fun x _ v hv => by cases hv)
  rw [List.nil_append] at e1
  rw [← hvs0] at e1 e2
  -- The frame of the data loop: the old objects keep their slots and positions.
  obtain ⟨-, -, -, -, -, f6, -, -⟩ := writeNodes_frame sp S0 db.D (k + 1) (dataIds sp al db tr) m3 hdnd ha.tbl
  generalize hw2 : m3.writeNodes sp S0 db.D (k + 1) (dataIds sp al db tr) = w2 at e1 e2 e3 e4 e5 e6 f6
  -- The taken nodes.
  have htnd := step_taken_nodup sp al db tr hinv
  have hok2 : ∀ x ∈ (parts sp al db tr).taken,
      WriteOK sp S0 db.S (parts sp al db tr).P (parts sp al db tr).D1 wr w2.1 x := by
    intro x hx
    obtain ⟨d, hxd, -⟩ := step_taken_inD (al := al) (tr := tr) hinv hx
    have hxD : inD db.D x = true := (inD_iff _ _).mpr ⟨d, hxd⟩
    obtain ⟨h, hc⟩ := Option.isSome_iff_exists.mp (ha.canon x (Or.inl hxD))
    obtain ⟨ht, o, ho, hco⟩ := (m3.canonicalOf_eq_some x h).mp hc
    obtain ⟨o2, ho2, hn2⟩ := ha.tbl x h ht
    rw [ho, Option.some.injEq] at ho2; subst ho2
    obtain ⟨n, hn, hh, hl, hd⟩ := ha.cc h o ho hco
    rw [hn2, ← hP] at hn
    -- x's object is not a data node's: unchanged by the data loop.
    obtain ⟨o', ho', a1, a2, a3, a4, a5, a6⟩ := f6 h o ho
    have hxnd : x ∉ dataIds sp al db tr := by
      intro hxd'
      obtain ⟨hnone, -⟩ := step_dataIds_spec sp al db tr hinv hstep hxd'
      have := hinv.dIndex (x, d) hxd
      simp [isIndex, hnone] at this
    have hsame : o'.pos = o.pos ∧ ∀ z, o'.slot? z = o.slot? z := by
      rcases a6 with ⟨h2, -⟩ | ⟨-, h1, h3⟩
      · rw [hn2] at h2; exact absurd h2 hxnd
      · exact ⟨h1, h3⟩
    have hc' : w2.1.canonicalOf x = some h := by rw [e6]; exact hc
    refine ⟨h, o', n, hc', ho', hn, by rw [a1, hn2], by rw [a4, hh], by rw [a2, hl], by rw [a3, hd],
      fun y hy hyD1 => ?_⟩
    have hyD : inD db.D y = false := by
      cases hyd : inD db.D y with
      | false => rfl
      | true =>
        exfalso
        have : inD (parts sp al db tr).D1 y = true := by
          obtain ⟨dy, hdy⟩ := (inD_iff _ _).mp hyd
          exact (inD_iff _ _).mpr ⟨dy, (step_D1_mem sp al db tr hinv.len _).mpr (Or.inl hdy)⟩
        rw [this] at hyD1; cases hyD1
    obtain ⟨sl, hsl, hi⟩ := ha.slots h o ho hco (by rw [hn2]; exact hinv.written_of_D hxD) (Or.inr (Or.inl (by
      rw [hn2]; exact hxD))) y (by rw [hh]; exact hy)
    obtain ⟨hval, hnew⟩ := hi.1 hyD
    by_cases hyn : y ∈ (parts sp al db tr).c.new.map (·.id)
    · obtain ⟨h', hsl', hcy⟩ := hnew hyn
      exact Or.inl ⟨h', by rw [hsame.2, hsl, hsl'], by rw [e6]; exact hcy⟩
    · right
      refine ⟨?_, ?_⟩
      · rw [Mem.slotRef_eq, hsame.2, hsl]
        simp only [Option.bind_some]
        rw [← hval]
        cases sl with
        | mem h'' =>
          obtain ⟨o'', ho'', hn''⟩ := ha.slotsNode h o ho y h'' hsl
          obtain ⟨o3, ho3, b1, -, -, -, -, b6⟩ := f6 h'' o'' ho''
          have hp : o3.pos = o''.pos := by
            rcases b6 with ⟨b7, -⟩ | ⟨-, b6, -⟩
            · exfalso; rw [hn''] at b7; exact hyn (hdnew y b7)
            · exact b6
          simp only [slotRefOf, ho3, ho'', Option.bind_some, hp]
        | stream r =>
          simp only [slotRefOf]
          rw [← hw2, (writeNodes_frame sp S0 db.D (k + 1) (dataIds sp al db tr) m3 hdnd ha.tbl).2.1]
      · intro hyw
        rcases List.mem_append.mp hyw with h1 | h1
        · exact hyn (hdnew y h1)
        · obtain ⟨dy, hdy, -⟩ := step_taken_inD (al := al) (tr := tr) hinv h1
          rw [(inD_iff _ _).mpr ⟨dy, hdy⟩] at hyD; cases hyD
  obtain ⟨g1, g2, -, -, -, -⟩ := writeNodes_eq sp S0 db.S (parts sp al db tr).P (parts sp al db tr).D1 (k + 1)
    (parts sp al db tr).taken (parts sp al db tr).vs0 w2.1 wr e3 e4
    (fun y hy => by rw [e6]; exact ha.canon_D1 hsp hinv hmk hstep hy) e2 hok2
    (fun v hv => by
      rw [hvs0] at hv
      rcases writeAll_node_mem sp db.S (k + 1) _ _ [] hv with h | h
      · cases h
      · exact List.mem_append_left _ h)
    (fun x hx => List.mem_append_right _ hx) htnd
    (fun x hx v hv => by
      rw [hvs0] at hv
      rcases writeAll_node_mem sp db.S (k + 1) _ _ [] hv with h | h
      · cases h
      · intro he
        rw [he] at h
        obtain ⟨d, hxd, -⟩ := step_taken_inD (al := al) (tr := tr) hinv hx
        obtain ⟨hnone, -⟩ := step_dataIds_spec sp al db tr hinv hstep h
        have := hinv.dIndex (x, d) hxd
        simp [isIndex, hnone] at this)
  rw [← hvs] at g1 g2
  exact ⟨e1, e2, by rw [e1]; exact g1, g2⟩

/-- What the two loops change, from the memory after the change (m3) to the
memory after the record (m6). -/
structure LoopsFrame (D0 D1 : Dirty) (xs1 xs2 : List NodeId) (i : Nat) (m3 m6 : Mem V) : Prop where
  table : m6.table = m3.table
  s : m6.s = m3.s
  root : m6.root = m3.root
  next : m6.next = m3.next
  canon : ∀ y, m6.canonicalOf y = m3.canonicalOf y
  none : ∀ h, m3.obj? h = none → m6.obj? h = none
  nodup : (m3.objs.map (·.1)).Nodup → (m6.objs.map (·.1)).Nodup
  obj : ∀ h o3, m3.obj? h = some o3 → ∃ o6, m6.obj? h = some o6 ∧ o6.node = o3.node ∧
    o6.level = o3.level ∧ o6.isData = o3.isData ∧ o6.hist = o3.hist ∧ o6.canonical = o3.canonical ∧
    (∀ z, o6.slot? z = o3.slot? z ∨ ((inD D0 z = true ∨ inD D1 z = true) ∧
      ∃ sl h0, o3.slot? z = some sl ∧ m3.canonicalOf z = some h0 ∧ o6.slot? z = some (Slot.mem h0))) ∧
    ((o3.node ∈ xs2 ∧ m3.canonicalOf o3.node = some h) → ∀ z sl h0, o3.slot? z = some sl →
      inD D1 z = true → m3.canonicalOf z = some h0 → o6.slot? z = some (Slot.mem h0)) ∧
    (¬ ((o3.node ∈ xs1 ∨ o3.node ∈ xs2) ∧ m3.canonicalOf o3.node = some h) →
      o6.pos = o3.pos ∧ ∀ z, o6.slot? z = o3.slot? z)

theorem loopsFrame (sp : Spec V T) (S0 : Stream V T) (D0 D1 : Dirty) (i : Nat) (xs1 xs2 : List NodeId)
    (m3 : Mem V) (h1 : xs1.Nodup) (h2 : xs2.Nodup) (htn : TableNode m3)
    (hdisj : ∀ x ∈ xs1, x ∉ xs2) :
    LoopsFrame D0 D1 xs1 xs2 i m3 ((m3.writeNodes sp S0 D0 i xs1).1.writeNodes sp S0 D1 i xs2).1 := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ := writeNodes_frame sp S0 D0 i xs1 m3 h1 htn
  have htn2 : TableNode (m3.writeNodes sp S0 D0 i xs1).1 := by
    intro y h ht
    rw [show (m3.writeNodes sp S0 D0 i xs1).1.tableOf y = m3.tableOf y by unfold Mem.tableOf; rw [a1]] at ht
    obtain ⟨o, ho, hno⟩ := htn y h ht
    obtain ⟨o1, ho1, e1, -⟩ := a6 h o ho
    exact ⟨o1, ho1, by rw [e1, hno]⟩
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8⟩ := writeNodes_frame sp S0 D1 i xs2 _ h2 htn2
  refine ⟨by rw [b1, a1], by rw [b2, a2], by rw [b3, a3], by rw [b4, a4], fun y => by rw [b5, a5],
    fun h hn => b7 h (a7 h hn), fun hnd => b8 (a8 hnd), fun h o3 ho3 => ?_⟩
  obtain ⟨o2, ho2, c1, c2, c3, c4, c5, c6⟩ := a6 h o3 ho3
  obtain ⟨o6, ho6, d1, d2, d3, d4, d5, d6⟩ := b6 h o2 ho2
  refine ⟨o6, ho6, by rw [d1, c1], by rw [d2, c2], by rw [d3, c3], by rw [d4, c4], by rw [d5, c5], ?_, ?_, ?_⟩
  · intro z
    have hp1 : o2.slot? z = o3.slot? z ∨ (inD D0 z = true ∧ ∃ sl h0, o3.slot? z = some sl ∧
        m3.canonicalOf z = some h0 ∧ o2.slot? z = some (Slot.mem h0)) := by
      rcases c6 with ⟨-, -, -, s1⟩ | ⟨-, -, s1⟩
      · rw [s1 z]; unfold pinnedSlot
        cases hz : o3.slot? z with
        | none => left; rfl
        | some sl =>
          simp only [Option.map_some]
          by_cases hD : inD D0 z = true
          · simp only [hD, ↓reduceIte]
            cases hc : m3.canonicalOf z with
            | none => left; rfl
            | some h0 => right; exact ⟨trivial, sl, h0, rfl, rfl, rfl⟩
          · left; simp [hD]
      · left; exact s1 z
    have hp2 : o6.slot? z = o2.slot? z ∨ (inD D1 z = true ∧ ∃ sl h0, o2.slot? z = some sl ∧
        m3.canonicalOf z = some h0 ∧ o6.slot? z = some (Slot.mem h0)) := by
      rcases d6 with ⟨-, -, -, s2⟩ | ⟨-, -, s2⟩
      · rw [s2 z]; unfold pinnedSlot
        cases hz : o2.slot? z with
        | none => left; rfl
        | some sl =>
          simp only [Option.map_some]
          by_cases hD : inD D1 z = true
          · simp only [hD, ↓reduceIte, a5]
            cases hc : m3.canonicalOf z with
            | none => left; rfl
            | some h0 => right; exact ⟨trivial, sl, h0, rfl, rfl, rfl⟩
          · left; simp [hD]
      · left; exact s2 z
    rcases hp2 with hp2 | ⟨hD1, sl, h0, hs2, hc0, hs6⟩
    · rw [hp2]
      rcases hp1 with hp1 | ⟨hD0, sl, h0, hs3, hc0, hs2⟩
      · left; exact hp1
      · right; exact ⟨Or.inl hD0, sl, h0, hs3, hc0, hs2⟩
    · right
      rcases hp1 with hp1 | ⟨hD0, sl', h0', hs3, hc0', hs2'⟩
      · exact ⟨Or.inr hD1, sl, h0, by rw [← hp1]; exact hs2, hc0, hs6⟩
      · exact ⟨Or.inr hD1, sl', h0, hs3, hc0, hs6⟩
  · intro ⟨hx2, hcx⟩ z sl h0 hsl hD1 hc0
    -- x's object was not written by the data loop (x is not one of its nodes)
    have hx1 : o3.node ∉ xs1 := fun h => hdisj _ h hx2
    have hs2 : o2.slot? z = o3.slot? z := by
      rcases c6 with ⟨h1', -⟩ | ⟨-, -, s1⟩
      · exact absurd h1' hx1
      · exact s1 z
    rcases d6 with ⟨-, -, -, s2⟩ | ⟨hn, -, -⟩
    · rw [s2 z]; unfold pinnedSlot
      rw [hs2, hsl]
      simp only [Option.map_some, hD1, ↓reduceIte, a5, hc0]
    · exfalso; exact hn ⟨by rw [c1]; exact hx2, by rw [c1, a5]; exact hcx⟩
  · intro hn
    have hp1 : o2.pos = o3.pos ∧ ∀ z, o2.slot? z = o3.slot? z := by
      rcases c6 with ⟨h1', hc1', -⟩ | ⟨-, p1, s1⟩
      · exact absurd ⟨Or.inl h1', hc1'⟩ hn
      · exact ⟨p1, s1⟩
    rcases d6 with ⟨h2', hc2', -⟩ | ⟨-, p2, s2⟩
    · exfalso; exact hn ⟨Or.inr (by rw [← c1]; exact h2'), by rw [← c1, ← a5]; exact hc2'⟩
    · exact ⟨by rw [p2, hp1.1], fun z => by rw [s2 z, hp1.2 z]⟩

theorem dOf_of_mem : ∀ {D : Dirty}, (D.map (·.1)).Nodup → ∀ {z : NodeId} {d : Nat}, (z, d) ∈ D →
    dOf D z = some d
  | [], _, _, _, h => by cases h
  | e :: D, hnd, z, d, h => by
    simp only [List.map_cons, List.nodup_cons] at hnd
    unfold dOf
    simp only [List.find?_cons]
    rcases List.mem_cons.mp h with rfl | h
    · simp
    · have hne : e.1 ≠ z := by
        intro he; apply hnd.1; rw [he]; exact List.mem_map.mpr ⟨(z, d), h, rfl⟩
      have : (e.1 == z) = false := by simp [hne]
      simp only [this]
      exact dOf_of_mem hnd.2 h

theorem mem_of_dOf {D : Dirty} {z : NodeId} {d : Nat} (h : dOf D z = some d) : (z, d) ∈ D := by
  unfold dOf at h
  cases hf : D.find? (fun e => e.1 == z) with
  | none => rw [hf] at h; cases h
  | some e =>
    rw [hf] at h
    simp only [Option.map_some, Option.some.injEq] at h
    have he := List.find?_some hf
    simp only [beq_iff_eq] at he
    have hm := List.mem_of_find?_eq_some hf
    rw [← he, ← h]
    exact hm

theorem dOf_inD {D : Dirty} {z : NodeId} (h : inD D z = true) : ∃ d, dOf D z = some d := by
  obtain ⟨d, hd⟩ := (inD_iff D z).mp h
  unfold dOf
  cases hf : D.find? (fun e => e.1 == z) with
  | none =>
    exfalso
    rw [List.find?_eq_none] at hf
    exact hf (z, d) hd (by simp)
  | some e => exact ⟨e.2, rfl⟩

/-- An entry of D after the transaction: got dirty in it, or an entry of D before
that was not taken. -/
theorem step_D'_entry {k : Nat} (hinv : Inv sp db k) {z : NodeId} {d : Nat}
    (h : (z, d) ∈ (parts sp al db tr).r7.1) : d = k + 1 ∨ ((z, d) ∈ db.D ∧ (parts sp al db tr).s < d) := by
  rw [(step_r7_shape sp al db tr hinv.len).1] at h
  rcases List.mem_append.mp h with h | h
  · obtain ⟨hD1, hs⟩ := (step_D2_mem sp al db tr _).mp h
    rcases (step_D1_mem sp al db tr hinv.len _).mp hD1 with h1 | ⟨h1, -⟩
    · exact Or.inr ⟨h1, hs⟩
    · exact Or.inl h1
  · obtain ⟨x, -, hx⟩ := List.mem_map.mp h
    simp only [Prod.mk.injEq] at hx
    exact Or.inl hx.2.symm

theorem lv_building_Snew (z : NodeId) :
    (db.S.building (parts sp al db tr).vs).lv z = (Snew sp al db tr).lv z := by
  unfold Snew Stream.building
  rw [lv_append, lv_append]
  simp [Stream.lv, parts_R]

end Writes

end SIS
