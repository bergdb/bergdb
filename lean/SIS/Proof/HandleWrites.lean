/-
Proofs about the physical layer with handles (bergdb item 009, step 2d), part 9:
the physical writer's two loops (the new data nodes, then the taken nodes) write
the model's record, and what they change.
-/
import SIS.Proof.HandleWrite

set_option linter.unusedSectionVars false

namespace SIS

variable {V T : Type} [DecidableEq V]

/-! ## What the writer's loop changes -/

theorem HMem.resolveP_congr {m m' : HMem V} (S0 : Stream V T) (D : Dirty)
    (hc : ∀ p, m'.holdsCanonical p = m.holdsCanonical p) (hcan : ∀ y, m'.canonicalOf y = m.canonicalOf y)
    (ht : ∀ y, m'.tableOf y = m.tableOf y) (hs : m'.s = m.s) :
    m'.resolveP S0 D = m.resolveP S0 D := by
  funext z q
  unfold HMem.resolveP
  rw [hc, hcan, ht, hs]

/-- Object o' at address a is object o after the loop that writes the nodes xs
with the pinned set D, from memory m: the same node, level, kind, history and
flag; record i and the pointers as `resolvePointers` leaves them if o is the
canonical object of a node of xs, the same position and pointers otherwise. -/
def HWrittenAt (S0 : Stream V T) (m : HMem V) (D : Dirty) (i : Nat) (xs : List NodeId) (a : Nat)
    (o o' : HObj V) : Prop :=
  o'.node = o.node ∧ o'.level = o.level ∧ o'.isData = o.isData ∧ o'.hist = o.hist ∧
    o'.canonical = o.canonical ∧
    ((o.node ∈ xs ∧ m.canonicalOf o.node = some a ∧ o'.pos = some i ∧
       ∀ z, o'.ptr? z = (o.ptr? z).map (m.resolveP S0 D z)) ∨
     (¬ (o.node ∈ xs ∧ m.canonicalOf o.node = some a) ∧ o'.pos = o.pos ∧ ∀ z, o'.ptr? z = o.ptr? z))

section Loop

variable (sp : Spec V T) (S0 : Stream V T) (D : Dirty) (i : Nat)

theorem writeNodesH_frame : ∀ (xs : List NodeId) (m : HMem V), xs.Nodup → HTableOK m →
    (m.writeNodes sp S0 D i xs).1.table = m.table ∧ (m.writeNodes sp S0 D i xs).1.handles = m.handles ∧
    (m.writeNodes sp S0 D i xs).1.s = m.s ∧ (m.writeNodes sp S0 D i xs).1.root = m.root ∧
    (m.writeNodes sp S0 D i xs).1.nextObj = m.nextObj ∧
    (m.writeNodes sp S0 D i xs).1.nextHandle = m.nextHandle ∧
    (∀ y, (m.writeNodes sp S0 D i xs).1.canonicalOf y = m.canonicalOf y) ∧
    (∀ p, (m.writeNodes sp S0 D i xs).1.holdsCanonical p = m.holdsCanonical p) ∧
    HTableOK (m.writeNodes sp S0 D i xs).1 ∧
    (∀ a o, m.obj? a = some o → ∃ o', (m.writeNodes sp S0 D i xs).1.obj? a = some o' ∧
      HWrittenAt S0 m D i xs a o o') ∧
    (∀ a, m.obj? a = none → (m.writeNodes sp S0 D i xs).1.obj? a = none) ∧
    ((m.objs.map (·.1)).Nodup → ((m.writeNodes sp S0 D i xs).1.objs.map (·.1)).Nodup) := by
  intro xs
  induction xs with
  | nil =>
    intro m _ htb
    have h0 : m.writeNodes sp S0 D i [] = (m, []) := rfl
    rw [h0]
    refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, fun _ => rfl, fun _ => rfl, htb, fun a o ho => ⟨o, ho, rfl, rfl, rfl,
      rfl, rfl, Or.inr ⟨fun h => by simp at h, rfl, fun _ => rfl⟩⟩, fun _ h => h, id⟩
  | cons x xs ih =>
    intro m hnd htb
    simp only [List.nodup_cons] at hnd
    rw [writeNodesH_eq_foldl, List.foldl_cons]
    -- One write: x's canonical object, if any.
    have hone : ∃ m1 : HMem V, (hwnStep sp S0 D i (m, []) x).1 = m1 ∧
        (xs.foldl (hwnStep sp S0 D i) (hwnStep sp S0 D i (m, []) x)).1 = (m1.writeNodes sp S0 D i xs).1 ∧
        m1.table = m.table ∧ m1.handles = m.handles ∧ m1.s = m.s ∧ m1.root = m.root ∧
        m1.nextObj = m.nextObj ∧ m1.nextHandle = m.nextHandle ∧
        (∀ y, m1.canonicalOf y = m.canonicalOf y) ∧ (∀ p, m1.holdsCanonical p = m.holdsCanonical p) ∧
        HTableOK m1 ∧
        (∀ a o, m.obj? a = some o → ∃ o1, m1.obj? a = some o1 ∧ HWrittenAt S0 m D i [x] a o o1) ∧
        (∀ a, m.obj? a = none → m1.obj? a = none) ∧
        ((m.objs.map (·.1)).Nodup → (m1.objs.map (·.1)).Nodup) := by
      cases hc : m.canonicalOf x with
      | none =>
        have hw : m.writeNode sp S0 D i x = (m, none) := by unfold HMem.writeNode; rw [hc]
        refine ⟨m, by rw [hwnStep_none sp S0 D i hw], ?_, rfl, rfl, rfl, rfl, rfl, rfl, fun _ => rfl,
          fun _ => rfl, htb,
          fun a o ho => ⟨o, ho, rfl, rfl, rfl, rfl, rfl, Or.inr ⟨fun ⟨h1, h2⟩ => ?_, rfl, fun _ => rfl⟩⟩,
          fun _ h => h, id⟩
        · rw [hwnStep_none sp S0 D i hw, foldl_hwnStep_prefix, writeNodesH_eq_foldl]
        · simp only [List.mem_singleton] at h1
          rw [h1, hc] at h2; cases h2
      | some a0 =>
        cases ho0 : m.obj? a0 with
        | none =>
          have hw : m.writeNode sp S0 D i x = (m, none) := by unfold HMem.writeNode; rw [hc]; simp [ho0]
          refine ⟨m, by rw [hwnStep_none sp S0 D i hw], ?_, rfl, rfl, rfl, rfl, rfl, rfl, fun _ => rfl,
            fun _ => rfl, htb,
            fun a o ho => ⟨o, ho, rfl, rfl, rfl, rfl, rfl, Or.inr ⟨fun ⟨h1, h2⟩ => ?_, rfl, fun _ => rfl⟩⟩,
            fun _ h => h, id⟩
          · rw [hwnStep_none sp S0 D i hw, foldl_hwnStep_prefix, writeNodesH_eq_foldl]
          · simp only [List.mem_singleton] at h1
            rw [h1, hc, Option.some.injEq] at h2
            subst h2
            rw [ho0] at ho; cases ho
        | some o0 =>
          have hw := HMem.writeNode_shape sp S0 D i hc ho0
          have hnode : o0.node = x := by
            obtain ⟨o2, ho2, hn2, -⟩ := htb.canonicalOf_node hc
            rw [ho0, Option.some.injEq] at ho2; subst ho2; exact hn2
          have hco : ({ o0 with pos := some i, ptrs := o0.ptrs.map (m.resolvePtr S0 D) } : HObj V).canonical =
              o0.canonical := rfl
          refine ⟨m.setObj a0 { o0 with pos := some i, ptrs := o0.ptrs.map (m.resolvePtr S0 D) }, by
            rw [hwnStep_some sp S0 D i hw], by
            rw [hwnStep_some sp S0 D i hw, foldl_hwnStep_prefix, writeNodesH_eq_foldl], rfl, rfl, rfl, rfl, rfl,
            rfl, HMem.canonicalOf_setObj_flag ho0 hco, HMem.holdsCanonical_setObj_flag ho0 hco,
            htb.setObj ho0 rfl (htb.resolve_node S0 D i ho0), fun a o ho => ?_, fun a hn => ?_,
            fun hnd' => HMem.setObj_nodup m a0 _ hnd'⟩
          · rw [HMem.obj?_setObj]
            split
            · rename_i he; subst he
              rw [ho0, Option.some.injEq] at ho; subst ho
              refine ⟨_, rfl, rfl, rfl, rfl, rfl, rfl,
                Or.inl ⟨by simp [hnode], by rw [hnode]; exact hc, rfl, fun z => ?_⟩⟩
              exact HMem.ptr?_resolve S0 m D o0.ptrs z
            · rename_i hne
              refine ⟨o, ho, rfl, rfl, rfl, rfl, rfl, Or.inr ⟨fun ⟨h1, h2⟩ => ?_, rfl, fun _ => rfl⟩⟩
              simp only [List.mem_singleton] at h1
              rw [h1, hc, Option.some.injEq] at h2
              exact hne h2.symm
          · rw [HMem.obj?_setObj]
            split
            · rename_i he; subst he; rw [ho0] at hn; cases hn
            · exact hn
    obtain ⟨m1, hm1, hfold, ht1, hh1, hs1, hr1, hn1, hnh1, hc1, hhc1, htb1, hobj1, hnone1, hnd1⟩ := hone
    rw [hfold]
    obtain ⟨t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12⟩ := ih m1 hnd.2 htb1
    have hres : m1.resolveP S0 D = m.resolveP S0 D :=
      HMem.resolveP_congr S0 D hhc1 hc1 (fun y => by unfold HMem.tableOf; rw [ht1]) hs1
    refine ⟨by rw [t1, ht1], by rw [t2, hh1], by rw [t3, hs1], by rw [t4, hr1], by rw [t5, hn1],
      by rw [t6, hnh1], fun y => by rw [t7, hc1], fun p => by rw [t8, hhc1], t9, fun a o ho => ?_,
      fun a hn => t11 a (hnone1 a hn), fun hnd' => t12 (hnd1 hnd')⟩
    obtain ⟨o1, ho1, a1, a2, a3, a4, a5, a6⟩ := hobj1 a o ho
    obtain ⟨o', ho', b1, b2, b3, b4, b5, b6⟩ := t10 a o1 ho1
    refine ⟨o', ho', by rw [b1, a1], by rw [b2, a2], by rw [b3, a3], by rw [b4, a4], by rw [b5, a5], ?_⟩
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
      rw [s2 z, hres, s1 z]
    · refine Or.inr ⟨fun ⟨h1, h2⟩ => ?_, by rw [p2, p1], fun z => by rw [s2 z, s1 z]⟩
      rcases List.mem_cons.mp h1 with h1 | h1
      · exact n1 ⟨by rw [h1]; exact List.mem_singleton_self _, h2⟩
      · exact n2 ⟨by rw [a1]; exact h1, by rw [a1, hc1]; exact h2⟩

end Loop

/-! ## The two loops of a transaction -/

/-- What the two loops change, from the memory after the change (m3) to the
memory after the record (m6). -/
structure LoopsFrameH (S0 : Stream V T) (D0 D1 : Dirty) (xs1 xs2 : List NodeId) (i : Nat) (m3 m6 : HMem V) :
    Prop where
  table : m6.table = m3.table
  handles : m6.handles = m3.handles
  s : m6.s = m3.s
  root : m6.root = m3.root
  nextObj : m6.nextObj = m3.nextObj
  nextHandle : m6.nextHandle = m3.nextHandle
  canon : ∀ y, m6.canonicalOf y = m3.canonicalOf y
  hc : ∀ p, m6.holdsCanonical p = m3.holdsCanonical p
  tbl : HTableOK m6
  none : ∀ a, m3.obj? a = none → m6.obj? a = none
  nodup : (m3.objs.map (·.1)).Nodup → (m6.objs.map (·.1)).Nodup
  obj : ∀ a o3, m3.obj? a = some o3 → ∃ o6, m6.obj? a = some o6 ∧ o6.node = o3.node ∧
    o6.level = o3.level ∧ o6.isData = o3.isData ∧ o6.hist = o3.hist ∧ o6.canonical = o3.canonical ∧
    (∀ z, o6.ptr? z = o3.ptr? z ∨ o6.ptr? z = (o3.ptr? z).map (m3.resolveP S0 D0 z) ∨
      o6.ptr? z = (o3.ptr? z).map (m3.resolveP S0 D1 z)) ∧
    ((o3.node ∈ xs2 ∧ m3.canonicalOf o3.node = some a) →
      ∀ z, o6.ptr? z = (o3.ptr? z).map (m3.resolveP S0 D1 z)) ∧
    (¬ ((o3.node ∈ xs1 ∨ o3.node ∈ xs2) ∧ m3.canonicalOf o3.node = some a) →
      o6.pos = o3.pos ∧ ∀ z, o6.ptr? z = o3.ptr? z)

theorem loopsFrameH (sp : Spec V T) (S0 : Stream V T) (D0 D1 : Dirty) (i : Nat) (xs1 xs2 : List NodeId)
    (m3 : HMem V) (h1 : xs1.Nodup) (h2 : xs2.Nodup) (htb : HTableOK m3)
    (hdisj : ∀ x ∈ xs1, x ∉ xs2) :
    LoopsFrameH S0 D0 D1 xs1 xs2 i m3 ((m3.writeNodes sp S0 D0 i xs1).1.writeNodes sp S0 D1 i xs2).1 := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12⟩ := writeNodesH_frame sp S0 D0 i xs1 m3 h1 htb
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12⟩ := writeNodesH_frame sp S0 D1 i xs2 _ h2 a9
  have hres : (m3.writeNodes sp S0 D0 i xs1).1.resolveP S0 D1 = m3.resolveP S0 D1 :=
    HMem.resolveP_congr S0 D1 a8 a7 (fun y => by unfold HMem.tableOf; rw [a1]) a3
  refine ⟨by rw [b1, a1], by rw [b2, a2], by rw [b3, a3], by rw [b4, a4], by rw [b5, a5], by rw [b6, a6],
    fun y => by rw [b7, a7], fun p => by rw [b8, a8], b9, fun a hn => b11 a (a11 a hn),
    fun hnd => b12 (a12 hnd), fun a o3 ho3 => ?_⟩
  obtain ⟨o2, ho2, c1, c2, c3, c4, c5, c6⟩ := a10 a o3 ho3
  obtain ⟨o6, ho6, d1, d2, d3, d4, d5, d6⟩ := b10 a o2 ho2
  refine ⟨o6, ho6, by rw [d1, c1], by rw [d2, c2], by rw [d3, c3], by rw [d4, c4], by rw [d5, c5], ?_, ?_, ?_⟩
  · intro z
    rcases c6 with ⟨x1, -, -, s1⟩ | ⟨-, -, s1⟩ <;> rcases d6 with ⟨x2, -, -, s2⟩ | ⟨-, -, s2⟩
    · exfalso; rw [c1] at x2; exact hdisj _ x1 x2
    · right; left; rw [s2 z, s1 z]
    · right; right; rw [s2 z, hres, s1 z]
    · left; rw [s2 z, s1 z]
  · intro ⟨hx2, hcx⟩ z
    have hx1 : o3.node ∉ xs1 := fun h => hdisj _ h hx2
    rcases c6 with ⟨h1', -⟩ | ⟨-, -, s1⟩
    · exact absurd h1' hx1
    · rcases d6 with ⟨-, -, -, s2⟩ | ⟨hn, -, -⟩
      · rw [s2 z, hres, s1 z]
      · exfalso; exact hn ⟨by rw [c1]; exact hx2, by rw [c1, a7]; exact hcx⟩
  · intro hn
    have hp1 : o2.pos = o3.pos ∧ ∀ z, o2.ptr? z = o3.ptr? z := by
      rcases c6 with ⟨h1', hc1', -⟩ | ⟨-, p1, s1⟩
      · exact absurd ⟨Or.inl h1', hc1'⟩ hn
      · exact ⟨p1, s1⟩
    rcases d6 with ⟨h2', hc2', -⟩ | ⟨-, p2, s2⟩
    · exfalso; exact hn ⟨Or.inr (by rw [← c1]; exact h2'), by rw [← c1, ← a7]; exact hc2'⟩
    · exact ⟨by rw [p2, hp1.1], fun z => by rw [s2 z, hp1.2 z]⟩

section Writes

variable {sp : Spec V T} {al : Algo V T} {db : DB V T} {tr : T} {S0 : Stream V T} {k : Nat}

/-- The nodes of D1 have canonical objects after the change: they are in D, or
marked (on the writer's paths, or new). -/
theorem HAInv.canon_D1 (hsp : SpecOK sp) (hinv : Inv sp db k) (hmk : al.mark = true)
    (hstep : StepOK sp db.P (k + 1) (parts sp al db tr).c) {m3 : HMem V}
    (ha : HAInv sp db S0 k (parts sp al db tr).c (pathOf sp db.P (parts sp al db tr).c (k + 1)) m3)
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
theorem HAInv.loops_vs (hsp : SpecOK sp) (hinv : Inv sp db k) (hmk : al.mark = true)
    (hstep : StepOK sp db.P (k + 1) (parts sp al db tr).c) (hinv' : Inv sp (step sp al db tr) (k + 1))
    {m3 : HMem V}
    (ha : HAInv sp db S0 k (parts sp al db tr).c (pathOf sp db.P (parts sp al db tr).c (k + 1)) m3) :
    (m3.writeNodes sp S0 db.D (k + 1) (dataIds sp al db tr)).2 = (parts sp al db tr).vs0 ∧
    HPosOK db.S (parts sp al db tr).vs0 (m3.writeNodes sp S0 db.D (k + 1) (dataIds sp al db tr)).1 ∧
    (m3.writeNodes sp S0 db.D (k + 1) (dataIds sp al db tr)).2 ++
      ((m3.writeNodes sp S0 db.D (k + 1) (dataIds sp al db tr)).1.writeNodes sp S0 (parts sp al db tr).D1
        (k + 1) (parts sp al db tr).taken).2 = (parts sp al db tr).vs ∧
    HPosOK db.S (parts sp al db tr).vs ((m3.writeNodes sp S0 db.D (k + 1) (dataIds sp al db tr)).1.writeNodes
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
  have hpos0 : HPosOK db.S [] m3 := by
    intro a o ho hc
    rw [ha.pos a o ho hc, lv_building]
    rfl
  -- The new data nodes: canonical objects with their whole history, no pointees.
  have hok1 : ∀ x ∈ dataIds sp al db tr, HWriteOK sp S0 db.S (parts sp al db tr).P db.D wr m3 x := by
    intro x hx
    obtain ⟨a, hc⟩ := Option.isSome_iff_exists.mp (ha.canon x (Or.inr (Or.inr (hdnew x hx))))
    obtain ⟨o, ho, hon, hco⟩ := ha.tbl.canonicalOf_node hc
    obtain ⟨n, hn, hh, hl, hd⟩ := ha.cc a o ho hco
    rw [hon, ← hP] at hn
    obtain ⟨-, n', hn', hdat⟩ := step_dataIds_spec sp al db tr hinv hstep hx
    rw [hn, Option.some.injEq] at hn'; subst hn'
    refine ⟨a, o, n, hc, ho, hn, hon, hh, hl, hd, fun y hy => ?_⟩
    exfalso
    rw [mem_pointees] at hy
    obtain ⟨e, he, hye⟩ := hy
    have := hinv'.data x n (by rw [step_P]; exact hn) hdat e he
    rw [this] at hye; cases hye
  obtain ⟨e1, e2, e3, e4⟩ := writeNodesH_eq sp S0 db.S (parts sp al db tr).P db.D (k + 1)
    (dataIds sp al db tr) [] m3 wr ha.tbl (fun y hy => ha.canon y (Or.inl hy)) hpos0 hok1
    (fun v hv => by cases hv) (fun x hx => List.mem_append_left _ hx) hdnd (fun x _ v hv => by cases hv)
  rw [List.nil_append] at e1
  rw [← hvs0] at e1 e2
  -- The frame of the data loop: the old objects keep their pointers and positions.
  obtain ⟨f1, f2, f3, -, -, -, -, -, -, f10, -, -⟩ :=
    writeNodesH_frame sp S0 db.D (k + 1) (dataIds sp al db tr) m3 hdnd ha.tbl
  generalize hw2 : m3.writeNodes sp S0 db.D (k + 1) (dataIds sp al db tr) = w2 at e1 e2 e3 e4 f1 f2 f3 f10
  -- The taken nodes.
  have htnd := step_taken_nodup sp al db tr hinv
  have hok2 : ∀ x ∈ (parts sp al db tr).taken,
      HWriteOK sp S0 db.S (parts sp al db tr).P (parts sp al db tr).D1 wr w2.1 x := by
    intro x hx
    obtain ⟨d, hxd, -⟩ := step_taken_inD (al := al) (tr := tr) hinv hx
    have hxD : inD db.D x = true := (inD_iff _ _).mpr ⟨d, hxd⟩
    obtain ⟨a, hc⟩ := Option.isSome_iff_exists.mp (ha.canon x (Or.inl hxD))
    obtain ⟨o, ho, hon, hco⟩ := ha.tbl.canonicalOf_node hc
    obtain ⟨n, hn, hh, hl, hd⟩ := ha.cc a o ho hco
    rw [hon, ← hP] at hn
    -- x's object is not a data node's: unchanged by the data loop.
    obtain ⟨o', ho', a1, a2, a3, a4, a5, a6⟩ := f10 a o ho
    have hxnd : x ∉ dataIds sp al db tr := by
      intro hxd'
      obtain ⟨hnone, -⟩ := step_dataIds_spec sp al db tr hinv hstep hxd'
      have := hinv.dIndex (x, d) hxd
      simp [isIndex, hnone] at this
    have hsame : o'.pos = o.pos ∧ ∀ z, o'.ptr? z = o.ptr? z := by
      rcases a6 with ⟨h2, -⟩ | ⟨-, h1, h3⟩
      · rw [hon] at h2; exact absurd h2 hxnd
      · exact ⟨h1, h3⟩
    have hc' : w2.1.canonicalOf x = some a := by rw [e4]; exact hc
    refine ⟨a, o', n, hc', ho', hn, by rw [a1, hon], by rw [a4, hh], by rw [a2, hl], by rw [a3, hd],
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
    obtain ⟨p, hp, hi1, -⟩ := ha.slots a o ho hco (by rw [hon]; exact hinv.written_of_D hxD)
      (Or.inr (Or.inl (by rw [hon]; exact hxD))) y (by rw [hh]; exact hy)
    obtain ⟨hval, hnew⟩ := hi1 hyD
    refine ⟨p, by rw [hsame.2]; exact hp, ?_⟩
    have htab2 : ∀ z, w2.1.tableOf z = m3.tableOf z := by intro z; unfold HMem.tableOf; rw [f1]
    by_cases hyn : y ∈ (parts sp al db tr).c.new.map (·.id)
    · left
      obtain ⟨n0, h1, h2, h3⟩ := hnew hyn
      exact ⟨n0, h1, by rw [htab2]; exact h2, by rw [e4]; exact h3⟩
    · right
      refine ⟨?_, ?_⟩
      · rw [← hval]
        -- the record rule in w2 is m3's: the object the handle holds, of node y, is not written
        apply HMem.ptrRef_congr S0 f3
        · cases hpn : p.handle with
          | none => rfl
          | some n0 =>
            simp only [Option.bind_some]
            unfold HMem.handle?; rw [f2]
        · intro hd b hph hb
          have hob : ∃ ob, m3.obj? b = some ob ∧ ob.node = y := by
            cases hpn : p.handle with
            | none => rw [hpn] at hph; cases hph
            | some n0 =>
              rw [hpn] at hph
              simp only [Option.bind_some] at hph
              obtain ⟨hd', hh', hy'⟩ := ha.tbl.ptrNode ho hp hpn
              rw [hph, Option.some.injEq] at hh'
              subst hh'
              obtain ⟨-, ob, hob, hob'⟩ := ha.tbl.obj_of_handle hph hb
              exact ⟨ob, hob, by rw [hob', hy']⟩
          obtain ⟨ob, hob, hony⟩ := hob
          obtain ⟨ob', hob', -, -, -, -, b5, b6⟩ := f10 b ob hob
          have hp' : ob'.pos = ob.pos := by
            rcases b6 with ⟨b7, -⟩ | ⟨-, b6, -⟩
            · exfalso; rw [hony] at b7; exact hyn (hdnew y b7)
            · exact b6
          rw [hob', hob]
          simp only [Option.map_some, b5, hp']
      · intro hyw
        rcases List.mem_append.mp hyw with h1 | h1
        · exact hyn (hdnew y h1)
        · obtain ⟨dy, hdy, -⟩ := step_taken_inD (al := al) (tr := tr) hinv h1
          rw [(inD_iff _ _).mpr ⟨dy, hdy⟩] at hyD; cases hyD
  obtain ⟨g1, g2, -, -⟩ := writeNodesH_eq sp S0 db.S (parts sp al db tr).P (parts sp al db tr).D1 (k + 1)
    (parts sp al db tr).taken (parts sp al db tr).vs0 w2.1 wr e3
    (fun y hy => by rw [e4]; exact ha.canon_D1 hsp hinv hmk hstep hy) e2 hok2
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

end Writes

end SIS
