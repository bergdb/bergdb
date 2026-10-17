/-
Proofs for stage 2 (bergdb item 001, WP E4), part 2: one transaction of the
physical writer keeps the invariant for reads at earlier times (`HInv`): the
writer's walk, the change, the writes, and the step to the next state.
-/
import SIS.Proof.EvictHist
import SIS.Proof.EvictTrans

set_option linter.unusedSectionVars false

namespace SIS

variable {V T : Type} [DecidableEq V]

/-! ## The writer's walk -/

section Walk

variable {sp : Spec V T} {db : DB V T} {S0 : Stream V T} {k : Nat} {m : Mem V}

/-- Promotion after the writer's follow keeps the invariant: the slot names a
canonical object, and a snapshot promoted is of the latest version of a clean
node, good for every time at which the node is reachable. -/
theorem HInv.promote_step (hinv : Inv sp db k) (hls : LiveSub sp) (hm : EInv sp db S0 k m)
    (hh : HInv sp db S0 k m) {hp : Nat} {op : Obj V} (hop : m.obj? hp = some op)
    (hco : op.canonical = true) (hr : reachable sp db.P k op.node = true) {y : NodeId}
    (hy : y ∈ sp.live op.hist) (hyw : written sp y = true) (hyne : y ≠ op.node) {h1 : Nat}
    (hsl : op.slot? y = some (Slot.mem h1)) :
    HInv sp db S0 k (m.promote hp y h1).1 := by
  obtain ⟨o1, ho1, hn1⟩ := hm.slotsNode hp op hop y h1 hsl
  have hp1 : hp ≠ h1 := by
    intro he; subst he; rw [hop, Option.some.injEq] at ho1; subst ho1; exact hyne hn1.symm
  have hss : ∀ z, z ≠ y → ∀ sl, (op.setSlot y sl).slot? z = op.slot? z := by
    intro z hz sl; rw [slot?_setSlot_of hsl]; simp [hz]
  cases hc : m.canonicalOf y with
  | some h0 =>
    obtain ⟨o0, ho0, hc0, hn0⟩ := hm.obj_of_canonicalOf hc
    have hp0 : hp ≠ h0 := by
      intro he; subst he; rw [hop, Option.some.injEq] at ho0; subst ho0; exact hyne hn0.symm
    have hpe : m.promote hp y h1 = (match ((m.setObj h0 { o0 with canonical := true }).setTable y h0).obj? hp with
        | some op3 => ((m.setObj h0 { o0 with canonical := true }).setTable y h0).setObj hp
            (op3.setSlot y (Slot.mem h0))
        | none => (m.setObj h0 { o0 with canonical := true }).setTable y h0, h0) := by
      unfold Mem.promote; simp only [hc, Option.getD_some, ho0]; rfl
    rw [hpe, obj_with_canonical_true hc0]
    have hop3 : ((m.setObj h0 o0).setTable y h0).obj? hp = some op := by
      rw [Mem.obj?_setTable, Mem.obj?_setObj]; simp only [hp0, ↓reduceIte]; exact hop
    simp only [hop3]
    have hobj : ∀ h, (((m.setObj h0 o0).setTable y h0).setObj hp (op.setSlot y (Slot.mem h0))).obj? h =
        if h = hp then some (op.setSlot y (Slot.mem h0)) else m.obj? h := by
      intro h
      rw [Mem.obj?_setObj, Mem.obj?_setTable, Mem.obj?_setObj]
      split
      · rfl
      · split
        · rename_i _ he; subst he; exact ho0.symm
        · rfl
    have hk : m.KeepRead (((m.setObj h0 o0).setTable y h0).setObj hp (op.setSlot y (Slot.mem h0))) := by
      intro h o ho
      rw [hobj]
      split
      · rename_i he; subst he; rw [hop, Option.some.injEq] at ho; subst ho
        exact ⟨_, rfl, rfl, id, fun _ => rfl⟩
      · exact ⟨o, ho, rfl, id, fun _ => rfl⟩
    have hs : (((m.setObj h0 o0).setTable y h0).setObj hp (op.setSlot y (Slot.mem h0))).s = m.s := rfl
    apply hh.transfer hk hs
    intro h o' ho' hc' t ht hrt z hz
    rw [hobj] at ho'
    split at ho'
    · rename_i he; subst he
      simp only [Option.some.injEq] at ho'
      subst ho'
      by_cases hzy : z = y
      · subst hzy
        right
        refine ⟨Slot.mem h0, by rw [slot?_setSlot_of hsl]; simp, o0, ?_, hn0, Or.inl hc0⟩
        rw [hobj]; simp only [Ne.symm hp0, ↓reduceIte]; exact ho0
      · exact Or.inl ⟨op, hop, hco, rfl, rfl, hss z hzy _⟩
    · exact Or.inl ⟨o', ho', hc', rfl, rfl, rfl⟩
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
    -- The object reached: the snapshot of y's latest version, good at every time
    -- at which y is reachable.
    obtain ⟨sl', hsl', hli⟩ := hm.live hp op hop hco hr y hy
    rw [hsl, Option.some.injEq] at hsl'
    subst hsl'
    have hpos1 : o1.pos = (db.S.lv y).map (·.recNo) := by
      have := hli.2 hyD
      simp only [slotRefOf, ho1, Option.bind_some] at this
      exact this
    obtain ⟨r1, w1, e1, e2, -⟩ := hm.snap h1 o1 ho1 hnc
    have hgood : ∀ t ≤ k, reachable sp db.P t y = true → good sp db.S db.P t w1 = true := by
      intro t ht hrt
      obtain ⟨v, hv, hg⟩ := hinv.clean_good hls hyD hyw ht hrt
      rw [hpos1, hv] at e1
      simp only [Option.map_some, Option.some.injEq] at e1
      rw [← e1, hn1, hinv.lv_at hv, Option.some.injEq] at e2
      rw [← e2]; exact hg
    have hpe : m.promote hp y h1 = (match ((m.setObj h1 { o1 with canonical := true }).setTable y h1).obj? hp with
        | some op3 => ((m.setObj h1 { o1 with canonical := true }).setTable y h1).setObj hp
            (op3.setSlot y (Slot.mem h1))
        | none => (m.setObj h1 { o1 with canonical := true }).setTable y h1, h1) := by
      unfold Mem.promote; simp only [hc, Option.getD_none, ho1]; rfl
    rw [hpe]
    have hop3 : ((m.setObj h1 { o1 with canonical := true }).setTable y h1).obj? hp = some op := by
      rw [Mem.obj?_setTable, Mem.obj?_setObj]; simp only [hp1, ↓reduceIte]; exact hop
    simp only [hop3]
    have hobj : ∀ h, (((m.setObj h1 { o1 with canonical := true }).setTable y h1).setObj hp
        (op.setSlot y (Slot.mem h1))).obj? h =
        if h = hp then some (op.setSlot y (Slot.mem h1)) else
          if h = h1 then some { o1 with canonical := true } else m.obj? h := by
      intro h
      rw [Mem.obj?_setObj, Mem.obj?_setTable, Mem.obj?_setObj]
    have hk : m.KeepRead (((m.setObj h1 { o1 with canonical := true }).setTable y h1).setObj hp
        (op.setSlot y (Slot.mem h1))) := by
      intro h o ho
      rw [hobj]
      split
      · rename_i he; subst he; rw [hop, Option.some.injEq] at ho; subst ho
        exact ⟨_, rfl, rfl, id, fun _ => rfl⟩
      · split
        · rename_i _ he; subst he; rw [ho1, Option.some.injEq] at ho; subst ho
          exact ⟨_, rfl, rfl, fun _ => rfl, fun h => by cases h⟩
        · exact ⟨o, ho, rfl, id, fun _ => rfl⟩
    have hs : (((m.setObj h1 { o1 with canonical := true }).setTable y h1).setObj hp
        (op.setSlot y (Slot.mem h1))).s = m.s := rfl
    apply hh.transfer hk hs
    intro h o' ho' hc' t ht hrt z hz
    rw [hobj] at ho'
    split at ho'
    · rename_i he; subst he
      simp only [Option.some.injEq] at ho'
      subst ho'
      by_cases hzy : z = y
      · subst hzy
        right
        refine ⟨Slot.mem h1, by rw [slot?_setSlot_of hsl]; simp, { o1 with canonical := true }, ?_, hn1,
          Or.inl rfl⟩
        rw [hobj]; simp only [Ne.symm hp1, ↓reduceIte]
      · exact Or.inl ⟨op, hop, hco, rfl, rfl, hss z hzy _⟩
    · split at ho'
      · rename_i _ he; subst he
        simp only [Option.some.injEq] at ho'
        subst ho'
        -- the snapshot promoted: its slots are as reads need them
        right
        have hrt' : reachable sp db.P t o1.node = true := hrt
        obtain ⟨sl, hsl1, hsh, -⟩ := hm.snap_hist hinv hls ho1 hnc e1 e2 (hgood t ht (by rw [← hn1]; exact hrt'))
          (y := z) hz
        exact ⟨sl, hsl1, (hsh o1.node).keep hk hs⟩
      · exact Or.inl ⟨o', ho', hc', rfl, rfl, rfl⟩

/-- The writer's follow of a live slot of the canonical object of a current node
keeps the invariant. -/
theorem HInv.follow4_writer (hinv : Inv sp db k) (hls : LiveSub sp) (hm : EInv sp db S0 k m)
    (hh : HInv sp db S0 k m) {hp : Nat} {op : Obj V} (hop : m.obj? hp = some op)
    (hco : op.canonical = true) (hr : reachable sp db.P k op.node = true) {y : NodeId}
    (hy : y ∈ sp.live op.hist) : HInv sp db S0 k (m.follow4 sp S0 db.S hp y true).1 := by
  obtain ⟨n, hn, hhist, -, -⟩ := hm.cc hp op hop hco
  have hy' : y ∈ sp.live (n.hist.upTo k) := by
    rw [upTo_of_forall _ _ (hinv.times _ n hn), ← hhist]; exact hy
  obtain ⟨-, hyroot, ny, hny, hlt⟩ := hinv.reach_child hls hn hr hy'
  have hyw : written sp y = true := written_of_ne_root sp hyroot
  have hyne : y ≠ op.node := by
    intro he; rw [he, hn, Option.some.injEq] at hny; subst hny; omega
  rw [follow4_eq]
  cases hrc : m.reached4 sp S0 db.S hp y with
  | none => exact hh
  | some p =>
    obtain ⟨m1, h1⟩ := p
    simp only [↓reduceIte]
    obtain ⟨hop2, -, -⟩ := hm.reached4_frame hop hrc
    have hm2 := hm.reached4 hinv hrc
    obtain ⟨hh2, -, -, -⟩ := hh.reached4 hinv hm hrc
    have hsl2 : (op.setSlot y (Slot.mem h1)).slot? y = some (Slot.mem h1) := by
      obtain ⟨op0, sl, hop0, hsl0, -⟩ := reached4_cases hrc
      rw [hop, Option.some.injEq] at hop0; subst hop0
      rw [slot?_setSlot_of hsl0]; simp
    exact hh2.promote_step hinv hls hm2 hop2 hco hr hy hyw hyne hsl2

/-- The writer reaches one node of a path. -/
theorem HInv.reachOnPath4 (hinv : Inv sp db k) (hls : LiveSub sp) (hm : EInv sp db S0 k m)
    (hh : HInv sp db S0 k m) {path : List NodeId} (hpath : ∀ p ∈ path, reachable sp db.P k p = true)
    (x : NodeId) : HInv sp db S0 k (m.reachOnPath4 sp S0 db.S db.P (k + 1) path x) := by
  unfold Mem.reachOnPath4
  have hK1 : k + 1 - 1 = k := by omega
  cases hf : path.find? (fun p => match db.P.get? p, m.canonicalOf p with
      | some n, some _ => (sp.live (n.hist.upTo (k + 1 - 1))).contains x
      | _, _ => false) with
  | none => exact hh
  | some p =>
    simp only
    have hpp := List.find?_some hf
    have hpm := List.mem_of_find?_eq_some hf
    cases hnp : db.P.get? p with
    | none => rw [hnp] at hpp; simp at hpp
    | some np =>
      cases hcp : m.canonicalOf p with
      | none => rw [hnp, hcp] at hpp; simp at hpp
      | some hp =>
        simp only
        rw [hnp, hcp] at hpp
        simp only [hK1, List.contains_iff_mem] at hpp
        obtain ⟨op, hop, hco, hnode⟩ := hm.obj_of_canonicalOf hcp
        obtain ⟨nf, hnf, hh', -, -⟩ := hm.cc hp op hop hco
        rw [hnode, hnp, Option.some.injEq] at hnf
        subst hnf
        have hxop : x ∈ sp.live op.hist := by
          rw [hh', ← upTo_of_forall _ _ (hinv.times p np hnp)]; exact hpp
        exact hh.follow4_writer hinv hls hm hop hco (by rw [hnode]; exact hpath p hpm) hxop

/-- The writer reaches the nodes of its paths: the invariant is kept. -/
theorem HInv.reachPath4 (hinv : Inv sp db k) (hls : LiveSub sp) (hev : EvLogic sp db k)
    {path : List NodeId} (hpath : ∀ p ∈ path, reachable sp db.P k p = true) :
    ∀ (L : List NodeId) (m : Mem V), EInv sp db S0 k m → HInv sp db S0 k m →
      HInv sp db S0 k (L.foldl (Mem.reachOnPath4 sp S0 db.S db.P (k + 1) path) m) := by
  intro L
  induction L with
  | nil => intro m _ hh; exact hh
  | cons x L ih =>
    intro m hm hh
    simp only [List.foldl_cons]
    exact ih _ (hm.reachOnPath4_ok hinv hls hev hpath x).1 (hh.reachOnPath4 hinv hls hm hpath x)

end Walk

/-! ## The change and the writes -/

section Change

variable {sp : Spec V T} {db : DB V T} {S0 : Stream V T} {k : Nat} {m : Mem V} {c : Changes V}

/-- After the new nodes' objects: a canonical object named by the node table is
of its node. -/
theorem EInv.addNew_canon (hm : EInv sp db S0 k m) {m1 : Mem V} (haf : AddFacts m m1 c) {z : NodeId}
    {h' : Nat} (hc : m1.canonicalOf z = some h') :
    ∃ o, m1.obj? h' = some o ∧ o.node = z ∧ o.canonical = true := by
  by_cases hzn : z ∈ c.new.map (·.id)
  · obtain ⟨nn, hnn, rfl⟩ := List.mem_map.mp hzn
    obtain ⟨h2, -, hc2, ho2⟩ := haf.canNew nn hnn
    rw [hc, Option.some.injEq] at hc2
    subst hc2
    exact ⟨newObj nn, ho2, rfl, rfl⟩
  · rw [haf.canOld z hzn] at hc
    obtain ⟨o, ho, hco, hn⟩ := hm.obj_of_canonicalOf hc
    exact ⟨o, by rw [haf.old h' (lt_next_of_obj? hm.fresh ho)]; exact ho, hn, hco⟩

/-- The change keeps the invariant, for the times up to k: the new entries are
at k + 1, a new pointer's slot names its pointee's canonical object or copies a
slot that serializes the pointee's latest version, and the new nodes are not
reachable before. -/
theorem HInv.applyChange4 (hinv : Inv sp db k) (hls : LiveSub sp) (hm : EInv sp db S0 k m)
    (hh : HInv sp db S0 k m) (hstep : StepOK sp db.P (k + 1) c) :
    HInv sp db S0 k (m.applyChange4 sp db.P (k + 1) c) := by
  have haf := hm.addFacts hstep.distinct
  have hcf := changeFacts sp db.P (k + 1) c m
  have hk : m.KeepRead (m.applyChange4 sp db.P (k + 1) c) := by
    intro h o ho
    have hlt := lt_next_of_obj? hm.fresh ho
    rw [hcf.obj h, haf.old h hlt, ho, Option.map_some]
    obtain ⟨e1, -, -, -, e5, e6⟩ := updAll4_core sp db.P (k + 1) (c.new.foldl addNew m)
      (c.adds.filter (fun a => (c.new.foldl addNew m).canonicalOf a.1 == some h)) o
    exact ⟨_, rfl, e1, fun hc => by rw [e5]; exact hc, fun _ => e6⟩
  have hs : (m.applyChange4 sp db.P (k + 1) c).s = m.s := by rw [hcf.s, haf.s]
  apply hh.transfer hk hs
  intro h o3 ho3 hc3 t ht hrt z hz
  rw [hcf.obj h] at ho3
  obtain ⟨o1, ho1, rfl⟩ := Option.map_eq_some_iff.mp ho3
  obtain ⟨e1, -, -, e4, e5, -⟩ := updAll4_core sp db.P (k + 1) (c.new.foldl addNew m)
    (c.adds.filter (fun a => (c.new.foldl addNew m).canonicalOf a.1 == some h)) o1
  rcases haf.cls h o1 ho1 with ⟨-, hold⟩ | ⟨-, nn, hnn, hon, -⟩
  · have hc1 : o1.canonical = true := by rw [← e5]; exact hc3
    have hup : (updAll4 sp db.P (k + 1) (c.new.foldl addNew m)
        (c.adds.filter (fun a => (c.new.foldl addNew m).canonicalOf a.1 == some h)) o1).hist.upTo t =
        o1.hist.upTo t := by
      rw [e4, upTo_append, upTo_eq_nil (List.map (fun a => (⟨k + 1, a.2⟩ : Entry V))
        (c.adds.filter (fun a => (c.new.foldl addNew m).canonicalOf a.1 == some h))) t ?_, List.append_nil]
      intro e he
      obtain ⟨a, -, rfl⟩ := List.mem_map.mp he
      show t < k + 1
      omega
    rw [hup] at hz
    have hrt1 : reachable sp db.P t o1.node = true := by rw [← e1]; exact hrt
    rw [updAll4_slot]
    split
    · -- a pointer of a new entry
      unfold combo4
      cases hns : NS4 sp db.P (k + 1) (c.new.foldl addNew m) z with
      | none =>
        simp only [Option.none_or]
        exact Or.inl ⟨o1, hold, hc1, e1.symm, hup.symm, rfl⟩
      | some sl =>
        simp only [Option.some_or]
        right
        refine ⟨sl, rfl, ?_⟩
        rcases hm.NS4_good hinv hstep hns with ⟨h', rfl, hc'⟩ | ⟨-, hzD, -, href, h0, o0, ho0, hsl0⟩
        · obtain ⟨o'', ho'', hn'', hco''⟩ := hm.addNew_canon haf hc'
          obtain ⟨f1, -, -, -, f5, -⟩ := updAll4_core sp db.P (k + 1) (c.new.foldl addNew m)
            (c.adds.filter (fun a => (c.new.foldl addNew m).canonicalOf a.1 == some h')) o''
          exact ⟨_, by rw [hcf.obj h', ho'']; rfl, by rw [f1, hn''], Or.inl (by rw [f5, hco''])⟩
        · obtain ⟨hrz, hzr, hzw⟩ := hm.reach_child hinv hls hold hc1 hrt1 hz
          exact (hm.slotHist_clean hinv hls ho0 hsl0 hzD hzw ht hrz href (updAll4 sp db.P (k + 1)
            (c.new.foldl addNew m) (c.adds.filter (fun a => (c.new.foldl addNew m).canonicalOf a.1 == some h))
            o1).node).keep hk hs
    · exact Or.inl ⟨o1, hold, hc1, e1.symm, hup.symm, rfl⟩
  · -- a new node is not reachable at times up to k
    exfalso
    have := hstep.fresh nn hnn
    rw [e1, hon] at hrt
    obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp (Reach.isSome ((reachable_iff _ _ _ _).mp hrt))
    simp only [newObj] at hn
    rw [this] at hn; cases hn

/-- The writes keep the invariant: a slot changes only to a memory slot to its
pointee's canonical object, and a snapshot keeps its position. -/
theorem HInv.loops {D0 D1 : Dirty} {xs1 xs2 : List NodeId} {i : Nat} {m3 m6 : Mem V}
    (hh : HInv sp db S0 k m3) (htn : TableNode m3) (hfr : LoopsFrame D0 D1 xs1 xs2 i m3 m6) :
    HInv sp db S0 k m6 := by
  have hk : m3.KeepRead m6 := by
    intro h o ho
    obtain ⟨o6, ho6, e1, -, -, -, e5, -, -, e8⟩ := hfr.obj h o ho
    refine ⟨o6, ho6, e1, fun hc => by rw [e5]; exact hc, fun hc6 => ?_⟩
    have hc : o.canonical = false := by rw [← e5]; exact hc6
    refine (e8 ?_).1
    rintro ⟨-, hcan⟩
    obtain ⟨-, o', ho', hco'⟩ := (m3.canonicalOf_eq_some _ h).mp hcan
    rw [ho, Option.some.injEq] at ho'
    subst ho'
    rw [hc] at hco'; cases hco'
  apply hh.transfer hk hfr.s
  intro h o6 ho6 hc6 t ht hrt z hz
  obtain ⟨o3, ho3⟩ : ∃ o3, m3.obj? h = some o3 := by
    cases h3 : m3.obj? h with
    | none => rw [hfr.none h h3] at ho6; cases ho6
    | some o3 => exact ⟨o3, rfl⟩
  obtain ⟨o6', ho6', e1, -, -, e4, e5, hsl, -, -⟩ := hfr.obj h o3 ho3
  rw [ho6, Option.some.injEq] at ho6'
  subst ho6'
  rcases hsl z with hs | ⟨-, sl, h0, -, hc0, hs⟩
  · exact Or.inl ⟨o3, ho3, by rw [← e5]; exact hc6, e1.symm, by rw [e4], hs⟩
  · right
    refine ⟨Slot.mem h0, hs, ?_⟩
    have hc6' : m6.canonicalOf z = some h0 := by rw [hfr.canon]; exact hc0
    obtain ⟨ht0, o0, ho0, hco0⟩ := (m6.canonicalOf_eq_some z h0).mp hc6'
    have ht3 : m3.tableOf z = some h0 := by
      unfold Mem.tableOf at ht0 ⊢; rw [hfr.table] at ht0; exact ht0
    obtain ⟨o0', ho0', hn0'⟩ := htn z h0 ht3
    obtain ⟨o0'', ho0'', f1, -⟩ := hfr.obj h0 o0' ho0'
    rw [ho0, Option.some.injEq] at ho0''
    subst ho0''
    exact ⟨o0, ho0, by rw [f1, hn0'], Or.inl hco0⟩

end Change

/-! ## The next state -/

section Next

variable {sp : Spec V T} {al : Algo V T} {db : DB V T} {tr : T} {S0 : Stream V T} {k : Nat}

/-- After the writes, the invariant of the next state: at the new time k + 1
from INV-SLOT's live part; at earlier times as before, good versions staying
good, and INV-SLOT's second half either written away (the object's node taken,
so its slot names the pinned pointee's canonical object) or kept (both stay in
D with their indexes). -/
theorem HInv.next (hsp : SpecOK sp) (hinv : Inv sp db k)
    (hinv' : Inv sp (step sp al db tr) (k + 1)) {m3 m6 : Mem V}
    (ha : AInv sp db S0 k (parts sp al db tr).c (pathOf sp db.P (parts sp al db tr).c (k + 1)) m3)
    (hfr : LoopsFrame db.D (parts sp al db tr).D1 (dataIds sp al db tr) (parts sp al db tr).taken (k + 1)
      m3 m6)
    (hh6 : HInv sp db S0 k m6) (hm6' : EInv sp (step sp al db tr) S0 (k + 1) m6) :
    HInv sp (step sp al db tr) S0 (k + 1) m6 := by
  have hls : LiveSub sp := hsp.liveSub
  have hgrow : Grow db.P k (step sp al db tr).P := step_grow sp al db tr hinv.len
  have hsext : SExt db.S (step sp al db tr).S := Snew_ext sp al db tr
  intro h o ho hc t ht hr z hz
  by_cases htk : t = k + 1
  · subst htk
    obtain ⟨n, hn, hhist, -, -⟩ := hm6'.cc h o ho hc
    have hz' : z ∈ sp.live o.hist := by
      rw [hhist] at hz ⊢
      rw [upTo_of_forall _ _ (hinv'.times _ n hn)] at hz
      exact hz
    obtain ⟨sl, hsl, hli⟩ := hm6'.live h o ho hc hr z hz'
    refine ⟨sl, hsl, ?_⟩
    cases hzD : inD (step sp al db tr).D z with
    | true =>
      obtain ⟨h', rfl, hc'⟩ := hli.1 hzD
      obtain ⟨o', ho', hco', hn'⟩ := hm6'.obj_of_canonicalOf hc'
      exact ⟨o', ho', hn', Or.inl hco'⟩
    | false =>
      obtain ⟨hrz, -, hzw⟩ := hm6'.reach_child hinv' hls ho hc hr hz
      exact hm6'.slotHist_clean hinv' hls ho hsl hzD hzw (Nat.le_refl _) hrz (hli.2 hzD) o.node
  · have ht' : t ≤ k := by omega
    have hr0 : reachable sp db.P t o.node = true := by
      rw [reachable_iff] at hr ⊢
      exact reach_of_grow_back hls hinv.ptrs hinv.rootIn hgrow ht' hr
    obtain ⟨sl, hsl, hsh⟩ := hh6 h o ho hc t ht' hr0 z hz
    refine ⟨sl, hsl, ?_⟩
    cases sl with
    | mem h' =>
      obtain ⟨o', ho', hn', hc'⟩ := hsh
      refine ⟨o', ho', hn', ?_⟩
      rcases hc' with hc' | ⟨r, w, hp, hw, hg⟩
      · exact Or.inl hc'
      · exact Or.inr ⟨r, w, hp, hsext.versionAt hw, good_mono' sp hsext hgrow ht' hg⟩
    | stream r =>
      rcases hsh with ⟨r', w, e1, e2, e3⟩ | ⟨hzD, -, a, b, ha', hb, hab⟩
      · exact Or.inl ⟨r', w, e1, hsext.versionAt e2, good_mono' sp hsext hgrow ht' e3⟩
      · obtain ⟨o3, ho3⟩ : ∃ o3, m3.obj? h = some o3 := by
          cases h3 : m3.obj? h with
          | none => rw [hfr.none h h3] at ho; cases ho
          | some o3 => exact ⟨o3, rfl⟩
        · obtain ⟨o6, ho6, e1, -, -, -, e5, hslr, hpin, -⟩ := hfr.obj h o3 ho3
          rw [ho, Option.some.injEq] at ho6
          subst ho6
          have hxa := mem_of_dOf ha'
          have hzb := mem_of_dOf hb
          by_cases has : a ≤ (parts sp al db tr).s
          · -- o's node is taken: its slot for z, pinned, names z's canonical object
            exfalso
            have hxt : o3.node ∈ (parts sp al db tr).taken :=
              (step_taken_mem sp al db tr _).mpr ⟨a, (step_D1_mem sp al db tr hinv.len _).mpr
                (Or.inl (by rw [← e1]; exact hxa)), has⟩
            have hc3 : o3.canonical = true := by rw [← e5]; exact hc
            have hcan3 : m3.canonicalOf o3.node = some h := ha.canonicalOf_of' ho3 hc3
            obtain ⟨h0, hc0⟩ := Option.isSome_iff_exists.mp (ha.canon z (Or.inl hzD))
            have hzD1 : inD (parts sp al db tr).D1 z = true :=
              (inD_iff _ _).mpr ⟨b, (step_D1_mem sp al db tr hinv.len _).mpr (Or.inl hzb)⟩
            obtain ⟨sl3, hsl3⟩ : ∃ sl3, o3.slot? z = some sl3 := by
              rcases hslr z with hs | ⟨-, sl3, -, hs3, -, -⟩
              · exact ⟨_, by rw [← hs]; exact hsl⟩
              · exact ⟨sl3, hs3⟩
            have := hpin ⟨hxt, hcan3⟩ z sl3 h0 hsl3 hzD1 hc0
            rw [hsl] at this; cases this
          · -- both stay in D, with their indexes
            right
            have hxD2 : (o.node, a) ∈ (parts sp al db tr).D2 :=
              (step_D2_mem sp al db tr _).mpr ⟨(step_D1_mem sp al db tr hinv.len _).mpr (Or.inl hxa), by
                simp only; omega⟩
            have hzD2 : (z, b) ∈ (parts sp al db tr).D2 :=
              (step_D2_mem sp al db tr _).mpr ⟨(step_D1_mem sp al db tr hinv.len _).mpr (Or.inl hzb), by
                simp only; omega⟩
            have hxD' : (o.node, a) ∈ (step sp al db tr).D := by
              show _ ∈ (parts sp al db tr).r7.1
              rw [(step_r7_shape sp al db tr hinv.len).1]; exact List.mem_append_left _ hxD2
            have hzD' : (z, b) ∈ (step sp al db tr).D := by
              show _ ∈ (parts sp al db tr).r7.1
              rw [(step_r7_shape sp al db tr hinv.len).1]; exact List.mem_append_left _ hzD2
            exact ⟨(inD_iff _ _).mpr ⟨b, hzD'⟩, (inD_iff _ _).mpr ⟨a, hxD'⟩, a, b,
              dOf_of_mem hinv'.dNodup hxD', dOf_of_mem hinv'.dNodup hzD', hab⟩

/-- One transaction of the physical writer keeps the invariant for reads at
earlier times. -/
theorem HInv.evictTrans_ok (hsp : SpecOK sp) (hinv : Inv sp db k) (hmk : al.mark = true)
    {m : Mem V} (hm : EInv sp db S0 k m) (hh : HInv sp db S0 k m) (hev : EvLogic sp db k)
    (hstep : StepOK sp db.P (k + 1) (parts sp al db tr).c) (hphys : PhysStep sp db.P (k + 1) (parts sp al db tr).c)
    (hcopy : CopyStep sp db.P (k + 1) (parts sp al db tr).c) (htree : treeAt sp db.P k)
    (hinv' : Inv sp (step sp al db tr) (k + 1)) (hev' : EvLogic sp (step sp al db tr) (k + 1)) :
    HInv sp (step sp al db tr) S0 (k + 1) (evictTrans sp al S0 db m tr).2 := by
  have hls : LiveSub sp := hsp.liveSub
  have hlen := hinv.len
  have hK1 : k + 1 - 1 = k := by omega
  obtain ⟨hm1, hv⟩ := hm.view4_ok hinv hls hev
  have hh1 : HInv sp db S0 k (m.view4 sp S0 db.S k).1 := hh.read4 hinv hm k
  have hc : sp.exec tr db.S.length (m.view4 sp S0 db.S (db.S.length - 1)).2 = (parts sp al db tr).c := by
    rw [hlen, hK1, hv, parts_c, hlen, hK1]
  rw [evictTrans_eq, hc, evictAfter_eq]
  have hm1' : EInv sp db S0 k (m.view4 sp S0 db.S (db.S.length - 1)).1 := by rw [hlen, hK1]; exact hm1
  have hh1' : HInv sp db S0 k (m.view4 sp S0 db.S (db.S.length - 1)).1 := by rw [hlen, hK1]; exact hh1
  generalize (m.view4 sp S0 db.S (db.S.length - 1)).1 = m1 at hm1' hh1' ⊢
  -- The writer's paths.
  have hpr : ∀ p ∈ pathOf sp db.P (parts sp al db tr).c (k + 1), reachable sp db.P k p = true := by
    intro p hp; have := (mem_pathOf hp).1; rw [hK1] at this; exact this
  have hparent : ∀ x ∈ pathOf sp db.P (parts sp al db tr).c (k + 1), x ≠ SIS.root →
      ∃ p ∈ pathOf sp db.P (parts sp al db tr).c (k + 1), ∃ np nx, db.P.get? p = some np ∧
        db.P.get? x = some nx ∧ nx.level < np.level ∧ x ∈ sp.live (np.hist.upTo k) := by
    intro x hx hxr
    have hrx := (mem_pathOf hx).1
    rw [hK1] at hrx
    obtain ⟨p, np, nx, hrp, hnp, hnx, hlt, hxl⟩ := reach_parent hrx hxr
    refine ⟨p, pathOf_parent hx (by rw [hK1]; exact hrp) hnp (by rw [hK1]; exact hxl) hnx hlt, np, nx, hnp, hnx,
      hlt, hxl⟩
  have hpnd : (pathOf sp db.P (parts sp al db tr).c (k + 1)).Nodup := by
    unfold pathOf; exact nodup_filter (nodup_eraseDups _) _
  have hsorted := pairwise_byLevelDesc db.P (pathOf sp db.P (parts sp al db tr).c (k + 1))
  obtain ⟨hm2, hpd⟩ := EInv.reachPath4_ok (S0 := S0) hinv hls hev hpr hparent
    ((pathOf sp db.P (parts sp al db tr).c (k + 1)).mergeSort (fun a b => decide (lev db.P b ≤ lev db.P a))) []
    m1 hm1' (fun a ha => by cases ha)
    (fun x => by rw [List.nil_append]; exact (List.mergeSort_perm _ _).mem_iff)
    (by rw [List.nil_append]; exact (List.mergeSort_perm _ _).nodup_iff.mpr hpnd)
    (by rw [List.nil_append]; exact hsorted)
  have hh2 := HInv.reachPath4 (S0 := S0) hinv hls hev hpr
    ((pathOf sp db.P (parts sp al db tr).c (k + 1)).mergeSort (fun a b => decide (lev db.P b ≤ lev db.P a)))
    m1 hm1' hh1'
  -- The change.
  have ha := hm2.applyChange4_ok hinv hls hpd hstep hphys hcopy htree
  have hh3 := hh2.applyChange4 hinv hls hm2 hstep
  have hpre : preWrite sp S0 db (parts sp al db tr).c m1 =
      (((pathOf sp db.P (parts sp al db tr).c (k + 1)).mergeSort (fun a b => decide (lev db.P b ≤ lev db.P a))).foldl
        (Mem.reachOnPath4 sp S0 db.S db.P (k + 1) (pathOf sp db.P (parts sp al db tr).c (k + 1))) m1).applyChange4
        sp db.P (k + 1) (parts sp al db tr).c := by
    unfold preWrite; rw [hlen]; rfl
  rw [hpre, hlen]
  generalize (((pathOf sp db.P (parts sp al db tr).c (k + 1)).mergeSort
    (fun a b => decide (lev db.P b ≤ lev db.P a))).foldl
      (Mem.reachOnPath4 sp S0 db.S db.P (k + 1) (pathOf sp db.P (parts sp al db tr).c (k + 1))) m1).applyChange4
      sp db.P (k + 1) (parts sp al db tr).c = m3 at ha hh3 ⊢
  -- The writes.
  obtain ⟨e1, -, -, e4⟩ := ha.loops_vs hsp hinv hmk hstep hinv'
  have hdata : ((parts sp al db tr).c.new.filter (·.isData)).map (·.id) = dataIds sp al db tr := rfl
  rw [hdata, e1, ← parts_D1Of, ← parts_takenOf]
  have hdnd : (dataIds sp al db tr).Nodup := (List.Sublist.map _ List.filter_sublist).nodup hstep.distinct
  have hdisj : ∀ x ∈ dataIds sp al db tr, x ∉ (parts sp al db tr).taken := by
    intro x hx hxt
    obtain ⟨d, hxd, -⟩ := step_taken_inD (al := al) (tr := tr) hinv hxt
    obtain ⟨hnone, -⟩ := step_dataIds_spec sp al db tr hinv hstep hx
    have := hinv.dIndex (x, d) hxd
    simp [isIndex, hnone] at this
  have hfr := loopsFrame sp S0 db.D (parts sp al db tr).D1 (k + 1) (dataIds sp al db tr) (parts sp al db tr).taken
    m3 hdnd (step_taken_nodup sp al db tr hinv) ha.tbl hdisj
  have hm6 := ha.final_ok hsp hinv hmk hstep hinv' hev' hfr e4
  exact (hh3.loops ha.tbl hfr).next hsp hinv hinv' ha hfr hm6

end Next

end SIS
