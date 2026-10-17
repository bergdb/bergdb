/-
Proofs for stage 2 (bergdb item 001, WP E5), part 2: restarts with eviction
(T2-C, and T-READ with restarts). The Level 4 startup from the stream after
T(k) gives a memory with the invariant and with the invariant for reads at
earlier times (`einv_hinv_startup`): its positions are the latest records, and
rule 4 links the pinned objects' slots to the nodes of D. The physical writer
depends on P only through its nodes, so a transaction from the logical
startup's state, which has the run's nodes, gives the run's record and D and
the same memory (`evictTrans_congr`); so a run with restarts keeps both
invariants (`evictInvR_all`).
-/
import SIS.Proof.EvictRerun

set_option linter.unusedSectionVars false

namespace SIS

variable {V T : Type} [DecidableEq V]

/-! ## The invariant after the Level 4 startup (T2-C) -/

theorem Mem.sectionPos_obj? (m : Mem V) (S : Stream V T) (h : Nat) :
    (m.sectionPos S).obj? h = (m.obj? h).map (fun o =>
      if !o.canonical then o else match newest S m.s o.node with
        | some w => { o with pos := some w.recNo }
        | none => o) := by
  unfold Mem.sectionPos Mem.obj?
  simp only
  rw [lookup_map_key _ (fun q => by
    cases q.2.canonical
    · simp
    · cases newest S m.s q.2.node <;> simp) h m.objs]
  congr 1
  funext o
  cases o.canonical
  · simp
  · cases newest S m.s o.node <;> simp

/-- Rule 4 on a pinned object: its stream slot for y becomes a memory slot to y's
canonical object, if y has one. -/
theorem linkObjD_pinned (m : Mem V) (D : Dirty) {h : Nat} {o : Obj V}
    (hp : o.canonical = true ∧ (inD D o.node = true ∨ h = m.root)) {y : NodeId} {r : Option Nat}
    (hs : o.slot? y = some (Slot.stream r)) {h0 : Nat} (hc : m.canonicalOf y = some h0) :
    (linkObjD m D h o).slot? y = some (Slot.mem h0) := by
  unfold linkObjD
  have : (!(o.canonical && (inD D o.node || h == m.root))) = false := by
    rcases hp with ⟨h1, h2 | h2⟩
    · simp [h1, h2]
    · simp [h1, h2]
  rw [this]
  simp only [Bool.false_eq_true, ↓reduceIte]
  unfold Obj.slot? at hs ⊢
  simp only
  rw [lookup_map_key (linkSlot m) (linkSlot_fst m) y o.slots, hs]
  simp [linkSlot, hc]

section Startup

variable {sp : Spec V T} {al : Algo V T} {ts : List T}

/-- T2-C's startup: the Level 4 startup from the stream after T(k) gives a memory
with the invariant, and with the invariant for reads at earlier times. -/
theorem einv_hinv_startup (hok : RunOK sp al ts) (hph : PhysRunOK sp al ts) (hj : al.stillDirty = javaTest sp)
    (hmk : al.mark = true) (hev : EvictRunOK sp al ts) {k : Nat} (hk : k ≤ ts.length) :
    EInv sp (st sp al ts k) (st sp al ts k).S k (evictStartup sp (st sp al ts k).S) ∧
      HInv sp (st sp al ts k) (st sp al ts k).S k (evictStartup sp (st sp al ts k).S) := by
  have hst : AlgOK sp al := algOK_of sp al (Or.inl hj)
  have hls : LiveSub sp := hok.1.liveSub
  have hinv := inv_st sp al ts hok hst k hk
  have hlog := evLogic_st sp al ts hok hj hmk hev k hk
  have hkk := kctx_st sp al ts hok hj (Nat.le_refl k) hk
  obtain ⟨hr, hm⟩ := rinv_lazyStartup hok hph hj hmk hev hk
  have hnd0 := tblND_lazyStartup sp (st sp al ts k).S
  have hD : (startup sp (st sp al ts k).S).D = (st sp al ts k).D := (T1_strong sp al ts hok hst hk).2
  unfold evictStartup
  rw [hD]
  generalize hm0 : lazyStartup sp (st sp al ts k).S = m0 at hr hm hnd0
  have hs0 : m0.s = lastSp (st sp al ts k).S := hm.sEq
  -- The memories after the positions (m1) and after rule 4 (m2), by lookup.
  have hobj1 := Mem.sectionPos_obj? m0 (st sp al ts k).S
  have htab1 : ∀ y, (m0.sectionPos (st sp al ts k).S).tableOf y = m0.tableOf y := fun _ => rfl
  have hobj2 := Mem.linkD_obj? (m0.sectionPos (st sp al ts k).S) (st sp al ts k).D
  have htab2 : ∀ y, ((m0.sectionPos (st sp al ts k).S).linkD (st sp al ts k).D).tableOf y = m0.tableOf y :=
    fun _ => rfl
  have hroot2 : ((m0.sectionPos (st sp al ts k).S).linkD (st sp al ts k).D).root = m0.root := rfl
  have hs2 : ((m0.sectionPos (st sp al ts k).S).linkD (st sp al ts k).D).s = m0.s := rfl
  -- canonicalOf is m0's throughout
  have hcan1 : ∀ y, (m0.sectionPos (st sp al ts k).S).canonicalOf y = m0.canonicalOf y := by
    intro y
    unfold Mem.canonicalOf
    rw [htab1]
    cases m0.tableOf y with
    | none => rfl
    | some h =>
      simp only
      rw [hobj1]
      cases ho : m0.obj? h with
      | none => rfl
      | some o =>
        simp only [Option.map_some]
        cases hc : o.canonical
        · simp [hc]
        · cases newest (st sp al ts k).S m0.s o.node <;> simp [hc]
  have hcan2 : ∀ y, ((m0.sectionPos (st sp al ts k).S).linkD (st sp al ts k).D).canonicalOf y =
      m0.canonicalOf y := by
    intro y
    unfold Mem.canonicalOf
    rw [htab2]
    cases ht : m0.tableOf y with
    | none => rfl
    | some h =>
      simp only
      rw [hobj2, hobj1]
      cases ho : m0.obj? h with
      | none => rfl
      | some o =>
        simp only [Option.map_some]
        have hc1 : ∀ o1 : Obj V, (linkObjD (m0.sectionPos (st sp al ts k).S) (st sp al ts k).D h o1).canonical =
            o1.canonical := fun o1 => congrArg (fun c => c.2.2.2.2.1) (linkObjD_core _ _ h o1)
        rw [hc1]
        cases hc : o.canonical
        · simp [hc]
        · cases newest (st sp al ts k).S m0.s o.node <;> simp [hc]
  -- What an object of m2 is.
  have hshape : ∀ h o2, ((m0.sectionPos (st sp al ts k).S).linkD (st sp al ts k).D).obj? h = some o2 →
      ∃ o0, m0.obj? h = some o0 ∧ o2.node = o0.node ∧ o2.hist = o0.hist ∧ o2.level = o0.level ∧
        o2.isData = o0.isData ∧ o2.canonical = true ∧
        o2.pos = ((st sp al ts k).S.lv o0.node).map (·.recNo) ∧
        (∀ y, o2.slot? y = o0.slot? y ∨ ∃ sl h0, o0.slot? y = some sl ∧ o2.slot? y = some (Slot.mem h0) ∧
          m0.canonicalOf y = some h0) ∧
        ((inD (st sp al ts k).D o0.node = true ∨ h = m0.root) → ∀ y r h0, o0.slot? y = some (Slot.stream r) →
          m0.canonicalOf y = some h0 → o2.slot? y = some (Slot.mem h0)) := by
    intro h o2 ho2
    rw [hobj2, hobj1] at ho2
    obtain ⟨o1, ho1, rfl⟩ := Option.map_eq_some_iff.mp ho2
    obtain ⟨o0, ho0, rfl⟩ := Option.map_eq_some_iff.mp ho1
    have hc0 := hr.canon h o0 ho0
    -- the object after the positions
    obtain ⟨p1, hp1, hpos1⟩ : ∃ p1, (if !o0.canonical then o0 else match newest (st sp al ts k).S m0.s o0.node with
        | some w => { o0 with pos := some w.recNo }
        | none => o0) = { o0 with pos := p1 } ∧ p1 = ((st sp al ts k).S.lv o0.node).map (·.recNo) := by
      cases hn : newest (st sp al ts k).S m0.s o0.node with
      | some w =>
        refine ⟨some w.recNo, ?_, ?_⟩
        · split
          · rename_i hc; simp [hc0] at hc
          · rfl
        · rw [hs0] at hn; rw [newest_lv hn]; rfl
      | none =>
        refine ⟨o0.pos, ?_, hr.pos h o0 ho0 (by rw [← hs0]; exact hn)⟩
        show _ = o0
        split <;> rfl
    rw [hp1]
    have hcore := linkObjD_core (m0.sectionPos (st sp al ts k).S) (st sp al ts k).D h { o0 with pos := p1 }
    simp only [Obj.core, Prod.mk.injEq] at hcore
    obtain ⟨c1, c2, c3, c4, c5, c6⟩ := hcore
    refine ⟨o0, ho0, c1, c4, c2, c3, by rw [c5]; exact hc0, by rw [c6]; exact hpos1, fun y => ?_, fun hpin y r h0 hsl hc => ?_⟩
    · rcases linkObjD_slot (m0.sectionPos (st sp al ts k).S) (st sp al ts k).D h { o0 with pos := p1 } y with
        he | ⟨sl, h0, hs1, hs2, hcy⟩
      · exact Or.inl he
      · exact Or.inr ⟨sl, h0, hs1, hs2, by rw [← hcan1]; exact hcy⟩
    · exact linkObjD_pinned (o := { o0 with pos := p1 }) (m0.sectionPos (st sp al ts k).S) (st sp al ts k).D
        ⟨hc0, hpin⟩ hsl
        (by rw [hcan1]; exact hc)
  have hback : ∀ h o0, m0.obj? h = some o0 →
      ∃ o2, ((m0.sectionPos (st sp al ts k).S).linkD (st sp al ts k).D).obj? h = some o2 := by
    intro h o0 ho0
    rw [hobj2, hobj1, ho0]
    exact ⟨_, rfl⟩
  -- A memory slot of m2 names an object of its pointee, canonical, at its latest version.
  have hmemslot : ∀ h o2 y h', ((m0.sectionPos (st sp al ts k).S).linkD (st sp al ts k).D).obj? h = some o2 →
      o2.slot? y = some (Slot.mem h') → ∃ o', ((m0.sectionPos (st sp al ts k).S).linkD
        (st sp al ts k).D).obj? h' = some o' ∧ o'.node = y ∧ m0.canonicalOf y = some h' ∧
        o'.pos = ((st sp al ts k).S.lv y).map (·.recNo) := by
    intro h o2 y h' ho2 hsl
    obtain ⟨o0, ho0, -, -, -, -, -, -, hsl', -⟩ := hshape h o2 ho2
    have hc' : m0.canonicalOf y = some h' := by
      rcases hsl' y with he | ⟨sl, h0, -, hs2, hcy⟩
      · rw [he] at hsl
        obtain ⟨o', ho', hn'⟩ := hr.memNode h o0 ho0 y h' hsl
        obtain ⟨ht', -⟩ := hm.canon h' o' ho' (hr.canon h' o' ho')
        rw [hn'] at ht'
        exact (m0.canonicalOf_eq_some y h').mpr ⟨ht', o', ho', hr.canon h' o' ho'⟩
      · rw [hs2, Option.some.injEq, Slot.mem.injEq] at hsl
        rw [← hsl]; exact hcy
    obtain ⟨ht', o', ho', -⟩ := (m0.canonicalOf_eq_some y h').mp hc'
    obtain ⟨o2', ho2'⟩ := hback h' o' ho'
    obtain ⟨o0', ho0', e1, -, -, -, -, e7, -, -⟩ := hshape h' o2' ho2'
    rw [ho', Option.some.injEq] at ho0'
    subst ho0'
    obtain ⟨o'', ho'', hn''⟩ := hm.tbl y h' ht'
    rw [ho', Option.some.injEq] at ho''
    subst ho''
    exact ⟨o2', ho2', by rw [e1, hn''], hc', by rw [e7, hn'']⟩
  -- A slot of m2 for y not in D serializes y's latest version.
  have hser : ∀ h o2 y sl, ((m0.sectionPos (st sp al ts k).S).linkD (st sp al ts k).D).obj? h = some o2 →
      o2.slot? y = some sl → slotRefOf (st sp al ts k).S ((m0.sectionPos (st sp al ts k).S).linkD
        (st sp al ts k).D) y sl = ((st sp al ts k).S.lv y).map (·.recNo) := by
    intro h o2 y sl ho2 hsl
    cases sl with
    | mem h' =>
      obtain ⟨o', ho', -, -, hpos'⟩ := hmemslot h o2 y h' ho2 hsl
      simp only [slotRefOf, ho', Option.bind_some]
      exact hpos'
    | stream r =>
      obtain ⟨o0, ho0, -, -, -, -, -, -, hsl', -⟩ := hshape h o2 ho2
      have hs0' : o0.slot? y = some (Slot.stream r) := by
        rcases hsl' y with he | ⟨sl, h0, -, hs2, -⟩
        · rw [← he]; exact hsl
        · rw [hs2] at hsl; cases hsl
      simp only [slotRefOf]
      rw [hs2, hs0]
      exact hr.fresh h o0 ho0 y r hs0'
  -- A node of D has a canonical object.
  have hdc : ∀ y, inD (st sp al ts k).D y = true → ∃ h0, m0.canonicalOf y = some h0 := by
    intro y hy
    obtain ⟨d, hd⟩ := (inD_iff _ _).mp hy
    have hsd : lastSp (st sp al ts k).S < d := by
      rcases Nat.lt_or_ge (lastSp (st sp al ts k).S) d with h1 | h1
      · exact h1
      · obtain ⟨r, w, hkr, hw⟩ := hkk.dLater y d hd h1
        have := versionAt_ge_length (S := (st sp al ts k).S) (r := r) (by rw [hinv.len]; omega) y
        rw [hw] at this; cases this
    obtain ⟨R, hR, hyR, hdk⟩ := hkk.dSec y d hd hsd
    have := hm.coverGd d R y hsd hdk hR hyR
    cases hc : m0.canonicalOf y with
    | none => exact absurd hc this
    | some h0 => exact ⟨h0, rfl⟩
  -- A stream slot of m2 for a node of D is not in a pinned object.
  have hpinned : ∀ h o2 y r, ((m0.sectionPos (st sp al ts k).S).linkD (st sp al ts k).D).obj? h = some o2 →
      o2.slot? y = some (Slot.stream r) → inD (st sp al ts k).D y = true →
      inD (st sp al ts k).D o2.node = false ∧ h ≠ m0.root := by
    intro h o2 y r ho2 hsl hy
    obtain ⟨o0, ho0, e1, -, -, -, -, -, hsl', hpin⟩ := hshape h o2 ho2
    have hs0' : o0.slot? y = some (Slot.stream r) := by
      rcases hsl' y with he | ⟨sl, h0, -, hs2, -⟩
      · rw [← he]; exact hsl
      · rw [hs2] at hsl; cases hsl
    obtain ⟨h0, hc⟩ := hdc y hy
    have hno : ¬ (inD (st sp al ts k).D o0.node = true ∨ h = m0.root) := by
      intro hp
      rw [hpin hp y r h0 hs0' hc] at hsl
      cases hsl
    rw [e1]
    refine ⟨?_, fun he => hno (Or.inr he)⟩
    cases hx : inD (st sp al ts k).D o0.node
    · rfl
    · exact absurd (Or.inl hx) hno
  -- An object's table entry and its node's whole history (CC).
  have hcc : ∀ h o2, ((m0.sectionPos (st sp al ts k).S).linkD (st sp al ts k).D).obj? h = some o2 →
      m0.tableOf o2.node = some h ∧ ∃ n, (st sp al ts k).P.get? o2.node = some n ∧ o2.hist = n.hist ∧
        o2.level = n.level ∧ o2.isData = n.isData := by
    intro h o2 ho2
    obtain ⟨o0, ho0, e1, e2, e3, e4, -, -, -, -⟩ := hshape h o2 ho2
    obtain ⟨ht, ⟨n, hn, hh, hl, hd⟩, -⟩ := hm.canon h o0 ho0 (hr.canon h o0 ho0)
    rw [e1, e2, e3, e4]
    refine ⟨ht, n, hn, ?_, hl, hd⟩
    rw [hh]
    exact upTo_of_forall _ _ (hinv.times _ n hn)
  -- A slot for each pointee.
  have hslot : ∀ h o2 y, ((m0.sectionPos (st sp al ts k).S).linkD (st sp al ts k).D).obj? h = some o2 →
      y ∈ pointees sp o2.hist → ∃ sl, o2.slot? y = some sl := by
    intro h o2 y ho2 hy
    obtain ⟨o0, ho0, -, e2, -, -, -, -, hsl', -⟩ := hshape h o2 ho2
    have hy0 : y ∈ pointees sp o0.hist := by rw [← e2]; exact hy
    obtain ⟨sl0, hsl0⟩ := Option.isSome_iff_exists.mp (hr.slotsAll h o0 ho0 y hy0)
    rcases hsl' y with he | ⟨sl, h0, -, hs2, -⟩
    · exact ⟨sl0, by rw [he, hsl0]⟩
    · exact ⟨_, hs2⟩
  refine ⟨⟨hinv.len, List.prefix_refl _, hs0, ?_, ?_, ?_, hnd0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · -- fresh
    intro h hh
    rw [hobj2, hobj1, hm.fresh h hh]; rfl
  · -- objNodup
    rw [Mem.linkD_keys, Mem.sectionPos_keys]; exact hm.nodup
  · -- root
    obtain ⟨-, o0, ho0, -, hn0⟩ := hm.root
    obtain ⟨o2, ho2⟩ := hback m0.root o0 ho0
    obtain ⟨o0', ho0', e1, -, -, -, e5, -⟩ := hshape m0.root o2 ho2
    rw [ho0, Option.some.injEq] at ho0'
    subst ho0'
    exact ⟨o2, ho2, e5, by rw [e1, hn0]⟩
  · -- tbl
    intro y h ht
    obtain ⟨o0, ho0, hn0⟩ := hm.tbl y h ht
    obtain ⟨o2, ho2⟩ := hback h o0 ho0
    obtain ⟨o0', ho0', e1, -⟩ := hshape h o2 ho2
    rw [ho0, Option.some.injEq] at ho0'
    subst ho0'
    exact ⟨o2, ho2, by rw [e1, hn0]⟩
  · -- slotsNode
    intro h o2 ho2 y h' hsl
    obtain ⟨o', ho', hn', -⟩ := hmemslot h o2 y h' ho2 hsl
    exact ⟨o', ho', hn'⟩
  · -- tblCanon
    intro y h ht
    obtain ⟨o0, ho0, -⟩ := hm.tbl y h ht
    obtain ⟨o2, ho2⟩ := hback h o0 ho0
    obtain ⟨-, -, -, -, -, -, e5, -⟩ := hshape h o2 ho2
    exact ⟨o2, ho2, e5⟩
  · -- canonTbl
    intro h o2 ho2 _
    exact (hcc h o2 ho2).1
  · -- cc
    intro h o2 ho2 _
    exact (hcc h o2 ho2).2
  · -- pos
    intro z h o2 hz ho2
    rw [lv_building]
    simp only [List.find?_nil, Option.none_or]
    obtain ⟨o0, ho0, -, -, -, -, -, e6, -⟩ := hshape h o2 ho2
    rw [hcan2] at hz
    obtain ⟨ht, -⟩ := (Mem.canonicalOf_eq_some _ z h).mp hz
    obtain ⟨o', ho', hn'⟩ := hm.tbl z h ht
    rw [ho0, Option.some.injEq] at ho'
    subst ho'
    rw [e6, hn']
  · -- dCanon
    intro y hy
    rw [hcan2]
    obtain ⟨h0, hc⟩ := hdc y hy
    rw [hc]; rfl
  · -- snap: every object is canonical
    intro h o2 ho2 hc
    obtain ⟨-, -, -, -, -, -, e5, -⟩ := hshape h o2 ho2
    rw [e5] at hc; cases hc
  · -- slots
    intro h o2 ho2 hrel y hy
    obtain ⟨sl, hsl⟩ := hslot h o2 y ho2 hy
    refine ⟨sl, hsl, ?_⟩
    unfold SlotInv
    refine ⟨fun _ => hser h o2 y sl ho2 hsl, fun hyD => Or.inl ?_⟩
    cases sl with
    | mem h' =>
      obtain ⟨-, -, -, hc', -⟩ := hmemslot h o2 y h' ho2 hsl
      exact ⟨h', rfl, by rw [hcan2]; exact hc'⟩
    | stream r =>
      exfalso
      obtain ⟨hxD, -⟩ := hpinned h o2 y r ho2 hsl hyD
      obtain ⟨-, hw, hreach⟩ := hrel
      rcases hreach with hrk | hxD'
      · obtain ⟨-, n, hn, hh, -⟩ := hcc h o2 ho2
        have := (hlog.clean o2.node n hw hrk hn hxD y (by rw [← hh]; exact hy)).1
        rw [hyD] at this; cases this
      · rw [hxD] at hxD'; cases hxD'
  · -- live
    intro h o2 ho2 _ hrk y hy
    obtain ⟨sl, hsl⟩ := hslot h o2 y ho2 (mem_pointees_of_live' hls hy)
    refine ⟨sl, hsl, ?_⟩
    unfold LiveInv
    refine ⟨fun hyD => ?_, fun _ => hser h o2 y sl ho2 hsl⟩
    cases sl with
    | mem h' =>
      obtain ⟨-, -, -, hc', -⟩ := hmemslot h o2 y h' ho2 hsl
      exact ⟨h', rfl, by rw [hcan2]; exact hc'⟩
    | stream r =>
      exfalso
      obtain ⟨hxD, hne⟩ := hpinned h o2 y r ho2 hsl hyD
      obtain ⟨ht, n, hn, hh, -⟩ := hcc h o2 ho2
      by_cases hxr : o2.node = SIS.root
      · apply hne
        rw [hxr] at ht
        obtain ⟨ht0, -⟩ := hm.root
        rw [ht0, Option.some.injEq] at ht
        exact ht.symm
      · have hw : written sp o2.node = true := written_of_ne_root sp hxr
        have hyn : y ∈ sp.live (n.hist.upTo k) := by
          rw [upTo_of_forall _ _ (hinv.times _ n hn), ← hh]; exact hy
        obtain ⟨e, he, hye⟩ := hls _ _ hy
        obtain ⟨m', hm', hlt⟩ := hinv.ptrs o2.node n hn e (by rw [← hh]; exact he) y hye
        have hyr : y ∈ reachFrom sp (st sp al ts k).P k o2.node n :=
          reachFrom_child_sub sp hyn hm' hlt y (self_mem_reachFrom sp _ k y m')
        rw [hlog.closed o2.node n y hw hrk hn hyD hyr] at hxD
        cases hxD
  · -- HInv: every object is canonical; a memory slot names a canonical object of
    -- its pointee, and a stream slot its pointee's latest version, which is good
    -- for t: the pointee is clean, or its parent is (and lemma M)
    intro h o2 ho2 _ t ht hrt y hy
    obtain ⟨ht2, n, hn, hh, -⟩ := hcc h o2 ho2
    obtain ⟨sl, hsl⟩ := hslot h o2 y ho2 (mem_pointees_of_live hls hy)
    refine ⟨sl, hsl, ?_⟩
    obtain ⟨e, he, hye⟩ := hls _ _ hy
    have he' : e ∈ n.hist := by rw [← hh]; exact (mem_upTo.mp he).1
    have hyr : y ≠ SIS.root := hinv.ptr_ne_root hn he' hye
    cases sl with
    | mem h' =>
      obtain ⟨o', ho', hn', -, -⟩ := hmemslot h o2 y h' ho2 hsl
      obtain ⟨-, -, -, -, -, -, e5, -⟩ := hshape h' o' ho'
      exact ⟨o', ho', hn', Or.inl e5⟩
    | stream r =>
      left
      have hs := hser h o2 y (Slot.stream r) ho2 hsl
      simp only [slotRefOf] at hs
      have hry : reachable sp (st sp al ts k).P t y = true := by
        rw [reachable_iff] at hrt ⊢
        obtain ⟨m', hm', hlt⟩ := hinv.ptrs o2.node n hn e he' y hye
        exact Reach.child hrt hn (by rw [← hh]; exact hy) hm' hlt
      obtain ⟨w, hw, hg⟩ : ∃ w, (st sp al ts k).S.lv y = some w ∧
          good sp (st sp al ts k).S (st sp al ts k).P t w = true := by
        cases hyD : inD (st sp al ts k).D y with
        | false => exact hinv.clean_good hls hyD (written_of_ne_root sp hyr) ht hry
        | true =>
          -- the slot's object is not pinned, so its node is clean, and its latest
          -- version names a version of y good for t
          obtain ⟨hxD, hne⟩ := hpinned h o2 y r ho2 hsl hyD
          have hxr : o2.node ≠ SIS.root := by
            intro hx
            apply hne
            rw [hx] at ht2
            obtain ⟨ht0, -⟩ := hm.root
            rw [ht0, Option.some.injEq] at ht2
            exact ht2.symm
          obtain ⟨v, hv, hgv⟩ := hinv.clean_good hls hxD (written_of_ne_root sp hxr) ht hrt
          obtain ⟨rv, hrv⟩ := lv_versionAt hv
          obtain ⟨hvx, -⟩ := hinv.version_node hrv
          obtain ⟨⟨n', hn', hvh⟩, hch⟩ := (good_iff sp _ _ t v).mp hgv
          rw [hvx, hn, Option.some.injEq] at hn'
          subst hn'
          have hyv : y ∈ sp.live (v.hist.upTo t) := by rw [hvh, ← hh]; exact hy
          obtain ⟨r0, w0, -, hw0, -, hg0⟩ := hch y hyv
          obtain ⟨r', u', hu', hlu, hr0⟩ := lv_recNo_ge hw0
          exact ⟨u', hlu, hinv.newer hls (w0.level + 1) r0 r' y w0 u' (by omega) hw0 hu' hr0 t hg0⟩
      refine ⟨w.recNo, w, ?_, hinv.lv_at hw, hg⟩
      rw [hs, hw]
      rfl

/-- T2-C's startup: the Level 4 startup from the stream after T(k) gives a memory
with the invariant. -/
theorem einv_startup (hok : RunOK sp al ts) (hph : PhysRunOK sp al ts) (hj : al.stillDirty = javaTest sp)
    (hmk : al.mark = true) (hev : EvictRunOK sp al ts) {k : Nat} (hk : k ≤ ts.length) :
    EInv sp (st sp al ts k) (st sp al ts k).S k (evictStartup sp (st sp al ts k).S) :=
  (einv_hinv_startup hok hph hj hmk hev hk).1

end Startup

/-! ## The physical writer depends on P only through its nodes -/

section Congr

variable {sp : Spec V T} {P P' : Struct V} (hP : SameNodes P P')
include hP

theorem reachOnPath4_congr (S0 S : Stream V T) (j : Time) (path : List NodeId) :
    Mem.reachOnPath4 sp S0 S P j path = Mem.reachOnPath4 sp S0 S P' j path := by
  have hP' : ∀ x, P.get? x = P'.get? x := hP
  funext m x
  unfold Mem.reachOnPath4
  simp only [hP']

theorem srcOK4_congr (j : Time) (y : NodeId) : srcOK4 sp P j y = srcOK4 sp P' j y := by
  have hP' : ∀ x, P.get? x = P'.get? x := hP
  funext p
  unfold srcOK4
  simp only [hP.reachable, hP']

theorem newSlot4_congr (j : Time) (m : Mem V) (o : Obj V) (y : NodeId) :
    m.newSlot4 sp P j o y = m.newSlot4 sp P' j o y := by
  unfold Mem.newSlot4
  rw [srcOK4_congr hP]

theorem applyChange4_congr (j : Time) (c : Changes V) (m : Mem V) :
    m.applyChange4 sp P j c = m.applyChange4 sp P' j c := by
  unfold Mem.applyChange4
  simp only [newSlot4_congr hP]

theorem preWrite_congr (S0 : Stream V T) (D : Dirty) (S : Stream V T) (c : Changes V) (m1 : Mem V) :
    preWrite sp S0 ⟨P, D, S⟩ c m1 = preWrite sp S0 ⟨P', D, S⟩ c m1 := by
  have hP' : ∀ x, P.get? x = P'.get? x := hP
  unfold preWrite
  simp only [pathOf_congr hP, hP', reachOnPath4_congr hP, applyChange4_congr hP]

theorem D1Of_congr (al : Algo V T) (D : Dirty) (S : Stream V T) (c : Changes V) (vs0 : List (Version V)) :
    D1Of sp al ⟨P, D, S⟩ c vs0 = D1Of sp al ⟨P', D, S⟩ c vs0 := by
  have hPP := hP.apply S.length c
  unfold D1Of
  simp only [markOf_congr sp hPP, gotDirtyOf_congr sp _ hPP]

theorem takenOf_congr (al : Algo V T) (D : Dirty) (S : Stream V T) (tr : T) (c : Changes V)
    (vs0 : List (Version V)) :
    takenOf sp al ⟨P, D, S⟩ tr c vs0 = takenOf sp al ⟨P', D, S⟩ tr c vs0 := by
  have hPP := hP.apply S.length c
  unfold takenOf
  simp only [D1Of_congr hP, byLevel_congr hPP]

theorem stepOf_congr (al : Algo V T) (hst : AlgOK sp al) (D : Dirty) (S : Stream V T) (tr : T)
    (c : Changes V) (vs0 vs : List (Version V)) :
    Rel (stepOf sp al ⟨P, D, S⟩ tr c vs0 vs) (stepOf sp al ⟨P', D, S⟩ tr c vs0 vs) := by
  have hPP := hP.apply S.length c
  unfold stepOf
  simp only [markOf_congr sp hPP, gotDirtyOf_congr sp _ hPP, byLevel_congr hPP,
    stillDirtyOf_congr al hst.still.congr hPP, topOf_sameNodes sp hPP]
  exact ⟨rfl, rfl, hPP⟩

end Congr

/-- A transaction of the physical writer with eviction from states with the
same stream, D and nodes: the same record and D, and the same memory. -/
theorem evictTrans_congr (sp : Spec V T) (al : Algo V T) (hst : AlgOK sp al) (S0 : Stream V T)
    {db1 db2 : DB V T} (h : Rel db1 db2) (m : Mem V) (tr : T) :
    Rel (evictTrans sp al S0 db1 m tr).1 (evictTrans sp al S0 db2 m tr).1 ∧
      (evictTrans sp al S0 db1 m tr).2 = (evictTrans sp al S0 db2 m tr).2 := by
  obtain ⟨hS, hD, hP⟩ := h
  obtain ⟨P1, D1, S1⟩ := db1
  obtain ⟨P2, D2, S2⟩ := db2
  simp only at hS hD hP
  subst hS hD
  rw [evictTrans_eq, evictTrans_eq, evictAfter_eq, evictAfter_eq]
  simp only [preWrite_congr hP, D1Of_congr hP, takenOf_congr hP]
  exact ⟨stepOf_congr hP al hst _ _ _ _ _ _, trivial⟩

/-! ## Runs with restarts -/

section Run

variable {sp : Spec V T} {al : Algo V T}

/-- What holds after the first j transactions of a run with eviction and
restarts, with the last restart (or the start) after k1 transactions: the
stream of the last startup is the run's after k1; ⟨P, D, S⟩ is the run's after
j (the same stream and D, the same nodes); the memory has the invariant at j
for the startup from that stream, and the invariant for reads at earlier
times. -/
def EvictInvR (sp : Spec V T) (al : Algo V T) (ts : List (T × Bool × List CacheOp)) (j : Nat)
    (r : DB V T × Mem V × Stream V T) : Prop :=
  ∃ k1, k1 ≤ j ∧ r.2.2 = (st sp al (ts.map (·.1)) k1).S ∧ Rel r.1 (st sp al (ts.map (·.1)) j) ∧
    EInv sp (st sp al (ts.map (·.1)) j) (st sp al (ts.map (·.1)) k1).S j r.2.1 ∧
    HInv sp (st sp al (ts.map (·.1)) j) (st sp al (ts.map (·.1)) k1).S j r.2.1

/-- One transaction of a run with eviction and restarts, and its cache
operations or its restart, keeps `EvictInvR`. -/
theorem evictInvR_step {ts : List (T × Bool × List CacheOp)} (hok : RunOK sp al (ts.map (·.1)))
    (hph : PhysRunOK sp al (ts.map (·.1))) (hev : EvictRunOK sp al (ts.map (·.1)))
    (hj : al.stillDirty = javaTest sp) (hmk : al.mark = true) {j : Nat} (hjt : j < ts.length)
    {acc : DB V T × Mem V × Stream V T} (hI : EvictInvR sp al ts j acc) :
    EvictInvR sp al ts (j + 1)
      (if ts[j].2.1 then
        (startup sp (evictTrans sp al acc.2.2 acc.1 acc.2.1 ts[j].1).1.S,
          evictStartup sp (evictTrans sp al acc.2.2 acc.1 acc.2.1 ts[j].1).1.S,
          (evictTrans sp al acc.2.2 acc.1 acc.2.1 ts[j].1).1.S)
      else
        ((evictTrans sp al acc.2.2 acc.1 acc.2.1 ts[j].1).1,
          ts[j].2.2.foldl (Mem.cacheOp sp acc.2.2 (evictTrans sp al acc.2.2 acc.1 acc.2.1 ts[j].1).1.S
            (evictTrans sp al acc.2.2 acc.1 acc.2.1 ts[j].1).1.D) (evictTrans sp al acc.2.2 acc.1 acc.2.1 ts[j].1).2,
          acc.2.2)) := by
  obtain ⟨k1, hk1, hS0, hrel, hm, hh⟩ := hI
  have hst : AlgOK sp al := algOK_of sp al (Or.inl hj)
  have hjm : j < (ts.map (·.1)).length := by simp; omega
  have htr : (ts.map (·.1))[j] = ts[j].1 := by simp
  obtain ⟨hrel1, hmem1⟩ := evictTrans_congr sp al hst acc.2.2 hrel acc.2.1 ts[j].1
  have hrun := EInv.run_step hok hph hev hj hmk hjm hm ts[j].2.2
  have hrunH := HInv.run_step hok hph hev hj hmk hjm hm hh ts[j].2.2
  rw [htr, ← hS0] at hrun hrunH
  obtain ⟨f1, f2⟩ := hrun
  have hrel' : Rel (evictTrans sp al acc.2.2 acc.1 acc.2.1 ts[j].1).1 (st sp al (ts.map (·.1)) (j + 1)) := by
    rw [← f1]; exact hrel1
  unfold EvictInvR
  split
  · -- A restart after j + 1: the logical startup and the Level 4 startup from the stream.
    refine ⟨j + 1, Nat.le_refl _, hrel'.1, ?_, ?_, ?_⟩
    · show Rel (startup sp (evictTrans sp al acc.2.2 acc.1 acc.2.1 ts[j].1).1.S) _
      rw [hrel'.1]
      have hT1 := T1_strong sp al (ts.map (·.1)) hok hst (k := j + 1) (by simp; omega)
      exact ⟨rfl, hT1.2, hT1.1⟩
    · show EInv sp _ _ _ (evictStartup sp (evictTrans sp al acc.2.2 acc.1 acc.2.1 ts[j].1).1.S)
      rw [hrel'.1]
      exact (einv_hinv_startup hok hph hj hmk hev (by simp; omega)).1
    · show HInv sp _ _ _ (evictStartup sp (evictTrans sp al acc.2.2 acc.1 acc.2.1 ts[j].1).1.S)
      rw [hrel'.1]
      exact (einv_hinv_startup hok hph hj hmk hev (by simp; omega)).2
  · -- No restart: the same startup stream; the memory is the one from the run's state.
    refine ⟨k1, by omega, hS0, hrel', ?_, ?_⟩
    · show EInv sp _ _ _ (ts[j].2.2.foldl (Mem.cacheOp sp acc.2.2 (evictTrans sp al acc.2.2 acc.1 acc.2.1 ts[j].1).1.S
        (evictTrans sp al acc.2.2 acc.1 acc.2.1 ts[j].1).1.D) (evictTrans sp al acc.2.2 acc.1 acc.2.1 ts[j].1).2)
      rw [hrel1.1, hrel1.2.1, hmem1, ← hS0]
      exact f2
    · show HInv sp _ _ _ (ts[j].2.2.foldl (Mem.cacheOp sp acc.2.2 (evictTrans sp al acc.2.2 acc.1 acc.2.1 ts[j].1).1.S
        (evictTrans sp al acc.2.2 acc.1 acc.2.1 ts[j].1).1.D) (evictTrans sp al acc.2.2 acc.1 acc.2.1 ts[j].1).2)
      rw [hrel1.1, hrel1.2.1, hmem1, ← hS0]
      exact hrunH

/-- `EvictInvR` holds after every prefix of a run with eviction and restarts. -/
theorem evictInvR_all {ts : List (T × Bool × List CacheOp)} (hok : RunOK sp al (ts.map (·.1)))
    (hph : PhysRunOK sp al (ts.map (·.1))) (hev : EvictRunOK sp al (ts.map (·.1)))
    (hj : al.stillDirty = javaTest sp) (hmk : al.mark = true) :
    ∀ j ≤ ts.length, EvictInvR sp al ts j (runEvict sp al (ts.take j)) := by
  intro j
  induction j with
  | zero =>
    intro _
    have h0 : runEvict sp al (ts.take 0) = (init sp, evictStartup sp (init sp).S, (init sp).S) := by
      simp [runEvict]
    rw [h0]
    refine ⟨0, Nat.le_refl _, by rw [st_zero], by rw [st_zero]; exact ⟨rfl, rfl, SameNodes.refl _⟩, ?_, ?_⟩
    · rw [st_zero]
      exact einv_init hok.1
    · rw [st_zero]
      exact HInv.of_live (inv_init sp hok.1) hok.1.liveSub (einv_init hok.1)
  | succ j ih =>
    intro hjt
    rw [runEvict_succ sp al ts (by omega)]
    exact evictInvR_step hok hph hev hj hmk (by omega) (ih (by omega))

end Run

end SIS
