/-
Proofs about the physical layer with handles (bergdb item 009, phase 4a):
restarts, T2-C and T-READ with restarts over handles (`t2_handles`,
`tr_handles_restarts`), as SIS/Proof/EvictRestart.lean shows for Evict.lean.
The startup with handles from the stream after T(k) is Evict.lean's Level 4
startup taken to handles, but for the references of the pointers that rule 4
links: Evict.lean's rule 4 makes a memory slot to the pointee's canonical
object, whose pointer has that object's position as its reference; rule 4 with
handles keeps the stream slot's reference, a version of the node. Neither
changes what the pointer gives (it holds the pointee's live handle with its
canonical object), so the startup's memory has the invariant
(`heinv_hinvH_startup`) and the invariant for reads at earlier times. The
physical writer with handles depends on P only through its nodes
(`handleTrans_congr`), so a run with restarts keeps both (`handleInvR_all`).
-/
import SIS.Proof.HandleReadT
import SIS.Proof.EvictRestart

set_option linter.unusedSectionVars false

namespace SIS

variable {V T : Type} [DecidableEq V]

/-! ## Evict.lean's memory with handles: canonical objects, rule 4 -/

/-- The canonical objects of `Mem.toH` are the memory's, when the node table has
no repeated keys and names objects of their nodes. -/
theorem Mem.toH_canonicalOf {m : Mem V} (hnd : (m.table.map (·.1)).Nodup)
    (hv : ∀ y a, m.tableOf y = some a → ∃ o, m.obj? a = some o ∧ o.node = y) (y : NodeId) :
    m.toH.canonicalOf y = m.canonicalOf y := by
  unfold HMem.canonicalOf Mem.canonicalOf
  rw [Mem.toH_tableOf]
  cases ht : m.tableOf y with
  | none => rfl
  | some a =>
    simp only [Option.bind_some]
    have hh : m.toH.objOf a = some a := by
      unfold HMem.objOf; rw [Mem.toH_handle?, Mem.table_find hnd hv ht]; rfl
    rw [hh]
    simp only
    obtain ⟨o, ho, -⟩ := hv y a ht
    have hheld : m.heldA a = true := by
      unfold Mem.heldA
      exact List.any_eq_true.mpr ⟨(y, a), mem_of_lookup m.table y a ht, by simp⟩
    rw [Mem.toH_obj?, hheld, ho]
    simp only [↓reduceIte, Option.map_some]
    rfl

/-- The slot of an object as Evict.lean's rule 4 leaves it. -/
theorem linkObjD_slot? (m : Mem V) (D : Dirty) (h : Nat) (o : Obj V) (y : NodeId) :
    (linkObjD m D h o).slot? y = if (o.canonical && (inD D o.node || h == m.root)) = true then
      (o.slot? y).map (fun sl => (linkSlot m (y, sl)).2) else o.slot? y := by
  unfold linkObjD
  cases (o.canonical && (inD D o.node || h == m.root)) with
  | false => simp
  | true =>
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    unfold Obj.slot?
    exact lookup_map_key (linkSlot m) (linkSlot_fst m) y o.slots

/-- The pointer of an object as rule 4 with handles leaves it. -/
theorem HMem.linkObj_ptr? (m : HMem V) (D : Dirty) (a : Nat) (o : HObj V) (y : NodeId) :
    (m.linkObj D a o).ptr? y = if (o.canonical && (inD D o.node || a == m.root)) = true then
      (o.ptr? y).map (fun q => (m.linkPtr (y, q)).2) else o.ptr? y := by
  unfold HMem.linkObj
  cases (o.canonical && (inD D o.node || a == m.root)) with
  | false => simp
  | true =>
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    unfold HObj.ptr?
    exact lookup_map_key m.linkPtr (HMem.linkPtr_fst m) y o.ptrs

/-! ## E4's invariant taken to handles -/

section ToH

variable {sp : Spec V T} {db : DB V T} {S0 : Stream V T} {k : Nat}

/-- The memory with handles that holds the objects of a memory with E4's
invariant for reads at earlier times, all canonical, has the invariant for reads
at earlier times with handles: a memory slot becomes a pointer that holds the
object's live handle, a stream slot a pointer whose slow path's reference is the
slot's reference after Rule R. -/
theorem HInv.toH {M : Mem V} (hm : EInv sp db S0 k M) (hh : HInv sp db S0 k M)
    (hall : ∀ h o, M.obj? h = some o → o.canonical = true) : HInvH sp db S0 k M.toH := by
  have hv : ∀ y a, M.tableOf y = some a → ∃ o, M.obj? a = some o ∧ o.node = y := hm.tbl
  have hheld : ∀ a o, M.obj? a = some o → M.heldA a = true := by
    intro a o ho
    have ht := hm.canonTbl a o ho (hall a o ho)
    unfold Mem.heldA
    exact List.any_eq_true.mpr ⟨(o.node, a), mem_of_lookup M.table o.node a ht, by simp⟩
  intro a o' ho' hc t ht hr y hy
  rw [Mem.toH_obj?] at ho'
  split at ho'
  · obtain ⟨o, ho, rfl⟩ := Option.map_eq_some_iff.mp ho'
    obtain ⟨sl, hsl, hsh⟩ := hh a o ho (hall a o ho) t ht hr y hy
    refine ⟨(M.ptrOfH (y, sl)).2, by rw [Mem.objH_ptr?, hsl]; rfl, ?_⟩
    cases sl with
    | mem h' =>
      left
      obtain ⟨o2, ho2, hn2, -⟩ := hsh
      have ht2 := hm.canonTbl h' o2 ho2 (hall h' o2 ho2)
      have hp : (M.ptrOfH (y, Slot.mem h')).2 = { ref := (M.obj? h').bind (·.pos), handle := some h' } := by
        show ({ ref := (M.obj? h').bind (·.pos), handle := if M.heldA h' then some h' else none } : HPtr) = _
        simp [hheld h' o2 ho2]
      rw [hp]
      refine (M.toH.holdsCanonical_iff _).mpr ⟨h', h', M.objH o2, rfl, ?_, ?_, hall h' o2 ho2⟩
      · unfold HMem.objOf; rw [Mem.toH_handle?, Mem.table_find hm.tblNodup hv ht2]; rfl
      · rw [Mem.toH_obj?, hheld h' o2 ho2, ho2]; rfl
    | stream r =>
      rcases hsh with ⟨r', w, h1, h2, h3⟩ | hd
      · right; left
        refine ⟨r', w, ?_, h2, h3⟩
        show M.toH.slowRef S0 y { ref := r, handle := none } = some r'
        unfold HMem.slowRef
        simp only [Option.bind_none, maxRef_none]
        exact h1
      · exact Or.inr (Or.inr hd)
  · cases ho'

end ToH

/-! ## The startup with handles from the stream after T(k) -/

section Startup

variable {sp : Spec V T} {al : Algo V T} {ts : List T}

/-- T2-C's startup with handles: the startup with handles from the stream after
T(k) gives a memory with the invariant, and with the invariant for reads at
earlier times. It is Evict.lean's Level 4 startup taken to handles (which has
both, by `einv_hinv_startup_facts`), but for the pointers that rule 4 links, of
the pinned objects to the nodes with canonical objects: they hold the node's
live handle in both, and keep the stream slot's reference, a version, instead
of the canonical object's position. Also what T9's invariant over handles needs
(bergdb 005-62): every pointer holds a canonical object or has its pointee's
latest version as its slow path's reference, and the root's pointers to the
nodes of D hold canonical objects. -/
theorem heinv_hinvH_startup (hok : RunOK sp al ts) (hph : PhysRunOK sp al ts) (hj : al.stillDirty = javaTest sp)
    (hmk : al.mark = true) (hev : EvictRunOK sp al ts) {k : Nat} (hk : k ≤ ts.length) :
    HEInv sp (st sp al ts k) (st sp al ts k).S k (handleStartup sp (st sp al ts k).S) ∧
      HInvH sp (st sp al ts k) (st sp al ts k).S k (handleStartup sp (st sp al ts k).S) ∧
      (∀ a o y p, (handleStartup sp (st sp al ts k).S).obj? a = some o → o.ptr? y = some p →
        (handleStartup sp (st sp al ts k).S).holdsCanonical p = true ∨
          (handleStartup sp (st sp al ts k).S).slowRef (st sp al ts k).S y p =
            ((st sp al ts k).S.lv y).map (·.recNo)) ∧
      (∀ o y p, (handleStartup sp (st sp al ts k).S).obj? (handleStartup sp (st sp al ts k).S).root = some o →
        o.ptr? y = some p → inD (st sp al ts k).D y = true →
        (handleStartup sp (st sp al ts k).S).holdsCanonical p = true) := by
  have hst : AlgOK sp al := algOK_of sp al (Or.inl hj)
  have hinv := inv_st sp al ts hok hst k hk
  obtain ⟨hE, hHE, hall, hser, hpin, hmem⟩ := einv_hinv_startup_facts hok hph hj hmk hev hk
  obtain ⟨hr, -⟩ := rinv_lazyStartup hok hph hj hmk hev hk
  have hD : (startup sp (st sp al ts k).S).D = (st sp al ts k).D := (T1_strong sp al ts hok hst hk).2
  unfold evictStartup at hE hHE hall hser hpin hmem
  unfold handleStartup
  rw [hD] at hE hHE hall hser hpin hmem ⊢
  generalize lazyStartup sp (st sp al ts k).S = m0 at hE hHE hall hser hpin hmem hr ⊢
  -- The memory after the positions, M1, and its objects: m0's, with the same slots.
  have hobj1 := Mem.sectionPos_obj? m0 (st sp al ts k).S
  have hslot1 : ∀ a o1, (m0.sectionPos (st sp al ts k).S).obj? a = some o1 →
      ∃ o0, m0.obj? a = some o0 ∧ ∀ y, o1.slot? y = o0.slot? y := by
    intro a o1 ho1
    rw [hobj1] at ho1
    obtain ⟨o0, ho0, rfl⟩ := Option.map_eq_some_iff.mp ho1
    refine ⟨o0, ho0, fun y => ?_⟩
    split
    · rfl
    · split <;> rfl
  generalize hM1 : m0.sectionPos (st sp al ts k).S = M1 at hE hHE hall hser hpin hmem hslot1 ⊢
  -- Evict.lean's startup E = M1.linkD D, and its objects.
  have hobjE := Mem.linkD_obj? M1 (st sp al ts k).D
  have hcanE : ∀ y, (M1.linkD (st sp al ts k).D).canonicalOf y = M1.canonicalOf y := by
    intro y
    unfold Mem.canonicalOf
    show (match M1.tableOf y with
      | some h => match (M1.linkD (st sp al ts k).D).obj? h with
        | some o => if o.canonical then some h else none
        | none => none
      | none => none) = _
    cases M1.tableOf y with
    | none => rfl
    | some h =>
      simp only
      rw [hobjE]
      cases M1.obj? h with
      | none => rfl
      | some o =>
        simp only [Option.map_some]
        rw [show (linkObjD M1 (st sp al ts k).D h o).canonical = o.canonical from
          congrArg (fun c => c.2.2.2.2.1) (linkObjD_core M1 (st sp al ts k).D h o)]
  have hall1 : ∀ a o1, M1.obj? a = some o1 → o1.canonical = true := by
    intro a o1 ho1
    have := hall a _ (by rw [hobjE, ho1]; rfl)
    rwa [show (linkObjD M1 (st sp al ts k).D a o1).canonical = o1.canonical from
      congrArg (fun c => c.2.2.2.2.1) (linkObjD_core M1 (st sp al ts k).D a o1)] at this
  have htn1 : ∀ y a, M1.tableOf y = some a → ∃ o, M1.obj? a = some o ∧ o.node = y := by
    intro y a ht
    obtain ⟨o2, ho2, hn2⟩ := hE.tbl y a ht
    rw [hobjE] at ho2
    obtain ⟨o1, ho1, rfl⟩ := Option.map_eq_some_iff.mp ho2
    exact ⟨o1, ho1, by rw [← hn2]; exact (congrArg (fun c => c.1) (linkObjD_core M1 _ a o1)).symm⟩
  have hnd1 : (M1.table.map (·.1)).Nodup := hE.tblNodup
  have hcanH1 : ∀ y, M1.toH.canonicalOf y = M1.canonicalOf y := Mem.toH_canonicalOf hnd1 htn1
  have hcanHE : ∀ y, (M1.linkD (st sp al ts k).D).toH.canonicalOf y = M1.canonicalOf y := by
    intro y; rw [Mem.toH_canonicalOf hE.tblNodup hE.tbl, hcanE]
  -- A memory slot of M1 names an object in the node table.
  have hheld : ∀ a o, M1.obj? a = some o → M1.heldA a = true := by
    intro a o ho
    have ho2 : (M1.linkD (st sp al ts k).D).obj? a = some (linkObjD M1 (st sp al ts k).D a o) := by
      rw [hobjE, ho]; rfl
    have ht := hE.canonTbl a _ ho2 (hall a _ ho2)
    unfold Mem.heldA
    exact List.any_eq_true.mpr ⟨(_, a), mem_of_lookup (M1.linkD (st sp al ts k).D).table _ a ht, by simp⟩
  have hmemheld : ∀ a o1 y h, M1.obj? a = some o1 → o1.slot? y = some (Slot.mem h) → M1.heldA h = true := by
    intro a o1 y h ho1 hsl
    have ho2 : (M1.linkD (st sp al ts k).D).obj? a = some (linkObjD M1 (st sp al ts k).D a o1) := by
      rw [hobjE, ho1]; rfl
    have hsl2 : (linkObjD M1 (st sp al ts k).D a o1).slot? y = some (Slot.mem h) := by
      rw [linkObjD_slot?, hsl]
      split <;> rfl
    obtain ⟨o', ho', -⟩ := hE.slotsNode a _ ho2 y h hsl2
    rw [hobjE] at ho'
    obtain ⟨o1', ho1', -⟩ := Option.map_eq_some_iff.mp ho'
    exact hheld h o1' ho1'
  -- The two memories' pointers, for a slot that rule 4 does not link.
  have hptrE : ∀ (y : NodeId) (sl : Slot),
      ((M1.linkD (st sp al ts k).D).ptrOfH (y, sl)).2 = (M1.ptrOfH (y, sl)).2 := by
    intro y sl
    cases sl with
    | stream r => rfl
    | mem h =>
      unfold Mem.ptrOfH
      simp only
      rw [hobjE]
      cases M1.obj? h with
      | none => rfl
      | some o =>
        simp only [Option.map_some, Option.bind_some]
        rw [show (linkObjD M1 (st sp al ts k).D h o).pos = o.pos from
          congrArg (fun c => c.2.2.2.2.2) (linkObjD_core M1 (st sp al ts k).D h o)]
        rfl
  -- Evict.lean's startup taken to handles has the invariant: its stream slots are m0's,
  -- whose references name versions.
  have hstrE : ∀ h o y r, (M1.linkD (st sp al ts k).D).obj? h = some o → o.slot? y = some (Slot.stream r) →
      ∀ r', r = some r' → ∃ u, (st sp al ts k).S.versionAt r' y = some u := by
    intro h o y r ho hsl r' hr'
    rw [hobjE] at ho
    obtain ⟨o1, ho1, rfl⟩ := Option.map_eq_some_iff.mp ho
    obtain ⟨o0, ho0, hs0⟩ := hslot1 h o1 ho1
    have hsl1 : o1.slot? y = some (Slot.stream r) := by
      rcases linkObjD_slot M1 (st sp al ts k).D h o1 y with he | ⟨sl, h0, -, hs2, -⟩
      · rw [← he]; exact hsl
      · rw [hs2] at hsl; cases hsl
    rw [hs0, hr'] at hsl1
    exact hr.ver h o0 ho0 y r' hsl1
  have hEH := hE.toH hinv hall hstrE
  have hHH := hHE.toH hE hall
  -- The startup with handles against Evict.lean's taken to handles.
  have hbk : ∀ a o', (M1.toH.linkD (st sp al ts k).D).obj? a = some o' →
      ∃ o, (M1.linkD (st sp al ts k).D).toH.obj? a = some o ∧ o'.core = o.core ∧
        (o.canonical = false → o' = o) ∧
        ∀ y, o'.ptr? y = o.ptr? y ∨ ∃ q q', o.ptr? y = some q ∧ o'.ptr? y = some q' ∧
          q'.handle = (M1.linkD (st sp al ts k).D).toH.tableOf y ∧
          ((M1.linkD (st sp al ts k).D).toH.canonicalOf y).isSome = true ∧
          ∀ r, q'.ref = some r → ∃ u, (st sp al ts k).S.versionAt r y = some u := by
    intro a o' ho'
    rw [HMem.linkD_obj?, Mem.toH_obj?] at ho'
    split at ho'
    · rename_i hha
      obtain ⟨oh, hoh, rfl⟩ := Option.map_eq_some_iff.mp ho'
      obtain ⟨o1, ho1, rfl⟩ := Option.map_eq_some_iff.mp hoh
      have hc1 := hall1 a o1 ho1
      refine ⟨(M1.linkD (st sp al ts k).D).objH (linkObjD M1 (st sp al ts k).D a o1), ?_, ?_, ?_, fun y => ?_⟩
      · rw [Mem.toH_obj?, (show (M1.linkD (st sp al ts k).D).heldA a = M1.heldA a from rfl), hha, hobjE, ho1]
        rfl
      · rw [HMem.linkObj_core]
        show o1.core = (linkObjD M1 (st sp al ts k).D a o1).core
        exact (linkObjD_core M1 (st sp al ts k).D a o1).symm
      · intro hc
        exfalso
        have : (linkObjD M1 (st sp al ts k).D a o1).canonical = o1.canonical :=
          congrArg (fun c => c.2.2.2.2.1) (linkObjD_core M1 (st sp al ts k).D a o1)
        have hc' : (linkObjD M1 (st sp al ts k).D a o1).canonical = false := hc
        rw [this, hc1] at hc'
        cases hc'
      · rw [HMem.linkObj_ptr?, Mem.objH_ptr?, Mem.objH_ptr?, linkObjD_slot?]
        have hpin : ((M1.objH o1).canonical && (inD (st sp al ts k).D (M1.objH o1).node ||
            a == M1.toH.root)) = (o1.canonical && (inD (st sp al ts k).D o1.node || a == M1.root)) := rfl
        rw [hpin]
        cases hp : (o1.canonical && (inD (st sp al ts k).D o1.node || a == M1.root)) with
        | false =>
          left
          simp only [Bool.false_eq_true, ↓reduceIte]
          cases o1.slot? y with
          | none => rfl
          | some sl => simp only [Option.map_some]; rw [hptrE]
        | true =>
          simp only [↓reduceIte]
          cases hsl : o1.slot? y with
          | none => left; rfl
          | some sl =>
            simp only [Option.map_some]
            cases sl with
            | mem h =>
              left
              have hpm : (M1.ptrOfH (y, Slot.mem h)).2 = { ref := (M1.obj? h).bind (·.pos), handle := some h } := by
                show ({ ref := (M1.obj? h).bind (·.pos), handle := if M1.heldA h then some h else none } : HPtr) = _
                simp [hmemheld a o1 y h ho1 hsl]
              rw [show (linkSlot M1 (y, Slot.mem h)).2 = Slot.mem h from rfl, hptrE, hpm]
              rfl
            | stream r =>
              cases hcy : M1.canonicalOf y with
              | none =>
                left
                have hl : (linkSlot M1 (y, Slot.stream r)).2 = Slot.stream r := by
                  unfold linkSlot; simp only [hcy]
                have hlp : (M1.toH.linkPtr (y, (M1.ptrOfH (y, Slot.stream r)).2)).2 =
                    (M1.ptrOfH (y, Slot.stream r)).2 := by
                  unfold HMem.linkPtr
                  simp only [Mem.ptrOfH, hcanH1, hcy]
                rw [hl, hlp, hptrE]
              | some h0 =>
                right
                have hl : (linkSlot M1 (y, Slot.stream r)).2 = Slot.mem h0 := by
                  unfold linkSlot; simp only [hcy]
                have hlp : (M1.toH.linkPtr (y, (M1.ptrOfH (y, Slot.stream r)).2)).2 =
                    { ref := r, handle := M1.toH.tableOf y } := by
                  unfold HMem.linkPtr
                  simp only [Mem.ptrOfH, hcanH1, hcy]
                rw [hl, hlp]
                refine ⟨_, _, rfl, rfl, rfl, by rw [hcanHE, hcy]; rfl, fun r' hr' => ?_⟩
                obtain ⟨o0, ho0, hs0⟩ := hslot1 a o1 ho1
                have hsl0 := hsl
                rw [hs0] at hsl0
                simp only at hr'
                rw [hr'] at hsl0
                exact hr.ver a o0 ho0 y r' hsl0
    · cases ho'
  have hfw : ∀ a o, (M1.linkD (st sp al ts k).D).toH.obj? a = some o →
      ∃ o', (M1.toH.linkD (st sp al ts k).D).obj? a = some o' := by
    intro a o ho
    rw [Mem.toH_obj?] at ho
    split at ho
    · rename_i hha
      rw [hobjE] at ho
      obtain ⟨o2, ho2, -⟩ := Option.map_eq_some_iff.mp ho
      obtain ⟨o1, ho1, -⟩ := Option.map_eq_some_iff.mp ho2
      refine ⟨M1.toH.linkObj (st sp al ts k).D a (M1.objH o1), ?_⟩
      rw [HMem.linkD_obj?, Mem.toH_obj?, (show M1.heldA a = (M1.linkD (st sp al ts k).D).heldA a from rfl), hha, ho1]
      rfl
    · cases ho
  have hnd : ((M1.toH.linkD (st sp al ts k).D).objs.map (·.1)).Nodup := by
    rw [HMem.linkD_keys, Mem.toH_objs, List.map_map]
    have hkeys : (M1.objs.map (·.1)).Nodup := by
      have h := hE.objNodup
      rwa [Mem.linkD_keys] at h
    have : ((List.filter (fun p => M1.heldA p.1) M1.objs).map ((·.1) ∘ fun p => (p.1, M1.objH p.2))) =
        (List.filter (fun p => M1.heldA p.1) M1.objs).map (·.1) := by
      apply List.map_congr_left; intro p _; rfl
    rw [this]
    exact (List.Sublist.map _ List.filter_sublist).nodup hkeys
  have hHinv := hEH.relinkH hfw hbk rfl rfl rfl rfl rfl rfl hnd
  -- Reads at earlier times: the pointers that differ hold a canonical object.
  have hcanM : ∀ c oc, (M1.linkD (st sp al ts k).D).toH.obj? c = some oc → oc.canonical = true →
      ∃ o'', (M1.toH.linkD (st sp al ts k).D).obj? c = some o'' ∧ o''.canonical = true := by
    intro c oc hoc hcc
    obtain ⟨o'', ho''⟩ := hfw c oc hoc
    obtain ⟨o3, ho3, hcore, -⟩ := hbk c o'' ho''
    rw [hoc, Option.some.injEq] at ho3
    rw [← ho3] at hcore
    exact ⟨o'', ho'', by rw [show o''.canonical = oc.canonical from congrArg (fun c => c.2.2.2.2.1) hcore]; exact hcc⟩
  have hkp : (M1.linkD (st sp al ts k).D).toH.KeepPtrs (M1.toH.linkD (st sp al ts k).D) := by
    refine ⟨rfl, fun n hd h => ⟨hd, h, rfl⟩, fun p h => ?_⟩
    obtain ⟨n, c, oc, hpn, hc, hoc, hcc⟩ := ((M1.linkD (st sp al ts k).D).toH.holdsCanonical_iff p).mp h
    obtain ⟨o'', ho'', hc''⟩ := hcanM c oc hoc hcc
    exact ((M1.toH.linkD (st sp al ts k).D).holdsCanonical_iff p).mpr ⟨n, c, o'', hpn, hc, ho'', hc''⟩
  refine ⟨hHinv, ?_, ?_⟩
  · apply hHH.transfer hEH.tbl hkp
    intro a o' ho' hc t ht hrt z hz
    obtain ⟨o, ho, hcore, -, hpt⟩ := hbk a o' ho'
    have e1 : o'.node = o.node := congrArg (fun c => c.1) hcore
    have e4 : o'.hist = o.hist := congrArg (fun c => c.2.2.2.1) hcore
    have e5 : o'.canonical = o.canonical := congrArg (fun c => c.2.2.2.2.1) hcore
    rcases hpt z with h | ⟨q, q', -, hq', hh', hcs, -⟩
    · exact Or.inl ⟨o, ho, by rw [← e5]; exact hc, e1.symm, by rw [e4], h⟩
    · right
      refine ⟨q', hq', Or.inl ?_⟩
      obtain ⟨c, hcz⟩ := Option.isSome_iff_exists.mp hcs
      obtain ⟨n, oc, htn, hcn, hoc, hcc⟩ := ((M1.linkD (st sp al ts k).D).toH.canonicalOf_eq_some z c).mp hcz
      obtain ⟨o'', ho'', hc''⟩ := hcanM c oc hoc hcc
      exact ((M1.toH.linkD (st sp al ts k).D).holdsCanonical_iff q').mpr ⟨n, c, o'', by rw [hh', htn], hcn, ho'',
        hc''⟩
  · -- The pointers (bergdb 005-62): each holds a canonical object, or its slow
    -- path's reference is its pointee's latest version; the root's pointers to the
    -- nodes of D hold canonical objects.
    have hEp : ∀ a o y q, (M1.linkD (st sp al ts k).D).toH.obj? a = some o → o.ptr? y = some q →
        ∃ oE sl, (M1.linkD (st sp al ts k).D).obj? a = some oE ∧ oE.slot? y = some sl ∧
          q = ((M1.linkD (st sp al ts k).D).ptrOfH (y, sl)).2 := by
      intro a o y q ho hq
      rw [Mem.toH_obj?] at ho
      split at ho
      · obtain ⟨oE, hoE, rfl⟩ := Option.map_eq_some_iff.mp ho
        rw [Mem.objH_ptr?] at hq
        obtain ⟨sl, hsl, rfl⟩ := Option.map_eq_some_iff.mp hq
        exact ⟨oE, sl, hoE, hsl, rfl⟩
      · cases ho
    have hmemC : ∀ a oE y h, (M1.linkD (st sp al ts k).D).obj? a = some oE → oE.slot? y = some (Slot.mem h) →
        (M1.toH.linkD (st sp al ts k).D).holdsCanonical
          ((M1.linkD (st sp al ts k).D).ptrOfH (y, Slot.mem h)).2 = true := by
      intro a oE y h hoE hsl
      have hc := hmem a oE y h hoE hsl
      have hth : (M1.linkD (st sp al ts k).D).tableOf y = some h := by
        unfold Mem.canonicalOf at hc
        cases ht : (M1.linkD (st sp al ts k).D).tableOf y with
        | none => rw [ht] at hc; cases hc
        | some h0 =>
          rw [ht] at hc
          simp only at hc
          cases ho0 : (M1.linkD (st sp al ts k).D).obj? h0 with
          | none => rw [ho0] at hc; cases hc
          | some o0 =>
            rw [ho0] at hc
            simp only at hc
            split at hc
            · rw [Option.some.injEq] at hc; rw [hc]
            · cases hc
      have hcEH : (M1.linkD (st sp al ts k).D).toH.canonicalOf y = some h := by
        rw [Mem.toH_canonicalOf hE.tblNodup hE.tbl]; exact hc
      obtain ⟨n, oc, htn, hcn, hoc, hcc⟩ := ((M1.linkD (st sp al ts k).D).toH.canonicalOf_eq_some y h).mp hcEH
      rw [Mem.toH_tableOf, hth, Option.some.injEq] at htn
      subst htn
      have hq : ((M1.linkD (st sp al ts k).D).ptrOfH (y, Slot.mem h)).2.handle = some h := by
        show (if (M1.linkD (st sp al ts k).D).table.any (fun e => e.2 == h) then some h else none) = some h
        have : (M1.linkD (st sp al ts k).D).table.any (fun e => e.2 == h) = true :=
          List.any_eq_true.mpr ⟨(y, h), mem_of_lookup _ _ _ hth, by simp⟩
        rw [this]; rfl
      obtain ⟨o'', ho'', hc''⟩ := hcanM h oc hoc hcc
      exact ((M1.toH.linkD (st sp al ts k).D).holdsCanonical_iff _).mpr ⟨h, h, o'', hq, hcn, ho'', hc''⟩
    have htabC : ∀ z q', q'.handle = (M1.linkD (st sp al ts k).D).toH.tableOf z →
        ((M1.linkD (st sp al ts k).D).toH.canonicalOf z).isSome = true →
        (M1.toH.linkD (st sp al ts k).D).holdsCanonical q' = true := by
      intro z q' hh' hcs
      obtain ⟨c, hcz⟩ := Option.isSome_iff_exists.mp hcs
      obtain ⟨n, oc, htn, hcn, hoc, hcc⟩ := ((M1.linkD (st sp al ts k).D).toH.canonicalOf_eq_some z c).mp hcz
      obtain ⟨o'', ho'', hc''⟩ := hcanM c oc hoc hcc
      exact ((M1.toH.linkD (st sp al ts k).D).holdsCanonical_iff q').mpr ⟨n, c, o'', by rw [hh', htn], hcn,
        ho'', hc''⟩
    refine ⟨fun a o' y q' ho' hq' => ?_, fun o' y q' ho' hq' hyD => ?_⟩
    · obtain ⟨o, ho, -, -, hpt⟩ := hbk a o' ho'
      rcases hpt y with h | ⟨q, q'', -, hq'', hh', hcs, -⟩
      · rw [h] at hq'
        obtain ⟨oE, sl, hoE, hsl, rfl⟩ := hEp a o y q' ho hq'
        cases sl with
        | mem h0 => exact Or.inl (hmemC a oE y h0 hoE hsl)
        | stream r =>
          right
          have := hser a oE y (Slot.stream r) hoE hsl
          simp only [slotRefOf] at this
          unfold HMem.slowRef
          simp only [Mem.ptrOfH, Option.bind_none, maxRef_none]
          exact this
      · rw [hq'', Option.some.injEq] at hq'
        subst hq'
        exact Or.inl (htabC y q'' hh' hcs)
    · obtain ⟨o, ho, -, -, hpt⟩ := hbk _ o' ho'
      rcases hpt y with h | ⟨q, q'', -, hq'', hh', hcs, -⟩
      · rw [h] at hq'
        obtain ⟨oE, sl, hoE, hsl, rfl⟩ := hEp _ o y q' ho hq'
        cases sl with
        | mem h0 => exact hmemC _ oE y h0 hoE hsl
        | stream r =>
          exfalso
          exact (hpin _ oE y r hoE hsl hyD).2 rfl
      · rw [hq'', Option.some.injEq] at hq'
        subst hq'
        exact htabC y q'' hh' hcs

end Startup

/-! ## The physical writer with handles depends on P only through its nodes -/

section Congr

variable {sp : Spec V T} {P P' : Struct V} (hP : SameNodes P P')
include hP

theorem reachOnPathH_congr (S0 S : Stream V T) (j : Time) (path : List NodeId) :
    HMem.reachOnPath sp S0 S P j path = HMem.reachOnPath sp S0 S P' j path := by
  have hP' : ∀ x, P.get? x = P'.get? x := hP
  funext m x
  unfold HMem.reachOnPath
  simp only [hP']

theorem srcOKH_congr (j : Time) (y : NodeId) : srcOKH sp P j y = srcOKH sp P' j y := by
  have hP' : ∀ x, P.get? x = P'.get? x := hP
  funext p
  unfold srcOKH
  simp only [hP.reachable, hP']

theorem newPtr_congr (j : Time) (m : HMem V) (o : HObj V) (y : NodeId) :
    m.newPtr sp P j o y = m.newPtr sp P' j o y := by
  unfold HMem.newPtr
  rw [srcOKH_congr hP]

theorem applyChangeH_congr (j : Time) (c : Changes V) (m : HMem V) :
    m.applyChange sp P j c = m.applyChange sp P' j c := by
  unfold HMem.applyChange
  simp only [newPtr_congr hP]

theorem preWriteH_congr (S0 : Stream V T) (D : Dirty) (S : Stream V T) (c : Changes V) (m1 : HMem V) :
    preWriteH sp S0 ⟨P, D, S⟩ c m1 = preWriteH sp S0 ⟨P', D, S⟩ c m1 := by
  have hP' : ∀ x, P.get? x = P'.get? x := hP
  unfold preWriteH
  simp only [pathOf_congr hP, hP', reachOnPathH_congr hP, applyChangeH_congr hP]

end Congr

/-- A transaction of the physical writer with handles from states with the same
stream, D and nodes: the same record and D, and the same memory. -/
theorem handleTrans_congr (sp : Spec V T) (al : Algo V T) (hst : AlgOK sp al) (S0 : Stream V T)
    {db1 db2 : DB V T} (h : Rel db1 db2) (m : HMem V) (tr : T) :
    Rel (handleTrans sp al S0 db1 m tr).1 (handleTrans sp al S0 db2 m tr).1 ∧
      (handleTrans sp al S0 db1 m tr).2 = (handleTrans sp al S0 db2 m tr).2 := by
  obtain ⟨hS, hD, hP⟩ := h
  obtain ⟨P1, D1, S1⟩ := db1
  obtain ⟨P2, D2, S2⟩ := db2
  simp only at hS hD hP
  subst hS hD
  rw [handleTrans_eq, handleTrans_eq, handleAfter_eq, handleAfter_eq]
  simp only [preWriteH_congr hP, D1Of_congr hP, takenOf_congr hP]
  exact ⟨stepOf_congr hP al hst _ _ _ _ _ _, trivial⟩

/-! ## Runs with restarts -/

section Run

variable {sp : Spec V T} {al : Algo V T}

/-- What holds after the first j transactions of a run with handles and
restarts, with the last restart (or the start) after k1 transactions: the
stream of the last startup is the run's after k1; ⟨P, D, S⟩ is the run's after
j (the same stream and D, the same nodes); the memory has the invariant at j for
the startup from that stream, and the invariant for reads at earlier times. -/
def HandleInvR (sp : Spec V T) (al : Algo V T) (ts : List (T × Bool × List HCacheOp)) (j : Nat)
    (r : DB V T × HMem V × Stream V T) : Prop :=
  ∃ k1, k1 ≤ j ∧ r.2.2 = (st sp al (ts.map (·.1)) k1).S ∧ Rel r.1 (st sp al (ts.map (·.1)) j) ∧
    HEInv sp (st sp al (ts.map (·.1)) j) (st sp al (ts.map (·.1)) k1).S j r.2.1 ∧
    HInvH sp (st sp al (ts.map (·.1)) j) (st sp al (ts.map (·.1)) k1).S j r.2.1

/-- One transaction of a run with handles and restarts, and its operations or
its restart, keeps `HandleInvR`. -/
theorem handleInvR_step {ts : List (T × Bool × List HCacheOp)} (hok : RunOK sp al (ts.map (·.1)))
    (hph : PhysRunOK sp al (ts.map (·.1))) (hev : EvictRunOK sp al (ts.map (·.1)))
    (hj : al.stillDirty = javaTest sp) (hmk : al.mark = true) {j : Nat} (hjt : j < ts.length)
    {acc : DB V T × HMem V × Stream V T} (hI : HandleInvR sp al ts j acc) :
    HandleInvR sp al ts (j + 1)
      (if ts[j].2.1 then
        (startup sp (handleTrans sp al acc.2.2 acc.1 acc.2.1 ts[j].1).1.S,
          handleStartup sp (handleTrans sp al acc.2.2 acc.1 acc.2.1 ts[j].1).1.S,
          (handleTrans sp al acc.2.2 acc.1 acc.2.1 ts[j].1).1.S)
      else
        ((handleTrans sp al acc.2.2 acc.1 acc.2.1 ts[j].1).1,
          ts[j].2.2.foldl (HMem.cacheOp sp acc.2.2 (handleTrans sp al acc.2.2 acc.1 acc.2.1 ts[j].1).1.S
            (handleTrans sp al acc.2.2 acc.1 acc.2.1 ts[j].1).1.D) (handleTrans sp al acc.2.2 acc.1 acc.2.1 ts[j].1).2,
          acc.2.2)) := by
  obtain ⟨k1, hk1, hS0, hrel, hm, hh⟩ := hI
  have hst : AlgOK sp al := algOK_of sp al (Or.inl hj)
  have hjm : j < (ts.map (·.1)).length := by simp; omega
  have htr : (ts.map (·.1))[j] = ts[j].1 := by simp
  obtain ⟨hrel1, hmem1⟩ := handleTrans_congr sp al hst acc.2.2 hrel acc.2.1 ts[j].1
  have hrun := HEInv.run_step hok hph hev hj hmk hjm hm ts[j].2.2
  have hrunH := HInvH.run_step hok hph hev hj hmk hjm hm hh ts[j].2.2
  rw [htr, ← hS0] at hrun hrunH
  obtain ⟨f1, f2⟩ := hrun
  have hrel' : Rel (handleTrans sp al acc.2.2 acc.1 acc.2.1 ts[j].1).1 (st sp al (ts.map (·.1)) (j + 1)) := by
    rw [← f1]; exact hrel1
  unfold HandleInvR
  split
  · -- A restart after j + 1: the logical startup and the startup with handles from the stream.
    refine ⟨j + 1, Nat.le_refl _, hrel'.1, ?_, ?_, ?_⟩
    · show Rel (startup sp (handleTrans sp al acc.2.2 acc.1 acc.2.1 ts[j].1).1.S) _
      rw [hrel'.1]
      have hT1 := T1_strong sp al (ts.map (·.1)) hok hst (k := j + 1) (by simp; omega)
      exact ⟨rfl, hT1.2, hT1.1⟩
    · show HEInv sp _ _ _ (handleStartup sp (handleTrans sp al acc.2.2 acc.1 acc.2.1 ts[j].1).1.S)
      rw [hrel'.1]
      exact (heinv_hinvH_startup hok hph hj hmk hev (by simp; omega)).1
    · show HInvH sp _ _ _ (handleStartup sp (handleTrans sp al acc.2.2 acc.1 acc.2.1 ts[j].1).1.S)
      rw [hrel'.1]
      exact (heinv_hinvH_startup hok hph hj hmk hev (by simp; omega)).2.1
  · -- No restart: the same startup stream; the memory is the one from the run's state.
    refine ⟨k1, by omega, hS0, hrel', ?_, ?_⟩
    · show HEInv sp _ _ _ (ts[j].2.2.foldl (HMem.cacheOp sp acc.2.2
        (handleTrans sp al acc.2.2 acc.1 acc.2.1 ts[j].1).1.S
        (handleTrans sp al acc.2.2 acc.1 acc.2.1 ts[j].1).1.D) (handleTrans sp al acc.2.2 acc.1 acc.2.1 ts[j].1).2)
      rw [hrel1.1, hrel1.2.1, hmem1, ← hS0]
      exact f2
    · show HInvH sp _ _ _ (ts[j].2.2.foldl (HMem.cacheOp sp acc.2.2
        (handleTrans sp al acc.2.2 acc.1 acc.2.1 ts[j].1).1.S
        (handleTrans sp al acc.2.2 acc.1 acc.2.1 ts[j].1).1.D) (handleTrans sp al acc.2.2 acc.1 acc.2.1 ts[j].1).2)
      rw [hrel1.1, hrel1.2.1, hmem1, ← hS0]
      exact hrunH

/-- `HandleInvR` holds after every prefix of a run with handles and restarts. -/
theorem handleInvR_all {ts : List (T × Bool × List HCacheOp)} (hok : RunOK sp al (ts.map (·.1)))
    (hph : PhysRunOK sp al (ts.map (·.1))) (hev : EvictRunOK sp al (ts.map (·.1)))
    (hj : al.stillDirty = javaTest sp) (hmk : al.mark = true) :
    ∀ j ≤ ts.length, HandleInvR sp al ts j (runHandles sp al (ts.take j)) := by
  intro j
  induction j with
  | zero =>
    intro _
    have h0 : runHandles sp al (ts.take 0) = (init sp, handleStartup sp (init sp).S, (init sp).S) := by
      simp [runHandles]
    rw [h0]
    refine ⟨0, Nat.le_refl _, by rw [st_zero], by rw [st_zero]; exact ⟨rfl, rfl, SameNodes.refl _⟩, ?_, ?_⟩
    · rw [st_zero]
      exact heinv_init hok.1
    · rw [st_zero]
      exact HInvH.of_live (inv_init sp hok.1) hok.1.liveSub (heinv_init hok.1)
  | succ j ih =>
    intro hjt
    rw [runHandles_succ sp al ts (by omega)]
    exact handleInvR_step hok hph hev hj hmk (by omega) (ih (by omega))

end Run

/-! ## T2-C and T-READ with restarts over handles -/

/-- `T2_handles` (SIS/HandleTheorems.lean) holds. -/
theorem t2_handles (sp : Spec V T) (al : Algo V T) : T2_handles sp al := by
  intro ts hok hph hev hj hmk j hjt db r m
  obtain ⟨k1, hk1, hS0, hrel, hm, -⟩ := handleInvR_all hok hph hev hj hmk j hjt
  have hst : st sp al (ts.map (·.1)) j = run sp al ((ts.take j).map (·.1)) := by
    unfold st; rw [List.map_take]
  have hst1 : st sp al (ts.map (·.1)) k1 = run sp al ((ts.take k1).map (·.1)) := by
    unfold st; rw [List.map_take]
  rw [hst] at hrel hm
  rw [hst1] at hS0 hm
  rw [← hS0] at hm
  obtain ⟨e1, e2, e3⟩ := hrel
  exact ⟨e1, e2, e3, k1, hk1, hS0, hm.tbl, hm.hcan, hm.hsnap, hm.hslot, hm.ruleR, hm.liveW, hm.hwritten⟩

/-- `TR_handles_restarts` (SIS/HandleTheorems.lean) holds. -/
theorem tr_handles_restarts (sp : Spec V T) (al : Algo V T) : TR_handles_restarts sp al := by
  intro ts hok hph hev hj hmk j hjt t ht db r m
  obtain ⟨k1, -, hS0, -, hm, hh⟩ := handleInvR_all hok hph hev hj hmk j hjt
  have hst : st sp al (ts.map (·.1)) j = run sp al ((ts.take j).map (·.1)) := by
    unfold st; rw [List.map_take]
  have hinv := inv_st sp al (ts.map (·.1)) hok (algOK_of sp al (Or.inl hj)) j
    (by rw [List.length_map]; exact hjt)
  rw [hst] at hm hh hinv
  rw [← hS0] at hm hh
  exact read_list_view (hm.readT_ok hinv hok.1.liveSub hh ht).2.2

end SIS
