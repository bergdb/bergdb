/-
Proofs about the physical layer with handles (bergdb 005-62): the startup with
handles from the stream after T(k) (`handleStartup`), proved over handles. Its
memory before `Mem.toH` and rule 4 is stage 1's lazy startup with the positions
of its section, which meets `StartMem` (`startMem_st`, from the rerun's
invariant `RInv`, SIS/Proof/PhysStart.lean): every object is canonical, its
node's table entry, with its node's whole history and latest position; a memory
slot names its pointee's canonical object, and a stream slot, after Rule R, its
pointee's latest version; a slot for every pointee; every node of D has a
canonical object. Taken to handles (`Mem.toH`) and with rule 4 with handles
(`HMem.linkD`), such a memory has the invariant with handles and the pointer
facts of T9's invariant (`StartMem.heinv`, `heinv_startup`; the invariant for
reads at earlier times is `StartMem.hinvH`, SIS/Proof/HandleRestart.lean): a
memory slot becomes a pointer that holds its pointee's live handle, a stream
slot of a pinned object to a node with a canonical object takes that node's
live handle by rule 4, and every other stream slot becomes a pointer whose slow
path's reference is its pointee's latest version.
-/
import SIS.Proof.PhysStart
import SIS.Proof.HandleInit

set_option linter.unusedSectionVars false

namespace SIS

variable {V T : Type} [DecidableEq V]

/-! ## The memory before rule 4 -/

/-- The positions of the section leave the node table and the canonical objects. -/
theorem Mem.sectionPos_canonicalOf (m : Mem V) (S : Stream V T) (y : NodeId) :
    (m.sectionPos S).canonicalOf y = m.canonicalOf y := by
  unfold Mem.canonicalOf
  rw [show (m.sectionPos S).tableOf y = m.tableOf y from rfl]
  cases m.tableOf y with
  | none => rfl
  | some h =>
    simp only
    rw [Mem.sectionPos_obj?]
    cases ho : m.obj? h with
    | none => rfl
    | some o =>
      simp only [Option.map_some]
      cases hc : o.canonical
      · simp [hc]
      · cases newest S m.s o.node <;> simp [hc]

/-- What the startup with handles needs of the memory before `Mem.toH` and rule 4,
in state db: the lazy startup's memory with the positions of the section. -/
structure StartMem (sp : Spec V T) (db : DB V T) (M : Mem V) : Prop where
  sEq : M.s = lastSp db.S
  fresh : ∀ h, M.next ≤ h → M.obj? h = none
  nodup : (M.objs.map (·.1)).Nodup
  tblNodup : (M.table.map (·.1)).Nodup
  root : M.tableOf root = some M.root ∧ ∃ o, M.obj? M.root = some o ∧ o.node = root
  tbl : ∀ y h, M.tableOf y = some h → ∃ o, M.obj? h = some o ∧ o.node = y
  /-- Every object is canonical and its node's table entry, -/
  canon : ∀ h o, M.obj? h = some o → o.canonical = true ∧ M.tableOf o.node = some h
  /-- with its node's whole history and its latest position. -/
  cc : ∀ h o, M.obj? h = some o →
    ∃ n, db.P.get? o.node = some n ∧ o.hist = n.hist ∧ o.level = n.level ∧ o.isData = n.isData
  pos : ∀ h o, M.obj? h = some o → o.pos = (db.S.lv o.node).map (·.recNo)
  /-- A memory slot names its pointee's canonical object; -/
  mem : ∀ h o y h', M.obj? h = some o → o.slot? y = some (Slot.mem h') → M.canonicalOf y = some h'
  /-- a stream slot names, after Rule R, its pointee's latest version, -/
  stream : ∀ h o y r, M.obj? h = some o → o.slot? y = some (Slot.stream r) →
    ruleRRef db.S (lastSp db.S) y r = (db.S.lv y).map (·.recNo)
  /-- and a version of it. -/
  ver : ∀ h o y r, M.obj? h = some o → o.slot? y = some (Slot.stream (some r)) →
    ∃ u, db.S.versionAt r y = some u
  /-- A slot for each pointee of the history. -/
  slots : ∀ h o, M.obj? h = some o → ∀ y ∈ pointees sp o.hist, (o.slot? y).isSome
  /-- Every node of D has a canonical object. -/
  dCanon : ∀ y, inD db.D y = true → (M.canonicalOf y).isSome

section Start

variable {sp : Spec V T} {al : Algo V T} {ts : List T}

/-- The lazy startup from the stream after T(k), with the positions of its
section, meets `StartMem`. -/
theorem startMem_st (hok : RunOK sp al ts) (hph : PhysRunOK sp al ts) (hj : al.stillDirty = javaTest sp)
    (hmk : al.mark = true) (hev : EvictRunOK sp al ts) {k : Nat} (hk : k ≤ ts.length) :
    StartMem sp (st sp al ts k) ((lazyStartup sp (st sp al ts k).S).sectionPos (st sp al ts k).S) := by
  have hst : AlgOK sp al := algOK_of sp al (Or.inl hj)
  have hinv := inv_st sp al ts hok hst k hk
  have hkk := kctx_st sp al ts hok hj (Nat.le_refl k) hk
  obtain ⟨hr, hm⟩ := rinv_lazyStartup hok hph hj hmk hev hk
  have hnd0 := tblND_lazyStartup sp (st sp al ts k).S
  generalize lazyStartup sp (st sp al ts k).S = m0 at hr hm hnd0
  have hs0 : m0.s = lastSp (st sp al ts k).S := hm.sEq
  have hobj1 := Mem.sectionPos_obj? m0 (st sp al ts k).S
  -- An object after the positions: m0's, at its node's latest position.
  have hshape : ∀ h o1, (m0.sectionPos (st sp al ts k).S).obj? h = some o1 →
      ∃ o0, m0.obj? h = some o0 ∧ o1 = { o0 with pos := ((st sp al ts k).S.lv o0.node).map (·.recNo) } := by
    intro h o1 ho1
    rw [hobj1] at ho1
    obtain ⟨o0, ho0, rfl⟩ := Option.map_eq_some_iff.mp ho1
    have hc0 := hr.canon h o0 ho0
    refine ⟨o0, ho0, ?_⟩
    simp only [hc0, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    cases hn : newest (st sp al ts k).S m0.s o0.node with
    | some w =>
      rw [hs0] at hn
      rw [newest_lv hn]
      rfl
    | none =>
      rw [← hr.pos h o0 ho0 (by rw [← hs0]; exact hn)]
      show o0 = _
      cases o0
      simp only at hc0
      rw [hc0]
  have hback : ∀ h o0, m0.obj? h = some o0 →
      (m0.sectionPos (st sp al ts k).S).obj? h = some { o0 with pos := ((st sp al ts k).S.lv o0.node).map (·.recNo) } := by
    intro h o0 ho0
    cases ho1 : (m0.sectionPos (st sp al ts k).S).obj? h with
    | none => rw [hobj1, ho0] at ho1; cases ho1
    | some o1 =>
      obtain ⟨o0', ho0', rfl⟩ := hshape h o1 ho1
      rw [ho0, Option.some.injEq] at ho0'
      rw [ho0']
  have hcan : ∀ y, (m0.sectionPos (st sp al ts k).S).canonicalOf y = m0.canonicalOf y :=
    Mem.sectionPos_canonicalOf m0 (st sp al ts k).S
  -- A canonical object of m0: its table entry and its node's whole history (CC).
  have hcc : ∀ h o0, m0.obj? h = some o0 → m0.tableOf o0.node = some h ∧
      ∃ n, (st sp al ts k).P.get? o0.node = some n ∧ o0.hist = n.hist ∧ o0.level = n.level ∧
        o0.isData = n.isData := by
    intro h o0 ho0
    obtain ⟨ht, ⟨n, hn, hh, hl, hd⟩, -⟩ := hm.canon h o0 ho0 (hr.canon h o0 ho0)
    refine ⟨ht, n, hn, ?_, hl, hd⟩
    rw [hh]
    exact upTo_of_forall _ _ (hinv.times _ n hn)
  refine
    { sEq := hs0
      fresh := fun h hh => by rw [hobj1, hm.fresh h hh]; rfl
      nodup := by rw [Mem.sectionPos_keys]; exact hm.nodup
      tblNodup := hnd0
      root := ?_
      tbl := ?_
      canon := ?_
      cc := ?_
      pos := ?_
      mem := ?_
      stream := ?_
      ver := ?_
      slots := ?_
      dCanon := ?_ }
  · obtain ⟨ht0, o0, ho0, -, hn0⟩ := hm.root
    exact ⟨ht0, _, hback _ o0 ho0, hn0⟩
  · intro y h ht
    obtain ⟨o0, ho0, hn0⟩ := hm.tbl y h ht
    exact ⟨_, hback h o0 ho0, hn0⟩
  · intro h o1 ho1
    obtain ⟨o0, ho0, rfl⟩ := hshape h o1 ho1
    exact ⟨hr.canon h o0 ho0, (hcc h o0 ho0).1⟩
  · intro h o1 ho1
    obtain ⟨o0, ho0, rfl⟩ := hshape h o1 ho1
    exact (hcc h o0 ho0).2
  · intro h o1 ho1
    obtain ⟨o0, ho0, rfl⟩ := hshape h o1 ho1
    rfl
  · intro h o1 y h' ho1 hsl
    obtain ⟨o0, ho0, rfl⟩ := hshape h o1 ho1
    obtain ⟨o', ho', hn'⟩ := hr.memNode h o0 ho0 y h' hsl
    obtain ⟨ht', -⟩ := hcc h' o' ho'
    rw [hn'] at ht'
    rw [hcan]
    exact (m0.canonicalOf_eq_some y h').mpr ⟨ht', o', ho', hr.canon h' o' ho'⟩
  · intro h o1 y r ho1 hsl
    obtain ⟨o0, ho0, rfl⟩ := hshape h o1 ho1
    exact hr.fresh h o0 ho0 y r hsl
  · intro h o1 y r ho1 hsl
    obtain ⟨o0, ho0, rfl⟩ := hshape h o1 ho1
    exact hr.ver h o0 ho0 y r hsl
  · intro h o1 ho1 y hy
    obtain ⟨o0, ho0, rfl⟩ := hshape h o1 ho1
    exact hr.slotsAll h o0 ho0 y hy
  · intro y hy
    rw [hcan]
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
    | some h0 => rfl

end Start

/-! ## The memory with handles -/

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

section Handles

variable {sp : Spec V T} {db : DB V T} {M : Mem V}

/-- The node table names every object. -/
theorem StartMem.heldA (hS : StartMem sp db M) {a : Nat} {o : Obj V} (ho : M.obj? a = some o) :
    M.heldA a = true := by
  unfold Mem.heldA
  exact List.any_eq_true.mpr ⟨(o.node, a), mem_of_lookup M.table o.node a (hS.canon a o ho).2, by simp⟩

theorem StartMem.toH_obj? (hS : StartMem sp db M) (a : Nat) : M.toH.obj? a = (M.obj? a).map M.objH := by
  rw [Mem.toH_obj?]
  cases ho : M.obj? a with
  | none => simp
  | some o => simp [hS.heldA ho]

/-- The objects of the startup with handles. -/
theorem StartMem.obj? (hS : StartMem sp db M) (D : Dirty) (a : Nat) :
    (M.toH.linkD D).obj? a = (M.obj? a).map (fun o => M.toH.linkObj D a (M.objH o)) := by
  rw [HMem.linkD_obj?, hS.toH_obj?, Option.map_map]
  rfl

/-- Its handles: one for each entry of the node table, with the entry's address
as its number. -/
theorem StartMem.handle? (hS : StartMem sp db M) (D : Dirty) {y : NodeId} {a : Nat}
    (h : M.tableOf y = some a) : (M.toH.linkD D).handle? a = some (handleOfEntry (y, a)) := by
  show M.toH.handle? a = _
  rw [Mem.toH_handle?, Mem.table_find hS.tblNodup hS.tbl h]
  rfl

theorem StartMem.handle?_some (hS : StartMem sp db M) (D : Dirty) {n : Nat} {hd : Handle}
    (h : (M.toH.linkD D).handle? n = some hd) : ∃ y, M.tableOf y = some n ∧ hd = handleOfEntry (y, n) :=
  Mem.toH_handle?_some hS.tblNodup h

/-- Its canonical objects are M's. -/
theorem StartMem.canonicalOf (hS : StartMem sp db M) (D : Dirty) (y : NodeId) :
    (M.toH.linkD D).canonicalOf y = M.canonicalOf y := by
  rw [← Mem.toH_canonicalOf hS.tblNodup hS.tbl y]
  refine HMem.canonicalOf_congr (m := M.toH) (m' := M.toH.linkD D) (fun _ => rfl) (fun _ => rfl)
    (fun a => ?_) y
  rw [HMem.linkD_obj?, Option.map_map]
  apply congrArg (fun f => Option.map f (M.toH.obj? a))
  funext o
  exact congrArg (fun c => c.2.2.2.2.1) (HMem.linkObj_core M.toH D a o)

/-- The pointer of the startup with handles for pointee y of the object of M at
address a: a memory slot holds its object's live handle, with its position; a
stream slot keeps its reference, and takes y's live handle by rule 4 if the
object is pinned and y has a canonical object. -/
theorem StartMem.ptr? (hS : StartMem sp db M) (D : Dirty) {a : Nat} {o : Obj V} (ho : M.obj? a = some o)
    (y : NodeId) :
    (M.toH.linkObj D a (M.objH o)).ptr? y = (o.slot? y).map (fun sl => match sl with
      | Slot.mem h' => ({ ref := (M.obj? h').bind (·.pos), handle := some h' } : HPtr)
      | Slot.stream r => ({ ref := r, handle :=
          if (inD D o.node || a == M.root) && (M.canonicalOf y).isSome then M.tableOf y else none } : HPtr)) := by
  rw [HMem.linkObj_ptr?, Mem.objH_ptr?]
  have hpin : ((M.objH o).canonical && (inD D (M.objH o).node || a == M.toH.root)) =
      (inD D o.node || a == M.root) := by
    show (o.canonical && _) = _
    rw [(hS.canon a o ho).1]
    rfl
  rw [hpin]
  cases hsl : o.slot? y with
  | none => split <;> rfl
  | some sl =>
    cases sl with
    | mem h' =>
      have hc := hS.mem a o y h' ho hsl
      obtain ⟨-, o', ho', -⟩ := (M.canonicalOf_eq_some y h').mp hc
      have hp : (M.ptrOfH (y, Slot.mem h')).2 = { ref := (M.obj? h').bind (·.pos), handle := some h' } := by
        show ({ ref := (M.obj? h').bind (·.pos), handle := if M.heldA h' then some h' else none } : HPtr) = _
        simp [hS.heldA ho']
      split
      · simp only [Option.map_some, hp]
        rfl
      · simp only [Option.map_some, hp]
    | stream r =>
      have hp : (M.ptrOfH (y, Slot.stream r)).2 = { ref := r, handle := none } := rfl
      split
      · rename_i hpinned
        simp only [Option.map_some, hp, hpinned, Bool.true_and]
        unfold HMem.linkPtr
        simp only
        rw [Mem.toH_canonicalOf hS.tblNodup hS.tbl y]
        cases M.canonicalOf y <;> rfl
      · rename_i hpinned
        simp only [Bool.not_eq_true] at hpinned
        simp [hp, hpinned]

/-- A pointer of the startup with handles holds its pointee's live handle, with
the pointee's canonical object; or it holds no handle, is of an object that is
not pinned or of a pointee with no canonical object, and its reference names,
after Rule R, its pointee's latest version. Either way its reference, if any,
names a version. -/
theorem StartMem.ptr_cases (hS : StartMem sp db M) {k : Nat} (hinv : Inv sp db k) (D : Dirty) {a : Nat}
    {o : Obj V} (ho : M.obj? a = some o) {y : NodeId} {q : HPtr}
    (hq : (M.toH.linkObj D a (M.objH o)).ptr? y = some q) :
    ((∃ b, q.handle = some b ∧ M.canonicalOf y = some b) ∨
      (q.handle = none ∧ ((inD D o.node || a == M.root) = true → M.canonicalOf y = none) ∧
        ruleRRef db.S (lastSp db.S) y q.ref = (db.S.lv y).map (·.recNo))) ∧
    ∀ r, q.ref = some r → ∃ u, db.S.versionAt r y = some u := by
  rw [hS.ptr? D ho y] at hq
  cases hsl : o.slot? y with
  | none => rw [hsl] at hq; cases hq
  | some sl =>
    rw [hsl] at hq
    simp only [Option.map_some, Option.some.injEq] at hq
    subst hq
    cases sl with
    | mem h' =>
      have hc := hS.mem a o y h' ho hsl
      obtain ⟨-, o', ho', -⟩ := (M.canonicalOf_eq_some y h').mp hc
      obtain ⟨-, ht'⟩ := hS.canon h' o' ho'
      obtain ⟨o'', ho'', hn''⟩ := hS.tbl o'.node h' ht'
      rw [ho', Option.some.injEq] at ho''
      subst ho''
      have hny : o'.node = y := by
        rw [Mem.canonicalOf_eq_some] at hc
        obtain ⟨hty, -⟩ := hc
        obtain ⟨o3, ho3, hn3⟩ := hS.tbl y h' hty
        rw [ho', Option.some.injEq] at ho3
        rw [ho3]; exact hn3
      refine ⟨Or.inl ⟨h', rfl, hc⟩, fun r hr => ?_⟩
      simp only [ho', Option.bind_some] at hr
      rw [hS.pos h' o' ho', hny] at hr
      cases hl : db.S.lv y with
      | none => rw [hl] at hr; cases hr
      | some v =>
        rw [hl] at hr
        simp only [Option.map_some, Option.some.injEq] at hr
        subst hr
        exact ⟨v, hinv.lv_at hl⟩
    | stream r =>
      refine ⟨?_, fun r' hr' => hS.ver a o y r' ho (by rw [hsl]; simp only at hr'; rw [hr'])⟩
      by_cases hl : ((inD D o.node || a == M.root) && (M.canonicalOf y).isSome) = true
      · left
        simp only [hl, ↓reduceIte]
        obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp (Bool.and_eq_true_iff.mp hl).2
        exact ⟨b, ((M.canonicalOf_eq_some y b).mp hb).1, hb⟩
      · right
        simp only [hl, Bool.false_eq_true, ↓reduceIte]
        refine ⟨trivial, fun hp => ?_, hS.stream a o y r ho hsl⟩
        cases hc : M.canonicalOf y with
        | none => rfl
        | some b => exfalso; apply hl; simp [hp, hc]

/-- A pointer that holds the live handle b of y's canonical object b holds y's live
handle with y's canonical object, and the record rule gives y's latest version. -/
theorem StartMem.holds (hS : StartMem sp db M) (D : Dirty) {y : NodeId} {b : Nat}
    (hb : M.canonicalOf y = some b) (q : HPtr) (hq : q.handle = some b) :
    (M.toH.linkD D).HoldsLive y q ∧ (M.toH.linkD D).holdsCanonical q = true ∧
      (M.toH.linkD D).ptrRef db.S y q = (db.S.lv y).map (·.recNo) := by
  have hhl : (M.toH.linkD D).HoldsLive y q :=
    ⟨b, hq, ((M.canonicalOf_eq_some y b).mp hb).1, by rw [hS.canonicalOf D, hb]; rfl⟩
  obtain ⟨b', o, hb', ho, hc, hpr⟩ := HMem.ptrRef_of_holdsLive db.S hhl
  rw [hS.canonicalOf D, hb, Option.some.injEq] at hb'
  subst hb'
  refine ⟨hhl, HMem.holdsCanonical_of_holdsLive hhl, ?_⟩
  rw [hpr]
  rw [hS.obj? D] at ho
  obtain ⟨o1, ho1, rfl⟩ := Option.map_eq_some_iff.mp ho
  have e := HMem.linkObj_core M.toH D b (M.objH o1)
  rw [show (M.toH.linkObj D b (M.objH o1)).pos = o1.pos from congrArg (fun c => c.2.2.2.2.2) e,
    hS.pos b o1 ho1]
  obtain ⟨ht, -⟩ := (M.canonicalOf_eq_some y b).mp hb
  obtain ⟨o2, ho2, hn2⟩ := hS.tbl y b ht
  rw [ho1, Option.some.injEq] at ho2
  rw [ho2, hn2]

/-- The objects of the startup with handles are M's, with their pointers as
`StartMem.ptr?` says. -/
theorem StartMem.back (hS : StartMem sp db M) {a : Nat} {o' : HObj V}
    (ho' : (M.toH.linkD db.D).obj? a = some o') :
    ∃ o, M.obj? a = some o ∧ o' = M.toH.linkObj db.D a (M.objH o) := by
  rw [hS.obj? db.D] at ho'
  obtain ⟨o, ho, rfl⟩ := Option.map_eq_some_iff.mp ho'
  exact ⟨o, ho, rfl⟩

theorem StartMem.fw (hS : StartMem sp db M) {a : Nat} {o : Obj V} (ho : M.obj? a = some o) :
    (M.toH.linkD db.D).obj? a = some (M.toH.linkObj db.D a (M.objH o)) := by
  rw [hS.obj? db.D, ho]
  rfl

theorem linkObjH_core (M : Mem V) (D : Dirty) (a : Nat) (o : Obj V) :
    (M.toH.linkObj D a (M.objH o)).node = o.node ∧ (M.toH.linkObj D a (M.objH o)).level = o.level ∧
      (M.toH.linkObj D a (M.objH o)).isData = o.isData ∧ (M.toH.linkObj D a (M.objH o)).hist = o.hist ∧
      (M.toH.linkObj D a (M.objH o)).canonical = o.canonical ∧ (M.toH.linkObj D a (M.objH o)).pos = o.pos := by
  have e := HMem.linkObj_core M.toH D a (M.objH o)
  simp only [HObj.core, Prod.mk.injEq] at e
  exact e

/-- The root's object is at the root's address, and only the root's. -/
theorem StartMem.root_iff (hS : StartMem sp db M) {a : Nat} {o : Obj V} (ho : M.obj? a = some o) :
    o.node = SIS.root ↔ a = M.root := by
  obtain ⟨ht0, o0, ho0, hn0⟩ := hS.root
  constructor
  · intro hn
    have ht := (hS.canon a o ho).2
    rw [hn, ht0, Option.some.injEq] at ht
    exact ht.symm
  · intro ha
    subst ha
    rw [ho0, Option.some.injEq] at ho
    rw [← ho, hn0]

/-- An object that is not pinned is not the root's, so its node is written. -/
theorem StartMem.unpin (hS : StartMem sp db M) {a : Nat} {o : Obj V} (ho : M.obj? a = some o)
    (hp : (inD db.D o.node || a == M.root) = false) : inD db.D o.node = false ∧ written sp o.node = true := by
  simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne] at hp
  exact ⟨hp.1, written_of_ne_root sp (fun hr => hp.2 ((hS.root_iff ho).mp hr))⟩

/-- The pointer of an object for a pointee of its history. -/
theorem StartMem.ptrOf (hS : StartMem sp db M) {a : Nat} {o : Obj V} (ho : M.obj? a = some o) {y : NodeId}
    (hy : y ∈ pointees sp o.hist) : ∃ q, (M.toH.linkObj db.D a (M.objH o)).ptr? y = some q := by
  obtain ⟨sl, hsl⟩ := Option.isSome_iff_exists.mp (hS.slots a o ho y hy)
  rw [hS.ptr? db.D ho y, hsl]
  exact ⟨_, rfl⟩

/-- A pointer of a pinned object to a node of D holds the node's live handle. -/
theorem StartMem.pinD (hS : StartMem sp db M) {k : Nat} (hinv : Inv sp db k) {a : Nat} {o : Obj V}
    (ho : M.obj? a = some o) {y : NodeId} {q : HPtr} (hq : (M.toH.linkObj db.D a (M.objH o)).ptr? y = some q)
    (hp : (inD db.D o.node || a == M.root) = true) (hy : inD db.D y = true) :
    ∃ b, q.handle = some b ∧ M.canonicalOf y = some b := by
  rcases (hS.ptr_cases hinv db.D ho hq).1 with h | ⟨-, hn, -⟩
  · exact h
  · obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp (hS.dCanon y hy)
    rw [hn hp] at hb; cases hb

/-- A pointer of the startup with handles: the record rule gives its pointee's
latest version, and it holds a canonical object or holds no handle and has its
pointee's latest version as its slow path's reference. -/
theorem StartMem.refs (hS : StartMem sp db M) {k : Nat} (hinv : Inv sp db k) {a : Nat} {o : Obj V}
    (ho : M.obj? a = some o) {y : NodeId} {q : HPtr} (hq : (M.toH.linkObj db.D a (M.objH o)).ptr? y = some q) :
    (M.toH.linkD db.D).ptrRef db.S y q = (db.S.lv y).map (·.recNo) ∧
      ((M.toH.linkD db.D).holdsCanonical q = true ∨
        (q.handle = none ∧ (M.toH.linkD db.D).slowRef db.S y q = (db.S.lv y).map (·.recNo))) := by
  rcases (hS.ptr_cases hinv db.D ho hq).1 with ⟨b, hb, hc⟩ | ⟨hn, -, hr⟩
  · obtain ⟨-, h2, h3⟩ := hS.holds db.D hc q hb
    exact ⟨h3, Or.inl h2⟩
  · have hs : (M.toH.linkD db.D).s = lastSp db.S := hS.sEq
    have h1 : (M.toH.linkD db.D).ptrRef db.S y q = (db.S.lv y).map (·.recNo) := by
      unfold HMem.ptrRef
      rw [hn, hs]
      exact hr
    refine ⟨h1, Or.inr ⟨hn, ?_⟩⟩
    unfold HMem.slowRef
    rw [hn, hs]
    simp only [Option.bind_none, maxRef_none]
    exact hr

/-- The startup with handles from a memory that meets `StartMem` in state db at
time k has the invariant with handles; every pointer holds a canonical object or
has its pointee's latest version as its slow path's reference; and the root's
pointers to the nodes of D hold canonical objects. -/
theorem StartMem.heinv (hS : StartMem sp db M) {k : Nat} (hinv : Inv sp db k) (hls : LiveSub sp)
    (hlog : EvLogic sp db k) :
    HEInv sp db db.S k (M.toH.linkD db.D) ∧
      (∀ a o y p, (M.toH.linkD db.D).obj? a = some o → o.ptr? y = some p →
        (M.toH.linkD db.D).holdsCanonical p = true ∨
          (M.toH.linkD db.D).slowRef db.S y p = (db.S.lv y).map (·.recNo)) ∧
      (∀ o y p, (M.toH.linkD db.D).obj? (M.toH.linkD db.D).root = some o → o.ptr? y = some p →
        inD db.D y = true → (M.toH.linkD db.D).holdsCanonical p = true) := by
  have hback : ∀ a o', (M.toH.linkD db.D).obj? a = some o' →
      ∃ o, M.obj? a = some o ∧ o' = M.toH.linkObj db.D a (M.objH o) := fun _ _ h => hS.back h
  have hfw : ∀ a o, M.obj? a = some o →
      (M.toH.linkD db.D).obj? a = some (M.toH.linkObj db.D a (M.objH o)) := fun _ _ h => hS.fw h
  have hcore := linkObjH_core M db.D
  have hcan := hS.canonicalOf db.D
  have hpinD : ∀ a o y q, M.obj? a = some o → (M.toH.linkObj db.D a (M.objH o)).ptr? y = some q →
      (inD db.D o.node || a == M.root) = true → inD db.D y = true →
      ∃ b, q.handle = some b ∧ M.canonicalOf y = some b := fun _ _ _ _ ho hq hp hy => hS.pinD hinv ho hq hp hy
  have hrec : ∀ a o y q, M.obj? a = some o → (M.toH.linkObj db.D a (M.objH o)).ptr? y = some q →
      (M.toH.linkD db.D).ptrRef db.S y q = (db.S.lv y).map (·.recNo) ∧
      ((M.toH.linkD db.D).holdsCanonical q = true ∨
        (q.handle = none ∧ (M.toH.linkD db.D).slowRef db.S y q = (db.S.lv y).map (·.recNo))) :=
    fun _ _ _ _ ho hq => hS.refs hinv ho hq
  -- The handles.
  have hhd : ∀ n hd, (M.toH.linkD db.D).handle? n = some hd →
      ∃ y o, M.tableOf y = some n ∧ hd = handleOfEntry (y, n) ∧ M.obj? n = some o ∧ o.node = y := by
    intro n hd hh
    obtain ⟨y, ht, rfl⟩ := hS.handle?_some db.D hh
    obtain ⟨o, ho, hn⟩ := hS.tbl y n ht
    exact ⟨y, o, ht, rfl, ho, hn⟩
  have hobjOf : ∀ y n, M.tableOf y = some n → (M.toH.linkD db.D).objOf n = some n := by
    intro y n ht
    unfold HMem.objOf
    rw [hS.handle? db.D ht]
    rfl
  have hptr : ∀ a o y, M.obj? a = some o → y ∈ pointees sp o.hist →
      ∃ q, (M.toH.linkObj db.D a (M.objH o)).ptr? y = some q := fun _ _ _ ho hy => hS.ptrOf ho hy
  have hunpin : ∀ a o, M.obj? a = some o → (inD db.D o.node || a == M.root) = false →
      inD db.D o.node = false ∧ written sp o.node = true := fun _ _ ho hp => hS.unpin ho hp
  have hheinv : HEInv sp db db.S k (M.toH.linkD db.D) := by
    refine
      { len := hinv.len
        pre := List.prefix_refl _
        sEq := hS.sEq
        freshO := fun a ha => by rw [hS.obj? db.D, hS.fresh a ha]; rfl
        freshH := ?_
        objNodup := ?_
        hNodup := ?_
        root := ?_
        tbl := ?_
        liveW := ?_
        cc := ?_
        pos := ?_
        dCanon := fun y hy => by rw [hcan]; exact hS.dCanon y hy
        snap := ?_
        ruleR := ?_
        wver := ?_
        rver := ?_
        slots := ?_
        live := ?_ }
    · intro n hn
      cases hh : (M.toH.linkD db.D).handle? n with
      | none => rfl
      | some hd =>
        exfalso
        obtain ⟨y, o, -, -, ho, -⟩ := hhd n hd hh
        rw [hS.fresh n hn] at ho; cases ho
    · rw [HMem.linkD_keys, Mem.toH_objs, List.map_map]
      exact (List.Sublist.map _ List.filter_sublist).nodup hS.nodup
    · show (M.toH.handles.map (·.1)).Nodup
      rw [Mem.toH_handles, List.map_map]
      have hinj : ∀ x ∈ M.table, ∀ z ∈ M.table, x.2 = z.2 → x = z := by
        intro x hx z hz hxz
        obtain ⟨y1, a1⟩ := x
        obtain ⟨y2, a2⟩ := z
        simp only at hxz
        subst hxz
        have h1 := lookup_of_mem M.table hS.tblNodup (y1, a1) hx
        have h2 := lookup_of_mem M.table hS.tblNodup (y2, a1) hz
        obtain ⟨o1, ho1, hn1⟩ := hS.tbl y1 a1 h1
        obtain ⟨o2, ho2, hn2⟩ := hS.tbl y2 a1 h2
        rw [ho1, Option.some.injEq] at ho2
        subst ho2
        rw [← hn1, hn2]
      exact nodup_map_of_inj _ M.table (nodup_of_map _ hS.tblNodup) (fun x hx z hz h => hinj x hx z hz h)
    · obtain ⟨-, o0, ho0, hn0⟩ := hS.root
      obtain ⟨e1, -, -, -, e5, -⟩ := hcore M.root o0
      refine ⟨M.toH.linkObj db.D M.root (M.objH o0), hfw M.root o0 ho0, ?_, ?_⟩
      · rw [e5]; exact (hS.canon _ o0 ho0).1
      · rw [e1, hn0]
    · refine ⟨fun y n hy => ?_, hS.tblNodup, fun n hd hh _ => ?_, fun n hd hh hdd => ?_, fun a o' ho' => ?_,
        fun a o' y p n ho' hp hpn => ?_⟩
      · obtain ⟨o, ho, hon⟩ := hS.tbl y n hy
        exact ⟨handleOfEntry (y, n), n, _, hS.handle? db.D hy, rfl, rfl, rfl, hfw n o ho,
          by rw [(hcore n o).1, hon]⟩
      · obtain ⟨y, o, ht, rfl, -⟩ := hhd n hd hh
        exact ht
      · obtain ⟨y, o, ht, rfl, -⟩ := hhd n hd hh
        cases hdd
      · obtain ⟨o, ho, rfl⟩ := hback a o' ho'
        have ht := (hS.canon a o ho).2
        refine ⟨a, by rw [(hcore a o).1]; exact ht, hobjOf o.node a ht⟩
      · obtain ⟨o, ho, rfl⟩ := hback a o' ho'
        rcases (hS.ptr_cases hinv db.D ho hp).1 with ⟨b, hb, hc⟩ | ⟨hn, -⟩
        · rw [hb, Option.some.injEq] at hpn
          subst hpn
          exact ⟨_, hS.handle? db.D ((M.canonicalOf_eq_some y b).mp hc).1, rfl⟩
        · rw [hn] at hpn; cases hpn
    · intro n hd hh _
      obtain ⟨y, o, -, rfl, -⟩ := hhd n hd hh
      rfl
    · intro a o' ho' _
      obtain ⟨o, ho, rfl⟩ := hback a o' ho'
      obtain ⟨e1, e2, e3, e4, -⟩ := hcore a o
      rw [e1, e2, e3, e4]
      exact hS.cc a o ho
    · intro a o' ho' _
      obtain ⟨o, ho, rfl⟩ := hback a o' ho'
      obtain ⟨e1, -, -, -, -, e6⟩ := hcore a o
      rw [e1, e6]
      exact hS.pos a o ho
    · intro a o' ho' hc
      obtain ⟨o, ho, rfl⟩ := hback a o' ho'
      rw [(hcore a o).2.2.2.2.1, (hS.canon a o ho).1] at hc
      cases hc
    · intro n hd b o' w hh hb ho' hc _
      obtain ⟨o, ho, rfl⟩ := hback b o' ho'
      rw [(hcore b o).2.2.2.2.1, (hS.canon b o ho).1] at hc
      cases hc
    · intro n hd w hh hw
      obtain ⟨y, o, -, rfl, -⟩ := hhd n hd hh
      cases hw
    · intro a o' y p r ho' hp hr
      obtain ⟨o, ho, rfl⟩ := hback a o' ho'
      exact (hS.ptr_cases hinv db.D ho hp).2 r hr
    · intro a o' ho' hrel y hy
      obtain ⟨o, ho, rfl⟩ := hback a o' ho'
      obtain ⟨e1, -, -, e4, -⟩ := hcore a o
      rw [e4] at hy
      obtain ⟨q, hq⟩ := hptr a o y ho hy
      refine ⟨q, hq, fun _ => (hrec a o y q ho hq).1, fun hyD => Or.inl ?_⟩
      cases hp : (inD db.D o.node || a == M.root)
      · exfalso
        obtain ⟨hxD, hw⟩ := hunpin a o ho hp
        obtain ⟨-, -, hreach⟩ := hrel
        rw [e1] at hreach
        rcases hreach with hrk | hxD'
        · obtain ⟨n, hn, hh, -⟩ := hS.cc a o ho
          have := (hlog.clean o.node n hw hrk hn hxD y (by rw [← hh]; exact hy)).1
          rw [hyD] at this; cases this
        · rw [hxD] at hxD'; cases hxD'
      · obtain ⟨b, hb, hc⟩ := hpinD a o y q ho hq hp hyD
        exact (hS.holds db.D hc q hb).1
    · intro a o' ho' hc hr y hy
      obtain ⟨o, ho, rfl⟩ := hback a o' ho'
      obtain ⟨e1, -, -, e4, -⟩ := hcore a o
      rw [e4] at hy
      rw [e1] at hr
      obtain ⟨q, hq⟩ := hptr a o y ho (mem_pointees_of_live' hls hy)
      refine ⟨q, hq, fun hyD => ?_, fun _ => (hrec a o y q ho hq).1⟩
      cases hp : (inD db.D o.node || a == M.root)
      · exfalso
        obtain ⟨hxD, hw⟩ := hunpin a o ho hp
        obtain ⟨n, hn, hh, -⟩ := hS.cc a o ho
        have hyn : y ∈ sp.live (n.hist.upTo k) := by
          rw [upTo_of_forall _ _ (hinv.times _ n hn), ← hh]; exact hy
        obtain ⟨e, he, hye⟩ := hls _ _ hy
        obtain ⟨m', hm', hlt⟩ := hinv.ptrs o.node n hn e (by rw [← hh]; exact he) y hye
        have hyr : y ∈ reachFrom sp db.P k o.node n :=
          reachFrom_child_sub sp hyn hm' hlt y (self_mem_reachFrom sp _ k y m')
        rw [hlog.closed o.node n y hw hr hn hyD hyr] at hxD
        cases hxD
      · obtain ⟨b, hb, hc⟩ := hpinD a o y q ho hq hp hyD
        exact (hS.holds db.D hc q hb).1
  refine ⟨hheinv, ?_, ?_⟩
  · intro a o' y p ho' hp
    obtain ⟨o, ho, rfl⟩ := hback a o' ho'
    rcases (hrec a o y p ho hp).2 with hc | ⟨-, hsr⟩
    · exact Or.inl hc
    · exact Or.inr hsr
  · intro o' y p ho' hp hyD
    obtain ⟨o, ho, rfl⟩ := hback _ o' ho'
    obtain ⟨b, hb, hc⟩ := hpinD _ o y p ho hp (by simp only [Bool.or_eq_true]; exact Or.inr (beq_self_eq_true _)) hyD
    exact (hS.holds db.D hc p hb).2.1

end Handles

section Startup

variable {sp : Spec V T} {al : Algo V T} {ts : List T}

/-- The startup with handles from the stream after T(k) gives a memory with the
invariant with handles; every pointer holds a canonical object or has its
pointee's latest version as its slow path's reference; and the root's pointers to
the nodes of D hold canonical objects. -/
theorem heinv_startup (hok : RunOK sp al ts) (hph : PhysRunOK sp al ts) (hj : al.stillDirty = javaTest sp)
    (hmk : al.mark = true) (hev : EvictRunOK sp al ts) {k : Nat} (hk : k ≤ ts.length) :
    HEInv sp (st sp al ts k) (st sp al ts k).S k (handleStartup sp (st sp al ts k).S) ∧
      (∀ a o y p, (handleStartup sp (st sp al ts k).S).obj? a = some o → o.ptr? y = some p →
        (handleStartup sp (st sp al ts k).S).holdsCanonical p = true ∨
          (handleStartup sp (st sp al ts k).S).slowRef (st sp al ts k).S y p =
            ((st sp al ts k).S.lv y).map (·.recNo)) ∧
      (∀ o y p, (handleStartup sp (st sp al ts k).S).obj? (handleStartup sp (st sp al ts k).S).root = some o →
        o.ptr? y = some p → inD (st sp al ts k).D y = true →
        (handleStartup sp (st sp al ts k).S).holdsCanonical p = true) := by
  have hst : AlgOK sp al := algOK_of sp al (Or.inl hj)
  have hinv := inv_st sp al ts hok hst k hk
  have hD : (startup sp (st sp al ts k).S).D = (st sp al ts k).D := (T1_strong sp al ts hok hst hk).2
  unfold handleStartup
  rw [hD]
  exact (startMem_st hok hph hj hmk hev hk).heinv hinv hok.1.liveSub (evLogic_st sp al ts hok hj hmk hev k hk)

/-- The startup with handles from R(0) gives a memory with the invariant. -/
theorem heinv_init (hok : RunOK sp al ts) (hph : PhysRunOK sp al ts) (hj : al.stillDirty = javaTest sp)
    (hmk : al.mark = true) (hev : EvictRunOK sp al ts) :
    HEInv sp (init sp) (init sp).S 0 (handleStartup sp (init sp).S) :=
  (heinv_startup hok hph hj hmk hev (Nat.zero_le _)).1

end Startup

end SIS
