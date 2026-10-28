/-
Proofs about reclaim with handles (bergdb 005-62), part 2 of T12 over handles:
the startup with handles from a stream cut safely is the startup with handles
from the whole stream but for the virtual root's object (`handleStartup_sim`).
The startup with handles is `Mem.toH` and rule 4 with handles on Evict.lean's
startup memory before rule 4, where the two startups are already the same but
for the root's object (`sectionPos_sim`, SIS/Proof/CutLaterStart.lean); `Mem.toH`
and rule 4 keep that. The two root objects agree from the first available time
on (`RootRelH`, `RootRel` over handles).
-/
import SIS.Proof.HandleCutLater
import SIS.Proof.CutLaterStart

set_option linter.unusedSectionVars false

namespace SIS

variable {V T : Type} [DecidableEq V]

/-! ## A memory with handles with another object for the root -/

/-- The memory with handles m with object oc at the root's address
(`Mem.withRoot` over handles). -/
def HMem.withRoot (m : HMem V) (oc : HObj V) : HMem V :=
  { m with objs := m.objs.map (fun p => if p.1 == m.root then (m.root, oc) else p) }

section Basic

variable {m : HMem V} {oc : HObj V}

@[simp] theorem HMem.withRoot_handles : (m.withRoot oc).handles = m.handles := rfl
@[simp] theorem HMem.withRoot_table : (m.withRoot oc).table = m.table := rfl
@[simp] theorem HMem.withRoot_s : (m.withRoot oc).s = m.s := rfl
@[simp] theorem HMem.withRoot_root : (m.withRoot oc).root = m.root := rfl
@[simp] theorem HMem.withRoot_nextObj : (m.withRoot oc).nextObj = m.nextObj := rfl
@[simp] theorem HMem.withRoot_nextHandle : (m.withRoot oc).nextHandle = m.nextHandle := rfl

theorem HMem.withRoot_obj? (a : Nat) :
    (m.withRoot oc).obj? a = if a = m.root then (m.obj? m.root).map (fun _ => oc) else m.obj? a := by
  unfold HMem.withRoot HMem.obj?
  exact lookup_map_set m.objs m.root a oc

theorem HMem.withRoot_obj?_ne {a : Nat} (hne : a ≠ m.root) : (m.withRoot oc).obj? a = m.obj? a := by
  rw [HMem.withRoot_obj?]; simp [hne]

theorem HMem.withRoot_obj?_root {oe : HObj V} (he : m.obj? m.root = some oe) :
    (m.withRoot oc).obj? m.root = some oc := by
  rw [HMem.withRoot_obj?]; simp [he]

theorem HMem.withRoot_canonicalOf {oe : HObj V} (he : m.obj? m.root = some oe)
    (hc : oc.canonical = oe.canonical) (y : NodeId) : (m.withRoot oc).canonicalOf y = m.canonicalOf y := by
  unfold HMem.canonicalOf HMem.tableOf HMem.objOf HMem.handle?
  simp only [HMem.withRoot_table, HMem.withRoot_handles]
  cases (m.table.lookup y).bind (fun n => (m.handles.lookup n).bind (·.obj)) with
  | none => rfl
  | some b =>
    simp only
    by_cases hb : b = m.root
    · subst hb
      rw [HMem.withRoot_obj?_root he, he]
      simp [hc]
    · rw [HMem.withRoot_obj?_ne hb]

end Basic

/-! ## The two root objects -/

/-- The root's object after a restart with handles from a cut stream (oc) and
after the restart from the whole stream (oe), each with the transactions since:
the same but for the history and the pointers of the root children that only
times before f need (`RootRel` over handles). Without a virtual root, the same
object. -/
structure RootRelH (sp : Spec V T) (f : Time) (oc oe : HObj V) : Prop where
  nv : sp.virt = false → oc = oe
  node : oc.node = oe.node
  level : oc.level = oe.level
  isData : oc.isData = oe.isData
  canonical : oc.canonical = oe.canonical
  pos : oc.pos = oe.pos
  live : ∀ t, f ≤ t → sp.live (oc.hist.upTo t) = sp.live (oe.hist.upTo t)
  ptrs : ∀ y, y ∈ pointees sp oc.hist → oc.ptr? y = oe.ptr? y
  noPtr : sp.virt = true → ∀ y, y ∉ pointees sp oc.hist → oc.ptr? y = none
  vals : sp.virt = true → ∀ e ∈ oc.hist, ∃ z, e.val = sp.rootVal z
  /-- oe has pointers for pointees of its history only. -/
  keysE : sp.virt = true → ∀ y, (oe.ptr? y).isSome = true → y ∈ pointees sp oe.hist

section Rel

variable {sp : Spec V T} {f : Time}

/-- The objects with handles of two related root objects. -/
theorem RootRel.objH {oc oe : Obj V} (hr : RootRel sp f oc oe) (m : Mem V) :
    RootRelH sp f (m.objH oc) (m.objH oe) := by
  have hptr : ∀ (o : Obj V) y, (m.objH o).ptr? y = (o.slot? y).map (fun sl => (m.ptrOfH (y, sl)).2) :=
    fun o y => Mem.objH_ptr? m o y
  refine ⟨fun hv => by rw [hr.nv hv], hr.node, hr.level, hr.isData, hr.canonical, hr.pos, hr.live,
    fun y hy => ?_, fun hv y hy => ?_, hr.vals, fun hv y hy => ?_⟩
  · rw [hptr, hptr, hr.slots y hy]
  · rw [hptr, hr.noSlot hv y hy]; rfl
  · rw [hptr] at hy
    apply hr.keysE hv y
    cases hs : oe.slot? y with
    | none => rw [hs] at hy; cases hy
    | some _ => rfl

/-- Rule 4 with handles on two related root objects. -/
theorem RootRelH.linkObj {oc oe : HObj V} (hr : RootRelH sp f oc oe) (m : HMem V) (D : Dirty) (a : Nat) :
    RootRelH sp f (m.linkObj D a oc) (m.linkObj D a oe) := by
  have hcond : (oc.canonical && (inD D oc.node || a == m.root)) =
      (oe.canonical && (inD D oe.node || a == m.root)) := by rw [hr.canonical, hr.node]
  have hcore : ∀ o : HObj V, (m.linkObj D a o).core = o.core := fun o => HMem.linkObj_core m D a o
  have hhist : ∀ o : HObj V, (m.linkObj D a o).hist = o.hist := fun o => congrArg (fun c => c.2.2.2.1) (hcore o)
  have hnode : ∀ o : HObj V, (m.linkObj D a o).node = o.node := fun o => congrArg (fun c => c.1) (hcore o)
  have hlevel : ∀ o : HObj V, (m.linkObj D a o).level = o.level := fun o => congrArg (fun c => c.2.1) (hcore o)
  have hdata : ∀ o : HObj V, (m.linkObj D a o).isData = o.isData :=
    fun o => congrArg (fun c => c.2.2.1) (hcore o)
  have hcan : ∀ o : HObj V, (m.linkObj D a o).canonical = o.canonical :=
    fun o => congrArg (fun c => c.2.2.2.2.1) (hcore o)
  have hpos : ∀ o : HObj V, (m.linkObj D a o).pos = o.pos := fun o => congrArg (fun c => c.2.2.2.2.2) (hcore o)
  refine ⟨fun hv => by rw [hr.nv hv], by rw [hnode, hnode, hr.node], by rw [hlevel, hlevel, hr.level],
    by rw [hdata, hdata, hr.isData], by rw [hcan, hcan, hr.canonical], by rw [hpos, hpos, hr.pos],
    fun t ht => by rw [hhist, hhist]; exact hr.live t ht, fun y hy => ?_, fun hv y hy => ?_,
    fun hv e he => hr.vals hv e (by rw [← hhist]; exact he), fun hv y hy => ?_⟩
  · rw [hhist] at hy
    rw [HMem.linkObj_ptr?, HMem.linkObj_ptr?, hcond, hr.ptrs y hy]
  · rw [hhist] at hy
    rw [HMem.linkObj_ptr?, hr.noPtr hv y hy]
    split <;> rfl
  · rw [hhist]
    apply hr.keysE hv y
    rw [HMem.linkObj_ptr?] at hy
    split at hy
    · cases hq : oe.ptr? y with
      | none => rw [hq] at hy; cases hy
      | some _ => rfl
    · exact hy

end Rel

/-! ## `Mem.toH` and rule 4 with another root object -/

section Transport

/-- A filter on keys and a map on values commute with setting the value at key
r. -/
theorem filter_map_set_root {β γ : Type} (P : Nat → Bool) (g : β → γ) (r : Nat) (x : β) :
    ∀ (l : List (Nat × β)), ((l.map (fun p => if p.1 == r then (r, x) else p)).filter (fun p => P p.1)).map
        (fun p => (p.1, g p.2)) =
      ((l.filter (fun p => P p.1)).map (fun p => (p.1, g p.2))).map
        (fun p => if p.1 == r then (r, g x) else p) := by
  intro l
  have hf : ∀ p : Nat × β, (if p.1 == r then (r, x) else p).1 = p.1 := by
    intro p
    by_cases hp : p.1 = r
    · simp [hp]
    · simp [hp]
  rw [List.filter_map, List.map_map, List.map_map]
  have hfil : List.filter ((fun p => P p.1) ∘ (fun p => if p.1 == r then (r, x) else p)) l =
      List.filter (fun p => P p.1) l := by
    apply List.filter_congr
    intro p _
    simp only [Function.comp, hf]
  rw [hfil]
  apply List.map_congr_left
  intro p _
  by_cases hp : p.1 = r
  · simp [Function.comp, hp]
  · simp [Function.comp, hp]

theorem HMem.ext' {m1 m2 : HMem V} (h1 : m1.objs = m2.objs) (h2 : m1.handles = m2.handles)
    (h3 : m1.table = m2.table) (h4 : m1.s = m2.s) (h5 : m1.root = m2.root) (h6 : m1.nextObj = m2.nextObj)
    (h7 : m1.nextHandle = m2.nextHandle) : m1 = m2 := by
  cases m1; cases m2; simp_all

/-- `Mem.toH` of a memory with another root object, of the same position: the
memory with handles with that object's object for the root. -/
theorem Mem.toH_withRoot {M : Mem V} {oc oe : Obj V} (hra : M.obj? M.root = some oe) (hpos : oc.pos = oe.pos) :
    (M.withRoot oc).toH = M.toH.withRoot (M.objH oc) := by
  -- The objects with handles of the two memories are the same.
  have hptr : (M.withRoot oc).ptrOfH = M.ptrOfH := by
    funext q
    unfold Mem.ptrOfH
    cases q.2 with
    | mem a =>
      simp only [withRoot_table]
      by_cases ha : a = M.root
      · subst ha
        rw [withRoot_obj?_root hra, hra]
        simp only [Option.bind_some, hpos]
        rfl
      · rw [withRoot_obj?_ne ha]
        rfl
    | stream r => rfl
  have hobjH : (M.withRoot oc).objH = M.objH := by
    funext o
    unfold Mem.objH
    rw [hptr]
  have hheldW : (M.withRoot oc).heldA = M.heldA := rfl
  have h1 := filter_map_set_root M.heldA M.objH M.root oc M.objs
  refine HMem.ext' ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [Mem.toH_objs, hheldW, hobjH]
    unfold HMem.withRoot
    rw [Mem.toH_objs]
    exact h1
  all_goals rfl

/-- Rule 4 with handles on a memory with another root object, as canonical as
the old one: rule 4 on the memory, with the new object linked for the root. -/
theorem HMem.linkD_withRoot {m : HMem V} {oc oe : HObj V} (hra : m.obj? m.root = some oe)
    (hc : oc.canonical = oe.canonical) (D : Dirty) :
    (m.withRoot oc).linkD D = (m.linkD D).withRoot (m.linkObj D m.root oc) := by
  have hlp : (m.withRoot oc).linkPtr = m.linkPtr := by
    funext q
    unfold HMem.linkPtr
    rw [HMem.withRoot_canonicalOf hra hc]
    rfl
  have hlo : (m.withRoot oc).linkObj D = m.linkObj D := by
    funext a o
    unfold HMem.linkObj
    rw [hlp, HMem.withRoot_root]
  refine HMem.ext' ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [HMem.linkD_objs, hlo]
    show (m.objs.map (fun p => if p.1 == m.root then (m.root, oc) else p)).map
        (fun p => (p.1, m.linkObj D p.1 p.2)) =
      ((m.linkD D).objs).map (fun p => if p.1 == m.root then (m.root, m.linkObj D m.root oc) else p)
    rw [HMem.linkD_objs]
    simp only [List.map_map]
    apply List.map_congr_left
    intro p _
    by_cases hp : p.1 = m.root
    · simp [Function.comp, hp]
    · simp [Function.comp, hp]
  all_goals rfl

end Transport

/-! ## The startup with handles from a stream cut safely -/

section Start

variable {sp : Spec V T} {al : Algo V T} {ts : List T}

/-- The startup with handles from a stream cut safely: the memory of the startup
with handles from the whole stream but for the root's object, which holds the
root's history of the logical startup from the cut stream. -/
theorem handleStartup_sim (hok : RunOK sp al ts) (hph : PhysRunOK sp al ts) (hev : EvictRunOK sp al ts)
    (hj : al.stillDirty = javaTest sp) (hmk : al.mark = true) (hex : ExecRootOK sp) (hvl : VirtLiveOK sp)
    {k c : Nat} (hk : k ≤ ts.length) (hcut : CutOK sp c (st sp al ts k) k) :
    ∃ oc oe, handleStartup sp (cutStream c (st sp al ts k).S) =
        (handleStartup sp (st sp al ts k).S).withRoot oc ∧
      (handleStartup sp (st sp al ts k).S).obj? (handleStartup sp (st sp al ts k).S).root = some oe ∧
      RootRelH sp (lastFa (st sp al ts k).S) oc oe ∧
      ∀ n, (startup sp (cutStream c (st sp al ts k).S)).P.get? root = some n → oc.hist = n.hist := by
  obtain ⟨oc, oe, hsec, hraP, hrr, hist⟩ := sectionPos_sim hok hph hev hj hmk hex hvl hk hcut
  have hfs := st_fa_le sp al ts hk
  have hcs : c ≤ lastSp (st sp al ts k).S := Nat.le_trans hcut.1 hfs
  have hD : (startup sp (cutStream c (st sp al ts k).S)).D = (startup sp (st sp al ts k).S).D := by
    rw [startup, startup, startup_D, startup_D, sectionD_cut hcs]
  -- The root's object is in the node table.
  have ht := (startMem_st hok hph hj hmk hev hk).root.1
  generalize hM1 : (lazyStartup sp (st sp al ts k).S).sectionPos (st sp al ts k).S = M1 at hsec hraP ht
  have hheld : M1.heldA M1.root = true := by
    unfold Mem.heldA
    exact List.any_eq_true.mpr ⟨(_, M1.root), mem_of_lookup _ _ _ ht, by simp⟩
  have hraH : M1.toH.obj? M1.toH.root = some (M1.objH oe) := by
    show M1.toH.obj? M1.root = _
    rw [Mem.toH_obj?, hheld, hraP]
    rfl
  have hcanH : (M1.objH oc).canonical = (M1.objH oe).canonical := hrr.canonical
  refine ⟨M1.toH.linkObj (startup sp (st sp al ts k).S).D M1.root (M1.objH oc),
    M1.toH.linkObj (startup sp (st sp al ts k).S).D M1.root (M1.objH oe), ?_, ?_, ?_, ?_⟩
  · unfold handleStartup
    rw [hM1, hsec, hD, Mem.toH_withRoot hraP hrr.pos, HMem.linkD_withRoot hraH hcanH]
    rfl
  · unfold handleStartup
    rw [hM1]
    show (M1.toH.linkD (startup sp (st sp al ts k).S).D).obj? M1.root = _
    rw [HMem.linkD_obj?]
    show (M1.toH.obj? M1.toH.root).map _ = _
    rw [hraH]
    rfl
  · exact (hrr.objH M1).linkObj M1.toH (startup sp (st sp al ts k).S).D M1.root
  · intro n hn
    have e := HMem.linkObj_core M1.toH (startup sp (st sp al ts k).S).D M1.root (M1.objH oc)
    have e4 : (M1.toH.linkObj (startup sp (st sp al ts k).S).D M1.root (M1.objH oc)).hist = oc.hist :=
      congrArg (fun c => c.2.2.2.1) e
    rw [e4]
    exact hist n hn

end Start

end SIS
