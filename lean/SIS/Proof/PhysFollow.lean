/-
Proofs about the physical layer, part 4: one first touch keeps the invariant
(bergdb item 001, WP L3).
-/
import SIS.Proof.PhysInv

set_option linter.unusedSectionVars false

namespace SIS

variable {V T : Type} [DecidableEq V]

/-! ### Handles -/

theorem nodup_setObj_keys (m : Mem V) (h : Nat) (o : Obj V) (hnd : (m.objs.map (·.1)).Nodup) :
    ((m.setObj h o).objs.map (·.1)).Nodup := by
  unfold Mem.setObj
  simp only [List.map_cons, List.nodup_cons]
  refine ⟨?_, ?_⟩
  · simp
  · exact (List.Sublist.map _ List.filter_sublist).nodup hnd

theorem lookup_none_of_not_mem {β : Type} {l : List (Nat × β)} {a : Nat} (h : a ∉ l.map (·.1)) :
    List.lookup a l = none := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    obtain ⟨b, x⟩ := p
    simp only [List.map_cons, List.mem_cons, not_or] at h
    rw [lookup_cons_eq]
    simp only [h.1, ↓reduceIte]
    exact ih h.2

theorem lookup_isSome_of_mem {β : Type} {l : List (Nat × β)} {a : Nat} (h : a ∈ l.map (·.1)) :
    (List.lookup a l).isSome := by
  induction l with
  | nil => cases h
  | cons p l ih =>
    obtain ⟨b, x⟩ := p
    rw [lookup_cons_eq]
    by_cases hb : a = b
    · simp [hb]
    · simp only [hb, ↓reduceIte]
      simp only [List.map_cons, List.mem_cons] at h
      rcases h with h | h
      · exact absurd h hb
      · exact ih h

theorem nodup_addObj_keys (m : Mem V) (o : Obj V) (hnd : (m.objs.map (·.1)).Nodup)
    (hfr : ∀ h, m.next ≤ h → m.obj? h = none) : ((m.addObj o).1.objs.map (·.1)).Nodup := by
  unfold Mem.addObj
  simp only [List.map_cons, List.nodup_cons]
  refine ⟨?_, hnd⟩
  intro hmem
  have h1 := lookup_isSome_of_mem hmem
  have h2 := hfr m.next (Nat.le_refl _)
  unfold Mem.obj? at h2
  rw [h2] at h1
  cases h1

theorem lt_next_of_obj? {m : Mem V} (hfr : ∀ h, m.next ≤ h → m.obj? h = none) {h : Nat} {o : Obj V}
    (ho : m.obj? h = some o) : h < m.next := by
  apply Nat.lt_of_not_le
  intro hle
  rw [hfr h hle] at ho; cases ho

/-! ### Swizzling a slot -/

section Swizzle

variable {sp : Spec V T} {db : DB V T}

theorem setObj_sameCore (m : Mem V) {hp : Nat} {op op' : Obj V} (hop : m.obj? hp = some op)
    (hc : op'.core = op.core) : m.SameCore (m.setObj hp op') := by
  refine ⟨rfl, fun h => ?_⟩
  rw [Mem.obj?_setObj]
  split
  · rename_i hh; subst hh; rw [hop]; simp [hc]
  · rfl

theorem setSlot_core (o : Obj V) (y : NodeId) (sl : Slot) : (o.setSlot y sl).core = o.core := rfl

/-- Swizzling: the parent's slot for y names object h1. The invariant is kept if
h1 is the node table's object for y, and good enough for what the parent uses
the slot for. -/
theorem MemInv.swizzle {K : Nat} {m : Mem V} (hm : MemInv sp db K m)
    {hp : Nat} {op : Obj V} (hop : m.obj? hp = some op) {y : NodeId} {h1 : Nat}
    (hms : MemSlotOK m y h1)
    (hcan : op.canonical = true →
      (∀ t ≤ K, reachable sp db.P t op.node = true → y ∈ sp.live (op.hist.upTo t) →
        Readable sp db m K t h1 y) ∧
      (reachable sp db.P K op.node = true → y ∈ sp.live op.hist → SlotFresh db m y (Slot.mem h1)))
    (hsnap : op.canonical = false → ∀ w, SnapOK db m K hp op w →
      AtLeast m y h1 (ruleRRef db.S (lastSp db.S) y (w.ref? y)))
    (hsl : (op.slot? y).isSome) :
    MemInv sp db K (m.setObj hp (op.setSlot y (Slot.mem h1))) ∧
      m.SameCore (m.setObj hp (op.setSlot y (Slot.mem h1))) := by
  have hs := setObj_sameCore m hop (setSlot_core op y (Slot.mem h1))
  refine ⟨?_, hs⟩
  have hslot : ∀ y', (op.setSlot y (Slot.mem h1)).slot? y' =
      if y' = y then some (Slot.mem h1) else op.slot? y' := by
    intro y'
    rw [Obj.slot?_setSlot]
    split
    · rename_i hy; subst hy
      obtain ⟨sl0, h0⟩ := Option.isSome_iff_exists.mp hsl
      rw [h0]; rfl
    · rfl
  refine ⟨hm.sEq, hm.sK, ?_, nodup_setObj_keys m hp _ hm.nodup, ?_, ?_, ?_, ?_, ?_, ?_,
    fun d R x h1 h2 h3 h4 => by rw [hs.canonicalOf]; exact hm.coverGd d R x h1 h2 h3 h4,
    fun x w h1 h2 h3 => by rw [hs.canonicalOf]; exact hm.coverSec x w h1 h2 h3,
    fun x n e h1 h2 h3 h4 => by rw [hs.canonicalOf]; exact hm.coverNew x n e h1 h2 h3 h4⟩
  · intro h hh
    simp only [Mem.setObj_next] at hh
    have := lt_next_of_obj? hm.fresh hop
    rw [Mem.obj?_setObj_ne _ _ (by omega)]
    exact hm.fresh h hh
  · obtain ⟨ht, o, ho, hc, hn⟩ := hm.root
    obtain ⟨o', ho', e1, -, -, -, e5, -⟩ := hs.obj ho
    exact ⟨by rw [hs.tableOf]; exact ht, o', ho', by rw [e5, hc], by rw [e1, hn]⟩
  · intro y' h ht
    obtain ⟨o, ho, hn⟩ := hm.tbl y' h (by rw [← hs.tableOf]; exact ht)
    obtain ⟨o', ho', e1, -⟩ := hs.obj ho
    exact ⟨o', ho', by rw [e1, hn]⟩
  · intro h o' ho'
    obtain ⟨o, ho, e1, -⟩ := hs.symm.obj ho'
    rw [← e1]; exact hm.born h o ho
  · -- Canonical objects.
    intro h o' ho' hc'
    rw [Mem.obj?_setObj] at ho'
    split at ho'
    · rename_i hh
      subst hh
      cases ho'
      have hc0 : op.canonical = true := hc'
      obtain ⟨c1, c2, c3, c4, c5⟩ := hm.canon h op hop hc0
      obtain ⟨hcan1, hcan2⟩ := hcan hc0
      refine ⟨by rw [hs.tableOf]; exact c1, c2, c3, ?_, ?_⟩
      · intro t ht hr y' hy'
        rw [hslot]
        split
        · rename_i hy; subst hy
          exact ⟨_, rfl, Readable.congr hs (hcan1 t ht hr hy')⟩
        · obtain ⟨sl, hsl', hg⟩ := c4 t ht hr y' hy'
          exact ⟨sl, hsl', SlotGood.congr hs hg⟩
      · intro hr y' hy'
        rw [hslot]
        split
        · rename_i hy; subst hy
          exact ⟨_, rfl, SlotFresh.congr hs (hcan2 hr hy')⟩
        · obtain ⟨sl, hsl', hg⟩ := c5 hr y' hy'
          exact ⟨sl, hsl', SlotFresh.congr hs hg⟩
    · obtain ⟨c1, c2, c3, c4, c5⟩ := hm.canon h o' ho' hc'
      refine ⟨by rw [hs.tableOf]; exact c1, c2, c3, ?_, ?_⟩
      · intro t ht hr y' hy'
        obtain ⟨sl, hsl', hg⟩ := c4 t ht hr y' hy'
        exact ⟨sl, hsl', SlotGood.congr hs hg⟩
      · intro hr y' hy'
        obtain ⟨sl, hsl', hg⟩ := c5 hr y' hy'
        exact ⟨sl, hsl', SlotFresh.congr hs hg⟩
  · -- Snapshots.
    intro h o' ho' hc'
    rw [Mem.obj?_setObj] at ho'
    split at ho'
    · rename_i hh
      subst hh
      cases ho'
      have hc0 : op.canonical = false := hc'
      obtain ⟨w, hw, hss1, hss2⟩ := hm.snap h op hop hc0
      refine ⟨w, SnapOK.congr hs hw rfl rfl rfl rfl rfl, ?_, ?_⟩
      · intro y' hy'
        rw [hslot]
        split
        · rfl
        · exact hss1 y' hy'
      · intro y' sl hsl'
        rw [hslot] at hsl'
        split at hsl'
        · rename_i hy; subst hy
          cases hsl'
          exact Or.inr ⟨h1, rfl, AtLeast.congr hs (hsnap hc0 w hw)⟩
        · rcases hss2 y' sl hsl' with h2 | ⟨h', h2, h3⟩
          · exact Or.inl h2
          · exact Or.inr ⟨h', h2, AtLeast.congr hs h3⟩
    · obtain ⟨w, hw, hss1, hss2⟩ := hm.snap h o' ho' hc'
      refine ⟨w, SnapOK.congr hs hw rfl rfl rfl rfl rfl, hss1, ?_⟩
      intro y' sl hsl'
      rcases hss2 y' sl hsl' with h2 | ⟨h', h2, h3⟩
      · exact Or.inl h2
      · exact Or.inr ⟨h', h2, AtLeast.congr hs h3⟩
  · -- Memory slots.
    intro h o' y' h' ho' hsl'
    rw [Mem.obj?_setObj] at ho'
    split at ho'
    · rename_i hh
      subst hh
      cases ho'
      rw [hslot] at hsl'
      split at hsl'
      · rename_i hy; subst hy
        cases hsl'
        exact MemSlotOK.congr hs hms
      · exact MemSlotOK.congr hs (hm.memSlot h op y' h' hop hsl')
    · exact MemSlotOK.congr hs (hm.memSlot h o' y' h' ho' hsl')

end Swizzle

/-! ### Objects read from the stream -/

theorem lookup_map_pair {β : Type} (l : List NodeId) (f : NodeId → β) (y : NodeId) :
    List.lookup y (l.map (fun z => (z, f z))) = if y ∈ l then some (f y) else none := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.map_cons, lookup_cons_eq]
    by_cases hya : y = a
    · subst hya; simp
    · simp only [hya, ↓reduceIte, ih, List.mem_cons, false_or]

/-- The history of the object read from version w, cut back or not. -/
def cutHist (w : Version V) (cut : Option Nat) : History V :=
  match cut with
  | some s => w.hist.upTo s
  | none => w.hist

theorem Obj.ofVersion_fields (sp : Spec V T) (w : Version V) (cut : Option Nat) :
    (Obj.ofVersion sp w cut).node = w.node ∧ (Obj.ofVersion sp w cut).level = w.level ∧
    (Obj.ofVersion sp w cut).isData = w.isData ∧ (Obj.ofVersion sp w cut).hist = cutHist w cut ∧
    (Obj.ofVersion sp w cut).canonical = false ∧ (Obj.ofVersion sp w cut).pos = some w.recNo := by
  unfold Obj.ofVersion cutHist
  cases cut <;> simp

theorem Obj.ofVersion_slot? (sp : Spec V T) (w : Version V) (cut : Option Nat) (z : NodeId) :
    (Obj.ofVersion sp w cut).slot? z =
      if z ∈ pointees sp (cutHist w cut) then some (Slot.stream (w.ref? z)) else none := by
  unfold Obj.ofVersion Obj.slot? cutHist
  cases cut <;> simp only [] <;> exact lookup_map_pair _ _ z

/-! ### Memories that keep m but for node y's table entry -/

/-- m' keeps m's objects (and may add more), m's node table but for node y, and
every node's canonical object. -/
structure Mem.KeepY (m m' : Mem V) (y : NodeId) : Prop where
  obj : ∀ h o, m.obj? h = some o → m'.obj? h = some o
  tbl : ∀ z, z ≠ y → m'.tableOf z = m.tableOf z
  canon : ∀ z, m'.canonicalOf z = m.canonicalOf z

section KeepY

variable {sp : Spec V T} {db : DB V T} {m m' : Mem V} {y : NodeId} (hk : m.KeepY m' y)
include hk

theorem Mem.KeepY.le : m.Le m' := by
  refine ⟨fun h o ho => ⟨o, hk.obj h o ho, rfl, rfl, rfl, rfl, id, fun _ => rfl⟩, ?_⟩
  intro z h hc
  rw [hk.canon]; exact hc

/-- A snapshot stays one, if a cut snapshot of y is still the table's. -/
theorem SnapOK.keepY {K h : Nat} {o : Obj V} {w : Version V} (h1 : SnapOK db m K h o w)
    (hY : o.node = y → Uncut K o w ∨ m'.tableOf y = some h) : SnapOK db m' K h o w := by
  obtain ⟨r, hr1, hr2, hr3, hr4, hr5⟩ := h1
  refine ⟨r, hr1, hr2, hr3, hr4, ?_⟩
  rcases hr5 with h5 | ⟨h5, h6, h7, h8⟩
  · exact Or.inl h5
  · by_cases hy : o.node = y
    · rcases hY hy with h9 | h9
      · exact Or.inl h9
      · exact Or.inr ⟨h5, h6, by rw [hy]; exact h9, h8⟩
    · exact Or.inr ⟨h5, h6, by rw [hk.tbl _ hy]; exact h7, h8⟩

/-- The condition of `SnapOK.keepY`, for every object of m. -/
def CutsKept (db : DB V T) (m m' : Mem V) (K : Nat) (y : NodeId) : Prop :=
  ∀ h o w, m.obj? h = some o → o.node = y → SnapOK db m K h o w → Uncut K o w ∨ m'.tableOf y = some h

theorem Readable.keepY {K : Nat} {t : Time} {h : Nat} {z : NodeId}
    (hc : CutsKept db m m' K y) (h1 : Readable sp db m K t h z) : Readable sp db m' K t h z := by
  obtain ⟨o, ho, hz, hcan⟩ := h1
  refine ⟨o, hk.obj h o ho, hz, ?_⟩
  rcases hcan with h2 | ⟨w, hw, hg⟩
  · exact Or.inl h2
  · exact Or.inr ⟨w, SnapOK.keepY hk hw (fun hy => hc h o w ho hy hw), hg⟩

theorem SlotGood.keepY {K : Nat} {t : Time} {z : NodeId} {sl : Slot}
    (hc : CutsKept db m m' K y) (h1 : SlotGood sp db m K t z sl) : SlotGood sp db m' K t z sl := by
  cases sl with
  | mem h' => exact Readable.keepY hk hc h1
  | stream r =>
    rcases h1 with h1 | h1
    · left; rw [hk.canon]; exact h1
    · exact Or.inr h1

theorem SlotFresh.keepY {z : NodeId} {sl : Slot} (h1 : SlotFresh db m z sl) :
    SlotFresh db m' z sl := by
  cases sl with
  | mem h' =>
    obtain ⟨o, ho, hc⟩ := h1
    exact ⟨o, hk.obj h' o ho, hc⟩
  | stream r =>
    rcases h1 with h1 | h1
    · left; rw [hk.canon]; exact h1
    · exact Or.inr h1

theorem AtLeast.keepY {z : NodeId} {h : Nat} {r' : Option Nat} (h1 : AtLeast m z h r') :
    AtLeast m' z h r' := by
  obtain ⟨o, ho, hz, hc⟩ := h1
  exact ⟨o, hk.obj h o ho, hz, hc⟩

end KeepY

/-! ### Reading a version from the stream: the object is added and registered -/

section Load

variable {sp : Spec V T} {db : DB V T}

theorem register_none (m : Mem V) {h : Nat} {o : Obj V} (ho : m.obj? h = some o)
    (ht : m.tableOf o.node = none) : m.register h = (m.setTable o.node h, h) := by
  unfold Mem.register; rw [ho]; simp only [ht]

theorem register_some (m : Mem V) {h h0 : Nat} {o o0 : Obj V} (ho : m.obj? h = some o)
    (ht : m.tableOf o.node = some h0) (hne : h0 ≠ h) (ho0 : m.obj? h0 = some o0) :
    m.register h = if o.better o0 then (m.setTable o.node h, h) else (m, h0) := by
  unfold Mem.register; rw [ho]; simp only [ht]
  have : (h0 == h) = false := by simp [hne]
  simp only [this, Bool.false_eq_true, ↓reduceIte, ho0]

/-- The new object, added and entered in the node table for y (accepted by
`register`): the invariant is kept, if the table's old object for y is an older
snapshot. -/
theorem MemInv.load_accept {K k : Nat} {m : Mem V} (hm : MemInv sp db K m)
    (hctx : PCtx sp db k) {y : NodeId} {r'' : Nat} {w : Version V}
    (hw : db.S.versionAt r'' y = some w) (hnc : m.canonicalOf y = none)
    (hold : ∀ h0 o0, m.tableOf y = some h0 → m.obj? h0 = some o0 →
      o0.canonical = false ∧ ∃ p0, o0.pos = some p0 ∧ p0 < r'')
    (hborn : ∃ t ≤ K, reachable sp db.P t y = true) (cut : Option Nat)
    (hcut : ∀ s', cut = some s' → s' = lastSp db.S ∧ histAt db.P y K = [] ∧ db.S.lv y = some w)
    (hle : cut = none → ∀ e ∈ w.hist, e.time ≤ K) :
    MemInv sp db K ((m.addObj (Obj.ofVersion sp w cut)).1.setTable y m.next) ∧
      m.KeepY ((m.addObj (Obj.ofVersion sp w cut)).1.setTable y m.next) y := by
  obtain ⟨hwy, hwr, ny, hny, hwh, hwl, hwd⟩ := hctx.inv.version_node hw
  obtain ⟨f1, f2, f3, f4, f5, f6⟩ := Obj.ofVersion_fields sp w cut
  rw [hwy] at f1
  -- The memory after.
  obtain ⟨m', hm'⟩ : ∃ m', m' = (m.addObj (Obj.ofVersion sp w cut)).1.setTable y m.next := ⟨_, rfl⟩
  rw [← hm']
  have hobj : ∀ h, m'.obj? h = if h = m.next then some (Obj.ofVersion sp w cut) else m.obj? h := by
    intro h; rw [hm', Mem.obj?_setTable, Mem.obj?_addObj]
  have htab : ∀ z, m'.tableOf z = if z = y then some m.next else m.tableOf z := by
    intro z; rw [hm', Mem.tableOf_setTable, Mem.tableOf_addObj]
  have hold' : ∀ h o, m.obj? h = some o → m'.obj? h = some o := by
    intro h o ho
    rw [hobj]
    have := lt_next_of_obj? hm.fresh ho
    simp only [show h ≠ m.next by omega, ↓reduceIte]
    exact ho
  have hyr : y ≠ SIS.root := by
    intro hy
    obtain ⟨ht, o, ho, hc, -⟩ := hm.root
    have := (m.canonicalOf_eq_some SIS.root m.root).mpr ⟨ht, o, ho, hc⟩
    rw [← hy, hnc] at this; cases this
  have hcanon : ∀ z, m'.canonicalOf z = m.canonicalOf z := by
    intro z
    by_cases hz : z = y
    · subst hz
      rw [hnc, Mem.canonicalOf_eq_none]
      intro h o ht ho
      rw [htab] at ht
      simp only [↓reduceIte, Option.some.injEq] at ht
      subst ht
      rw [hobj] at ho
      simp only [↓reduceIte, Option.some.injEq] at ho
      rw [← ho]; exact f5
    · cases hc : m.canonicalOf z with
      | some h =>
        obtain ⟨ht, o, ho, hcan⟩ := (m.canonicalOf_eq_some z h).mp hc
        exact (m'.canonicalOf_eq_some z h).mpr ⟨by rw [htab]; simp only [hz, ↓reduceIte]; exact ht,
          o, hold' h o ho, hcan⟩
      | none =>
        rw [Mem.canonicalOf_eq_none] at hc ⊢
        intro h o ht ho
        rw [htab] at ht
        simp only [hz, ↓reduceIte] at ht
        obtain ⟨o0, ho0, -⟩ := hm.tbl z h ht
        rw [hold' h o0 ho0, Option.some.injEq] at ho
        subst ho
        exact hc h o0 ht ho0
  have hk : m.KeepY m' y := ⟨hold', fun z hz => by rw [htab]; simp [hz], hcanon⟩
  -- A cut snapshot of y in m is the table's old object, which is older: none.
  have hcuts : CutsKept db m m' K y := by
    intro h o w' ho hoy hsn
    obtain ⟨r0, hr0, hr0w, -, -, h5⟩ := hsn
    rcases h5 with h5 | ⟨-, hlv, ht, -⟩
    · exact Or.inl h5
    · exfalso
      rw [hoy] at ht hlv hr0w
      obtain ⟨hc0, p0, hp0, hlt⟩ := hold h o ht ho
      rw [hr0] at hp0
      cases hp0
      obtain ⟨-, hrec0, -⟩ := hctx.inv.version_node hr0w
      obtain ⟨v, hv, hle⟩ := hctx.inv.le_lv hw
      rw [hlv, Option.some.injEq] at hv
      subst hv
      omega
  refine ⟨⟨by rw [hm']; exact hm.sEq, hm.sK, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    fun d R x h1 h2 h3 h4 => by rw [hcanon]; exact hm.coverGd d R x h1 h2 h3 h4,
    fun x w h1 h2 h3 => by rw [hcanon]; exact hm.coverSec x w h1 h2 h3,
    fun x n e h1 h2 h3 h4 => by rw [hcanon]; exact hm.coverNew x n e h1 h2 h3 h4⟩, hk⟩
  · -- fresh
    intro h hh
    rw [hm'] at hh
    simp only [Mem.setTable_next, Mem.addObj_next] at hh
    rw [hobj]
    simp only [show h ≠ m.next by omega, ↓reduceIte]
    exact hm.fresh h (by omega)
  · -- nodup
    rw [hm', Mem.setTable_objs]
    exact nodup_addObj_keys m _ hm.nodup hm.fresh
  · -- root
    obtain ⟨ht, o, ho, hc, hn⟩ := hm.root
    rw [hm']
    simp only [Mem.setTable_root, Mem.addObj_root]
    rw [← hm']
    exact ⟨by rw [htab]; simp only [show SIS.root ≠ y from fun h => hyr h.symm, ↓reduceIte]; exact ht,
      o, hold' _ o ho, hc, hn⟩
  · -- tbl
    intro z h ht
    rw [htab] at ht
    by_cases hz : z = y
    · subst hz
      simp only [↓reduceIte, Option.some.injEq] at ht
      subst ht
      exact ⟨_, by rw [hobj]; simp, f1⟩
    · simp only [hz, ↓reduceIte] at ht
      obtain ⟨o, ho, hn⟩ := hm.tbl z h ht
      exact ⟨o, hold' h o ho, hn⟩
  · -- born
    intro h o ho
    rw [hobj] at ho
    split at ho
    · cases ho; rw [f1]; exact hborn
    · exact hm.born h o ho
  · -- canonical objects
    intro h o ho hc
    rw [hobj] at ho
    split at ho
    · cases ho; rw [f5] at hc; cases hc
    · obtain ⟨c1, c2, c3, c4, c5⟩ := hm.canon h o ho hc
      have hny : o.node ≠ y := by
        intro hoy
        have := (m.canonicalOf_eq_some o.node h).mpr ⟨c1, o, ho, hc⟩
        rw [hoy, hnc] at this; cases this
      refine ⟨by rw [htab]; simp only [hny, ↓reduceIte]; exact c1, c2, c3, ?_, ?_⟩
      · intro t ht hr z hz
        obtain ⟨sl, hsl, hg⟩ := c4 t ht hr z hz
        exact ⟨sl, hsl, SlotGood.keepY hk hcuts hg⟩
      · intro hr z hz
        obtain ⟨sl, hsl, hg⟩ := c5 hr z hz
        exact ⟨sl, hsl, SlotFresh.keepY hk hg⟩
  · -- snapshots
    intro h o ho hc
    rw [hobj] at ho
    split at ho
    · rename_i hh
      subst hh
      cases ho
      have hhist : Uncut K (Obj.ofVersion sp w cut) w ∨
          ((Obj.ofVersion sp w cut).hist = w.hist.upTo (lastSp db.S) ∧ db.S.lv y = some w ∧
            histAt db.P y K = []) := by
        unfold Uncut
        rw [f4]
        cases hcv : cut with
        | none => left; exact ⟨rfl, hle hcv⟩
        | some s' =>
          obtain ⟨hs', hh, hlv⟩ := hcut s' hcv
          right
          exact ⟨by rw [hs']; rfl, hlv, hh⟩
      refine ⟨w, ⟨r'', by rw [f6, hwr], by rw [f1]; exact hw, f2, f3, ?_⟩, ?_, ?_⟩
      · rcases hhist with h1 | ⟨h1, h2, h3⟩
        · exact Or.inl h1
        · exact Or.inr ⟨h1, by rw [f1]; exact h2, by rw [f1, htab]; simp, by rw [f1]; exact h3⟩
      · intro z hz
        rw [Obj.ofVersion_slot?, ← f4]
        simp [hz]
      · intro z sl hsl
        rw [Obj.ofVersion_slot?] at hsl
        split at hsl
        · cases hsl; exact Or.inl rfl
        · cases hsl
    · obtain ⟨w', hw', hss1, hss2⟩ := hm.snap h o ho hc
      refine ⟨w', SnapOK.keepY hk hw' (fun hy => hcuts h o w' ho hy hw'), hss1, ?_⟩
      intro z sl hsl
      rcases hss2 z sl hsl with h2 | ⟨h', h2, h3⟩
      · exact Or.inl h2
      · exact Or.inr ⟨h', h2, AtLeast.keepY hk h3⟩
  · -- memory slots
    intro h o z h' ho hsl
    rw [hobj] at ho
    split at ho
    · cases ho
      rw [Obj.ofVersion_slot?] at hsl
      split at hsl <;> cases hsl
    · obtain ⟨o', ho', hz, hc⟩ := hm.memSlot h o z h' ho hsl
      refine ⟨o', hold' h' o' ho', hz, ?_⟩
      by_cases hzy : z = y
      · subst hzy
        right
        rcases hc with hc | ⟨hcan, h0, o0, p, p0, ht, ho0, hp, hp0, hlt⟩
        · obtain ⟨hc0, p0, hp0, hlt⟩ := hold h' o' hc ho'
          exact ⟨hc0, m.next, Obj.ofVersion sp w cut, p0, r'', by rw [htab]; simp,
            by rw [hobj]; simp, hp0, by rw [f6, hwr], hlt⟩
        · obtain ⟨-, p1, hp1, hlt1⟩ := hold h0 o0 ht ho0
          rw [hp0, Option.some.injEq] at hp1
          subst hp1
          exact ⟨hcan, m.next, Obj.ofVersion sp w cut, p, r'', by rw [htab]; simp,
            by rw [hobj]; simp, hp, by rw [f6, hwr], by omega⟩
      · rcases hc with hc | ⟨hcan, h0, o0, p, p0, ht, ho0, hp, hp0, hlt⟩
        · left; rw [htab]; simp only [hzy, ↓reduceIte]; exact hc
        · right
          exact ⟨hcan, h0, o0, p, p0, by rw [htab]; simp only [hzy, ↓reduceIte]; exact ht,
            hold' h0 o0 ho0, hp, hp0, hlt⟩


/-- A new object that is not entered in the node table (`register` keeps the
table's object, which happens only for a data node): the invariant is kept. -/
theorem MemInv.load_orphan {K k : Nat} {m : Mem V} (hm : MemInv sp db K m)
    (hctx : PCtx sp db k) {y : NodeId} {r'' : Nat} {w : Version V}
    (hw : db.S.versionAt r'' y = some w)
    (hborn : ∃ t ≤ K, reachable sp db.P t y = true) (cut : Option Nat) (hcut : cut = none)
    (hle : ∀ e ∈ w.hist, e.time ≤ K) :
    MemInv sp db K (m.addObj (Obj.ofVersion sp w cut)).1 ∧
      m.KeepY (m.addObj (Obj.ofVersion sp w cut)).1 y := by
  subst hcut
  obtain ⟨hwy, hwr, -⟩ := hctx.inv.version_node hw
  obtain ⟨f1, f2, f3, f4, f5, f6⟩ := Obj.ofVersion_fields sp w none
  rw [hwy] at f1
  obtain ⟨m', hm'⟩ : ∃ m', m' = (m.addObj (Obj.ofVersion sp w none)).1 := ⟨_, rfl⟩
  rw [← hm']
  have hobj : ∀ h, m'.obj? h = if h = m.next then some (Obj.ofVersion sp w none) else m.obj? h := by
    intro h; rw [hm', Mem.obj?_addObj]
  have htab : ∀ z, m'.tableOf z = m.tableOf z := by intro z; rw [hm', Mem.tableOf_addObj]
  have hold' : ∀ h o, m.obj? h = some o → m'.obj? h = some o := by
    intro h o ho
    rw [hobj]
    have := lt_next_of_obj? hm.fresh ho
    simp only [show h ≠ m.next by omega, ↓reduceIte]
    exact ho
  have hcanon : ∀ z, m'.canonicalOf z = m.canonicalOf z := by
    intro z
    cases hc : m.canonicalOf z with
    | some h =>
      obtain ⟨ht, o, ho, hcan⟩ := (m.canonicalOf_eq_some z h).mp hc
      exact (m'.canonicalOf_eq_some z h).mpr ⟨by rw [htab]; exact ht, o, hold' h o ho, hcan⟩
    | none =>
      rw [Mem.canonicalOf_eq_none] at hc ⊢
      intro h o ht ho
      rw [htab] at ht
      obtain ⟨o0, ho0, -⟩ := hm.tbl z h ht
      rw [hold' h o0 ho0, Option.some.injEq] at ho
      subst ho
      exact hc h o0 ht ho0
  have hk : m.KeepY m' y := ⟨hold', fun z _ => htab z, hcanon⟩
  have hcuts : CutsKept db m m' K y := by
    intro h o w' ho hoy hsn
    obtain ⟨r0, -, -, -, -, h5⟩ := hsn
    rcases h5 with h5 | ⟨-, -, ht, -⟩
    · exact Or.inl h5
    · right; rw [htab, ← hoy]; exact ht
  refine ⟨⟨by rw [hm']; exact hm.sEq, hm.sK, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    fun d R x h1 h2 h3 h4 => by rw [hcanon]; exact hm.coverGd d R x h1 h2 h3 h4,
    fun x w h1 h2 h3 => by rw [hcanon]; exact hm.coverSec x w h1 h2 h3,
    fun x n e h1 h2 h3 h4 => by rw [hcanon]; exact hm.coverNew x n e h1 h2 h3 h4⟩, hk⟩
  · intro h hh
    rw [hm', Mem.addObj_next] at hh
    rw [hobj]
    simp only [show h ≠ m.next by omega, ↓reduceIte]
    exact hm.fresh h (by omega)
  · rw [hm']
    exact nodup_addObj_keys m _ hm.nodup hm.fresh
  · obtain ⟨ht, o, ho, hc, hn⟩ := hm.root
    rw [hm', Mem.addObj_root, ← hm']
    exact ⟨by rw [htab]; exact ht, o, hold' _ o ho, hc, hn⟩
  · intro z h ht
    rw [htab] at ht
    obtain ⟨o, ho, hn⟩ := hm.tbl z h ht
    exact ⟨o, hold' h o ho, hn⟩
  · intro h o ho
    rw [hobj] at ho
    split at ho
    · cases ho; rw [f1]; exact hborn
    · exact hm.born h o ho
  · intro h o ho hc
    rw [hobj] at ho
    split at ho
    · cases ho; rw [f5] at hc; cases hc
    · obtain ⟨c1, c2, c3, c4, c5⟩ := hm.canon h o ho hc
      refine ⟨by rw [htab]; exact c1, c2, c3, ?_, ?_⟩
      · intro t ht hr z hz
        obtain ⟨sl, hsl, hg⟩ := c4 t ht hr z hz
        exact ⟨sl, hsl, SlotGood.keepY hk hcuts hg⟩
      · intro hr z hz
        obtain ⟨sl, hsl, hg⟩ := c5 hr z hz
        exact ⟨sl, hsl, SlotFresh.keepY hk hg⟩
  · intro h o ho hc
    rw [hobj] at ho
    split at ho
    · cases ho
      refine ⟨w, ⟨r'', by rw [f6, hwr], by rw [f1]; exact hw, f2, f3, Or.inl ⟨by rw [f4]; rfl, hle⟩⟩, ?_, ?_⟩
      · intro z hz
        rw [Obj.ofVersion_slot?, ← f4]
        simp [hz]
      · intro z sl hsl
        rw [Obj.ofVersion_slot?] at hsl
        split at hsl
        · cases hsl; exact Or.inl rfl
        · cases hsl
    · obtain ⟨w', hw', hss1, hss2⟩ := hm.snap h o ho hc
      refine ⟨w', SnapOK.keepY hk hw' (fun hy => hcuts h o w' ho hy hw'), hss1, ?_⟩
      intro z sl hsl
      rcases hss2 z sl hsl with h2 | ⟨h', h2, h3⟩
      · exact Or.inl h2
      · exact Or.inr ⟨h', h2, AtLeast.keepY hk h3⟩
  · intro h o z h' ho hsl
    rw [hobj] at ho
    split at ho
    · cases ho
      rw [Obj.ofVersion_slot?] at hsl
      split at hsl <;> cases hsl
    · obtain ⟨o', ho', hz, hc⟩ := hm.memSlot h o z h' ho hsl
      refine ⟨o', hold' h' o' ho', hz, ?_⟩
      rcases hc with hc | ⟨hcan, h0, o0, p, p0, ht, ho0, hp, hp0, hlt⟩
      · left; rw [htab]; exact hc
      · exact Or.inr ⟨hcan, h0, o0, p, p0, by rw [htab]; exact ht, hold' h0 o0 ho0, hp, hp0, hlt⟩

end Load

/-! ### Evaluating a first touch -/

section Eval

variable (sp : Spec V T) (S : Stream V T)

theorem follow_mem_eval (m : Mem V) {hp : Nat} {op : Obj V} (hop : m.obj? hp = some op) {y : NodeId}
    {h : Nat} (hsl : op.slot? y = some (Slot.mem h)) {o : Obj V} (ho : m.obj? h = some o) :
    m.follow sp S hp y false = (m, some h) := by
  unfold Mem.follow
  simp only [hop, hsl, Option.bind_some, ho, Bool.false_and, Bool.false_eq_true, ↓reduceIte]

theorem follow_table_eval (m : Mem V) {hp : Nat} {op : Obj V} (hop : m.obj? hp = some op)
    {y : NodeId} {r : Option Nat} (hsl : op.slot? y = some (Slot.stream r)) {h0 : Nat} {o0 : Obj V}
    (ht : m.tableOf y = some h0) (ho0 : m.obj? h0 = some o0)
    (hu : o0.usable (ruleRRef S m.s y r) = true) :
    m.follow sp S hp y false = (m.setObj hp (op.setSlot y (Slot.mem h0)), some h0) := by
  unfold Mem.follow
  simp only [hop, hsl, Option.bind_some, ht, ho0, hu, ↓reduceIte]
  rw [Mem.obj?_setObj]
  split <;> rfl

theorem follow_load_eval (m : Mem V) {hp : Nat} {op : Obj V} (hop : m.obj? hp = some op)
    {y : NodeId} {r : Option Nat} (hsl : op.slot? y = some (Slot.stream r))
    (hnu : ∀ h0 o0, m.tableOf y = some h0 → m.obj? h0 = some o0 →
      o0.usable (ruleRRef S m.s y r) = false)
    {r'' : Nat} (hr : ruleRRef S m.s y r = some r'') {w : Version V} (hw : S.versionAt r'' y = some w)
    {m1 : Mem V} {h1 : Nat}
    (hreg : (m.addObj (Obj.ofVersion sp w (if m.s ≤ r'' && isKeyLevel sp w.isData w.level then
      some m.s else none))).1.register m.next = (m1, h1))
    (hop1 : m1.obj? hp = some op) :
    m.follow sp S hp y false = (m1.setObj hp (op.setSlot y (Slot.mem h1)), some h1) := by
  unfold Mem.follow
  simp only [hop, hsl, Option.bind_some]
  cases ht : m.tableOf y with
  | none =>
    simp only [hr, hw, Mem.addObj_snd, hreg, hop1, Mem.obj?_setObj]
    split <;> rfl
  | some h0 =>
    cases ho0 : m.obj? h0 with
    | none =>
      simp only [ho0, hr, hw, Mem.addObj_snd, hreg, hop1, Mem.obj?_setObj]
      split <;> rfl
    | some o0 =>
      have hu' : o0.usable (some r'') = false := by rw [← hr]; exact hnu h0 o0 ht ho0
      simp only [ho0, hu', hr, hw, Mem.addObj_snd, hreg, hop1, Mem.obj?_setObj,
        Bool.false_eq_true, ↓reduceIte]
      split <;> rfl

theorem follow_mem_eval_w (m : Mem V) {hp : Nat} {op : Obj V} (hop : m.obj? hp = some op) {y : NodeId}
    {h : Nat} (hsl : op.slot? y = some (Slot.mem h)) {o : Obj V} (ho : m.obj? h = some o) :
    m.follow sp S hp y true = if o.canonical then (m, some h) else ((m.makeCanonical hp y h).1, some (m.makeCanonical hp y h).2) := by
  unfold Mem.follow
  simp only [hop, hsl, Option.bind_some, ho, Bool.true_and]
  cases o.canonical <;> rfl

theorem follow_table_eval_w (m : Mem V) {hp : Nat} {op : Obj V} (hop : m.obj? hp = some op)
    {y : NodeId} {r : Option Nat} (hsl : op.slot? y = some (Slot.stream r)) {h0 : Nat} {o0 : Obj V}
    (ht : m.tableOf y = some h0) (ho0 : m.obj? h0 = some o0)
    (hu : o0.usable (ruleRRef S m.s y r) = true) (hne : h0 ≠ hp) :
    m.follow sp S hp y true = if o0.canonical then (m.setObj hp (op.setSlot y (Slot.mem h0)), some h0)
      else (((m.setObj hp (op.setSlot y (Slot.mem h0))).makeCanonical hp y h0).1,
        some ((m.setObj hp (op.setSlot y (Slot.mem h0))).makeCanonical hp y h0).2) := by
  unfold Mem.follow
  simp only [hop, hsl, Option.bind_some, ht, ho0, hu, ↓reduceIte]
  rw [Mem.obj?_setObj]
  simp only [hne, ↓reduceIte, ho0, Bool.true_and]
  cases o0.canonical <;> rfl

theorem follow_load_eval_w (m : Mem V) {hp : Nat} {op : Obj V} (hop : m.obj? hp = some op)
    {y : NodeId} {r : Option Nat} (hsl : op.slot? y = some (Slot.stream r))
    (hnu : ∀ h0 o0, m.tableOf y = some h0 → m.obj? h0 = some o0 →
      o0.usable (ruleRRef S m.s y r) = false)
    {r'' : Nat} (hr : ruleRRef S m.s y r = some r'') {w : Version V} (hw : S.versionAt r'' y = some w)
    {m1 : Mem V} {h1 : Nat}
    (hreg : (m.addObj (Obj.ofVersion sp w (if m.s ≤ r'' && isKeyLevel sp w.isData w.level then
      some m.s else none))).1.register m.next = (m1, h1))
    (hop1 : m1.obj? hp = some op) (hne : h1 ≠ hp) {o1 : Obj V} (ho1 : m1.obj? h1 = some o1) :
    m.follow sp S hp y true = if o1.canonical then (m1.setObj hp (op.setSlot y (Slot.mem h1)), some h1)
      else (((m1.setObj hp (op.setSlot y (Slot.mem h1))).makeCanonical hp y h1).1,
        some ((m1.setObj hp (op.setSlot y (Slot.mem h1))).makeCanonical hp y h1).2) := by
  have hfin : (match (m1.setObj hp (op.setSlot y (Slot.mem h1))).obj? h1 with
      | some o1 => if (true && !o1.canonical) = true then
          (((m1.setObj hp (op.setSlot y (Slot.mem h1))).makeCanonical hp y h1).1,
            some ((m1.setObj hp (op.setSlot y (Slot.mem h1))).makeCanonical hp y h1).2)
        else (m1.setObj hp (op.setSlot y (Slot.mem h1)), some h1)
      | none => (m1.setObj hp (op.setSlot y (Slot.mem h1)), some h1)) =
      if o1.canonical then (m1.setObj hp (op.setSlot y (Slot.mem h1)), some h1)
      else (((m1.setObj hp (op.setSlot y (Slot.mem h1))).makeCanonical hp y h1).1,
        some ((m1.setObj hp (op.setSlot y (Slot.mem h1))).makeCanonical hp y h1).2) := by
    rw [Mem.obj?_setObj]
    simp only [hne, ↓reduceIte, ho1, Bool.true_and]
    cases o1.canonical <;> rfl
  unfold Mem.follow
  simp only [hop, hsl, Option.bind_some]
  cases ht : m.tableOf y with
  | none =>
    simp only [hr, hw, Mem.addObj_snd, hreg, hop1]
    exact hfin
  | some h0 =>
    cases ho0 : m.obj? h0 with
    | none =>
      simp only [ho0, hr, hw, Mem.addObj_snd, hreg, hop1]
      exact hfin
    | some o0 =>
      have hu' : o0.usable (some r'') = false := by rw [← hr]; exact hnu h0 o0 ht ho0
      simp only [ho0, hu', hr, hw, Mem.addObj_snd, hreg, hop1, Bool.false_eq_true, ↓reduceIte]
      exact hfin

end Eval

/-! ### Facts for one first touch -/

theorem Mem.SameCore.le {m m' : Mem V} (hs : m.SameCore m') : m.Le m' := by
  refine ⟨fun h o ho => ?_, fun y h hc => by rw [hs.canonicalOf]; exact hc⟩
  obtain ⟨o', ho', e1, e2, e3, e4, e5, e6⟩ := hs.obj ho
  exact ⟨o', ho', e1, e2, e3, e6, fun h => by rw [e5]; exact h, fun _ => e4⟩

/-- m' keeps the core of every object of m (only slots change, and objects are
added). -/
def Mem.KeepCore (m m' : Mem V) : Prop :=
  ∀ h o, m.obj? h = some o → ∃ o', m'.obj? h = some o' ∧ o'.core = o.core

theorem Mem.KeepCore.refl (m : Mem V) : m.KeepCore m := fun _ o ho => ⟨o, ho, rfl⟩

theorem Mem.KeepCore.trans {m m' m'' : Mem V} (h1 : m.KeepCore m') (h2 : m'.KeepCore m'') :
    m.KeepCore m'' := by
  intro h o ho
  obtain ⟨o', ho', e⟩ := h1 h o ho
  obtain ⟨o'', ho'', e'⟩ := h2 h o' ho'
  exact ⟨o'', ho'', by rw [e', e]⟩

theorem Mem.SameCore.keepCore {m m' : Mem V} (hs : m.SameCore m') : m.KeepCore m' := by
  intro h o ho
  have := hs.2 h
  rw [ho] at this
  cases h' : m'.obj? h with
  | none => rw [h'] at this; cases this
  | some o' => rw [h'] at this; exact ⟨o', rfl, Option.some.inj this⟩

theorem Mem.KeepY.keepCore {m m' : Mem V} {y : NodeId} (hk : m.KeepY m' y) : m.KeepCore m' :=
  fun h o ho => ⟨o, hk.obj h o ho, rfl⟩

theorem ruleR_newest_ge {S : Stream V T} {s : Nat} {y : NodeId} {w' : Version V}
    (hn : newest S s y = some w') {r : Option Nat} {r' : Nat} (h : ruleRRef S s y r = some r') :
    w'.recNo ≤ r' := by
  unfold ruleRRef at h
  rw [hn] at h
  simp only at h
  cases r with
  | none => simp at h; omega
  | some r0 =>
    simp only at h
    split at h
    · cases h; exact Nat.le_refl _
    · cases h; omega

section Touch

variable {sp : Spec V T} {db : DB V T}

/-- A node table object of y that is not canonical: y has no canonical object. -/
theorem canonicalOf_none_of_table {m : Mem V}
    {y : NodeId} {h0 : Nat} {o0 : Obj V} (ht : m.tableOf y = some h0) (ho0 : m.obj? h0 = some o0)
    (hc0 : o0.canonical = false) : m.canonicalOf y = none := by
  rw [Mem.canonicalOf_eq_none]
  intro h o ht' ho
  rw [ht, Option.some.injEq] at ht'
  subst ht'
  rw [ho0, Option.some.injEq] at ho
  subst ho
  exact hc0

/-- The node table's object, usable for what a stream slot leads to, can be read
whenever the slot could. -/
theorem MemInv.table_readable {K k : Nat} {m : Mem V} (hm : MemInv sp db K m)
    (hctx : PCtx sp db k) {y : NodeId} {h0 : Nat} {o0 : Obj V} (ht : m.tableOf y = some h0)
    (ho0 : m.obj? h0 = some o0) {r : Option Nat}
    (hu : o0.usable (ruleRRef db.S (lastSp db.S) y r) = true) {t : Time}
    (hg : SlotGood sp db m K t y (Slot.stream r)) : Readable sp db m K t h0 y := by
  obtain ⟨o0', ho0', hn0⟩ := hm.tbl y h0 ht
  rw [ho0, Option.some.injEq] at ho0'
  subst ho0'
  refine ⟨o0, ho0, hn0, ?_⟩
  cases hc0 : o0.canonical
  · right
    have hnc := canonicalOf_none_of_table ht ho0 hc0
    rcases hg with hg | ⟨r', w2, hr', hw2, hg2⟩
    · exact absurd hnc hg
    · obtain ⟨w0, hw0, -⟩ := hm.snap h0 o0 ho0 hc0
      refine ⟨w0, hw0, fun _ => ?_⟩
      obtain ⟨p0, hp0, hv0, -⟩ := hw0
      unfold Obj.usable at hu
      rw [hc0, hr', hp0] at hu
      simp only [Bool.false_or, decide_eq_true_eq] at hu
      rw [hn0] at hv0
      exact hctx.inv.newer hctx.ls (w2.level + 1) r' p0 y w2 w0 (by omega) hw2 hv0 hu t hg2
  · exact Or.inl rfl

/-- The node table's object, usable for what a fresh stream slot leads to, is
fresh. -/
theorem MemInv.table_fresh {K k : Nat} {m : Mem V} (hm : MemInv sp db K m)
    (hctx : PCtx sp db k) {y : NodeId} {h0 : Nat} {o0 : Obj V} (ht : m.tableOf y = some h0)
    (ho0 : m.obj? h0 = some o0) {r : Option Nat}
    (hu : o0.usable (ruleRRef db.S (lastSp db.S) y r) = true)
    (hf : SlotFresh db m y (Slot.stream r)) : SlotFresh db m y (Slot.mem h0) := by
  obtain ⟨o0', ho0', hn0⟩ := hm.tbl y h0 ht
  rw [ho0, Option.some.injEq] at ho0'
  subst ho0'
  refine ⟨o0, ho0, ?_⟩
  cases hc0 : o0.canonical
  · have hnc := canonicalOf_none_of_table ht ho0 hc0
    obtain ⟨w0, hw0, -⟩ := hm.snap h0 o0 ho0 hc0
    obtain ⟨p0, hp0, hv0, -, hd0, -⟩ := hw0
    rw [hn0] at hv0
    rcases hf with hf | ⟨n, r', w, hn, hnd, -, -⟩ | ⟨hf, hsome⟩
    · exact absurd hnc hf
    · right; left
      obtain ⟨-, -, n', hn', -, -, hd'⟩ := hctx.inv.version_node hv0
      rw [hn, Option.some.injEq] at hn'
      subst hn'
      rw [hd0, hd', hnd]
    · right; right
      obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hsome
      rw [hv] at hf ⊢
      unfold Obj.usable at hu
      rw [hc0, hf, hp0] at hu
      simp only [Option.map_some, Bool.false_or, decide_eq_true_eq] at hu
      obtain ⟨v', hv', hle⟩ := hctx.inv.le_lv hv0
      rw [hv, Option.some.injEq] at hv'
      subst hv'
      rw [hp0]
      simp only [Option.map_some, Option.some.injEq]
      omega
  · exact Or.inl rfl

end Touch

/-! ### A reader's first touch -/

/-- A fresh memory slot names the node table's object. -/
theorem MemInv.fresh_table {sp : Spec V T} {db : DB V T} {K k : Nat} {m : Mem V}
    (hm : MemInv sp db K m) (hctx : PCtx sp db k) {hp : Nat} {op : Obj V}
    (hop : m.obj? hp = some op) {y : NodeId} {h : Nat} (hsl : op.slot? y = some (Slot.mem h))
    (hf : SlotFresh db m y (Slot.mem h)) : m.tableOf y = some h := by
  obtain ⟨o, ho, hoy, hc⟩ := hm.memSlot hp op y h hop hsl
  rcases hc with hc | ⟨hcan, h0, o0, p, p0, ht, ho0, hp', hp0, hlt⟩
  · exact hc
  · exfalso
    obtain ⟨o', ho', hf'⟩ := hf
    rw [ho, Option.some.injEq] at ho'
    subst ho'
    -- the table's object is a version of y too, at most y's latest
    obtain ⟨-, hn0⟩ : ∃ o0', m.obj? h0 = some o0' ∧ o0'.node = y := hm.tbl y h0 ht
    have hpos0 : (db.S.versionAt p0 y).isSome := by
      cases hc0 : o0.canonical
      · obtain ⟨w0, hw0, -⟩ := hm.snap h0 o0 ho0 hc0
        obtain ⟨r0, hr0, hv0, -⟩ := hw0
        rw [hp0, Option.some.injEq] at hr0
        subst hr0
        obtain ⟨o0', ho0', hn0'⟩ := hm.tbl y h0 ht
        rw [ho0, Option.some.injEq] at ho0'
        subst ho0'
        rw [hn0'] at hv0
        simp [hv0]
      · obtain ⟨-, -, c3, -⟩ := hm.canon h0 o0 ho0 hc0
        obtain ⟨o0', ho0', hn0'⟩ := hm.tbl y h0 ht
        rw [ho0, Option.some.injEq] at ho0'
        subst ho0'
        have := c3 p0 hp0
        rw [hn0'] at this
        exact this
    obtain ⟨u0, hu0⟩ := Option.isSome_iff_exists.mp hpos0
    obtain ⟨v, hv, hle⟩ := hctx.inv.le_lv hu0
    rcases hf' with hf' | hf' | hf'
    · rw [hcan] at hf'; cases hf'
    · -- a data node: it has one version, so the two records are the same
      obtain ⟨w1, hw1, -⟩ := hm.snap h o ho hcan
      obtain ⟨r1, hr1, hv1, -, hd1, -⟩ := hw1
      rw [hp', Option.some.injEq] at hr1
      subst hr1
      rw [hoy] at hv1
      obtain ⟨-, hrec1, n1, hn1, -, -, hd1'⟩ := hctx.inv.version_node hv1
      have hdat : n1.isData = true := by rw [← hd1', ← hd1, hf']
      have h1 := hctx.dataOnce y n1 p w1 hn1 hdat hv1
      have h2 := hctx.dataOnce y n1 p0 u0 hn1 hdat hu0
      rw [h1, Option.some.injEq] at h2
      subst h2
      obtain ⟨-, hrec0, -⟩ := hctx.inv.version_node hu0
      omega
    · rw [hp', hv, Option.map_some, Option.some.injEq] at hf'
      omega

section Reader

variable {sp : Spec V T} {db : DB V T}

/-- A cut back object of y needs y to have no entries up to K. -/
theorem MemInv.cut_empty {K k : Nat} {m : Mem V} (hm : MemInv sp db K m)
    (hctx : PCtx sp db k) {y : NodeId} (hnc : m.canonicalOf y = none) {r : Option Nat} {r' : Nat}
    (hr : ruleRRef db.S (lastSp db.S) y r = some r') {w : Version V}
    (hw : db.S.versionAt r' y = some w) (hs : lastSp db.S ≤ r') (hd : w.isData = false) :
    histAt db.P y K = [] ∧ db.S.lv y = some w := by
  obtain ⟨-, hrec, ny, hny, hwh, -, hwd⟩ := hctx.inv.version_node hw
  -- y's newest version in the section is w.
  cases hnw : newest db.S (lastSp db.S) y with
  | none =>
    have := (newest_eq_none_iff db.S (lastSp db.S) y).mp hnw r' hs
    rw [hw] at this; cases this
  | some w' =>
    obtain ⟨r2, -, hw2, hle⟩ := newest_ge hnw hw
    obtain ⟨-, hrec2, -⟩ := hctx.inv.version_node hw2
    have hge := ruleR_newest_ge hnw hr
    have hr2 : r2 = r' := by omega
    subst hr2
    rw [hw, Option.some.injEq] at hw2
    subst hw2
    refine ⟨?_, newest_lv hnw⟩
    have hsec : w.hist.upTo (lastSp db.S) = [] := by
      cases hh : w.hist.upTo (lastSp db.S) with
      | nil => rfl
      | cons e l =>
        exfalso
        exact hm.coverSec y w hnw hd (by rw [hh]; simp) hnc
    have hs' : ny.hist.upTo (lastSp db.S) = [] := by
      rw [hwh, upTo_upTo _ hs] at hsec; exact hsec
    unfold histAt
    rw [hny]
    simp only [Option.map_some, Option.getD_some]
    apply upTo_eq_nil
    intro e he
    apply Classical.byContradiction
    intro hlt
    have hek : e.time ≤ K := by omega
    by_cases hes : e.time ≤ lastSp db.S
    · have : e ∈ ny.hist.upTo (lastSp db.S) := mem_upTo.mpr ⟨he, hes⟩
      rw [hs'] at this; cases this
    · exact hm.coverNew y ny e hny he (by omega) hek hnc

/-- A reader's first touch of the slot for y of object hp: the read goes on to
an object that can be read at t, and the invariant is kept. -/
theorem MemInv.follow_reader {K k : Nat} {m : Mem V} (hm : MemInv sp db K m)
    (hctx : PCtx sp db k) (hfix : FixedLe sp db K) {hp : Nat} {op : Obj V}
    (hop : m.obj? hp = some op) {y : NodeId}
    {sl : Slot} (hsl : op.slot? y = some sl) (hyne : y ≠ op.node) {t : Time} (ht : t ≤ K)
    (hry : reachable sp db.P t y = true) (hg : SlotGood sp db m K t y sl) :
    ∃ m' h1, m.follow sp db.S hp y false = (m', some h1) ∧ MemInv sp db K m' ∧ m.Le m' ∧
      m.KeepCore m' ∧ Readable sp db m' K t h1 y ∧
      (∃ o1, m'.obj? h1 = some o1 ∧ o1.node = y ∧
        m.follow sp db.S hp y true = (if o1.canonical then (m', some h1) else
          ((m'.makeCanonical hp y h1).1, some (m'.makeCanonical hp y h1).2))) ∧
      (SlotFresh db m y sl → m'.tableOf y = some h1 ∧ SlotFresh db m' y (Slot.mem h1)) := by
  cases sl with
  | mem h =>
    obtain ⟨o, ho, hn, hc⟩ := hg
    exact ⟨m, h, follow_mem_eval sp db.S m hop hsl ho, hm, Mem.Le.refl m, Mem.KeepCore.refl m,
      ⟨o, ho, hn, hc⟩, ⟨o, ho, hn, follow_mem_eval_w sp db.S m hop hsl ho⟩,
      fun hf => ⟨hm.fresh_table hctx hop hsl hf, hf⟩⟩
  | stream r =>
    have hsE := hm.sEq
    -- The parent's own facts about this slot.
    have hpar_can : op.canonical = true →
        (∀ t' ≤ K, reachable sp db.P t' op.node = true → y ∈ sp.live (op.hist.upTo t') →
          SlotGood sp db m K t' y (Slot.stream r)) ∧
        (reachable sp db.P K op.node = true → y ∈ sp.live op.hist →
          SlotFresh db m y (Slot.stream r)) := by
      intro hc
      obtain ⟨-, -, -, c4, c5⟩ := hm.canon hp op hop hc
      refine ⟨fun t' ht' hr hy => ?_, fun hr hy => ?_⟩
      · obtain ⟨sl', hsl', hg'⟩ := c4 t' ht' hr y hy
        rw [hsl, Option.some.injEq] at hsl'; subst hsl'; exact hg'
      · obtain ⟨sl', hsl', hg'⟩ := c5 hr y hy
        rw [hsl, Option.some.injEq] at hsl'; subst hsl'; exact hg'
    have hpar_snap : op.canonical = false → ∀ w, SnapOK db m K hp op w → r = w.ref? y := by
      intro hc w hw
      obtain ⟨w', hw', -, hss2⟩ := hm.snap hp op hop hc
      have hww : w' = w := by
        obtain ⟨r1, hp1, hv1, -⟩ := hw
        obtain ⟨r2, hp2, hv2, -⟩ := hw'
        rw [hp1, Option.some.injEq] at hp2; subst hp2
        rw [hv1, Option.some.injEq] at hv2; exact hv2.symm
      subst hww
      rcases hss2 y (Slot.stream r) hsl with h1 | ⟨h', h1, -⟩
      · exact Slot.stream.inj h1
      · cases h1
    by_cases htab : ∃ h0 o0, m.tableOf y = some h0 ∧ m.obj? h0 = some o0 ∧
        o0.usable (ruleRRef db.S m.s y r) = true
    · -- The node table's object serves the slot.
      obtain ⟨h0, o0, ht0, ho0, hu⟩ := htab
      rw [hsE] at hu
      have hev := follow_table_eval sp db.S m hop hsl ht0 ho0 (by rw [hsE]; exact hu)
      obtain ⟨o0', ho0', hn0⟩ := hm.tbl y h0 ht0
      rw [ho0, Option.some.injEq] at ho0'
      subst ho0'
      have hms : MemSlotOK m y h0 := by
        obtain ⟨o0', ho0', hn0'⟩ := hm.tbl y h0 ht0
        exact ⟨o0', ho0', hn0', Or.inl ht0⟩
      obtain ⟨hm', hs⟩ := hm.swizzle hop hms
        (fun hc => ⟨fun t' ht' hr hy => hm.table_readable hctx ht0 ho0 hu ((hpar_can hc).1 t' ht' hr hy),
          fun hr hy => hm.table_fresh hctx ht0 ho0 hu ((hpar_can hc).2 hr hy)⟩)
        (fun hc w hw => by
          rw [← hpar_snap hc w hw]
          refine ⟨o0, ho0, ?_, ?_⟩
          · obtain ⟨o0', ho0', hn0'⟩ := hm.tbl y h0 ht0
            rw [ho0, Option.some.injEq] at ho0'; subst ho0'; exact hn0'
          · unfold Obj.usable at hu
            cases hc0 : o0.canonical
            · rw [hc0] at hu
              right; right
              simp only [Bool.false_or] at hu
              split at hu
              · rename_i r1 p1 hr1 hp1
                exact ⟨p1, hp1, fun r2 h2 => by rw [hr1, Option.some.injEq] at h2; subst h2; simpa using hu⟩
              · cases hu
            · exact Or.inl rfl)
        (by rw [hsl]; rfl)
      have hne0 : h0 ≠ hp := by
        intro he; subst he
        rw [hop, Option.some.injEq] at ho0
        subst ho0
        exact hyne hn0.symm
      refine ⟨_, h0, hev, hm', hs.le, hs.keepCore,
        Readable.congr hs (hm.table_readable hctx ht0 ho0 hu hg),
        ⟨o0, by rw [Mem.obj?_setObj]; simp only [hne0, ↓reduceIte]; exact ho0, hn0,
          follow_table_eval_w sp db.S m hop hsl ht0 ho0 (by rw [hsE]; exact hu) hne0⟩,
        fun hf => ⟨by rw [hs.tableOf]; exact ht0, SlotFresh.congr hs (hm.table_fresh hctx ht0 ho0 hu hf)⟩⟩
    · -- The version is read from the stream.
      have hnu : ∀ h0 o0, m.tableOf y = some h0 → m.obj? h0 = some o0 →
          o0.usable (ruleRRef db.S m.s y r) = false := by
        intro h0 o0 ht0 ho0
        cases hu : o0.usable (ruleRRef db.S m.s y r)
        · rfl
        · exact absurd ⟨h0, o0, ht0, ho0, hu⟩ htab
      have hnc : m.canonicalOf y = none := by
        cases hc : m.canonicalOf y with
        | none => rfl
        | some hc0 =>
          exfalso
          obtain ⟨ht0, o0, ho0, hcan⟩ := (m.canonicalOf_eq_some y hc0).mp hc
          have := hnu hc0 o0 ht0 ho0
          unfold Obj.usable at this
          rw [hcan] at this; cases this
      rcases hg with hg | ⟨r', w, hr', hw, hgw⟩
      · exact absurd hnc hg
      obtain ⟨-, hwr, ny, hny, -, -, hwd⟩ := hctx.inv.version_node hw
      have hborn : ∃ t' ≤ K, reachable sp db.P t' y = true := ⟨t, ht, hry⟩
      have hlt := lt_next_of_obj? hm.fresh hop
      -- Whether the version is cut back.
      have hcut : ∀ s', (if m.s ≤ r' && isKeyLevel sp w.isData w.level then some m.s else none) =
          some s' → s' = lastSp db.S ∧ histAt db.P y K = [] ∧ db.S.lv y = some w := by
        intro s' hs'
        split at hs'
        · rename_i hc
          cases hs'
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
          have hdat : w.isData = false := by
            unfold isKeyLevel at hc
            cases hd : w.isData
            · rfl
            · rw [hd] at hc; simp at hc
          rw [hsE] at hc ⊢
          exact ⟨rfl, hm.cut_empty hctx hnc hr' hw hc.1 hdat⟩
        · cases hs'
      have hle : (if m.s ≤ r' && isKeyLevel sp w.isData w.level then some m.s else none) = none →
          ∀ e ∈ w.hist, e.time ≤ K := by
        intro hn e he
        obtain ⟨-, -, ny', hny', hwh', hwl', hwd'⟩ := hctx.inv.version_node hw
        rw [hny, Option.some.injEq] at hny'
        subst hny'
        rw [hwh'] at he
        have he1 := (mem_upTo.mp he)
        split at hn
        · cases hn
        · rename_i hc
          simp only [Bool.and_eq_true, decide_eq_true_eq, not_and] at hc
          by_cases hs : m.s ≤ r'
          · have hk := hc hs
            have hkl : isKeyLevel sp ny.isData ny.level = false := by
              rw [← hwd', ← hwl']; simpa using hk
            have hyr : y ≠ SIS.root := by
              intro hy
              obtain ⟨ht0, o0, ho0, hc0, -⟩ := hm.root
              have := (m.canonicalOf_eq_some SIS.root m.root).mpr ⟨ht0, o0, ho0, hc0⟩
              rw [← hy, hnc] at this; cases this
            exact hfix y ny hny hkl (Or.inr hyr) hborn e he1.1
          · have := hm.sK; rw [← hsE] at this; omega
      have hold : ∀ h0 o0, m.tableOf y = some h0 → m.obj? h0 = some o0 →
          o0.canonical = false ∧ ∃ p0, o0.pos = some p0 ∧ p0 < r' := by
        intro h0 o0 ht0 ho0
        have hu := hnu h0 o0 ht0 ho0
        unfold Obj.usable at hu
        rw [hsE, hr'] at hu
        simp only [Bool.or_eq_false_iff] at hu
        refine ⟨hu.1, ?_⟩
        obtain ⟨w0, hw0, -⟩ := hm.snap h0 o0 ho0 hu.1
        obtain ⟨p0, hp0, -⟩ := hw0
        rw [hp0] at hu
        simp only [decide_eq_false_iff_not, Nat.not_le] at hu
        exact ⟨p0, hp0, hu.2⟩
      -- The facts about the object the read goes on to, for the swizzle.
      suffices key : ∀ (m1 : Mem V) (h1 : Nat), (m.addObj (Obj.ofVersion sp w
          (if m.s ≤ r' && isKeyLevel sp w.isData w.level then some m.s else none))).1.register m.next =
          (m1, h1) → MemInv sp db K m1 → m.KeepY m1 y → m1.tableOf y = some h1 →
          (∃ o1, m1.obj? h1 = some o1 ∧ o1.node = y ∧ o1.canonical = false ∧
            (∀ t', good sp db.S db.P t' w = true → Readable sp db m1 K t' h1 y) ∧
            (o1.isData = true ∨ o1.pos = some r')) →
          ∃ m' h1, m.follow sp db.S hp y false = (m', some h1) ∧ MemInv sp db K m' ∧ m.Le m' ∧
            m.KeepCore m' ∧ Readable sp db m' K t h1 y ∧
            (∃ o1, m'.obj? h1 = some o1 ∧ o1.node = y ∧
              m.follow sp db.S hp y true = (if o1.canonical then (m', some h1) else
                ((m'.makeCanonical hp y h1).1, some (m'.makeCanonical hp y h1).2))) ∧
            (SlotFresh db m y (Slot.stream r) → m'.tableOf y = some h1 ∧
              SlotFresh db m' y (Slot.mem h1)) by
        -- The two outcomes of register.
        obtain ⟨f1, f2, f3, f4, f5, f6⟩ := Obj.ofVersion_fields sp w
          (if m.s ≤ r' && isKeyLevel sp w.isData w.level then some m.s else none)
        have hwy : w.node = y := (hctx.inv.version_node hw).1
        rw [hwy] at f1
        have hobjn : (m.addObj (Obj.ofVersion sp w
            (if m.s ≤ r' && isKeyLevel sp w.isData w.level then some m.s else none))).1.obj? m.next =
            some (Obj.ofVersion sp w
              (if m.s ≤ r' && isKeyLevel sp w.isData w.level then some m.s else none)) := by
          rw [Mem.obj?_addObj]; simp
        have hgoodN : ∀ (m1 : Mem V), MemInv sp db K m1 →
            m1.obj? m.next = some (Obj.ofVersion sp w
              (if m.s ≤ r' && isKeyLevel sp w.isData w.level then some m.s else none)) →
            ∀ t', good sp db.S db.P t' w = true → Readable sp db m1 K t' m.next y := by
          intro m1 hm1 ho1 t' hgt
          obtain ⟨w1, hw1, -⟩ := hm1.snap m.next _ ho1 f5
          have hww : w1 = w := by
            obtain ⟨r1, hp1, hv1, -⟩ := hw1
            rw [f6, hwr, Option.some.injEq] at hp1
            subst hp1
            rw [f1, hw, Option.some.injEq] at hv1
            exact hv1.symm
          subst hww
          exact ⟨_, ho1, f1, Or.inr ⟨w1, hw1, fun _ => hgt⟩⟩
        cases hT : m.tableOf y with
        | none =>
          have hreg := register_none (m.addObj (Obj.ofVersion sp w
            (if m.s ≤ r' && isKeyLevel sp w.isData w.level then some m.s else none))).1 hobjn
            (by rw [f1, Mem.tableOf_addObj]; exact hT)
          rw [f1] at hreg
          obtain ⟨hm1, hk1⟩ := hm.load_accept hctx hw hnc hold hborn _ hcut hle
          refine key _ _ hreg hm1 hk1 (by rw [Mem.tableOf_setTable]; simp) ⟨_, ?_, f1, f5, ?_, ?_⟩
          · rw [Mem.obj?_setTable]; exact hobjn
          · exact hgoodN _ hm1 (by rw [Mem.obj?_setTable]; exact hobjn)
          · right; rw [f6, hwr]
        | some h0 =>
          obtain ⟨o0, ho0, hn0⟩ := hm.tbl y h0 hT
          have hne : h0 ≠ m.next := by have := lt_next_of_obj? hm.fresh ho0; omega
          have hreg := register_some (m.addObj (Obj.ofVersion sp w
            (if m.s ≤ r' && isKeyLevel sp w.isData w.level then some m.s else none))).1 hobjn
            (by rw [f1, Mem.tableOf_addObj]; exact hT) hne
            (by rw [Mem.obj?_addObj]; simp only [hne, ↓reduceIte]; exact ho0)
          rw [f1] at hreg
          obtain ⟨hc0, p0, hp0, hlt0⟩ := hold h0 o0 hT ho0
          cases hdat : w.isData
          · -- An index node: the new object is better.
            have hb : (Obj.ofVersion sp w
                (if m.s ≤ r' && isKeyLevel sp w.isData w.level then some m.s else none)).better o0 = true := by
              unfold Obj.better
              rw [f5, f6, f3, hdat, hc0, hp0, hwr]
              simp [hlt0]
            rw [hb] at hreg
            simp only [↓reduceIte] at hreg
            obtain ⟨hm1, hk1⟩ := hm.load_accept hctx hw hnc hold hborn _ hcut hle
            refine key _ _ hreg hm1 hk1 (by rw [Mem.tableOf_setTable]; simp) ⟨_, ?_, f1, f5, ?_, ?_⟩
            · rw [Mem.obj?_setTable]; exact hobjn
            · exact hgoodN _ hm1 (by rw [Mem.obj?_setTable]; exact hobjn)
            · right; rw [f6, hwr]
          · -- A data node: the table's object stays, and serves.
            have hb : (Obj.ofVersion sp w
                (if m.s ≤ r' && isKeyLevel sp w.isData w.level then some m.s else none)).better o0 = false := by
              unfold Obj.better
              rw [f3, hdat]
              simp
            rw [hb] at hreg
            simp only [Bool.false_eq_true, ↓reduceIte] at hreg
            have hcutn : (if m.s ≤ r' && isKeyLevel sp w.isData w.level then some m.s else none) = none := by
              unfold isKeyLevel; rw [hdat]; simp
            obtain ⟨hm1, hk1⟩ := hm.load_orphan hctx hw hborn _ hcutn (hle hcutn)
            refine key _ _ hreg hm1 hk1 (by rw [Mem.tableOf_addObj]; exact hT)
              ⟨o0, hk1.obj h0 o0 ho0, hn0, hc0, ?_, ?_⟩
            · intro t' _
              obtain ⟨w0, hw0, -⟩ := hm1.snap h0 o0 (hk1.obj h0 o0 ho0) hc0
              refine ⟨o0, hk1.obj h0 o0 ho0, hn0, Or.inr ⟨w0, hw0, fun _ => ?_⟩⟩
              obtain ⟨p1, -, hv1, -, hd1, -⟩ := hw0
              rw [hn0] at hv1
              obtain ⟨-, -, n1, hn1, -, -, hd1'⟩ := hctx.inv.version_node hv1
              rw [hny, Option.some.injEq] at hn1
              subst hn1
              have hlv := hctx.dataOnce y ny p1 w0 hny (by rw [← hwd, hdat]) hv1
              exact hctx.inv.good_data hctx.ls hny (by rw [← hwd, hdat]) hlv t'
            · left
              obtain ⟨w0, hw0, -⟩ := hm.snap h0 o0 ho0 hc0
              obtain ⟨p1, -, hv1, -, hd1, -⟩ := hw0
              rw [hn0] at hv1
              obtain ⟨-, -, n1, hn1, -, -, hd1'⟩ := hctx.inv.version_node hv1
              rw [hny, Option.some.injEq] at hn1
              subst hn1
              rw [hd1, hd1', ← hwd, hdat]
      -- The swizzle.
      intro m1 h1 hreg hm1 hk1 ht1 ⟨o1, ho1, hn1, hc1, hrd, hpos⟩
      have hev := follow_load_eval sp db.S m hop hsl hnu (by rw [hsE]; exact hr') hw hreg
        (hk1.obj hp op hop)
      have hms : MemSlotOK m1 y h1 := ⟨o1, ho1, hn1, Or.inl ht1⟩
      have hop1 := hk1.obj hp op hop
      have hfresh1 : SlotFresh db m y (Slot.stream r) → SlotFresh db m1 y (Slot.mem h1) := by
        intro hf
        refine ⟨o1, ho1, ?_⟩
        rcases hf with h2 | ⟨n2, r2, w2, hn2, hd2, -, -⟩ | ⟨h2, -⟩
        · exact absurd hnc h2
        · rcases hpos with hpos | hpos
          · exact Or.inr (Or.inl hpos)
          · right; left
            obtain ⟨w1, hw1, -⟩ := hm1.snap h1 o1 ho1 hc1
            obtain ⟨p1, hp1, hv1, -, hd1, -⟩ := hw1
            rw [hn1] at hv1
            obtain ⟨-, -, n1, hn1', -, -, hd1'⟩ := hctx.inv.version_node hv1
            rw [hn2, Option.some.injEq] at hn1'
            subst hn1'
            rw [hd1, hd1', hd2]
        · rcases hpos with hpos | hpos
          · exact Or.inr (Or.inl hpos)
          · right; right
            rw [hpos, ← h2, hr']
      obtain ⟨hm2, hs2⟩ := hm1.swizzle hop1 hms
        (fun hc => ⟨fun t' ht' hr hy => by
            rcases (hpar_can hc).1 t' ht' hr hy with h2 | ⟨r2, w2, hr2, hw2, hg2⟩
            · exact absurd hnc h2
            · rw [hr', Option.some.injEq] at hr2; subst hr2
              rw [hw, Option.some.injEq] at hw2; subst hw2
              exact hrd t' hg2,
          fun hr hy => hfresh1 ((hpar_can hc).2 hr hy)⟩)
        (fun hc w hw' => by
          obtain ⟨w0, hw0, -⟩ := hm.snap hp op hop hc
          have hww : w = w0 := by
            obtain ⟨r1, hp1, hv1, -⟩ := hw'
            obtain ⟨r2, hp2, hv2, -⟩ := hw0
            rw [hp1, Option.some.injEq] at hp2; subst hp2
            rw [hv1, Option.some.injEq] at hv2; exact hv2
          subst hww
          rw [← hpar_snap hc w hw0, hr']
          refine ⟨o1, ho1, hn1, ?_⟩
          rcases hpos with hpos | hpos
          · exact Or.inr (Or.inl hpos)
          · exact Or.inr (Or.inr ⟨r', hpos, fun r2 h2 => by cases h2; exact Nat.le_refl _⟩))
        (by rw [hsl]; rfl)
      have hne1 : h1 ≠ hp := by
        intro he; subst he
        rw [hop1, Option.some.injEq] at ho1
        subst ho1
        exact hyne hn1.symm
      refine ⟨_, h1, hev, hm2, hk1.le.trans hs2.le, hk1.keepCore.trans hs2.keepCore,
        Readable.congr hs2 (hrd t hgw),
        ⟨o1, by rw [Mem.obj?_setObj]; simp only [hne1, ↓reduceIte]; exact ho1, hn1,
          follow_load_eval_w sp db.S m hop hsl hnu (by rw [hsE]; exact hr') hw hreg hop1 hne1 ho1⟩,
        fun hf => ⟨by rw [hs2.tableOf]; exact ht1, SlotFresh.congr hs2 (hfresh1 hf)⟩⟩

end Reader

end SIS
