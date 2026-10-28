/-
Proofs for stage 2 (bergdb item 001, WP E6), part 1: no object's slots repeat
a pointee (`SlotsND`), in every memory of a run with eviction and restarts.
Every object is made with one slot per pointee (`Obj.ofVersion`, from the
pointees of a history, which have no repeats) or with none, and the
operations change slots in place (`Obj.setSlot`) or add one for a pointee
without one (`Obj.putSlot`). T-PIN needs it: unswizzling the slot for y of
every object whose slot for y names an object then leaves no memory slot to
it.
-/
import SIS.Proof.EvictRestart

set_option linter.unusedSectionVars false

namespace SIS

variable {V T : Type} [DecidableEq V]

/-! ## Objects -/

/-- No two slots of object o are for the same pointee. -/
def Obj.KeysND (o : Obj V) : Prop := (o.slots.map (·.1)).Nodup

/-- No object in memory has two slots for the same pointee. -/
def SlotsND (m : Mem V) : Prop := ∀ p ∈ m.objs, p.2.KeysND

theorem keys_map_fst (l : List (NodeId × Slot)) {f : NodeId × Slot → NodeId × Slot}
    (hf : ∀ q, (f q).1 = q.1) : (l.map f).map (·.1) = l.map (·.1) := by
  rw [List.map_map]
  apply List.map_congr_left
  intro q _
  exact hf q

theorem Obj.KeysND.of_slots {o o' : Obj V} (h : o.KeysND) {f : NodeId × Slot → NodeId × Slot}
    (hf : ∀ q, (f q).1 = q.1) (he : o'.slots = o.slots.map f) : o'.KeysND := by
  unfold Obj.KeysND at *
  rw [he, keys_map_fst _ hf]
  exact h

theorem Obj.KeysND.setSlot {o : Obj V} (h : o.KeysND) (y : NodeId) (sl : Slot) :
    (o.setSlot y sl).KeysND := by
  apply h.of_slots (f := fun p => if p.1 == y then (y, sl) else p) _ rfl
  intro q
  split
  · rename_i hq; exact (beq_iff_eq.mp hq).symm
  · rfl

theorem Obj.KeysND.putSlot {o : Obj V} (h : o.KeysND) (y : NodeId) (sl : Slot) :
    (o.putSlot y sl).KeysND := by
  unfold Obj.putSlot
  split
  · exact h.setSlot y sl
  · rename_i hy
    unfold Obj.KeysND at *
    simp only [List.map_append, List.map_cons, List.map_nil]
    rw [List.nodup_append]
    refine ⟨h, List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩, ?_⟩
    intro a ha b hb hab
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    subst hb
    subst hab
    exact hy (lookup_isSome_of_mem ha)

theorem Obj.KeysND.of_ofVersion (sp : Spec V T) (w : Version V) (cut : Option Nat) :
    (Obj.ofVersion sp w cut).KeysND := by
  unfold Obj.KeysND Obj.ofVersion
  simp only [List.map_map]
  have : ((·.1) ∘ fun y => (y, Slot.stream (w.ref? y))) = (id : NodeId → NodeId) := by
    funext y; rfl
  rw [this, List.map_id]
  exact nodup_eraseDups _

theorem Obj.KeysND.of_canonOfVersion (sp : Spec V T) (S : Stream V T) (s : Nat) (w : Version V) :
    (canonOfVersion sp S s w).KeysND := by
  unfold SIS.canonOfVersion
  apply (Obj.KeysND.of_ofVersion sp w _).of_slots (f := fun p => match p.2 with
    | Slot.stream r => (p.1, Slot.stream (ruleRRef S s p.1 r))
    | sl => (p.1, sl)) _ rfl
  intro q
  split <;> rfl

theorem Obj.KeysND.nil (o : Obj V) (h : o.slots = []) : o.KeysND := by
  unfold Obj.KeysND; rw [h]; exact List.nodup_nil

/-! ## Memories -/

theorem SlotsND.obj {m : Mem V} (hm : SlotsND m) {h : Nat} {o : Obj V} (ho : m.obj? h = some o) :
    o.KeysND :=
  hm (h, o) (mem_of_lookup m.objs h o ho)

theorem SlotsND.setObj {m : Mem V} (hm : SlotsND m) (h : Nat) {o : Obj V} (ho : o.KeysND) :
    SlotsND (m.setObj h o) := by
  intro p hp
  unfold Mem.setObj at hp
  simp only [List.mem_cons, List.mem_filter] at hp
  rcases hp with rfl | ⟨hp, -⟩
  · exact ho
  · exact hm p hp

theorem SlotsND.addObj {m : Mem V} (hm : SlotsND m) {o : Obj V} (ho : o.KeysND) :
    SlotsND (m.addObj o).1 := by
  intro p hp
  unfold Mem.addObj at hp
  simp only [List.mem_cons] at hp
  rcases hp with rfl | hp
  · exact ho
  · exact hm p hp

theorem SlotsND.setTable {m : Mem V} (hm : SlotsND m) (y : NodeId) (h : Nat) : SlotsND (m.setTable y h) :=
  hm

/-- A memory whose objects are m's, each with its slots mapped pointee by
pointee. -/
theorem SlotsND.map_objs {m m' : Mem V} (hm : SlotsND m) {f : Nat × Obj V → Nat × Obj V}
    (he : m'.objs = m.objs.map f) (hf : ∀ p ∈ m.objs, (f p).2.slots.map (·.1) = p.2.slots.map (·.1)) :
    SlotsND m' := by
  intro p hp
  rw [he, List.mem_map] at hp
  obtain ⟨q, hq, rfl⟩ := hp
  unfold Obj.KeysND
  rw [hf q hq]
  exact hm q hq

/-- The object at h made canonical and the table's for y. -/
theorem SlotsND.canonical {m : Mem V} (hm : SlotsND m) (h : Nat) (y : NodeId) :
    SlotsND (match m.obj? h with
      | some o => (m.setObj h { o with canonical := true }).setTable y h
      | none => m) := by
  split
  · rename_i o ho
    have hk : o.KeysND := hm.obj ho
    exact (hm.setObj h (o := { o with canonical := true }) hk).setTable _ _
  · exact hm

/-- The slot of object hp for y set to a memory slot. -/
theorem SlotsND.link {m : Mem V} (hm : SlotsND m) (hp : Nat) (y : NodeId) (h : Nat) :
    SlotsND (match m.obj? hp with
      | some op => m.setObj hp (op.setSlot y (Slot.mem h))
      | none => m) := by
  split
  · rename_i op hop
    exact hm.setObj _ ((hm.obj hop).setSlot _ _)
  · exact hm

/-! ## Stage 1's operations, and its startup -/

theorem SlotsND.register {m : Mem V} (hm : SlotsND m) (h1 : Nat) : SlotsND (m.register h1).1 := by
  unfold Mem.register
  split
  · exact hm
  · split
    · exact hm.setTable _ _
    · split
      · exact hm
      · split
        · split
          · exact hm.setTable _ _
          · exact hm
        · exact hm.setTable _ _

theorem SlotsND.makeCanonical {m : Mem V} (hm : SlotsND m) (hp : Nat) (y : NodeId) (h1 : Nat) :
    SlotsND (m.makeCanonical hp y h1).1 := by
  unfold Mem.makeCanonical
  exact (hm.canonical _ y).link hp y _

theorem SlotsND.follow {m : Mem V} (hm : SlotsND m) (sp : Spec V T) (S : Stream V T) (hp : Nat)
    (y : NodeId) (w : Bool) : SlotsND (m.follow sp S hp y w).1 := by
  unfold Mem.follow
  split
  · exact hm
  · split
    · split
      · exact hm.makeCanonical _ _ _
      · exact hm
    · exact hm
  · simp only
    split
    · exact hm
    · rename_i m1 h1 hl
      have hm1 : SlotsND m1 := by
        split at hl
        · simp only [Option.some.injEq, Prod.mk.injEq] at hl
          obtain ⟨rfl, -⟩ := hl
          exact hm
        · split at hl
          · cases hl
          · split at hl
            · cases hl
            · simp only [Option.some.injEq] at hl
              have key := congrArg Prod.fst hl
              simp only at key
              rw [← key]
              exact (hm.addObj (Obj.KeysND.of_ofVersion _ _ _)).register _
      have hm2 := hm1.link hp y h1
      split
      · split
        · exact hm2.makeCanonical _ _ _
        · exact hm2
      · exact hm2

theorem SlotsND.reachOnPath {m : Mem V} (hm : SlotsND m) (sp : Spec V T) (S : Stream V T) (P : Struct V)
    (j : Time) (path : List NodeId) (x : NodeId) : SlotsND (m.reachOnPath sp S P j path x) := by
  unfold Mem.reachOnPath
  split
  · exact hm
  · simp only
    split
    · split
      · exact hm.follow _ _ _ _ _
      · exact hm
    · exact hm

theorem Obj.KeysND.upd1 {o : Obj V} (h : o.KeysND) (sp : Spec V T) (P : Struct V) (j : Time) (m1 : Mem V)
    (y : NodeId) : (upd1 sp P j m1 o y).KeysND := by
  unfold SIS.upd1
  split
  · exact h.putSlot _ _
  · exact h

theorem Obj.KeysND.updObj {o : Obj V} (h : o.KeysND) (sp : Spec V T) (P : Struct V) (j : Time) (m1 : Mem V)
    (v : V) : (updObj sp P j m1 o v).KeysND := by
  unfold SIS.updObj
  have key : ∀ (L : List NodeId) (o' : Obj V), o'.KeysND → (L.foldl (SIS.upd1 sp P j m1) o').KeysND := by
    intro L
    induction L with
    | nil => intro o' h'; exact h'
    | cons y L ih => intro o' h'; exact ih _ (h'.upd1 sp P j m1 y)
  exact key _ _ h

theorem SlotsND.addNew {m : Mem V} (hm : SlotsND m) (nn : NewNode) : SlotsND (SIS.addNew m nn) :=
  (hm.addObj (Obj.KeysND.nil _ rfl)).setTable _ _

theorem SlotsND.foldl_addNew {m : Mem V} (hm : SlotsND m) (L : List NewNode) :
    SlotsND (L.foldl SIS.addNew m) := by
  induction L generalizing m with
  | nil => exact hm
  | cons nn L ih => exact ih (hm.addNew nn)

theorem SlotsND.applyChange {m : Mem V} (hm : SlotsND m) (sp : Spec V T) (P : Struct V) (j : Time)
    (c : Changes V) : SlotsND (m.applyChange sp P j c) := by
  rw [applyChange_eq]
  have key : ∀ (L : List (NodeId × V)) (m' : Mem V), SlotsND m' →
      SlotsND (L.foldl (SIS.addsStep sp P j (c.new.foldl SIS.addNew m)) m') := by
    intro L
    induction L with
    | nil => intro m' h'; exact h'
    | cons a L ih =>
      intro m' h'
      apply ih
      unfold SIS.addsStep
      split
      · exact h'
      · split
        · exact h'
        · rename_i o ho
          exact h'.setObj _ ((h'.obj ho).updObj sp P j _ a.2)
  exact key _ _ (hm.foldl_addNew _)

theorem SlotsND.canonicalNode {m : Mem V} (hm : SlotsND m) (sp : Spec V T) (S : Stream V T) (x : NodeId) :
    SlotsND (m.canonicalNode sp S x) := by
  unfold Mem.canonicalNode
  split
  · exact hm
  · split
    · exact (hm.addObj (Obj.KeysND.of_canonOfVersion _ _ _ _)).setTable _ _
    · exact hm

theorem SlotsND.rerunStep {acc : Mem V × Struct V} (h : SlotsND acc.1) (sp : Spec V T) (S : Stream V T)
    (j : Nat) : SlotsND (SIS.rerunStep sp S acc j).1 := by
  unfold SIS.rerunStep
  split
  · split
    · simp only
      have hw : ∀ (L : List NodeId) (m : Mem V), SlotsND m → ∀ P path, SlotsND (L.foldl
          (Mem.reachOnPath sp S P j path) m) := by
        intro L
        induction L with
        | nil => intro m h _ _; exact h
        | cons x L ih => intro m h P path; exact ih _ (h.reachOnPath _ _ _ _ _ _) P path
      have hc : ∀ (L : List NodeId) (m : Mem V), SlotsND m → SlotsND (L.foldl (Mem.canonicalNode sp S) m) := by
        intro L
        induction L with
        | nil => intro m h; exact h
        | cons x L ih => intro m h; exact ih _ (h.canonicalNode _ _ _)
      exact hc _ _ ((hw _ _ h _ _).applyChange _ _ _ _)
    · exact h
  · exact h

theorem slotsND_lazySec (sp : Spec V T) (S : Stream V T) : SlotsND (lazySec sp S) := by
  unfold lazySec
  have key : ∀ (L : List NodeId) (m : Mem V), SlotsND m → SlotsND (L.foldl (secStep sp S) m) := by
    intro L
    induction L with
    | nil => intro m h; exact h
    | cons x L ih =>
      intro m h
      apply ih
      unfold secStep
      split
      · split
        · exact h
        · exact (h.addObj (Obj.KeysND.of_canonOfVersion _ _ _ _)).setTable _ _
      · exact h
  exact key _ _ (fun p hp => by cases hp)

theorem SlotsND.lazyRoot {m : Mem V} (hm : SlotsND m) (sp : Spec V T) (S : Stream V T) :
    SlotsND (SIS.lazyRoot sp S m) := by
  unfold SIS.lazyRoot
  by_cases hv : sp.virt = true
  · simp only [hv, ↓reduceIte]
    exact (hm.addObj (o := { (canonOfVersion sp S (lastSp S) (rootVersion sp (lastSp S)
      (topsRead sp S (lastSp S) true))) with hist := (rootVersion sp (lastSp S)
      (topsRead sp S (lastSp S) true)).hist, pos := none })
      (Obj.KeysND.of_canonOfVersion _ _ _ _)).setTable SIS.root m.next
  · simp only [hv, Bool.false_eq_true, ↓reduceIte]
    cases hc : m.canonicalOf root with
    | some h0 => exact hm
    | none =>
      simp only
      cases ht : topVersion S (lastSp S) true with
      | none => exact hm
      | some w => exact (hm.addObj (Obj.KeysND.of_canonOfVersion sp S (lastSp S) w)).setTable SIS.root m.next

theorem SlotsND.linkCanonical {m : Mem V} (hm : SlotsND m) : SlotsND m.linkCanonical := by
  apply hm.map_objs rfl
  intro p _
  dsimp only
  split
  · rfl
  · apply keys_map_fst
    intro q
    split
    · split
      · split
        · split <;> rfl
        · rfl
      · rfl
    · rfl

theorem slotsND_lazyStartup (sp : Spec V T) (S : Stream V T) : SlotsND (lazyStartup sp S) := by
  rw [lazyStartup_eq]
  have h0 : SlotsND (lazyBase sp S) := ((slotsND_lazySec sp S).lazyRoot sp S).linkCanonical
  have key : ∀ (L : List Nat) (acc : Mem V × Struct V), SlotsND acc.1 →
      SlotsND (L.foldl (rerunStep sp S) acc).1 := by
    intro L
    induction L with
    | nil => intro acc h; exact h
    | cons j L ih => intro acc h; exact ih _ (SlotsND.rerunStep h _ _ _)
  exact key _ _ h0

/-! ## The Level 4 operations, its startup and its runs -/

end SIS
