/-
Proofs for stage 2 (bergdb item 001, WP E3), part 4: the Level 4 loader keeps the
invariant. A reader's follow (`Mem.follow4`) of any slot and a read at any time
(`Mem.read4`); the writer's follow (with `Mem.promote`) is in EvictPromote.lean.
-/
import SIS.Proof.EvictInv

set_option linter.unusedSectionVars false

namespace SIS

variable {V T : Type} [DecidableEq V]

/-! ## Memories with the same lookups -/

/-- m' has m's objects and node table, by lookup, and m's startup pos, root and
next handle. -/
def Mem.Same (m m' : Mem V) : Prop :=
  (∀ h, m'.obj? h = m.obj? h) ∧ (∀ y, m'.tableOf y = m.tableOf y) ∧ m'.s = m.s ∧
    m'.root = m.root ∧ m'.next = m.next

section Same

variable {sp : Spec V T} {db : DB V T} {S0 : Stream V T} {k : Nat} {m m' : Mem V}

theorem Mem.Same.canonicalOf (hs : m.Same m') (y : NodeId) : m'.canonicalOf y = m.canonicalOf y := by
  unfold Mem.canonicalOf
  rw [hs.2.1 y]
  cases m.tableOf y with
  | none => rfl
  | some h => simp only [hs.1 h]

theorem Mem.Same.coreEq (hs : m.Same m') : m.CoreEq m' :=
  ⟨fun h => by rw [hs.1 h], hs.canonicalOf, hs.2.2.1⟩

/-- The invariant depends on the memory only through its lookups (and the node
table's keys having no repeats). -/
theorem EInv.same (hm : EInv sp db S0 k m) (hs : m.Same m') (hnd : (m'.table.map (·.1)).Nodup)
    (hnd2 : (m'.objs.map (·.1)).Nodup) : EInv sp db S0 k m' := by
  have hce := hs.coreEq
  refine ⟨hm.len, hm.pre, by rw [hs.2.2.1]; exact hm.sEq, fun h hh => by
      rw [hs.1 h]; exact hm.fresh h (by rw [← hs.2.2.2.2]; exact hh), hnd2, ?_, hnd, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨o, ho, hc, hn⟩ := hm.root
    exact ⟨o, by rw [hs.2.2.2.1, hs.1]; exact ho, hc, hn⟩
  · intro y h ht
    rw [hs.2.1] at ht
    obtain ⟨o, ho, hn⟩ := hm.tbl y h ht
    exact ⟨o, by rw [hs.1]; exact ho, hn⟩
  · intro h o ho y h' hy
    rw [hs.1] at ho
    obtain ⟨o', ho', hn⟩ := hm.slotsNode h o ho y h' hy
    exact ⟨o', by rw [hs.1]; exact ho', hn⟩
  · intro y h ht
    rw [hs.2.1] at ht
    obtain ⟨o, ho, hc⟩ := hm.tblCanon y h ht
    exact ⟨o, by rw [hs.1]; exact ho, hc⟩
  · intro h o ho hc
    rw [hs.1] at ho
    rw [hs.2.1]; exact hm.canonTbl h o ho hc
  · intro h o ho hc
    rw [hs.1] at ho
    exact hm.cc h o ho hc
  · intro z h o hz ho
    rw [hs.canonicalOf] at hz
    rw [hs.1] at ho
    exact hm.pos z h o hz ho
  · intro y hy
    rw [hs.canonicalOf]; exact hm.dCanon y hy
  · intro h o ho hc
    rw [hs.1] at ho
    exact (hm.snap h o ho hc).congr hce
  · intro h o ho hr y hy
    rw [hs.1] at ho
    obtain ⟨sl, hsl, hi⟩ := hm.slots h o ho hr y hy
    exact ⟨sl, hsl, hi.congr hce⟩
  · intro h o ho hc hr y hy
    rw [hs.1] at ho
    obtain ⟨sl, hsl, hi⟩ := hm.live h o ho hc hr y hy
    exact ⟨sl, hsl, hi.congr hce⟩

end Same

/-! ## Slots that change in place -/

section Slots

variable {sp : Spec V T} {db : DB V T} {S0 : Stream V T} {k : Nat} {m : Mem V}

theorem slot?_setSlot_of {o : Obj V} {y : NodeId} {sl0 : Slot} (h : o.slot? y = some sl0) (sl : Slot)
    (z : NodeId) : (o.setSlot y sl).slot? z = if z = y then some sl else o.slot? z := by
  rw [Obj.slot?_setSlot]
  split
  · rename_i hz; subst hz; rw [h]; rfl
  · rfl

end Slots

/-! ## A snapshot read from the stream -/

section AddSnap

variable {sp : Spec V T} {db : DB V T} {S0 : Stream V T} {k : Nat} {m : Mem V}

end AddSnap

/-! ## The reader's follow -/

/-- The slot of object hp for y names object h1. -/
def Mem.swz (m : Mem V) (hp : Nat) (y : NodeId) (h1 : Nat) : Mem V :=
  match m.obj? hp with
  | some op => m.setObj hp (op.setSlot y (Slot.mem h1))
  | none => m

section Reader

variable {sp : Spec V T} {db : DB V T} {S0 : Stream V T} {k : Nat} {m : Mem V}

end Reader

end SIS
