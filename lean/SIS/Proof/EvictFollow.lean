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

section Same

variable {sp : Spec V T} {db : DB V T} {S0 : Stream V T} {k : Nat} {m m' : Mem V}

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
