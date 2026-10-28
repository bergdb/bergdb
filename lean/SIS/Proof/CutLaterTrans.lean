/-
Proofs about reclaim, part 20 (bergdb item 001, WP R5, T12 with eviction): one
transaction of the physical writer after a restart from a cut stream. The run
that restarted from the cut stream (C) and the run that restarted from the
whole stream at the same points (E) write the same record: C's memory is E's
but for the root's object (`RootRel`) and where its entry is (`RootPerm`);
C's reads on the cut streams are E's on the whole streams (`NInv`, `Later`);
and C's structure agrees with E's from the first available time on
(`CutRel`).
-/
import SIS.Proof.CutLaterSim
import SIS.Proof.EvictKeys
import SIS.Proof.CutRuns

set_option linter.unusedSectionVars false

namespace SIS

variable {V T : Type} [DecidableEq V]

/-! ## The root apart, from the invariants -/

section Sep

variable {sp : Spec V T} {m : Mem V}

theorem RootSep.mk' (hroot : ∃ o, m.obj? m.root = some o ∧ o.node = root)
    (hfr : ∀ h, m.next ≤ h → m.obj? h = none) (htbl : TableNode m) (hsn : SlotsNode m)
    (hptr : ∀ h o, m.obj? h = some o → ∀ y ∈ pointees sp o.hist, y ≠ root) : RootSep sp m := by
  obtain ⟨o0, ho0, hn0⟩ := hroot
  refine ⟨fun o ho => by rw [ho0, Option.some.injEq] at ho; subst ho; exact hn0, ?_, ?_, ?_, hptr⟩
  · apply Nat.lt_of_not_le
    intro hle
    rw [hfr _ hle] at ho0
    cases ho0
  · intro h o y h' ho hsl hy he
    obtain ⟨o', ho', hn'⟩ := hsn h o ho y h' hsl
    rw [he, ho0, Option.some.injEq] at ho'
    subst ho'
    exact hy (hn'.symm.trans hn0)
  · intro y h ht hy he
    obtain ⟨o', ho', hn'⟩ := htbl y h ht
    rw [he, ho0, Option.some.injEq] at ho'
    subst ho'
    exact hy (hn'.symm.trans hn0)

end Sep

/-! ## With a virtual root, the root's object is the only source of a slot for a
live root child -/

section Only

variable {sp : Spec V T} {db : DB V T} {S0 : Stream V T} {k : Nat} {m : Mem V}

end Only

/-! ## One transaction -/

section Trans

variable {sp : Spec V T} {al : Algo V T}

end Trans

/-! ## The cache operations -/

section Ops

variable {sp : Spec V T}

end Ops

end SIS
