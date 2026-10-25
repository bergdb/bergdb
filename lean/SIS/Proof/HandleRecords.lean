/-
Proofs for the physical layer with handles (bergdb item 009, phase 2, step 2d):
T-CACHE for handles (`TC_handles`, SIS/HandleTheorems.lean). For a run of
BergDB's algorithm that meets the assumptions, from the startup with handles
from R(0), with any reads and evictions after each transaction and no restart,
the physical writer with handles appends exactly the model's records and leaves
the model's D (`TC_handles_records`), and the memory meets the invariants of
`TC_handles` (`tc_handles`).

The proof follows E3's for Evict.lean (SIS/Proof/Evict*.lean), part by part:
SIS/Proof/HandleMem.lean (the memory's operations), HandleInv.lean (the
invariant `HEInv`; eviction keeps it), HandleFollow.lean (the readers' follow:
the fast path, the slow path's write-back, the live handle, the load),
HandleRead.lean (reads and the operations between transactions keep the
invariant; a read at the last time gives P there), HandleWalk.lean (the
writer's promote and its walk), HandleApply.lean and HandleApplyInv.lean (the
change, with A-COPY), HandleWrite.lean and HandleWrites.lean (the writer's two
loops give the model's versions), HandleStepInv.lean (the invariant after the
record), HandleTrans.lean (one transaction, and runs from a memory with the
invariant), HandleInit.lean (the startup with handles from R(0) has it).
-/
import SIS.Proof.HandleInit

set_option linter.unusedSectionVars false

namespace SIS

variable {V T : Type} [DecidableEq V]

section Facts

variable {sp : Spec V T} {db : DB V T} {S0 : Stream V T} {k : Nat} {m : HMem V}

/-- INV-SNAP in the terms of HandleTheorems.lean. -/
theorem HEInv.hsnap (hm : HEInv sp db S0 k m) : HSnapOK db m := by
  intro a o ho hc
  obtain ⟨r, w, h1, h2, h3, h4, h5, -, -⟩ := hm.snap a o ho hc
  exact ⟨r, w, h1, h2, h3, h4, h5⟩

/-- INV-SLOT in the terms of HandleTheorems.lean: the record rule gives every
pointee of a relevant object its latest version. -/
theorem HEInv.hslot (hm : HEInv sp db S0 k m) : HSlotOK sp S0 db k m := by
  intro a o ho hc hw hr y hy
  obtain ⟨p, hp, hi1, hi2⟩ := hm.slots a o ho ⟨hc, hw, hr⟩ y hy
  refine ⟨by rw [hp]; rfl, ?_, ?_⟩
  · unfold HMem.refOf
    cases hD : inD db.D y with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, hp, Option.bind_some]
      exact hi1 hD
    | true =>
      simp only [↓reduceIte]
      obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp (hm.dCanon y hD)
      rw [hb]
      obtain ⟨ob, hob, hcb, hnb⟩ := hm.obj_of_canonicalOf hb
      simp only [hob, Option.bind_some]
      rw [hm.pos b ob hob hcb, hnb]
  · intro hD
    rcases hi2 hD with ⟨n, hpn, htn, hcs⟩ | ⟨hx, a', b', ha', hb', hab⟩
    · exact Or.inl ⟨p, n, hp, hpn, htn, hcs⟩
    · exact Or.inr ⟨hx, a', b', mem_of_dOf ha', mem_of_dOf hb', hab⟩

end Facts

section Main

variable {sp : Spec V T} {al : Algo V T}

/-- T-CACHE's records for handles: for a run of BergDB's algorithm (`javaTest`,
with marking) that meets the assumptions, those of the physical layer and those
of stage 2, from the startup with handles from R(0), with any reads and
evictions after each transaction and no restart, after every transaction and
its operations the physical writer with handles has appended exactly the
model's records and left the model's D: the state is the model's. -/
theorem TC_handles_records (ts : List (T × Bool × List HCacheOp)) (hok : RunOK sp al (ts.map (·.1)))
    (hph : PhysRunOK sp al (ts.map (·.1))) (hev : EvictRunOK sp al (ts.map (·.1)))
    (hj : al.stillDirty = javaTest sp) (hmk : al.mark = true) (hnr : ∀ p ∈ ts, p.2.1 = false) :
    ∀ j ≤ ts.length, (runHandles sp al (ts.take j)).1 = run sp al ((ts.take j).map (·.1)) := by
  intro j hjl
  obtain ⟨e1, -, -⟩ := TC_runH hok hph hev hj hmk hnr (heinv_init hok.1) j hjl
  rw [e1]
  unfold st
  rw [List.map_take]

/-- `TC_handles` (SIS/HandleTheorems.lean) holds. -/
theorem tc_handles (sp : Spec V T) (al : Algo V T) : TC_handles sp al := by
  intro ts hok hph hev hj hmk hnr j hjl
  obtain ⟨e1, -, e3⟩ := TC_runH hok hph hev hj hmk hnr (heinv_init hok.1) j hjl
  have hst : st sp al (ts.map (·.1)) j = run sp al ((ts.take j).map (·.1)) := by
    unfold st; rw [List.map_take]
  rw [hst] at e1 e3
  exact ⟨e1, e3.tbl, e3.hcan, e3.hsnap, e3.hslot, e3.ruleR, e3.liveW, e3.hwritten⟩

end Main

end SIS
