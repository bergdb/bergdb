/-
Proofs about reclaim, part 13 (bergdb item 001, WP R4, T9): reads in the
running process after a cut. A physical read at a time t from f on, through
the Level 4 loader, reads only versions that `ReadsPhys` covers, so a safe cut
(`CutOK`'s part 2) changes nothing it reads. What it needs of the memory
(`CInv`): a canonical object of a clean node names, for each pointee, a
canonical object or a record at or after the one that the node's latest
version names; one of a node of D names, by a memory slot to a snapshot, a
pointee of D at its latest version; a virtual root's object names its root
children of D by memory slots to their canonical objects and the others at
their latest versions; and no snapshot is of a version that Rule A put back
and that is still in D.
-/
import SIS.Proof.EvictHist
import SIS.Proof.EvictTrans
import SIS.Proof.CutStream

set_option linter.unusedSectionVars false

namespace SIS

variable {V T : Type} [DecidableEq V]

/-! ## The invariant -/

/-! ## The loader on a stream cut safely -/

section Load

variable {sp : Spec V T} {S0 S : Stream V T}

end Load

/-! ## The slots that a read at t follows -/

section Slots

variable {sp : Spec V T} {db : DB V T} {S0 : Stream V T} {k : Nat} {m : Mem V}

end Slots

/-! ## The reader's follow -/

section Reader

variable {sp : Spec V T} {db : DB V T} {S0 : Stream V T} {k : Nat} {m : Mem V}

end Reader

/-! ## Reads in the running process after a safe cut (T9) -/

section ReadCut

variable {sp : Spec V T} {db : DB V T} {S0 : Stream V T} {k : Nat} {m : Mem V}

theorem foldl_eq_inv {α β : Type} (f g : α → β → α) (I : α → Prop) :
    ∀ (l : List β), (∀ a z, z ∈ l → I a → f a z = g a z ∧ I (g a z)) →
      ∀ a, I a → l.foldl f a = l.foldl g a ∧ I (l.foldl g a) := by
  intro l
  induction l with
  | nil => intro _ a h; exact ⟨rfl, h⟩
  | cons z l ih =>
    intro hstep a ha
    simp only [List.foldl_cons]
    obtain ⟨e, h2⟩ := hstep a z List.mem_cons_self ha
    rw [e]
    exact ih (fun a' z' hz' ha' => hstep a' z' (List.mem_cons_of_mem z hz') ha') _ h2

end ReadCut

/-! ## Unswizzle and release -/

section Cache

variable {sp : Spec V T} {db : DB V T} {S0 : Stream V T} {k : Nat} {m : Mem V}

/-- A reference of the latest version of a node is at or before the latest
version of the pointee. -/
theorem Inv.ref_le_lv (hinv : Inv sp db k) {x : NodeId} {v : Version V} (hv : db.S.lv x = some v)
    {y : NodeId} {r0 : Nat} (hr0 : v.ref? y = some r0) :
    ∃ u, db.S.lv y = some u ∧ r0 ≤ u.recNo := by
  obtain ⟨u0, hu0⟩ := hinv.ref_versionAt (hinv.lv_at hv) hr0
  obtain ⟨r', u', h1, h2, hle⟩ := lv_recNo_ge hu0
  rw [(hinv.version_node h1).2.1.symm] at hle
  exact ⟨u', h2, hle⟩

end Cache

/-! ## The writer's walk -/

section Walk

variable {sp : Spec V T} {db : DB V T} {S0 : Stream V T} {k : Nat} {m : Mem V}

end Walk

end SIS
