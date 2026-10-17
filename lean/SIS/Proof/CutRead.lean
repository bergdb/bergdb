/-
Proofs about reclaim, part 2 (bergdb item 001, WP R4): reading a stream cut
before every record that the read needs.
-/
import SIS.Proof.CutStream
import SIS.Proof.Read

set_option linter.unusedSectionVars false

namespace SIS

variable {V T : Type} [DecidableEq V]

/-- Following a pointer on a stream cut at or before s gives what it gives on
the whole stream, when the record it reads, if it reads one, is at the cut or
later. -/
theorem follow_cut {S : Stream V T} {c s : Nat} (hcs : c ≤ s) (y : NodeId) (ref : Option Nat)
    (h : newest S s y = none → ∀ r, ref = some r → (S.versionAt r y).isSome → c ≤ r) :
    follow (cutStream c S) s true y ref = follow S s true y ref := by
  unfold follow
  simp only [ite_true]
  rw [newest_cut hcs]
  cases hn : newest S s y with
  | some w => rfl
  | none =>
    cases ref with
    | none => rfl
    | some r =>
      simp only [Option.bind_some]
      rcases Nat.lt_or_ge r c with hr | hr
      · cases hv : S.versionAt r y with
        | none => rw [versionAt_cut_lt hr, hv]; rfl
        | some w =>
          have := h hn r rfl (by rw [hv]; rfl)
          omega
      · exact versionAt_cut_ge hr y

/-- Reading from version v on a stream cut at or before s gives what it gives
on the whole stream, when every pointer the read follows without Rule R reads
a record at the cut or later. -/
theorem readFrom_cut (sp : Spec V T) (S : Stream V T) {c s : Nat} (hcs : c ≤ s) (t : Time) :
    ∀ (b : Nat) (v : Version V), v.level < b →
      (∀ p ∈ readFrom sp S s true t v, ∀ y ∈ sp.live (p.2.hist.upTo t),
        newest S s y = none → ∀ r, p.2.ref? y = some r → (S.versionAt r y).isSome → c ≤ r) →
      readFrom sp (cutStream c S) s true t v = readFrom sp S s true t v := by
  intro b
  induction b with
  | zero => intro v h; omega
  | succ b ih =>
    intro v hb h
    rw [readFrom_eq, readFrom_eq]
    congr 1
    apply flatMap_congr_mem
    intro y hy
    have hf : follow (cutStream c S) s true y (v.ref? y) = follow S s true y (v.ref? y) :=
      follow_cut hcs y _ (h (v.node, v) (by rw [readFrom_eq]; exact List.mem_cons_self) y hy)
    rw [hf]
    cases hw : follow S s true y (v.ref? y) with
    | none => rfl
    | some w =>
      simp only
      split
      · rename_i hlt
        apply ih w (by omega)
        intro p hp
        apply h p
        rw [readFrom_eq]
        apply List.mem_cons_of_mem
        exact List.mem_flatMap.mpr ⟨y, hy, by rw [hw]; simp only [hlt, ↓reduceIte]; exact hp⟩
      · rfl

/-- Reading from a version that lookups at t may read reaches only versions that
lookups at t may read. -/
theorem readFrom_readsAt (sp : Spec V T) (S : Stream V T) (P : Struct V) (t : Time) :
    ∀ (b : Nat) (v : Version V), v.level < b → ReadsAt sp S P t v →
      ∀ p ∈ readFrom sp S (lastSp S) true t v, ReadsAt sp S P t p.2 := by
  intro b
  induction b with
  | zero => intro v h; omega
  | succ b ih =>
    intro v hb hv p hp
    rw [readFrom_eq] at hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact hv
    · obtain ⟨y, hy, hp⟩ := List.mem_flatMap.mp hp
      cases hw : follow S (lastSp S) true y (v.ref? y) with
      | none => rw [hw] at hp; simp at hp
      | some w =>
        rw [hw] at hp
        simp only at hp
        split at hp
        · rename_i hlt
          exact ih w (by omega) (ReadsAt.child v y w hv hy hw) p hp
        · simp at hp

end SIS
