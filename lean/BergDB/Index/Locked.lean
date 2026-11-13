/-
The user indexes of BergDB 2026.4 in Lean: a build step's locked phase
(bergdb 020-29).

The heart of 020-26, section 4, point 8, and of 020-10, section 6.1: "under
it [the lock] only the writers that read the index set before can collide
with the step". While a build holds the index manager's lock, no writer comes
to be able to commit a write of an object key (it would have to read an index
set, under the lock), and every write of an object key is the commit of a
writer that could commit one when the lock was taken, which then cannot again
while the lock is held. So a step in its locked phase is refused at most once
per writer that could commit when the lock was taken. Keys with a suffix are
in no step's read set (020-18, F1). The temporal part of point 8 (fair runs,
the step's tries) is not here.
-/
import BergDB.Index.Steps

namespace BergDB.Index

variable {V F L W : Type}

/-- A writer's transaction that can commit a write of an object key: it writes
one, and has read the index set of each object key it writes. -/
def CanCommitObj (sp : Spec V F L) : WSt V F → Prop
  | .idle => False
  | .run ws _ _ _ S => (∃ k, ws k = true ∧ sp.isObj k = true) ∧
      ∀ k, ws k = true → sp.isObj k = true → S k ≠ none

variable [DecidableEq W]

/-- While a build holds the lock, a writer that can commit a write of an object
key after a step could before it, in the same state: a step that keeps the
lock reads no index set, and a transaction that starts has read none. -/
theorem locked_no_new_writer {sp : Spec V F L} {s s' : Sys V F L W} {lb : Lbl W}
    (hst : Step sp s lb s')
    {n : Name} {g : Gen} (hl : s.m.lock = .bld n g) (hl' : s'.m.lock = .bld n g) (w : W)
    (hc : CanCommitObj sp (s'.m.wr w)) : s'.m.wr w = s.m.wr w := by
  cases hst with
  | wStart w' ws nv _ =>
    show upd s.m.wr w' _ w = s.m.wr w
    by_cases hw : w = w'
    · exfalso
      change CanCommitObj sp (upd s.m.wr w' (.run ws nv s.st.now s.st.data (fun _ => none)) w)
        at hc
      rw [hw, upd_same] at hc
      obtain ⟨⟨k, hk, hob⟩, hS⟩ := hc
      exact hS k hk hob rfl
    · exact upd_ne _ _ hw
  | wReadS w' k ws nv R old S _ hfree => rw [hl] at hfree; cases hfree
  | wCommit w' ws nv R old S _ _ =>
    show upd s.m.wr w' _ w = s.m.wr w
    by_cases hw : w = w'
    · exfalso
      change CanCommitObj sp (upd s.m.wr w' .idle w) at hc
      rw [hw, upd_same] at hc; exact hc
    · exact upd_ne _ _ hw
  | wDrop w' _ =>
    show upd s.m.wr w' _ w = s.m.wr w
    by_cases hw : w = w'
    · exfalso
      change CanCommitObj sp (upd s.m.wr w' .idle w) at hc
      rw [hw, upd_same] at hc; exact hc
    · exact upd_ne _ _ hw
  | crash pre x rest _ => change Lock.free = _ at hl'; cases hl'
  | _ => rfl

/-- While a build holds the lock, a step that writes an object key is the commit
of a writer that could commit a write of an object key, which it ends. -/
theorem locked_obj_write {sp : Spec V F L} {s s' : Sys V F L W} {lb : Lbl W}
    (hst : Step sp s lb s')
    {n : Name} {g : Gen} (hl' : s'.m.lock = .bld n g)
    {k : Key} (hk : sp.isObj k = true) (hw : s'.st.wk k ≠ s.st.wk k) :
    ∃ w, CanCommitObj sp (s.m.wr w) ∧ s'.m.wr w = .idle := by
  cases hst with
  | wSuffix ws nv hsuf =>
    exfalso; apply hw
    change writeTimes s.st.wk ws (s.st.now + 1) k = s.st.wk k
    cases hwk : ws k with
    | true => rw [hsuf k hwk] at hk; cases hk
    | false => exact writeTimes_no hwk
  | wCommit w ws nv R old S hw' hc =>
    have hwk : ws k = true := by
      cases hwk : ws k with
      | true => rfl
      | false =>
        exfalso; apply hw
        change writeTimes s.st.wk ws (s.st.now + 1) k = s.st.wk k
        exact writeTimes_no hwk
    refine ⟨w, ?_, ?_⟩
    · rw [hw']
      refine ⟨⟨k, hwk, hk⟩, fun k' hk' hob' => ?_⟩
      obtain ⟨m, hm, _⟩ := hc k' hk' hob'
      rw [hm]; intro h; cases h
    · show upd s.m.wr w .idle w = .idle; exact upd_same _ _ _
  | crash pre x rest _ => exfalso; change Lock.free = _ at hl'; cases hl'
  | _ => exact absurd rfl hw

/-- The locked phase over `d` steps from `r i`, by induction on `d`. -/
theorem locked_phase_aux {sp : Spec V F L} (r : Nat → Sys V F L W) (i : Nat)
    {n : Name} {g : Gen} :
    ∀ d, (∀ t, i ≤ t → t < i + d → ∃ lb, Step sp (r t) lb (r (t + 1))) →
      (∀ t, i ≤ t → t ≤ i + d → (r t).m.lock = .bld n g) →
      (∀ w, CanCommitObj sp ((r (i + d)).m.wr w) → (r (i + d)).m.wr w = (r i).m.wr w) ∧
      (∀ k, sp.isObj k = true → (r (i + d)).st.wk k ≠ (r i).st.wk k →
        ∃ w, CanCommitObj sp ((r i).m.wr w) ∧ ¬ CanCommitObj sp ((r (i + d)).m.wr w)) := by
  intro d
  induction d with
  | zero =>
    intro _ _
    exact ⟨fun _ _ => rfl, fun _ _ h => absurd rfl h⟩
  | succ d ih =>
    intro hst hlock
    have hst' : ∀ t, i ≤ t → t < i + d → ∃ lb, Step sp (r t) lb (r (t + 1)) :=
      fun t h1 h2 => hst t h1 (by omega)
    have hlock' : ∀ t, i ≤ t → t ≤ i + d → (r t).m.lock = .bld n g :=
      fun t h1 h2 => hlock t h1 (by omega)
    obtain ⟨ih1, ih2⟩ := ih hst' hlock'
    have hstep : ∃ lb, Step sp (r (i + d)) lb (r (i + d + 1)) := hst (i + d) (by omega) (by omega)
    have hlj := hlock (i + d) (by omega) (by omega)
    have hlj1 : (r (i + d + 1)).m.lock = .bld n g := hlock (i + d + 1) (by omega) (by omega)
    -- a writer that can commit at the next state could before, in the same state
    have hkeep : ∀ w, CanCommitObj sp ((r (i + d + 1)).m.wr w) →
        (r (i + d + 1)).m.wr w = (r (i + d)).m.wr w :=
      fun w hc => locked_no_new_writer hstep.choose_spec hlj hlj1 w hc
    show (∀ w, CanCommitObj sp ((r (i + d + 1)).m.wr w) → (r (i + d + 1)).m.wr w = (r i).m.wr w) ∧
      (∀ k, sp.isObj k = true → (r (i + d + 1)).st.wk k ≠ (r i).st.wk k →
        ∃ w, CanCommitObj sp ((r i).m.wr w) ∧ ¬ CanCommitObj sp ((r (i + d + 1)).m.wr w))
    refine ⟨fun w hc => ?_, fun k hk hne => ?_⟩
    · have h1 := hkeep w hc
      rw [h1] at hc ⊢
      exact ih1 w hc
    · by_cases hsame : (r (i + d + 1)).st.wk k = (r (i + d)).st.wk k
      · rw [hsame] at hne
        obtain ⟨w, hci, hcj⟩ := ih2 k hk hne
        refine ⟨w, hci, fun hc => hcj ?_⟩
        rw [← hkeep w hc]; exact hc
      · obtain ⟨w, hcj, hidle⟩ := locked_obj_write hstep.choose_spec hlj1 hk hsame
        refine ⟨w, ?_, ?_⟩
        · rw [← ih1 w hcj]; exact hcj
        · rw [hidle]; exact id

/-- **The locked phase** (020-26, section 4, point 8): over a run from `r i` to
`r j` during which a build holds the lock, (1) a writer that can commit a
write of an object key at `r j` was so at `r i`, in the same state; (2) if an
object key was written, some writer that could commit at `r i` cannot at
`r j`. So each object key that a locked step reads can be written, and the
step refused, only by a writer that could commit when the lock was taken, and
by each of them at most once. -/
theorem locked_phase {sp : Spec V F L} (r : Nat → Sys V F L W) {i j : Nat} (hij : i ≤ j)
    {n : Name} {g : Gen}
    (hst : ∀ t, i ≤ t → t < j → ∃ lb, Step sp (r t) lb (r (t + 1)))
    (hlock : ∀ t, i ≤ t → t ≤ j → (r t).m.lock = .bld n g) :
    (∀ w, CanCommitObj sp ((r j).m.wr w) → (r j).m.wr w = (r i).m.wr w) ∧
      (∀ k, sp.isObj k = true → (r j).st.wk k ≠ (r i).st.wk k →
        ∃ w, CanCommitObj sp ((r i).m.wr w) ∧ ¬ CanCommitObj sp ((r j).m.wr w)) := by
  obtain ⟨d, rfl⟩ : ∃ d, j = i + d := ⟨j - i, by omega⟩
  exact locked_phase_aux r i d hst hlock

end BergDB.Index
