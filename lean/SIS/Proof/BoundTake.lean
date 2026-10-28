/-
Proofs for T3 for BergDB's take (bergdb 007-08): the take keeps up with its
deadline's distance (`takePolicy_keepsUp`), so the section after a transaction
is shorter than that distance (`take_step`), and runs, with and without
restarts, with settings at most M (`fold_bound`) or after a change of the
setting (`fold_decrease`).
-/
import SIS.Proof.Bound

set_option linter.unusedSectionVars false

namespace SIS

variable {V T : Type} [DecidableEq V]

/-! ### The target of a distance -/

theorem foldl_max_eq_or_mem : ∀ (l : List Nat) (a : Nat), l.foldl max a = a ∨ l.foldl max a ∈ l
  | [], _ => Or.inl rfl
  | y :: l, a => by
    simp only [List.foldl_cons]
    rcases foldl_max_eq_or_mem l (max a y) with h | h
    · rw [h]
      by_cases hay : a ≤ y
      · right; rw [Nat.max_eq_right hay]; simp
      · left; rw [Nat.max_eq_left (by omega)]
    · right; exact List.mem_cons_of_mem _ h

/-- The target of a distance d is 0, or a transaction that begins at least d
before the end of the stream. -/
theorem sdTarget_spec (size : Record V T → Nat) (d : Nat) (S : Stream V T) :
    sdTarget size d S = 0 ∨
      (sdTarget size d S < S.length ∧ d ≤ S.cost size (sdTarget size d S) S.length) := by
  unfold sdTarget
  rcases foldl_max_eq_or_mem ((List.range S.length).filter
      (fun j => decide (d ≤ S.cost size j S.length))) 0 with h | h
  · left; exact h
  · right
    rw [List.mem_filter, List.mem_range] at h
    exact ⟨h.1, by simpa using h.2⟩

/-! ### The take's loop -/

section Loop

variable (size : Record V T → Nat) (d : Nat) (pace : Nat → Nat → Bool) (S : Stream V T)
  (D : Dirty)

/-- The take never asks for a startup pos before the one it starts from. -/
theorem takeLoop_ge : ∀ (n a taken acc : Nat), acc < a →
    acc ≤ takeLoop size d pace S D (List.range' a n) taken acc
  | 0, _, _, _, _ => by simp [takeLoop]
  | n + 1, a, taken, acc, h => by
    rw [List.range'_succ]
    simp only [takeLoop]
    split
    · exact Nat.le_trans (Nat.le_of_lt h) (takeLoop_ge n (a + 1) _ a (by omega))
    · exact Nat.le_refl _

/-- If every transaction from a to J begins at least d before the end, the
take takes them all: whatever the pace, it asks for J or a later startup pos. -/
theorem takeLoop_reaches : ∀ (n a taken acc J : Nat),
    (∀ j, a ≤ j → j ≤ J → d ≤ S.cost size j S.length) → a ≤ J → J < a + n → acc < a →
    J ≤ takeLoop size d pace S D (List.range' a n) taken acc
  | 0, _, _, _, _, _, haJ, hJn, _ => by omega
  | n + 1, a, taken, acc, J, hP, haJ, hJn, _ => by
    rw [List.range'_succ]
    simp only [takeLoop]
    split
    · by_cases hJ : J = a
      · rw [hJ]
        exact takeLoop_ge size d pace S D n (a + 1) _ a (by omega)
      · exact takeLoop_reaches n (a + 1) _ a J (fun j h1 h2 => hP j (by omega) h2)
          (by omega) (by omega) (by omega)
    · rename_i h
      exact absurd (Or.inl (hP a (Nat.le_refl a) haJ)) h

end Loop

/-- BergDB's take keeps up with its deadline's distance: whatever the pace, it
never asks for a startup pos before the target of the larger of twice the
setting and the span of the section. -/
theorem takePolicy_keepsUp (size : Record V T → Nat) (sd : Time → Nat) (pace : Pace V T)
    (S : Stream V T) (D : Dirty) (i : Time) (tr : T) :
    sdTarget size (max (2 * sd i) (S.span size)) S ≤ takePolicy size sd pace S D i tr := by
  unfold takePolicy sectionIdx
  generalize max (2 * sd i) (S.span size) = d
  rcases sdTarget_spec size d S with h0 | ⟨hlt, hP⟩
  · rw [h0]; exact Nat.zero_le _
  · by_cases hJ : sdTarget size d S ≤ lastSp S
    · exact Nat.le_trans hJ (takeLoop_ge size d _ S D _ _ _ _ (by omega))
    · apply takeLoop_reaches size d _ S D _ _ _ _ _ _ (by omega) (by omega) (by omega)
      intro j _ h2
      exact Nat.le_trans hP (cost_le_of_le size S h2)

/-! ### One transaction -/

/-- T3 for one transaction, for a policy that, in this transaction, keeps up
with a distance dd: after it, the startup section without its last record
costs less than dd, or nothing. -/
theorem section_step_of (sp : Spec V T) (al : Algo V T) (size : Record V T → Nat)
    (db : DB V T) (tr : T) (dd : Nat)
    (hk : sdTarget size dd db.S ≤ al.policy db.S (parts sp al db tr).D1 db.S.length tr) :
    (step sp al db tr).S.span size < dd ∨ (step sp al db tr).S.span size = 0 := by
  unfold Stream.span
  rw [lastSp_step]
  have hlen : (step sp al db tr).S.length - 1 = db.S.length := by
    rw [step_S_snoc, List.length_append, List.length_singleton, Nat.add_sub_cancel]
  rw [hlen, step_S_snoc, cost_append_left size _ _ _ (Nat.le_refl _)]
  have hs := parts_s sp al db tr
  unfold startupPos at hs
  by_cases h1 : (parts sp al db tr).s + 1 < db.S.length
  · left
    apply sdTarget_max size dd db.S _ h1
    omega
  · right
    exact cost_eq_zero size _ (by omega)

/-- T3 for one transaction with BergDB's take: after it, the startup section
without its last record costs less than the larger of twice the setting and
that section before it, or nothing. -/
theorem take_step (sp : Spec V T) (al : Algo V T) (size : Record V T → Nat) (sd : Time → Nat)
    (pace : Pace V T) (hp : al.policy = takePolicy size sd pace) (db : DB V T) (tr : T) :
    (step sp al db tr).S.span size < max (2 * sd db.S.length) (db.S.span size) ∨
      (step sp al db tr).S.span size = 0 :=
  section_step_of sp al size db tr _ (by rw [hp]; exact takePolicy_keepsUp size sd pace _ _ _ _)

/-! ### Runs: steps, each followed by a restart or not -/

section Fold

variable (sp : Spec V T) (al : Algo V T) (size : Record V T → Nat) (sd : Time → Nat)
  (pace : Pace V T) {X : Type} (next : DB V T → X → DB V T) (g : X → T)

/-- Each transaction of a fold adds one record. -/
theorem fold_length (hn : ∀ db x, (next db x).S = (step sp al db (g x)).S) :
    ∀ (xs : List X) (db : DB V T), (xs.foldl next db).S.length = db.S.length + xs.length
  | [], db => by simp
  | x :: xs, db => by
    rw [List.foldl_cons, fold_length hn xs (next db x), hn, step_S_snoc]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

/-- T3 with settings at most M: if the section is shorter than 2 M before, so
it is after every transaction. -/
theorem fold_bound (hn : ∀ db x, (next db x).S = (step sp al db (g x)).S)
    (hp : al.policy = takePolicy size sd pace) {M : Nat} (hM0 : 0 < M) :
    ∀ (xs : List X) (db : DB V T), db.S.span size < 2 * M →
      (∀ i, db.S.length ≤ i → i < db.S.length + xs.length → sd i ≤ M) →
      (xs.foldl next db).S.span size < 2 * M
  | [], _, h, _ => h
  | x :: xs, db, h, hM => by
    rw [List.foldl_cons]
    have hstep := take_step sp al size sd pace hp db (g x)
    rw [← hn] at hstep
    have hlen : (next db x).S.length = db.S.length + 1 := by
      rw [hn, step_S_snoc, List.length_append, List.length_singleton]
    have hsd := hM db.S.length (Nat.le_refl _) (by simp only [List.length_cons]; omega)
    apply fold_bound hn hp hM0 xs (next db x)
    · rcases hstep with h1 | h1
      · rcases Nat.le_total (2 * sd db.S.length) (db.S.span size) with h2 | h2
        · rw [Nat.max_eq_right h2] at h1; omega
        · rw [Nat.max_eq_left h2] at h1; omega
      · omega
    · intro i h1 h2
      rw [hlen] at h1 h2
      exact hM i (by omega) (by simp only [List.length_cons]; omega)

/-- T3 after a change of the setting to sd': after each transaction with the
setting sd', the section is shorter than 2 sd', or it has lost at least one
for each such transaction. -/
theorem fold_decrease (hn : ∀ db x, (next db x).S = (step sp al db (g x)).S)
    (hp : al.policy = takePolicy size sd pace) {sd' : Nat} (hsd' : 0 < sd') :
    ∀ (xs : List X) (db : DB V T),
      (∀ i, db.S.length ≤ i → i < db.S.length + xs.length → sd i = sd') →
      (xs.foldl next db).S.span size < 2 * sd' ∨
        (xs.foldl next db).S.span size + xs.length ≤ db.S.span size
  | [], _, _ => Or.inr (by simp)
  | x :: xs, db, hset => by
    rw [List.foldl_cons]
    have hstep := take_step sp al size sd pace hp db (g x)
    rw [← hn, hset db.S.length (Nat.le_refl _) (by simp only [List.length_cons]; omega)]
      at hstep
    have hlen : (next db x).S.length = db.S.length + 1 := by
      rw [hn, step_S_snoc, List.length_append, List.length_singleton]
    have ih := fold_decrease hn hp hsd' xs (next db x) (fun i h1 h2 => by
      rw [hlen] at h1 h2
      exact hset i (by omega) (by simp only [List.length_cons]; omega))
    simp only [List.length_cons]
    rcases ih with h | h
    · exact Or.inl h
    · rcases hstep with h1 | h1
      · rcases Nat.le_total (2 * sd') (db.S.span size) with h2 | h2
        · rw [Nat.max_eq_right h2] at h1
          by_cases h3 : (xs.foldl next (next db x)).S.span size < 2 * sd'
          · exact Or.inl h3
          · right; omega
        · rw [Nat.max_eq_left h2] at h1; left; omega
      · left; omega

end Fold

/-! ### Runs -/

theorem init_span (sp : Spec V T) (size : Record V T → Nat) : (init sp).S.span size = 0 := by
  obtain ⟨R, hR, _⟩ := init_S sp (T := T)
  unfold Stream.span
  rw [hR]
  exact cost_eq_zero size _ (by simp)

theorem init_length (sp : Spec V T) : (init sp).S.length = 1 := by
  obtain ⟨R, hR, _⟩ := init_S sp (T := T)
  rw [hR]; rfl

theorem step_next (sp : Spec V T) (al : Algo V T) (db : DB V T) (tr : T) :
    (step sp al db tr).S = (step sp al db (id tr)).S := rfl

/-- A step followed by a restart or not, as in `runRestarts`. -/
def restartNext (sp : Spec V T) (al : Algo V T) (db : DB V T) (p : T × Bool) : DB V T :=
  let db := step sp al db p.1
  if p.2 then startup sp db.S else db

theorem restartNext_S (sp : Spec V T) (al : Algo V T) (db : DB V T) (p : T × Bool) :
    (restartNext sp al db p).S = (step sp al db p.1).S := by
  unfold restartNext
  split <;> rfl

theorem runRestarts_eq_fold (sp : Spec V T) (al : Algo V T) (ts : List (T × Bool)) :
    runRestarts sp al ts = ts.foldl (restartNext sp al) (init sp) := rfl

theorem run_length (sp : Spec V T) (al : Algo V T) (ts : List T) :
    (run sp al ts).S.length = ts.length + 1 := by
  have h := fold_length sp al (step sp al) id (step_next sp al) ts (init sp)
  unfold run
  rw [h, init_length]
  omega

theorem runRestarts_length (sp : Spec V T) (al : Algo V T) (ts : List (T × Bool)) :
    (runRestarts sp al ts).S.length = ts.length + 1 := by
  rw [runRestarts_eq_fold, fold_length sp al (restartNext sp al) Prod.fst (restartNext_S sp al),
    init_length]
  omega

end SIS
