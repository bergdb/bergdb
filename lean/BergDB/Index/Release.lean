/-
The user indexes of BergDB 2026.4 in Lean: the manager's lock is released
(bergdb 020-29). `build_ends` takes as a hypothesis that the lock is free, or
the build's, at times without end. Here that follows from the weak fairness of
the threads that hold it: a definition change's maps free it; a build in its
locked phase steps on until it commits (`build_ends` on the run from then,
whose lock is its own); a build of a deleted generation fails its check.
So BuildEnds holds under strong fairness of the build and weak fairness of
the others (`build_ends_wf`).
-/
import BergDB.Index.Liveness

namespace BergDB.Index

variable {V F L W : Type} [DecidableEq W]

/-- The run from time k on. -/
def Run.shift {sp : Spec V F L} (ρ : Run sp W) (k : Nat) : Run sp W where
  sys i := ρ.sys (k + i)
  lbl i := ρ.lbl (k + i)
  start := ρ.reach k
  step i := ρ.step (k + i)

/-- A held lock changes its holder only through free. -/
theorem lock_keep {sp : Spec V F L} {s s' : Sys V F L W} {lb : Lbl W}
    (hst : Step sp s lb s') (h : s.m.lock ≠ .free) (h' : s'.m.lock ≠ .free) :
    s'.m.lock = s.m.lock := by
  cases hst with
  | aCreate _ _ _ hl _ => exact absurd hl h
  | aDelete _ _ _ hl _ => exact absurd hl h
  | aCreateMap _ _ _ _ => exact absurd rfl h'
  | aDeleteMap _ _ _ => exact absurd rfl h'
  | bCheckFail _ _ _ _ _ _ _ => exact absurd rfl h'
  | bLock _ _ _ _ _ hl => exact absurd hl h
  | bActivate _ _ _ _ _ _ hl _ _ => exact absurd hl h
  | bActivateFail _ _ _ _ _ hl _ => exact absurd hl h
  | bCommit _ _ b _ _ _ _ =>
    change (if b.locked = true then Lock.free else s.m.lock) ≠ .free at h'
    show (if b.locked = true then Lock.free else s.m.lock) = s.m.lock
    by_cases hb : b.locked = true
    · rw [ite_eq_left hb] at h'; exact absurd rfl h'
    · rw [ite_eq_right hb]
  | bRetry _ _ b _ _ =>
    change (if b.locked = true then Lock.free else s.m.lock) ≠ .free at h'
    show (if b.locked = true then Lock.free else s.m.lock) = s.m.lock
    by_cases hb : b.locked = true
    · rw [ite_eq_left hb] at h'; exact absurd rfl h'
    · rw [ite_eq_right hb]
  | bAbort _ _ b _ =>
    change (if b.locked = true then Lock.free else s.m.lock) ≠ .free at h'
    show (if b.locked = true then Lock.free else s.m.lock) = s.m.lock
    by_cases hb : b.locked = true
    · rw [ite_eq_left hb] at h'; exact absurd rfl h'
    · rw [ite_eq_right hb]
  | crash => exact absurd rfl h'
  | _ => rfl

/-- A definition change's maps free the lock. -/
theorem amap_frees {sp : Spec V F L} {s s' : Sys V F L W} (hst : Step sp s .amap s') :
    s'.m.lock = .free := by
  cases hst with
  | aCreateMap _ _ _ _ => rfl
  | aDeleteMap _ _ _ => rfl

/-- While a definition change holds the lock, its maps can step. -/
theorem amap_enabled {sp : Spec V F L} {s : Sys V F L W} (hi : Inv sp s)
    (hl : s.m.lock = .mgr) : Enabled sp s .amap := by
  have ha := hi.minv.lockMgr.mp hl
  cases hadm : s.m.admin with
  | idle => exact absurd hadm ha
  | create n g fn => exact ⟨_, Step.aCreateMap s n g fn hadm⟩
  | delete n g => exact ⟨_, Step.aDeleteMap s n g hadm⟩

/-- A retry, or an end, of the build that holds the lock frees it. -/
theorem retry_frees {sp : Spec V F L} {s s' : Sys V F L W} {n : Name} {g : Gen}
    (hi : Inv sp s) (hl : s.m.lock = .bld n g)
    (hst : Step sp s (.bretry n g) s' ∨ Step sp s (.babort n g) s') : s'.m.lock = .free := by
  obtain ⟨b0, hb0, hlk⟩ := hi.minv.lockBld n g hl
  rcases hst with hst | hst
  · cases hst with
    | bRetry _ _ b hb _ =>
      rw [hb0] at hb; cases hb
      exact ite_eq_left hlk
  · cases hst with
    | bAbort _ _ b hb =>
      rw [hb0] at hb; cases hb
      exact ite_eq_left hlk

/-- While a build holds the lock, the definitions stay: a definition change and
an activation need the lock free, and no crash. -/
theorem dfn_locked {sp : Spec V F L} {s s' : Sys V F L W} {lb : Lbl W} (hst : Step sp s lb s')
    {n : Name} {g : Gen} (hl : s.m.lock = .bld n g) (hcr : lb ≠ .crash) :
    s'.st.dfn = s.st.dfn := by
  cases hst with
  | aCreate _ _ _ hf _ => rw [hl] at hf; cases hf
  | aDelete _ _ _ hf _ => rw [hl] at hf; cases hf
  | bActivate _ _ _ _ _ _ hf _ _ => rw [hl] at hf; cases hf
  | crash => exact absurd rfl hcr
  | _ => rfl

/-- While a build holds the lock, a step of another thread, no crash and no
retry or end of the build, keeps the build. -/
theorem locked_other {sp : Spec V F L} {s s' : Sys V F L W} {lb : Lbl W}
    (hst : Step sp s lb s') {n : Name} {g : Gen} (hadm : s.m.admin = .idle)
    (hl : lb ≠ .bld n g) (hre : lb ≠ .bretry n g) (hab : lb ≠ .babort n g)
    (hcr : lb ≠ .crash) : s'.m.bld n g = s.m.bld n g := by
  cases hst with
  | aCreateMap n' g' fn ha' => rw [hadm] at ha'; cases ha'
  | bReadE n' g' b e _ _ _ =>
    show upd2 s.m.bld n' g' _ n g = _; rw [upd2_ne _ _ (lbl_bld_ne hl)]
  | bRead n' g' b e hi' _ _ _ _ _ =>
    show upd2 s.m.bld n' g' _ n g = _; rw [upd2_ne _ _ (lbl_bld_ne hl)]
  | bCheck n' g' b d' _ _ _ _ _ =>
    show upd2 s.m.bld n' g' _ n g = _; rw [upd2_ne _ _ (lbl_bld_ne hl)]
  | bCheckFail n' g' b _ _ _ _ =>
    show upd2 s.m.bld n' g' _ n g = _; rw [upd2_ne _ _ (lbl_bld_ne hl)]
  | bCommit n' g' b _ _ _ _ =>
    show upd2 s.m.bld n' g' _ n g = _; rw [upd2_ne _ _ (lbl_bld_ne hl)]
  | bRefused n' g' b _ _ _ =>
    show upd2 s.m.bld n' g' _ n g = _; rw [upd2_ne _ _ (lbl_bld_ne hl)]
  | bLock n' g' b _ _ _ =>
    show upd2 s.m.bld n' g' _ n g = _; rw [upd2_ne _ _ (lbl_bld_ne hl)]
  | bActivate n' g' b d' _ _ _ _ _ =>
    show upd2 s.m.bld n' g' _ n g = _; rw [upd2_ne _ _ (lbl_bld_ne hl)]
  | bActivateFail n' g' b _ _ _ _ =>
    show upd2 s.m.bld n' g' _ n g = _; rw [upd2_ne _ _ (lbl_bld_ne hl)]
  | bRetry n' g' b _ _ =>
    show upd2 s.m.bld n' g' _ n g = _
    have : ¬ (n = n' ∧ g = g') := fun hh => hre (by rw [hh.1, hh.2])
    rw [upd2_ne _ _ this]
  | bAbort n' g' b _ =>
    show upd2 s.m.bld n' g' _ n g = _
    have : ¬ (n = n' ∧ g = g') := fun hh => hab (by rw [hh.1, hh.2])
    rw [upd2_ne _ _ this]
  | crash => exact absurd rfl hcr
  | _ => rfl

/-- The build of the generation g of the name n is of a deleted generation:
n's definition, if any, has another generation. -/
def Dead (s : Sys V F L W) (n : Name) (g : Gen) : Prop :=
  ∀ d, s.st.dfn n = some d → d.gen ≠ g

/-- The phase of a build of a deleted generation, for its measure: it fails
its next check. -/
def dPh : BPc → Nat
  | .readE => 3
  | .commit => 2
  | .read => 1
  | _ => 0

/-- A dead build's measure. -/
def dMeasure (s : Sys V F L W) (n : Name) (g : Gen) : Nat :=
  match s.m.bld n g with
  | some b => dPh b.pc
  | none => 0

omit [DecidableEq W] in
theorem dMeasure_of {s : Sys V F L W} {n : Name} {g : Gen} {b : BSt V F}
    (h : s.m.bld n g = some b) : dMeasure s n g = dPh b.pc := by
  unfold dMeasure; rw [h]

/-- A step of a dead build that keeps the lock lowers its phase. -/
theorem dead_own {sp : Spec V F L} {s s' : Sys V F L W} (hi : Inv sp s) {n : Name} {g : Gen}
    (hst : Step sp s (.bld n g) s') (hl : s.m.lock = .bld n g) (hl' : s'.m.lock = .bld n g)
    (hD : Dead s n g) (hadm : s.m.admin = .idle) {b : BSt V F} (hb : s.m.bld n g = some b)
    (hlk : b.locked = true) :
    ∃ b', s'.m.bld n g = some b' ∧ dPh b'.pc < dPh b.pc := by
  have hmem : s.m.mem n = s.st.dfn n :=
    (hi.minv.memAgrees n).resolve_right (by rw [hadm]; intro h; cases h)
  cases hst with
  | bReadE _ _ b0 e hb0 hpc _ =>
    rw [hb] at hb0; cases hb0
    refine ⟨_, upd2_same _ _ _ _, ?_⟩
    show dPh BPc.read < dPh b.pc
    rw [hpc]; decide
  | bRead _ _ b0 e hi0 hb0 hpc _ _ _ =>
    rw [hb] at hb0; cases hb0
    refine ⟨_, upd2_same _ _ _ _, ?_⟩
    show dPh BPc.check < dPh b.pc
    rw [hpc]; decide
  | bCheck _ _ b0 d hb0 _ _ hm hdg =>
    rw [hmem] at hm; exact absurd hdg (hD d hm)
  | bCheckFail _ _ _ _ _ _ _ =>
    change Lock.free = Lock.bld n g at hl'; cases hl'
  | bCommit _ _ b0 hb0 _ _ _ =>
    rw [hb] at hb0; cases hb0
    change (if b.locked = true then Lock.free else s.m.lock) = .bld n g at hl'
    rw [ite_eq_left hlk] at hl'; cases hl'
  | bRefused _ _ b0 hb0 hpc _ =>
    rw [hb] at hb0; cases hb0
    refine ⟨_, upd2_same _ _ _ _, ?_⟩
    show dPh (if b.locked = false ∧ sp.lockedAfter ≤ b.tries + 1 then BPc.lock else BPc.read) <
      dPh b.pc
    have hc : ¬ (b.locked = false ∧ sp.lockedAfter ≤ b.tries + 1) := fun h => by
      rw [hlk] at h; cases h.1
    rw [ite_eq_right hc, hpc]; decide
  | bLock _ _ _ _ _ hf => rw [hl] at hf; cases hf
  | bActivate _ _ _ _ _ _ hf _ _ => rw [hl] at hf; cases hf
  | bActivateFail _ _ _ _ _ hf _ => rw [hl] at hf; cases hf

/-- A dead build that holds the lock can step: it fails its check. -/
theorem dead_enabled {sp : Spec V F L} {s : Sys V F L W} (hi : Inv sp s) {n : Name} {g : Gen}
    (hl : s.m.lock = .bld n g) (hD : Dead s n g) (hadm : s.m.admin = .idle)
    (hfin : ∃ e, ∀ k, e < k → s.st.data k = none) : Enabled sp s (.bld n g) := by
  obtain ⟨b, hb, hlk⟩ := hi.minv.lockBld n g hl
  have hbi := hi.minv.bInv n g b hb
  have hmem : s.m.mem n = s.st.dfn n :=
    (hi.minv.memAgrees n).resolve_right (by rw [hadm]; intro h; cases h)
  cases hpc : b.pc with
  | readE =>
    obtain ⟨e, he⟩ := hfin
    exact ⟨_, Step.bReadE s n g b e hb hpc (fun k hk => by rw [he k hk]; exact sp.f_none _ _)⟩
  | read =>
    obtain ⟨e, hE, hne⟩ := hbi.readNext (Or.inl hpc)
    exact ⟨_, Step.bRead s n g b e (e + 1) hb hpc hE (by omega) (Nat.le_refl _)⟩
  | check =>
    exact ⟨_, Step.bCheckFail s n g b hb hpc (Or.inr hl) (fun d hd => by rw [hmem] at hd; exact hD d hd)⟩
  | commit =>
    by_cases hA : s.st.wdef n ≤ b.R
    · by_cases hB2 : ∀ k, b.next ≤ k → k < b.hi → sp.f b.fn k (b.snap k) ≠ none →
          s.st.wk k ≤ b.R
      · exact ⟨_, Step.bCommit s n g b hb hpc hA hB2⟩
      · refine ⟨_, Step.bRefused s n g b hb hpc (Or.inr ?_)⟩
        apply Classical.byContradiction
        intro hno
        apply hB2
        intro k h1 h2 h3
        apply Classical.byContradiction
        intro h4
        exact hno ⟨k, h1, h2, h3, Nat.lt_of_not_le h4⟩
    · exact ⟨_, Step.bRefused s n g b hb hpc (Or.inl (Nat.lt_of_not_le hA))⟩
  | lock => rw [hbi.unlocked (Or.inl hpc)] at hlk; cases hlk
  | activate => rw [hbi.unlocked (Or.inr hpc)] at hlk; cases hlk

/-- **The lock is released**: in a run with finitely many crashes, weak
fairness of the definition changes' maps and of every build, finitely many
keys with a value at each time and finitely many writers, the manager's lock is
free at times without end. A definition change that holds it frees it at its
maps; a build that holds it, of a definition that is building, commits its
step (`build_ends` on the run from then, whose lock is the build's own); a
build of a deleted generation fails its check. -/
theorem lock_released {sp : Spec V F L} (ρ : Run sp W)
    (hcr : ∃ N, ∀ j, N ≤ j → ρ.lbl j ≠ .crash)
    (hwm : WeakFair ρ .amap) (hwb : ∀ n g, WeakFair ρ (.bld n g))
    (hfin : ∀ j, ∃ e, ∀ k, e < k → (ρ.sys j).st.data k = none)
    (hW : ∃ ws : List W, ∀ w, w ∈ ws) (j : Nat) :
    ∃ j', j ≤ j' ∧ (ρ.sys j').m.lock = .free := by
  apply Classical.byContradiction
  intro hno
  have hnf : ∀ j', j ≤ j' → (ρ.sys j').m.lock ≠ .free := fun j' hj' h => hno ⟨j', hj', h⟩
  obtain ⟨N, hN⟩ := hcr
  obtain ⟨j1, hj1a, hj1b⟩ : ∃ j1, j ≤ j1 ∧ N ≤ j1 :=
    ⟨max j N, Nat.le_max_left _ _, Nat.le_max_right _ _⟩
  -- the holder at j1 holds the lock from then on
  have hkeep : ∀ d, (ρ.sys (j1 + d)).m.lock = (ρ.sys j1).m.lock := by
    intro d
    induction d with
    | zero => rfl
    | succ d ih =>
      rw [← ih]
      exact lock_keep (ρ.step (j1 + d)) (hnf _ (by omega)) (hnf _ (by omega))
  have hkeep' : ∀ j', j1 ≤ j' → (ρ.sys j').m.lock = (ρ.sys j1).m.lock := by
    intro j' hj'; have := hkeep (j' - j1); rwa [show j1 + (j' - j1) = j' by omega] at this
  cases hX : (ρ.sys j1).m.lock with
  | free => exact hnf j1 hj1a hX
  | mgr =>
    obtain ⟨j2, hj2, hl⟩ := hwm j1 (fun j' hj' =>
      amap_enabled (ρ.inv j') (by rw [hkeep' j' hj', hX]))
    have hst := ρ.step j2
    rw [hl] at hst
    exact hnf (j2 + 1) (by omega) (amap_frees hst)
  | bld n g =>
    have hL : ∀ j', j1 ≤ j' → (ρ.sys j').m.lock = .bld n g := fun j' hj' => by
      rw [hkeep' j' hj', hX]
    have hre : ∀ j', j1 ≤ j' → ρ.lbl j' ≠ .bretry n g ∧ ρ.lbl j' ≠ .babort n g := by
      intro j' hj'
      constructor
      · intro h
        have hst := ρ.step j'
        rw [h] at hst
        exact hnf (j' + 1) (by omega) (retry_frees (ρ.inv j') (hL j' hj') (Or.inl hst))
      · intro h
        have hst := ρ.step j'
        rw [h] at hst
        exact hnf (j' + 1) (by omega) (retry_frees (ρ.inv j') (hL j' hj') (Or.inr hst))
    have hadm : ∀ j', j1 ≤ j' → (ρ.sys j').m.admin = .idle := by
      intro j' hj'
      apply Classical.byContradiction
      intro h
      have := (ρ.inv j').minv.lockMgr.mpr h
      rw [hL j' hj'] at this; cases this
    have hdfn : ∀ d, (ρ.sys (j1 + d)).st.dfn = (ρ.sys j1).st.dfn := by
      intro d
      induction d with
      | zero => rfl
      | succ d ih =>
        rw [← ih]
        exact dfn_locked (ρ.step (j1 + d)) (hL _ (by omega)) (hN _ (by omega))
    have hdfn' : ∀ j', j1 ≤ j' → (ρ.sys j').st.dfn = (ρ.sys j1).st.dfn := by
      intro j' hj'; have := hdfn (j' - j1); rwa [show j1 + (j' - j1) = j' by omega] at this
    have hbx : ∀ j', j1 ≤ j' → ∃ b, (ρ.sys j').m.bld n g = some b ∧ b.locked = true :=
      fun j' hj' => (ρ.inv j').minv.lockBld n g (hL j' hj')
    by_cases hB : Building (ρ.sys j1) n g
    · -- a build of a definition that is building: BuildEnds on the run from j1
      have hBj : ∀ j', j1 ≤ j' → Building (ρ.sys j') n g := by
        intro j' hj'
        obtain ⟨d, hd, h2, h3⟩ := hB
        exact ⟨d, by rw [hdfn' j' hj']; exact hd, h2, h3⟩
      have hen : ∀ j', j1 ≤ j' → Enabled sp (ρ.sys j') (.bld n g) := by
        intro j' hj'
        obtain ⟨b, hb, _⟩ := hbx j' hj'
        exact build_enabled (ρ.inv j') (hBj j' hj') (by rw [hadm j' hj']; intro h; cases h) hb
          (Or.inr (hL j' hj')) (hfin j')
      have hb0 : (ρ.sys (j1 + 0)).m.bld n g ≠ none := by
        obtain ⟨b, hb, _⟩ := hbx j1 (Nat.le_refl _)
        show (ρ.sys j1).m.bld n g ≠ none
        rw [hb]; intro h; cases h
      have ha0 : (ρ.sys (j1 + 0)).m.admin.name ≠ some n := by
        show (ρ.sys j1).m.admin.name ≠ some n
        rw [hadm j1 (Nat.le_refl _)]; intro h; cases h
      obtain ⟨jx, _, hnB⟩ := build_ends (ρ.shift j1) (n := n) (g := g)
        ⟨0, fun i _ => ⟨hN (j1 + i) (by omega), (hre (j1 + i) (by omega)).1⟩⟩
        (fun i => (hre (j1 + i) (by omega)).2)
        (fun i _ => by
          obtain ⟨j', hj', hl⟩ := hwb n g (j1 + i) (fun j' hj' => hen j' (by omega))
          refine ⟨j' - j1, by omega, ?_⟩
          show ρ.lbl (j1 + (j' - j1)) = _
          rw [show j1 + (j' - j1) = j' by omega]; exact hl)
        (fun i => ⟨i, Nat.le_refl _, Or.inr (hL (j1 + i) (by omega))⟩)
        (fun i => hfin (j1 + i)) hW (i := 0) hb0 ha0
      exact hnB (hBj (j1 + jx) (by omega))
    · -- a build of a deleted generation: it fails its check
      have hD : ∀ j', j1 ≤ j' → Dead (ρ.sys j') n g := by
        intro j' hj' d hd hdg
        rw [hdfn' j' hj'] at hd
        obtain ⟨b, hb, _⟩ := hbx j1 (Nat.le_refl _)
        have hda := (((ρ.inv j1).minv.bInv n g b hb).fnEq d hd hdg).2
        exact hB ⟨d, hd, hdg, hda⟩
      have hle : ∀ j', j1 ≤ j' → dMeasure (ρ.sys (j' + 1)) n g ≤ dMeasure (ρ.sys j') n g ∧
          (ρ.lbl j' = .bld n g → dMeasure (ρ.sys (j' + 1)) n g < dMeasure (ρ.sys j') n g) := by
        intro j' hj'
        obtain ⟨b, hb, hlk⟩ := hbx j' hj'
        by_cases hlb : ρ.lbl j' = .bld n g
        · have hst := ρ.step j'
          rw [hlb] at hst
          obtain ⟨b', hb', hlt⟩ := dead_own (ρ.inv j') hst (hL j' hj') (hL (j' + 1) (by omega))
            (hD j' hj') (hadm j' hj') hb hlk
          rw [dMeasure_of hb, dMeasure_of hb']
          exact ⟨Nat.le_of_lt hlt, fun _ => hlt⟩
        · have heq := locked_other (ρ.step j') (hadm j' hj') hlb (hre j' hj').1 (hre j' hj').2
            (hN j' (by omega))
          refine ⟨Nat.le_of_eq ?_, fun h => absurd h hlb⟩
          unfold dMeasure; rw [heq]
      exact descent (μ := fun j' => dMeasure (ρ.sys j') n g) (P := fun j' => ρ.lbl j' = .bld n g)
        (i := j1) (fun j' hj' => (hle j' hj').1) (fun j' hj' hp => (hle j' hj').2 hp)
        (fun j' hj' => hwb n g j' (fun j'' hj'' =>
          dead_enabled (ρ.inv j'') (hL j'' (by omega)) (hD j'' (by omega)) (hadm j'' (by omega))
            (hfin j'')))

/-- **BuildEnds** under fairness of the threads alone: `build_ends` with its
hypothesis on the lock from `lock_released`. Hypotheses: finitely many
crashes, and of the build's retries; no end of the build's thread without its
activation; strong fairness of the build; weak fairness of the definition
changes' maps and of every build; finitely many keys with a value at each
time, and finitely many writers. -/
theorem build_ends_wf {sp : Spec V F L} (ρ : Run sp W) {n : Name} {g : Gen}
    (hcr : ∃ N, ∀ j, N ≤ j → ρ.lbl j ≠ .crash ∧ ρ.lbl j ≠ .bretry n g)
    (hab : ∀ j, ρ.lbl j ≠ .babort n g)
    (hsf : StrongFair ρ (.bld n g))
    (hwm : WeakFair ρ .amap) (hwb : ∀ n g, WeakFair ρ (.bld n g))
    (hfin : ∀ j, ∃ e, ∀ k, e < k → (ρ.sys j).st.data k = none)
    (hW : ∃ ws : List W, ∀ w, w ∈ ws)
    {i : Nat} (hb : (ρ.sys i).m.bld n g ≠ none) (ha : (ρ.sys i).m.admin.name ≠ some n) :
    ∃ j, i ≤ j ∧ ¬ Building (ρ.sys j) n g := by
  have hcr' : ∃ N, ∀ j, N ≤ j → ρ.lbl j ≠ .crash :=
    let ⟨N, hN⟩ := hcr; ⟨N, fun j hj => (hN j hj).1⟩
  exact build_ends ρ hcr hab hsf
    (fun j => let ⟨j', hj', hl⟩ := lock_released ρ hcr' hwm hwb hfin hW j; ⟨j', hj', Or.inl hl⟩)
    hfin hW hb ha

end BergDB.Index
