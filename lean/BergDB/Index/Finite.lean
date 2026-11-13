/-
The user indexes of BergDB 2026.4 in Lean: with finitely many definition
changes, weak fairness gives BuildEnds (bergdb 020-29). The starving run of
Starve.lean takes definition changes without end. Without them, from some
time on no definition change holds the lock, and every build takes it
finitely often: each of its locked phases ends with a commit that moves it on,
up to its end key (`phi`). So from some time on the lock is free (no one takes
it, and `lock_released` frees it once more), and weak fairness of the build
gives it its steps.
-/
import BergDB.Index.Release

namespace BergDB.Index

variable {V F L W : Type} [DecidableEq W]

/-- No step but a definition change's start makes one under way. -/
theorem admin_idle_keep {sp : Spec V F L} {s s' : Sys V F L W} {lb : Lbl W}
    (hst : Step sp s lb s') (hac : lb ≠ .achange) (ha : s.m.admin = .idle) :
    s'.m.admin = .idle := by
  cases hst with
  | aCreate => exact absurd rfl hac
  | aDelete => exact absurd rfl hac
  | aCreateMap => rfl
  | aDeleteMap => rfl
  | crash => rfl
  | _ => exact ha

/-- A definition change's maps end it. -/
theorem amap_idle {sp : Spec V F L} {s s' : Sys V F L W} (hst : Step sp s .amap s') :
    s'.m.admin = .idle := by
  cases hst with
  | aCreateMap _ _ _ _ => rfl
  | aDeleteMap _ _ _ => rfl

/-- A step that gives a build the lock is the build's `bLock`, from its phase
`lock`. -/
theorem takes_lock {sp : Spec V F L} {s s' : Sys V F L W} {lb : Lbl W}
    (hst : Step sp s lb s') {n : Name} {g : Gen} (h : s.m.lock ≠ .bld n g)
    (h' : s'.m.lock = .bld n g) : lb = .bld n g ∧ ∃ b, s.m.bld n g = some b ∧ b.pc = .lock := by
  cases hst with
  | aCreate => change Lock.mgr = .bld n g at h'; cases h'
  | aDelete => change Lock.mgr = .bld n g at h'; cases h'
  | aCreateMap => change Lock.free = .bld n g at h'; cases h'
  | aDeleteMap => change Lock.free = .bld n g at h'; cases h'
  | bCheckFail => change Lock.free = .bld n g at h'; cases h'
  | bLock n' g' b hb hpc _ =>
    change Lock.bld n' g' = .bld n g at h'
    injection h' with h1 h2
    subst h1; subst h2
    exact ⟨rfl, b, hb, hpc⟩
  | bCommit _ _ b _ _ _ _ =>
    change (if b.locked = true then Lock.free else s.m.lock) = .bld n g at h'
    by_cases hb : b.locked = true
    · rw [ite_eq_left hb] at h'; cases h'
    · rw [ite_eq_right hb] at h'; exact absurd h' h
  | bRetry _ _ b _ _ =>
    change (if b.locked = true then Lock.free else s.m.lock) = .bld n g at h'
    by_cases hb : b.locked = true
    · rw [ite_eq_left hb] at h'; cases h'
    · rw [ite_eq_right hb] at h'; exact absurd h' h
  | bAbort _ _ b _ =>
    change (if b.locked = true then Lock.free else s.m.lock) = .bld n g at h'
    by_cases hb : b.locked = true
    · rw [ite_eq_left hb] at h'; cases h'
    · rw [ite_eq_right hb] at h'; exact absurd h' h
  | crash => change Lock.free = .bld n g at h'; cases h'
  | _ => exact absurd h' h

/-- A build's progress through its locked phases: twice the keys left up to
its end key, and one while it holds no lock. -/
def phiB (b : BSt V F) : Nat :=
  2 * (b.E.getD 0 + 1 - b.next) + (if b.locked = true then 0 else 1)

/-- The progress of the build of the generation g of the name n, if any. -/
def phi (s : Sys V F L W) (n : Name) (g : Gen) : Nat :=
  match s.m.bld n g with
  | some b => phiB b
  | none => 0

omit [DecidableEq W] in
theorem phi_of {s : Sys V F L W} {n : Name} {g : Gen} {b : BSt V F}
    (h : s.m.bld n g = some b) : phi s n g = phiB b := by
  unfold phi; rw [h]

/-- A build's own step, out of `readE`: it ends (not from `lock`), or its
progress does not grow, and falls when it takes the lock. -/
theorem own_phi {sp : Spec V F L} {s s' : Sys V F L W} (hi : Inv sp s) {n : Name} {g : Gen}
    (hst : Step sp s (.bld n g) s') (hR : ∀ b, s.m.bld n g = some b → b.pc ≠ .readE) :
    ∃ b, s.m.bld n g = some b ∧ ((s'.m.bld n g = none ∧ b.pc ≠ .lock) ∨
      ∃ b', s'.m.bld n g = some b' ∧ b'.pc ≠ .readE ∧ phiB b' ≤ phiB b ∧
        (b.pc = .lock → phiB b' < phiB b)) := by
  cases hst with
  | bReadE _ _ b e hb hpc _ => exact absurd hpc (hR b hb)
  | bRead _ _ b e hi0 hb hpc _ _ _ =>
    refine ⟨b, hb, Or.inr ⟨_, upd2_same _ _ _ _, (fun h => by cases h), Nat.le_refl _,
      fun h => ?_⟩⟩
    rw [hpc] at h; cases h
  | bCheck _ _ b d hb hpc _ _ _ =>
    refine ⟨b, hb, Or.inr ⟨_, upd2_same _ _ _ _, (fun h => by cases h), Nat.le_refl _,
      fun h => ?_⟩⟩
    rw [hpc] at h; cases h
  | bCheckFail _ _ b hb hpc _ _ =>
    exact ⟨b, hb, Or.inl ⟨upd2_same _ _ _ _, by rw [hpc]; intro h; cases h⟩⟩
  | bCommit _ _ b hb hpc _ _ =>
    obtain ⟨e, hE, hnh, hhi, _⟩ := ((hi.minv.bInv n g b hb).inStep (Or.inr hpc)).range
    have hlt : phiB (bAfter b) < phiB b := by
      show 2 * (b.E.getD 0 + 1 - b.hi) + 1 <
        2 * (b.E.getD 0 + 1 - b.next) + (if b.locked = true then 0 else 1)
      rw [hE]
      show 2 * (e + 1 - b.hi) + 1 < 2 * (e + 1 - b.next) + (if b.locked = true then 0 else 1)
      omega
    refine ⟨b, hb, Or.inr ⟨_, upd2_same _ _ _ _, ?_, Nat.le_of_lt hlt, fun _ => hlt⟩⟩
    show (if b.ended = true then BPc.activate else BPc.read) ≠ .readE
    split <;> intro h <;> cases h
  | bRefused _ _ b hb hpc _ =>
    refine ⟨b, hb, Or.inr ⟨_, upd2_same _ _ _ _, ?_, Nat.le_refl _, fun h => ?_⟩⟩
    · show (if b.locked = false ∧ sp.lockedAfter ≤ b.tries + 1 then BPc.lock else BPc.read) ≠
        .readE
      split <;> intro h <;> cases h
    · rw [hpc] at h; cases h
  | bLock _ _ b hb hpc _ =>
    have hlk := (hi.minv.bInv n g b hb).unlocked (Or.inl hpc)
    have hlt : phiB { b with locked := true, pc := .read } < phiB b := by
      show 2 * (b.E.getD 0 + 1 - b.next) + 0 <
        2 * (b.E.getD 0 + 1 - b.next) + (if b.locked = true then 0 else 1)
      rw [hlk]
      show 2 * (b.E.getD 0 + 1 - b.next) + 0 < 2 * (b.E.getD 0 + 1 - b.next) + 1
      omega
    exact ⟨b, hb, Or.inr ⟨_, upd2_same _ _ _ _, (fun h => by cases h), Nat.le_of_lt hlt,
      fun _ => hlt⟩⟩
  | bActivate _ _ b d hb hpc _ _ _ =>
    exact ⟨b, hb, Or.inl ⟨upd2_same _ _ _ _, by rw [hpc]; intro h; cases h⟩⟩
  | bActivateFail _ _ b hb hpc _ _ =>
    exact ⟨b, hb, Or.inl ⟨upd2_same _ _ _ _, by rw [hpc]; intro h; cases h⟩⟩

/-- With no definition change under way, no crash and no retry of the build,
a build out of `readE` stays out of it, its progress does not grow, and falls
when it takes the lock. -/
theorem phi_step {sp : Spec V F L} {s s' : Sys V F L W} {lb : Lbl W} (hi : Inv sp s)
    (hst : Step sp s lb s') {n : Name} {g : Gen} (hcr : lb ≠ .crash)
    (hre : lb ≠ .bretry n g) (hadm : s.m.admin = .idle)
    (hR : ∀ b, s.m.bld n g = some b → b.pc ≠ .readE) :
    (∀ b', s'.m.bld n g = some b' → b'.pc ≠ .readE) ∧ phi s' n g ≤ phi s n g ∧
      (s.m.lock ≠ .bld n g → s'.m.lock = .bld n g → phi s' n g < phi s n g) := by
  by_cases hl : lb = .bld n g
  · subst hl
    obtain ⟨b, hb, h⟩ := own_phi hi hst hR
    rcases h with ⟨h0, hpcl⟩ | ⟨b', hb', hpc', hle, hlt⟩
    · refine ⟨(fun b' h => by rw [h0] at h; cases h), ?_, fun h1 h2 => ?_⟩
      · unfold phi; rw [h0]; exact Nat.zero_le _
      · obtain ⟨_, b0, hb0, hpc0⟩ := takes_lock hst h1 h2
        rw [hb] at hb0; cases hb0; exact absurd hpc0 hpcl
    · refine ⟨(fun b'' h => by rw [hb'] at h; cases h; exact hpc'), ?_, fun h1 h2 => ?_⟩
      · rw [phi_of hb', phi_of hb]; exact hle
      · obtain ⟨_, b0, hb0, hpc0⟩ := takes_lock hst h1 h2
        rw [hb] at hb0; cases hb0
        rw [phi_of hb', phi_of hb]; exact hlt hpc0
  · by_cases hab : lb = .babort n g
    · subst hab
      have h0 : s'.m.bld n g = none := by
        cases hst with
        | bAbort _ _ b _ => exact upd2_same _ _ _ _
      refine ⟨(fun b' h => by rw [h0] at h; cases h), ?_, fun h1 h2 => ?_⟩
      · unfold phi; rw [h0]; exact Nat.zero_le _
      · exact absurd (takes_lock hst h1 h2).1 (by intro h; cases h)
    · have heq := locked_other hst hadm hl hre hab hcr
      refine ⟨fun b' h => hR b' (by rw [← heq]; exact h), Nat.le_of_eq ?_,
        fun h1 h2 => absurd (takes_lock hst h1 h2).1 hl⟩
      unfold phi; rw [heq]

/-- A measure that never grows from some time on stops falling. -/
theorem eventually_const {μ : Nat → Nat} {i : Nat} (hle : ∀ j, i ≤ j → μ (j + 1) ≤ μ j) :
    ∃ T, i ≤ T ∧ ∀ j, T ≤ j → ¬ μ (j + 1) < μ j := by
  apply Classical.byContradiction
  intro hno
  exact descent (μ := μ) (P := fun j => μ (j + 1) < μ j) (i := i) hle (fun _ _ hp => hp)
    (fun j hj => Classical.byContradiction fun h =>
      hno ⟨j, hj, fun j' hj' hlt => h ⟨j', hj', hlt⟩⟩)

/-- With no crash, definition change or retry, and none under way, from some
time on, a build takes the lock finitely often. -/
theorem build_lock_finite {sp : Spec V F L} (ρ : Run sp W) {N : Nat}
    (hN : ∀ j, N ≤ j →
      ρ.lbl j ≠ .crash ∧ ρ.lbl j ≠ .achange ∧ ∀ n' g', ρ.lbl j ≠ .bretry n' g')
    (hadm : ∀ j, N ≤ j → (ρ.sys j).m.admin = .idle) (n : Name) (g : Gen) :
    ∃ T, ∀ j, T ≤ j →
      ¬ ((ρ.sys j).m.lock ≠ .bld n g ∧ (ρ.sys (j + 1)).m.lock = .bld n g) := by
  by_cases hR : ∃ M, N ≤ M ∧ ∀ b, (ρ.sys M).m.bld n g = some b → b.pc ≠ .readE
  · obtain ⟨M, hM, hRM⟩ := hR
    have hRall : ∀ d, ∀ b, (ρ.sys (M + d)).m.bld n g = some b → b.pc ≠ .readE := by
      intro d
      induction d with
      | zero => exact hRM
      | succ d ih =>
        exact (phi_step (ρ.inv (M + d)) (ρ.step (M + d)) (hN _ (by omega)).1
          ((hN _ (by omega)).2.2 n g) (hadm _ (by omega)) ih).1
    have hR' : ∀ j, M ≤ j → ∀ b, (ρ.sys j).m.bld n g = some b → b.pc ≠ .readE := by
      intro j hj; have := hRall (j - M); rwa [show M + (j - M) = j by omega] at this
    obtain ⟨T, hT, hc⟩ := eventually_const (μ := fun j => phi (ρ.sys j) n g) (i := M)
      (fun j hj => (phi_step (ρ.inv j) (ρ.step j) (hN j (by omega)).1
        ((hN j (by omega)).2.2 n g) (hadm j (by omega)) (hR' j hj)).2.1)
    exact ⟨T, fun j hj ⟨h1, h2⟩ => hc j hj ((phi_step (ρ.inv j) (ρ.step j)
      (hN j (by omega)).1 ((hN j (by omega)).2.2 n g) (hadm j (by omega))
      (hR' j (by omega))).2.2 h1 h2)⟩
  · refine ⟨N, fun j hj ⟨h1, h2⟩ => hR ⟨j, hj, fun b hb hpc => ?_⟩⟩
    obtain ⟨_, b0, hb0, hpc0⟩ := takes_lock (ρ.step j) h1 h2
    rw [hb] at hb0; cases hb0; rw [hpc] at hpc0; cases hpc0

/-- For each of finitely many things from some time on, so for all. -/
theorem list_eventually {α : Type} (Q : α → Nat → Prop) :
    ∀ l : List α, (∀ x ∈ l, ∃ T, ∀ j, T ≤ j → Q x j) → ∃ T, ∀ x ∈ l, ∀ j, T ≤ j → Q x j
  | [], _ => ⟨0, fun _ hx => nomatch hx⟩
  | a :: l, h => by
    obtain ⟨T1, h1⟩ := h a List.mem_cons_self
    obtain ⟨T2, h2⟩ := list_eventually Q l (fun x hx => h x (List.mem_cons_of_mem a hx))
    refine ⟨max T1 T2, fun x hx j hj => ?_⟩
    rcases List.mem_cons.mp hx with rfl | hx
    · exact h1 j (by omega)
    · exact h2 x hx j (by omega)

/-- **BuildEnds under weak fairness**, when the definition changes are
finitely many: a build that runs ends, its definition active or deleted.
Hypotheses: finitely many crashes, definition changes and retries (of every
build); no end of the build's thread without its activation; weak fairness of
the definition changes' maps and of every build; finitely many keys with a
value at each time, writers, and builds. With the starving run of
`weak_fairness_not_enough`, which takes definition changes without end: a
build can starve only while definition changes go on. -/
theorem build_ends_finite {sp : Spec V F L} (ρ : Run sp W) {n : Name} {g : Gen}
    (hcr : ∃ N, ∀ j, N ≤ j →
      ρ.lbl j ≠ .crash ∧ ρ.lbl j ≠ .achange ∧ ∀ n' g', ρ.lbl j ≠ .bretry n' g')
    (hab : ∀ j, ρ.lbl j ≠ .babort n g)
    (hwm : WeakFair ρ .amap) (hwb : ∀ n' g', WeakFair ρ (.bld n' g'))
    (hfin : ∀ j, ∃ e, ∀ k, e < k → (ρ.sys j).st.data k = none)
    (hW : ∃ ws : List W, ∀ w, w ∈ ws)
    (hNG : ∃ ngs : List (Name × Gen), ∀ j n' g', (ρ.sys j).m.bld n' g' ≠ none → (n', g') ∈ ngs)
    {i : Nat} (hb : (ρ.sys i).m.bld n g ≠ none) (ha : (ρ.sys i).m.admin.name ≠ some n) :
    ∃ j, i ≤ j ∧ ¬ Building (ρ.sys j) n g := by
  obtain ⟨N, hN⟩ := hcr
  -- the last definition change ends at its maps
  have hkeep : ∀ j, N ≤ j → (ρ.sys j).m.admin = .idle →
      ∀ d, (ρ.sys (j + d)).m.admin = .idle := by
    intro j hj h d
    induction d with
    | zero => exact h
    | succ d ih => exact admin_idle_keep (ρ.step (j + d)) (hN _ (by omega)).2.1 ih
  obtain ⟨N1, hN1, hadm⟩ : ∃ N1, N ≤ N1 ∧ ∀ j, N1 ≤ j → (ρ.sys j).m.admin = .idle := by
    obtain ⟨j2, hj2, h2⟩ : ∃ j2, N ≤ j2 ∧ (ρ.sys j2).m.admin = .idle := by
      apply Classical.byContradiction
      intro hno
      have hne : ∀ j, N ≤ j → (ρ.sys j).m.admin ≠ .idle := fun j hj h => hno ⟨j, hj, h⟩
      obtain ⟨j3, hj3, hl⟩ := hwm N (fun j hj =>
        amap_enabled (ρ.inv j) ((ρ.inv j).minv.lockMgr.mpr (hne j hj)))
      have hst := ρ.step j3
      rw [hl] at hst
      exact hne (j3 + 1) (by omega) (amap_idle hst)
    refine ⟨j2, hj2, fun j hj => ?_⟩
    have := hkeep j2 hj2 h2 (j - j2)
    rwa [show j2 + (j - j2) = j by omega] at this
  -- from some time on, no build takes the lock
  obtain ⟨ngs, hngs⟩ := hNG
  obtain ⟨T, hT⟩ := list_eventually
    (fun (p : Name × Gen) j =>
      ¬ ((ρ.sys j).m.lock ≠ .bld p.1 p.2 ∧ (ρ.sys (j + 1)).m.lock = .bld p.1 p.2)) ngs
    (fun p _ => build_lock_finite ρ (N := N1) (fun j hj => hN j (by omega)) hadm p.1 p.2)
  have hnt : ∀ j, max T N1 ≤ j → ∀ n' g',
      ¬ ((ρ.sys j).m.lock ≠ .bld n' g' ∧ (ρ.sys (j + 1)).m.lock = .bld n' g') := by
    intro j hj n' g' ⟨h1, h2⟩
    obtain ⟨b, hb', _⟩ := (ρ.inv (j + 1)).minv.lockBld n' g' h2
    have hmem := hngs (j + 1) n' g' (by rw [hb']; intro h; cases h)
    exact hT (n', g') hmem j (by omega) ⟨h1, h2⟩
  -- the lock is free once more, and then for ever
  obtain ⟨j3, hj3, hfree⟩ := lock_released ρ ⟨N, fun j hj => (hN j hj).1⟩ hwm hwb hfin hW
    (max T N1)
  have hfr : ∀ d, (ρ.sys (j3 + d)).m.lock = .free := by
    intro d
    induction d with
    | zero => exact hfree
    | succ d ih =>
      show (ρ.sys (j3 + d + 1)).m.lock = .free
      cases h : (ρ.sys (j3 + d + 1)).m.lock with
      | free => rfl
      | mgr =>
        exact absurd (hadm (j3 + d + 1) (by omega)) ((ρ.inv (j3 + d + 1)).minv.lockMgr.mp h)
      | bld n' g' =>
        exact absurd ⟨(by rw [ih]; intro h; cases h), h⟩ (hnt (j3 + d) (by omega) n' g')
  -- the build, if it stayed building, could step at every time: weak fairness
  apply Classical.byContradiction
  intro hno
  have hBj : ∀ j, i ≤ j → Building (ρ.sys j) n g := fun j hj =>
    Classical.byContradiction fun h => hno ⟨j, hj, h⟩
  have hadmn : ∀ d, (ρ.sys (i + d)).m.admin.name ≠ some n := by
    intro d
    induction d with
    | zero => exact ha
    | succ d ih =>
      exact admin_keep (ρ.inv (i + d)) (ρ.step (i + d)) ih (hBj (i + d) (by omega))
        (hBj (i + d + 1) (by omega))
  have hbld : ∀ d, (ρ.sys (i + d)).m.bld n g ≠ none := by
    intro d
    induction d with
    | zero => exact hb
    | succ d ih =>
      exact (bld_keep (ρ.inv (i + d)) (ρ.step (i + d)) (hab _) (hadmn d) (hBj (i + d) (by omega))
        (hBj (i + d + 1) (by omega)) ih).1
  have hen : ∀ j, max i j3 ≤ j → Enabled sp (ρ.sys j) (.bld n g) := by
    intro j hj
    have h1 := hbld (j - i)
    rw [show i + (j - i) = j by omega] at h1
    have h2 := hadmn (j - i)
    rw [show i + (j - i) = j by omega] at h2
    have h3 := hfr (j - j3)
    rw [show j3 + (j - j3) = j by omega] at h3
    cases hb' : (ρ.sys j).m.bld n g with
    | none => exact absurd hb' h1
    | some b => exact build_enabled (ρ.inv j) (hBj j (by omega)) h2 hb' (Or.inl h3) (hfin j)
  have hsf : StrongFair ρ (.bld n g) := fun i0 _ =>
    let ⟨j, hj, hl⟩ := hwb n g (max i0 (max i j3)) (fun j hj => hen j (by omega))
    ⟨j, by omega, hl⟩
  obtain ⟨j, hj, hnB⟩ := build_ends ρ ⟨N, fun j hj => ⟨(hN j hj).1, (hN j hj).2.2 n g⟩⟩ hab
    hsf (fun j => ⟨max j j3, Nat.le_max_left _ _, Or.inl (by
      have := hfr (max j j3 - j3)
      rwa [show j3 + (max j j3 - j3) = max j j3 by omega] at this)⟩) hfin hW hb ha
  exact hnB (hBj j hj)

/-! ### Finitely many definitions and builds -/

/-- Finitely many names have a definition in the streams of the system, and
finitely many builds run. -/
def FinSys (s : Sys V F L W) : Prop :=
  (∃ ns : List Name, ∀ x ∈ s.st :: s.past, ∀ n, x.dfn n ≠ none → n ∈ ns) ∧
  ∃ ngs : List (Name × Gen), ∀ n g, s.m.bld n g ≠ none → (n, g) ∈ ngs

omit [DecidableEq W] in
theorem finSys_init (d0 : Key → Option V) : FinSys (Sys.init d0 : Sys V F L W) := by
  refine ⟨⟨[], fun x hx n h => ?_⟩, ⟨[], fun n g h => absurd rfl h⟩⟩
  change x ∈ [Stream.init d0] at hx
  rw [List.mem_singleton] at hx
  subst hx
  exact absurd rfl h

theorem fin_past {ns : List Name} {st' : Stream V F L} {l : List (Stream V F L)}
    (h1 : ∀ n, st'.dfn n ≠ none → n ∈ ns) (h2 : ∀ x ∈ l, ∀ n, x.dfn n ≠ none → n ∈ ns) :
    ∀ x ∈ st' :: l, ∀ n, x.dfn n ≠ none → n ∈ ns := by
  intro x hx n hn
  rcases List.mem_cons.mp hx with rfl | hx
  · exact h1 n hn
  · exact h2 x hx n hn

theorem fin_upd2 {β : Type} {f : Name → Gen → Option β} {ngs : List (Name × Gen)}
    (h : ∀ n g, f n g ≠ none → (n, g) ∈ ngs) {n0 : Name} {g0 : Gen} {v : Option β} :
    ∀ n g, upd2 f n0 g0 v n g ≠ none → (n, g) ∈ (n0, g0) :: ngs := by
  intro n g hn
  by_cases hgg : n = n0 ∧ g = g0
  · rw [hgg.1, hgg.2]; exact List.mem_cons_self
  · rw [upd2_ne _ _ hgg] at hn; exact List.mem_cons_of_mem _ (h n g hn)

/-- Every step keeps `FinSys`. -/
theorem finSys_step {sp : Spec V F L} {s s' : Sys V F L W} {lb : Lbl W}
    (hst : Step sp s lb s') (h : FinSys s) : FinSys s' := by
  obtain ⟨⟨ns, hns⟩, ⟨ngs, hngs⟩⟩ := h
  have hst0 : ∀ n, s.st.dfn n ≠ none → n ∈ ns := hns s.st List.mem_cons_self
  have keep : ∀ (st' : Stream V F L), st'.dfn = s.st.dfn →
      ∀ x ∈ st' :: (s.st :: s.past), ∀ n, x.dfn n ≠ none → n ∈ ns :=
    fun st' he => fin_past (fun n hn => hst0 n (by rw [← he]; exact hn)) hns
  have chg : ∀ (st' : Stream V F L) (n0 : Name) (v : Option (Def F)),
      st'.dfn = upd s.st.dfn n0 v →
      ∀ x ∈ st' :: (s.st :: s.past), ∀ n, x.dfn n ≠ none → n ∈ n0 :: ns := by
    intro st' n0 v he
    apply fin_past
    · intro n hn
      rw [he] at hn
      by_cases hc : n = n0
      · rw [hc]; exact List.mem_cons_self
      · rw [upd_ne _ _ hc] at hn; exact List.mem_cons_of_mem _ (hst0 n hn)
    · intro x hx n hn; exact List.mem_cons_of_mem _ (hns x hx n hn)
  cases hst with
  | wSuffix => exact ⟨⟨ns, keep _ (by rfl)⟩, ⟨ngs, hngs⟩⟩
  | wCommit => exact ⟨⟨ns, keep _ (by rfl)⟩, ⟨ngs, hngs⟩⟩
  | aCreate n fn _ _ _ => exact ⟨⟨_, chg _ n _ (by rfl)⟩, ⟨ngs, hngs⟩⟩
  | aDelete n d _ _ _ => exact ⟨⟨_, chg _ n _ (by rfl)⟩, ⟨ngs, hngs⟩⟩
  | aCreateMap => exact ⟨⟨ns, hns⟩, ⟨_, fin_upd2 hngs⟩⟩
  | bReadE => exact ⟨⟨ns, hns⟩, ⟨_, fin_upd2 hngs⟩⟩
  | bRead => exact ⟨⟨ns, hns⟩, ⟨_, fin_upd2 hngs⟩⟩
  | bCheck => exact ⟨⟨ns, hns⟩, ⟨_, fin_upd2 hngs⟩⟩
  | bCheckFail => exact ⟨⟨ns, hns⟩, ⟨_, fin_upd2 hngs⟩⟩
  | bCommit => exact ⟨⟨ns, keep _ (by rfl)⟩, ⟨_, fin_upd2 hngs⟩⟩
  | bRefused => exact ⟨⟨ns, hns⟩, ⟨_, fin_upd2 hngs⟩⟩
  | bLock => exact ⟨⟨ns, hns⟩, ⟨_, fin_upd2 hngs⟩⟩
  | bActivate n g b d _ _ _ _ _ => exact ⟨⟨_, chg _ n _ (by rfl)⟩, ⟨_, fin_upd2 hngs⟩⟩
  | bActivateFail => exact ⟨⟨ns, hns⟩, ⟨_, fin_upd2 hngs⟩⟩
  | bRetry => exact ⟨⟨ns, hns⟩, ⟨_, fin_upd2 hngs⟩⟩
  | bAbort => exact ⟨⟨ns, hns⟩, ⟨_, fin_upd2 hngs⟩⟩
  | cDel => exact ⟨⟨ns, keep _ (by rfl)⟩, ⟨ngs, hngs⟩⟩
  | cEnd => exact ⟨⟨ns, keep _ (by rfl)⟩, ⟨ngs, hngs⟩⟩
  | cut j =>
    refine ⟨⟨ns, fun x hx n hn => ?_⟩, ⟨ngs, hngs⟩⟩
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hst0 n hn
    · exact hns x (List.mem_cons_of_mem _ (List.mem_of_mem_take hx)) n hn
  | crash pre x rest heq =>
    have hin : ∀ y ∈ x :: rest, y ∈ s.st :: s.past := by
      intro y hy; rw [heq]; exact List.mem_append_right _ hy
    refine ⟨⟨ns, fun y hy n hn => hns y (hin y hy) n hn⟩,
      ⟨ns.filterMap (fun n => (x.dfn n).map (fun d => (n, d.gen))), fun n g hb => ?_⟩⟩
    change (match x.dfn n with
      | some d => if d.gen = g ∧ d.active = false then some (BSt.init d.fn) else none
      | none => none) ≠ none at hb
    cases hd : x.dfn n with
    | none => rw [hd] at hb; exact absurd rfl hb
    | some d =>
      rw [hd] at hb
      dsimp only at hb
      by_cases hc : d.gen = g ∧ d.active = false
      · have hn : n ∈ ns := hns x (hin x List.mem_cons_self) n (by rw [hd]; intro h; cases h)
        rw [List.mem_filterMap]
        exact ⟨n, hn, by rw [hd, ← hc.1]; rfl⟩
      · rw [ite_eq_right hc] at hb; exact absurd rfl hb
  | _ => exact ⟨⟨ns, hns⟩, ⟨ngs, hngs⟩⟩

theorem reach_finSys {sp : Spec V F L} {s : Sys V F L W} (h : Reach sp s) :
    FinSys s := by
  induction h with
  | init d0 => exact finSys_init d0
  | step _ hst ih => exact finSys_step hst ih

theorem upd2_new {β : Type} {f : Name → Gen → Option β} {n' n : Name} {g' g : Gen}
    {v : Option β} (h : f n g = none) (h' : upd2 f n' g' v n g ≠ none)
    (hv : f n' g' ≠ none ∨ v = none) : False := by
  by_cases hgg : n = n' ∧ g = g'
  · rw [hgg.1, hgg.2, upd2_same] at h'
    rw [hgg.1, hgg.2] at h
    rcases hv with hv | hv
    · exact hv h
    · exact h' hv
  · rw [upd2_ne _ _ hgg] at h'; exact h' h

/-- A build appears only at a creation's maps, or at a start. -/
theorem bld_new {sp : Spec V F L} {s s' : Sys V F L W} {lb : Lbl W}
    (hst : Step sp s lb s') {n : Name} {g : Gen} (h : s.m.bld n g = none)
    (h' : s'.m.bld n g ≠ none) : lb = .amap ∨ lb = .crash := by
  have hs : ∀ {n' g'} {b : BSt V F}, s.m.bld n' g' = some b → s.m.bld n' g' ≠ none :=
    fun hb => by rw [hb]; intro h; cases h
  cases hst with
  | aCreateMap => exact Or.inl rfl
  | crash => exact Or.inr rfl
  | bReadE _ _ _ _ hb _ _ => exact (upd2_new h h' (Or.inl (hs hb))).elim
  | bRead _ _ _ _ _ hb _ _ _ _ => exact (upd2_new h h' (Or.inl (hs hb))).elim
  | bCheck _ _ _ _ hb _ _ _ _ => exact (upd2_new h h' (Or.inl (hs hb))).elim
  | bCheckFail => exact (upd2_new h h' (Or.inr rfl)).elim
  | bCommit _ _ _ hb _ _ _ => exact (upd2_new h h' (Or.inl (hs hb))).elim
  | bRefused _ _ _ hb _ _ => exact (upd2_new h h' (Or.inl (hs hb))).elim
  | bLock _ _ _ hb _ _ => exact (upd2_new h h' (Or.inl (hs hb))).elim
  | bActivate => exact (upd2_new h h' (Or.inr rfl)).elim
  | bActivateFail => exact (upd2_new h h' (Or.inr rfl)).elim
  | bRetry _ _ _ hb _ => exact (upd2_new h h' (Or.inl (hs hb))).elim
  | bAbort => exact (upd2_new h h' (Or.inr rfl)).elim
  | _ => exact absurd h h'

/-- A definition change's maps come only while one is under way. -/
theorem amap_admin {sp : Spec V F L} {s s' : Sys V F L W} (hst : Step sp s .amap s') :
    s.m.admin ≠ .idle := by
  cases hst with
  | aCreateMap _ _ _ ha => rw [ha]; intro h; cases h
  | aDeleteMap _ _ ha => rw [ha]; intro h; cases h

/-- With no crash and no definition change under way from some time on, a run
has finitely many builds. -/
theorem run_bld_finite {sp : Spec V F L} (ρ : Run sp W) {N : Nat}
    (hN : ∀ j, N ≤ j → ρ.lbl j ≠ .crash) (hadm : ∀ j, N ≤ j → (ρ.sys j).m.admin = .idle) :
    ∃ ngs : List (Name × Gen), ∀ j n g, (ρ.sys j).m.bld n g ≠ none → (n, g) ∈ ngs := by
  have hL : ∀ j, ∃ l : List (Name × Gen), ∀ n g, (ρ.sys j).m.bld n g ≠ none → (n, g) ∈ l :=
    fun j => (reach_finSys (ρ.reach j)).2
  let L := fun j => Classical.choose (hL j)
  have hLs : ∀ j n g, (ρ.sys j).m.bld n g ≠ none → (n, g) ∈ L j :=
    fun j => Classical.choose_spec (hL j)
  have hback : ∀ d n g, (ρ.sys (N + d)).m.bld n g ≠ none → (ρ.sys N).m.bld n g ≠ none := by
    intro d
    induction d with
    | zero => exact fun _ _ h => h
    | succ d ih =>
      intro n g h
      apply ih n g
      intro h0
      rcases bld_new (ρ.step (N + d)) h0 h with hl | hl
      · have hst := ρ.step (N + d)
        rw [hl] at hst
        exact amap_admin hst (hadm _ (by omega))
      · exact hN _ (by omega) hl
  refine ⟨((List.range (N + 1)).map L).flatten, fun j n g h => ?_⟩
  rw [List.mem_flatten]
  by_cases hj : j ≤ N
  · exact ⟨L j, List.mem_map.mpr ⟨j, List.mem_range.mpr (by omega), rfl⟩, hLs j n g h⟩
  · have h2 := hback (j - N) n g (by rw [show N + (j - N) = j by omega]; exact h)
    exact ⟨L N, List.mem_map.mpr ⟨N, List.mem_range.mpr (by omega), rfl⟩, hLs N n g h2⟩

/-- From some time on, no definition change is under way, if they are
finitely many and their maps weakly fair. -/
theorem admin_idle_eventually {sp : Spec V F L} (ρ : Run sp W) {N : Nat}
    (hN : ∀ j, N ≤ j → ρ.lbl j ≠ .achange) (hwm : WeakFair ρ .amap) :
    ∃ N1, N ≤ N1 ∧ ∀ j, N1 ≤ j → (ρ.sys j).m.admin = .idle := by
  have hkeep : ∀ j, N ≤ j → (ρ.sys j).m.admin = .idle →
      ∀ d, (ρ.sys (j + d)).m.admin = .idle := by
    intro j hj h d
    induction d with
    | zero => exact h
    | succ d ih => exact admin_idle_keep (ρ.step (j + d)) (hN _ (by omega)) ih
  obtain ⟨j2, hj2, h2⟩ : ∃ j2, N ≤ j2 ∧ (ρ.sys j2).m.admin = .idle := by
    apply Classical.byContradiction
    intro hno
    have hne : ∀ j, N ≤ j → (ρ.sys j).m.admin ≠ .idle := fun j hj h => hno ⟨j, hj, h⟩
    obtain ⟨j3, hj3, hl⟩ := hwm N (fun j hj =>
      amap_enabled (ρ.inv j) ((ρ.inv j).minv.lockMgr.mpr (hne j hj)))
    have hst := ρ.step j3
    rw [hl] at hst
    exact hne (j3 + 1) (by omega) (amap_idle hst)
  refine ⟨j2, hj2, fun j hj => ?_⟩
  have := hkeep j2 hj2 h2 (j - j2)
  rwa [show j2 + (j - j2) = j by omega] at this

/-- **BuildEnds under weak fairness**, when the definition changes are
finitely many, with no hypothesis on the builds: `build_ends_finite`, its
finitely many builds from `run_bld_finite` (a reachable system has finitely
many, and from some time on none is made). -/
theorem build_ends_weak {sp : Spec V F L} (ρ : Run sp W) {n : Name} {g : Gen}
    (hcr : ∃ N, ∀ j, N ≤ j →
      ρ.lbl j ≠ .crash ∧ ρ.lbl j ≠ .achange ∧ ∀ n' g', ρ.lbl j ≠ .bretry n' g')
    (hab : ∀ j, ρ.lbl j ≠ .babort n g)
    (hwm : WeakFair ρ .amap) (hwb : ∀ n' g', WeakFair ρ (.bld n' g'))
    (hfin : ∀ j, ∃ e, ∀ k, e < k → (ρ.sys j).st.data k = none)
    (hW : ∃ ws : List W, ∀ w, w ∈ ws)
    {i : Nat} (hb : (ρ.sys i).m.bld n g ≠ none) (ha : (ρ.sys i).m.admin.name ≠ some n) :
    ∃ j, i ≤ j ∧ ¬ Building (ρ.sys j) n g := by
  obtain ⟨N, hN⟩ := hcr
  obtain ⟨N1, hN1, hadm⟩ := admin_idle_eventually ρ (N := N) (fun j hj => (hN j hj).2.1) hwm
  exact build_ends_finite ρ ⟨N, hN⟩ hab hwm hwb hfin hW
    (run_bld_finite ρ (N := N1) (fun j hj => (hN j (by omega)).1) hadm) hb ha

end BergDB.Index
