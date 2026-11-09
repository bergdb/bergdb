/-
The user indexes of BergDB 2026.4 in Lean: liveness (bergdb 020-29), 020-26's
CleanupEnds and BuildEnds (its section 4, points 9 and 8), under fairness.

A run is an infinite sequence of systems, each a step of a thread (`Lbl`)
from the one before. Weak fairness of a thread: if it can step at every time
from some time on, it steps. Strong fairness: if it can step at times from
some time on without end, it steps.
-/
import BergDB.Index.Locked

namespace BergDB.Index

variable {V F L W : Type}

/-! ### Counting, and descent -/

open Classical in
/-- The members of a list that have the property P (with repeats). -/
noncomputable def cnt {α : Type} (P : α → Prop) : List α → Nat
  | [] => 0
  | a :: l => (if P a then 1 else 0) + cnt P l

theorem cnt_mono {α : Type} {P P' : α → Prop} (h : ∀ a, P' a → P a) :
    ∀ l : List α, cnt P' l ≤ cnt P l
  | [] => Nat.le_refl 0
  | a :: l => by
    have := cnt_mono h l
    simp only [cnt]
    by_cases h1 : P' a
    · rw [ite_eq_left h1, ite_eq_left (h a h1)]; omega
    · rw [ite_eq_right h1]; split <;> omega

theorem cnt_lt {α : Type} {P P' : α → Prop} (h : ∀ a, P' a → P a) :
    ∀ l : List α, (∃ a, a ∈ l ∧ P a ∧ ¬ P' a) → cnt P' l < cnt P l
  | [], ⟨a, ha, _⟩ => by simp at ha
  | b :: l, ⟨a, ha, hp, hnp⟩ => by
    simp only [cnt]
    rcases List.mem_cons.mp ha with hab | ha
    · rw [← hab, ite_eq_right hnp, ite_eq_left hp]
      have := cnt_mono h l; omega
    · have := cnt_lt h l ⟨a, ha, hp, hnp⟩
      by_cases h1 : P' b
      · rw [ite_eq_left h1, ite_eq_left (h b h1)]; omega
      · rw [ite_eq_right h1]; split <;> omega

theorem cnt_le_length {α : Type} (P : α → Prop) : ∀ l : List α, cnt P l ≤ l.length
  | [] => Nat.le_refl 0
  | a :: l => by
    have := cnt_le_length P l
    simp only [cnt, List.length_cons]
    split <;> omega

/-- A measure that never grows, and falls at every step of a thread that steps
from every time on, gives a contradiction. -/
theorem descent {μ : Nat → Nat} {P : Nat → Prop} {i : Nat}
    (hle : ∀ j, i ≤ j → μ (j + 1) ≤ μ j)
    (hlt : ∀ j, i ≤ j → P j → μ (j + 1) < μ j)
    (hinf : ∀ j, i ≤ j → ∃ j', j ≤ j' ∧ P j') : False := by
  have hseg : ∀ j, i ≤ j → ∀ d, μ (j + d) ≤ μ j := by
    intro j hj d
    induction d with
    | zero => exact Nat.le_refl _
    | succ d ih => exact Nat.le_trans (hle (j + d) (by omega)) ih
  have key : ∀ m j, i ≤ j → μ j ≤ m → False := by
    intro m
    induction m with
    | zero =>
      intro j hj hμ
      obtain ⟨j', hj', hp⟩ := hinf j hj
      have h1 := hseg j hj (j' - j)
      rw [show j + (j' - j) = j' by omega] at h1
      have h2 := hlt j' (by omega) hp
      omega
    | succ m ih =>
      intro j hj hμ
      obtain ⟨j', hj', hp⟩ := hinf j hj
      have h1 := hseg j hj (j' - j)
      rw [show j + (j' - j) = j' by omega] at h1
      have h2 := hlt j' (by omega) hp
      exact ih (j' + 1) (by omega) (by omega)
  exact key (μ i) i (Nat.le_refl _) (Nat.le_refl _)

variable [DecidableEq W]

/-! ### Runs and fairness -/

/-- A run: systems from a reachable one, each a step of the thread `lbl i`
from the one before. -/
structure Run (sp : Spec V F L) (W : Type) [DecidableEq W] where
  sys : Nat → Sys V F L W
  lbl : Nat → Lbl W
  start : Reach sp (sys 0)
  step : ∀ i, Step sp (sys i) (lbl i) (sys (i + 1))

/-- The thread l can take a step from s. -/
def Enabled (sp : Spec V F L) (s : Sys V F L W) (l : Lbl W) : Prop :=
  ∃ s', Step sp s l s'

/-- Weak fairness of the thread l: if it can step at every time from i on, it
steps at some time from i on. -/
def WeakFair {sp : Spec V F L} (ρ : Run sp W) (l : Lbl W) : Prop :=
  ∀ i, (∀ j, i ≤ j → Enabled sp (ρ.sys j) l) → ∃ j, i ≤ j ∧ ρ.lbl j = l

/-- Strong fairness of the thread l: if it can step at times from i on without
end, it steps at some time from i on. -/
def StrongFair {sp : Spec V F L} (ρ : Run sp W) (l : Lbl W) : Prop :=
  ∀ i, (∀ i', i ≤ i' → ∃ j, i' ≤ j ∧ Enabled sp (ρ.sys j) l) → ∃ j, i ≤ j ∧ ρ.lbl j = l

theorem Run.reach {sp : Spec V F L} (ρ : Run sp W) : ∀ i, Reach sp (ρ.sys i)
  | 0 => ρ.start
  | i + 1 => Reach.step (ρ.reach i) (ρ.step i)

theorem Run.inv {sp : Spec V F L} (ρ : Run sp W) (i : Nat) : Inv sp (ρ.sys i) :=
  reach_inv (ρ.reach i)

/-! ### The cleanups (point 9) -/

/-- No step but a crash adds an entry to a generation with a marker. -/
theorem ent_no_grow {sp : Spec V F L} {s s' : Sys V F L W} {lb : Lbl W} (hi : Inv sp s)
    (hst : Step sp s lb s') (hcr : lb ≠ .crash) {n : Name} {g : Gen}
    (hm : s.st.mark n g = true) (k : Key) (l : L) (he : s'.st.ent n g k l) :
    s.st.ent n g k l := by
  cases hst with
  | wCommit w ws nv R old S hw hc =>
    change wEntries sp s.st.ent ws S old nv n g k l at he
    have hwi := hi.minv.wInv w
    rw [hw] at hwi
    simp only [WInv] at hwi
    obtain ⟨_, _, hS⟩ := hwi
    rcases wcommit_new he with h | ⟨a, hia, hga, hfa⟩
    · exact h
    · obtain ⟨d, hd, hdg⟩ := wcommit_live hS hc hia hfa
      exfalso
      have := hi.sinv.markerNotLive n d hd
      rw [hdg, ← hga, hm] at this; cases this
  | bCommit n' g' b hb hpc hdef _ =>
    rcases he with h | ⟨hn, hg, _⟩
    · exact h
    · exfalso
      obtain ⟨d, hd, hdg⟩ := (hi.minv.bInv n' g' b hb).live hpc hdef
      have := hi.sinv.markerNotLive n' d hd
      rw [hdg, ← hg, ← hn, hm] at this; cases this
  | cDel n' g' c _ _ => exact he.1
  | crash => exact absurd rfl hcr
  | _ => exact he

/-- A cleanup goes on while its marker stays: only a crash resets it, only its
own steps change it. -/
theorem cln_next {sp : Spec V F L} {s s' : Sys V F L W} {lb : Lbl W} (hi : Inv sp s)
    (hst : Step sp s lb s') {n : Name} {g : Gen} (hab : lb ≠ .cabort n g)
    (hc : s.m.cln n g ≠ none) (hm' : s'.st.mark n g = true) :
    s'.m.cln n g ≠ none ∧ (lb ≠ .cln n g → lb ≠ .crash → s'.m.cln n g = s.m.cln n g) := by
  cases hst with
  | aDeleteMap n' g' ha =>
    show upd2 s.m.cln n' g' (some CSt.init) n g ≠ none ∧
      (_ → _ → upd2 s.m.cln n' g' (some CSt.init) n g = s.m.cln n g)
    by_cases hgg : n = n' ∧ g = g'
    · exfalso; rw [hgg.1, hgg.2] at hc; exact hc (hi.minv.adminDelete n' g' ha).2.2
    · rw [upd2_ne _ _ hgg]; exact ⟨hc, fun _ _ => rfl⟩
  | cScan n' g' c keys _ _ _ _ =>
    show upd2 s.m.cln n' g' _ n g ≠ none ∧ (_ → _ → upd2 s.m.cln n' g' _ n g = s.m.cln n g)
    by_cases hgg : n = n' ∧ g = g'
    · rw [hgg.1, hgg.2, upd2_same]
      exact ⟨(fun h => nomatch h), fun h _ => absurd rfl h⟩
    · rw [upd2_ne _ _ hgg]; exact ⟨hc, fun _ _ => rfl⟩
  | cScanEnd n' g' c _ _ _ =>
    show upd2 s.m.cln n' g' _ n g ≠ none ∧ (_ → _ → upd2 s.m.cln n' g' _ n g = s.m.cln n g)
    by_cases hgg : n = n' ∧ g = g'
    · rw [hgg.1, hgg.2, upd2_same]
      exact ⟨(fun h => nomatch h), fun h _ => absurd rfl h⟩
    · rw [upd2_ne _ _ hgg]; exact ⟨hc, fun _ _ => rfl⟩
  | cDel n' g' c _ _ =>
    show upd2 s.m.cln n' g' _ n g ≠ none ∧ (_ → _ → upd2 s.m.cln n' g' _ n g = s.m.cln n g)
    by_cases hgg : n = n' ∧ g = g'
    · rw [hgg.1, hgg.2, upd2_same]
      exact ⟨(fun h => nomatch h), fun h _ => absurd rfl h⟩
    · rw [upd2_ne _ _ hgg]; exact ⟨hc, fun _ _ => rfl⟩
  | cEnd n' g' c _ _ =>
    show upd2 s.m.cln n' g' none n g ≠ none ∧ (_ → _ → upd2 s.m.cln n' g' none n g = s.m.cln n g)
    by_cases hgg : n = n' ∧ g = g'
    · exfalso
      change upd2 s.st.mark n' g' false n g = true at hm'
      rw [hgg.1, hgg.2, upd2_same] at hm'; cases hm'
    · rw [upd2_ne _ _ hgg]; exact ⟨hc, fun _ _ => rfl⟩
  | cAbort n' g' c _ =>
    show upd2 s.m.cln n' g' none n g ≠ none ∧ (_ → _ → upd2 s.m.cln n' g' none n g = s.m.cln n g)
    by_cases hgg : n = n' ∧ g = g'
    · exact absurd (by rw [hgg.1, hgg.2]) hab
    · rw [upd2_ne _ _ hgg]; exact ⟨hc, fun _ _ => rfl⟩
  | crash pre x rest _ =>
    refine ⟨?_, fun _ h => absurd rfl h⟩
    change (if x.mark n g = true then some CSt.init else none) ≠ none
    change x.mark n g = true at hm'
    rw [ite_eq_left hm']; intro h; cases h
  | _ => exact ⟨hc, fun _ _ => rfl⟩

open Classical in
/-- A cleanup's phase in its measure: a deletion of entries that some are
still there costs 1, one of nothing 3. -/
noncomputable def cPh (ent : Key → L → Prop) : Option (CSt L) → Nat
  | some c => match c.pc with
    | .scan => 2
    | .del => if ∃ k l, c.keys k l ∧ ent k l then 1 else 3
    | .done => 0
  | none => 0

/-- A cleanup's measure: three for each entry left, and its phase. -/
noncomputable def cMeasure (es : List (Key × L)) (s : Sys V F L W) (n : Name) (g : Gen) :
    Nat :=
  3 * cnt (fun p : Key × L => s.st.ent n g p.1 p.2) es + cPh (s.st.ent n g) (s.m.cln n g)

open Classical in
/-- **CleanupEnds** (020-26, section 4, point 9): a cleanup that runs ends: its
generation's marker is deleted. Hypotheses: finitely many crashes; the
cleanup's thread does not end otherwise (`cabort`: then the next start
resumes it); weak fairness of the cleanup's thread; finitely many entries.
None on the lock: a cleanup takes none. -/
theorem cleanup_ends {sp : Spec V F L} (ρ : Run sp W) {n : Name} {g : Gen}
    (hcr : ∃ N, ∀ j, N ≤ j → ρ.lbl j ≠ .crash)
    (hab : ∀ j, ρ.lbl j ≠ .cabort n g)
    (hwf : WeakFair ρ (.cln n g))
    (hfin : ∀ j, ∃ es : List (Key × L), ∀ k l, (ρ.sys j).st.ent n g k l → (k, l) ∈ es)
    {i : Nat} (hc : (ρ.sys i).m.cln n g ≠ none) :
    ∃ j, i ≤ j ∧ (ρ.sys j).st.mark n g = false := by
  apply Classical.byContradiction
  intro hno
  have hmk : ∀ j, i ≤ j → (ρ.sys j).st.mark n g = true := by
    intro j hj
    cases h : (ρ.sys j).st.mark n g with
    | true => rfl
    | false => exact absurd ⟨j, hj, h⟩ hno
  -- the cleanup exists from i on
  have hex : ∀ d, (ρ.sys (i + d)).m.cln n g ≠ none := by
    intro d
    induction d with
    | zero => exact hc
    | succ d ih =>
      exact (cln_next (ρ.inv (i + d)) (ρ.step (i + d)) (hab _) ih (hmk _ (by omega))).1
  have hex' : ∀ j, i ≤ j → (ρ.sys j).m.cln n g ≠ none := by
    intro j hj
    have := hex (j - i)
    rwa [show i + (j - i) = j by omega] at this
  obtain ⟨N, hN⟩ := hcr
  obtain ⟨M, hMi, hMN⟩ : ∃ M, i ≤ M ∧ N ≤ M := ⟨max i N, Nat.le_max_left _ _, Nat.le_max_right _ _⟩
  obtain ⟨es, hes⟩ := hfin M
  -- the entries left are in es from M on
  have hcov : ∀ d, ∀ k l, (ρ.sys (M + d)).st.ent n g k l → (k, l) ∈ es := by
    intro d
    induction d with
    | zero => exact hes
    | succ d ih =>
      intro k l h
      exact ih k l (ent_no_grow (ρ.inv (M + d)) (ρ.step (M + d)) (hN _ (by omega))
        (hmk _ (by omega)) k l h)
  -- the cleanup's thread can always step
  have hen : ∀ j, M ≤ j → Enabled sp (ρ.sys j) (.cln n g) := by
    intro j hj
    have hcj := hex' j (by omega)
    cases hcl : (ρ.sys j).m.cln n g with
    | none => exact absurd hcl hcj
    | some c =>
      cases hpc : c.pc with
      | scan =>
        by_cases hent : ∃ k l, (ρ.sys j).st.ent n g k l
        · exact ⟨_, Step.cScan _ n g c (fun k l => (ρ.sys j).st.ent n g k l) hcl hpc hent
            (fun _ _ h => h)⟩
        · exact ⟨_, Step.cScanEnd _ n g c hcl hpc (fun k l h => hent ⟨k, l, h⟩)⟩
      | del => exact ⟨_, Step.cDel _ n g c hcl hpc⟩
      | done => exact ⟨_, Step.cEnd _ n g c hcl hpc⟩
  have hinf : ∀ j, M ≤ j → ∃ j', j ≤ j' ∧ ρ.lbl j' = .cln n g := by
    intro j hj
    exact hwf j (fun j' hj' => hen j' (by omega))
  -- the measure
  have hcovj : ∀ j, M ≤ j → ∀ k l, (ρ.sys j).st.ent n g k l → (k, l) ∈ es := by
    intro j hj
    have := hcov (j - M)
    rwa [show M + (j - M) = j by omega] at this
  have hstep : ∀ j, M ≤ j → cMeasure es (ρ.sys (j + 1)) n g ≤ cMeasure es (ρ.sys j) n g ∧
      (ρ.lbl j = .cln n g → cMeasure es (ρ.sys (j + 1)) n g < cMeasure es (ρ.sys j) n g) := by
    intro j hj
    have hi := ρ.inv j
    have hsub : ∀ k l, (ρ.sys (j + 1)).st.ent n g k l → (ρ.sys j).st.ent n g k l :=
      fun k l h => ent_no_grow hi (ρ.step j) (hN j (by omega)) (hmk j (by omega)) k l h
    have hcnt : cnt (fun p : Key × L => (ρ.sys (j + 1)).st.ent n g p.1 p.2) es ≤
        cnt (fun p : Key × L => (ρ.sys j).st.ent n g p.1 p.2) es :=
      cnt_mono (fun p h => hsub p.1 p.2 h) es
    have hmk1 := hmk (j + 1) (by omega)
    have hcl := hex' j (by omega)
    obtain ⟨_, hsame⟩ := cln_next hi (ρ.step j) (hab j) hcl hmk1
    by_cases hl : ρ.lbl j = .cln n g
    · -- a step of the cleanup
      have hst := ρ.step j
      rw [hl] at hst
      suffices h : cMeasure es (ρ.sys (j + 1)) n g < cMeasure es (ρ.sys j) n g from
        ⟨Nat.le_of_lt h, fun _ => h⟩
      unfold cMeasure
      have hcovs := hcovj j (by omega)
      generalize hsj : ρ.sys j = s at hst hsub hcnt hcl hcovs
      generalize hsj1 : ρ.sys (j + 1) = s' at hst hsub hcnt hmk1
      cases hst with
      | cScan _ _ c keys hc' hpc hne hks =>
        show 3 * cnt (fun p : Key × L => s.st.ent n g p.1 p.2) es +
            cPh (s.st.ent n g) (upd2 s.m.cln n g (some { c with pc := .del, keys := keys }) n g) <
          3 * cnt (fun p : Key × L => s.st.ent n g p.1 p.2) es + cPh (s.st.ent n g) (s.m.cln n g)
        rw [upd2_same, hc']
        simp only [cPh, hpc]
        obtain ⟨k, l, hkl⟩ := hne
        rw [ite_eq_left ⟨k, l, hkl, hks k l hkl⟩]; omega
      | cScanEnd _ _ c hc' hpc hno =>
        show 3 * cnt (fun p : Key × L => s.st.ent n g p.1 p.2) es +
            cPh (s.st.ent n g) (upd2 s.m.cln n g (some { c with pc := .done }) n g) <
          3 * cnt (fun p : Key × L => s.st.ent n g p.1 p.2) es + cPh (s.st.ent n g) (s.m.cln n g)
        rw [upd2_same, hc']
        simp only [cPh, hpc]; omega
      | cDel _ _ c hc' hpc =>
        show 3 * cnt (fun p : Key × L => s.st.ent n g p.1 p.2 ∧ ¬ (n = n ∧ g = g ∧ c.keys p.1 p.2))
              es +
            cPh (fun k l => s.st.ent n g k l ∧ ¬ (n = n ∧ g = g ∧ c.keys k l))
              (upd2 s.m.cln n g (some { c with pc := .scan }) n g) <
          3 * cnt (fun p : Key × L => s.st.ent n g p.1 p.2) es + cPh (s.st.ent n g) (s.m.cln n g)
        rw [upd2_same, hc']
        rw [show cPh (s.st.ent n g) (some c) =
            (if ∃ k l, c.keys k l ∧ s.st.ent n g k l then 1 else 3) by simp only [cPh, hpc]]
        show 3 * cnt (fun p : Key × L => s.st.ent n g p.1 p.2 ∧ ¬ (n = n ∧ g = g ∧ c.keys p.1 p.2))
              es + 2 < _
        have hmono := cnt_mono (P := fun p : Key × L => s.st.ent n g p.1 p.2)
          (P' := fun p : Key × L => s.st.ent n g p.1 p.2 ∧ ¬ (n = n ∧ g = g ∧ c.keys p.1 p.2))
          (fun p h => h.1) es
        by_cases hp : ∃ k l, c.keys k l ∧ s.st.ent n g k l
        · rw [ite_eq_left hp]
          obtain ⟨k, l, hk1, hk2⟩ := hp
          have := cnt_lt (P := fun p : Key × L => s.st.ent n g p.1 p.2)
            (P' := fun p : Key × L => s.st.ent n g p.1 p.2 ∧ ¬ (n = n ∧ g = g ∧ c.keys p.1 p.2))
            (fun p h => h.1) es ⟨(k, l), hcovs k l hk2, hk2, fun h => h.2 ⟨rfl, rfl, hk1⟩⟩
          omega
        · rw [ite_eq_right hp]; omega
      | cEnd _ _ c hc' hpc =>
        exfalso
        change upd2 s.st.mark n g false n g = true at hmk1
        rw [upd2_same] at hmk1; cases hmk1
    · -- another thread's step: the cleanup is the same, no entry comes
      refine ⟨?_, fun h => absurd h hl⟩
      have hc1 := hsame hl (by intro h; exact hN j (by omega) h)
      unfold cMeasure
      rw [hc1]
      cases hcl' : (ρ.sys j).m.cln n g with
      | none => exact absurd hcl' hcl
      | some c =>
        cases hpc : c.pc with
        | scan => simp only [cPh, hpc]; omega
        | done => simp only [cPh, hpc]; omega
        | del =>
          simp only [cPh, hpc]
          by_cases hp1 : ∃ k l, c.keys k l ∧ (ρ.sys (j + 1)).st.ent n g k l
          · rw [ite_eq_left hp1]
            obtain ⟨k, l, hk1, hk2⟩ := hp1
            rw [ite_eq_left ⟨k, l, hk1, hsub k l hk2⟩]; omega
          · rw [ite_eq_right hp1]
            by_cases hp0 : ∃ k l, c.keys k l ∧ (ρ.sys j).st.ent n g k l
            · rw [ite_eq_left hp0]
              obtain ⟨k, l, hk1, hk2⟩ := hp0
              have hlt := cnt_lt (fun p h => hsub p.1 p.2 h) es
                ⟨(k, l), hcovj j (by omega) k l hk2, hk2, fun h => hp1 ⟨k, l, hk1, h⟩⟩
              omega
            · rw [ite_eq_right hp0]; omega
  exact descent (μ := fun j => cMeasure es (ρ.sys j) n g) (P := fun j => ρ.lbl j = .cln n g)
    (fun j hj => (hstep j hj).1) (fun j hj hp => (hstep j hj).2 hp) hinf


/-! ### The builds (point 8) -/

/-- The last write times are at most the latest time. -/
structure TimesOk (x : Stream V F L) : Prop where
  wk_le : ∀ k, x.wk k ≤ x.now
  wdef_le : ∀ n, x.wdef n ≤ x.now

/-- In every stream of a reachable system, the last write times are at most its
latest time. -/
theorem times_ok {sp : Spec V F L} {s : Sys V F L W} (h : Reach sp s) :
    ∀ x ∈ s.st :: s.past, TimesOk x := by
  induction h with
  | init d0 =>
    intro x hx
    rcases List.mem_cons.mp hx with hx | hx
    · rw [hx]; exact ⟨fun _ => Nat.le_refl 0, fun _ => Nat.le_refl 0⟩
    · cases hx
  | @step s s' l _ hst ih =>
    have h0 := ih s.st List.mem_cons_self
    have hc : ∀ (st' : Stream V F L) (m' : Mem V F L W), TimesOk st' →
        ∀ x ∈ (s.commit st' m').st :: (s.commit st' m').past, TimesOk x := by
      intro st' m' h' x hx
      rcases List.mem_cons.mp hx with hx | hx
      · rw [hx]; exact h'
      · exact ih x hx
    have hwt : ∀ (ws : Key → Bool) k, writeTimes s.st.wk ws (s.st.now + 1) k ≤ s.st.now + 1 := by
      intro ws k
      cases h : ws k
      · rw [writeTimes_no h]; exact Nat.le_succ_of_le (h0.wk_le k)
      · rw [writeTimes_yes h]; exact Nat.le_refl _
    have hud : ∀ n0 n, upd s.st.wdef n0 (s.st.now + 1) n ≤ s.st.now + 1 := by
      intro n0 n
      by_cases h : n = n0
      · rw [h, upd_same]; exact Nat.le_refl _
      · rw [upd_ne _ _ h]; exact Nat.le_succ_of_le (h0.wdef_le n)
    have hk1 : ∀ k, s.st.wk k ≤ s.st.now + 1 := fun k => Nat.le_succ_of_le (h0.wk_le k)
    have hd1 : ∀ n, s.st.wdef n ≤ s.st.now + 1 := fun n => Nat.le_succ_of_le (h0.wdef_le n)
    cases hst with
    | wSuffix ws nv _ => exact hc _ _ ⟨fun k => hwt ws k, hd1⟩
    | wCommit w ws nv R old S _ _ => exact hc _ _ ⟨fun k => hwt ws k, hd1⟩
    | aCreate n fn _ _ _ => exact hc _ _ ⟨hk1, fun n' => hud n n'⟩
    | aDelete n d _ _ _ => exact hc _ _ ⟨hk1, fun n' => hud n n'⟩
    | bCommit n g b _ _ _ _ => exact hc _ _ ⟨hk1, hd1⟩
    | bActivate n g b d _ _ _ _ _ => exact hc _ _ ⟨hk1, fun n' => hud n n'⟩
    | cDel n g c _ _ => exact hc _ _ ⟨hk1, hd1⟩
    | cEnd n g c _ _ => exact hc _ _ ⟨hk1, hd1⟩
    | cut j =>
      intro x hx
      rcases List.mem_cons.mp hx with hx | hx
      · rw [hx]; exact h0
      · exact ih x (List.mem_cons_of_mem _ (List.mem_of_mem_take hx))
    | crash pre x rest he =>
      intro y hy
      apply ih
      rw [he]; simp [hy]
    | _ => exact ih

/-- The definition of the name n is in state building with the generation g. -/
def Building (s : Sys V F L W) (n : Name) (g : Gen) : Prop :=
  ∃ d, s.st.dfn n = some d ∧ d.gen = g ∧ d.active = false

/-- While n's definition stays building, no definition change of n begins. -/
theorem admin_keep {sp : Spec V F L} {s s' : Sys V F L W} {lb : Lbl W} (hi : Inv sp s)
    (hst : Step sp s lb s') {n : Name} {g : Gen} (ha : s.m.admin.name ≠ some n)
    (hB : Building s n g) (hB' : Building s' n g) : s'.m.admin.name ≠ some n := by
  cases hst with
  | aCreate n' fn _ _ hmem =>
    intro h
    change some n' = some n at h
    have hn : n' = n := Option.some.inj h
    rw [hn] at hmem
    obtain ⟨d, hd, _, _⟩ := hB
    rcases hi.minv.memAgrees n with hm | hm
    · rw [hmem, hd] at hm; cases hm
    · exact ha hm
  | aDelete n' d _ _ _ =>
    intro h
    change some n' = some n at h
    have hn : n' = n := Option.some.inj h
    obtain ⟨d', hd', _, _⟩ := hB'
    change upd s.st.dfn n' none n = some d' at hd'
    rw [hn, upd_same] at hd'; cases hd'
  | aCreateMap _ _ _ _ => intro h; cases h
  | aDeleteMap _ _ _ => intro h; cases h
  | crash _ _ _ _ => intro h; cases h
  | _ => exact ha

theorem upd2_some_keep {β : Type} {f : Name → Gen → Option β} {n' n : Name} {g' g : Gen} {x : β}
    (hb : f n g ≠ none) : upd2 f n' g' (some x) n g ≠ none := by
  by_cases h : n = n' ∧ g = g'
  · rw [h.1, h.2, upd2_same]; intro h'; cases h'
  · rw [upd2_ne _ _ h]; exact hb

omit [DecidableEq W] in
theorem lbl_bld_ne {n' n : Name} {g' g : Gen} (h : (Lbl.bld n' g' : Lbl W) ≠ .bld n g) :
    ¬ (n = n' ∧ g = g') := fun hh => h (by rw [hh.1, hh.2])

/-- While n's definition stays building with g and no change of n is under way,
the build of g goes on: only its own steps change it, and only a crash or a
retry resets it. -/
theorem bld_keep {sp : Spec V F L} {s s' : Sys V F L W} {lb : Lbl W} (hi : Inv sp s)
    (hst : Step sp s lb s') {n : Name} {g : Gen} (hab : lb ≠ .babort n g)
    (ha : s.m.admin.name ≠ some n) (hB : Building s n g) (hB' : Building s' n g)
    (hb : s.m.bld n g ≠ none) :
    s'.m.bld n g ≠ none ∧
      (lb ≠ .bld n g → lb ≠ .bretry n g → lb ≠ .crash → s'.m.bld n g = s.m.bld n g) := by
  obtain ⟨d, hd, hdg, hda⟩ := hB
  have hmem : s.m.mem n = some d := by rw [(hi.minv.memAgrees n).resolve_right ha]; exact hd
  cases hst with
  | aCreateMap n' g' fn ha' =>
    show upd2 s.m.bld n' g' _ n g ≠ none ∧ (_ → _ → _ → upd2 s.m.bld n' g' _ n g = s.m.bld n g)
    by_cases hgg : n = n' ∧ g = g'
    · exfalso; apply ha; rw [ha', hgg.1]; rfl
    · rw [upd2_ne _ _ hgg]; exact ⟨hb, fun _ _ _ => rfl⟩
  | bReadE n' g' b e _ _ _ =>
    exact ⟨upd2_some_keep hb, fun h _ _ => by
      show upd2 s.m.bld n' g' _ n g = _; rw [upd2_ne _ _ (lbl_bld_ne h)]⟩
  | bRead n' g' b e hi' _ _ _ _ _ =>
    exact ⟨upd2_some_keep hb, fun h _ _ => by
      show upd2 s.m.bld n' g' _ n g = _; rw [upd2_ne _ _ (lbl_bld_ne h)]⟩
  | bCheck n' g' b d' _ _ _ _ _ =>
    exact ⟨upd2_some_keep hb, fun h _ _ => by
      show upd2 s.m.bld n' g' _ n g = _; rw [upd2_ne _ _ (lbl_bld_ne h)]⟩
  | bCommit n' g' b _ _ _ _ =>
    exact ⟨upd2_some_keep hb, fun h _ _ => by
      show upd2 s.m.bld n' g' _ n g = _; rw [upd2_ne _ _ (lbl_bld_ne h)]⟩
  | bRefused n' g' b _ _ _ =>
    exact ⟨upd2_some_keep hb, fun h _ _ => by
      show upd2 s.m.bld n' g' _ n g = _; rw [upd2_ne _ _ (lbl_bld_ne h)]⟩
  | bLock n' g' b _ _ _ =>
    exact ⟨upd2_some_keep hb, fun h _ _ => by
      show upd2 s.m.bld n' g' _ n g = _; rw [upd2_ne _ _ (lbl_bld_ne h)]⟩
  | bRetry n' g' b _ _ =>
    refine ⟨upd2_some_keep hb, fun _ h _ => ?_⟩
    show upd2 s.m.bld n' g' _ n g = _
    have : ¬ (n = n' ∧ g = g') := fun hh => h (by rw [hh.1, hh.2])
    rw [upd2_ne _ _ this]
  | bCheckFail n' g' b _ _ _ hnot =>
    show upd2 s.m.bld n' g' none n g ≠ none ∧ (_ → _ → _ → upd2 s.m.bld n' g' none n g = _)
    by_cases hgg : n = n' ∧ g = g'
    · exfalso; rw [← hgg.1] at hnot; exact hnot d hmem (by rw [hdg, hgg.2])
    · rw [upd2_ne _ _ hgg]; exact ⟨hb, fun _ _ _ => rfl⟩
  | bActivateFail n' g' b _ _ _ hnot =>
    show upd2 s.m.bld n' g' none n g ≠ none ∧ (_ → _ → _ → upd2 s.m.bld n' g' none n g = _)
    by_cases hgg : n = n' ∧ g = g'
    · exfalso; rw [← hgg.1] at hnot; exact hnot d hmem (by rw [hdg, hgg.2])
    · rw [upd2_ne _ _ hgg]; exact ⟨hb, fun _ _ _ => rfl⟩
  | bActivate n' g' b d' _ _ _ _ _ =>
    show upd2 s.m.bld n' g' none n g ≠ none ∧ (_ → _ → _ → upd2 s.m.bld n' g' none n g = _)
    by_cases hgg : n = n' ∧ g = g'
    · exfalso
      obtain ⟨d2, hd2, _, hda2⟩ := hB'
      change upd s.st.dfn n' (some ⟨g', b.fn, true⟩) n = some d2 at hd2
      rw [hgg.1, upd_same] at hd2; cases hd2; cases hda2
    · rw [upd2_ne _ _ hgg]; exact ⟨hb, fun _ _ _ => rfl⟩
  | bAbort n' g' b _ =>
    show upd2 s.m.bld n' g' none n g ≠ none ∧ (_ → _ → _ → upd2 s.m.bld n' g' none n g = _)
    by_cases hgg : n = n' ∧ g = g'
    · exact absurd (by rw [hgg.1, hgg.2]) hab
    · rw [upd2_ne _ _ hgg]; exact ⟨hb, fun _ _ _ => rfl⟩
  | crash pre x rest _ =>
    refine ⟨?_, fun _ _ h => absurd rfl h⟩
    obtain ⟨d2, hd2, hdg2, hda2⟩ := hB'
    change (match x.dfn n with
      | some d => if d.gen = g ∧ d.active = false then some (BSt.init d.fn) else none
      | none => none) ≠ none
    change x.dfn n = some d2 at hd2
    rw [hd2]
    dsimp only
    rw [ite_eq_left ⟨hdg2, hda2⟩]; intro h; cases h
  | _ => exact ⟨hb, fun _ _ _ => rfl⟩

/-- A build of a definition that is building, whose change is done, can step
whenever the lock is free or its own, if finitely many keys have a value. -/
theorem build_enabled {sp : Spec V F L} {s : Sys V F L W} (hi : Inv sp s) {n : Name} {g : Gen}
    (hB : Building s n g) (ha : s.m.admin.name ≠ some n) {b : BSt V F}
    (hb : s.m.bld n g = some b) (hl : s.m.lock = .free ∨ s.m.lock = .bld n g)
    (hfin : ∃ e, ∀ k, e < k → s.st.data k = none) : Enabled sp s (.bld n g) := by
  obtain ⟨d, hd, hdg, _⟩ := hB
  have hmem : s.m.mem n = some d := by rw [(hi.minv.memAgrees n).resolve_right ha]; exact hd
  have hbi := hi.minv.bInv n g b hb
  have hfree : b.locked = false → s.m.lock = .free := by
    intro hlk
    rcases hl with hl | hl
    · exact hl
    · obtain ⟨b', hb', hl'⟩ := hi.minv.lockBld n g hl
      rw [hb] at hb'; cases hb'; rw [hlk] at hl'; cases hl'
  cases hpc : b.pc with
  | readE =>
    obtain ⟨e, he⟩ := hfin
    exact ⟨_, Step.bReadE s n g b e hb hpc (fun k hk => by rw [he k hk]; exact sp.f_none _ _)⟩
  | read =>
    obtain ⟨e, hE, hne⟩ := hbi.readNext (Or.inl hpc)
    exact ⟨_, Step.bRead s n g b e (e + 1) hb hpc hE (by omega) (Nat.le_refl _)⟩
  | check => exact ⟨_, Step.bCheck s n g b d hb hpc hl hmem hdg⟩
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
  | lock => exact ⟨_, Step.bLock s n g b hb hpc (hfree (hbi.unlocked (Or.inl hpc)))⟩
  | activate =>
    exact ⟨_, Step.bActivate s n g b d hb hpc (hfree (hbi.unlocked (Or.inr hpc))) hmem hdg⟩

/-- A step's conflict: the condition of its refusal. -/
def Conflict (sp : Spec V F L) (st : Stream V F L) (n : Name) (b : BSt V F) : Prop :=
  b.R < st.wdef n ∨ ∃ k, b.next ≤ k ∧ k < b.hi ∧ sp.f b.fn k (b.snap k) ≠ none ∧ b.R < st.wk k

open Classical in
/-- The arithmetic of a build's measure within its step: L the tries before
the locked phase, lw the writers, c those that can commit a write of an
object key, lk locked, pc the phase, t the tries, cf a conflict. -/
noncomputable def nuOf (L lw c : Nat) (lk : Bool) (pc : BPc) (t : Nat) (cf : Prop) : Nat :=
  match lk, pc with
  | true, .read => 3 * c + 2
  | true, .check => 3 * c + 1 + (if cf then 3 else 0)
  | true, .commit => 3 * c + (if cf then 3 else 0)
  | true, _ => 0
  | false, .read => 3 * (L - t) + 2 + (3 * lw + 6)
  | false, .check => 3 * (L - t) + 1 + (3 * lw + 6)
  | false, .commit => 3 * (L - t) + (3 * lw + 6)
  | false, .lock => 3 * lw + 5
  | false, _ => 0

/-- A build's measure within its step. Unlocked: its tries left, then its
phase. Locked: three for each writer that can commit a write of an object key
(`locked_phase`: only those can refuse the step, each once), and its phase,
three more for a conflict already there. -/
noncomputable def bNu (sp : Spec V F L) (ws : List W) (s : Sys V F L W) (n : Name)
    (b : BSt V F) : Nat :=
  nuOf sp.lockedAfter ws.length (cnt (fun w => CanCommitObj sp (s.m.wr w)) ws) b.locked b.pc
    b.tries (Conflict sp s.st n b)

/-- A build's measure: the keys left up to E, each worth more than any step. -/
noncomputable def bMeasure (sp : Spec V F L) (ws : List W) (s : Sys V F L W) (n : Name)
    (g : Gen) : Nat :=
  match s.m.bld n g with
  | some b => (b.E.getD 0 + 1 - b.next) * (3 * sp.lockedAfter + 3 * ws.length + 12) +
      bNu sp ws s n b
  | none => 0

theorem nuOf_lt (L lw c : Nat) (hc : c ≤ lw) (lk : Bool) (pc : BPc) (t : Nat) (cf : Prop) :
    nuOf L lw c lk pc t cf < 3 * L + 3 * lw + 12 := by
  cases lk <;> cases pc <;> simp only [nuOf] <;> (try split) <;> omega

omit [DecidableEq W] in
theorem bMeasure_of {sp : Spec V F L} {ws : List W} {s : Sys V F L W} {n : Name} {g : Gen}
    {b : BSt V F} (h : s.m.bld n g = some b) :
    bMeasure sp ws s n g = (b.E.getD 0 + 1 - b.next) * (3 * sp.lockedAfter + 3 * ws.length + 12) +
      bNu sp ws s n b := by
  unfold bMeasure; rw [h]

/-- While a build holds the lock, no step changes a definition's key. -/
theorem wdef_locked {sp : Spec V F L} {s s' : Sys V F L W} {lb : Lbl W} (hst : Step sp s lb s')
    {n : Name} {g : Gen} (hl : s.m.lock = .bld n g) (hcr : lb ≠ .crash) :
    s'.st.wdef = s.st.wdef := by
  cases hst with
  | aCreate _ _ _ hf _ => rw [hl] at hf; cases hf
  | aDelete _ _ _ hf _ => rw [hl] at hf; cases hf
  | bActivate _ _ _ _ _ _ hf _ _ => rw [hl] at hf; cases hf
  | crash => exact absurd rfl hcr
  | _ => rfl


omit [DecidableEq W] in
theorem bNu_lt (sp : Spec V F L) (ws : List W) (s : Sys V F L W) (n : Name) (b : BSt V F) :
    bNu sp ws s n b < 3 * sp.lockedAfter + 3 * ws.length + 12 :=
  nuOf_lt _ _ _ (cnt_le_length _ ws) _ _ _ _

omit [DecidableEq W] in
/-- A build's measure falls when its next key moves up, up to its end key. -/
theorem bMeasure_next {sp : Spec V F L} {ws : List W} {s₁ s₂ : Sys V F L W} {n : Name}
    {g : Gen} {b₁ b₂ : BSt V F} {e : Key} (h₁ : s₁.m.bld n g = some b₁)
    (h₂ : s₂.m.bld n g = some b₂) (hE₁ : b₁.E = some e) (hE₂ : b₂.E = some e)
    (hn : b₁.next < b₂.next) (hle : b₂.next ≤ e + 1) :
    bMeasure sp ws s₂ n g < bMeasure sp ws s₁ n g := by
  rw [bMeasure_of h₁, bMeasure_of h₂, hE₁, hE₂]
  have hK := bNu_lt sp ws s₂ n b₂
  have h1 : (e + 1 - b₂.next + 1) * (3 * sp.lockedAfter + 3 * ws.length + 12) ≤
      (e + 1 - b₁.next) * (3 * sp.lockedAfter + 3 * ws.length + 12) :=
    Nat.mul_le_mul_right _ (by omega)
  have h2 : (e + 1 - b₂.next + 1) * (3 * sp.lockedAfter + 3 * ws.length + 12) =
      (e + 1 - b₂.next) * (3 * sp.lockedAfter + 3 * ws.length + 12) +
        (3 * sp.lockedAfter + 3 * ws.length + 12) := Nat.succ_mul _ _
  show (e + 1 - b₂.next) * _ + _ < (e + 1 - b₁.next) * _ + _
  omega

omit [DecidableEq W] in
/-- With the same E and next, a build's measure compares as its step's part. -/
theorem bMeasure_same {sp : Spec V F L} {ws : List W} {s₁ s₂ : Sys V F L W} {n : Name}
    {g : Gen} {b₁ b₂ : BSt V F} (h₁ : s₁.m.bld n g = some b₁) (h₂ : s₂.m.bld n g = some b₂)
    (hE : b₂.E = b₁.E) (hn : b₂.next = b₁.next) :
    (bNu sp ws s₂ n b₂ ≤ bNu sp ws s₁ n b₁ → bMeasure sp ws s₂ n g ≤ bMeasure sp ws s₁ n g) ∧
    (bNu sp ws s₂ n b₂ < bNu sp ws s₁ n b₁ → bMeasure sp ws s₂ n g < bMeasure sp ws s₁ n g) := by
  rw [bMeasure_of h₁, bMeasure_of h₂, hE, hn]
  exact ⟨fun h => by omega, fun h => by omega⟩

open Classical in
/-- One step of a run while a definition stays building: its build stays out of
`readE`, its measure does not grow, and falls at the build's own step. -/
theorem build_step {sp : Spec V F L} {ws : List W} (hws : ∀ w, w ∈ ws) {s s' : Sys V F L W}
    {lb : Lbl W} (hi : Inv sp s) (hi' : Inv sp s') (htk : TimesOk s.st) (hst : Step sp s lb s')
    {n : Name} {g : Gen} (hcr : lb ≠ .crash) (hre : lb ≠ .bretry n g) (hab : lb ≠ .babort n g)
    (ha : s.m.admin.name ≠ some n) (hB : Building s n g) (hB' : Building s' n g)
    {b : BSt V F} (hb : s.m.bld n g = some b) (hpc : b.pc ≠ .readE) :
    ∃ b', s'.m.bld n g = some b' ∧ b'.pc ≠ .readE ∧
      bMeasure sp ws s' n g ≤ bMeasure sp ws s n g ∧
      (lb = .bld n g → bMeasure sp ws s' n g < bMeasure sp ws s n g) := by
  have hbi := hi.minv.bInv n g b hb
  have hcle := cnt_le_length (fun w => CanCommitObj sp (s.m.wr w)) ws
  by_cases hl : lb = .bld n g
  · subst hl
    obtain ⟨d, hd, hdg, hda⟩ := hB
    have hmem : s.m.mem n = some d := by rw [(hi.minv.memAgrees n).resolve_right ha]; exact hd
    cases hst with
    | bReadE _ _ b0 e hb0 hpc0 _ =>
      rw [hb] at hb0; cases hb0; exact absurd hpc0 hpc
    | bRead _ _ b0 e hi0 hb0 hpc0 hE hnh hhi =>
      rw [hb] at hb0; cases hb0
      refine ⟨_, upd2_same _ _ _ _, (fun h => by cases h), ?_⟩
      have hlt : bNu sp ws s n
          { b with hi := hi0, R := s.st.now, snap := s.st.data, ended := decide (hi0 = e + 1),
                   pc := .check } < bNu sp ws s n b := by
        have hnc : Conflict sp s.st n
            { b with hi := hi0, R := s.st.now, snap := s.st.data, ended := decide (hi0 = e + 1),
                     pc := .check } = False := by
          apply propext; refine ⟨?_, False.elim⟩
          rintro (h | ⟨k, _, _, _, h⟩)
          · exact absurd h (Nat.not_lt.mpr (htk.wdef_le n))
          · exact absurd h (Nat.not_lt.mpr (htk.wk_le k))
        simp only [bNu]
        rw [hnc, hpc0]
        cases hlk : b.locked
        · simp only [nuOf]; omega
        · simp only [nuOf]; rw [ite_eq_right not_false]; omega
      suffices hm : bMeasure sp ws _ n g < bMeasure sp ws s n g from ⟨Nat.le_of_lt hm, fun _ => hm⟩
      exact (bMeasure_same hb (by exact upd2_same _ _ _ _) (by rfl) (by rfl)).2 hlt
    | bCheck _ _ b0 d0 hb0 hpc0 _ _ _ =>
      rw [hb] at hb0; cases hb0
      refine ⟨_, upd2_same _ _ _ _, (fun h => by cases h), ?_⟩
      have hlt : bNu sp ws s n { b with pc := .commit } < bNu sp ws s n b := by
        have hce : Conflict sp s.st n { b with pc := .commit } = Conflict sp s.st n b := rfl
        simp only [bNu]
        rw [hce, hpc0]
        cases hlk : b.locked
        · simp only [nuOf]; omega
        · simp only [nuOf]; split <;> omega
      suffices hm : bMeasure sp ws _ n g < bMeasure sp ws s n g from ⟨Nat.le_of_lt hm, fun _ => hm⟩
      exact (bMeasure_same hb (by exact upd2_same _ _ _ _) (by rfl) (by rfl)).2 hlt
    | bCheckFail _ _ b0 hb0 _ _ hnot =>
      exact absurd hdg (hnot d hmem)
    | bCommit _ _ b0 hb0 hpc0 _ _ =>
      rw [hb] at hb0; cases hb0
      obtain ⟨e, hE, hnh, hhi, _⟩ := (hbi.inStep (Or.inr hpc0)).range
      refine ⟨_, upd2_same _ _ _ _, ?_, ?_⟩
      · show (if b.ended = true then BPc.activate else BPc.read) ≠ .readE
        split <;> (intro h; cases h)
      · suffices hm : bMeasure sp ws _ n g < bMeasure sp ws s n g from
          ⟨Nat.le_of_lt hm, fun _ => hm⟩
        exact bMeasure_next (b₂ := bAfter b) hb (by exact upd2_same _ _ _ _) hE hE hnh hhi
    | bRefused _ _ b0 hb0 hpc0 hconf =>
      rw [hb] at hb0; cases hb0
      refine ⟨_, upd2_same _ _ _ _, ?_, ?_⟩
      · show (if b.locked = false ∧ sp.lockedAfter ≤ b.tries + 1 then BPc.lock else BPc.read) ≠ .readE
        split <;> (intro h; cases h)
      · have hlt : bNu sp ws s n
            { b with pc := if b.locked = false ∧ sp.lockedAfter ≤ b.tries + 1 then .lock else .read,
                     tries := if b.locked = true ∨ sp.lockedAfter ≤ b.tries + 1 then 0
                              else b.tries + 1 } < bNu sp ws s n b := by
          have hce : Conflict sp s.st n
              { b with pc := if b.locked = false ∧ sp.lockedAfter ≤ b.tries + 1 then .lock else .read,
                       tries := if b.locked = true ∨ sp.lockedAfter ≤ b.tries + 1 then 0
                                else b.tries + 1 } = Conflict sp s.st n b := rfl
          have hcf : Conflict sp s.st n b := hconf
          simp only [bNu]
          rw [hce, hpc0]
          cases hlk : b.locked
          · by_cases hL : sp.lockedAfter ≤ b.tries + 1
            · rw [ite_eq_left ⟨rfl, hL⟩]
              simp only [nuOf]; omega
            · rw [ite_eq_right (fun h => hL h.2), ite_eq_right (fun h => by
                rcases h with h | h
                · cases h
                · exact hL h)]
              simp only [nuOf]; omega
          · rw [ite_eq_right (fun h => by cases h.1)]
            simp only [nuOf]
            rw [ite_eq_left hcf]; omega
        suffices hm : bMeasure sp ws _ n g < bMeasure sp ws s n g from
          ⟨Nat.le_of_lt hm, fun _ => hm⟩
        exact (bMeasure_same hb (by exact upd2_same _ _ _ _) (by rfl) (by rfl)).2 hlt
    | bLock _ _ b0 hb0 hpc0 _ =>
      rw [hb] at hb0; cases hb0
      have hunl := hbi.unlocked (Or.inl hpc0)
      refine ⟨_, upd2_same _ _ _ _, (fun h => by cases h), ?_⟩
      have hlt : bNu sp ws s n { b with locked := true, pc := .read } < bNu sp ws s n b := by
        simp only [bNu]
        rw [hpc0, hunl]
        simp only [nuOf]; omega
      suffices hm : bMeasure sp ws _ n g < bMeasure sp ws s n g from ⟨Nat.le_of_lt hm, fun _ => hm⟩
      exact (bMeasure_same hb (by exact upd2_same _ _ _ _) (by rfl) (by rfl)).2 hlt
    | bActivate _ _ b0 d0 hb0 _ _ _ _ =>
      exfalso
      obtain ⟨d2, hd2, _, hda2⟩ := hB'
      change upd s.st.dfn n (some ⟨g, b0.fn, true⟩) n = some d2 at hd2
      rw [upd_same] at hd2; cases hd2; cases hda2
    | bActivateFail _ _ b0 hb0 _ _ hnot =>
      exact absurd hdg (hnot d hmem)
  · -- another thread's step: the build is the same
    obtain ⟨_, hsame⟩ := bld_keep hi hst hab ha hB hB' (by rw [hb]; intro h; cases h)
    have hb' : s'.m.bld n g = some b := by rw [hsame hl hre hcr, hb]
    refine ⟨b, hb', hpc, ?_, fun h => absurd h hl⟩
    apply (bMeasure_same (sp := sp) (ws := ws) hb hb' rfl rfl).1
    simp only [bNu]
    cases hlk : b.locked
    · cases b.pc <;> simp only [nuOf] <;> omega
    · -- locked: the lock is the build's, before and after
      have hl0 : s.m.lock = .bld n g := hi.minv.bLocked n g b hb hlk
      have hl1 : s'.m.lock = .bld n g := hi'.minv.bLocked n g b hb' hlk
      have hcm : ∀ w, CanCommitObj sp (s'.m.wr w) → CanCommitObj sp (s.m.wr w) := by
        intro w h; have := locked_no_new_writer hst hl0 hl1 w h; rw [this] at h; exact h
      have hc := cnt_mono hcm ws
      have hcf : Conflict sp s'.st n b → Conflict sp s.st n b ∨
          cnt (fun w => CanCommitObj sp (s'.m.wr w)) ws <
            cnt (fun w => CanCommitObj sp (s.m.wr w)) ws := by
        intro hc'
        by_cases hc0 : Conflict sp s.st n b
        · exact Or.inl hc0
        · right
          rcases hc' with h1 | ⟨k, h1, h2, h3, h4⟩
          · exfalso; apply hc0; left; rw [← wdef_locked hst hl0 hcr]; exact h1
          · have hne : s'.st.wk k ≠ s.st.wk k := fun he =>
              hc0 (Or.inr ⟨k, h1, h2, h3, by rw [← he]; exact h4⟩)
            have hob : sp.isObj k = true := by
              cases hk : sp.isObj k with
              | true => rfl
              | false => exact absurd (sp.f_suffix _ _ _ hk) h3
            obtain ⟨w, hw1, hw2⟩ := locked_obj_write hst hl1 hob hne
            exact cnt_lt hcm ws ⟨w, hws w, hw1, by rw [hw2]; exact id⟩
      cases hpc' : b.pc with
      | read => simp only [nuOf]; omega
      | check =>
        simp only [nuOf]
        by_cases h1 : Conflict sp s'.st n b
        · rcases hcf h1 with h2 | h2
          · rw [ite_eq_left h1, ite_eq_left h2]; omega
          · rw [ite_eq_left h1]; split <;> omega
        · rw [ite_eq_right h1]; split <;> omega
      | commit =>
        simp only [nuOf]
        by_cases h1 : Conflict sp s'.st n b
        · rcases hcf h1 with h2 | h2
          · rw [ite_eq_left h1, ite_eq_left h2]; omega
          · rw [ite_eq_left h1]; split <;> omega
        · rw [ite_eq_right h1]; split <;> omega
      | readE => exact absurd hpc' hpc
      | lock => simp only [nuOf]; omega
      | activate => simp only [nuOf]; omega


/-- A build's step from `readE` reads its end key. -/
theorem readE_step {sp : Spec V F L} {s s' : Sys V F L W} {n : Name} {g : Gen}
    (hst : Step sp s (.bld n g) s') {b : BSt V F} (hb : s.m.bld n g = some b)
    (hpc : b.pc = .readE) : ∃ b', s'.m.bld n g = some b' ∧ b'.pc ≠ .readE := by
  cases hst with
  | bReadE _ _ b0 e hb0 _ _ =>
    exact ⟨_, upd2_same _ _ _ _, fun h => by cases h⟩
  | bRead _ _ b0 _ _ hb0 hpc0 _ _ _ => rw [hb] at hb0; cases hb0; rw [hpc] at hpc0; cases hpc0
  | bCheck _ _ b0 _ hb0 hpc0 _ _ _ => rw [hb] at hb0; cases hb0; rw [hpc] at hpc0; cases hpc0
  | bCheckFail _ _ b0 hb0 hpc0 _ _ => rw [hb] at hb0; cases hb0; rw [hpc] at hpc0; cases hpc0
  | bCommit _ _ b0 hb0 hpc0 _ _ => rw [hb] at hb0; cases hb0; rw [hpc] at hpc0; cases hpc0
  | bRefused _ _ b0 hb0 hpc0 _ => rw [hb] at hb0; cases hb0; rw [hpc] at hpc0; cases hpc0
  | bLock _ _ b0 hb0 hpc0 _ => rw [hb] at hb0; cases hb0; rw [hpc] at hpc0; cases hpc0
  | bActivate _ _ b0 _ hb0 hpc0 _ _ _ => rw [hb] at hb0; cases hb0; rw [hpc] at hpc0; cases hpc0
  | bActivateFail _ _ b0 hb0 hpc0 _ _ =>
    rw [hb] at hb0; cases hb0; rw [hpc] at hpc0; cases hpc0

/-- **BuildEnds** (020-26, section 4, point 8): a build that runs ends: its
definition becomes active, or is deleted. The hypotheses, plainly:

* finitely many crashes and retries of the build (`bretry`, after an
  exception), and no end of its thread without its activation (`babort`, a
  FAILED build: then the definition stays building until the next start, by
  design);
* **the lock**: the build's thread is strongly fair (if it can step at times
  without end, it steps), and the lock is free or the build's own at times
  without end (its other holders, definition changes and other builds'
  locked steps, release it). The steps that need no lock are then taken
  whenever the build can take them; only those that need it (`isLive`, its
  locked phase, its activation) need the lock's fairness;
* finitely many keys with a value at each time (E exists), and finitely many
  writers.

Writers may write for ever: in its locked phase a step is refused at most once
per writer that could commit when the lock was taken (`locked_phase`). -/
theorem build_ends {sp : Spec V F L} (ρ : Run sp W) {n : Name} {g : Gen}
    (hcr : ∃ N, ∀ j, N ≤ j → ρ.lbl j ≠ .crash ∧ ρ.lbl j ≠ .bretry n g)
    (hab : ∀ j, ρ.lbl j ≠ .babort n g)
    (hsf : StrongFair ρ (.bld n g))
    (hlock : ∀ j, ∃ j', j ≤ j' ∧ ((ρ.sys j').m.lock = .free ∨ (ρ.sys j').m.lock = .bld n g))
    (hfin : ∀ j, ∃ e, ∀ k, e < k → (ρ.sys j).st.data k = none)
    (hW : ∃ ws : List W, ∀ w, w ∈ ws)
    {i : Nat} (hb : (ρ.sys i).m.bld n g ≠ none) (ha : (ρ.sys i).m.admin.name ≠ some n) :
    ∃ j, i ≤ j ∧ ¬ Building (ρ.sys j) n g := by
  apply Classical.byContradiction
  intro hno
  have hBj : ∀ j, i ≤ j → Building (ρ.sys j) n g := fun j hj =>
    Classical.byContradiction fun h => hno ⟨j, hj, h⟩
  obtain ⟨ws, hws⟩ := hW
  obtain ⟨N, hN⟩ := hcr
  have hadm : ∀ d, (ρ.sys (i + d)).m.admin.name ≠ some n := by
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
      exact (bld_keep (ρ.inv (i + d)) (ρ.step (i + d)) (hab _) (hadm d) (hBj (i + d) (by omega))
        (hBj (i + d + 1) (by omega)) ih).1
  have hadm' : ∀ j, i ≤ j → (ρ.sys j).m.admin.name ≠ some n := by
    intro j hj; have := hadm (j - i); rwa [show i + (j - i) = j by omega] at this
  have hbld' : ∀ j, i ≤ j → ∃ b, (ρ.sys j).m.bld n g = some b := by
    intro j hj
    have := hbld (j - i)
    rw [show i + (j - i) = j by omega] at this
    cases h : (ρ.sys j).m.bld n g with
    | none => exact absurd h this
    | some b => exact ⟨b, rfl⟩
  -- the build steps from every time on: strong fairness, the lock free or its own
  have hinf : ∀ j, i ≤ j → ∃ j', j ≤ j' ∧ ρ.lbl j' = .bld n g := by
    intro j hj
    apply hsf j
    intro i' hi'
    obtain ⟨j', hj', hl⟩ := hlock i'
    refine ⟨j', hj', ?_⟩
    obtain ⟨b, hb'⟩ := hbld' j' (by omega)
    exact build_enabled (ρ.inv j') (hBj j' (by omega)) (hadm' j' (by omega)) hb' hl (hfin j')
  -- a time M after the crashes and retries, with the build out of readE
  obtain ⟨M, hMi, hMN, hM⟩ : ∃ M, i ≤ M ∧ N ≤ M ∧
      ∃ b, (ρ.sys M).m.bld n g = some b ∧ b.pc ≠ .readE := by
    apply Classical.byContradiction
    intro hno2
    obtain ⟨j, hj, hlj⟩ := hinf (max i N) (Nat.le_max_left _ _)
    obtain ⟨b, hbj⟩ := hbld' j (by omega)
    have hpcj : b.pc = .readE := Classical.byContradiction fun h =>
      hno2 ⟨j, by omega, by omega, b, hbj, h⟩
    have hst := ρ.step j
    rw [hlj] at hst
    obtain ⟨b', hb', hpc'⟩ := readE_step hst hbj hpcj
    exact hno2 ⟨j + 1, by omega, by omega, b', hb', hpc'⟩
  -- from M on: the measure
  have hstep : ∀ j, M ≤ j → (∃ b, (ρ.sys j).m.bld n g = some b ∧ b.pc ≠ .readE) →
      (∃ b', (ρ.sys (j + 1)).m.bld n g = some b' ∧ b'.pc ≠ .readE) ∧
      bMeasure sp ws (ρ.sys (j + 1)) n g ≤ bMeasure sp ws (ρ.sys j) n g ∧
      (ρ.lbl j = .bld n g → bMeasure sp ws (ρ.sys (j + 1)) n g < bMeasure sp ws (ρ.sys j) n g) := by
    intro j hj ⟨b, hbj, hpcj⟩
    obtain ⟨b', hb', hpc', hle, hlt⟩ := build_step hws (ρ.inv j) (ρ.inv (j + 1))
      (times_ok (ρ.reach j) _ List.mem_cons_self) (ρ.step j) (hN j (by omega)).1
      (hN j (by omega)).2 (hab j) (hadm' j (by omega)) (hBj j (by omega)) (hBj (j + 1) (by omega))
      hbj hpcj
    exact ⟨⟨b', hb', hpc'⟩, hle, hlt⟩
  have hout : ∀ d, ∃ b, (ρ.sys (M + d)).m.bld n g = some b ∧ b.pc ≠ .readE := by
    intro d
    induction d with
    | zero => exact hM
    | succ d ih => exact (hstep (M + d) (by omega) ih).1
  have hout' : ∀ j, M ≤ j → ∃ b, (ρ.sys j).m.bld n g = some b ∧ b.pc ≠ .readE := by
    intro j hj; have := hout (j - M); rwa [show M + (j - M) = j by omega] at this
  exact descent (μ := fun j => bMeasure sp ws (ρ.sys j) n g) (P := fun j => ρ.lbl j = .bld n g)
    (i := M) (fun j hj => (hstep j hj (hout' j hj)).2.1)
    (fun j hj hp => (hstep j hj (hout' j hj)).2.2 hp) (fun j hj => hinf j (by omega))

end BergDB.Index
