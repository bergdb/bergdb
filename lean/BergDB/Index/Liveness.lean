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

end BergDB.Index
