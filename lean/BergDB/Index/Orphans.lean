/-
The user indexes of BergDB 2026.4 in Lean: 020-26's NoOrphans (bergdb 020-29),
the entries of a generation that is not live are deleted, under fairness: a
corollary of CleanupEnds (BergDB/Index/Liveness.lean) and GensAccounted.

A marker has its cleanup, or the deletion that put it is in its maps, whose
step starts the cleanup (`CleanOk`): so after every start, and every step
keeps it but a cleanup's end by an exception (`cabort`), until the next start.
-/
import BergDB.Index.Liveness

namespace BergDB.Index

variable {V F L W : Type} [DecidableEq W]

/-- The marker of the generation g of the name n has its cleanup, or the
deletion that put it is in its maps. -/
def CleanOk (s : Sys V F L W) (n : Name) (g : Gen) : Prop :=
  s.st.mark n g = true → s.m.cln n g ≠ none ∨ s.m.admin = .delete n g

/-- The generation g of the name n has entries, and is not n's live one. -/
def Orphan (s : Sys V F L W) (n : Name) (g : Gen) : Prop :=
  (∃ k l, s.st.ent n g k l) ∧ ¬ ∃ d, s.st.dfn n = some d ∧ d.gen = g

/-- Every step keeps `CleanOk` but a cleanup's end by an exception. -/
theorem cleanOk_step {sp : Spec V F L} {s s' : Sys V F L W} {lb : Lbl W}
    (hst : Step sp s lb s') {n : Name} {g : Gen} (hab : lb ≠ .cabort n g)
    (h : CleanOk s n g) : CleanOk s' n g := by
  intro hm'
  cases hst with
  | aCreate n' fn ha _ _ =>
    rcases h hm' with hc | hc
    · exact Or.inl hc
    · rw [ha] at hc; cases hc
  | aCreateMap n' g' fn ha =>
    rcases h hm' with hc | hc
    · exact Or.inl hc
    · rw [ha] at hc; cases hc
  | aDelete n' d ha _ _ =>
    by_cases hgg : n = n' ∧ g = d.gen
    · right
      show Admin.delete n' d.gen = .delete n g
      rw [hgg.1, hgg.2]
    · have hm : s.st.mark n g = true := by
        change upd2 s.st.mark n' d.gen true n g = true at hm'
        rwa [upd2_ne _ _ hgg] at hm'
      rcases h hm with hc | hc
      · exact Or.inl hc
      · rw [ha] at hc; cases hc
  | aDeleteMap n' g' ha =>
    left
    show upd2 s.m.cln n' g' (some CSt.init) n g ≠ none
    by_cases hgg : n = n' ∧ g = g'
    · rw [hgg.1, hgg.2, upd2_same]; intro h; cases h
    · rw [upd2_ne _ _ hgg]
      rcases h hm' with hc | hc
      · exact hc
      · rw [ha] at hc
        injection hc with h1 h2
        exact absurd ⟨h1.symm, h2.symm⟩ hgg
  | cScan n' g' c keys _ _ _ _ =>
    by_cases hgg : n = n' ∧ g = g'
    · left
      show upd2 s.m.cln n' g' _ n g ≠ none
      rw [hgg.1, hgg.2, upd2_same]; intro h; cases h
    · rcases h hm' with hc | hc
      · left
        show upd2 s.m.cln n' g' _ n g ≠ none
        rw [upd2_ne _ _ hgg]; exact hc
      · exact Or.inr hc
  | cScanEnd n' g' c _ _ _ =>
    by_cases hgg : n = n' ∧ g = g'
    · left
      show upd2 s.m.cln n' g' _ n g ≠ none
      rw [hgg.1, hgg.2, upd2_same]; intro h; cases h
    · rcases h hm' with hc | hc
      · left
        show upd2 s.m.cln n' g' _ n g ≠ none
        rw [upd2_ne _ _ hgg]; exact hc
      · exact Or.inr hc
  | cDel n' g' c _ _ =>
    by_cases hgg : n = n' ∧ g = g'
    · left
      show upd2 s.m.cln n' g' _ n g ≠ none
      rw [hgg.1, hgg.2, upd2_same]; intro h; cases h
    · rcases h hm' with hc | hc
      · left
        show upd2 s.m.cln n' g' _ n g ≠ none
        rw [upd2_ne _ _ hgg]; exact hc
      · exact Or.inr hc
  | cEnd n' g' c _ _ =>
    by_cases hgg : n = n' ∧ g = g'
    · exfalso
      change upd2 s.st.mark n' g' false n g = true at hm'
      rw [hgg.1, hgg.2, upd2_same] at hm'; cases hm'
    · have hm : s.st.mark n g = true := by
        change upd2 s.st.mark n' g' false n g = true at hm'
        rwa [upd2_ne _ _ hgg] at hm'
      rcases h hm with hc | hc
      · left
        show upd2 s.m.cln n' g' none n g ≠ none
        rw [upd2_ne _ _ hgg]; exact hc
      · exact Or.inr hc
  | cAbort n' g' c _ =>
    by_cases hgg : n = n' ∧ g = g'
    · exact absurd (by rw [hgg.1, hgg.2]) hab
    · rcases h hm' with hc | hc
      · left
        show upd2 s.m.cln n' g' none n g ≠ none
        rw [upd2_ne _ _ hgg]; exact hc
      · exact Or.inr hc
  | crash pre x rest _ =>
    left
    change (if x.mark n g = true then some CSt.init else none) ≠ none
    change x.mark n g = true at hm'
    rw [ite_eq_left hm']; intro h; cases h
  | _ => exact h hm'

/-- Along a run with no `cabort` of the cleanup, `CleanOk` holds if it held at
the start. -/
theorem Run.cleanOk {sp : Spec V F L} (ρ : Run sp W) {n : Name} {g : Gen}
    (hab : ∀ j, ρ.lbl j ≠ .cabort n g) (h0 : CleanOk (ρ.sys 0) n g) :
    ∀ j, CleanOk (ρ.sys j) n g
  | 0 => h0
  | j + 1 => cleanOk_step (ρ.step j) (hab j) (ρ.cleanOk hab h0 j)

/-- A deletion's maps start its cleanup. -/
theorem amap_cln {sp : Spec V F L} {s s' : Sys V F L W} (hst : Step sp s .amap s')
    {n : Name} {g : Gen} (ha : s.m.admin = .delete n g) : s'.m.cln n g ≠ none := by
  cases hst with
  | aCreateMap n' g' fn ha' => rw [ha] at ha'; cases ha'
  | aDeleteMap n' g' ha' =>
    rw [ha] at ha'
    injection ha' with h1 h2
    show upd2 s.m.cln n' g' (some CSt.init) n g ≠ none
    rw [← h1, ← h2, upd2_same]; intro h; cases h

omit [DecidableEq W] in
/-- At a database's first start, every marker has its cleanup (there is
none). -/
theorem cleanOk_init (d0 : Key → Option V) (n : Name) (g : Gen) :
    CleanOk (Sys.init d0 : Sys V F L W) n g := by
  intro h; cases h

/-- **NoOrphans** (020-26, section 3): the entries of a generation that is not
its name's live one are deleted. From any time, at that time or later the
generation g of the name n has no entry, or is live (also after a crash that
went back to before its deletion): it is not an orphan for ever, so in
TLA+'s words `Orphan ~> ~Orphan`. Hypotheses: those
of `cleanup_ends` (finitely many crashes, no `cabort` of g's cleanup, weak
fairness of its thread, finitely many entries); weak fairness of the
definition changes' maps (a deletion's maps start its cleanup); and at the
run's start, a marker of g has its cleanup or its deletion is in its maps,
as after every start (`CleanOk`, `cleanOk_init`). -/
theorem no_orphans {sp : Spec V F L} (ρ : Run sp W) {n : Name} {g : Gen}
    (hcr : ∃ N, ∀ j, N ≤ j → ρ.lbl j ≠ .crash)
    (hab : ∀ j, ρ.lbl j ≠ .cabort n g)
    (hwf : WeakFair ρ (.cln n g))
    (hwm : WeakFair ρ .amap)
    (hfin : ∀ j, ∃ es : List (Key × L), ∀ k l, (ρ.sys j).st.ent n g k l → (k, l) ∈ es)
    (h0 : CleanOk (ρ.sys 0) n g) (i : Nat) :
    ∃ j, i ≤ j ∧ ¬ Orphan (ρ.sys j) n g := by
  apply Classical.byContradiction
  intro hno
  have hO : ∀ j, i ≤ j → Orphan (ρ.sys j) n g := fun j hj =>
    Classical.byContradiction fun h => hno ⟨j, hj, h⟩
  -- the marker stays from i on (GensAccounted)
  have hmk : ∀ j, i ≤ j → (ρ.sys j).st.mark n g = true := by
    intro j hj
    obtain ⟨⟨k, l, he⟩, hnl⟩ := hO j hj
    rcases (ρ.inv j).sinv.accounted n g k l he with h | h
    · exact absurd h hnl
    · exact h
  have hok := Run.cleanOk ρ hab h0
  by_cases hc : ∃ j, i ≤ j ∧ (ρ.sys j).m.cln n g ≠ none
  · -- a cleanup runs: CleanupEnds deletes the marker
    obtain ⟨j, hj, hcj⟩ := hc
    obtain ⟨j', hj', hm'⟩ := cleanup_ends ρ hcr hab hwf hfin hcj
    rw [hmk j' (by omega)] at hm'
    cases hm'
  · -- none: the deletion is in its maps for ever, which weak fairness refuses
    have hnc : ∀ j, i ≤ j → (ρ.sys j).m.cln n g = none := fun j hj =>
      Classical.byContradiction fun h => hc ⟨j, hj, h⟩
    have had : ∀ j, i ≤ j → (ρ.sys j).m.admin = .delete n g := by
      intro j hj
      rcases hok j (hmk j hj) with h | h
      · exact absurd (hnc j hj) h
      · exact h
    obtain ⟨j, hj, hl⟩ := hwm i (fun j hj => ⟨_, Step.aDeleteMap _ n g (had j hj)⟩)
    have hst := ρ.step j
    rw [hl] at hst
    exact amap_cln hst (had j hj) (hnc (j + 1) (by omega))

end BergDB.Index
