/-
Proofs for a cold start's reads counted as reads (bergdb item 007;
SIS/BoundColdReads.lean). Added 2026-11-13.

The count is structural: a writer's follow reads at most a header and a
version, a node of gd(j) at most its version; the rest is summed as it is.
-/
import SIS.BoundColdReads
import SIS.Proof.BoundColdDropJ

set_option linter.unusedSectionVars false

namespace SIS

variable {V T : Type} [DecidableEq V]

theorem lazyMemBase_eq (sp : Spec V T) (S : Stream V T) : lazyMemBase sp S = lazyBase sp S := rfl

theorem foldl_pair_fst {α β : Type} (f : α → β → α) (g : α → β → Nat) :
    ∀ (l : List β) (m : α) (n : Nat),
      (l.foldl (fun (a : α × Nat) x => (f a.1 x, a.2 + g a.1 x)) (m, n)).1 = l.foldl f m := by
  intro l
  induction l with
  | nil => intro m n; rfl
  | cons x l ih => intro m n; simp only [List.foldl_cons]; exact ih _ _

theorem foldl_pair_snd_le {α β : Type} (f : α → β → α) (g : α → β → Nat) (c : Nat)
    (hg : ∀ m x, g m x ≤ c) :
    ∀ (l : List β) (m : α) (n : Nat),
      (l.foldl (fun (a : α × Nat) x => (f a.1 x, a.2 + g a.1 x)) (m, n)).2 ≤ n + c * l.length := by
  intro l
  induction l with
  | nil => intro m n; simp
  | cons x l ih =>
    intro m n
    simp only [List.foldl_cons, List.length_cons]
    have h1 := ih (f m x) (n + g m x)
    have h2 := hg m x
    rw [Nat.mul_add, Nat.mul_one]
    omega

theorem Mem.followReads_le (S : Stream V T) (m : Mem V) (hp : Nat) (y : NodeId) :
    m.followReads S hp y ≤ 2 := by
  unfold Mem.followReads
  split
  · dsimp only
    repeat' split
    all_goals omega
  · omega

theorem Mem.reachOnPathReads_le (sp : Spec V T) (S : Stream V T) (P : Struct V) (j : Time)
    (path : List NodeId) (m : Mem V) (x : NodeId) : m.reachOnPathReads sp S P j path x ≤ 2 := by
  unfold Mem.reachOnPathReads
  split
  · omega
  · simp only
    split
    · split
      · exact Mem.followReads_le S m _ x
      · omega
    · omega

theorem Mem.canonicalNodeReads_le (S : Stream V T) (m : Mem V) (x : NodeId) :
    m.canonicalNodeReads S x ≤ 1 := by
  unfold Mem.canonicalNodeReads
  split
  · omega
  · split <;> omega

/-- The memory of the counted rerun is the lazy startup's. -/
theorem lazyReadsRun_mem (sp : Spec V T) (sib : T → Nat) (S : Stream V T) :
    (lazyReadsRun sp sib S).1.1 = lazyStartup sp S := by
  rw [lazyStartup_eq]
  unfold lazyReadsRun
  rw [lazyMemBase_eq]
  have key : ∀ (l : List Nat) (acc : Mem V × Struct V) (n : Nat),
      (l.foldl (lazyReadStep sp sib S) (acc, n)).1 = l.foldl (rerunStep sp S) acc := by
    intro l
    induction l with
    | nil => intro acc n; rfl
    | cons j l ih =>
      intro acc n
      simp only [List.foldl_cons]
      have h : lazyReadStep sp sib S (acc, n) j =
          (rerunStep sp S acc j, (lazyReadStep sp sib S (acc, n) j).2) := by
        cases hS : S[j]? with
        | none => simp [lazyReadStep, rerunStep, hS]
        | some R =>
          cases htr : R.trans with
          | none => simp [lazyReadStep, rerunStep, hS, htr]
          | some tr =>
            rw [rerunStep_eq sp S acc hS htr]
            simp only [lazyReadStep, hS, htr, foldl_pair_fst]
            rfl
      rw [h, ih]
  rw [key]

/-- One counted transaction of the rerun: P moves as the rerun's, and the
reads are at most 2 for each node of the writer's paths, 1 for each node of
gd(j), and 2 `sib tr`. -/
theorem lazyReadStep_spec (sp : Spec V T) (sib : T → Nat) (S : Stream V T)
    (acc : (Mem V × Struct V) × Nat) {j : Nat} {R : Record V T} {tr : T}
    (hS : S[j]? = some R) (htr : R.trans = some tr) :
    (lazyReadStep sp sib S acc j).1.2 = acc.1.2.apply j (sp.exec tr j (view sp acc.1.2 (j - 1))) ∧
    (lazyReadStep sp sib S acc j).2 ≤ acc.2 +
      2 * (pathOf sp acc.1.2 (sp.exec tr j (view sp acc.1.2 (j - 1))) j).length + R.gd.length +
      2 * sib tr := by
  unfold lazyReadStep
  simp only [hS, htr]
  refine ⟨by first | rfl | trivial, ?_⟩
  refine Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.le_refl _) ?_) ?_) (Nat.le_refl _)
  · exact Nat.le_trans (foldl_pair_snd_le _ _ 2 (fun m x => Mem.reachOnPathReads_le sp S _ j _ m x)
      _ _ 0) (by rw [List.length_mergeSort]; omega)
  · exact Nat.le_trans (foldl_pair_snd_le _ _ 1 (fun m x => Mem.canonicalNodeReads_le S m x) _ _ 0)
      (by omega)

theorem fold_reads_gen (sp : Spec V T) (sib : T → Nat) (S : Stream V T)
    (G : Nat × Struct V → Nat → Nat × Struct V) (sibOf : Nat → Nat)
    (hG1 : ∀ b j R tr, S[j]? = some R → R.trans = some tr →
      G b j = (b.1 + (pathOf sp b.2 (sp.exec tr j (view sp b.2 (j - 1))) j).length +
        (sp.exec tr j (view sp b.2 (j - 1))).new.length + R.gd.length,
        b.2.apply j (sp.exec tr j (view sp b.2 (j - 1)))) ∧ sibOf j = sib tr)
    (hG0 : ∀ b j, (∀ R tr, S[j]? = some R → R.trans = some tr → False) → G b j = b ∧ sibOf j = 0) :
    ∀ (l : List Nat) (acc : (Mem V × Struct V) × Nat) (b : Nat × Struct V), acc.1.2 = b.2 →
      (l.foldl (lazyReadStep sp sib S) acc).2 + 2 * b.1 ≤
        acc.2 + 2 * (l.foldl G b).1 + 2 * (l.map sibOf).sum := by
  intro l
  induction l with
  | nil => intro acc b _; simp
  | cons j l ih =>
    intro acc b hab
    simp only [List.foldl_cons, List.map_cons, List.sum_cons]
    by_cases hx : ∃ R tr, S[j]? = some R ∧ R.trans = some tr
    · obtain ⟨R, tr, hS, htr⟩ := hx
      obtain ⟨hG, hsj⟩ := hG1 b j R tr hS htr
      obtain ⟨hP, hcnt⟩ := lazyReadStep_spec sp sib S acc hS htr
      rw [hab] at hP hcnt
      have hP' : (lazyReadStep sp sib S acc j).1.2 = (G b j).2 := by rw [hG]; exact hP
      have := ih (lazyReadStep sp sib S acc j) (G b j) hP'
      have hb1 : (G b j).1 = b.1 + (pathOf sp b.2 (sp.exec tr j (view sp b.2 (j - 1))) j).length +
          (sp.exec tr j (view sp b.2 (j - 1))).new.length + R.gd.length := by rw [hG]
      rw [hsj]
      omega
    · have hn : ∀ R tr, S[j]? = some R → R.trans = some tr → False :=
        fun R tr h1 h2 => hx ⟨R, tr, h1, h2⟩
      obtain ⟨hG, hsj⟩ := hG0 b j hn
      have hF : lazyReadStep sp sib S acc j = acc := by
        cases hS : S[j]? with
        | none => simp [lazyReadStep, hS]
        | some R =>
          cases htr : R.trans with
          | none => simp [lazyReadStep, hS, htr]
          | some tr => exact absurd (hn R tr hS htr) id
      rw [hF, hG, hsj]
      have := ih acc b hab
      omega

theorem fold_reads_gen' (sp : Spec V T) (sib : T → Nat) (S : Stream V T)
    (G : Nat × Struct V → Nat → Nat × Struct V) (sibOf : Nat → Nat) (l : List Nat) (m0 : Mem V)
    (P0 : Struct V)
    (hG1 : ∀ b j R tr, S[j]? = some R → R.trans = some tr →
      G b j = (b.1 + (pathOf sp b.2 (sp.exec tr j (view sp b.2 (j - 1))) j).length +
        (sp.exec tr j (view sp b.2 (j - 1))).new.length + R.gd.length,
        b.2.apply j (sp.exec tr j (view sp b.2 (j - 1)))) ∧ sibOf j = sib tr)
    (hG0 : ∀ b j, (∀ R tr, S[j]? = some R → R.trans = some tr → False) → G b j = b ∧ sibOf j = 0) :
    (l.foldl (lazyReadStep sp sib S) ((m0, P0), 0)).2 ≤
      2 * (l.foldl G (0, P0)).1 + 2 * (l.map sibOf).sum := by
  have := fold_reads_gen sp sib S G sibOf hG1 hG0 l ((m0, P0), 0) (0, P0) rfl
  simp only at this
  omega

/-- The rerun reads at most twice what it reaches (`rerunReach`: a header and a
version for each node of a writer's path, a version for each node of gd(j);
`rerunReach` counts the new nodes too), and twice the follows outside the
paths. -/
theorem lazyReadsRun_reads (sp : Spec V T) (sib : T → Nat) (S : Stream V T) :
    (lazyReadsRun sp sib S).2 ≤ 2 * rerunReach sp S + 2 * sibReach sib S := by
  unfold lazyReadsRun rerunReach sibReach
  simp only
  apply fold_reads_gen'
  · intro b j R tr hS htr
    simp [hS, htr]
  · intro b j hn
    cases hS : S[j]? with
    | none => simp
    | some R =>
      cases htr : R.trans with
      | none => simp [htr]
      | some tr => exact absurd (hn R tr hS htr) id

theorem lazyReads_le (sp : Spec V T) (sib : T → Nat) (S : Stream V T) :
    lazyReads sp sib S ≤ sectionVersions S (lastSp S) + 2 + topHeaderReads sp S (lastSp S) +
      2 * rerunReach sp S + 2 * sibReach sib S := by
  unfold lazyReads
  have := lazyReadsRun_reads sp sib S
  omega

theorem lazyReads_run (sp : Spec V T) (al : Algo V T) (sib : T → Nat) (ts : List T)
    (hok : RunOK sp al ts) (hst : AlgOK sp al) :
    lazyReads sp sib (run sp al ts).S ≤ sectionVersions (run sp al ts).S (lastSp (run sp al ts).S) +
      2 + topHeaderReads sp (run sp al ts).S (lastSp (run sp al ts).S) +
      2 * ((sectionIdx (run sp al ts).S (lastSp (run sp al ts).S)).map (fun j =>
        (pathOf sp (run sp al (ts.take (j - 1))).P (changeAt sp al ts j) j).length +
          (changeAt sp al ts j).new.length)).sum +
      2 * (run sp al ts).D.length + 2 * sibReach sib (run sp al ts).S := by
  have h1 := lazyReads_le sp sib (run sp al ts).S
  have h2 := rerunReach_st hok hst (k := ts.length) (Nat.le_refl _)
  have h3 := sum_gd_eq_D hok hst (k := ts.length) (Nat.le_refl _)
  rw [st_length] at h2 h3
  rw [h2, sum_map_add] at h1
  rw [h3] at h1
  simp only [st] at h1
  omega

theorem lazyReads_height_dropJ (sp : Spec V T) (al : Algo V T) (sib : T → Nat) (ts : List T)
    (hok : RunOK sp al ts) (hst : AlgOK sp al)
    (htree0 : treeAt sp (run sp al []).P 0) (htree : TreeRunOK sp al ts)
    (w : V → Nat) (k : Nat → Nat) (hdrop : DropRunOKJ sp al w k ts)
    (H : Nat) (hH : ∀ t ≤ ts.length, LiveHeightLe sp (run sp al (ts.take t)).P t H root) :
    lazyReads sp sib (run sp al ts).S ≤ sectionVersions (run sp al ts).S (lastSp (run sp al ts).S) +
      2 + topHeaderReads sp (run sp al ts).S (lastSp (run sp al ts).S) +
      2 * ((sectionIdx (run sp al ts).S (lastSp (run sp al ts).S)).map (fun j =>
        (H + 1) * ((changeAt sp al ts j).new.length + (changeAt sp al ts j).adds.length +
          (changeAt sp al ts j).touch.length +
          ((changeAt sp al ts j).adds.map (fun a => w a.2)).sum + k j) +
        (changeAt sp al ts j).new.length)).sum +
      2 * (run sp al ts).D.length + 2 * sibReach sib (run sp al ts).S := by
  have h := lazyReads_run sp al sib ts hok hst
  have hle := sum_map_le (sectionIdx (run sp al ts).S (lastSp (run sp al ts).S))
    (fun j => (pathOf sp (run sp al (ts.take (j - 1))).P (changeAt sp al ts j) j).length +
      (changeAt sp al ts j).new.length)
    (fun j => (H + 1) * ((changeAt sp al ts j).new.length + (changeAt sp al ts j).adds.length +
          (changeAt sp al ts j).touch.length +
          ((changeAt sp al ts j).adds.map (fun a => w a.2)).sum + k j) +
        (changeAt sp al ts j).new.length) (by
      intro j hj
      simp only [sectionIdx, List.mem_range'_1, run_length] at hj
      obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      have hj' : j' < ts.length := by omega
      have htj : treeAt sp (run sp al (ts.take j')).P j' := by
        rcases Nat.eq_zero_or_pos j' with h0' | hpos
        · subst h0'; rw [List.take_zero]; exact htree0
        · obtain ⟨j'', hj''⟩ : ∃ j'', j' = j'' + 1 := ⟨j' - 1, by omega⟩
          subst hj''
          exact htree j'' (by omega)
      have hinvj := inv_st sp al ts hok hst j' (by omega)
      obtain ⟨nr, hnr⟩ := Option.isSome_iff_exists.mp hinvj.rootIn
      have hp := pathOf_count_height (P := (st sp al ts j').P) (j := j' + 1)
        (by simpa [st] using htj) hnr (by simpa [st] using hH j' (by omega))
        (changeAt sp al ts (j' + 1))
      have hr := removedAt_le_J sp w _ _ _ _ (hdrop j' hj')
      rw [changeAt_succ j' hj'] at hp ⊢
      simp only [Nat.add_sub_cancel, chg, st] at hp hr ⊢
      have := Nat.mul_le_mul_left (H + 1)
        (show (sp.exec ts[j'] (j' + 1) (view sp (run sp al (List.take j' ts)).P j')).new.length +
            (sp.exec ts[j'] (j' + 1) (view sp (run sp al (List.take j' ts)).P j')).adds.length +
            (sp.exec ts[j'] (j' + 1) (view sp (run sp al (List.take j' ts)).P j')).touch.length +
            (removedAt sp (run sp al (List.take j' ts)).P
              (sp.exec ts[j'] (j' + 1) (view sp (run sp al (List.take j' ts)).P j')) (j' + 1)).length ≤
          (sp.exec ts[j'] (j' + 1) (view sp (run sp al (List.take j' ts)).P j')).new.length +
            (sp.exec ts[j'] (j' + 1) (view sp (run sp al (List.take j' ts)).P j')).adds.length +
            (sp.exec ts[j'] (j' + 1) (view sp (run sp al (List.take j' ts)).P j')).touch.length +
            ((sp.exec ts[j'] (j' + 1) (view sp (run sp al (List.take j' ts)).P j')).adds.map
              (fun a => w a.2)).sum + k (j' + 1) by
          omega)
      omega)
  omega

end SIS
