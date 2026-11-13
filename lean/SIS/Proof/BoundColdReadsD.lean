/-
Proofs for a cold start's reads without the |D| term (bergdb item 007;
SIS/BoundColdReads.lean). Added 2026-11-13.

With BergDB's test, TREE and `LiveAppend`, every node of gd(j) has a canonical
object once T(j)'s change is applied in the rerun (`MemInv.coverGd`, as in
SIS/Proof/BoundColdD.lean), so `canonicalNode` reads nothing.
-/
import SIS.Proof.BoundColdReads
import SIS.Proof.BoundColdD

set_option linter.unusedSectionVars false

namespace SIS

variable {V T : Type} [DecidableEq V]

theorem lazyReadStep_fst (sp : Spec V T) (sib : T → Nat) (S : Stream V T)
    (acc : (Mem V × Struct V) × Nat) (j : Nat) :
    (lazyReadStep sp sib S acc j).1 = rerunStep sp S acc.1 j := by
  cases hS : S[j]? with
  | none => simp [lazyReadStep, rerunStep, hS]
  | some R =>
    cases htr : R.trans with
    | none => simp [lazyReadStep, rerunStep, hS, htr]
    | some tr =>
      rw [rerunStep_eq sp S acc.1 hS htr]
      simp only [lazyReadStep, hS, htr, foldl_pair_fst]
      rfl

theorem foldl_gd_reads_zero (sp : Spec V T) (S : Stream V T) :
    ∀ (L : List NodeId) (m : Mem V) (n : Nat), (∀ x ∈ L, m.canonicalOf x ≠ none) →
      (L.foldl (fun (a : Mem V × Nat) x =>
        (a.1.canonicalNode sp S x, a.2 + a.1.canonicalNodeReads S x)) (m, n)).2 = n := by
  intro L
  induction L with
  | nil => intro m n _; rfl
  | cons x L ih =>
    intro m n hL
    simp only [List.foldl_cons]
    have hx := hL x List.mem_cons_self
    have h0 : m.canonicalNodeReads S x = 0 := by
      unfold Mem.canonicalNodeReads
      cases hc : m.canonicalOf x with
      | none => exact absurd hc hx
      | some _ => rfl
    rw [canonicalNode_noop sp S m x hx, h0, Nat.add_zero]
    exact ih m n (fun y hy => hL y (List.mem_cons_of_mem x hy))

theorem reads_aux {a x y s p : Nat} (h : x ≤ 0 + 2 * p) (hy : y = 0) :
    a + x + y + 2 * s ≤ a + 2 * p + 2 * s := by omega

/-- One counted transaction of the rerun when every node of gd(j) has a
canonical object after the change: at most 2 reads for each node of its
writer's paths, and 2 `sib tr`. -/
theorem lazyReadStep_spec0 (sp : Spec V T) (sib : T → Nat) (S : Stream V T)
    (acc : (Mem V × Struct V) × Nat) {j : Nat} {R : Record V T} {tr : T}
    (hS : S[j]? = some R) (htr : R.trans = some tr)
    (hcov : ∀ x ∈ R.gd,
      ((((pathOf sp acc.1.2 (sp.exec tr j (view sp acc.1.2 (j - 1))) j).mergeSort
        (fun a b => decide (lev acc.1.2 b ≤ lev acc.1.2 a))).foldl
        (Mem.reachOnPath sp S acc.1.2 j (pathOf sp acc.1.2 (sp.exec tr j (view sp acc.1.2 (j - 1))) j))
          acc.1.1).applyChange sp acc.1.2 j (sp.exec tr j (view sp acc.1.2 (j - 1)))).canonicalOf x ≠
        none) :
    (lazyReadStep sp sib S acc j).2 ≤ acc.2 +
      2 * (pathOf sp acc.1.2 (sp.exec tr j (view sp acc.1.2 (j - 1))) j).length + 2 * sib tr := by
  unfold lazyReadStep
  simp only [hS, htr]
  apply reads_aux
  · exact Nat.le_trans (foldl_pair_snd_le _ _ 2 (fun m x => Mem.reachOnPathReads_le sp S _ j _ m x)
      _ _ 0) (by rw [List.length_mergeSort]; omega)
  · apply foldl_gd_reads_zero
    intro x hx
    rw [foldl_pair_fst]
    exact hcov x hx

section Run

variable {sp : Spec V T} {al : Algo V T} {ts : List T}

theorem readsRun_noD (hok : RunOK sp al ts) (hph : PhysRunOK sp al ts) (sib : T → Nat)
    (hj : al.stillDirty = javaTest sp) {k : Nat} (hk : k ≤ ts.length) {m0 : Mem V} {P0 : Struct V}
    (hm0 : MemInv sp (st sp al ts k) (lastSp (st sp al ts k).S) m0)
    (hP0 : SameNodes P0 (st sp al ts (lastSp (st sp al ts k).S)).P) :
    ((sectionIdx (st sp al ts k).S (lastSp (st sp al ts k).S)).foldl
      (lazyReadStep sp sib (st sp al ts k).S) ((m0, P0), 0)).2 ≤
      2 * ((sectionIdx (st sp al ts k).S (lastSp (st sp al ts k).S)).map (fun j =>
        (pathOf sp (st sp al ts (j - 1)).P (changeAt sp al ts j) j).length)).sum +
      2 * sibReach sib (st sp al ts k).S := by
  have hst : AlgOK sp al := algOK_of sp al (Or.inl hj)
  have hinv := inv_st sp al ts hok hst k hk
  have hsk : lastSp (st sp al ts k).S ≤ k := by have := hinv.spLt; omega
  unfold sibReach
  generalize hs : lastSp (st sp al ts k).S = s at hm0 hP0 hsk
  have hidx : sectionIdx (st sp al ts k).S s = List.range' (s + 1) (k - s) := by
    simp [sectionIdx, hinv.len]
  rw [hidx]
  have key : ∀ n, n ≤ k - s →
      MemInv sp (st sp al ts k) (s + n)
          ((List.range' (s + 1) n).foldl (lazyReadStep sp sib (st sp al ts k).S) ((m0, P0), 0)).1.1 ∧
        SameNodes ((List.range' (s + 1) n).foldl (lazyReadStep sp sib (st sp al ts k).S)
          ((m0, P0), 0)).1.2 (st sp al ts (s + n)).P ∧
        ((List.range' (s + 1) n).foldl (lazyReadStep sp sib (st sp al ts k).S) ((m0, P0), 0)).2 ≤
          2 * ((List.range' (s + 1) n).map (fun j =>
            (pathOf sp (st sp al ts (j - 1)).P (changeAt sp al ts j) j).length)).sum +
          2 * ((List.range' (s + 1) n).map (fun j =>
            match (st sp al ts k).S[j]? with
            | some R => match R.trans with
              | some tr => sib tr
              | none => 0
            | none => 0)).sum := by
    intro n
    induction n with
    | zero => intro _; exact ⟨hm0, hP0, by simp⟩
    | succ n ih =>
      intro hn
      rw [List.range'_concat, List.foldl_append, List.map_append, List.sum_append,
        List.map_append, List.sum_append]
      simp only [List.foldl_cons, List.foldl_nil, Nat.one_mul, List.map_cons, List.map_nil,
        List.sum_cons, List.sum_nil, Nat.add_zero]
      obtain ⟨h1, h2, h3⟩ := ih (by omega)
      generalize hacc : (List.foldl (lazyReadStep sp sib (st sp al ts k).S) ((m0, P0), 0)
        (List.range' (s + 1) n)) = acc at h1 h2 h3 ⊢
      have hK : s + n < ts.length := by omega
      have hKk : s + n < k := by omega
      obtain ⟨g1, g2⟩ := rerunStep_ok hok hph hj hk (K := s + n) (acc := acc.1) (by rw [hs]; omega)
        hKk h1 h2
      rw [show s + 1 + n = s + n + 1 by omega, show s + (n + 1) = s + n + 1 by omega]
      rw [lazyReadStep_fst]
      refine ⟨g1, g2, ?_⟩
      have htr := st_trans sp al ts hok hst (j := s + n + 1) (k := k) (by omega) (by omega) hk
      simp only [Nat.add_sub_cancel] at htr
      obtain ⟨R, hR, hRt⟩ : ∃ R, (st sp al ts k).S[s + n + 1]? = some R ∧ R.trans = some ts[s + n] := by
        cases h : (st sp al ts k).S[s + n + 1]? with
        | none => rw [h] at htr; cases htr
        | some R => rw [h] at htr; exact ⟨R, rfl, htr⟩
      have hm2 := rerun_apply_ok hok hph hj hk hKk h1 h2 (tr := ts[s + n])
        (List.getElem?_eq_getElem hK)
      have hc := lazyReadStep_spec0 sp sib (st sp al ts k).S acc hR hRt (by
        intro x hx
        have := hm2.coverGd (s + n + 1) R x (by omega) (Nat.le_refl _) hR hx
        simpa using this)
      simp only [Nat.add_sub_cancel] at hc
      rw [h2.view (s + n), pathOf_congr h2] at hc
      rw [changeAt_succ (s + n) hK]
      simp only [chg, hR, hRt, Nat.add_sub_cancel] at hc ⊢
      omega
  exact (key (k - s) (Nat.le_refl _)).2.2

end Run

/-- A cold start's reads after a run, without D. -/
theorem lazyReads_run_noD (sp : Spec V T) (al : Algo V T) (sib : T → Nat) (ts : List T)
    (hok : RunOK sp al ts) (hla : LiveAppend sp) (htree : TreeRunOK sp al ts)
    (hj : al.stillDirty = javaTest sp) :
    lazyReads sp sib (run sp al ts).S ≤ sectionVersions (run sp al ts).S (lastSp (run sp al ts).S) +
      2 + topHeaderReads sp (run sp al ts).S (lastSp (run sp al ts).S) +
      2 * ((sectionIdx (run sp al ts).S (lastSp (run sp al ts).S)).map (fun j =>
        (pathOf sp (run sp al (ts.take (j - 1))).P (changeAt sp al ts j) j).length)).sum +
      2 * sibReach sib (run sp al ts).S := by
  have hph := physRunOK_of_tree hok hla htree
  have hst : AlgOK sp al := algOK_of sp al (Or.inl hj)
  have hk : ts.length ≤ ts.length := Nat.le_refl _
  have hctx := pctx_st hok hst hk
  have hsk : lastSp (st sp al ts ts.length).S ≤ ts.length := by have := hctx.inv.spLt; omega
  have hkS := kctx_st sp al ts hok hj hsk hk
  have h1 := readsRun_noD hok hph sib hj hk (hctx.base_ok hkS) (base_sameNodes sp al ts hok hst hk)
  rw [st_length] at h1
  unfold lazyReads lazyReadsRun
  rw [lazyMemBase_eq]
  simp only [st] at h1
  omega

/-- A cold start's reads after a run, without D, by height, with `DropRunOKJ`. -/
theorem lazyReads_height_noD (sp : Spec V T) (al : Algo V T) (sib : T → Nat) (ts : List T)
    (hok : RunOK sp al ts) (hla : LiveAppend sp) (hj : al.stillDirty = javaTest sp)
    (htree0 : treeAt sp (run sp al []).P 0) (htree : TreeRunOK sp al ts)
    (w : V → Nat) (k : Nat → Nat) (hdrop : DropRunOKJ sp al w k ts)
    (H : Nat) (hH : ∀ t ≤ ts.length, LiveHeightLe sp (run sp al (ts.take t)).P t H root) :
    lazyReads sp sib (run sp al ts).S ≤ sectionVersions (run sp al ts).S (lastSp (run sp al ts).S) +
      2 + topHeaderReads sp (run sp al ts).S (lastSp (run sp al ts).S) +
      2 * ((sectionIdx (run sp al ts).S (lastSp (run sp al ts).S)).map (fun j =>
        (H + 1) * ((changeAt sp al ts j).new.length + (changeAt sp al ts j).adds.length +
          (changeAt sp al ts j).touch.length +
          ((changeAt sp al ts j).adds.map (fun a => w a.2)).sum + k j))).sum +
      2 * sibReach sib (run sp al ts).S := by
  have hst : AlgOK sp al := algOK_of sp al (Or.inl hj)
  have h := lazyReads_run_noD sp al sib ts hok hla htree hj
  have hle := sum_map_le (sectionIdx (run sp al ts).S (lastSp (run sp al ts).S))
    (fun j => (pathOf sp (run sp al (ts.take (j - 1))).P (changeAt sp al ts j) j).length)
    (fun j => (H + 1) * ((changeAt sp al ts j).new.length + (changeAt sp al ts j).adds.length +
          (changeAt sp al ts j).touch.length +
          ((changeAt sp al ts j).adds.map (fun a => w a.2)).sum + k j)) (by
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
