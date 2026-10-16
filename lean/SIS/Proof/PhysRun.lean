/-
Proofs about the physical layer, part 8: facts of the run for the rerun of a
lazy startup (bergdb item 001, WP L3).
-/
import SIS.Proof.PhysWriter

set_option linter.unusedSectionVars false

namespace SIS

variable {V T : Type} [DecidableEq V]

section Run

variable (sp : Spec V T) (al : Algo V T) (ts : List T)

theorem versionAt_prefix {S S' : Stream V T} (h : S <+: S') {r : Nat} {y : NodeId}
    {w : Version V} (hw : S.versionAt r y = some w) : S'.versionAt r y = some w := by
  obtain ⟨l, hl⟩ := h
  rw [← hl]
  obtain ⟨R, hR, -, -⟩ := versionAt_spec hw
  obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.mp hR
  rw [versionAt_append_left hlt]; exact hw

/-- A node of D after T(K) stays in D, with the same d(x), until it is written. -/
theorem D_later (hok : RunOK sp al ts) (hst : AlgOK sp al) {K : Nat} {y : NodeId} {d : Nat}
    (hd : (y, d) ∈ (st sp al ts K).D) :
    ∀ k, K ≤ k → k ≤ ts.length → (y, d) ∈ (st sp al ts k).D ∨
      ∃ r w, K < r ∧ r ≤ k ∧ (st sp al ts k).S.versionAt r y = some w := by
  intro k
  induction k with
  | zero => intro hK _; have : K = 0 := by omega
            subst this; exact Or.inl hd
  | succ k ih =>
    intro hK hk
    rcases Nat.lt_or_ge K (k + 1) with hlt | hge
    · have hinv := inv_st sp al ts hok hst k (by omega)
      have hstep : StepOK sp (st sp al ts k).P (k + 1) (parts sp al (st sp al ts k) ts[k]).c := by
        have := hok.2 k (by omega)
        rw [parts_c, hinv.len]
        simpa [st] using this
      have hpre : (st sp al ts k).S <+: (st sp al ts (k + 1)).S :=
        st_S_prefix sp al ts (by omega) (by omega)
      rcases ih (by omega) (by omega) with h | ⟨r, w, h1, h2, h3⟩
      · -- in D before the step: taken (written now) or still in D
        have hD1 : (y, d) ∈ (parts sp al (st sp al ts k) ts[k]).D1 :=
          (step_D1_mem sp al _ _ hinv.len _).mpr (Or.inl h)
        by_cases ht : y ∈ (parts sp al (st sp al ts k) ts[k]).taken
        · right
          have hyi := step_taken_index sp al _ _ hinv ht
          obtain ⟨w, hw, hwy⟩ := (step_written_iff sp al _ _ hinv hstep y).mpr (Or.inr ht)
          refine ⟨k + 1, w, hlt, Nat.le_refl _, ?_⟩
          rw [st_S_succ sp al ts (by omega)]
          have := versionAt_snoc_self (st sp al ts k).S (parts sp al (st sp al ts k) ts[k]).R y
          rw [hinv.len] at this
          rw [this, parts_R]
          exact find?_node_of_mem (step_vs_nodup sp al _ _ hinv hstep) hw hwy
        · left
          rw [st_succ sp al ts (by omega), step_D, (step_r7_shape sp al _ _ hinv.len).1]
          apply List.mem_append_left
          refine (step_D2_mem sp al _ _ _).mpr ⟨hD1, ?_⟩
          simp only
          apply Nat.lt_of_not_le
          intro hle
          exact ht ((step_taken_mem sp al _ _ y).mpr ⟨d, hD1, hle⟩)
      · exact Or.inr ⟨r, w, h1, by omega, versionAt_prefix hpre h3⟩
    · have : K = k + 1 := by omega
      subst this; exact Or.inl hd

/-- A data node, or a root child of a virtual root, gets no entries after T(K)
once it exists. -/
theorem fixed_after (hok : RunOK sp al ts) (hst : AlgOK sp al) {K : Nat} {y : NodeId} {n : Node V}
    (hn : (st sp al ts K).P.get? y = some n)
    (hfix : n.isData = true ∨ (sp.virt = true ∧ y ≠ root ∧ sp.topLevel ≤ n.level)) :
    ∀ k, K ≤ k → k ≤ ts.length → (st sp al ts k).P.get? y = some n := by
  intro k
  induction k with
  | zero => intro hK _; have : K = 0 := by omega
            subst this; exact hn
  | succ k ih =>
    intro hK hk
    rcases Nat.lt_or_ge K (k + 1) with hlt | hge
    · have hinv := inv_st sp al ts hok hst k (by omega)
      have hstep : StepOK sp (st sp al ts k).P (k + 1) (parts sp al (st sp al ts k) ts[k]).c := by
        have := hok.2 k (by omega)
        rw [parts_c, hinv.len]
        simpa [st] using this
      have h0 := ih (by omega) (by omega)
      rw [st_succ sp al ts (by omega), step_P, step_P_old sp al _ _ hinv.len h0]
      have hadds : addsFor (parts sp al (st sp al ts k) ts[k]).c (k + 1) y = [] := by
        simp only [addsFor, List.map_eq_nil_iff, List.filter_eq_nil_iff, beq_iff_eq]
        intro a ha hay
        rcases hfix with hd | ⟨hv, hyr, hlev⟩
        · have := hstep.dataFixed a ha n (by rw [hay]; exact h0)
          rw [hd] at this; cases this
        · have := (hstep.virt hv).topFixed a ha n (by rw [hay]; exact h0) (by rw [hay]; exact hyr)
          omega
      rw [hadds, List.append_nil]
    · have : K = k + 1 := by omega
      subst this; exact hn

/-- The facts of the run at time K, for the final state after T(k). -/
theorem kctx_st (hok : RunOK sp al ts) (hj : al.stillDirty = javaTest sp) {K k : Nat}
    (hKk : K ≤ k) (hk : k ≤ ts.length) : KCtx sp (st sp al ts k) (st sp al ts K) K := by
  have hst : AlgOK sp al := algOK_of sp al (Or.inl hj)
  have hinvK := inv_st sp al ts hok hst K (by omega)
  have hinvk := inv_st sp al ts hok hst k hk
  have hpre : (st sp al ts K).S <+: (st sp al ts k).S := st_S_prefix sp al ts hKk hk
  have hls : LiveSub sp := hok.1.liveSub
  refine ⟨hinvK, cleanFresh_st sp al ts hok hj K (by omega), ?_, st_grow sp al ts hok hst hKk hk,
    ?_, ?_, ?_⟩
  · rw [List.prefix_iff_eq_take.mp hpre, hinvK.len]
  · intro y d hd hds
    rcases D_later sp al ts hok hst hd k hKk hk with h | ⟨r, w, h1, -, h3⟩
    · exfalso
      have := (sectionD_mem (hinvk.inv1 ▸ h)).1
      omega
    · exact ⟨r, w, h1, h3⟩
  · intro y d hd hds
    obtain ⟨-, hlt, R, hR, hy⟩ := sectionD_mem (hinvK.inv1 ▸ hd)
    refine ⟨R, ?_, hy, by rw [hinvK.len] at hlt; omega⟩
    obtain ⟨l, hl⟩ := hpre
    rw [← hl, List.getElem?_append_left (by omega)]
    exact hR
  · intro y n hn hkl hyr ⟨t, ht, hr⟩ e he
    have hrK : reachable sp (st sp al ts K).P t y = true := by
      rw [← reachable_grow hls hinvK.ptrs hinvK.rootIn (st_grow sp al ts hok hst hKk hk) ht y]
      exact hr
    obtain ⟨nK, hnK⟩ := Option.isSome_iff_exists.mp (Reach.isSome ((reachable_iff _ _ _ _).mp hrK))
    obtain ⟨n', hn', hl', hd', -⟩ := st_grow sp al ts hok hst hKk hk y nK hnK
    rw [hn, Option.some.injEq] at hn'
    subst hn'
    have hfix : nK.isData = true ∨ (sp.virt = true ∧ y ≠ root ∧ sp.topLevel ≤ nK.level) := by
      unfold isKeyLevel at hkl
      cases hdk : nK.isData
      · right
        rw [hd', hdk] at hkl
        simp only [Bool.not_false, Bool.true_and, Bool.or_eq_false_iff, Bool.not_eq_eq_eq_not,
          decide_eq_false_iff_not, Nat.not_lt] at hkl
        exact ⟨hkl.1, hyr.resolve_left (by rw [hd', hdk]; simp), by rw [← hl']; exact hkl.2⟩
      · left; rfl
    have hsame := fixed_after sp al ts hok hst hnK hfix k hKk hk
    rw [hn, Option.some.injEq] at hsame
    subst hsame
    exact hinvK.times y _ hnK e he

end Run

end SIS
