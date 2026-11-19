/- Reachability bookkeeping for the read-prefix invariant. -/
import Contract.Proof.OldReadsSection
namespace Contract.OldReads
open SIS
variable {V T : Type} [DecidableEq V]
variable {sp : Spec V T} {al : Algo V T} {ts : List T}

theorem old_version_exists (hok : RunOK sp al ts) (hst : AlgOK sp al)
    {k a r x : Nat} (hk : k ≤ ts.length) (hak : a ≤ k) {w : Version V}
    (hw : (st sp al ts k).S.versionAt r x = some w) (hra : r ≤ a) :
    ((st sp al ts a).P.get? x).isSome := by
  cases hx : (st sp al ts a).P.get? x with
  | some n => simp
  | none =>
    have := st_version_after hok hst hak hk hx hw
    omega

theorem reach_back_in_final (hok : RunOK sp al ts) (hst : AlgOK sp al)
    {k a t x : Nat} (hk : k ≤ ts.length) (hat : a ≤ t) (htk : t ≤ k)
    (hr : reachable sp (st sp al ts k).P t x = true)
    (hex : ((st sp al ts a).P.get? x).isSome) :
    reachable sp (st sp al ts k).P a x = true := by
  have h := reach_back_st hok hst (j1 := a) hk (t-a) t (by omega) htk x hr hex
  have hinva := inv_st sp al ts hok hst a (by omega)
  rw [reachable_grow hok.1.liveSub hinva.ptrs hinva.rootIn
    (st_grow sp al ts hok hst (by omega : a ≤ k) hk) (Nat.le_refl a)]
  exact h

/-- Even if x later retires, an old node appearing in x's later live view
    was already reachable at cutoff a. A new entry witnesses a current x;
    without a new entry the live view is unchanged. -/
theorem live_child_back (hok : RunOK sp al ts) (hst : AlgOK sp al)
    {k a x y : Nat} (hk : k ≤ ts.length) (hak : a ≤ k) {nx : Node V}
    (hnx : (st sp al ts k).P.get? x = some nx)
    (hrx : reachable sp (st sp al ts k).P a x = true)
    (hey : ((st sp al ts a).P.get? y).isSome) :
    ∀ p, a ≤ p → p ≤ k → y ∈ sp.live (nx.hist.upTo p) →
      reachable sp (st sp al ts k).P a y = true := by
  have hinv := inv_st sp al ts hok hst k hk
  intro p
  induction p with
  | zero =>
    intro ha _ hy
    have heq : a = 0 := by omega
    subst a
    exact (hinv.reach_child hok.1.liveSub hnx hrx hy).1
  | succ p ih =>
    intro hap hpk hy
    by_cases heq : a = p+1
    · subst a
      exact (hinv.reach_child hok.1.liveSub hnx hrx hy).1
    by_cases he : ∃ e ∈ nx.hist, e.time = p+1
    · obtain ⟨e, he, het⟩ := he
      have hrp := hinv.er x nx hnx e he
      rw [het] at hrp
      have hry := (hinv.reach_child hok.1.liveSub hnx hrp hy).1
      exact reach_back_in_final hok hst hk hap hpk hry hey
    · have hh : nx.hist.upTo p = nx.hist.upTo (p+1) :=
        upTo_eq_of_none_between nx.hist (by omega) (fun e hem hb =>
          he ⟨e, hem, by omega⟩)
      rw [← hh] at hy
      exact ih (by omega) (by omega) hy

/-- A written index node already existed at the final startup time, even
    when its version is in the startup section. -/
theorem index_exists_at_startup (hok : RunOK sp al ts) (hst : AlgOK sp al)
    {k r x : Nat} (hk : k ≤ ts.length) {w : Version V}
    (hw : (st sp al ts k).S.versionAt r x = some w) (hdata : w.isData = false) :
    ((st sp al ts (lastSp (st sp al ts k).S)).P.get? x).isSome := by
  have hinvk := inv_st sp al ts hok hst k hk
  have hsk : lastSp (st sp al ts k).S ≤ k := by have := hinvk.spLt; omega
  by_cases hr : r ≤ lastSp (st sp al ts k).S
  · exact old_version_exists hok hst hk hsk hw hr
  have hrk : r ≤ k := by
    have := versionAt_lt_length hw
    rw [hinvk.len] at this
    omega
  obtain ⟨i, rfl⟩ : ∃ i, r = i+1 := ⟨r-1, by omega⟩
  have hi : i < ts.length := by omega
  have hinvi := inv_st sp al ts hok hst i (by omega)
  have hstep : StepOK sp (st sp al ts i).P (i+1)
      (parts sp al (st sp al ts i) ts[i]).c := by
    have h := hok.2 i hi
    rw [parts_c, hinvi.len]
    simpa [st] using h
  obtain ⟨R, hR, hwR, _⟩ := versionAt_spec hw
  rw [st_rec hok hst (i := i) (j := k) (by omega) hk] at hR
  have hReq := Option.some.inj hR
  rw [← hReq, parts_R] at hwR
  have hnode := (hinvk.version_node hw).1
  obtain ⟨nx, _, hnx, _, _, _, _, hwd, _⟩ :=
    built_mem (step_vs_built sp al (st sp al ts i) ts[i] hinvi.len) hwR
  rw [hnode] at hnx
  have hx := (step_written_iff sp al (st sp al ts i) ts[i] hinvi hstep x).mp ⟨w, hwR, hnode⟩
  have ht : x ∈ (parts sp al (st sp al ts i) ts[i]).taken := by
    rcases hx with hx | hx
    · obtain ⟨_, nx', hnx', hd'⟩ := step_dataIds_spec sp al _ _ hinvi hstep hx
      rw [hnx] at hnx'
      cases hnx'
      rw [← hwd, hdata] at hd'
      cases hd'
    · exact hx
  obtain ⟨d, hd, hds⟩ := step_taken_inD hinvi ht
  have hs : (parts sp al (st sp al ts i) ts[i]).s = lastSp (st sp al ts (i+1)).S := by
    rw [st_succ sp al ts hi, step_S, step_lastSp]
  have hm := lastSp_st_mono hok hst (i := i+1) (j := k) (by omega) hk
  have hdcut : d ≤ lastSp (st sp al ts k).S := by omega
  have hDcut := st_D_persist hok hst (i := lastSp (st sp al ts k).S)
    (j := i) (by omega) (by omega) hd hdcut
  have hinvs := inv_st sp al ts hok hst (lastSp (st sp al ts k).S) (by omega)
  exact isSome_of_isIndex (hinvs.dIndex _ hDcut)

end Contract.OldReads
