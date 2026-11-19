/- bergdb 030-24: I0 and I5 hold in every reached state (`sectionLatest_st`,
   `sectionRefsGood_st`). -/
import Contract.Proof.OldReadsDefs
import SIS.Proof.BoundT4Debt

namespace Contract.OldReads
open SIS
variable {V T : Type} [DecidableEq V]
variable {sp : Spec V T} {al : Algo V T} {ts : List T}

theorem dirty_latest_le_mark (hok : RunOK sp al ts) (hst : AlgOK sp al)
    {k x d : Nat} (hk : k ≤ ts.length) (hD : (x,d) ∈ (st sp al ts k).D)
    {w : Version V} (hw : (st sp al ts k).S.lv x = some w) : w.recNo ≤ d := by
  apply Classical.byContradiction
  intro h
  have hinv := inv_st sp al ts hok hst k hk
  have hvat := hinv.lv_at hw
  have hle : w.recNo ≤ k := by
    have := versionAt_lt_length hvat
    rw [hinv.len] at this
    omega
  have hn := st_D_not_written hok hst hk hD (by omega : d < w.recNo) hle
  rw [hvat] at hn
  cases hn

/-- A second version of a node can only be written once the startup position
    has reached the record of the first. New data cannot be that second write. -/
theorem two_versions_startup (hok : RunOK sp al ts) (hst : AlgOK sp al)
    {k r r' x : Nat} (hk : k ≤ ts.length) {u w : Version V}
    (hu : (st sp al ts k).S.versionAt r x = some u)
    (hw : (st sp al ts k).S.versionAt r' x = some w) (hrr : r < r') :
    r ≤ lastSp (st sp al ts k).S := by
  have hinvk := inv_st sp al ts hok hst k hk
  have hrk : r' ≤ k := by
    have := versionAt_lt_length hw
    rw [hinvk.len] at this
    omega
  obtain ⟨i, rfl⟩ : ∃ i, r' = i+1 := ⟨r'-1, by omega⟩
  have hi : i < ts.length := by omega
  have hinvi := inv_st sp al ts hok hst i (by omega)
  have hstep : StepOK sp (st sp al ts i).P (i+1)
      (parts sp al (st sp al ts i) ts[i]).c := by
    have h := hok.2 i hi
    rw [parts_c, hinvi.len]
    simpa [st] using h
  have hup : (st sp al ts i).S.versionAt r x = some u := by
    have h := versionAt_of_prefix (st_S_prefix sp al ts (by omega : i ≤ k) hk)
      (by rw [hinvi.len]; omega : r < (st sp al ts i).S.length) x
    rw [hu] at h
    exact h.symm
  obtain ⟨_, _, n, hn, _⟩ := hinvi.version_node hup
  obtain ⟨R, hR, hwR, _⟩ := versionAt_spec hw
  rw [st_rec hok hst (i := i) (j := k) (by omega) hk] at hR
  have hReq := Option.some.inj hR
  rw [← hReq, parts_R] at hwR
  have hx := (step_written_iff sp al (st sp al ts i) ts[i] hinvi hstep x).mp
    ⟨w, hwR, (hinvk.version_node hw).1⟩
  have ht : x ∈ (parts sp al (st sp al ts i) ts[i]).taken := by
    rcases hx with hx | hx
    · have hnone := (step_dataIds_spec sp al _ _ hinvi hstep hx).1
      rw [hn] at hnone
      cases hnone
    · exact hx
  obtain ⟨d, hd, hds⟩ := step_taken_inD hinvi ht
  obtain ⟨v, hv, hrv⟩ := hinvi.le_lv hup
  have hvd := dirty_latest_le_mark hok hst (by omega : i ≤ ts.length) hd hv
  have hs : (parts sp al (st sp al ts i) ts[i]).s = lastSp (st sp al ts (i+1)).S := by
    rw [st_succ sp al ts hi, step_S, step_lastSp]
  have hm := lastSp_st_mono hok hst (i := i+1) (j := k) (by omega) hk
  omega

/-- I0 is a theorem of the kept algorithm, for any RunOK/AlgOK run. -/
theorem sectionLatest_st (hok : RunOK sp al ts) (hst : AlgOK sp al)
    {k : Nat} (hk : k ≤ ts.length) : SectionLatest (st sp al ts k) := by
  intro r x w hw hr
  have hinv := inv_st sp al ts hok hst k hk
  obtain ⟨u, hu, hru⟩ := hinv.le_lv hw
  by_cases heq : u.recNo = r
  · have hua := hinv.lv_at hu
    rw [heq, hw] at hua
    have := Option.some.inj hua
    subst this
    exact hu
  · have hlt : r < u.recNo := by omega
    have := two_versions_startup hok hst hk hw (hinv.lv_at hu) hlt
    omega

/-- I5 follows from the exact put-back guard, bottom-up serialization, and
    the old clean-good invariant at the time the parent was written. -/
theorem sectionRefsGood_st (hok : RunOK sp al ts) (hj : al.stillDirty = javaTest sp)
    {k : Nat} (hk : k ≤ ts.length) : SectionRefsGood sp (st sp al ts k) := by
  have hst : AlgOK sp al := algOK_of sp al (Or.inl hj)
  intro r x w hw hrs hguard y a u ha has hus hyr z hz
  have hinvk := inv_st sp al ts hok hst k hk
  have hrk : r ≤ k := by
    have := versionAt_lt_length hw
    rw [hinvk.len] at this
    omega
  obtain ⟨i, rfl⟩ : ∃ i, r = i+1 := ⟨r-1, by omega⟩
  have hi : i < ts.length := by omega
  have hinvi := inv_st sp al ts hok hst i (by omega)
  have hinvr := inv_st sp al ts hok hst (i+1) (by omega)
  have hstep : StepOK sp (st sp al ts i).P (i+1)
      (parts sp al (st sp al ts i) ts[i]).c := by
    have h := hok.2 i hi
    rw [parts_c, hinvi.len]
    simpa [st] using h
  have hP : (parts sp al (st sp al ts i) ts[i]).P = (st sp al ts (i+1)).P := by
    rw [st_succ sp al ts hi]; rfl
  have hS : Snew sp al (st sp al ts i) ts[i] = (st sp al ts (i+1)).S := by
    rw [st_succ sp al ts hi, step_S]
  have hD : (parts sp al (st sp al ts i) ts[i]).r7.1 = (st sp al ts (i+1)).D := by
    rw [st_succ sp al ts hi]; rfl
  have hpre := st_S_prefix sp al ts (by omega : i+1 ≤ k) hk
  have hwr : (st sp al ts (i+1)).S.versionAt (i+1) x = some w := by
    have h := versionAt_of_prefix hpre
      (by rw [hinvr.len]; omega : i+1 < (st sp al ts (i+1)).S.length) x
    rw [hw] at h
    exact h.symm
  obtain ⟨_, _, nx, hnx, hwh, _, _⟩ := hinvr.version_node hwr
  have hwhole : w.hist = nx.hist := by
    rw [hwh, upTo_of_forall _ _ (hinvr.times x nx hnx)]
  have hyp := hinvr.ref_mem_pointees hwr ha
  have hyn : y ∈ pointees sp nx.hist := by rw [← hwhole]; exact hyp
  have hidx : nx.isData = false := by
    cases hd : nx.isData
    · rfl
    · obtain ⟨e, he, hye⟩ := (mem_pointees sp nx.hist y).mp hyn
      rw [hinvr.data x nx hnx hd e he] at hye
      cases hye
  obtain ⟨R, hR, hwR, _⟩ := versionAt_spec hw
  have hRstep := st_rec hok hst (i := i) (j := k) (by omega) hk
  rw [hRstep] at hR
  have hReq := Option.some.inj hR
  rw [← hReq, parts_R] at hwR
  have hx := (step_written_iff sp al (st sp al ts i) ts[i] hinvi hstep x).mp
    ⟨w, hwR, (hinvk.version_node hw).1⟩
  have ht : x ∈ (parts sp al (st sp al ts i) ts[i]).taken := by
    rcases hx with hx | hx
    · obtain ⟨_, n', hn', hd'⟩ := step_dataIds_spec sp al _ _ hinvi hstep hx
      rw [hP, hnx] at hn'
      cases hn'
      rw [hidx] at hd'
      cases hd'
    · exact hx
  have hn7 : x ∉ (parts sp al (st sp al ts i) ts[i]).r7.2 := by
    intro hx7
    have hgd : x ∈ (parts sp al (st sp al ts i) ts[i]).R.gd := by
      rw [parts_R]; exact List.mem_append.mpr (Or.inr hx7)
    have hsec := mem_sectionD_of hrs
      (by rw [hinvk.len]; omega : i+1 < (st sp al ts k).S.length) hRstep hgd
    apply hguard
    rw [hinvk.inv1]
    exact hsec
  have hnyD : inD (st sp al ts (i+1)).D y = false := by
    cases hyD : inD (st sp al ts (i+1)).D y
    · rfl
    · exfalso
      apply hn7
      apply (step_java_pointee sp al (st sp al ts i) ts[i] hj hok.1 hinvi hstep ht
        (by rw [hP]; exact hnx)).mpr
      exact ⟨y, hyn, by rw [hD]; exact hyD⟩
  obtain ⟨vx, hlvx, _, href⟩ := step_ref_lower sp al (st sp al ts i) ts[i] hinvi hstep ht
  have hsp_r : lastSp (st sp al ts (i+1)).S < i+1 := by
    have := hinvr.spLt
    omega
  have hlw := sectionLatest_st hok hst (k := i+1) (by omega) (i+1) x w hwr hsp_r
  rw [hS, hlw] at hlvx
  have hvxw := Option.some.inj hlvx
  subst vx
  have hpf := step_pfacts sp al (st sp al ts i) ts[i] hok.1 hinvi hstep
  have hlt := pointee_lvl_lt sp hpf (by rw [hP]; exact hnx) hyn
  have hafresh := href y hyp hlt
  rw [hS, ha] at hafresh
  obtain ⟨w0, hw0⟩ := hinvr.ref_versionAt hwr ha
  have hyw := hinvr.written_of_versionAt hw0
  have hgrow := st_grow sp al ts hok hst (by omega : i+1 ≤ k) hk
  have hury : reachable sp (st sp al ts (i+1)).P u y = true := by
    rw [← reachable_grow hok.1.liveSub hinvr.ptrs hinvr.rootIn hgrow (by omega) y]
    exact hyr
  obtain ⟨v, hv, hgood⟩ := hinvr.clean_good hok.1.liveSub hnyD hyw (by omega : u ≤ i+1) hury
  rw [hv] at hafresh
  have hav : a = v.recNo := Option.some.inj hafresh
  have hvat := hinvr.lv_at hv
  rw [← hav] at hvat
  have hvatk := versionAt_prefix hpre hvat
  rw [hz] at hvatk
  have hvz := Option.some.inj hvatk
  subst z
  exact good_mono' sp (sext_of_prefix hpre) hgrow (by omega) hgood

end Contract.OldReads
