/- bergdb 030-24: I3, the pending-reference invariant (`pendingRefsFresh_st`);
   A6' enters only through `EvLogic.clean`. -/
import Contract.Proof.OldReadsReach
namespace Contract.OldReads
open SIS
variable {V T : Type} [DecidableEq V]
variable {sp : Spec V T} {al : Algo V T} {ts : List T}

theorem no_write_after_clean (hok : RunOK sp al ts) (hst : AlgOK sp al)
    {k j x : Nat} (hk : k ≤ ts.length) (_hjk : j ≤ k)
    (hsp : lastSp (st sp al ts k).S ≤ j)
    (hex : ((st sp al ts j).P.get? x).isSome) (hclean : inD (st sp al ts j).D x = false) :
    ∀ r, j < r → (st sp al ts k).S.versionAt r x = none := by
  intro r hjr
  cases hw : (st sp al ts k).S.versionAt r x with
  | none => rfl
  | some w =>
    exfalso
    have hinvk := inv_st sp al ts hok hst k hk
    have hrk : r ≤ k := by
      have := versionAt_lt_length hw
      rw [hinvk.len] at this; omega
    obtain ⟨i, rfl⟩ : ∃ i, r = i+1 := ⟨r-1, by omega⟩
    have hi : i < ts.length := by omega
    have hinvi := inv_st sp al ts hok hst i (by omega)
    have hstep : StepOK sp (st sp al ts i).P (i+1)
        (parts sp al (st sp al ts i) ts[i]).c := by
      have h := hok.2 i hi
      rw [parts_c, hinvi.len]; simpa [st] using h
    obtain ⟨n0, hn0⟩ := Option.isSome_iff_exists.mp hex
    obtain ⟨n, hn, _⟩ := st_grow sp al ts hok hst (by omega : j ≤ i) (by omega) x n0 hn0
    obtain ⟨R, hR, hwR, _⟩ := versionAt_spec hw
    rw [st_rec hok hst (i := i) (j := k) (by omega) hk] at hR
    have hReq := Option.some.inj hR
    rw [← hReq, parts_R] at hwR
    have hx := (step_written_iff sp al (st sp al ts i) ts[i] hinvi hstep x).mp
      ⟨w, hwR, (hinvk.version_node hw).1⟩
    have ht : x ∈ (parts sp al (st sp al ts i) ts[i]).taken := by
      rcases hx with hx | hx
      · have hnone := (step_dataIds_spec sp al _ _ hinvi hstep hx).1
        rw [hn] at hnone; cases hnone
      · exact hx
    obtain ⟨d, hd, hds⟩ := step_taken_inD hinvi ht
    have hs : (parts sp al (st sp al ts i) ts[i]).s = lastSp (st sp al ts (i+1)).S := by
      rw [st_succ sp al ts hi, step_S, step_lastSp]
    have hm := lastSp_st_mono hok hst (i := i+1) (j := k) (by omega) hk
    have hDj := st_D_persist hok hst (i := j) (j := i) (by omega) (by omega) hd (by omega)
    have : inD (st sp al ts j).D x = true := (inD_iff _ _).mpr ⟨d, hDj⟩
    rw [hclean] at this; cases this

theorem latest_in_prefix (hok : RunOK sp al ts) (hst : AlgOK sp al)
    {k j x : Nat} (hk : k ≤ ts.length) (hjk : j ≤ k) {w : Version V}
    (hw : (st sp al ts k).S.lv x = some w) (hwj : w.recNo ≤ j) :
    (st sp al ts j).S.lv x = some w := by
  have hinvk := inv_st sp al ts hok hst k hk
  have hinvj := inv_st sp al ts hok hst j (by omega)
  obtain ⟨r, hwr, hlast⟩ := (lv_eq_some_iff _ _ _).mp hw
  have hrec : w.recNo = r := (hinvk.version_node hwr).2.1
  have h := lv_of_prefix_none (st_S_prefix sp al ts hjk hk) (y := x)
    (fun r' hr' => hlast r' (by rw [hinvj.len] at hr'; omega))
  rw [hw] at h
  exact h.symm

theorem pendingRefsFresh_st (hok : RunOK sp al ts) (hj : al.stillDirty = javaTest sp)
    (hmk : al.mark = true) (hev : EvictRunOK sp al ts)
    {k : Nat} (hk : k ≤ ts.length) : PendingRefsFresh (st sp al ts k) := by
  have hst : AlgOK sp al := algOK_of sp al (Or.inl hj)
  have hinvk := inv_st sp al ts hok hst k hk
  intro x hxD w hlw hws y a ha
  obtain ⟨d, hd⟩ := (inD_iff _ _).mp hxD
  obtain ⟨hsd, hdl, R, hR, hgd⟩ := sectionD_mem (hinvk.inv1 ▸ hd)
  have hdk : d ≤ k := by rw [hinvk.len] at hdl; omega
  obtain ⟨i, rfl⟩ : ∃ i, d = i+1 := ⟨d-1, by omega⟩
  have hi : i < ts.length := by omega
  have hinvi := inv_st sp al ts hok hst i (by omega)
  have hstep : StepOK sp (st sp al ts i).P (i+1)
      (parts sp al (st sp al ts i) ts[i]).c := by
    have h := hok.2 i hi
    rw [parts_c, hinvi.len]; simpa [st] using h
  rw [st_rec hok hst (i := i) (j := k) (by omega) hk] at hR
  have hReq := Option.some.inj hR
  rw [← hReq, parts_R] at hgd
  have hxgd : x ∈ (parts sp al (st sp al ts i) ts[i]).gd3 := by
    rcases List.mem_append.mp hgd with hg3 | h7
    · exact hg3
    · exfalso
      have ht := (step_r7_shape sp al (st sp al ts i) ts[i] hinvi.len).2.subset h7
      obtain ⟨vx, hvx, hvxn⟩ := (step_written_iff sp al (st sp al ts i) ts[i] hinvi hstep x).mpr
        (Or.inr ht)
      have hvat : (st sp al ts k).S.versionAt (i+1) x = some vx := by
        unfold Stream.versionAt
        rw [st_rec hok hst (i := i) (j := k) (by omega) hk]
        simp only
        rw [parts_R]
        exact find?_node_of_mem (step_vs_nodup sp al _ _ hinvi hstep) hvx hvxn
      obtain ⟨u, hu, hle⟩ := hinvk.le_lv hvat
      rw [hlw] at hu; cases hu
      omega
  obtain ⟨_, _, hxND, hxw, hmarked⟩ :=
    (step_gd3_marked sp al (st sp al ts i) ts[i] hok.1 hinvi hstep x).mp hxgd
  have hlwi := latest_in_prefix hok hst hk (by omega : i ≤ k) hlw (by omega)
  have hwati := hinvi.lv_at hlwi
  obtain ⟨_, _, nx, hnx, hh, _, _⟩ := hinvi.version_node hwati
  have hreach : reachable sp (st sp al ts i).P i x = true := by
    rcases hmarked with hm | ht
    · have hp : reachable sp (parts sp al (st sp al ts i) ts[i]).P (i+1) x = true := by
        unfold marked at hm
        simp only [Bool.and_eq_true] at hm
        exact hm.1
      have hP : (parts sp al (st sp al ts i) ts[i]).P = (st sp al ts (i+1)).P := by
        rw [st_succ sp al ts hi]; rfl
      rw [hP] at hp
      rcases st_noRes hok hst hi x hp with hp | hn
      · exact hp
      · rw [hn] at hnx; cases hnx
    · exact hstep.touchReach x ht
  have hyp := hinvi.ref_mem_pointees hwati ha
  have hyn : y ∈ pointees sp nx.hist := by
    obtain ⟨e, he, hye⟩ := (mem_pointees sp w.hist y).mp hyp
    rw [hh] at he
    exact (mem_pointees sp nx.hist y).mpr ⟨e, (mem_upTo.mp he).1, hye⟩
  have hevI := evLogic_st sp al ts hok hj hmk hev i (by omega)
  obtain ⟨hyND, v, hv, href⟩ := hevI.clean x nx hxw hreach hnx hxND y hyn
  rw [hlwi] at hv; cases hv
  obtain ⟨u, hu⟩ := hinvi.ref_versionAt hwati ha
  obtain ⟨_, _, ny, hny, _⟩ := hinvi.version_node hu
  have hnone := no_write_after_clean hok hst hk (by omega : i ≤ k)
    (by omega) (by rw [hny]; simp) hyND
  have hsame := lv_of_prefix_none (st_S_prefix sp al ts (by omega : i ≤ k) hk)
    (y := y) (fun r hr => hnone r (by rw [hinvi.len] at hr; omega))
  rw [hsame, ← href]
  exact ha

end Contract.OldReads
