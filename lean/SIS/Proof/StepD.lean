/-
Proofs, part 11: one transaction keeps the facts about D.
-/
import SIS.Proof.Still

set_option linter.unusedSectionVars false

namespace SIS

variable {V T : Type} [DecidableEq V]

theorem sectionD_mem {S : Stream V T} {x : NodeId} {d : Nat} (h : (x, d) ∈ sectionD S) :
    lastSp S < d ∧ d + 1 ≤ S.length ∧ ∃ R, S[d]? = some R ∧ x ∈ R.gd := by
  rw [sectionD_eq] at h
  simp only [sectionIdx, List.mem_flatMap, List.mem_range'_1] at h
  obtain ⟨j, ⟨hj1, hj2⟩, hj⟩ := h
  split at hj
  · rename_i R hR
    simp only [List.mem_map, Prod.mk.injEq] at hj
    obtain ⟨y, hy, rfl, rfl⟩ := hj
    exact ⟨by omega, by omega, R, hR, hy⟩
  · simp at hj

section Step

variable (sp : Spec V T) (al : Algo V T) (db : DB V T) (tr : T)

/-- Taken nodes and the nodes left in D2 are different. -/
theorem step_not_taken_of_D2 {k : Nat} (hinv : Inv sp db k) {x : NodeId} {d : Nat}
    (h : (x, d) ∈ (parts sp al db tr).D2) : x ∉ (parts sp al db tr).taken := by
  intro hx
  obtain ⟨d', hd', hle⟩ := (step_taken_mem sp al db tr x).mp hx
  obtain ⟨hD1, hlt⟩ := (step_D2_mem sp al db tr _).mp h
  have := mem_of_nodup_keys (step_D1_nodup sp al db tr hinv) hD1 hd'
  simp only at hlt
  omega

/-- A node that is an index node is not a data node written in step 2. -/
theorem step_not_dataId {k : Nat} (hinv : Inv sp db k)
    (hstep : StepOK sp db.P (k + 1) (parts sp al db tr).c) {x : NodeId}
    (hx : isIndex (parts sp al db tr).P x = true) : x ∉ dataIds sp al db tr := by
  intro hd
  obtain ⟨-, n, hn, hdata⟩ := step_dataIds_spec sp al db tr hinv hstep hd
  simp [isIndex, hn, hdata] at hx

theorem step_lv_index_not_taken {k : Nat} (hinv : Inv sp db k)
    (hstep : StepOK sp db.P (k + 1) (parts sp al db tr).c) {x : NodeId}
    (hx : isIndex (parts sp al db tr).P x = true) (ht : x ∉ (parts sp al db tr).taken) :
    (Snew sp al db tr).lv x = db.S.lv x := by
  apply lv_Snew_not_written
  intro w hw hwx
  have := (step_written_iff sp al db tr hinv hstep x).mp ⟨w, hw, hwx⟩
  rcases this with h | h
  · exact step_not_dataId sp al db tr hinv hstep hx h
  · exact ht h

theorem step_D_eq {k : Nat} (hinv : Inv sp db k) :
    (parts sp al db tr).r7.1 = sectionD (Snew sp al db tr) := by
  obtain ⟨L, hL⟩ : ∃ L, (parts sp al db tr).r7.2 = L := ⟨_, rfl⟩
  have hr7 : (parts sp al db tr).r7 = ((parts sp al db tr).D2 ++ L.map (fun x => (x, k + 1)), L) := by
    rw [(step_r7_shape sp al db tr hinv.len).1, hL]
  have hgd : (parts sp al db tr).R.gd = (parts sp al db tr).gd3 ++ (parts sp al db tr).r7.2 := by
    rw [parts_R]
  have hsp : (parts sp al db tr).R.sp = (parts sp al db tr).s := by rw [parts_R]
  have hs := step_s_le sp al db tr hinv.len
  have hsec : sectionD (Snew sp al db tr) =
      (sectionD db.S).filter (fun e : NodeId × Nat => decide ((parts sp al db tr).R.sp < e.2)) ++
        (parts sp al db tr).R.gd.map (fun x => (x, k + 1)) :=
    sectionD_append db.S (parts sp al db tr).R k hinv.len
      (by rw [hsp]; exact step_s_ge sp al db tr hinv.len hinv.spLt) (by rw [hsp]; exact hs)
  rw [hsec, hgd, hsp, ← hinv.inv1, hr7]
  simp only [parts_D2, parts_D1, hinv.len, List.filter_append, List.map_append, List.append_assoc]
  congr 1
  congr 1
  apply List.filter_eq_self.mpr
  intro e he
  simp only [List.mem_map] at he
  obtain ⟨x, -, rfl⟩ := he
  simp
  omega

theorem step_dNodup {k : Nat} (hinv : Inv sp db k) :
    ((parts sp al db tr).r7.1.map (·.1)).Nodup := by
  obtain ⟨L, hL⟩ : ∃ L, (parts sp al db tr).r7.2 = L := ⟨_, rfl⟩
  have hsub : L.Sublist (parts sp al db tr).taken := by
    rw [← hL]; exact (step_r7_shape sp al db tr hinv.len).2
  rw [(step_r7_shape sp al db tr hinv.len).1, hL]
  simp only [List.map_append, List.map_map]
  rw [List.nodup_append]
  refine ⟨?_, ?_, ?_⟩
  · rw [parts_D2]
    exact (List.Sublist.map _ List.filter_sublist).nodup (step_D1_nodup sp al db tr hinv)
  · have : (((·.1) ∘ fun x => (x, k + 1)) : NodeId → NodeId) = id := by funext x; rfl
    rw [this, List.map_id]
    exact hsub.nodup (step_taken_nodup sp al db tr hinv)
  · intro a ha b hb hab
    subst hab
    simp only [List.mem_map, Function.comp] at ha hb
    obtain ⟨⟨y, d⟩, hy, rfl⟩ := ha
    obtain ⟨z, hz, rfl⟩ := hb
    exact step_not_taken_of_D2 sp al db tr hinv hy (hsub.subset hz)

theorem step_dIndex {k : Nat} (hinv : Inv sp db k) :
    ∀ e ∈ (parts sp al db tr).r7.1, isIndex (parts sp al db tr).P e.1 = true := by
  obtain ⟨L, hL⟩ : ∃ L, (parts sp al db tr).r7.2 = L := ⟨_, rfl⟩
  have hsub : L.Sublist (parts sp al db tr).taken := by
    rw [← hL]; exact (step_r7_shape sp al db tr hinv.len).2
  rw [(step_r7_shape sp al db tr hinv.len).1, hL]
  intro e he
  simp only [List.mem_append, List.mem_map] at he
  rcases he with he | ⟨x, hx, rfl⟩
  · obtain ⟨hD1, -⟩ := (step_D2_mem sp al db tr _).mp he
    rcases (step_D1_mem sp al db tr hinv.len _).mp hD1 with h | ⟨-, h⟩
    · have hi := hinv.dIndex _ h
      rw [step_isIndex_old sp al db tr hinv.len (isSome_of_isIndex hi)]
      exact hi
    · exact (step_gd3_basic sp al db tr hinv.len _ h).2.1
  · exact step_taken_index sp al db tr hinv (hsub.subset hx)

theorem step_inv2 (hst : StillOK sp al) (hok : SpecOK sp) {k : Nat}
    (hinv : Inv sp db k) (hstep : StepOK sp db.P (k + 1) (parts sp al db tr).c) :
    ∀ x, isIndex (parts sp al db tr).P x = true → written sp x = true →
      dirty sp (Snew sp al db tr) (parts sp al db tr).P (k + 1) x = true →
        inD (parts sp al db tr).r7.1 x = true := by
  intro x hx hw hd
  rw [(step_r7_shape sp al db tr hinv.len).1, inD_iff]
  simp only [List.mem_append, List.mem_map, Prod.mk.injEq]
  by_cases ht : x ∈ (parts sp al db tr).taken
  · exact ⟨k + 1, Or.inr ⟨x, hst.complete db k tr hok hinv hstep x ht hd, rfl, rfl⟩⟩
  · -- x stays in D, or got dirty in step 3, or was clean before the writes of step 6.
    have hs := step_s_le sp al db tr hinv.len
    by_cases hD : inD db.D x = true
    · obtain ⟨d, hd'⟩ := (inD_iff _ _).mp hD
      have hD1 : (x, d) ∈ (parts sp al db tr).D1 := (step_D1_mem sp al db tr hinv.len _).mpr (Or.inl hd')
      have hlt : (parts sp al db tr).s < d := Nat.lt_of_not_le (fun hle =>
        ht ((step_taken_mem sp al db tr x).mpr ⟨d, hD1, hle⟩))
      exact ⟨d, Or.inl ((step_D2_mem sp al db tr _).mpr ⟨hD1, hlt⟩)⟩
    · by_cases hg : x ∈ (parts sp al db tr).gd3
      · have hD1 : (x, k + 1) ∈ (parts sp al db tr).D1 :=
          (step_D1_mem sp al db tr hinv.len _).mpr (Or.inr ⟨rfl, hg⟩)
        exact ⟨k + 1, Or.inl ((step_D2_mem sp al db tr _).mpr ⟨hD1, by simp only; omega⟩)⟩
      · exfalso
        have hclean : dirty sp (db.S.building (parts sp al db tr).vs0) (parts sp al db tr).P (k + 1) x
            = false := by
          cases hc : dirty sp (db.S.building (parts sp al db tr).vs0) (parts sp al db tr).P (k + 1) x
          · rfl
          · exfalso
            apply hg
            rw [step_gd3_mem' sp al db tr hok hinv hstep]
            exact ⟨isSome_of_isIndex hx, hx, by simpa using hD, hw, hc⟩
        rw [dirty_false_iff] at hclean
        obtain ⟨v, hv, hgood⟩ := hclean
        have hlvS : (Snew sp al db tr).lv x = some v := by
          rw [step_lv_index_not_taken sp al db tr hinv hstep hx ht]
          rw [lv_building] at hv
          have : (parts sp al db tr).vs0.find? (fun v => v.node == x) = none := by
            rw [List.find?_eq_none]
            intro w hw hwx
            have hw' : w ∈ (parts sp al db tr).vs :=
              (step_vs0_prefix sp al db tr).subset hw
            have := step_lv_index_not_taken sp al db tr hinv hstep hx ht
            have h2 := (step_written_iff sp al db tr hinv hstep x).mp ⟨w, hw', by simpa using hwx⟩
            rcases h2 with h2 | h2
            · exact step_not_dataId sp al db tr hinv hstep hx h2
            · exact ht h2
          rw [this, Option.none_or] at hv
          exact hv
        have hext : SExt (db.S.building (parts sp al db tr).vs0) (Snew sp al db tr) :=
          (SExt.building (step_vs0_prefix sp al db tr)).trans
            (SExt.building_complete (parts sp al db tr).R (by rw [parts_R]))
        rw [← Bool.not_eq_false, dirty_false_iff] at hd
        exact hd ⟨v, hlvS, fun t ht' hr =>
          good_mono' sp hext (Grow.refl _ (k + 1)) ht' (hgood t ht' hr)⟩

/-- An entry of D2 comes from D, or got dirty in step 3 with d = k+1. -/
theorem step_D2_cases {k : Nat} (hinv : Inv sp db k) {x : NodeId} {d : Nat}
    (h : (x, d) ∈ (parts sp al db tr).D2) :
    ((x, d) ∈ db.D ∧ d ≤ k) ∨ (d = k + 1 ∧ x ∈ (parts sp al db tr).gd3 ∧ inD db.D x = false) := by
  obtain ⟨hD1, -⟩ := (step_D2_mem sp al db tr _).mp h
  rcases (step_D1_mem sp al db tr hinv.len _).mp hD1 with h1 | ⟨h1, h2⟩
  · left
    refine ⟨h1, ?_⟩
    rw [hinv.inv1] at h1
    have := (sectionD_mem h1).2.1
    rw [hinv.len] at this
    omega
  · right
    exact ⟨h1, h2, (step_gd3_basic sp al db tr hinv.len x h2).2.2⟩

theorem step_inv3 (hok : SpecOK sp) {k : Nat}
    (hinv : Inv sp db k) (hstep : StepOK sp db.P (k + 1) (parts sp al db tr).c) :
    ∀ x d v, (x, d) ∈ (parts sp al db tr).r7.1 → (Snew sp al db tr).lv x = some v →
      d ≤ v.recNo ∨ ∀ t < d, reachable sp (parts sp al db tr).P t x = true →
        good sp (Snew sp al db tr) (parts sp al db tr).P t v = true := by
  have hg := step_grow sp al db tr hinv.len
  have hreach : ∀ t ≤ k, ∀ x, reachable sp (parts sp al db tr).P t x = reachable sp db.P t x :=
    fun t ht x => reachable_grow hok.liveSub hinv.ptrs hinv.rootIn hg ht x
  have hext := Snew_ext sp al db tr
  intro x d v hxd hlv
  have hsub := (step_r7_shape sp al db tr hinv.len).2
  rw [(step_r7_shape sp al db tr hinv.len).1] at hxd
  simp only [List.mem_append, List.mem_map, Prod.mk.injEq] at hxd
  rcases hxd with hxd | ⟨y, hy, rfl, rfl⟩
  · have hnt := step_not_taken_of_D2 sp al db tr hinv hxd
    have hidx : isIndex (parts sp al db tr).P x = true :=
      step_dIndex sp al db tr hinv (x, d) (by
        rw [(step_r7_shape sp al db tr hinv.len).1]; exact List.mem_append_left _ hxd)
    rw [step_lv_index_not_taken sp al db tr hinv hstep hidx hnt] at hlv
    rcases step_D2_cases sp al db tr hinv hxd with ⟨hD, hdk⟩ | ⟨rfl, hgd, hnD⟩
    · rcases hinv.inv3 x d v hD hlv with h | h
      · exact Or.inl h
      · right
        intro t ht hr
        rw [hreach t (by omega)] at hr
        exact good_mono' sp hext hg (by omega) (h t ht hr)
    · right
      -- x got dirty in step 3: it was clean after the previous transaction.
      obtain ⟨r, hr⟩ := lv_versionAt hlv
      obtain ⟨R, hR, hvR, hvx⟩ := versionAt_spec hr
      obtain ⟨n, hn, -⟩ := hinv.vh r R hR v hvR
      rw [hvx] at hn
      have hidx0 : isIndex db.P x = true := by
        rw [← step_isIndex_old sp al db tr hinv.len (by simp [hn])]; exact hidx
      have hcl : dirty sp db.S db.P k x = false := by
        cases hc : dirty sp db.S db.P k x
        · rfl
        · have := hinv.inv2 x hidx0 (step_gd3_written sp al db tr x hgd) hc
          rw [hnD] at this; simp at this
      rw [dirty_false_iff] at hcl
      obtain ⟨v', hv', hgood⟩ := hcl
      rw [hlv] at hv'
      cases hv'
      intro t ht hr
      rw [hreach t (by omega)] at hr
      exact good_mono' sp hext hg (by omega) (hgood t (by omega) hr)
  · -- x stayed dirty after it was written in this transaction.
    left
    have hyt := hsub.subset hy
    obtain ⟨w, hw, hwy⟩ := (step_written_iff sp al db tr hinv hstep y).mpr (Or.inr hyt)
    have := lv_Snew_written sp al db tr (step_vs_nodup sp al db tr hinv hstep) hw
    rw [hwy, hlv] at this
    cases this
    obtain ⟨n, pre, -, -, h, -⟩ := built_mem (step_vs_built sp al db tr hinv.len) hw
    omega

theorem step_inv4 (hok : SpecOK sp) {k : Nat}
    (hinv : Inv sp db k) (hstep : StepOK sp db.P (k + 1) (parts sp al db tr).c) :
    ∀ x d, (x, d) ∈ (parts sp al db tr).r7.1 → (Snew sp al db tr).lv x = none →
      ∀ t < d, reachable sp (parts sp al db tr).P t x = false := by
  have hg := step_grow sp al db tr hinv.len
  have hreach : ∀ t ≤ k, ∀ x, reachable sp (parts sp al db tr).P t x = reachable sp db.P t x :=
    fun t ht x => reachable_grow hok.liveSub hinv.ptrs hinv.rootIn hg ht x
  intro x d hxd hlv
  have hsub := (step_r7_shape sp al db tr hinv.len).2
  rw [(step_r7_shape sp al db tr hinv.len).1] at hxd
  simp only [List.mem_append, List.mem_map, Prod.mk.injEq] at hxd
  rcases hxd with hxd | ⟨y, hy, rfl, rfl⟩
  · have hnt := step_not_taken_of_D2 sp al db tr hinv hxd
    have hidx : isIndex (parts sp al db tr).P x = true :=
      step_dIndex sp al db tr hinv (x, d) (by
        rw [(step_r7_shape sp al db tr hinv.len).1]; exact List.mem_append_left _ hxd)
    rw [step_lv_index_not_taken sp al db tr hinv hstep hidx hnt] at hlv
    rcases step_D2_cases sp al db tr hinv hxd with ⟨hD, hdk⟩ | ⟨rfl, hgd, hnD⟩
    · intro t ht
      rw [hreach t (by omega)]
      exact hinv.inv4 x d hD hlv t ht
    · intro t ht
      rw [hreach t (by omega)]
      -- x is new: an old index node without a version would be in D.
      cases hx0 : db.P.get? x with
      | none =>
        cases hr : reachable sp db.P t x
        · rfl
        · rw [reachable_iff] at hr
          have := hr.isSome
          rw [hx0] at this; simp at this
      | some n =>
        exfalso
        have hidx0 : isIndex db.P x = true := by
          rw [← step_isIndex_old sp al db tr hinv.len (by simp [hx0])]; exact hidx
        have hdirty : dirty sp db.S db.P k x = true := by simp [dirty, hlv]
        have := hinv.inv2 x hidx0 (step_gd3_written sp al db tr x hgd) hdirty
        rw [hnD] at this; simp at this
  · exfalso
    have hyt := hsub.subset hy
    obtain ⟨w, hw, hwy⟩ := (step_written_iff sp al db tr hinv hstep y).mpr (Or.inr hyt)
    have := lv_Snew_written sp al db tr (step_vs_nodup sp al db tr hinv hstep) hw
    rw [hwy, hlv] at this
    simp at this

theorem step_dataV {k : Nat} (hinv : Inv sp db k)
    (hstep : StepOK sp db.P (k + 1) (parts sp al db tr).c) :
    ∀ x n, (parts sp al db tr).P.get? x = some n → n.isData = true →
      ∃ v, (Snew sp al db tr).lv x = some v ∧ v.hist = n.hist := by
  intro x n' hn' hd
  rcases step_node_cases sp al db tr hinv.len hn' with ⟨n, hn, rfl⟩ | ⟨hx0, nn, hnn, hid, rfl⟩
  · simp only at hd
    obtain ⟨v, hv, hvh⟩ := hinv.dataV x n hn hd
    have hA : addsFor (parts sp al db tr).c (k + 1) x = [] := by
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro e he
      rw [mem_addsFor] at he
      have := hstep.dataFixed (x, e.val) he.2 n hn
      rw [hd] at this; simp at this
    refine ⟨v, ?_, by simp [hA, hvh]⟩
    rw [lv_Snew_not_written]
    · exact hv
    · intro w hw hwx
      have := (step_written_iff sp al db tr hinv hstep x).mp ⟨w, hw, hwx⟩
      rcases this with h | h
      · have := (step_dataIds_spec sp al db tr hinv hstep h).1
        rw [hn] at this; simp at this
      · have := step_taken_index sp al db tr hinv h
        simp [isIndex, step_P_old sp al db tr hinv.len hn, hd] at this
  · simp only at hd
    have hxd : x ∈ dataIds sp al db tr := by
      simp only [dataIds, List.mem_map, List.mem_filter]
      exact ⟨nn, ⟨hnn, hd⟩, hid⟩
    obtain ⟨w, hw, hwx⟩ := (step_written_iff sp al db tr hinv hstep x).mpr (Or.inl hxd)
    refine ⟨w, by rw [← hwx]; exact lv_Snew_written sp al db tr (step_vs_nodup sp al db tr hinv hstep) hw, ?_⟩
    obtain ⟨n2, pre, hn2, -, -, h1, -⟩ := built_mem (step_vs_built sp al db tr hinv.len) hw
    rw [hwx, hn'] at hn2
    cases hn2
    exact h1

end Step

end SIS
