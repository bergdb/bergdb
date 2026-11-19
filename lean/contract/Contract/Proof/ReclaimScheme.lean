/-
The contract package (bergdb 030-23): the proofs of T-SCHEME's proved half
(Contract/ReclaimScheme.lean), in the abstract model's words. Given that every
node reachable at a time from e to k has its latest version at c or later
(`latest_st`, which RC gives), every node of D has its latest version at c or
later (`inD_lv_ge`), and so has the version that top(k) names (`top_ge`).

A node of D got dirty at a record d after the startup pos, so after e: it was
marked then (reachable at d), touched (reachable at d - 1), or put back by Rule
A (written at d). With a virtual root, the root child that top(k) names, the
newest one created up to the startup pos s, is a live child of the root at s
(`reach_top_virt`): no root child points to a newer one, so the root child
is the root's live child at its creation, and the root has no later entry up
to s.
-/
import SIS.ReclaimTheorems
import SIS.Proof.HandleCutT12
import SIS.Proof.EvLogic
import SIS.Proof.PhysStart
import SIS.Proof.BoundT4Debt
import SIS.Proof.BoundT4

namespace Contract

open SIS

variable {V T : Type} [DecidableEq V]

/-! ## The startup pos and the largest cut -/

section

variable {sp : Spec V T} {al : Algo V T} {ts : List T}

/-- The startup pos of the state after the first j transactions of a run is at
most j (it is clamped to i - 1, and that of record 0 is 0). -/
theorem lastSp_take_le (hok : RunOK sp al ts) (hst : AlgOK sp al) (j : Nat) :
    lastSp (run sp al (ts.take j)).S ≤ j := by
  have key : ∀ i ≤ ts.length, lastSp (st sp al ts i).S ≤ i := by
    intro i hi
    rcases (inv_st sp al ts hok hst i hi).spLt with h | ⟨-, h⟩ <;> omega
  by_cases h : j ≤ ts.length
  · exact key j h
  · have h1 : ts.take j = ts.take ts.length := by
      rw [List.take_of_length_le (by omega), List.take_length]
    have := key ts.length (Nat.le_refl _)
    simp only [st] at this
    rw [h1]
    omega

end

/-- The largest cut of the first j + 1 marks is the cut c of mark j when every
earlier mark's cut is at most c. -/
theorem cutMax_take_of_le {C : Type} (cs : List (T × Option Nat × C)) {j : Nat}
    (hj : j < cs.length) {c : Nat} (hc : cs[j].2.1 = some c)
    (hle : ∀ i (hi : i < j) c', cs[i].2.1 = some c' → c' ≤ c) :
    cutMax ((cs.take (j + 1)).map (·.2.1)) = c := by
  have hpre : ∀ i ≤ j, cutMax ((cs.take i).map (·.2.1)) ≤ c := by
    intro i
    induction i with
    | zero => intro _; simp [cutMax]
    | succ i ih =>
      intro hi
      rw [cutMax_take_succ cs (by omega)]
      refine Nat.max_le.mpr ⟨ih (by omega), ?_⟩
      cases hci : cs[i].2.1 with
      | none => simp
      | some c' => simpa using hle i (by omega) c' hci
  rw [cutMax_take_succ cs hj, hc]
  have := hpre j (Nat.le_refl _)
  simp only [Option.getD_some]
  omega

/-! ## The nodes of D -/

section

variable {sp : Spec V T} {al : Algo V T} {ts : List T}

/-- Record j + 1 of a later state is the record that transaction j + 1 appended. -/
theorem st_record {j : Nat} (hj : j < ts.length) {k : Nat} (hjk : j + 1 ≤ k) (hk : k ≤ ts.length)
    (hlen : (st sp al ts j).S.length = j + 1) {R : Record V T}
    (hR : (st sp al ts k).S[j + 1]? = some R) : R = (parts sp al (st sp al ts j) ts[j]).R := by
  have hpre := st_S_prefix sp al ts hjk hk
  rw [st_S_succ sp al ts hj] at hpre
  obtain ⟨l, hl⟩ := hpre
  rw [← hl, List.getElem?_append_left (by simp [hlen]), List.getElem?_append_right (by omega),
    hlen] at hR
  simp only [Nat.sub_self, List.getElem?_cons_zero, Option.some.injEq] at hR
  exact hR.symm

/-- Under the conclusion of `latest_st` from e on, with the startup pos of
record k at e or later: every node of D after T(k) has its latest version, if
any, at c or later. A node of D got dirty at a record d after the startup pos,
so after e: marked (reachable at d), touched (reachable at d - 1), or put back
by Rule A (written at d). With the marking (`Algo.mark`), step 3 takes the
marked nodes and the touched ones. -/
theorem inD_lv_ge (hok : RunOK sp al ts) (hst : AlgOK sp al) (hmk : al.mark = true) {c e k : Nat}
    (hk : k ≤ ts.length) (hce : c ≤ e) (hes : e ≤ lastSp (run sp al (ts.take k)).S)
    (hlat : ∀ t x, e ≤ t → t ≤ k → reachable sp (run sp al (ts.take k)).P t x = true →
      ∀ v, (run sp al (ts.take k)).S.lv x = some v → c ≤ v.recNo) :
    ∀ x, inD (run sp al (ts.take k)).D x = true → ∀ v, (run sp al (ts.take k)).S.lv x = some v →
      c ≤ v.recNo := by
  intro x hx v hv
  have hls : LiveSub sp := hok.1.liveSub
  have hinvk := inv_st sp al ts hok hst k hk
  obtain ⟨d, hd⟩ := (inD_iff _ _).mp hx
  have hsec : (x, d) ∈ sectionD (st sp al ts k).S := by rw [← hinvk.inv1]; exact hd
  obtain ⟨hsd, hdl, R, hR, hxR⟩ := sectionD_mem hsec
  have hlen := hinvk.len
  have hes' : e ≤ lastSp (st sp al ts k).S := hes
  obtain ⟨j, rfl⟩ : ∃ j, d = j + 1 := ⟨d - 1, by omega⟩
  have hj : j < ts.length := by omega
  have hjk : j + 1 ≤ k := by omega
  have hinvj := inv_st sp al ts hok hst j (by omega)
  have hstep : StepOK sp (st sp al ts j).P (j + 1) (parts sp al (st sp al ts j) ts[j]).c := by
    have := hok.2 j hj
    rw [parts_c, hinvj.len]
    simpa [st] using this
  have hRj := st_record hj hjk hk hinvj.len hR
  subst hRj
  have hgd : (parts sp al (st sp al ts j) ts[j]).R.gd =
      (parts sp al (st sp al ts j) ts[j]).gd3 ++ (parts sp al (st sp al ts j) ts[j]).r7.2 := rfl
  rw [hgd] at hxR
  rcases List.mem_append.mp hxR with hg | hr7
  · -- With marking, step 3 takes the marked nodes and the touched ones.
    have hcase : marked sp (parts sp al (st sp al ts j) ts[j]).P
        (parts sp al (st sp al ts j) ts[j]).c (j + 1) x = true ∨
        x ∈ (parts sp al (st sp al ts j) ts[j]).c.touch := by
      rw [parts_gd3, hinvj.len, List.mem_filter, List.mem_append] at hg
      rcases hg.1 with h1 | h1
      · simp only [hmk, ↓reduceIte, markOf, List.mem_mergeSort, List.mem_filter, mem_allIds,
          Bool.and_eq_true] at h1
        exact Or.inl h1.2.2
      · exact Or.inr (mem_touchOf.mp h1).1
    rcases hcase with hm | ht
    · -- Marked: reachable at j + 1 after the change.
      have hP : (st sp al ts (j + 1)).P = (parts sp al (st sp al ts j) ts[j]).P := by
        rw [st_succ sp al ts hj, step_eq_parts]
      have hre : reachable sp (st sp al ts (j + 1)).P (j + 1) x = true := by
        rw [hP]
        simp only [marked, Bool.and_eq_true] at hm
        exact hm.1
      have hinv1 := inv_st sp al ts hok hst (j + 1) (by omega)
      have hg1 := st_grow sp al ts hok hst (j := j + 1) (j' := k) hjk hk
      rw [← reachable_grow hls hinv1.ptrs hinv1.rootIn hg1 (Nat.le_refl _)] at hre
      exact hlat (j + 1) x (by omega) hjk hre v hv
    · -- Touched: reachable at j before the change.
      have hre := hstep.touchReach x ht
      simp only [Nat.add_sub_cancel] at hre
      have hg1 := st_grow sp al ts hok hst (j := j) (j' := k) (by omega) hk
      rw [← reachable_grow hls hinvj.ptrs hinvj.rootIn hg1 (Nat.le_refl _)] at hre
      exact hlat j x (by omega) (by omega) hre v hv
  · -- Put back by Rule A: written at j + 1.
    have htk := (step_r7_shape sp al _ _ hinvj.len).2.subset hr7
    obtain ⟨w, hw, hwx⟩ := (step_written_iff sp al _ _ hinvj hstep x).mpr (Or.inr htk)
    have hver : (st sp al ts (j + 1)).S.versionAt (j + 1) x = some w := by
      rw [st_S_succ sp al ts hj]
      have := versionAt_snoc_self (st sp al ts j).S (parts sp al (st sp al ts j) ts[j]).R x
      rw [hinvj.len] at this
      rw [this]
      exact find?_node_of_mem (step_vs_nodup sp al _ _ hinvj hstep) hw hwx
    have := st_lv_ge hok hst hjk hk hver hv
    omega

end

/-! ## The references of D's nodes below the cut -/

section

variable {sp : Spec V T} {al : Algo V T} {ts : List T}

/-- A node with a version in a record r after J, with the startup pos of the
state after T(k), r ≤ k, at J or before, was taken at r: it is in D after T(J)
with an index at most s(r), if it is an index node after T(k) or exists after
T(J) (a data node is written only when created). -/
theorem written_inD (hok : RunOK sp al ts) (hst : AlgOK sp al) {J k r : Nat} (hk : k ≤ ts.length)
    (hsJ : lastSp (st sp al ts k).S ≤ J) (hJr : J < r) (hrk : r ≤ k) {y : NodeId}
    {u : Version V} (hu : (st sp al ts k).S.versionAt r y = some u)
    (hy : isIndex (st sp al ts k).P y = true ∨ ((st sp al ts J).P.get? y).isSome) :
    ∃ d, (y, d) ∈ (st sp al ts J).D ∧ d ≤ lastSp (st sp al ts r).S := by
  obtain ⟨i, rfl⟩ : ∃ i, r = i + 1 := ⟨r - 1, by omega⟩
  have hi : i < ts.length := by omega
  have hinvi := inv_st sp al ts hok hst i (by omega)
  have hlen := hinvi.len
  have hstep : StepOK sp (st sp al ts i).P (i + 1) (parts sp al (st sp al ts i) ts[i]).c := by
    have := hok.2 i hi
    rw [parts_c, hlen]
    simpa [st] using this
  have hinv1 := inv_st sp al ts hok hst (i + 1) (by omega)
  have hu' : (st sp al ts (i + 1)).S.versionAt (i + 1) y = some u := by
    rw [← versionAt_of_prefix (st_S_prefix sp al ts hrk hk) (by rw [hinv1.len]; omega)]
    exact hu
  rw [st_S_succ sp al ts hi, ← hlen, versionAt_snoc_self] at hu'
  obtain ⟨hmem, hnode⟩ := find?_node_spec hu'
  rcases (step_written_iff sp al _ _ hinvi hstep y).mp ⟨u, hmem, hnode⟩ with hd | ht
  · -- A data node created at r.
    exfalso
    obtain ⟨hnone, n, hn, hdat⟩ := step_dataIds_spec sp al _ _ hinvi hstep hd
    rcases hy with hy | hy
    · have hP : (st sp al ts (i + 1)).P = (parts sp al (st sp al ts i) ts[i]).P := by
        rw [st_succ sp al ts hi, step_eq_parts]
      have hg := st_grow sp al ts hok hst (j := i + 1) (j' := k) hrk hk
      obtain ⟨n', hn', -, hd', -⟩ := hg y n (by rw [hP]; exact hn)
      simp [isIndex, hn', hd', hdat] at hy
    · have hg := st_grow sp al ts hok hst (j := J) (j' := i) (by omega) (by omega)
      obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp hy
      obtain ⟨n', hn', -⟩ := hg y n hn
      rw [hnone] at hn'
      cases hn'
  · -- Taken at r: in D before the step, with an index at most s(r).
    obtain ⟨d, hd1, hds⟩ := (step_taken_mem sp al _ _ y).mp ht
    have hs : (parts sp al (st sp al ts i) ts[i]).s = lastSp (st sp al ts (i + 1)).S := by
      rw [st_succ sp al ts hi, step_S, step_lastSp]
    rw [hs] at hds
    have hsk := lastSp_st_mono hok hst (i := i + 1) (j := k) hrk hk
    rcases (step_D1_mem sp al _ _ hlen _).mp hd1 with h | ⟨h, -⟩
    · refine ⟨d, ?_, hds⟩
      have hsec : (y, d) ∈ sectionD (st sp al ts i).S := by rw [← hinvi.inv1]; exact h
      obtain ⟨h1, -, R, hR, hyR⟩ := sectionD_mem hsec
      have hinvJ := inv_st sp al ts hok hst J (by omega)
      have hspJ := lastSp_st_mono hok hst (i := J) (j := i) (by omega) (by omega)
      rw [hinvJ.inv1]
      have hdJ : d < (st sp al ts J).S.length := by rw [hinvJ.len]; omega
      refine mem_sectionD_of (by omega) hdJ ?_ hyR
      obtain ⟨l, hl⟩ := st_S_prefix sp al ts (j := J) (j' := i) (by omega) (by omega)
      rw [← hl, List.getElem?_append_left hdJ] at hR
      exact hR
    · simp only at h
      omega

/-- The references below c of the latest versions of D's nodes, given that the
nodes of D have their latest versions at c or later in every state from the
startup pos of the state after T(k) to k (RC gives it: `inD_lv_ge`). Let x be
in D after T(k), with index d > s(k), and its latest version w name record r0
< c for a pointee y. Then there is a state J from s(k) to k in which y is not
in D and y's latest version is at r0:

* x got dirty at d by marking or the touch: J = d - 1. x is not written after
  J (it would have been in D then), so w is x's latest version then, x is
  reachable then and not in D, and with A6' (`EvLogic.clean`) y is not in D
  then and w names y's latest version then.
* x was put back by Rule A at d: J = d. w is x's version written at d, which
  names the latest versions of its pointees after T(d) (`step_taken_refs`); y
  is not in D then, since its latest version is below c.

As s(k) ≤ J, y is not written after J (`written_inD`): its latest version after
T(k) is at r0, so it is not in D after T(k) either. -/
theorem dref_lv (hok : RunOK sp al ts) (hj : al.stillDirty = javaTest sp) (hmk : al.mark = true)
    (hev : EvictRunOK sp al ts) {c k : Nat} (hk : k ≤ ts.length)
    (hD : ∀ K, lastSp (run sp al (ts.take k)).S ≤ K → K ≤ k →
      ∀ x, inD (run sp al (ts.take K)).D x = true → ∀ v, (run sp al (ts.take K)).S.lv x = some v →
        c ≤ v.recNo) :
    ∀ x, inD (run sp al (ts.take k)).D x = true → ∀ v, (run sp al (ts.take k)).S.lv x = some v →
      ∀ y r, v.ref? y = some r → r < c →
        ((run sp al (ts.take k)).S.lv y).map (·.recNo) = some r ∧
          inD (run sp al (ts.take k)).D y = false := by
  intro x hx w hw y r0 hr0 hrc
  have hst : AlgOK sp al := algOK_of sp al (Or.inl hj)
  have hinvk := inv_st sp al ts hok hst k hk
  change inD (st sp al ts k).D x = true at hx
  change (st sp al ts k).S.lv x = some w at hw
  change ((st sp al ts k).S.lv y).map (·.recNo) = some r0 ∧ inD (st sp al ts k).D y = false
  obtain ⟨dx, hdx⟩ := (inD_iff _ _).mp hx
  have hsec : (x, dx) ∈ sectionD (st sp al ts k).S := by rw [← hinvk.inv1]; exact hdx
  obtain ⟨hsd, hdl, R, hR, hxR⟩ := sectionD_mem hsec
  have hlen := hinvk.len
  have hxi : isIndex (st sp al ts k).P x = true := hinvk.dIndex _ hdx
  obtain ⟨j, rfl⟩ : ∃ j, dx = j + 1 := ⟨dx - 1, by omega⟩
  have hjl : j < ts.length := by omega
  have hjk : j + 1 ≤ k := by omega
  have hinvj := inv_st sp al ts hok hst j (by omega)
  have hinv1 := inv_st sp al ts hok hst (j + 1) (by omega)
  have hstep : StepOK sp (st sp al ts j).P (j + 1) (parts sp al (st sp al ts j) ts[j]).c := by
    have := hok.2 j hjl
    rw [parts_c, hinvj.len]
    simpa [st] using this
  have hRj := st_record hjl hjk hk hinvj.len hR
  subst hRj
  have hgd : (parts sp al (st sp al ts j) ts[j]).R.gd =
      (parts sp al (st sp al ts j) ts[j]).gd3 ++ (parts sp al (st sp al ts j) ts[j]).r7.2 := rfl
  rw [hgd] at hxR
  have hvk : ∀ {z : NodeId} {r' : Nat} {u : Version V},
      (st sp al ts k).S.versionAt r' z = some u → r' ≤ k := by
    intro z r' u h
    obtain ⟨R', hR', -⟩ := versionAt_spec h
    have := (List.getElem?_eq_some_iff.mp hR').1
    omega
  -- A state J from s(k) on in which y is not in D and its latest version is at r0.
  have key : ∃ J, lastSp (st sp al ts k).S ≤ J ∧ J ≤ k ∧ inD (st sp al ts J).D y = false ∧
      ((st sp al ts J).P.get? y).isSome ∧ ((st sp al ts J).S.lv y).map (·.recNo) = some r0 := by
    rcases List.mem_append.mp hxR with hg | hr7
    · -- x got dirty at j + 1 by marking or the touch: J = j.
      have hxD : inD (st sp al ts j).D x = false := step_gd3_not_inD sp al _ _ hg
      have hxw : written sp x = true := step_gd3_written sp al _ _ x hg
      have hxnone : ∀ r', j + 1 ≤ r' → (st sp al ts k).S.versionAt r' x = none := by
        intro r' hr'
        cases hv : (st sp al ts k).S.versionAt r' x with
        | none => rfl
        | some u =>
          exfalso
          obtain ⟨d, hd, -⟩ := written_inD hok hst hk (J := j) (by omega) (by omega) (hvk hv) hv
            (Or.inl hxi)
          have : inD (st sp al ts j).D x = true := (inD_iff _ _).mpr ⟨d, hd⟩
          rw [hxD] at this
          cases this
      have hlvj : (st sp al ts j).S.lv x = some w := by
        rw [st_S_take hok hst (j := j) (k := k) (by omega) hk, lv_take hxnone]
        exact hw
      have hwj := hinvj.lv_at hlvj
      obtain ⟨-, -, n, hn, hwh, -, -⟩ := hinvj.version_node hwj
      have hcase : marked sp (parts sp al (st sp al ts j) ts[j]).P
          (parts sp al (st sp al ts j) ts[j]).c (j + 1) x = true ∨
          x ∈ (parts sp al (st sp al ts j) ts[j]).c.touch := by
        rw [parts_gd3, hinvj.len, List.mem_filter, List.mem_append] at hg
        rcases hg.1 with h1 | h1
        · simp only [hmk, ↓reduceIte, markOf, List.mem_mergeSort, List.mem_filter, mem_allIds,
            Bool.and_eq_true] at h1
          exact Or.inl h1.2.2
        · exact Or.inr (mem_touchOf.mp h1).1
      have hre : reachable sp (st sp al ts j).P j x = true := by
        rcases hcase with hm | ht
        · have hre1 : reachable sp (parts sp al (st sp al ts j) ts[j]).P (j + 1) x = true := by
            simp only [marked, Bool.and_eq_true] at hm
            exact hm.1
          rw [parts_P' sp al _ _ hinvj.len] at hre1
          rcases hstep.noRes x hre1 with h | h
          · simpa using h
          · exfalso
            obtain ⟨nn, hnn, hid⟩ := List.mem_map.mp h
            have := hstep.fresh nn hnn
            rw [hid, hn] at this
            cases this
        · have := hstep.touchReach x ht
          simpa using this
      have hyp : y ∈ pointees sp n.hist := by
        have h1 := hinvj.ref_mem_pointees hwj hr0
        rw [hwh] at h1
        obtain ⟨e', he', hye⟩ := (mem_pointees sp _ y).mp h1
        exact (mem_pointees sp _ y).mpr ⟨e', (mem_upTo.mp he').1, hye⟩
      have hlog := evLogic_st sp al ts hok hj hmk hev j (by omega)
      obtain ⟨hyD, v', hv', hvref⟩ := hlog.clean x n hxw hre hn hxD y hyp
      rw [hlvj, Option.some.injEq] at hv'
      subst hv'
      obtain ⟨e', he', hye⟩ := (mem_pointees sp _ y).mp hyp
      obtain ⟨m, hm, -⟩ := hinvj.ptrs x n hn e' he' y hye
      refine ⟨j, by omega, by omega, hyD, by simp [hm], ?_⟩
      rw [← hvref]
      exact hr0
    · -- x was put back by Rule A at j + 1: J = j + 1.
      have htk := (step_r7_shape sp al _ _ hinvj.len).2.subset hr7
      have hP : (st sp al ts (j + 1)).P = (parts sp al (st sp al ts j) ts[j]).P := by
        rw [st_succ sp al ts hjl, step_eq_parts]
      have hS : (st sp al ts (j + 1)).S = Snew sp al (st sp al ts j) ts[j] := by
        rw [st_succ sp al ts hjl, step_S]
      obtain ⟨nx, hnx⟩ := Option.isSome_iff_exists.mp
        (isSome_of_isIndex (step_taken_index sp al _ _ hinvj htk))
      obtain ⟨v, hv, hvref⟩ := step_taken_refs sp al _ _ hok.1 hinvj hstep htk hnx
      have hsk1 := lastSp_st_mono hok hst (i := j + 1) (j := k) hjk hk
      have hxD1 : (x, j + 1) ∈ (st sp al ts (j + 1)).D := by
        rw [hinv1.inv1]
        refine mem_sectionD_of (R := (parts sp al (st sp al ts j) ts[j]).R) (by omega)
          (by rw [hinv1.len]; omega) ?_ (by rw [hgd]; exact hxR)
        rw [hS, ← hinvj.len]
        exact Snew_getElem?_new sp al _ _
      have hxnone : ∀ r', j + 2 ≤ r' → (st sp al ts k).S.versionAt r' x = none := by
        intro r' hr'
        cases hv' : (st sp al ts k).S.versionAt r' x with
        | none => rfl
        | some u =>
          exfalso
          have hr'k := hvk hv'
          obtain ⟨d, hd, hds⟩ := written_inD hok hst hk (J := j + 1) (by omega) (by omega) hr'k hv'
            (Or.inl hxi)
          have h1 := mem_of_nodup_keys hinv1.dNodup hd hxD1
          have h2 := lastSp_st_mono hok hst (i := r') (j := k) hr'k hk
          omega
      have hlv1 : (st sp al ts (j + 1)).S.lv x = some w := by
        rw [st_S_take hok hst (j := j + 1) (k := k) hjk hk, lv_take hxnone]
        exact hw
      have hwj := hinv1.lv_at hlv1
      rw [hS, hv, Option.some.injEq] at hlv1
      subst hlv1
      obtain ⟨-, -, n1, hn1, hwh, -, -⟩ := hinv1.version_node hwj
      have hn1x : n1 = nx := by
        rw [hP, hnx] at hn1
        exact (Option.some.inj hn1).symm
      subst hn1x
      have hyp : y ∈ pointees sp n1.hist := by
        have h1 := hinv1.ref_mem_pointees hwj hr0
        rw [hwh] at h1
        obtain ⟨e', he', hye⟩ := (mem_pointees sp _ y).mp h1
        exact (mem_pointees sp _ y).mpr ⟨e', (mem_upTo.mp he').1, hye⟩
      have hr0' := hvref y hyp
      rw [hr0, ← hS] at hr0'
      obtain ⟨e', he', hye⟩ := (mem_pointees sp _ y).mp hyp
      obtain ⟨m, hm, -⟩ := hinv1.ptrs x n1 (by rw [hP]; exact hnx) e' he' y hye
      refine ⟨j + 1, by omega, hjk, ?_, by simp [hm], hr0'.symm⟩
      cases hyD : inD (st sp al ts (j + 1)).D y with
      | false => rfl
      | true =>
        exfalso
        cases hl : (st sp al ts (j + 1)).S.lv y with
        | none => rw [hl] at hr0'; cases hr0'
        | some u =>
          rw [hl, Option.map_some, Option.some.injEq] at hr0'
          have := hD (j + 1) (show lastSp (st sp al ts k).S ≤ j + 1 by omega) hjk y hyD u hl
          omega
  obtain ⟨J, hsJ, hJk, hyD, hyJ, hlvJ⟩ := key
  have hnone : ∀ r', J + 1 ≤ r' → (st sp al ts k).S.versionAt r' y = none := by
    intro r' hr'
    cases hv : (st sp al ts k).S.versionAt r' y with
    | none => rfl
    | some u =>
      exfalso
      obtain ⟨d, hd, -⟩ := written_inD hok hst hk hsJ (by omega) (hvk hv) hv (Or.inr hyJ)
      have : inD (st sp al ts J).D y = true := (inD_iff _ _).mpr ⟨d, hd⟩
      rw [hyD] at this
      cases this
  have hlvk : (st sp al ts k).S.lv y = (st sp al ts J).S.lv y := by
    rw [st_S_take hok hst hJk hk, lv_take hnone]
  have h1 : ((st sp al ts k).S.lv y).map (·.recNo) = some r0 := by rw [hlvk]; exact hlvJ
  refine ⟨h1, ?_⟩
  cases hyk : inD (st sp al ts k).D y with
  | false => rfl
  | true =>
    exfalso
    cases hl : (st sp al ts k).S.lv y with
    | none => rw [hl] at h1; cases h1
    | some u =>
      rw [hl, Option.map_some, Option.some.injEq] at h1
      have hspk : lastSp (st sp al ts k).S ≤ k := by
        rcases hinvk.spLt with h | ⟨-, h⟩ <;> omega
      have := hD k hspk (Nat.le_refl _) y hyk u hl
      omega

end

/-! ## The top -/

section

variable {sp : Spec V T} {db : DB V T} {k : Nat}

/-- With a virtual root: a root child reachable at t is a live child of the
root at t, or is reached through root children from one that is, created
later. -/
theorem reach_top_live (hinv : Inv sp db k) (hls : LiveSub sp) (hv : sp.virt = true)
    {n0 : Node V} (h0 : db.P.get? root = some n0) {t : Time} {y : NodeId}
    (hr : Reach sp db.P t y) :
    ∀ my cy, TopAt sp db.P y my cy → ∃ y0 m0 c0, TopAt sp db.P y0 m0 c0 ∧
      y0 ∈ sp.live (n0.hist.upTo t) ∧ cy ≤ c0 ∧ (cy = c0 → y = y0) := by
  have hvi := hinv.vr hv
  induction hr with
  | root n _ => intro my cy hyt; exact absurd rfl hyt.2.1
  | @child x y n m _ hxn hy hym hlt ih =>
    intro my cy hyt
    have hmy : my = m := by have := hyt.1; rw [hym] at this; exact (Option.some.inj this).symm
    subst hmy
    by_cases hxr : x = root
    · subst hxr
      rw [h0] at hxn
      cases hxn
      exact ⟨y, my, cy, hyt, hy, Nat.le_refl _, fun _ => rfl⟩
    · have hxt : isTop sp db.P x = true :=
        isTop_iff.mpr ⟨hxr, n, hxn, Nat.le_trans hyt.2.2.1 (Nat.le_of_lt hlt)⟩
      obtain ⟨nx, cx, hxt'⟩ := hvi.tops x hxt
      have hnx : nx = n := by have := hxt'.1; rw [hxn] at this; exact (Option.some.inj this).symm
      subst hnx
      obtain ⟨y0, m0, c0, h1, h2, h3, -⟩ := ih nx cx hxt'
      have hyp : y ∈ pointees sp nx.hist := mem_pointees_of_live hls hy
      obtain ⟨m', c', hyt', hlt'⟩ := hvi.older x nx cx hxt' y hyp hyt.isTop
      have := hyt.time_unique hyt'
      exact ⟨y0, m0, c0, h1, h2, by omega, fun h => by omega⟩

/-- With a virtual root: the root child that top(k) names, the root's child by
its last entry up to the startup pos s, is reachable at s. -/
theorem reach_top_virt (hinv : Inv sp db k) (hls : LiveSub sp) (hv : sp.virt = true)
    {n0 : Node V} (h0 : db.P.get? root = some n0) {e0 : Entry V}
    (hl : (n0.hist.upTo (lastSp db.S)).getLast? = some e0) {z : NodeId}
    (hz : (sp.ptrs e0.val).head? = some z) : reachable sp db.P (lastSp db.S) z = true := by
  have hvi := hinv.vr hv
  have he0 := List.mem_of_getLast? hl
  obtain ⟨he1, he2⟩ := mem_upTo.mp he0
  obtain ⟨zs, ms, hzt, hval⟩ := hvi.rootEntry n0 h0 e0 he1
  have hzs : z = zs := by
    rw [hval, hvi.rootPtrs] at hz
    simp only [List.head?_cons, Option.some.injEq] at hz
    exact hz.symm
  subst hzs
  -- The root has no entry after e0 up to s.
  have hup : n0.hist.upTo (lastSp db.S) = n0.hist.upTo e0.time := by
    obtain ⟨ys, hys⟩ := List.getLast?_eq_some_iff.mp hl
    have hsorted : (n0.hist.upTo (lastSp db.S)).Pairwise (fun e e' => e.time < e'.time) :=
      (hvi.rootSorted n0 h0).filter _
    rw [hys] at hsorted
    unfold History.upTo
    apply List.filter_congr
    intro e he
    simp only [decide_eq_decide]
    constructor
    · intro hes
      have hmem : e ∈ ys ++ [e0] := by
        rw [← hys]; exact mem_upTo.mpr ⟨he, hes⟩
      rcases List.mem_append.mp hmem with h | h
      · have := (List.pairwise_append.mp hsorted).2.2 _ h e0 (List.mem_singleton_self e0)
        omega
      · rw [List.mem_singleton] at h
        rw [h]
        exact Nat.le_refl _
    · intro h; omega
  -- zs is the root's live child at its creation: no root child points to it.
  obtain ⟨ez, hez, hezt⟩ := hzt.exists_entry
  have hrz := hinv.er z ms hzt.1 ez hez
  rw [hezt, reachable_iff] at hrz
  obtain ⟨y0, m0, c0, h1, h2, h3, h4⟩ := reach_top_live hinv hls hv h0 hrz ms e0.time hzt
  obtain ⟨e', he', hy0⟩ := hls _ _ h2
  obtain ⟨he'1, he'2⟩ := mem_upTo.mp he'
  obtain ⟨z', m', hzt', hval'⟩ := hvi.rootEntry n0 h0 e' he'1
  rw [hval', hvi.rootPtrs, List.mem_singleton] at hy0
  subst hy0
  have := h1.time_unique hzt'
  have hzy : z = y0 := h4 (by omega)
  subst hzy
  have hlvl : ms.level < n0.level := by
    rcases reach_level_root hrz h0 ms hzt.1 with h | h
    · exact absurd h hzt.2.1
    · exact h
  rw [reachable_iff]
  exact Reach.child (Reach.root n0 h0) h0 (by rw [hup]; exact h2) hzt.1 hlvl

/-- Under the conclusion of `latest_st` from e on, with the startup pos of the
last record at e or later: top(k) names a record at c or later. Without a
virtual root, top(k) is the root's latest version, and the root is reachable
at k; with one, the latest version of the root child that the root's last
entry up to s names, reachable at s (`reach_top_virt`). -/
theorem top_ge (hinv : Inv sp db k) (hls : LiveSub sp) {c e : Nat}
    (hes : e ≤ lastSp db.S)
    (hlat : ∀ t x, e ≤ t → t ≤ k → reachable sp db.P t x = true →
      ∀ v, db.S.lv x = some v → c ≤ v.recNo) :
    ∀ R z r, db.S.getLast? = some R → R.top = some (z, r) → c ≤ r := by
  intro R z r hR htop
  rw [hinv.top R hR] at htop
  have hsk : lastSp db.S ≤ k := by rcases hinv.spLt with h | ⟨-, h⟩ <;> omega
  obtain ⟨n0, h0⟩ := Option.isSome_iff_exists.mp hinv.rootIn
  cases hv : sp.virt
  · simp only [topOf, hv, Bool.false_eq_true, ↓reduceIte, Option.map_eq_some_iff,
      Prod.mk.injEq] at htop
    obtain ⟨u, hu, -, rfl⟩ := htop
    have hre : reachable sp db.P k root = true := by
      rw [reachable_iff]; exact Reach.root n0 h0
    exact hlat k root (by omega) (Nat.le_refl _) hre u hu
  · simp only [topOf, hv, ↓reduceIte, topV, h0, Option.bind_some] at htop
    cases hl : (n0.hist.upTo (lastSp db.S)).getLast? with
    | none => rw [hl] at htop; simp at htop
    | some e0 =>
      rw [hl] at htop
      simp only at htop
      cases hz : (sp.ptrs e0.val).head? with
      | none => rw [hz] at htop; simp at htop
      | some z' =>
        rw [hz] at htop
        simp only [Option.map_eq_some_iff, Prod.mk.injEq] at htop
        obtain ⟨u, hu, rfl, rfl⟩ := htop
        exact hlat _ _ hes hsk (reach_top_virt hinv hls hv h0 hl hz) u hu

end

end Contract
