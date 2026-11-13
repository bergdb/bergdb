/-
Proofs for bounds, part 2 (bergdb item 007): T4, the debt of D with the exact
still-dirty test (`DebtByChanges`, SIS/BoundT4.lean). Added 2026-11-13.

The argument, by induction on the level. A node y of D got into D in step 3,
on the access path of the change (or touched), or in step 7: taken and still
dirty. Then the version written for it is not good at some time t, and either
y itself has an entry after the record, or a live child y1 at t has a version
(the latest one after the record, `step_ref_lower`) that is not good at t. A
node whose latest version after T(j) is not good at t has a change below it at
some time τ ≤ t after spIter (lev + 1) j (`debt_main`, part 1): it was created
after j, or it was clean after T(j) and lemma G applies (`Inv.stale_entry`), or
it got into D in step 3 at a time from which on its version was not good, or
in step 7, which is part 2 one level down. A change below the child at τ1 ≤ t
puts the parent on the access path at a time from τ1 to t
(`onAccessPath_lift`).
-/
import SIS.Proof.BoundT4

set_option linter.unusedSectionVars false

namespace SIS

variable {V T : Type} [DecidableEq V]

/-! ### Streams and versions -/

theorem versionAt_of_prefix {S S' : Stream V T} (h : S <+: S') {r : Nat} (hr : r < S.length)
    (y : NodeId) : S'.versionAt r y = S.versionAt r y := by
  obtain ⟨L, rfl⟩ := h
  unfold Stream.versionAt
  rw [List.getElem?_append_left hr]

theorem sext_of_prefix {S S' : Stream V T} (h : S <+: S') : SExt S S' := by
  obtain ⟨L, rfl⟩ := h
  exact SExt.append S L

theorem mem_sectionD_of {S : Stream V T} {x : NodeId} {d : Nat} {R : Record V T}
    (h1 : lastSp S < d) (h2 : d < S.length) (hR : S[d]? = some R) (hx : x ∈ R.gd) :
    (x, d) ∈ sectionD S := by
  rw [sectionD_eq]
  simp only [sectionIdx, List.mem_flatMap, List.mem_range'_1]
  refine ⟨d, ⟨by omega, by omega⟩, ?_⟩
  rw [hR]
  exact List.mem_map.mpr ⟨x, hx, rfl⟩

section Run

variable {sp : Spec V T} {al : Algo V T} {ts : List T}

/-- Record i + 1 of a later state is the record that T(i + 1) appended. -/
theorem st_rec (hok : RunOK sp al ts) (hst : AlgOK sp al) {i j : Nat} (hij : i < j)
    (hj : j ≤ ts.length) :
    (st sp al ts j).S[i + 1]? = some (parts sp al (st sp al ts i) ts[i]).R := by
  have hpre := st_S_prefix sp al ts (j := i + 1) (j' := j) (by omega) hj
  have hlen := st_len sp al ts hok hst (j := i + 1) (by omega)
  obtain ⟨L, hL⟩ := hpre
  rw [← hL, List.getElem?_append_left (by omega), st_S_succ sp al ts (by omega)]
  have hlen' := st_len sp al ts hok hst (j := i) (by omega)
  rw [List.getElem?_append_right (by omega), hlen']
  simp

/-- The startup pos of a state is at most that of a later state. -/
theorem lastSp_st_mono (hok : RunOK sp al ts) (hst : AlgOK sp al) {i j : Nat} (hij : i ≤ j)
    (hj : j ≤ ts.length) : lastSp (st sp al ts i).S ≤ lastSp (st sp al ts j).S := by
  obtain ⟨d, rfl⟩ : ∃ d, j = i + d := ⟨j - i, by omega⟩
  clear hij
  induction d with
  | zero => exact Nat.le_refl _
  | succ d ih =>
    exact Nat.le_trans (ih (by omega)) (lastSp_st_succ hok hst (j := i + d) (by omega))

/-- A good version of a state is good in a later state, at a time up to the
earlier state's; and back (`good_mono` is the forward direction). -/
theorem good_down (hok : RunOK sp al ts) (hst : AlgOK sp al) {d K : Nat} (hdK : d ≤ K)
    (hK : K ≤ ts.length) {t : Time} (ht : t ≤ d) :
    ∀ (b r : Nat) (y : NodeId) (v : Version V), v.level < b →
      (st sp al ts d).S.versionAt r y = some v →
      good sp (st sp al ts K).S (st sp al ts K).P t v = true →
      good sp (st sp al ts d).S (st sp al ts d).P t v = true := by
  have hinvd := inv_st sp al ts hok hst d (by omega)
  have hpre := st_S_prefix sp al ts hdK hK
  have hg := st_grow sp al ts hok hst hdK hK
  intro b
  induction b with
  | zero => intro r y v h; omega
  | succ b ih =>
    intro r y v hb hv hgood
    obtain ⟨hvy, hvr, n, hn, hvh, hvl, -⟩ := hinvd.version_node hv
    rw [good_iff] at hgood ⊢
    obtain ⟨⟨nK, hnK, hh⟩, hc⟩ := hgood
    obtain ⟨nK', hnK', -, -, hhK⟩ := hg y n hn
    rw [hvy, hnK'] at hnK
    cases hnK
    refine ⟨⟨n, by rw [hvy]; exact hn, by rw [hh]; exact upTo_eq_of_le ht hhK⟩, ?_⟩
    intro y1 hy1
    obtain ⟨r1, w, h1, h2, h3, h4⟩ := hc y1 hy1
    have hr1 : r1 ≤ r := hvr ▸ hinvd.ref_le_recNo hv h1
    have hrd : r ≤ d := (version_old_facts hinvd hv).1
    have hlen := hinvd.len
    have h2' : (st sp al ts d).S.versionAt r1 y1 = some w := by
      rw [← versionAt_of_prefix hpre (by omega)]; exact h2
    have hwb : w.level < b := by rw [hvl] at h3; rw [hvl] at hb; omega
    exact ⟨r1, w, h1, h2', h3, ih r1 y1 w hwb h2' h4⟩

/-- A data node never changes after it is created. -/
theorem st_data_const (hok : RunOK sp al ts) (hst : AlgOK sp al) {j : Nat} {y : NodeId}
    {n : Node V} (hn : (st sp al ts j).P.get? y = some n) (hd : n.isData = true) :
    ∀ m, j + m ≤ ts.length → (st sp al ts (j + m)).P.get? y = some n := by
  intro m
  induction m with
  | zero => intro _; exact hn
  | succ m ih =>
    intro hm
    have h0 := ih (by omega)
    rw [show j + (m + 1) = (j + m) + 1 by omega, st_P_succ sp al ts hok hst (by omega),
      get?_apply_of_get? h0]
    have hstep := hok.2 (j + m) (by omega)
    have hadds : addsFor (sp.exec ts[j + m] (j + m + 1) (view sp (st sp al ts (j + m)).P (j + m)))
        (j + m + 1) y = [] := by
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro e he
      rw [mem_addsFor] at he
      have := hstep.dataFixed (y, e.val) he.2 n (by simpa [st] using h0)
      rw [hd] at this; simp at this
    rw [hadds, List.append_nil]

/-- A node that is in a later state but not in an earlier one was created at
some time c in between. -/
theorem st_created {j : Nat} {y : NodeId}
    (hy : (st sp al ts j).P.get? y = none) :
    ∀ m, j + m ≤ ts.length → ((st sp al ts (j + m)).P.get? y).isSome →
      ∃ c, j < c ∧ c ≤ j + m ∧ (st sp al ts (c - 1)).P.get? y = none ∧
        ((st sp al ts c).P.get? y).isSome := by
  intro m
  induction m with
  | zero => intro _ h; rw [Nat.add_zero, hy] at h; simp at h
  | succ m ih =>
    intro hm h
    cases h0 : (st sp al ts (j + m)).P.get? y with
    | some n =>
      obtain ⟨c, h1, h2, h3, h4⟩ := ih (by omega) (by rw [h0]; rfl)
      exact ⟨c, h1, by omega, h3, h4⟩
    | none =>
      refine ⟨j + m + 1, by omega, by omega, ?_, ?_⟩
      · rw [show j + m + 1 - 1 = j + m by omega]; exact h0
      · rw [show j + m + 1 = j + (m + 1) by omega]; exact h

/-! ### The access path -/

/-- The change of transaction T(j + 1) of the run, made on P after T(j). -/
abbrev chg (sp : Spec V T) (al : Algo V T) (ts : List T) (j : Nat) (hj : j < ts.length) :
    Changes V :=
  sp.exec ts[j] (j + 1) (view sp (st sp al ts j).P j)

theorem onAccessPath_intro (hok : RunOK sp al ts) (hst : AlgOK sp al) {j : Nat}
    (hj : j < ts.length) {x : NodeId}
    (h : marked sp (st sp al ts (j + 1)).P (chg sp al ts j hj) (j + 1) x = true ∨
      x ∈ (chg sp al ts j hj).touch) :
    onAccessPath sp al ts (j + 1) x := by
  refine ⟨by omega, ts[j], by simp [List.getElem?_eq_getElem hj], ?_⟩
  show marked sp ((run sp al (ts.take j)).P.apply (j + 1)
      (sp.exec ts[j] (j + 1) (view sp (run sp al (ts.take j)).P j))) _ (j + 1) x = true ∨
    x ∈ (sp.exec ts[j] (j + 1) (view sp (run sp al (ts.take j)).P j)).touch
  have hP : (run sp al (ts.take j)).P.apply (j + 1)
      (sp.exec ts[j] (j + 1) (view sp (run sp al (ts.take j)).P j)) = (st sp al ts (j + 1)).P :=
    (st_P_succ sp al ts hok hst hj).symm
  rw [hP]
  exact h

theorem onAccessPath_elim (hok : RunOK sp al ts) (hst : AlgOK sp al) {τ : Nat} {x : NodeId}
    (h : onAccessPath sp al ts τ x) :
    ∃ j, ∃ (hj : j < ts.length), τ = j + 1 ∧
      (marked sp (st sp al ts (j + 1)).P (chg sp al ts j hj) (j + 1) x = true ∨
        x ∈ (chg sp al ts j hj).touch) := by
  obtain ⟨h0, tr, htr, hm⟩ := h
  obtain ⟨j, rfl⟩ : ∃ j, τ = j + 1 := ⟨τ - 1, by omega⟩
  rw [Nat.add_sub_cancel] at htr hm
  have hj : j < ts.length := by
    rcases Nat.lt_or_ge j ts.length with h | h
    · exact h
    · rw [List.getElem?_eq_none h] at htr; cases htr
  rw [List.getElem?_eq_getElem hj, Option.some.injEq] at htr
  subst htr
  refine ⟨j, hj, rfl, ?_⟩
  have hP : (run sp al (ts.take j)).P.apply (j + 1)
      (sp.exec ts[j] (j + 1) (view sp (run sp al (ts.take j)).P j)) = (st sp al ts (j + 1)).P :=
    (st_P_succ sp al ts hok hst hj).symm
  simp only at hm
  rw [hP] at hm
  exact hm

/-- A node created by T(c) is on the access path of T(c)'s change. -/
theorem onAccessPath_new (hok : RunOK sp al ts) (hst : AlgOK sp al) {j : Nat}
    (hj : j < ts.length) {y : NodeId} (h0 : (st sp al ts j).P.get? y = none)
    (h1 : ((st sp al ts (j + 1)).P.get? y).isSome) : onAccessPath sp al ts (j + 1) y := by
  apply onAccessPath_intro hok hst hj
  left
  have hP := st_P_succ sp al ts hok hst hj
  have hstep : StepOK sp (st sp al ts j).P (j + 1) (chg sp al ts j hj) := by
    show StepOK sp (st sp al ts j).P (j + 1) (sp.exec ts[j] (j + 1) (view sp (st sp al ts j).P j))
    have := hok.2 j hj; simpa [st] using this
  obtain ⟨n1, hn1⟩ := Option.isSome_iff_exists.mp h1
  have hn1' := hn1
  rw [hP, get?_apply, h0, Option.none_or] at hn1'
  cases hnew : newNodeOf (chg sp al ts j hj) y with
  | none => rw [hnew] at hn1'; cases hn1'
  | some m =>
    obtain ⟨nn, hnn, hid, -⟩ := newNodeOf_some hnew
    have hr : reachable sp (st sp al ts (j + 1)).P (j + 1) y = true := by
      rw [hP, ← hid]; exact hstep.newReachable nn hnn
    unfold marked
    rw [hr, hn1]
    simp only [Bool.true_and, List.any_eq_true]
    refine ⟨y, self_mem_reachFrom sp _ _ y n1, ?_⟩
    unfold changed
    simp only [Bool.or_eq_true, List.any_eq_true, beq_iff_eq]
    exact Or.inl ⟨nn, hnn, hid⟩

/-- A node that got dirty in step 3 of T(j + 1) is on the access path of its
change, or touched by it. -/
theorem onAccessPath_gd3 (hok : RunOK sp al ts) (hst : AlgOK sp al) {j : Nat}
    (hj : j < ts.length) {y : NodeId} (hy : y ∈ (parts sp al (st sp al ts j) ts[j]).gd3) :
    onAccessPath sp al ts (j + 1) y := by
  have hinv := inv_st sp al ts hok hst j (by omega)
  have hlen := hinv.len
  have hc : (parts sp al (st sp al ts j) ts[j]).c = chg sp al ts j hj := by
    rw [parts_c, hlen]; rfl
  have hstep : StepOK sp (st sp al ts j).P (j + 1) (parts sp al (st sp al ts j) ts[j]).c := by
    rw [hc]
    show StepOK sp (st sp al ts j).P (j + 1) (sp.exec ts[j] (j + 1) (view sp (st sp al ts j).P j))
    have := hok.2 j hj; simpa [st] using this
  have hP : (parts sp al (st sp al ts j) ts[j]).P = (st sp al ts (j + 1)).P := by
    rw [st_succ sp al ts hj]; rfl
  obtain ⟨-, hidx, hD, hw, hdt⟩ := (step_gd3_mem' sp al _ _ hok.1 hinv hstep y).mp hy
  apply onAccessPath_intro hok hst hj
  rcases hdt with hd | ht
  · left
    rw [← step_marked_iff sp al _ _ hok.1 hinv hstep hidx hD hw, hP, hc] at hd
    exact hd
  · right; rw [← hc]; exact ht

/-! ### D: entries stay until taken; a node of D is not written -/

/-- An entry of D after T(j) was in D after every T(i) from its own on. -/
theorem st_D_persist (hok : RunOK sp al ts) (hst : AlgOK sp al) {i j : Nat} (hij : i ≤ j)
    (hj : j ≤ ts.length) {y : NodeId} {d : Nat} (hD : (y, d) ∈ (st sp al ts j).D) (hdi : d ≤ i) :
    (y, d) ∈ (st sp al ts i).D := by
  have hinvj := inv_st sp al ts hok hst j hj
  have hinvi := inv_st sp al ts hok hst i (by omega)
  rw [hinvj.inv1] at hD
  obtain ⟨hs, hdl, R, hR, hyR⟩ := sectionD_mem hD
  rw [hinvi.inv1]
  have hpre := st_S_prefix sp al ts hij hj
  have hli := hinvi.len
  have hR' : (st sp al ts i).S[d]? = some R := by
    obtain ⟨L, hL⟩ := hpre
    rw [← hL, List.getElem?_append_left (by omega)] at hR
    exact hR
  exact mem_sectionD_of (Nat.lt_of_le_of_lt (lastSp_st_mono hok hst hij hj) hs) (by omega) hR' hyR

/-- A node of D after T(j), with d(x) = d, has no version in the records
after R(d): it is not taken while it is in D. -/
theorem st_D_not_written (hok : RunOK sp al ts) (hst : AlgOK sp al) {j : Nat}
    (hj : j ≤ ts.length) {y : NodeId} {d : Nat} (hD : (y, d) ∈ (st sp al ts j).D) {r : Nat}
    (hdr : d < r) (hrj : r ≤ j) : (st sp al ts j).S.versionAt r y = none := by
  obtain ⟨i, rfl⟩ : ∃ i, r = i + 1 := ⟨r - 1, by omega⟩
  have hi : i < ts.length := by omega
  have hinvj := inv_st sp al ts hok hst j hj
  have hinvi := inv_st sp al ts hok hst i (by omega)
  have hlen := hinvi.len
  have hDi := st_D_persist hok hst (i := i) (by omega) hj hD (by omega)
  have hsj := (sectionD_mem (hinvj.inv1 ▸ hD)).1
  have hstep : StepOK sp (st sp al ts i).P (i + 1) (parts sp al (st sp al ts i) ts[i]).c := by
    have hc : (parts sp al (st sp al ts i) ts[i]).c = chg sp al ts i hi := by rw [parts_c, hlen]; rfl
    rw [hc]
    show StepOK sp (st sp al ts i).P (i + 1) (sp.exec ts[i] (i + 1) (view sp (st sp al ts i).P i))
    have := hok.2 i hi; simpa [st] using this
  unfold Stream.versionAt
  rw [st_rec hok hst (i := i) (j := j) (by omega) hj]
  simp only
  rw [List.find?_eq_none]
  intro u hu hux
  simp only [beq_iff_eq] at hux
  have hmem : y ∈ (parts sp al (st sp al ts i) ts[i]).vs.map (·.node) := by
    rw [← hux]; exact List.mem_map_of_mem (by rw [parts_R] at hu; exact hu)
  rw [step_vs_nodes] at hmem
  rcases List.mem_append.mp hmem with h | h
  · have := (step_dataIds_spec sp al _ _ hinvi hstep (List.mem_filter.mp h).1).1
    have hidx := hinvi.dIndex (y, d) hDi
    rw [isIndex, this] at hidx
    simp at hidx
  · obtain ⟨d', hd', hle⟩ := (step_taken_mem sp al _ _ y).mp (List.mem_filter.mp h).1
    rcases (step_D1_mem sp al _ _ hlen _).mp hd' with h1 | ⟨h1, -⟩
    · have := mem_of_nodup_keys hinvi.dNodup hDi h1
      subst this
      have hs : (parts sp al (st sp al ts i) ts[i]).s = lastSp (st sp al ts (i + 1)).S := by
        rw [st_succ sp al ts hi, step_S, step_lastSp]
      have hmono := lastSp_st_mono hok hst (i := i + 1) (j := j) (by omega) hj
      omega
    · simp only at h1
      have := step_s_le sp al _ ts[i] hlen
      omega

/-- A node that got dirty in step 3 of T(i + 1) has no version in R(i + 1). -/
theorem st_gd3_not_written (hok : RunOK sp al ts) (hst : AlgOK sp al) {i j : Nat} (hij : i < j)
    (hj : j ≤ ts.length) (hi : i < ts.length) {y : NodeId}
    (hy : y ∈ (parts sp al (st sp al ts i) ts[i]).gd3) :
    (st sp al ts j).S.versionAt (i + 1) y = none := by
  have hinvi := inv_st sp al ts hok hst i (by omega)
  have hlen := hinvi.len
  have hstep : StepOK sp (st sp al ts i).P (i + 1) (parts sp al (st sp al ts i) ts[i]).c := by
    have hc : (parts sp al (st sp al ts i) ts[i]).c = chg sp al ts i hi := by rw [parts_c, hlen]; rfl
    rw [hc]
    show StepOK sp (st sp al ts i).P (i + 1) (sp.exec ts[i] (i + 1) (view sp (st sp al ts i).P i))
    have := hok.2 i hi; simpa [st] using this
  obtain ⟨-, hidx, hD, -, -⟩ := (step_gd3_mem' sp al _ _ hok.1 hinvi hstep y).mp hy
  unfold Stream.versionAt
  rw [st_rec hok hst (i := i) (j := j) hij hj]
  simp only
  rw [List.find?_eq_none]
  intro u hu hux
  simp only [beq_iff_eq] at hux
  have hmem : y ∈ (parts sp al (st sp al ts i) ts[i]).vs.map (·.node) := by
    rw [← hux]; exact List.mem_map_of_mem (by rw [parts_R] at hu; exact hu)
  rw [step_vs_nodes] at hmem
  rcases List.mem_append.mp hmem with h | h
  · obtain ⟨-, n, hn, hdn⟩ := step_dataIds_spec sp al _ _ hinvi hstep (List.mem_filter.mp h).1
    rw [isIndex, hn] at hidx
    simp [hdn] at hidx
  · obtain ⟨d', hd', hle⟩ := (step_taken_mem sp al _ _ y).mp (List.mem_filter.mp h).1
    rcases (step_D1_mem sp al _ _ hlen _).mp hd' with h1 | ⟨h1, -⟩
    · have : inD (st sp al ts i).D y = true := (inD_iff _ _).mpr ⟨d', h1⟩
      rw [hD] at this; cases this
    · simp only at h1
      have := step_s_le sp al _ ts[i] hlen
      omega

/-- Two streams, one a prefix of the other, with no version of y in the
longer one's other records, have the same latest version of y. -/
theorem lv_of_prefix_none {S S' : Stream V T} (h : S <+: S') {y : NodeId}
    (hn : ∀ r, S.length ≤ r → S'.versionAt r y = none) : S'.lv y = S.lv y := by
  apply lv_congr_node
  intro r
  rcases Nat.lt_or_ge r S.length with hr | hr
  · exact versionAt_of_prefix h hr y
  · rw [hn r hr]
    unfold Stream.versionAt
    rw [List.getElem?_eq_none hr]

end Run

/-! ### The version written for a taken node refers to the latest versions -/

section Step

variable (sp : Spec V T) (al : Algo V T) (db : DB V T) (tr : T)

/-- The version that T(k + 1) writes for a taken node x names, for each
pointee on a lower level, its latest version after T(k + 1): versions are
written lowest level first. -/
theorem step_ref_lower {k : Nat} (hinv : Inv sp db k)
    (hstep : StepOK sp db.P (k + 1) (parts sp al db tr).c) {x : NodeId}
    (hx : x ∈ (parts sp al db tr).taken) :
    ∃ vx, (Snew sp al db tr).lv x = some vx ∧ vx.recNo = k + 1 ∧
      ∀ y ∈ pointees sp vx.hist, lvlOf (parts sp al db tr).P y < lvlOf (parts sp al db tr).P x →
        vx.ref? y = ((Snew sp al db tr).lv y).map (·.recNo) := by
  have hlen := hinv.len
  obtain ⟨pre, post, hsplit, -, -, -, hpost⟩ := step_taken_split sp al db tr hinv hx
  obtain ⟨nx, hnx⟩ := Option.isSome_iff_exists.mp
    (isSome_of_isIndex (step_taken_index sp al db tr hinv hx))
  obtain ⟨wpre, hwpre⟩ : ∃ w, w = writeAll sp db.S (k + 1) (parts sp al db tr).P pre
      (parts sp al db tr).vs0 := ⟨_, rfl⟩
  obtain ⟨vx, hvx⟩ : ∃ v, v = mkVersion sp (db.S.building wpre) (k + 1) x nx := ⟨_, rfl⟩
  have hvs : (parts sp al db tr).vs =
      writeAll sp db.S (k + 1) (parts sp al db tr).P post (wpre ++ [vx]) := by
    rw [parts_vs, hlen, hsplit, writeAll_split sp _ _ _ hnx, ← hwpre, ← hvx]
  have hpre_vs : wpre ++ [vx] <+: (parts sp al db tr).vs := by
    rw [hvs]; exact writeAll_prefix sp _ _ _ _ _
  have hvx_mem : vx ∈ (parts sp al db tr).vs := hpre_vs.subset (by simp)
  have hnodup := step_vs_nodup sp al db tr hinv hstep
  have hvxnode : vx.node = x := by rw [hvx]; rfl
  have hlvx : (Snew sp al db tr).lv x = some vx := by
    rw [← hvxnode]; exact lv_Snew_written sp al db tr hnodup hvx_mem
  refine ⟨vx, hlvx, by rw [hvx]; rfl, ?_⟩
  intro y hy hlt
  have hyx : y ≠ x := by intro h; subst h; omega
  obtain ⟨rest, hrest⟩ := hpre_vs
  have hrest_nodes : ∀ u ∈ rest, u.node ∈ post := by
    have h1 := writeAll_nodes sp db.S (k + 1) (parts sp al db tr).P post (wpre ++ [vx])
    rw [← hvs, ← hrest, List.map_append] at h1
    have h2 := List.append_cancel_left h1
    intro u hu
    have : u.node ∈ rest.map (·.node) := List.mem_map_of_mem hu
    rw [h2] at this
    exact (List.mem_filter.mp this).1
  have href : vx.ref? y = ((db.S.building wpre).lv y).map (·.recNo) := by
    have hy' : y ∈ pointees sp nx.hist := by rw [hvx] at hy; exact hy
    rw [hvx, ref?_mkVersion]
    simp only [hy', ↓reduceIte]
  rw [href]
  congr 1
  unfold Snew
  rw [lv_building, lv_append]
  have hR : Stream.lv [(parts sp al db tr).R] y =
      (parts sp al db tr).vs.find? (fun v => v.node == y) := by
    simp only [Stream.lv, List.reverse_singleton, List.findSome?_singleton, parts_R]
  rw [hR, ← hrest, List.find?_append, List.find?_append]
  have hvxf : [vx].find? (fun v => v.node == y) = none := by
    simp only [List.find?_cons, List.find?_nil, hvxnode]
    have : (x == y) = false := by simp; exact fun h => hyx h.symm
    simp [this]
  have hrestf : rest.find? (fun v => v.node == y) = none := by
    rw [List.find?_eq_none]
    intro u hu h
    have hpu := hpost u.node (hrest_nodes u hu)
    simp only [beq_iff_eq] at h
    rw [h] at hpu
    omega
  rw [hvxf, hrestf]
  simp

end Step

/-! ### From a child's access path to its parent's -/

section Lift

variable {sp : Spec V T} {al : Algo V T} {ts : List T}

/-- If a live child y1 of y at t is on the access path of the change of T(τ1),
τ1 ≤ t, then y is on the access path of the change of some T(τ), τ1 ≤ τ ≤ t:
y has an entry from τ1 to t (its own change), or y1 was its child already at
τ1 - 1 and τ1, and then y was reachable then with the change below it, or
touched (`StepOK.touchUp`). -/
theorem onAccessPath_lift (hok : RunOK sp al ts) (hst : AlgOK sp al) (hv : sp.virt = false)
    {K : Nat} (hK : K ≤ ts.length) {y : NodeId} {ny : Node V} {t : Nat} (htK : t ≤ K)
    (hyr : reachable sp (st sp al ts K).P t y = true) (hny : (st sp al ts K).P.get? y = some ny)
    {y1 : NodeId} (hy1 : y1 ∈ sp.live (ny.hist.upTo t)) {τ1 : Nat} (hτ1 : τ1 ≤ t)
    (hap : onAccessPath sp al ts τ1 y1) :
    ∃ τ, τ1 ≤ τ ∧ τ ≤ t ∧ onAccessPath sp al ts τ y := by
  obtain ⟨j, hj, rfl, hm⟩ := onAccessPath_elim hok hst hap
  by_cases hex : ∃ e ∈ ny.hist, j < e.time ∧ e.time ≤ t
  · obtain ⟨e, he, h1, h2⟩ := hex
    obtain ⟨τ, h3, h4, h5⟩ := onAccessPath_of_below hok hst hK htK hyr hny
      (self_mem_reachFrom sp _ t y ny) hny he (by omega) h2
    exact ⟨τ, by omega, h4, h5⟩
  · have hls : LiveSub sp := hok.1.liveSub
    have hupj : ny.hist.upTo j = ny.hist.upTo t :=
      upTo_eq_of_none_between ny.hist (by omega) (fun e he h => hex ⟨e, he, h⟩)
    have hupj1 : ny.hist.upTo (j + 1) = ny.hist.upTo t :=
      upTo_eq_of_none_between ny.hist (by omega) (fun e he h => hex ⟨e, he, by omega, h.2⟩)
    have hy1j : y1 ∈ sp.live (ny.hist.upTo j) := by rw [hupj]; exact hy1
    obtain ⟨e0, he0, hy1e0⟩ := hls _ _ hy1j
    have hKj : j + (K - j) = K := by omega
    obtain ⟨n0, hn0, he0'⟩ := st_entry_back hok hst (τ := j) (K - j) (by omega) y ny
      (by rw [hKj]; exact hny) e0 (mem_upTo.mp he0).1 (mem_upTo.mp he0).2
    have hinvj := inv_st sp al ts hok hst j (by omega)
    have hgjK := st_grow sp al ts hok hst (j := j) (j' := K) (by omega) hK
    obtain ⟨nyK, hnyK, -, -, hh0⟩ := hgjK y n0 hn0
    rw [hny, Option.some.injEq] at hnyK
    subst hnyK
    obtain ⟨m0, hm0, hlt0⟩ := hinvj.ptrs y n0 hn0 e0 he0' y1 hy1e0
    have hy1n0 : y1 ∈ sp.live (n0.hist.upTo j) := by rw [← hh0]; exact hy1j
    have hryj : reachable sp (st sp al ts j).P j y = true :=
      reach_back_st hok hst (j1 := j) (j := K) hK (t - j) t (by omega) htK y hyr (by rw [hn0]; rfl)
    rcases hm with hm | htouch
    · refine ⟨j + 1, Nat.le_refl _, hτ1, onAccessPath_intro hok hst hj (Or.inl ?_)⟩
      have hgj1 := st_grow sp al ts hok hst (j := j) (j' := j + 1) (by omega) (by omega)
      obtain ⟨n1, hn1, hl1, -, -⟩ := hgj1 y n0 hn0
      obtain ⟨m1, hm1, hml1, -, -⟩ := hgj1 y1 m0 hm0
      have hg1K := st_grow sp al ts hok hst (j := j + 1) (j' := K) (by omega) hK
      obtain ⟨n1K, hn1K, -, -, hh1K⟩ := hg1K y n1 hn1
      rw [hny, Option.some.injEq] at hn1K
      subst hn1K
      have hryj1 : reachable sp (st sp al ts (j + 1)).P (j + 1) y = true :=
        reach_back_st hok hst (j1 := j + 1) (j := K) hK (t - (j + 1)) t (by omega) htK y hyr
          (by rw [hn1]; rfl)
      have hy1n1 : y1 ∈ sp.live (n1.hist.upTo (j + 1)) := by rw [← hh1K, hupj1]; exact hy1
      unfold marked at hm ⊢
      rw [hryj1, hn1]
      rw [hm1] at hm
      simp only [Bool.true_and, Bool.and_eq_true, List.any_eq_true] at hm ⊢
      obtain ⟨-, z, hz, hcz⟩ := hm
      exact ⟨z, reachFrom_child_sub sp hy1n1 hm1 (by rw [hml1, hl1]; exact hlt0) z hz, hcz⟩
    · have hstep : StepOK sp (st sp al ts j).P (j + 1) (chg sp al ts j hj) := by
        show StepOK sp (st sp al ts j).P (j + 1) (sp.exec ts[j] (j + 1) (view sp (st sp al ts j).P j))
        have := hok.2 j hj; simpa [st] using this
      have h := hstep.touchUp y1 htouch y n0
      simp only [Nat.add_sub_cancel] at h
      rcases h hryj hn0 (reachFrom_child_sub sp hy1n0 hm0 hlt0 y1 (self_mem_reachFrom sp _ j y1 m0))
        with h | ⟨hvt, -⟩
      · exact ⟨j + 1, Nat.le_refl _, hτ1, onAccessPath_intro hok hst hj (Or.inr h)⟩
      · rw [hv] at hvt; cases hvt

end Lift

/-! ### The induction on the level -/

section Main

variable {sp : Spec V T} {al : Algo V T} {ts : List T}

theorem levelOf_of_get {P : Struct V} {x : NodeId} {n : Node V} (h : P.get? x = some n) :
    levelOf P x = n.level := by
  simp [levelOf, h]

/-- The induction (exact test, no virtual root), in the state after T(K).

1. A node y reachable at t ≤ K whose latest version after T(j), j ≤ K, is not
   good at t (or that has none) is on the access path of the change of some
   T(τ), spIter (lev y + 1) j < τ ≤ t.
2. A node y taken by T(i + 1), i < K, whose version written then is not good at
   t ≤ K, while reachable at t, is on the access path of the change of some
   T(τ), spIter (lev y) (i + 1) < τ ≤ t.

Both for the nodes on levels below b, by induction on b: 2 for y uses 1 for its
children, and 1 for y uses 2 for y. -/
theorem debt_main (hok : RunOK sp al ts) (hst : AlgOK sp al) (hv : sp.virt = false) {K : Nat} (hK : K ≤ ts.length) : ∀ b,
    (∀ y, levelOf (st sp al ts K).P y < b → ∀ j ≤ K, ∀ t ≤ K,
      reachable sp (st sp al ts K).P t y = true →
      (∀ v, (st sp al ts j).S.lv y = some v →
        good sp (st sp al ts K).S (st sp al ts K).P t v = false) →
      ∃ τ, spIter (st sp al ts K).S (levelOf (st sp al ts K).P y + 1) j < τ ∧ τ ≤ t ∧
        onAccessPath sp al ts τ y) ∧
    (∀ y, levelOf (st sp al ts K).P y < b → ∀ i (hi : i < ts.length), i < K →
      y ∈ (parts sp al (st sp al ts i) ts[i]).taken →
      ∀ v, (st sp al ts (i + 1)).S.lv y = some v → ∀ t ≤ K,
      reachable sp (st sp al ts K).P t y = true →
      good sp (st sp al ts K).S (st sp al ts K).P t v = false →
      ∃ τ, spIter (st sp al ts K).S (levelOf (st sp al ts K).P y) (i + 1) < τ ∧ τ ≤ t ∧
        onAccessPath sp al ts τ y) := by
  have hls : LiveSub sp := hok.1.liveSub
  have hinvK := inv_st sp al ts hok hst K hK
  have hle := spAt_st_le hok hst hK
  have hmono := spAt_st_mono hok hst hK
  intro b
  induction b with
  | zero => exact ⟨fun y h => by omega, fun y h => by omega⟩
  | succ b ih =>
    -- Part 2 first.
    have part2 : ∀ y, levelOf (st sp al ts K).P y < b + 1 → ∀ i (hi : i < ts.length), i < K →
        y ∈ (parts sp al (st sp al ts i) ts[i]).taken →
        ∀ v, (st sp al ts (i + 1)).S.lv y = some v → ∀ t ≤ K,
        reachable sp (st sp al ts K).P t y = true →
        good sp (st sp al ts K).S (st sp al ts K).P t v = false →
        ∃ τ, spIter (st sp al ts K).S (levelOf (st sp al ts K).P y) (i + 1) < τ ∧ τ ≤ t ∧
          onAccessPath sp al ts τ y := by
      intro y hyb i hi hiK hyt v hv1 t htK hyr hng
      obtain ⟨ny, hny⟩ := Option.isSome_iff_exists.mp ((reachable_iff _ _ _ _).mp hyr).isSome
      have hlev := levelOf_of_get hny
      have hinvi := inv_st sp al ts hok hst i (by omega)
      have hinv1 := inv_st sp al ts hok hst (i + 1) (by omega)
      have hleni := hinvi.len
      have hstep : StepOK sp (st sp al ts i).P (i + 1) (parts sp al (st sp al ts i) ts[i]).c := by
        have hc : (parts sp al (st sp al ts i) ts[i]).c = chg sp al ts i hi := by
          rw [parts_c, hleni]; rfl
        rw [hc]
        show StepOK sp (st sp al ts i).P (i + 1) (sp.exec ts[i] (i + 1) (view sp (st sp al ts i).P i))
        have := hok.2 i hi; simpa [st] using this
      obtain ⟨vx, hlvx, hrec, href⟩ := step_ref_lower sp al _ _ hinvi hstep hyt
      have hSn : Snew sp al (st sp al ts i) ts[i] = (st sp al ts (i + 1)).S := by
        rw [st_succ sp al ts hi]; rfl
      have hPn : (parts sp al (st sp al ts i) ts[i]).P = (st sp al ts (i + 1)).P := by
        rw [st_succ sp al ts hi]; rfl
      rw [hSn] at hlvx href
      rw [hPn] at href
      rw [hlvx, Option.some.injEq] at hv1
      subst hv1
      have hpre1K := st_S_prefix sp al ts (j := i + 1) (j' := K) (by omega) hK
      have hv1at : (st sp al ts (i + 1)).S.versionAt (i + 1) y = some vx := by
        have := hinv1.lv_at hlvx; rw [hrec] at this; exact this
      have hvK : (st sp al ts K).S.versionAt (i + 1) y = some vx := versionAt_prefix hpre1K hv1at
      obtain ⟨hvnode, -, n, hn, hvh, hvl, -⟩ := hinvK.version_node hvK
      rw [hny, Option.some.injEq] at hn
      subst hn
      by_cases hexe : ∃ e ∈ ny.hist, i + 1 < e.time ∧ e.time ≤ t
      · obtain ⟨e, he, h1, h2⟩ := hexe
        obtain ⟨τ, h3, h4, h5⟩ := onAccessPath_of_below hok hst hK htK hyr hny
          (self_mem_reachFrom sp _ t y ny) hny he (by omega) h2
        have := spIter_le (st sp al ts K).S K hle (levelOf (st sp al ts K).P y) (i + 1) (by omega)
        exact ⟨τ, by omega, h4, h5⟩
      · have hvn : vx.hist.upTo t = ny.hist.upTo t := by
          rw [hvh]
          by_cases hti : t ≤ i + 1
          · exact upTo_upTo _ hti
          · rw [upTo_upTo' _ (by omega)]
            exact upTo_eq_of_none_between ny.hist (by omega) (fun e he h => hexe ⟨e, he, h⟩)
        have hng' : ¬ (good sp (st sp al ts K).S (st sp al ts K).P t vx = true) := by
          rw [hng]; simp
        rw [good_iff] at hng'
        obtain ⟨y1, hy1, hy1f⟩ : ∃ y1 ∈ sp.live (vx.hist.upTo t), ¬ ∃ r w, vx.ref? y1 = some r ∧
            (st sp al ts K).S.versionAt r y1 = some w ∧ w.level < vx.level ∧
            good sp (st sp al ts K).S (st sp al ts K).P t w = true := by
          apply Classical.byContradiction
          intro hcon
          apply hng'
          refine ⟨⟨ny, by rw [hvnode]; exact hny, hvn⟩, fun w hw => ?_⟩
          apply Classical.byContradiction
          intro h
          exact hcon ⟨w, hw, h⟩
        have hy1n : y1 ∈ sp.live (ny.hist.upTo t) := by rw [← hvn]; exact hy1
        obtain ⟨e1, he1, hy1e1⟩ := hls _ _ hy1
        have hyp : y1 ∈ pointees sp vx.hist :=
          (mem_pointees sp _ y1).mpr ⟨e1, (mem_upTo.mp he1).1, hy1e1⟩
        -- The node of y in P after T(i + 1), and y1 below it.
        obtain ⟨-, -, n1, hn1, hvh1, hvl1, -⟩ := hinv1.version_node hv1at
        have he1n1 : e1 ∈ n1.hist := by
          have := (mem_upTo.mp he1).1
          rw [hvh1] at this
          exact (mem_upTo.mp this).1
        obtain ⟨m1, hm1, hlt1⟩ := hinv1.ptrs y n1 hn1 e1 he1n1 y1 hy1e1
        have hlvl : lvlOf (st sp al ts (i + 1)).P y1 < lvlOf (st sp al ts (i + 1)).P y := by
          simp [lvlOf, hm1, hn1, hlt1]
        have hr1 := href y1 hyp hlvl
        have hg1K := st_grow sp al ts hok hst (j := i + 1) (j' := K) (by omega) hK
        obtain ⟨m, hm, hml, -, -⟩ := hg1K y1 m1 hm1
        obtain ⟨n1K, hn1K, hnl, -, -⟩ := hg1K y n1 hn1
        rw [hny, Option.some.injEq] at hn1K
        subst hn1K
        have hltK : m.level < ny.level := by rw [hml, hnl]; exact hlt1
        have hr1t : reachable sp (st sp al ts K).P t y1 = true := by
          rw [reachable_iff] at hyr ⊢
          exact Reach.child hyr hny hy1n hm hltK
        have hlev1 := levelOf_of_get hm
        obtain ⟨τ1, hτa, hτb, hap1⟩ := (ih).1 y1 (by rw [hlev1]; rw [hlev] at hyb; omega) (i + 1)
          (by omega) t htK hr1t (by
            intro w hw
            cases hgw : good sp (st sp al ts K).S (st sp al ts K).P t w with
            | false => rfl
            | true =>
              exfalso
              apply hy1f
              have hwat := hinv1.lv_at hw
              obtain ⟨-, -, m1', hm1', -, hwl, -⟩ := hinv1.version_node hwat
              rw [hm1, Option.some.injEq] at hm1'
              subst hm1'
              refine ⟨w.recNo, w, by rw [hr1, hw]; rfl, versionAt_prefix hpre1K hwat, ?_, hgw⟩
              rw [hwl, hvl]; omega)
        obtain ⟨τ, h1, h2, h3⟩ := onAccessPath_lift hok hst hv hK htK hyr hny hy1n hτb hap1
        refine ⟨τ, ?_, h2, h3⟩
        have hanti := spIter_anti (st sp al ts K).S K hle hmono (i + 1) (by omega)
          (ny.level - (m.level + 1)) (m.level + 1)
        rw [show m.level + 1 + (ny.level - (m.level + 1)) = ny.level by omega] at hanti
        rw [hlev]
        rw [hlev1] at hτa
        omega
    refine ⟨?_, part2⟩
    -- Part 1.
    intro y hyb j hjK t htK hyr hH
    obtain ⟨ny, hny⟩ := Option.isSome_iff_exists.mp ((reachable_iff _ _ _ _).mp hyr).isSome
    have hlev := levelOf_of_get hny
    have hinvj := inv_st sp al ts hok hst j (by omega)
    have hlenj := hinvj.len
    have hpreK := st_S_prefix sp al ts hjK hK
    have hgjK := st_grow sp al ts hok hst hjK hK
    have hsle := spIter_le (st sp al ts K).S K hle (levelOf (st sp al ts K).P y + 1) j hjK
    cases hPj : (st sp al ts j).P.get? y with
    | none =>
      obtain ⟨c, hjc, hcK, hc0, hc1⟩ := st_created hPj (K - j) (by omega)
        (by rw [show j + (K - j) = K by omega, hny]; rfl)
      obtain ⟨c', rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
      rw [Nat.add_sub_cancel] at hc0
      have hap := onAccessPath_new hok hst (j := c') (by omega) hc0 hc1
      have hct : c' + 1 ≤ t := by
        apply Nat.lt_of_not_le
        intro htc
        have hinvt := inv_st sp al ts hok hst t (by omega)
        have hgtK := st_grow sp al ts hok hst (j := t) (j' := K) htK hK
        rw [reachable_grow hls hinvt.ptrs hinvt.rootIn hgtK (Nat.le_refl _)] at hyr
        obtain ⟨nt, hnt⟩ := Option.isSome_iff_exists.mp ((reachable_iff _ _ _ _).mp hyr).isSome
        obtain ⟨nc, hnc, -⟩ := st_grow sp al ts hok hst (j := t) (j' := c') htc (by omega) y nt hnt
        rw [hc0] at hnc; cases hnc
      exact ⟨c' + 1, by omega, hct, hap⟩
    | some nj =>
      cases hdata : nj.isData
      · -- An index node.
        have hidx : isIndex (st sp al ts j).P y = true := by simp [isIndex, hPj, hdata]
        cases hD : inD (st sp al ts j).D y
        · -- Not in D: clean after T(j); lemma G.
          have hcl : dirty sp (st sp al ts j).S (st sp al ts j).P j y = false := by
            cases hc : dirty sp (st sp al ts j).S (st sp al ts j).P j y
            · rfl
            · have := hinvj.inv2 y hidx (by simp [written, hv]) hc
              rw [hD] at this; cases this
          rw [dirty_false_iff] at hcl
          obtain ⟨v, hlv, hgood⟩ := hcl
          have hngv := hH v hlv
          have hSext := sext_of_prefix hpreK
          by_cases htj : t ≤ j
          · exfalso
            rw [reachable_grow hls hinvj.ptrs hinvj.rootIn hgjK htj] at hyr
            have := good_mono' sp hSext hgjK htj (hgood t htj hyr)
            rw [hngv] at this; cases this
          · have hrj : reachable sp (st sp al ts j).P j y = true :=
              reach_back_st hok hst (j1 := j) (j := K) hK (t - j) t (by omega) htK y hyr
                (by rw [hPj]; rfl)
            have hgj := good_mono' sp hSext hgjK (Nat.le_refl _) (hgood j (Nat.le_refl _) hrj)
            have hvj := hinvj.lv_at hlv
            have hvK := versionAt_prefix hpreK hvj
            have hρ : v.recNo ≤ j := (version_old_facts hinvj hvj).1
            obtain ⟨z, hz, nz, hnz, e, he, h1, h2⟩ := hinvK.stale_entry (ny.level + 1) v.recNo y v ny
              (by omega) hvK hny j t hρ (by omega) hgj hngv
            obtain ⟨τ, h3, h4, h5⟩ := onAccessPath_of_below hok hst hK htK hyr hny hz hnz he
              (by omega) h2
            exact ⟨τ, by omega, h4, h5⟩
        · -- In D, with d(y) = i + 1.
          obtain ⟨d, hd⟩ := (inD_iff _ _).mp hD
          have hd' := hd
          rw [hinvj.inv1] at hd'
          obtain ⟨hsd, hdl, R, hR, hyR⟩ := sectionD_mem hd'
          obtain ⟨i, rfl⟩ : ∃ i, d = i + 1 := ⟨d - 1, by omega⟩
          have hi : i < ts.length := by omega
          rw [st_rec hok hst (i := i) (j := j) (by omega) (by omega), Option.some.injEq] at hR
          subst hR
          rw [parts_R] at hyR
          have hsj : lastSp (st sp al ts j).S = spAt (st sp al ts K).S j :=
            (spAt_st hok hst hK hjK).symm
          have hsplit : spIter (st sp al ts K).S (levelOf (st sp al ts K).P y + 1) j =
              spIter (st sp al ts K).S (levelOf (st sp al ts K).P y) (spAt (st sp al ts K).S j) := rfl
          rcases List.mem_append.mp hyR with hg3 | hr7
          · -- Got dirty in step 3 of T(i + 1): on its access path, at a time up to t.
            have hap := onAccessPath_gd3 hok hst (j := i) hi hg3
            have hit : i + 1 ≤ t := by
              apply Nat.lt_of_not_le
              intro hti
              have hrt : reachable sp (st sp al ts j).P t y = true := by
                rw [reachable_grow hls hinvj.ptrs hinvj.rootIn hgjK (by omega)] at hyr; exact hyr
              cases hlv : (st sp al ts j).S.lv y with
              | none =>
                have := hinvj.inv4 y (i + 1) hd hlv t (by omega)
                rw [hrt] at this; cases this
              | some v =>
                have hvj := hinvj.lv_at hlv
                have hρ : v.recNo ≤ j := (version_old_facts hinvj hvj).1
                have hlt : v.recNo < i + 1 := by
                  apply Nat.lt_of_not_le
                  intro hge
                  rcases Nat.lt_or_ge (i + 1) v.recNo with h | h
                  · rw [st_D_not_written hok hst (by omega) hd h hρ] at hvj; cases hvj
                  · have : v.recNo = i + 1 := by omega
                    rw [this, st_gd3_not_written hok hst (i := i) (j := j) (by omega) (by omega) hi hg3]
                      at hvj
                    cases hvj
                rcases hinvj.inv3 y (i + 1) v hd hlv with h | h
                · omega
                · have := good_mono' sp (sext_of_prefix hpreK) hgjK (by omega) (h t (by omega) hrt)
                  rw [hH v hlv] at this; cases this
            have h1 := spIter_le (st sp al ts K).S K hle (levelOf (st sp al ts K).P y)
              (spAt (st sp al ts K).S j) (by have := hle j hjK; omega)
            exact ⟨i + 1, by omega, hit, hap⟩
          · -- Taken by T(i + 1) and still dirty: part 2.
            have hleni := (inv_st sp al ts hok hst i (by omega)).len
            have hyt : y ∈ (parts sp al (st sp al ts i) ts[i]).taken :=
              (step_r7_shape sp al (st sp al ts i) ts[i] hleni).2.subset hr7
            have hpre1 := st_S_prefix sp al ts (j := i + 1) (j' := j) (by omega) (by omega)
            have hlen1 := (inv_st sp al ts hok hst (i + 1) (by omega)).len
            have hlvj : (st sp al ts j).S.lv y = (st sp al ts (i + 1)).S.lv y := by
              apply lv_of_prefix_none hpre1
              intro r hr
              rw [hlen1] at hr
              rcases Nat.lt_or_ge j r with h | h
              · unfold Stream.versionAt
                rw [List.getElem?_eq_none (by omega)]
              · exact st_D_not_written hok hst (by omega) hd (by omega) h
            cases hlv1 : (st sp al ts (i + 1)).S.lv y with
            | none =>
              exfalso
              have hstep : StepOK sp (st sp al ts i).P (i + 1)
                  (parts sp al (st sp al ts i) ts[i]).c := by
                have hc : (parts sp al (st sp al ts i) ts[i]).c = chg sp al ts i hi := by
                  rw [parts_c, hleni]; rfl
                rw [hc]
                show StepOK sp (st sp al ts i).P (i + 1)
                  (sp.exec ts[i] (i + 1) (view sp (st sp al ts i).P i))
                have := hok.2 i hi; simpa [st] using this
              obtain ⟨vx, hlvx, -⟩ := step_ref_lower sp al _ _ (inv_st sp al ts hok hst i (by omega))
                hstep hyt
              have hSn : Snew sp al (st sp al ts i) ts[i] = (st sp al ts (i + 1)).S := by
                rw [st_succ sp al ts hi]; rfl
              rw [hSn, hlv1] at hlvx
              cases hlvx
            | some u =>
              have hngu := hH u (by rw [hlvj, hlv1])
              obtain ⟨τ, h1, h2, h3⟩ := part2 y hyb i hi (by omega) hyt u hlv1 t htK hyr hngu
              have hm := spIter_mono (st sp al ts K).S K hle hmono (levelOf (st sp al ts K).P y)
                (spAt (st sp al ts K).S j) (i + 1) (by omega) (by omega)
              exact ⟨τ, by omega, h2, h3⟩
      · -- A data node: its version is good.
        exfalso
        obtain ⟨v, hlv, hvh⟩ := hinvj.dataV y nj hPj hdata
        have hnK := st_data_const hok hst hPj hdata (K - j) (by omega)
        rw [show j + (K - j) = K by omega] at hnK
        have hvnode := (hinvj.version_node (hinvj.lv_at hlv)).1
        have := good_data sp (st sp al ts K).S (st sp al ts K).P t hnK hls
          (hinvj.data y nj hPj hdata) hvnode hvh
        rw [hH v hlv] at this; cases this

/-- T4, the debt of D, with the exact still-dirty test and no virtual root. -/
theorem debtByChanges_exact (sp : Spec V T) (al : Algo V T) (ts : List T) (hok : RunOK sp al ts)
    (hex : al.stillDirty = exactTest sp) (hv : sp.virt = false) : DebtByChanges sp al ts := by
  have hst : AlgOK sp al := algOK_of sp al (Or.inr ⟨hv, hex⟩)
  have hls : LiveSub sp := hok.1.liveSub
  have hK : ts.length ≤ ts.length := Nat.le_refl _
  have hinvK := inv_st sp al ts hok hst ts.length hK
  have hle := spAt_st_le hok hst hK
  have hmono := spAt_st_mono hok hst hK
  show ∀ e ∈ (run sp al ts).D, ∃ τ,
    spIter (run sp al ts).S (levelOf (run sp al ts).P e.1 + 1) ts.length < τ ∧ τ ≤ ts.length ∧
      onAccessPath sp al ts τ e.1
  rw [← st_length sp al ts]
  rintro ⟨x, d⟩ hxd
  simp only
  have hd' := hxd
  rw [hinvK.inv1] at hd'
  obtain ⟨hsd, hdl, R, hR, hxR⟩ := sectionD_mem hd'
  obtain ⟨i, rfl⟩ : ∃ i, d = i + 1 := ⟨d - 1, by omega⟩
  have hlenK := hinvK.len
  have hi : i < ts.length := by omega
  rw [st_rec hok hst (i := i) (j := ts.length) (by omega) hK, Option.some.injEq] at hR
  subst hR
  rw [parts_R] at hxR
  have hsK : lastSp (st sp al ts ts.length).S = spAt (st sp al ts ts.length).S ts.length :=
    (spAt_st hok hst hK (Nat.le_refl _)).symm
  have hsplit : spIter (st sp al ts ts.length).S (levelOf (st sp al ts ts.length).P x + 1) ts.length =
      spIter (st sp al ts ts.length).S (levelOf (st sp al ts ts.length).P x)
        (spAt (st sp al ts ts.length).S ts.length) := rfl
  rcases List.mem_append.mp hxR with hg3 | hr7
  · have h1 := spIter_le (st sp al ts ts.length).S ts.length hle
      (levelOf (st sp al ts ts.length).P x) (spAt (st sp al ts ts.length).S ts.length)
      (by have := hle ts.length hK; omega)
    exact ⟨i + 1, by omega, by omega, onAccessPath_gd3 hok hst hi hg3⟩
  · have hinvi := inv_st sp al ts hok hst i (by omega)
    have hleni := hinvi.len
    have hinv1 := inv_st sp al ts hok hst (i + 1) (by omega)
    have hstep : StepOK sp (st sp al ts i).P (i + 1) (parts sp al (st sp al ts i) ts[i]).c := by
      have hc : (parts sp al (st sp al ts i) ts[i]).c = chg sp al ts i hi := by
        rw [parts_c, hleni]; rfl
      rw [hc]
      show StepOK sp (st sp al ts i).P (i + 1) (sp.exec ts[i] (i + 1) (view sp (st sp al ts i).P i))
      have := hok.2 i hi; simpa [st] using this
    rw [step_r7 sp al _ _ hex hleni] at hr7
    obtain ⟨hxt, hdirty⟩ := List.mem_filter.mp hr7
    obtain ⟨vx, hlvx, hrec, -⟩ := step_ref_lower sp al _ _ hinvi hstep hxt
    have hSn : Snew sp al (st sp al ts i) ts[i] = (st sp al ts (i + 1)).S := by
      rw [st_succ sp al ts hi]; rfl
    have hPn : (parts sp al (st sp al ts i) ts[i]).P = (st sp al ts (i + 1)).P := by
      rw [st_succ sp al ts hi]; rfl
    rw [hSn] at hlvx hdirty
    rw [hPn] at hdirty
    -- Where x is dirty after T(i + 1): a time t, reachable, its version not good.
    obtain ⟨t, ht, hrt, hng⟩ : ∃ t ≤ i + 1, reachable sp (st sp al ts (i + 1)).P t x = true ∧
        good sp (st sp al ts (i + 1)).S (st sp al ts (i + 1)).P t vx = false := by
      apply Classical.byContradiction
      intro hno
      have : dirty sp (st sp al ts (i + 1)).S (st sp al ts (i + 1)).P (i + 1) x = false := by
        rw [dirty_false_iff]
        refine ⟨vx, hlvx, fun t ht hr => ?_⟩
        cases hg : good sp (st sp al ts (i + 1)).S (st sp al ts (i + 1)).P t vx
        · exact absurd ⟨t, ht, hr, hg⟩ hno
        · rfl
      rw [hdirty] at this; cases this
    have hinv1 := inv_st sp al ts hok hst (i + 1) (by omega)
    have hg1K := st_grow sp al ts hok hst (j := i + 1) (j' := ts.length) (by omega) hK
    have hrK : reachable sp (st sp al ts ts.length).P t x = true := by
      rw [reachable_grow hls hinv1.ptrs hinv1.rootIn hg1K ht]; exact hrt
    have hngK : good sp (st sp al ts ts.length).S (st sp al ts ts.length).P t vx = false := by
      cases hg : good sp (st sp al ts ts.length).S (st sp al ts ts.length).P t vx
      · rfl
      · have := good_down hok hst (d := i + 1) (K := ts.length) (by omega) hK ht (vx.level + 1)
          vx.recNo x vx (by omega) (hinv1.lv_at hlvx) hg
        rw [hng] at this; cases this
    obtain ⟨τ, h1, h2, h3⟩ := (debt_main hok hst hv hK (levelOf (st sp al ts ts.length).P x + 1)).2
      x (by omega) i hi (by omega) hxt vx hlvx t (by omega) hrK hngK
    have hm := spIter_mono (st sp al ts ts.length).S ts.length hle hmono
      (levelOf (st sp al ts ts.length).P x) (spAt (st sp al ts ts.length).S ts.length) (i + 1)
      (by omega) (by omega)
    exact ⟨τ, by omega, by omega, h3⟩

end Main

end SIS
