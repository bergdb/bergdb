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
