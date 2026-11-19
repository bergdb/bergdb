/-
The contract package (bergdb 030-23, section 5.2): the proofs for GIS-J's
clauses (Contract/ReclaimGis.lean), in the abstract model's words.

A version of z that is good for a time t' at or after e leads below z to a
good version of every node below z at t', each in a record at or before its
own (`Inv.good_below`). Every node below z at e is below z at t' too, unless
a node on the way got an entry after e; a version good for t' holds that
entry, so it is in a record after e. So a version good for t' is at c ≤ e or
later if a data node below its node at e has all its versions at c or later
(`good_ge_below`).

A node of D whose latest version was not put back at its record got dirty by
the marking or the touch: it was reachable just before, and clean, so its
latest version was good then, and stays good for that time later
(`dirty_good`).
-/
import SIS.ReclaimTheorems
import SIS.Proof.CutHist
import Contract.Proof.ReclaimScheme

namespace Contract

open SIS

variable {V T : Type} [DecidableEq V]

section

variable {sp : Spec V T} {db : DB V T} {k : Nat}

/-- In a state with the invariant: a version v of node z at record r, good for
a time t' at or after e, is at c or later if c ≤ e and some node below z at e
has all its versions at c or later. Each step down follows a live child at e;
if z's live children are the same at t', the version's reference for that
child names a good version at or before r (`good_iff`, `Inv.ref_le_recNo`);
if not, z got an entry after e and up to t', which v holds, so r > e. -/
theorem good_ge_below (hinv : Inv sp db k) {c e t' : Nat} (hce : c ≤ e) (het : e ≤ t') :
    ∀ (b : Nat) (z : NodeId) (n : Node V) (r : Nat) (v : Version V), n.level < b →
      db.P.get? z = some n → db.S.versionAt r z = some v → good sp db.S db.P t' v = true →
      ∀ d ∈ reachFrom sp db.P e z n, (∀ r' u, db.S.versionAt r' d = some u → c ≤ r') →
        c ≤ r := by
  intro b
  induction b with
  | zero => intro z n r v h; omega
  | succ b ih =>
    intro z n r v hb hz hv hg d hd hdc
    obtain ⟨hvz, -, nv, hnv, hvh, -, -⟩ := hinv.version_node hv
    rw [hz, Option.some.injEq] at hnv
    subst hnv
    have hg' := (good_iff sp _ _ _ _).mp hg
    obtain ⟨⟨n', hn', hh⟩, hc⟩ := hg'
    rw [hvz, hz, Option.some.injEq] at hn'
    subst hn'
    rw [reachFrom_eq] at hd
    simp only [List.mem_cons, List.mem_flatMap] at hd
    rcases hd with rfl | ⟨y, hy, hd⟩
    · exact hdc r v hv
    · split at hd
      · rename_i m hm
        split at hd
        · rename_i hlt
          by_cases hup : n.hist.upTo e = n.hist.upTo t'
          · -- z's live children are the same at e and t'.
            have hy' : y ∈ sp.live (v.hist.upTo t') := by rw [hh, ← hup]; exact hy
            obtain ⟨r1, w1, h1, h2, -, h4⟩ := hc y hy'
            have hle : r1 ≤ r := hinv.ref_le_recNo hv h1
            have := ih y m r1 w1 (by omega) hm h2 h4 d hd hdc
            omega
          · -- z got an entry after e and up to t', which v holds.
            have hex : ∃ en ∈ n.hist, e < en.time ∧ en.time ≤ t' := by
              apply Classical.byContradiction
              intro hne
              apply hup
              unfold History.upTo
              apply List.filter_congr
              intro en hen
              simp only [decide_eq_decide]
              constructor
              · intro h; omega
              · intro h
                by_cases h' : en.time ≤ e
                · exact h'
                · exact absurd ⟨en, hen, by omega, h⟩ hne
            obtain ⟨en, hen, he1, he2⟩ := hex
            have h1 : en ∈ v.hist.upTo t' := by rw [hh]; exact mem_upTo.mpr ⟨hen, he2⟩
            rw [hvh] at h1
            have := (mem_upTo.mp (mem_upTo.mp h1).1).2
            omega
        · simp at hd
      · simp at hd

end

section

variable {sp : Spec V T} {al : Algo V T} {ts : List T}

/-- A node x of D after T(k), with index d, whose latest version w was not put
back at its record, got dirty at d by the marking or the touch (Rule A would
have written it at d, and it is not written after d): x is reachable at d - 1,
was clean then, and w is its latest version then, so w is good for d - 1, in
the state after T(d - 1) and so in the state after T(k). -/
theorem dirty_good (hok : RunOK sp al ts) (hj : al.stillDirty = javaTest sp)
    (hmk : al.mark = true) {k : Nat} (hk : k ≤ ts.length) {x : NodeId} {d : Nat}
    (hd : (x, d) ∈ (st sp al ts k).D) {w : Version V} (hw : (st sp al ts k).S.lv x = some w)
    (hwD : (x, w.recNo) ∉ (st sp al ts k).D) :
    ∃ j, j + 1 = d ∧ reachable sp (st sp al ts k).P j x = true ∧
      good sp (st sp al ts k).S (st sp al ts k).P j w = true := by
  have hst : AlgOK sp al := algOK_of sp al (Or.inl hj)
  have hls : LiveSub sp := hok.1.liveSub
  have hinvk := inv_st sp al ts hok hst k hk
  have hsec : (x, d) ∈ sectionD (st sp al ts k).S := by rw [← hinvk.inv1]; exact hd
  obtain ⟨hsd, hdl, R, hR, hxR⟩ := sectionD_mem hsec
  have hlen := hinvk.len
  have hxi : isIndex (st sp al ts k).P x = true := hinvk.dIndex _ hd
  obtain ⟨j, rfl⟩ : ∃ j, d = j + 1 := ⟨d - 1, by omega⟩
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
  rcases List.mem_append.mp hxR with hg | hr7
  · -- Marked or touched at j + 1: reachable at j and clean then.
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
    obtain ⟨-, -, n, hn, -, -, -⟩ := hinvj.version_node hwj
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
    obtain ⟨v, hv, hgv⟩ := hinvj.clean_good hls hxD hxw (Nat.le_refl j) hre
    rw [hlvj, Option.some.injEq] at hv
    subst hv
    have hgk := st_grow sp al ts hok hst (j := j) (j' := k) (by omega) hk
    refine ⟨j, rfl, ?_, ?_⟩
    · rw [reachable_grow hls hinvj.ptrs hinvj.rootIn hgk (Nat.le_refl j)]
      exact hre
    · exact good_mono' sp (sext_of_prefix (st_S_prefix sp al ts (by omega) hk)) hgk
        (Nat.le_refl j) hgv
  · -- Put back by Rule A at j + 1: written then and not after, so w is at j + 1.
    exfalso
    have htk := (step_r7_shape sp al _ _ hinvj.len).2.subset hr7
    obtain ⟨u, hu, hux⟩ := (step_written_iff sp al _ _ hinvj hstep x).mpr (Or.inr htk)
    have hver : (st sp al ts (j + 1)).S.versionAt (j + 1) x = some u := by
      rw [st_S_succ sp al ts hjl]
      have := versionAt_snoc_self (st sp al ts j).S (parts sp al (st sp al ts j) ts[j]).R x
      rw [hinvj.len] at this
      rw [this]
      exact find?_node_of_mem (step_vs_nodup sp al _ _ hinvj hstep) hu hux
    have hge := st_lv_ge hok hst hjk hk hver hw
    have hsk1 := lastSp_st_mono hok hst (i := j + 1) (j := k) hjk hk
    have hxD1 : (x, j + 1) ∈ (st sp al ts (j + 1)).D := by
      rw [hinv1.inv1]
      refine mem_sectionD_of (R := (parts sp al (st sp al ts j) ts[j]).R) (by omega)
        (by rw [hinv1.len]; omega) ?_ (by rw [hgd]; exact hxR)
      rw [st_succ sp al ts hjl, step_S, ← hinvj.len]
      exact Snew_getElem?_new sp al _ _
    have hxnone : ∀ r', j + 2 ≤ r' → (st sp al ts k).S.versionAt r' x = none := by
      intro r' hr'
      cases hv' : (st sp al ts k).S.versionAt r' x with
      | none => rfl
      | some u' =>
        exfalso
        have hr'k := hvk hv'
        obtain ⟨d, hd, hds⟩ := written_inD hok hst hk (J := j + 1) (by omega) (by omega) hr'k hv'
          (Or.inl hxi)
        have h1 := mem_of_nodup_keys hinv1.dNodup hd hxD1
        have h2 := lastSp_st_mono hok hst (i := r') (j := k) hr'k hk
        omega
    have hwa := hinvk.lv_at hw
    have hwr : w.recNo = j + 1 := by
      by_cases h : j + 2 ≤ w.recNo
      · rw [hxnone _ h] at hwa
        cases hwa
      · omega
    rw [hwr] at hwD
    exact hwD hd

end

end Contract
