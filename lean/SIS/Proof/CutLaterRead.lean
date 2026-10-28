/-
Proofs about reclaim, part 17 (bergdb item 001, WP R5, T12 with eviction):
reads in the states after a restart from a stream at whose state a cut at c is
safe. With `NInv`, a read at a time from the first available time on follows
only versions that the state of the last startup may read (`ReadsPhys`), or
versions written after it; so it gives the same on the streams cut at c (the
last startup's and the current one) as on the whole streams. So does the
writer's walk.
-/
import SIS.Proof.CutLater
import SIS.Proof.CutRuns

set_option linter.unusedSectionVars false

namespace SIS

variable {V T : Type} [DecidableEq V]

/-! ## Reachability back to the last startup -/

section Back

variable {sp : Spec V T} {al : Algo V T} {ts : List T}

/-- A5 for a run: a node reachable at i + 1 after T(i + 1) was reachable at i
after T(i), or did not exist then. -/
theorem st_noRes (hok : RunOK sp al ts) (hst : AlgOK sp al) {i : Nat} (hi : i < ts.length) (x : NodeId)
    (hr : reachable sp (st sp al ts (i + 1)).P (i + 1) x = true) :
    reachable sp (st sp al ts i).P i x = true ∨ (st sp al ts i).P.get? x = none := by
  have hinv := inv_st sp al ts hok hst i (by omega)
  have hstep : StepOK sp (st sp al ts i).P (i + 1) (sp.exec ts[i] (i + 1) (view sp (st sp al ts i).P i)) :=
    hok.2 i hi
  have hc : (parts sp al (st sp al ts i) ts[i]).c = sp.exec ts[i] (i + 1) (view sp (st sp al ts i).P i) := by
    rw [parts_c, hinv.len, Nat.add_sub_cancel]
  have hP : (st sp al ts (i + 1)).P = (st sp al ts i).P.apply (i + 1)
      (sp.exec ts[i] (i + 1) (view sp (st sp al ts i).P i)) := by
    rw [st_succ sp al ts hi]
    show (parts sp al (st sp al ts i) ts[i]).P = _
    rw [parts_P' sp al _ _ hinv.len, hc]
  rw [hP] at hr
  rcases hstep.noRes x hr with h | h
  · left; simpa using h
  · right
    obtain ⟨nn, hnn, hid⟩ := List.mem_map.mp h
    rw [← hid]
    exact hstep.fresh nn hnn

/-- A node reachable at a time t from j1 on, in a state after T(j) with j1 ≤ t
≤ j, that exists after T(j1), was reachable at j1 after T(j1). -/
theorem reach_back_st (hok : RunOK sp al ts) (hst : AlgOK sp al) {j1 j : Nat} (hj : j ≤ ts.length) :
    ∀ d t, t = j1 + d → t ≤ j → ∀ x, reachable sp (st sp al ts j).P t x = true →
      ((st sp al ts j1).P.get? x).isSome → reachable sp (st sp al ts j1).P j1 x = true := by
  have hls : LiveSub sp := hok.1.liveSub
  intro d
  induction d with
  | zero =>
    intro t ht htj x hr _
    have ht' : t = j1 := by omega
    rw [ht'] at hr htj
    have hinv1 := inv_st sp al ts hok hst j1 (by omega)
    have hg := st_grow sp al ts hok hst (j := j1) (j' := j) htj hj
    rw [reachable_grow hls hinv1.ptrs hinv1.rootIn hg (Nat.le_refl _)] at hr
    exact hr
  | succ d ih =>
    intro t ht htj x hr hx
    have hinvt := inv_st sp al ts hok hst t (by omega)
    have hg := st_grow sp al ts hok hst (j := t) (j' := j) htj hj
    rw [reachable_grow hls hinvt.ptrs hinvt.rootIn hg (Nat.le_refl _)] at hr
    have ht1 : t = (j1 + d) + 1 := by omega
    rw [ht1] at hr
    rcases st_noRes hok hst (i := j1 + d) (by omega) x hr with h | h
    · exact ih (j1 + d) rfl (by omega) x
        (by
          have hinvd := inv_st sp al ts hok hst (j1 + d) (by omega)
          have hgd := st_grow sp al ts hok hst (j := j1 + d) (j' := j) (by omega) hj
          rw [reachable_grow hls hinvd.ptrs hinvd.rootIn hgd (Nat.le_refl _)]
          exact h) hx
    · exfalso
      have hg1 := st_grow sp al ts hok hst (j := j1) (j' := j1 + d) (by omega) (by omega)
      obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp hx
      obtain ⟨n', hn', -⟩ := hg1 x n hn
      rw [h] at hn'; cases hn'


/-- The state after the last startup's (db1, after T(j1)) and a later one (db,
after T(j)) of one run. -/
structure Later (sp : Spec V T) (db1 db : DB V T) (j1 j : Nat) : Prop where
  inv1 : Inv sp db1 j1
  inv : Inv sp db j
  le : j1 ≤ j
  pre : db1.S <+: db.S
  fa1 : lastFa db1.S ≤ lastSp db1.S
  /-- A node reachable at t later, that exists at j1, was reachable at the
  earlier of t and j1. -/
  reach : ∀ t x, t ≤ j → reachable sp db.P t x = true → (db1.P.get? x).isSome →
    reachable sp db1.P (min t j1) x = true

theorem later_st (hok : RunOK sp al ts) (hst : AlgOK sp al) {j1 j : Nat} (h1 : j1 ≤ j) (hj : j ≤ ts.length) :
    Later sp (st sp al ts j1) (st sp al ts j) j1 j where
  inv1 := inv_st sp al ts hok hst j1 (by omega)
  inv := inv_st sp al ts hok hst j hj
  le := h1
  pre := st_S_prefix sp al ts h1 hj
  fa1 := st_fa_le sp al ts (k := j1) (by omega)
  reach := by
    intro t x htj hr hx
    rcases Nat.lt_or_ge j1 t with ht | ht
    · rw [Nat.min_eq_right (by omega)]
      exact reach_back_st hok hst hj (t - j1) t (by omega) htj x hr hx
    · rw [Nat.min_eq_left ht]
      have hinv1 := inv_st sp al ts hok hst j1 (by omega)
      have hg := st_grow sp al ts hok hst (j := j1) (j' := j) h1 hj
      rw [reachable_grow hok.1.liveSub hinv1.ptrs hinv1.rootIn hg ht] at hr
      exact hr

end Back

/-! ## Rule R and the loader of the last startup on a cut stream -/

section CutS0

variable {sp : Spec V T} {S0 S : Stream V T} {c s : Nat}

theorem ruleRRef_cut (h : c ≤ s) (y : NodeId) (r : Option Nat) :
    ruleRRef (cutStream c S0) s y r = ruleRRef S0 s y r := by
  unfold ruleRRef; rw [newest_cut h]

end CutS0

/-! ## The versions that a later read may follow -/

section Safe

variable {sp : Spec V T} {db1 db : DB V T} {j1 j : Nat}

/-- A version that a read at t in the later state may follow: one that the
last startup's state may read at the earlier of t and j1, or one written after
the last startup's stream. -/
def LaterOK (sp : Spec V T) (db1 : DB V T) (j1 : Nat) (t : Time) (w : Version V) : Prop :=
  ReadsPhys sp db1.S db1.P db1.D (min t j1) w ∨ db1.S.length ≤ w.recNo

/-- A version that `LaterOK` allows is at a cut that is safe at the last
startup's state, or later. -/
theorem LaterOK.ge (hL : Later sp db1 db j1 j) {c : Nat} (hcut : CutOK sp c db1 j1) {t : Time}
    (hft : lastFa db1.S ≤ t) {w : Version V} (hw : LaterOK sp db1 j1 t w) : c ≤ w.recNo := by
  have hfs : lastFa db1.S ≤ j1 := by
    have h1 := hL.inv1.spLt
    have h2 := hL.fa1
    omega
  rcases hw with hw | hw
  · exact hcut.2.1 (min t j1) w (Nat.le_min.mpr ⟨hft, hfs⟩) (Nat.min_le_right _ _) hw
  · have := hL.inv1.len
    have := hcut.1
    omega

/-- A record that `VOK` allows names, for a node reachable at t, a version
that `LaterOK` allows. -/
theorem Later.VOK_ok (hL : Later sp db1 db j1 j) {t : Time} (ht : t ≤ j) {z : NodeId}
    (hz : reachable sp db.P t z = true) {r : Nat} (hr : VOK db1.S z r) {w : Version V}
    (hw : db.S.versionAt r z = some w) : LaterOK sp db1 j1 t w := by
  rcases hr with hr | hr
  · left
    cases hl : db1.S.lv z with
    | none => rw [hl] at hr; cases hr
    | some u =>
      rw [hl, Option.map_some, Option.some.injEq] at hr
      subst hr
      have hu := hL.inv1.lv_at hl
      rw [versionAt_prefix hL.pre hu, Option.some.injEq] at hw
      subst hw
      obtain ⟨-, -, n, hn, -⟩ := hL.inv1.version_node hu
      exact ReadsPhys.latest z u (hL.reach t z ht hz (by rw [hn]; rfl)) hl
  · right
    rw [(hL.inv.version_node hw).2.1]
    exact hr


/-- A version that `ReadsPhys` gives is a version of the stream. -/
theorem Inv.readsPhys_version {sp : Spec V T} {db : DB V T} {k : Nat} (hinv : Inv sp db k) {t : Time}
    {w : Version V} (hw : ReadsPhys sp db.S db.P db.D t w) : ∃ r, db.S.versionAt r w.node = some w := by
  induction hw with
  | latest x v _ hv =>
    have h := hinv.lv_at hv
    rw [← (hinv.version_node h).1] at h
    exact ⟨_, h⟩
  | child v y w _ _ hf _ =>
    rcases hf with hf | ⟨-, r, hr, -⟩
    · obtain ⟨-, r, hr⟩ := follow_spec hf
      rw [← (hinv.version_node hr).1] at hr
      exact ⟨r, hr⟩
    · rw [← (hinv.version_node hr).1] at hr
      exact ⟨r, hr⟩

/-- For a version of S0, the loader's Rule R (S0's) on its reference gives the
version that a lookup follows. -/
theorem Later.follow_of_ruleRRef (hL : Later sp db1 db j1 j) {v : Version V} {x : NodeId} {r0 : Nat}
    (hv : db1.S.versionAt r0 x = some v) {s : Nat} {z : NodeId} {r' : Nat} {w : Version V}
    (h1 : ruleRRef db1.S s z (v.ref? z) = some r') (h2 : db.S.versionAt r' z = some w) :
    follow db1.S s true z (v.ref? z) = some w := by
  unfold ruleRRef at h1
  unfold follow
  cases hn : newest db1.S s z with
  | some u =>
    simp only [↓reduceIte]
    rw [hn] at h1
    have hlv := newest_lv hn
    have hu := hL.inv1.lv_at hlv
    have hwu : db.S.versionAt u.recNo z = some u := versionAt_prefix hL.pre hu
    have hr' : r' = u.recNo := by
      cases hr : v.ref? z with
      | none =>
        rw [hr] at h1
        simp only [Option.some.injEq] at h1
        exact h1.symm
      | some r1 =>
        rw [hr] at h1
        simp only at h1
        obtain ⟨u1, hu1⟩ := hL.inv1.ref_versionAt hv hr
        obtain ⟨v2, hv2, hle⟩ := hL.inv1.le_lv hu1
        rw [hlv, Option.some.injEq] at hv2
        subst hv2
        split at h1
        · simp only [Option.some.injEq] at h1
          exact h1.symm
        · simp only [Option.some.injEq] at h1
          omega
    subst hr'
    rw [hwu, Option.some.injEq] at h2
    rw [h2]
  | none =>
    simp only [↓reduceIte]
    rw [hn] at h1
    simp only at h1
    obtain ⟨u1, hu1⟩ := hL.inv1.ref_versionAt hv h1
    rw [h1, Option.bind_some, hu1]
    rw [versionAt_prefix hL.pre hu1] at h2
    exact h2

/-- A reference of a version written after the last startup's stream names a
pointee's latest version in that stream, or a record after it. -/
theorem Later.ref_VOK_new (hL : Later sp db1 db j1 j) {r : Nat} {x : NodeId} {v : Version V}
    (hv : db.S.versionAt r x = some v) (hr : db1.S.length ≤ r) {z : NodeId} {r0 : Nat}
    (h : v.ref? z = some r0) : VOK db1.S z r0 := by
  obtain ⟨R, hR, hvR, -⟩ := versionAt_spec hv
  obtain ⟨pre, hpre, href⟩ := hL.inv.ref r R hR v hvR
  rw [href z] at h
  split at h
  · rw [lv_building] at h
    cases hf : pre.find? (fun u => u.node == z) with
    | some u =>
      rw [hf, Option.some_or, Option.map_some, Option.some.injEq] at h
      subst h
      right
      have hu : u ∈ R.vers := hpre.subset (List.mem_of_find?_eq_some hf)
      rw [hL.inv.recNo r R hR u hu]
      exact hr
    | none =>
      rw [hf, Option.none_or] at h
      cases hl : Stream.lv (db.S.take r) z with
      | none => rw [hl] at h; cases h
      | some u =>
        rw [hl, Option.map_some, Option.some.injEq] at h
        subst h
        by_cases hlt : u.recNo < db1.S.length
        · left
          -- z has no version in R(|S0|), ..., R(r - 1): its latest one in S0 is u.
          obtain ⟨r2, hr2, hlast⟩ := (lv_eq_some_iff _ z u).mp hl
          rw [versionAt_take] at hr2
          split at hr2
          · have hr2' := (hL.inv.version_node hr2).2.1
            have htake : db1.S = (db.S.take r).take db1.S.length := by
              rw [List.take_take, Nat.min_eq_left hr]
              exact List.prefix_iff_eq_take.mp hL.pre
            have hnone : ∀ r', db1.S.length ≤ r' → Stream.versionAt (db.S.take r) r' z = none := by
              intro r' hr'
              exact hlast r' (by omega)
            rw [htake, lv_take hnone, hl]
            rfl
          · cases hr2
        · right; omega
  · cases h


/-- What the loader makes of a snapshot's reference, Rule R'd, is a version
that `LaterOK` allows, when the snapshot's version is. -/
theorem Later.own_ok (hL : Later sp db1 db j1 j) {t : Time} (ht : t ≤ j) {r : Nat} {y : NodeId}
    {w : Version V} (hw : db.S.versionAt r y = some w) (hok : LaterOK sp db1 j1 t w)
    {z : NodeId} (hz : z ∈ sp.live (w.hist.upTo t)) (hrz : reachable sp db.P t z = true)
    {r' : Nat} (h1 : ruleRRef db1.S (lastSp db1.S) z (w.ref? z) = some r') {w' : Version V}
    (h2 : db.S.versionAt r' z = some w') : LaterOK sp db1 j1 t w' := by
  rcases hok with hrp | hnew
  · -- a version of the last startup's stream: the follow of a lookup
    left
    obtain ⟨r1, hr1⟩ := hL.inv1.readsPhys_version hrp
    have hf := hL.follow_of_ruleRRef hr1 h1 h2
    refine ReadsPhys.child w z w' hrp ?_ (Or.inl hf)
    rcases Nat.lt_or_ge j1 t with htj | htj
    · rw [Nat.min_eq_right (by omega)]
      obtain ⟨-, hrr, n, -, hvh, -⟩ := hL.inv1.version_node hr1
      have hlt := versionAt_lt_length hr1
      have hlen := hL.inv1.len
      have hall : ∀ e ∈ w.hist, e.time ≤ j1 := by
        intro e he
        rw [hvh] at he
        have := (mem_upTo.mp he).2
        omega
      rw [upTo_of_forall _ _ hall]
      rw [upTo_of_forall _ _ (fun e he => Nat.le_trans (hall e he) (by omega))] at hz
      exact hz
    · rw [Nat.min_eq_left htj]; exact hz
  · -- a version written after it: its references name latest versions
    have hwr := (hL.inv.version_node hw).2.1
    cases hz' : w.ref? z with
    | none =>
      rw [hz'] at h1
      exact hL.VOK_ok ht hrz (ruleRRef_none_VOK h1) h2
    | some r0 =>
      rw [hz'] at h1
      have hV := hL.ref_VOK_new hw (by rw [← hwr]; exact hnew) hz'
      rw [hL.inv.ruleRRef_VOK hL.pre _ hV, Option.some.injEq] at h1
      subst h1
      exact hL.VOK_ok ht hrz hV h2

end Safe

/-! ## The slots that a later read follows -/

section Slots

variable {sp : Spec V T} {db1 db : DB V T} {j1 j : Nat} {m : Mem V}


end Slots

/-! ## The reader's follow, and reads, in a later state on the cut streams -/

section Reader

variable {sp : Spec V T} {db1 db : DB V T} {j1 j : Nat} {m : Mem V}

end Reader


/-! ## The writer's walk in a later state on the cut streams -/

section Walk

variable {sp : Spec V T} {db1 db : DB V T} {j1 j : Nat} {m : Mem V}

end Walk

end SIS
