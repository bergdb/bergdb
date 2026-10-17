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

theorem reached4_cutS0 {m : Mem V} (h : c ≤ m.s) (hp : Nat) (y : NodeId) :
    m.reached4 sp (cutStream c S0) S hp y = m.reached4 sp S0 S hp y := by
  unfold Mem.reached4; simp only [ruleRRef_cut h]

theorem follow4_cutS0 {m : Mem V} (h : c ≤ m.s) (hp : Nat) (y : NodeId) (w : Bool) :
    m.follow4 sp (cutStream c S0) S hp y w = m.follow4 sp S0 S hp y w := by
  rw [follow4_eq, follow4_eq, reached4_cutS0 h]

end CutS0

/-! ## The versions that a later read may follow -/

section Safe

variable {sp : Spec V T} {db1 db : DB V T} {j1 j : Nat}

/-- A version that a read at t in the later state may follow: one that the
last startup's state may read at the earlier of t and j1, or one written after
the last startup's stream. -/
def LaterOK (sp : Spec V T) (db1 : DB V T) (j1 : Nat) (t : Time) (w : Version V) : Prop :=
  ReadsPhys sp db1.S db1.P db1.D (min t j1) w ∨ db1.S.length ≤ w.recNo

/-- Object h, of node y, can be read at t: canonical, or a snapshot of a
version that `LaterOK` allows. -/
def LaterSafeT (sp : Spec V T) (db1 : DB V T) (j1 : Nat) (db : DB V T) (m : Mem V) (t : Time) (h : Nat)
    (y : NodeId) : Prop :=
  ∃ o, m.obj? h = some o ∧ o.node = y ∧
    (o.canonical = true ∨ ∃ r w, o.pos = some r ∧ db.S.versionAt r y = some w ∧ LaterOK sp db1 j1 t w)

/-- A slot for y that a read at t may follow: to an object that can be read
so, or a stream slot that the loader turns into y's canonical object, or into a
version that `LaterOK` allows. -/
def SlotLaterT (sp : Spec V T) (S0 : Stream V T) (db1 : DB V T) (j1 : Nat) (db : DB V T) (m : Mem V)
    (t : Time) (y : NodeId) : Slot → Prop
  | Slot.mem h' => LaterSafeT sp db1 j1 db m t h' y
  | Slot.stream r => m.canonicalOf y ≠ none ∨
      ∀ r' w, ruleRRef S0 m.s y r = some r' → db.S.versionAt r' y = some w → LaterOK sp db1 j1 t w

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

/-- A slot for z that `SlotVOK` allows, of a node reachable at t: as a later
read needs it. -/
theorem Later.slotVOK (hL : Later sp db1 db j1 j) (hm : EInv sp db db1.S j m) {t : Time} (ht : t ≤ j)
    {h : Nat} {o : Obj V} (ho : m.obj? h = some o) {z : NodeId} {sl : Slot} (hsl : o.slot? z = some sl)
    (hrz : reachable sp db.P t z = true) (ha : SlotVOK db1.S m z sl) :
    SlotLaterT sp db1.S db1 j1 db m t z sl := by
  cases sl with
  | mem h' =>
    obtain ⟨o', ho', hn'⟩ := hm.slotsNode h o ho z h' hsl
    cases hc' : o'.canonical with
    | true => exact ⟨o', ho', hn', Or.inl hc'⟩
    | false =>
      obtain ⟨p, w, hp, hw, -⟩ := hm.snap h' o' ho' hc'
      rw [hn'] at hw
      refine ⟨o', ho', hn', Or.inr ⟨p, w, hp, hw, ?_⟩⟩
      rcases ha with ⟨h2, o2, he, ho2, hc2⟩ | ha
      · simp only [Slot.mem.injEq] at he
        subst he
        rw [ho', Option.some.injEq] at ho2
        subst ho2
        rw [hc'] at hc2; cases hc2
      · exact hL.VOK_ok ht hrz (ha p (by simp only [slotRefOf, ho', Option.bind_some, hp])) hw
  | stream r =>
    right
    intro r' w hr' hw
    rcases ha with ⟨h2, o2, he, -, -⟩ | ha
    · cases he
    · exact hL.VOK_ok ht hrz (ha r' (by simp only [slotRefOf]; exact hr')) hw

/-- The slots of an object that a read at t from f on may follow, for its live
children at t, in a later state: as such a read needs them. -/
theorem NInv.slotLater (hL : Later sp db1 db j1 j) (hls : LiveSub sp) (hm : EInv sp db db1.S j m)
    (hh : HInv sp db db1.S j m) (hn : NInv db db1.S m) {t : Time} (ht : t ≤ j) {h : Nat} {y : NodeId}
    (hrd : ReadableT sp db m t h y) (hcs : LaterSafeT sp db1 j1 db m t h y)
    (hr : reachable sp db.P t y = true) {o : Obj V} (ho : m.obj? h = some o) {z : NodeId}
    (hz : z ∈ sp.live (o.hist.upTo t)) :
    ∃ sl, o.slot? z = some sl ∧ SlotLaterT sp db1.S db1 j1 db m t z sl := by
  have hinv := hL.inv
  obtain ⟨o1, ho1, hoy, hcase⟩ := hcs
  rw [ho, Option.some.injEq] at ho1
  subst ho1
  cases hco : o.canonical with
  | true =>
    obtain ⟨hrz, -, -⟩ := hm.reach_child hinv hls ho hco (by rw [hoy]; exact hr) hz
    obtain ⟨sl, hsl, -⟩ := hh h o ho hco t ht (by rw [hoy]; exact hr) z hz
    exact ⟨sl, hsl, hL.slotVOK hm ht ho hsl hrz (hn.canon h o ho hco z sl hsl)⟩
  | false =>
    rcases hcase with hcase | ⟨r, w, hp, hw, hok⟩
    · rw [hco] at hcase; cases hcase
    obtain ⟨r0, w0, hp0, hw0, hh0, -, -, hex, -⟩ := hm.snap h o ho hco
    rw [hp, Option.some.injEq] at hp0
    subst hp0
    rw [hoy, hw, Option.some.injEq] at hw0
    subst hw0
    -- z is reachable at t: the version is good for t.
    have hgood : good sp db.S db.P t w = true := by
      obtain ⟨o2, ho2, -, hc2⟩ := hrd
      rw [ho, Option.some.injEq] at ho2
      subst ho2
      rcases hc2 with hc2 | ⟨r2, w2, hp2, hw2, hg⟩
      · rw [hco] at hc2; cases hc2
      · rw [hp, Option.some.injEq] at hp2
        subst hp2
        rw [hw, Option.some.injEq] at hw2
        subst hw2
        exact hg
    obtain ⟨hwn, -⟩ := hinv.version_node hw
    obtain ⟨⟨ny, hny, hwh⟩, -⟩ := (good_iff sp db.S db.P t w).mp hgood
    rw [hwn] at hny
    rw [hh0] at hz
    obtain ⟨hrz, -, -⟩ := hinv.reach_child hls hny hr (by rw [← hwh]; exact hz)
    obtain ⟨sl, hsl⟩ := Option.isSome_iff_exists.mp
      (hex z (by rw [hh0]; exact mem_pointees_of_live hls hz))
    refine ⟨sl, hsl, ?_⟩
    rcases hn.snap h o ho hco r w hp (by rw [hoy]; exact hw) z sl hsl with ha | ha
    · exact hL.slotVOK hm ht ho hsl hrz ha
    · have hs := hm.sEq
      cases sl with
      | mem h' =>
        obtain ⟨o', ho', hn'⟩ := hm.slotsNode h o ho z h' hsl
        cases hc' : o'.canonical with
        | true => exact ⟨o', ho', hn', Or.inl hc'⟩
        | false =>
          obtain ⟨p, w', hp', hw', -⟩ := hm.snap h' o' ho' hc'
          rw [hn'] at hw'
          refine ⟨o', ho', hn', Or.inr ⟨p, w', hp', hw', ?_⟩⟩
          have h1 := ha p (by simp only [slotRefOf, ho', Option.bind_some, hp'])
          rw [hs] at h1
          exact hL.own_ok ht hw hok hz hrz h1 hw'
      | stream r1 =>
        right
        intro r' w' hr' hw'
        have h1 := ha r' (by simp only [slotRefOf]; exact hr')
        rw [hs] at h1
        exact hL.own_ok ht hw hok hz hrz h1 hw'


end Slots

/-! ## The reader's follow, and reads, in a later state on the cut streams -/

section Reader

variable {sp : Spec V T} {db1 db : DB V T} {j1 j : Nat} {m : Mem V}

/-- The last startup's stream position is at least a cut safe there. -/
theorem Later.cut_le_s (hL : Later sp db1 db j1 j) (hm : EInv sp db db1.S j m) {c : Nat}
    (hcut : CutOK sp c db1 j1) : c ≤ m.s := by
  rw [hm.sEq]
  exact Nat.le_trans hcut.1 hL.fa1

/-- The follow of a slot that a later read may follow: the same on the cut
streams, and it reaches an object that can be read so. -/
theorem EInv.follow_later (hL : Later sp db1 db j1 j) (hm : EInv sp db db1.S j m) {c : Nat}
    (hcut : CutOK sp c db1 j1) {t : Time} (hft : lastFa db1.S ≤ t) {hp : Nat}
    {op : Obj V} (hop : m.obj? hp = some op) {z : NodeId} {sl : Slot} (hsl : op.slot? z = some sl)
    (hg : SlotLaterT sp db1.S db1 j1 db m t z sl) (wr : Bool) :
    m.follow4 sp (cutStream c db1.S) (cutStream c db.S) hp z wr = m.follow4 sp db1.S db.S hp z wr ∧
      ∀ m1 h1, m.reached4 sp db1.S db.S hp z = some (m1, h1) →
        LaterSafeT sp db1 j1 db (m1.swz hp z h1) t h1 z := by
  refine ⟨?_, fun m1 h1 hrc => ?_⟩
  · rw [follow4_cutS0 (hL.cut_le_s hm hcut)]
    refine follow4_cut m hp z wr (fun r r' he hcz hr hw => ?_)
    rw [hop, Option.bind_some, hsl, Option.some.injEq] at he
    subst he
    rcases hg with hg | hg
    · exact absurd hcz hg
    · obtain ⟨w, hw'⟩ := Option.isSome_iff_exists.mp hw
      have := (hg r' w hr hw').ge hL hcut hft
      rw [(hL.inv.version_node hw').2.1] at this
      exact this
  · have hk := hm.reached4_keepCore hrc
    obtain ⟨op', sl', hop', hsl', hcase⟩ := reached4_cases hrc
    rw [hop, Option.some.injEq] at hop'
    subst hop'
    rw [hsl, Option.some.injEq] at hsl'
    subst hsl'
    have hkeep : ∀ h y, LaterSafeT sp db1 j1 db m t h y → LaterSafeT sp db1 j1 db (m1.swz hp z h1) t h y := by
      intro h y hcs
      obtain ⟨o, ho, hn, hc⟩ := hcs
      obtain ⟨o', ho', hcore⟩ := hk h o ho
      have e1 : o'.node = o.node := congrArg (fun c => c.1) hcore
      have e5 : o'.canonical = o.canonical := congrArg (fun c => c.2.2.2.2.1) hcore
      have e6 : o'.pos = o.pos := congrArg (fun c => c.2.2.2.2.2) hcore
      exact ⟨o', ho', by rw [e1, hn], by rw [e5, e6]; exact hc⟩
    rcases hcase with ⟨rfl, rfl, -⟩ | ⟨r, rfl, hcz, rfl⟩ | ⟨r, r', w, rfl, hcz, hr, hw, rfl, rfl⟩
    · exact hkeep _ _ hg
    · obtain ⟨o0, ho0, hc0, hn0⟩ := hm.obj_of_canonicalOf hcz
      exact hkeep _ _ ⟨o0, ho0, hn0, Or.inl hc0⟩
    · rcases hg with hg | hg
      · exact absurd hcz hg
      have hok := hg r' w hr hw
      have hpn : hp ≠ m.next := by
        intro he; subst he; rw [hm.fresh _ (Nat.le_refl _)] at hop; cases hop
      have hobj : ((m.addObj (Obj.ofVersion sp w none)).1.swz hp z m.next).obj? m.next =
          some (Obj.ofVersion sp w none) := by
        unfold Mem.swz
        rw [Mem.obj?_addObj]
        simp only [hpn, ↓reduceIte, hop]
        rw [Mem.obj?_setObj]
        simp only [Ne.symm hpn, ↓reduceIte, Mem.obj?_addObj]
      obtain ⟨f1, -, -, -, f5, f6⟩ := Obj.ofVersion_fields sp w none
      obtain ⟨hwn, hwr, -⟩ := hL.inv.version_node hw
      refine ⟨_, hobj, by rw [f1, hwn], Or.inr ⟨w.recNo, w, f6, by rw [hwr]; exact hw, hok⟩⟩

/-- A read at t from f on, in a later state, from an object that a later read
may follow, of a node reachable at t: the same on the cut streams as on the
whole streams; the invariants are kept. -/
theorem NInv.readAt4_later (hL : Later sp db1 db j1 j) (hls : LiveSub sp) {c : Nat}
    (hcut : CutOK sp c db1 j1) {t : Time} (hft : lastFa db1.S ≤ t) (htj : t ≤ j) :
    ∀ (fuel : Nat) (m : Mem V) (h : Nat) (y : NodeId) (n : Node V), EInv sp db db1.S j m →
      HInv sp db db1.S j m → NInv db db1.S m → ReadableT sp db m t h y → LaterSafeT sp db1 j1 db m t h y →
      db.P.get? y = some n → reachable sp db.P t y = true → n.level < fuel →
      m.readAt4 sp (cutStream c db1.S) (cutStream c db.S) fuel t h = m.readAt4 sp db1.S db.S fuel t h ∧
        EInv sp db db1.S j (m.readAt4 sp db1.S db.S fuel t h).1 ∧
        HInv sp db db1.S j (m.readAt4 sp db1.S db.S fuel t h).1 ∧
        NInv db db1.S (m.readAt4 sp db1.S db.S fuel t h).1 ∧ m.KeepCore (m.readAt4 sp db1.S db.S fuel t h).1 := by
  have hinv := hL.inv
  intro fuel
  induction fuel with
  | zero => intro m h y n _ _ _ _ _ _ _ hlt; omega
  | succ fuel ih =>
    intro m h y n hm hh hn hrd hcs hny hr hlt
    obtain ⟨o, ho, hoy, hoh, hol, hod⟩ := hm.readableT_facts hinv hrd hny
    rw [readAt4_succ_eq sp (cutStream c db1.S) (cutStream c db.S) fuel m t h ho,
      readAt4_succ_eq sp db1.S db.S fuel m t h ho]
    have hlive : sp.live (o.hist.upTo t) = sp.live (n.hist.upTo t) := by rw [hoh]
    have hstep : ∀ (acc : Mem V × List (NodeId × Node V)) z, z ∈ sp.live (o.hist.upTo t) →
        (EInv sp db db1.S j acc.1 ∧ HInv sp db db1.S j acc.1 ∧ NInv db db1.S acc.1 ∧ m.KeepCore acc.1) →
        readStep4 sp (cutStream c db1.S) (cutStream c db.S) fuel t h o acc z =
            readStep4 sp db1.S db.S fuel t h o acc z ∧
          (EInv sp db db1.S j (readStep4 sp db1.S db.S fuel t h o acc z).1 ∧
            HInv sp db db1.S j (readStep4 sp db1.S db.S fuel t h o acc z).1 ∧
            NInv db db1.S (readStep4 sp db1.S db.S fuel t h o acc z).1 ∧
            m.KeepCore (readStep4 sp db1.S db.S fuel t h o acc z).1) := by
      intro acc z hz ⟨hmA, hhA, hnA, hkA⟩
      obtain ⟨o', ho', hcore⟩ := hkA h o ho
      have e4 : o'.hist = o.hist := congrArg (fun c => c.2.2.2.1) hcore
      have hz' : z ∈ sp.live (o'.hist.upTo t) := by rw [e4]; exact hz
      have hcsA : LaterSafeT sp db1 j1 db acc.1 t h y := by
        obtain ⟨o0, ho0, hn0, hc0⟩ := hcs
        obtain rfl : o = o0 := Option.some.inj (ho.symm.trans ho0)
        have e1 : o'.node = o.node := congrArg (fun c => c.1) hcore
        have e5 : o'.canonical = o.canonical := congrArg (fun c => c.2.2.2.2.1) hcore
        have e6 : o'.pos = o.pos := congrArg (fun c => c.2.2.2.2.2) hcore
        exact ⟨o', ho', by rw [e1, hn0], by rw [e5, e6]; exact hc0⟩
      obtain ⟨sl, hsl, hg⟩ := hmA.readableT_slot hinv hls hhA htj (hrd.keepCore hkA) hr ho' hz'
      obtain ⟨sl', hsl', hgc⟩ := hnA.slotLater hL hls hmA hhA htj (hrd.keepCore hkA) hcsA hr ho' hz'
      rw [hsl, Option.some.injEq] at hsl'
      subst hsl'
      obtain ⟨hfeq, hcsafe⟩ := hmA.follow_later hL hcut hft ho' hsl hgc false
      obtain ⟨m1, h1, hev1, hm1, hh1, hkc1, hrd1⟩ := hmA.follow_goodT hinv hhA ho' hsl hg
      have hn1 : NInv db db1.S m1 := by
        have := hnA.follow4_reader hinv hmA h z
        rw [hev1] at this; exact this
      have hcs1 : LaterSafeT sp db1 j1 db m1 t h1 z := by
        rw [follow4_eq] at hev1
        cases hrc : acc.1.reached4 sp db1.S db.S h z with
        | none => rw [hrc] at hev1; simp at hev1
        | some p =>
          obtain ⟨m2, h2⟩ := p
          rw [hrc] at hev1
          simp only [Bool.false_eq_true, ↓reduceIte, Prod.mk.injEq, Option.some.injEq] at hev1
          obtain ⟨rfl, rfl⟩ := hev1
          exact hcsafe m2 h2 hrc
      have hz2 : z ∈ sp.live (n.hist.upTo t) := by rw [← hlive]; exact hz
      obtain ⟨hrz, -, nz, hnz, hlvl⟩ := hinv.reach_child hls hny hr hz2
      obtain ⟨o1, ho1, -, -, hol1, -⟩ := hm1.readableT_facts hinv hrd1 hnz
      obtain ⟨heq, hI2, hH2, hN2, hkc2⟩ := ih m1 h1 z nz hm1 hh1 hn1 hrd1 hcs1 hnz hrz (by omega)
      have hst : ∀ S0' S' : Stream V T, acc.1.follow4 sp S0' S' h z false = (m1, some h1) →
          readStep4 sp S0' S' fuel t h o acc z =
            ((Mem.readAt4 sp S0' S' fuel m1 t h1).1, acc.2 ++ (Mem.readAt4 sp S0' S' fuel m1 t h1).2) := by
        intro S0' S' hS'
        unfold readStep4
        rw [hS']
        simp only [ho1, hol1, hol, hlvl, ↓reduceIte]
      rw [hst db1.S db.S hev1, hst (cutStream c db1.S) (cutStream c db.S) (by rw [hfeq]; exact hev1), heq]
      exact ⟨rfl, hI2, hH2, hN2, (hkA.trans hkc1).trans hkc2⟩
    obtain ⟨heq, hI⟩ := foldl_eq_inv (readStep4 sp (cutStream c db1.S) (cutStream c db.S) fuel t h o)
      (readStep4 sp db1.S db.S fuel t h o)
      (fun acc => EInv sp db db1.S j acc.1 ∧ HInv sp db db1.S j acc.1 ∧ NInv db db1.S acc.1 ∧ m.KeepCore acc.1)
      (sp.live (o.hist.upTo t)) hstep (m, [(o.node, o.nodeAt t)]) ⟨hm, hh, hn, Mem.KeepCore.refl m⟩
    exact ⟨heq, hI.1, hI.2.1, hI.2.2.1, hI.2.2.2⟩

/-- A read at a time from f on, in a later state: the same on the cut streams
as on the whole streams. -/
theorem NInv.read4_later (hL : Later sp db1 db j1 j) (hls : LiveSub sp) (hm : EInv sp db db1.S j m)
    (hh : HInv sp db db1.S j m) (hn : NInv db db1.S m) {c : Nat} (hcut : CutOK sp c db1 j1) {t : Time}
    (hft : lastFa db1.S ≤ t) (htj : t ≤ j) :
    m.read4 sp (cutStream c db1.S) (cutStream c db.S) t = m.read4 sp db1.S db.S t := by
  have hinv := hL.inv
  obtain ⟨o, ho, hco, hn'⟩ := hm.root
  obtain ⟨n0, hn0⟩ := Option.isSome_iff_exists.mp hinv.rootIn
  have hrd : ReadableT sp db m t m.root SIS.root := ⟨o, ho, hn', Or.inl hco⟩
  have hcs : LaterSafeT sp db1 j1 db m t m.root SIS.root := ⟨o, ho, hn', Or.inl hco⟩
  obtain ⟨o', ho', -, -, hol, -⟩ := hm.readableT_facts hinv hrd hn0
  rw [ho, Option.some.injEq] at ho'
  subst ho'
  unfold Mem.read4
  rw [ho]
  exact (NInv.readAt4_later hL hls hcut hft htj (o.level + 1) m m.root SIS.root n0 hm hh hn hrd hcs hn0
    (reachable_root hn0 t) (by omega)).1

end Reader


/-! ## The writer's walk in a later state on the cut streams -/

section Walk

variable {sp : Spec V T} {db1 db : DB V T} {j1 j : Nat} {m : Mem V}

/-- The writer reaches one node of a path: the same on the cut streams. -/
theorem NInv.reachOnPath4_later (hL : Later sp db1 db j1 j) (hls : LiveSub sp) (hm : EInv sp db db1.S j m)
    (hn : NInv db db1.S m) {c : Nat} (hcut : CutOK sp c db1 j1) {path : List NodeId}
    (hpath : ∀ p ∈ path, reachable sp db.P j p = true) (x : NodeId) :
    m.reachOnPath4 sp (cutStream c db1.S) (cutStream c db.S) db.P (j + 1) path x =
      m.reachOnPath4 sp db1.S db.S db.P (j + 1) path x := by
  have hK1 : j + 1 - 1 = j := by omega
  unfold Mem.reachOnPath4
  cases hf : path.find? (fun p => match db.P.get? p, m.canonicalOf p with
      | some n, some _ => (sp.live (n.hist.upTo (j + 1 - 1))).contains x
      | _, _ => false) with
  | none => rfl
  | some p =>
    simp only
    have hpp := List.find?_some hf
    have hpm := List.mem_of_find?_eq_some hf
    cases hnp : db.P.get? p with
    | none => rw [hnp] at hpp; simp at hpp
    | some np =>
      cases hcp : m.canonicalOf p with
      | none => rfl
      | some hp =>
        simp only
        rw [hnp, hcp] at hpp
        simp only [hK1, List.contains_iff_mem] at hpp
        obtain ⟨op, hop, hco, hnode⟩ := hm.obj_of_canonicalOf hcp
        have hrx : reachable sp db.P j x = true := (hL.inv.reach_child hls hnp (hpath p hpm) hpp).1
        rw [follow4_cutS0 (hL.cut_le_s hm hcut)]
        rw [follow4_cut m hp x true (fun r r' he hcz hr hw => ?_)]
        rw [hop, Option.bind_some] at he
        obtain ⟨w, hw'⟩ := Option.isSome_iff_exists.mp hw
        rcases hn.canon hp op hop hco x (Slot.stream r) he with ⟨h2, o2, he2, -, -⟩ | hV
        · cases he2
        · have hok := hL.VOK_ok (Nat.le_refl j) hrx (hV r' (by simp only [slotRefOf]; exact hr)) hw'
          have hfj : lastFa db1.S ≤ j := by
            have := hL.fa1; have := hL.inv1.spLt; have := hL.le; omega
          have := hok.ge hL hcut hfj
          rw [(hL.inv.version_node hw').2.1] at this
          exact this

/-- The writer's walk: the same on the cut streams. -/
theorem NInv.reachPath4_later (hL : Later sp db1 db j1 j) (hls : LiveSub sp) (hev : EvLogic sp db j)
    {c : Nat} (hcut : CutOK sp c db1 j1) {path : List NodeId}
    (hpath : ∀ p ∈ path, reachable sp db.P j p = true) :
    ∀ (L : List NodeId) (m : Mem V), EInv sp db db1.S j m → NInv db db1.S m →
      L.foldl (Mem.reachOnPath4 sp (cutStream c db1.S) (cutStream c db.S) db.P (j + 1) path) m =
        L.foldl (Mem.reachOnPath4 sp db1.S db.S db.P (j + 1) path) m := by
  intro L
  induction L with
  | nil => intro m _ _; rfl
  | cons x L ih =>
    intro m hm hn
    simp only [List.foldl_cons]
    rw [hn.reachOnPath4_later hL hls hm hcut hpath x]
    exact ih _ (hm.reachOnPath4_ok hL.inv hls hev hpath x).1 (hn.reachOnPath4 hL.inv hls hev hm hpath x)

end Walk

end SIS
