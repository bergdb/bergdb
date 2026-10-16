/-
Proofs, part 10b: marking the access path of the change (step 3 with
`Algo.mark`) finds exactly the dirty index nodes that are not in D (T13). A
node reachable now with a changed node below it is dirty: no version written
before the change can be good now along the path to the changed node. A node
not in D with no changed node below it is clean: it was clean before (inv2),
it was reachable before (A5), and nothing below it changed.

Written 2026-10-15 for F1-008-11, WP E1 (docs/level2-alignment.md, M2). The
idea follows F1-008-08's Proof/MarkTests.lean; the proofs are new, for the
Level 2 model's `dirty`.
-/
import SIS.Proof.StepS

set_option linter.unusedSectionVars false

namespace SIS

variable {V T : Type} [DecidableEq V]

theorem self_mem_reachFrom (sp : Spec V T) (P : Struct V) (t : Time) (x : NodeId) (n : Node V) :
    x ∈ reachFrom sp P t x n := by
  rw [reachFrom_eq]; simp

/-- The nodes below a live child on a lower level are below the node. -/
theorem reachFrom_child_sub (sp : Spec V T) {P : Struct V} {t : Time} {y y' : NodeId}
    {m m' : Node V} (hy' : y' ∈ sp.live (m.hist.upTo t)) (hm' : P.get? y' = some m')
    (hlt : m'.level < m.level) :
    ∀ z ∈ reachFrom sp P t y' m', z ∈ reachFrom sp P t y m := by
  intro z hz
  rw [reachFrom_eq]
  simp only [List.mem_cons, List.mem_flatMap]
  right
  refine ⟨y', hy', ?_⟩
  rw [hm']
  simp only [hlt, ite_true]
  exact hz

/-- A version in the stream of a state with the invariant: its record is at
most k, its node is in P with the history cut at the record, and all its
entries are at most k. -/
theorem version_old_facts {sp : Spec V T} {db : DB V T} {k : Nat} (hinv : Inv sp db k)
    {r : Nat} {y : NodeId} {w : Version V} (h : db.S.versionAt r y = some w) :
    r ≤ k ∧ w.node = y ∧ ∃ n, db.P.get? y = some n ∧ w.hist = n.hist.upTo r ∧
      w.level = n.level ∧ (∀ e ∈ w.hist, e.time ≤ k) := by
  obtain ⟨R, hR, hwR, hwy⟩ := versionAt_spec h
  have hr : r < db.S.length := by
    rcases Nat.lt_or_ge r db.S.length with h1 | h1
    · exact h1
    · rw [List.getElem?_eq_none h1] at hR; simp at hR
  rw [hinv.len] at hr
  obtain ⟨n, hn, hh, hl, -⟩ := hinv.vh r R hR w hwR
  rw [hwy] at hn
  refine ⟨by omega, hwy, n, hn, hh, hl, ?_⟩
  intro e he
  rw [hh] at he
  have := (mem_upTo.mp he).2
  omega

section Step

variable (sp : Spec V T) (al : Algo V T) (db : DB V T) (tr : T)

/-- The data versions of step 2 are of nodes that are not in P before. -/
theorem step_vs0_not_old {k : Nat} (hinv : Inv sp db k)
    (hstep : StepOK sp db.P (k + 1) (parts sp al db tr).c) {w : Version V}
    (hw : w ∈ (parts sp al db tr).vs0) : db.P.get? w.node = none := by
  have hmem : w.node ∈ (parts sp al db tr).vs0.map (·.node) := List.mem_map_of_mem hw
  rw [parts_vs0, writeAll_nodes] at hmem
  simp only [List.map_nil, List.nil_append, List.mem_filter] at hmem
  exact (step_dataIds_spec sp al db tr hinv hstep hmem.1).1

/-- An old node has, in the stream with the data versions, the latest version
it has in the stream. -/
theorem step_lv_S0_old {k : Nat} (hinv : Inv sp db k)
    (hstep : StepOK sp db.P (k + 1) (parts sp al db tr).c) {x : NodeId}
    (hx : (db.P.get? x).isSome) :
    (db.S.building (parts sp al db tr).vs0).lv x = db.S.lv x := by
  rw [lv_building]
  have : (parts sp al db tr).vs0.find? (fun v => v.node == x) = none := by
    rw [List.find?_eq_none]
    intro w hw hwx
    have hwx' : w.node = x := by simpa using hwx
    have := step_vs0_not_old sp al db tr hinv hstep hw
    rw [hwx'] at this
    rw [this] at hx
    simp at hx
  rw [this, Option.none_or]

/-- A version of an old node in the stream with the data versions is in the
stream. -/
theorem step_versionAt_S0_old {k : Nat} (hinv : Inv sp db k)
    (hstep : StepOK sp db.P (k + 1) (parts sp al db tr).c) {r : Nat} {y : NodeId}
    {w : Version V} (hy : (db.P.get? y).isSome)
    (h : (db.S.building (parts sp al db tr).vs0).versionAt r y = some w) :
    db.S.versionAt r y = some w := by
  rcases Nat.lt_or_ge r db.S.length with hr | hr
  · rw [versionAt_building_lt hr] at h; exact h
  · rcases Nat.eq_or_lt_of_le hr with hr | hr
    · subst hr
      rw [versionAt_building_eq] at h
      have hw := List.mem_of_find?_eq_some h
      have hwy : w.node = y := by simpa using List.find?_some h
      have := step_vs0_not_old sp al db tr hinv hstep hw
      rw [hwy] at this
      rw [this] at hy
      simp at hy
    · have hlen : (db.S.building (parts sp al db tr).vs0).length ≤ r := by
        simp [Stream.building]; omega
      rw [versionAt_ge_length hlen] at h
      simp at h

/-- A good version, written before the change, of a node reachable now: no
node below it has changed. Every version written before has entries up to k
only; a changed node has an entry at k + 1 or is new, and then the version
of its parent that names it cannot be good. -/
theorem step_unchanged_below (hsp : SpecOK sp) {k : Nat} (hinv : Inv sp db k)
    (hstep : StepOK sp db.P (k + 1) (parts sp al db tr).c) :
    ∀ (b : Nat) (y : NodeId) (m : Node V) (w : Version V) (r : Nat), m.level < b →
      (parts sp al db tr).P.get? y = some m → db.S.versionAt r y = some w →
      good sp (db.S.building (parts sp al db tr).vs0) (parts sp al db tr).P (k + 1) w = true →
      ∀ z ∈ reachFrom sp (parts sp al db tr).P (k + 1) y m, changed (parts sp al db tr).c z = false := by
  have hlen := hinv.len
  intro b
  induction b with
  | zero => intro y m w r h; omega
  | succ b ih =>
    intro y m w r hb hm hw hg z hz
    obtain ⟨-, hwy, n0, hn0, hwh, -, hwt⟩ := version_old_facts hinv hw
    have hm0 := step_P_old sp al db tr hlen hn0
    rw [hm, Option.some.injEq] at hm0
    -- The histories: w's entries are up to k; m's are n0's and the new ones at k + 1.
    rw [good_iff] at hg
    obtain ⟨⟨m1, hm1, hc⟩, hch⟩ := hg
    rw [hwy, hm, Option.some.injEq] at hm1
    subst hm1
    have hwup : w.hist.upTo (k + 1) = w.hist := upTo_of_forall _ _ (fun e he => by
      have := hwt e he; omega)
    have hn0t : ∀ e ∈ n0.hist, e.time ≤ k := hinv.times y n0 hn0
    have hmup : m.hist.upTo (k + 1) = m.hist := by
      apply upTo_of_forall
      intro e he
      rw [hm0] at he
      simp only [List.mem_append] at he
      rcases he with he | he
      · have := hn0t e he; omega
      · exact Nat.le_of_eq (mem_addsFor.mp he).1
    rw [hwup, hmup] at hc
    rw [reachFrom_eq] at hz
    simp only [List.mem_cons, List.mem_flatMap] at hz
    rcases hz with rfl | ⟨y', hy', hz⟩
    · -- z = y: not new (it is in P before), and no entry at k + 1.
      unfold changed
      rw [Bool.or_eq_false_iff]
      constructor
      · rw [List.any_eq_false]
        intro nn hnn hid
        have := hstep.fresh nn hnn
        rw [show nn.id = z by simpa using hid, hn0] at this
        simp at this
      · rw [List.any_eq_false]
        intro a ha haz
        obtain ⟨a1, a2⟩ := a
        have ha1 : a1 = z := by simpa using haz
        subst ha1
        have he : (⟨k + 1, a2⟩ : Entry V) ∈ m.hist := by
          rw [hm0]
          apply List.mem_append_right
          rw [mem_addsFor]
          exact ⟨rfl, ha⟩
        rw [← hc] at he
        have := hwt _ he
        simp only at this
        omega
    · -- z below a live child y' of y.
      split at hz
      · rename_i m' hm'
        split at hz
        · rename_i hlt
          rw [hmup, ← hc, ← hwup] at hy'
          obtain ⟨r', w', h1, h2, -, h4⟩ := hch y' hy'
          have hy'old : (db.P.get? y').isSome := by
            obtain ⟨e, he, hye⟩ := hsp.liveSub _ _ hy'
            rw [hwup, hwh] at he
            obtain ⟨m0, hm0', -⟩ := hinv.ptrs y n0 hn0 e (mem_upTo.mp he).1 y' hye
            simp [hm0']
          have h2' := step_versionAt_S0_old sp al db tr hinv hstep hy'old h2
          exact ih y' m' w' r' (by omega) hm' h2' h4 z hz
        · simp at hz
      · simp at hz

/-- Marked implies dirty. -/
theorem step_marked_dirty (hsp : SpecOK sp) {k : Nat} (hinv : Inv sp db k)
    (hstep : StepOK sp db.P (k + 1) (parts sp al db tr).c) {x : NodeId}
    (hx : isIndex (parts sp al db tr).P x = true)
    (hm : marked sp (parts sp al db tr).P (parts sp al db tr).c (k + 1) x = true) :
    dirty sp (db.S.building (parts sp al db tr).vs0) (parts sp al db tr).P (k + 1) x = true := by
  unfold marked at hm
  rw [Bool.and_eq_true] at hm
  obtain ⟨hr, hm⟩ := hm
  cases hn : (parts sp al db tr).P.get? x with
  | none => rw [hn] at hm; simp at hm
  | some n =>
    rw [hn] at hm
    obtain ⟨z, hz, hcz⟩ := List.any_eq_true.mp hm
    cases hd : dirty sp (db.S.building (parts sp al db tr).vs0) (parts sp al db tr).P (k + 1) x
    · exfalso
      obtain ⟨v, hv, hgood⟩ := (dirty_false_iff _ _ _ _ _).mp hd
      -- x has a version, so it is old; that version is in the stream.
      have hxold : (db.P.get? x).isSome := by
        cases h0 : db.P.get? x with
        | some _ => rfl
        | none =>
          exfalso
          rw [lv_building] at hv
          cases hf : (parts sp al db tr).vs0.find? (fun v => v.node == x) with
          | none =>
            rw [hf, Option.none_or] at hv
            obtain ⟨r, hr'⟩ := lv_versionAt hv
            obtain ⟨-, -, n1, hn1, -⟩ := version_old_facts hinv hr'
            rw [h0] at hn1; simp at hn1
          | some w =>
            have hw := List.mem_of_find?_eq_some hf
            have hwx : w.node = x := by simpa using List.find?_some hf
            obtain ⟨-, n2, hn2, hd2⟩ := step_dataIds_spec sp al db tr hinv hstep (by
              have hmem : w.node ∈ (parts sp al db tr).vs0.map (·.node) := List.mem_map_of_mem hw
              rw [parts_vs0, writeAll_nodes] at hmem
              simp only [List.map_nil, List.nil_append, List.mem_filter] at hmem
              exact hwx ▸ hmem.1)
            simp [isIndex, hn2, hd2] at hx
      rw [step_lv_S0_old sp al db tr hinv hstep hxold] at hv
      obtain ⟨r, hr'⟩ := lv_versionAt hv
      have := step_unchanged_below sp al db tr hsp hinv hstep (n.level + 1) x n v r (by omega) hn hr'
        (hgood (k + 1) (Nat.le_refl _) hr) z hz
      rw [hcz] at this
      simp at this
    · rfl

/-- A good version at k, of a node with nothing changed below it now, is good
now. -/
theorem step_good_unchanged (hsp : SpecOK sp) {k : Nat} (hinv : Inv sp db k)
    (hstep : StepOK sp db.P (k + 1) (parts sp al db tr).c) :
    ∀ (b : Nat) (y : NodeId) (m : Node V) (w : Version V) (r : Nat), m.level < b →
      (parts sp al db tr).P.get? y = some m → db.S.versionAt r y = some w →
      (∀ z ∈ reachFrom sp (parts sp al db tr).P (k + 1) y m, changed (parts sp al db tr).c z = false) →
      good sp db.S db.P k w = true →
      good sp (db.S.building (parts sp al db tr).vs0) (parts sp al db tr).P (k + 1) w = true := by
  have hlen := hinv.len
  have hpf := step_pfacts sp al db tr hsp hinv hstep
  intro b
  induction b with
  | zero => intro y m w r h; omega
  | succ b ih =>
    intro y m w r hb hm hw hun hg
    obtain ⟨-, hwy, n0, hn0, -, -, hwt⟩ := version_old_facts hinv hw
    have hm0 := step_P_old sp al db tr hlen hn0
    -- y has no new entries: m = n0.
    have hadds : addsFor (parts sp al db tr).c (k + 1) y = [] := by
      rw [List.eq_nil_iff_forall_not_mem]
      intro e he
      obtain ⟨-, ha⟩ := mem_addsFor.mp he
      have hc := hun y (self_mem_reachFrom sp _ _ y m)
      unfold changed at hc
      rw [Bool.or_eq_false_iff, List.any_eq_false, List.any_eq_false] at hc
      exact hc.2 _ ha (by simp)
    rw [hadds, List.append_nil] at hm0
    rw [hm, Option.some.injEq] at hm0
    have hmn : m = n0 := by rw [hm0]
    subst hmn
    have hn0t : ∀ e ∈ m.hist, e.time ≤ k := hinv.times y m hn0
    have hwup : w.hist.upTo (k + 1) = w.hist.upTo k := by
      rw [upTo_of_forall _ _ (fun e he => by have := hwt e he; omega),
        upTo_of_forall _ _ (fun e he => hwt e he)]
    have hmup : m.hist.upTo (k + 1) = m.hist.upTo k := by
      rw [upTo_of_forall _ _ (fun e he => by have := hn0t e he; omega),
        upTo_of_forall _ _ (fun e he => hn0t e he)]
    rw [good_iff] at hg ⊢
    obtain ⟨⟨m1, hm1, hc⟩, hch⟩ := hg
    rw [hwy, hn0, Option.some.injEq] at hm1
    subst hm1
    refine ⟨⟨m, by rw [hwy]; exact hm, by rw [hwup, hmup]; exact hc⟩, ?_⟩
    intro y' hy'
    rw [hwup] at hy'
    obtain ⟨r', w', h1, h2, h3, h4⟩ := hch y' hy'
    refine ⟨r', w', h1, (SExt.append _ _).versionAt h2, h3, ?_⟩
    -- y' is a live child of y now, on a lower level.
    have hy'm : y' ∈ sp.live (m.hist.upTo (k + 1)) := by rw [hmup, ← hc]; exact hy'
    obtain ⟨e, he, hye⟩ := hsp.liveSub _ _ hy'm
    obtain ⟨m', hm', hlt⟩ := hpf.ptrs y m hm e (mem_upTo.mp he).1 y' hye
    exact ih y' m' w' r' (by omega) hm' h2
      (fun z hz => hun z (reachFrom_child_sub sp hy'm hm' hlt z hz)) h4

/-- Not marked, and not in D, implies clean (but for a virtual root). -/
theorem step_unmarked_clean (hsp : SpecOK sp) {k : Nat} (hinv : Inv sp db k)
    (hstep : StepOK sp db.P (k + 1) (parts sp al db tr).c) {x : NodeId}
    (hx : isIndex (parts sp al db tr).P x = true) (hD : inD db.D x = false)
    (hw : written sp x = true)
    (hm : marked sp (parts sp al db tr).P (parts sp al db tr).c (k + 1) x = false) :
    dirty sp (db.S.building (parts sp al db tr).vs0) (parts sp al db tr).P (k + 1) x = false := by
  have hlen := hinv.len
  have hg := step_grow sp al db tr hlen
  have hP := parts_P' sp al db tr hlen
  obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp (isSome_of_isIndex hx)
  -- x is an old node: a new node is changed and reachable now, so marked.
  obtain ⟨n0, hn0⟩ : ∃ n0, db.P.get? x = some n0 := by
    cases h0 : db.P.get? x with
    | some n0 => exact ⟨n0, rfl⟩
    | none =>
      exfalso
      rcases step_node_cases sp al db tr hlen hn with ⟨n1, hn1, -⟩ | ⟨-, nn, hnn, hid, -⟩
      · rw [h0] at hn1; simp at hn1
      · have hr : reachable sp (parts sp al db tr).P (k + 1) x = true := by
          rw [hP, ← hid]; exact hstep.newReachable nn hnn
        have hc : changed (parts sp al db tr).c x = true := by
          unfold changed
          rw [Bool.or_eq_true]
          exact Or.inl (List.any_eq_true.mpr ⟨nn, hnn, by simp [hid]⟩)
        unfold marked at hm
        rw [hr, hn] at hm
        simp only [Bool.true_and, List.any_eq_false] at hm
        exact hm x (self_mem_reachFrom sp _ _ x n) hc
  have hxi : isIndex db.P x = true := by
    rw [← step_isIndex_old sp al db tr hlen (by simp [hn0])]; exact hx
  -- x is clean at k.
  have hc0 : dirty sp db.S db.P k x = false := by
    cases h : dirty sp db.S db.P k x
    · rfl
    · rw [hinv.inv2 x hxi hw h] at hD; simp at hD
  obtain ⟨v, hv, hgood⟩ := (dirty_false_iff _ _ _ _ _).mp hc0
  obtain ⟨r, hr⟩ := lv_versionAt hv
  rw [dirty_false_iff]
  refine ⟨v, by rw [step_lv_S0_old sp al db tr hinv hstep (by simp [hn0])]; exact hv, ?_⟩
  intro t ht hrt
  rcases Nat.lt_or_ge t (k + 1) with h | h
  · -- Before the change: as at k.
    rw [reachable_grow hsp.liveSub hinv.ptrs hinv.rootIn hg (by omega)] at hrt
    exact good_mono' sp (SExt.append _ _) hg (by omega) (hgood t (by omega) hrt)
  · -- Now: reachable at k too (A5), and nothing changed below it.
    have ht' : t = k + 1 := by omega
    subst ht'
    have hxk : reachable sp db.P k x = true := by
      rcases hstep.noRes x (by rw [← hP]; exact hrt) with h1 | h1
      · simpa using h1
      · exfalso
        obtain ⟨nn, hnn, hid⟩ := List.mem_map.mp h1
        have := hstep.fresh nn hnn
        rw [hid, hn0] at this
        simp at this
    have hun : ∀ z ∈ reachFrom sp (parts sp al db tr).P (k + 1) x n,
        changed (parts sp al db tr).c z = false := by
      unfold marked at hm
      rw [hrt, hn] at hm
      simp only [Bool.true_and, List.any_eq_false] at hm
      intro z hz
      cases h1 : changed (parts sp al db tr).c z
      · rfl
      · exact absurd h1 (hm z hz)
    exact step_good_unchanged sp al db tr hsp hinv hstep (n.level + 1) x n v r (by omega) hn hr hun
      (hgood k (Nat.le_refl _) hxk)

/-- T13 in one transaction: for an index node not in D (and not a virtual
root), marked is the same as dirty. -/
theorem step_marked_iff (hsp : SpecOK sp) {k : Nat} (hinv : Inv sp db k)
    (hstep : StepOK sp db.P (k + 1) (parts sp al db tr).c) {x : NodeId}
    (hx : isIndex (parts sp al db tr).P x = true) (hD : inD db.D x = false)
    (hw : written sp x = true) :
    marked sp (parts sp al db tr).P (parts sp al db tr).c (k + 1) x =
      dirty sp (db.S.building (parts sp al db tr).vs0) (parts sp al db tr).P (k + 1) x := by
  cases hm : marked sp (parts sp al db tr).P (parts sp al db tr).c (k + 1) x
  · exact (step_unmarked_clean sp al db tr hsp hinv hstep hx hD hw hm).symm
  · exact (step_marked_dirty sp al db tr hsp hinv hstep hx hm).symm

/-- Step 3 in either way gives the dirty index nodes not in D (but a virtual
root). -/
theorem step_gd3_mem' (hsp : SpecOK sp) {k : Nat} (hinv : Inv sp db k)
    (hstep : StepOK sp db.P (k + 1) (parts sp al db tr).c) (x : NodeId) :
    x ∈ (parts sp al db tr).gd3 ↔
      ((parts sp al db tr).P.get? x).isSome ∧ isIndex (parts sp al db tr).P x = true ∧
        inD db.D x = false ∧ written sp x = true ∧
        dirty sp (db.S.building (parts sp al db tr).vs0) (parts sp al db tr).P (k + 1) x = true :=
  step_gd3_mem sp al db tr hinv.len
    (fun _ _ hy hD hw => step_marked_iff sp al db tr hsp hinv hstep hy hD hw) x

end Step

end SIS
