/-
Proofs, part 14c: with a virtual root (`Spec.virt`, option (a) of Q7),
startup reads the root children from top(k) and rebuilds the root.

Written 2026-10-16 for F1-008-11, WP E3 (bergdb 011-11, 8.2).
-/
import SIS.Proof.Read

set_option linter.unusedSectionVars false

namespace SIS

variable {V T : Type} [DecidableEq V]

/-! ### Histories sorted by time, one entry per time -/

section Sorted

variable {h : History V}

theorem sorted_time_eq (hs : h.Pairwise (fun e e' => e.time < e'.time)) {e e' : Entry V}
    (he : e ∈ h) (he' : e' ∈ h) (ht : e.time = e'.time) : e = e' := by
  induction h with
  | nil => simp at he
  | cons a h ih =>
    rw [List.pairwise_cons] at hs
    rcases List.mem_cons.mp he with h1 | h1 <;> rcases List.mem_cons.mp he' with h2 | h2
    · rw [h1, h2]
    · rw [h1] at ht; have := hs.1 e' h2; omega
    · rw [h2] at ht; have := hs.1 e h1; omega
    · exact ih hs.2 h1 h2

theorem find?_time_eq_some (hs : h.Pairwise (fun e e' => e.time < e'.time)) (t : Time)
    (e : Entry V) : h.find? (fun e => e.time == t) = some e ↔ e ∈ h ∧ e.time = t := by
  constructor
  · intro hf
    exact ⟨List.mem_of_find?_eq_some hf, by simpa using List.find?_some hf⟩
  · rintro ⟨he, het⟩
    cases hf : h.find? (fun e => e.time == t) with
    | none =>
      rw [List.find?_eq_none] at hf
      have := hf e he
      simp [het] at this
    | some e' =>
      have h1 := List.mem_of_find?_eq_some hf
      have h2 : e'.time = t := by simpa using List.find?_some hf
      rw [sorted_time_eq hs h1 he (by rw [h2, het])]

/-- Entries at time ≤ s+1: those at time ≤ s, then the one at s+1. -/
theorem filter_le_succ (hs : h.Pairwise (fun e e' => e.time < e'.time)) (s : Nat) :
    h.filter (fun e => decide (e.time ≤ s + 1)) =
      h.filter (fun e => decide (e.time ≤ s)) ++ h.filter (fun e => e.time == s + 1) := by
  induction h with
  | nil => rfl
  | cons a h ih =>
    rw [List.pairwise_cons] at hs
    by_cases h1 : a.time ≤ s
    · have h2 : a.time ≤ s + 1 := by omega
      have h3 : (a.time == s + 1) = false := by simp; omega
      simp only [List.filter_cons, h1, h2, h3, decide_true, ↓reduceIte, Bool.false_eq_true,
        List.cons_append]
      rw [ih hs.2]
    · by_cases h2 : a.time = s + 1
      · -- Everything after a is later.
        have hl : h.filter (fun e => decide (e.time ≤ s + 1)) = [] := by
          rw [List.filter_eq_nil_iff]
          intro e he
          have := hs.1 e he
          simp; omega
        have hl' : h.filter (fun e => decide (e.time ≤ s)) = [] := by
          rw [List.filter_eq_nil_iff]
          intro e he
          have := hs.1 e he
          simp; omega
        have hl'' : h.filter (fun e => e.time == s + 1) = [] := by
          rw [List.filter_eq_nil_iff]
          intro e he
          have := hs.1 e he
          simp; omega
        simp [h2, hl, hl', hl'']
      · have h3 : ¬ a.time ≤ s + 1 := by omega
        have h4 : (a.time == s + 1) = false := by simp; omega
        simp only [List.filter_cons, h1, h3, h4, decide_false, Bool.false_eq_true, ↓reduceIte]
        exact ih hs.2

theorem filter_time_eq (hs : h.Pairwise (fun e e' => e.time < e'.time)) (t : Time) :
    h.filter (fun e => e.time == t) = (h.find? (fun e => e.time == t)).toList := by
  induction h with
  | nil => rfl
  | cons a h ih =>
    rw [List.pairwise_cons] at hs
    by_cases ha : a.time = t
    · have hl : h.filter (fun e => e.time == t) = [] := by
        rw [List.filter_eq_nil_iff]
        intro e he
        have := hs.1 e he
        simp; omega
      simp [ha, hl]
    · have : (a.time == t) = false := by simp [ha]
      simp only [List.filter_cons, List.find?_cons, this, Bool.false_eq_true, ↓reduceIte]
      exact ih hs.2

/-- A history sorted by time, with one entry per time, up to s: its entry at
each time t ≤ s, in order. -/
theorem upTo_eq_filterMap (hs : h.Pairwise (fun e e' => e.time < e'.time)) (s : Nat) :
    h.upTo s = (List.range (s + 1)).filterMap (fun t => h.find? (fun e => e.time == t)) := by
  induction s with
  | zero =>
    rw [show List.range (0 + 1) = [0] from rfl]
    simp only [History.upTo, List.filterMap_cons, List.filterMap_nil]
    rw [show h.filter (fun e => decide (e.time ≤ 0)) = h.filter (fun e => e.time == 0) by
      apply List.filter_congr; intro e _; apply Bool.eq_iff_iff.mpr; simp]
    rw [filter_time_eq hs 0]
    cases hf : h.find? (fun e => e.time == 0) <;> rfl
  | succ s ih =>
    simp only [History.upTo] at ih ⊢
    rw [filter_le_succ hs, ih, filter_time_eq hs]
    rw [show List.range (s + 1 + 1) = List.range (s + 1) ++ [s + 1] from List.range_succ,
      List.filterMap_append]
    simp only [List.filterMap_cons, List.filterMap_nil]
    cases hf : h.find? (fun e => e.time == s + 1) <;> rfl

end Sorted

theorem filterMap_congr_mem {α β : Type} {l : List α} {f g : α → Option β}
    (h : ∀ a ∈ l, f a = g a) : l.filterMap f = l.filterMap g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.filterMap_cons]
    rw [h a (List.mem_cons_self), ih (fun b hb => h b (List.mem_cons_of_mem a hb))]

/-- The lookup of y in the references to versions ws, when every version of y
in ws is u. -/
theorem lookup_refs {ws : List (Version V)} {y : NodeId} {u : Version V}
    (hex : ∃ w ∈ ws, w.node = y) (hall : ∀ w ∈ ws, w.node = y → w = u) :
    List.lookup y (ws.map (fun w => (w.node, w.recNo))) = some u.recNo := by
  induction ws with
  | nil => obtain ⟨w, hw, -⟩ := hex; simp at hw
  | cons a ws ih =>
    simp only [List.map_cons, List.lookup_cons]
    by_cases ha : a.node = y
    · have := hall a List.mem_cons_self ha
      subst this
      simp [ha]
    · have hne : (y == a.node) = false := by simp; exact fun h => ha h.symm
      simp only [hne]
      apply ih
      · obtain ⟨w, hw, hwy⟩ := hex
        rcases List.mem_cons.mp hw with rfl | hw
        · exact absurd hwy ha
        · exact ⟨w, hw, hwy⟩
      · exact fun w hw hwy => hall w (List.mem_cons_of_mem a hw) hwy

theorem newest_lv {S : Stream V T} {s : Nat} {y : NodeId} {w : Version V}
    (h : newest S s y = some w) : S.lv y = some w := by
  rw [newest_eq] at h
  rw [show S = S.take s ++ S.drop s from (List.take_append_drop s S).symm, lv_append, h]
  rfl

theorem readTops_eq (sp : Spec V T) (S : Stream V T) (s : Nat) (ruleR : Bool) (v : Version V) :
    readTops sp S s ruleR v =
      v :: (pointees sp v.hist).flatMap (fun y =>
        match follow S s ruleR y (v.ref? y) with
        | none => []
        | some w => if sp.topLevel ≤ w.level ∧ w.level < v.level then readTops sp S s ruleR w else []) := by
  rw [readTops]; rfl

section VRead

variable {sp : Spec V T} {db : DB V T} {k : Nat}

/-- Following the reference to a node's latest version, with Rule R, reads
that version. -/
theorem Inv.follow_lv (hinv : Inv sp db k) {y : NodeId} {u : Version V}
    (hu : db.S.lv y = some u) : follow db.S (lastSp db.S) true y (some u.recNo) = some u := by
  cases hnw : newest db.S (lastSp db.S) y with
  | some w =>
    rw [follow_newest hnw]
    have := newest_lv hnw
    rw [hu] at this
    exact this.symm
  | none =>
    rw [follow_old hnw]
    exact hinv.lv_at hu

/-- An index node, not a virtual root, that is reachable at a time up to s has a
version. -/
theorem Inv.lv_of_reachable (hinv : Inv sp db k) {x : NodeId} (hx : isIndex db.P x = true)
    (hw : written sp x = true) {t : Time} (ht : t ≤ lastSp db.S)
    (hr : reachable sp db.P t x = true) : ∃ u, db.S.lv x = some u := by
  cases hl : db.S.lv x with
  | some u => exact ⟨u, rfl⟩
  | none =>
    exfalso
    have hdirty : dirty sp db.S db.P k x = true := by simp [dirty, hl]
    obtain ⟨d, hd⟩ := (inD_iff _ _).mp (hinv.inv2 x hx hw hdirty)
    have hsd := (sectionD_mem (hinv.inv1 ▸ hd)).1
    have := hinv.inv4 x d hd hl t (by omega)
    rw [hr] at this; simp at this

/-- A root child created up to s has a version. -/
theorem Inv.topAt_lv (hinv : Inv sp db k) {z : NodeId} {m : Node V} {c : Time}
    (h : TopAt sp db.P z m c) (hc : c ≤ lastSp db.S) : ∃ u, db.S.lv z = some u := by
  obtain ⟨e, he, hec⟩ := h.exists_entry
  have hr := hinv.er z m h.1 e he
  rw [hec] at hr
  exact hinv.lv_of_reachable (by simp [isIndex, h.1, h.2.2.2.1]) (written_of_ne_root sp h.2.1) hc hr

/-- Two root children created at the same time are the same. -/
theorem Inv.topAt_unique (hinv : Inv sp db k) (hv : sp.virt = true) {z z' : NodeId} {m m' : Node V}
    {c : Time} (h : TopAt sp db.P z m c) (h' : TopAt sp db.P z' m' c) : z = z' := by
  have hvi := hinv.vr hv
  obtain ⟨n0, h0⟩ := Option.isSome_iff_exists.mp hinv.rootIn
  have e1 := hvi.topEntry z m c h n0 h0
  have e2 := hvi.topEntry z' m' c h' n0 h0
  have := sorted_time_eq (hvi.rootSorted n0 h0) e1 e2 rfl
  have hv' : sp.rootVal z = sp.rootVal z' := by simpa using this
  have := congrArg sp.ptrs hv'
  rw [hvi.rootPtrs, hvi.rootPtrs] at this
  simpa using this

/-- From the latest version w of a root child created up to s, the pointer
to a root child y reads y's latest version (Rule R, or `VInv.fresh`). -/
theorem Inv.top_follow (hinv : Inv sp db k) (hv : sp.virt = true) {z : NodeId} {m : Node V}
    {c : Time} (hz : TopAt sp db.P z m c) (hc : c ≤ lastSp db.S) {w : Version V}
    (hw : db.S.lv z = some w) {y : NodeId} (hy : y ∈ pointees sp w.hist)
    (hyt : isTop sp db.P y = true) :
    ∃ u, db.S.lv y = some u ∧ follow db.S (lastSp db.S) true y (w.ref? y) = some u ∧
      ∃ m' c', TopAt sp db.P y m' c' ∧ c' < c := by
  have hvi := hinv.vr hv
  have hwr := hinv.lv_at hw
  have hwh := hvi.topVers z m c hz w.recNo w hwr
  have hym : y ∈ pointees sp m.hist := by rw [← hwh]; exact hy
  obtain ⟨m', c', hyt', hlt⟩ := hvi.older z m c hz y hym hyt
  obtain ⟨u, hu⟩ := hinv.topAt_lv hyt' (by omega)
  refine ⟨u, hu, ?_, m', c', hyt', hlt⟩
  cases hnw : newest db.S (lastSp db.S) y with
  | some w' =>
    rw [follow_newest hnw]
    have := newest_lv hnw
    rw [hu] at this
    exact this.symm
  | none =>
    have hnone := (newest_eq_none_iff db.S (lastSp db.S) y).mp hnw
    have href : w.ref? y = some u.recNo := by
      rcases Nat.lt_or_ge w.recNo (lastSp db.S) with hrs | hrs
      · -- Written before s: the reference is fresh (VInv.fresh).
        have hzD : (z, w.recNo) ∉ db.D := by
          intro hD
          have := (sectionD_mem (hinv.inv1 ▸ hD)).1
          omega
        rw [(hvi.fresh z w hz.isTop hw hzD y hy hyt).2, hu]
        rfl
      · -- Written in R(s), ..., R(k): y has no version since, so the reference
        -- is y's latest version.
        obtain ⟨R, hR, hvR, -⟩ := versionAt_spec hwr
        obtain ⟨pre, hpre, hrefw⟩ := hinv.ref w.recNo R hR w hvR
        have hpre_none : pre.find? (fun w' => w'.node == y) = none := by
          rw [List.find?_eq_none]
          intro w' hw' hw'y
          have hw'R : w' ∈ R.vers := hpre.subset hw'
          have := hnone w.recNo hrs
          rw [← (show w'.node = y by simpa using hw'y)] at this
          rw [versionAt_of_mem hR (hinv.versNodup w.recNo R hR) hw'R] at this
          simp at this
        have hlvy : Stream.lv (Stream.building (db.S.take w.recNo) pre) y = db.S.lv y := by
          rw [lv_building, hpre_none, Option.none_or]
          exact lv_take (fun r' hr' => hnone r' (by omega))
        rw [hrefw y, ite_eq_left_iff.mpr (fun h => absurd hy h), hlvy, hu]
        rfl
    rw [href, follow_old hnw]
    exact hinv.lv_at hu

/-- A root child version read at startup: the latest version of a root child
created up to s. -/
def TopRead (sp : Spec V T) (db : DB V T) (w : Version V) : Prop :=
  ∃ m c, TopAt sp db.P w.node m c ∧ c ≤ lastSp db.S ∧ db.S.lv w.node = some w

/-- Every version that `readTops` reads from a `TopRead` version is one too. -/
theorem Inv.readTops_read (hinv : Inv sp db k) (hv : sp.virt = true) :
    ∀ (b : Nat) (w : Version V), w.level < b → TopRead sp db w →
      ∀ w' ∈ readTops sp db.S (lastSp db.S) true w, TopRead sp db w' := by
  intro b
  induction b with
  | zero => intro w h; omega
  | succ b ih =>
    intro w hb hw w' hw'
    rw [readTops_eq] at hw'
    rcases List.mem_cons.mp hw' with rfl | hw'
    · exact hw
    · obtain ⟨y, hy, hw'⟩ := List.mem_flatMap.mp hw'
      split at hw'
      · simp at hw'
      · rename_i w1 hf
        split at hw'
        · rename_i hc
          obtain ⟨hw1y, r1, hr1⟩ := follow_spec hf
          obtain ⟨-, -, my, hmy, -, hl1, -⟩ := hinv.version_node hr1
          obtain ⟨m, c, hzt, hcs, hlvz⟩ := hw
          have hyr : y ≠ root := hinv.pointee_ne_root (hinv.lv_at hlvz) hy
          have hyt : isTop sp db.P y = true := isTop_iff.mpr ⟨hyr, my, hmy, by omega⟩
          obtain ⟨u, hu, hfu, m', c', hyt', hlt⟩ := hinv.top_follow hv hzt hcs hlvz hy hyt
          rw [hf] at hfu
          cases hfu
          apply ih w1 (by omega) _ w' hw'
          exact ⟨m', c', by rw [hw1y]; exact hyt', by omega, by rw [hw1y]; exact hu⟩
        · simp at hw'

/-- `readTops` reads every root child that R4 reaches. -/
theorem Inv.readTops_all (hinv : Inv sp db k) (hv : sp.virt = true) :
    ∀ (b : Nat) (w : Version V) (m : Node V) (c : Time), m.level < b →
      TopAt sp db.P w.node m c → c ≤ lastSp db.S → db.S.lv w.node = some w →
      ∀ y ∈ topClosure sp db.P w.node m, ∃ w' ∈ readTops sp db.S (lastSp db.S) true w, w'.node = y := by
  have hvi := hinv.vr hv
  intro b
  induction b with
  | zero => intro w m c h; omega
  | succ b ih =>
    intro w m c hb hzt hcs hlv y hy
    rw [topClosure_eq sp] at hy
    rcases List.mem_cons.mp hy with rfl | hy
    · exact ⟨w, by rw [readTops_eq]; exact List.mem_cons_self, rfl⟩
    · obtain ⟨y', hy', hy⟩ := List.mem_flatMap.mp hy
      split at hy
      · rename_i my' hmy'
        split at hy
        · rename_i hc
          have hwr := hinv.lv_at hlv
          have hwh := hvi.topVers w.node m c hzt w.recNo w hwr
          have hy'w : y' ∈ pointees sp w.hist := by rw [hwh]; exact hy'
          have hy'r : y' ≠ root := hinv.pointee_ne_root hwr hy'w
          have hyt : isTop sp db.P y' = true := isTop_iff.mpr ⟨hy'r, my', hmy', hc.1⟩
          obtain ⟨u, hu, hfu, m'', c'', hyt'', hlt⟩ := hinv.top_follow hv hzt hcs hlv hy'w hyt
          have hm'' : m'' = my' := by
            have := hyt''.1; rw [hmy'] at this; exact (Option.some.inj this).symm
          subst hm''
          obtain ⟨hun, -, my2, hmy2, -, hul, -⟩ := hinv.version_node (hinv.lv_at hu)
          rw [hmy', Option.some.injEq] at hmy2
          subst hmy2
          obtain ⟨-, -, mw, hmw, -, hwl, -⟩ := hinv.version_node hwr
          rw [hzt.1, Option.some.injEq] at hmw
          subst hmw
          obtain ⟨w', hw', hw'y⟩ := ih u m'' c'' (by omega) (by rw [hun]; exact hyt'') (by omega)
            (by rw [hun]; exact hu) y (by rw [hun]; exact hy)
          refine ⟨w', ?_, hw'y⟩
          rw [readTops_eq]
          apply List.mem_cons_of_mem
          apply List.mem_flatMap.mpr
          refine ⟨y', hy'w, ?_⟩
          rw [hfu]
          have hcond : sp.topLevel ≤ u.level ∧ u.level < w.level := ⟨by omega, by omega⟩
          simp only [hcond, and_self, ite_true]
          exact hw'
        · simp at hy
      · simp at hy

end VRead

section VStart

variable {sp : Spec V T} {db : DB V T} {k : Nat}

/-- The version that top(k) names, with a virtual root: none if no root child
was created up to s; otherwise the latest version of the newest one. -/
theorem Inv.topVersion_virt (hinv : Inv sp db k) (hv : sp.virt = true) {n0 : Node V}
    (h0 : db.P.get? root = some n0) :
    (n0.hist.upTo (lastSp db.S) = [] ∧ topVersion db.S (lastSp db.S) true = none) ∨
    (∃ zs ms cs us, TopAt sp db.P zs ms cs ∧ cs ≤ lastSp db.S ∧
      (∀ y m c, TopAt sp db.P y m c → c ≤ lastSp db.S → c ≤ cs) ∧ db.S.lv zs = some us ∧
      topVersion db.S (lastSp db.S) true = some us) := by
  have hvi := hinv.vr hv
  obtain ⟨R, hR⟩ : ∃ R, db.S.getLast? = some R := by
    cases h : db.S.getLast? with
    | none =>
      have : db.S = [] := List.getLast?_eq_none_iff.mp h
      have := hinv.len; simp_all
    | some R => exact ⟨R, rfl⟩
  have htop := hinv.top R hR
  have hlast : db.S.getLast?.bind (·.top) = topV sp db.P db.S (lastSp db.S) := by
    rw [hR]; simp only [Option.bind_some]; rw [htop]; simp [topOf, hv]
  cases hl : (n0.hist.upTo (lastSp db.S)).getLast? with
  | none =>
    left
    refine ⟨List.getLast?_eq_none_iff.mp hl, ?_⟩
    have hV : topV sp db.P db.S (lastSp db.S) = none := by
      unfold topV; rw [h0]; simp only [Option.bind_some, hl]
    unfold topVersion
    rw [hlast, hV]
  | some e =>
    right
    have he := List.mem_of_getLast? hl
    obtain ⟨he1, he2⟩ := mem_upTo.mp he
    obtain ⟨zs, ms, hzt, hval⟩ := hvi.rootEntry n0 h0 e he1
    obtain ⟨us, hus⟩ := hinv.topAt_lv hzt he2
    refine ⟨zs, ms, e.time, us, hzt, he2, ?_, hus, ?_⟩
    · intro y m c hyt hc
      have hent : (⟨c, sp.rootVal y⟩ : Entry V) ∈ n0.hist.upTo (lastSp db.S) :=
        mem_upTo.mpr ⟨hvi.topEntry y m c hyt n0 h0, hc⟩
      obtain ⟨ys, hys⟩ := List.getLast?_eq_some_iff.mp hl
      have hsorted : (n0.hist.upTo (lastSp db.S)).Pairwise (fun e e' => e.time < e'.time) :=
        (hvi.rootSorted n0 h0).filter _
      rw [hys] at hent hsorted
      rcases List.mem_append.mp hent with h | h
      · have := (List.pairwise_append.mp hsorted).2.2 _ h e (List.mem_singleton_self e)
        simp only at this
        omega
      · rw [List.mem_singleton] at h
        rw [← h]
        exact Nat.le_refl _
    · have hV : topV sp db.P db.S (lastSp db.S) = some (zs, us.recNo) := by
        unfold topV; rw [h0]; simp only [Option.bind_some, hl]
        rw [hval, hvi.rootPtrs]
        simp [hus]
      unfold topVersion
      rw [hlast, hV]
      exact hinv.follow_lv hus

/-- The root that startup rebuilds has the root's history up to s, if the
root children read are latest versions of root children created up to s, and
include every such root child. -/
theorem Inv.rootHist_virt (hinv : Inv sp db k) (hv : sp.virt = true) {n0 : Node V}
    (h0 : db.P.get? root = some n0) (ws : List (Version V))
    (hws1 : ∀ w ∈ ws, TopRead sp db w)
    (hws2 : ∀ y m c, TopAt sp db.P y m c → c ≤ lastSp db.S → ∃ w ∈ ws, w.node = y) :
    (rootVersion sp (lastSp db.S) ws).hist = n0.hist.upTo (lastSp db.S) := by
  have hvi := hinv.vr hv
  rw [upTo_eq_filterMap (hvi.rootSorted n0 h0)]
  unfold rootVersion
  simp only
  apply filterMap_congr_mem
  intro t ht
  have hts : t ≤ lastSp db.S := by have := List.mem_range.mp ht; omega
  -- A version read has an entry at t exactly when its root child was created at t.
  have hent : ∀ w ∈ ws, ∀ m c, TopAt sp db.P w.node m c →
      (w.hist.any (fun e => e.time == t) = true ↔ c = t) := by
    intro w hw m c hzt
    have hwh := hvi.topVers w.node m c hzt w.recNo w (hinv.lv_at (by
      obtain ⟨m', c', h1, -, h3⟩ := hws1 w hw; exact h3))
    rw [hwh]
    constructor
    · intro h
      obtain ⟨e, he, het⟩ := List.any_eq_true.mp h
      rw [← hzt.time_of_mem he]
      simpa using het
    · intro hc
      obtain ⟨e, he, hec⟩ := hzt.exists_entry
      exact List.any_eq_true.mpr ⟨e, he, by simp [hec, hc]⟩
  by_cases hex : ∃ z m, TopAt sp db.P z m t
  · obtain ⟨z, m, hzt⟩ := hex
    have hR : n0.hist.find? (fun e => e.time == t) = some ⟨t, sp.rootVal z⟩ :=
      (find?_time_eq_some (hvi.rootSorted n0 h0) t _).mpr ⟨hvi.topEntry z m t hzt n0 h0, rfl⟩
    rw [hR]
    obtain ⟨w, hw, hwz⟩ := hws2 z m t hzt hts
    cases hf : ws.find? (fun w => w.hist.any (fun e => e.time == t)) with
    | none =>
      exfalso
      rw [List.find?_eq_none] at hf
      apply hf w hw
      exact (hent w hw m t (by rw [hwz]; exact hzt)).mpr rfl
    | some w0 =>
      have hw0 := List.mem_of_find?_eq_some hf
      have hw0t := List.find?_some hf
      obtain ⟨m0, c0, hzt0, -, -⟩ := hws1 w0 hw0
      have hc0 := (hent w0 hw0 m0 c0 hzt0).mp hw0t
      subst hc0
      have := hinv.topAt_unique hv hzt0 hzt
      simp [this]
  · have hR : n0.hist.find? (fun e => e.time == t) = none := by
      rw [List.find?_eq_none]
      intro e he het
      obtain ⟨z, m, hzt, -⟩ := hvi.rootEntry n0 h0 e he
      have : e.time = t := by simpa using het
      rw [this] at hzt
      exact hex ⟨z, m, hzt⟩
    rw [hR]
    have hL : ws.find? (fun w => w.hist.any (fun e => e.time == t)) = none := by
      rw [List.find?_eq_none]
      intro w hw hwt
      obtain ⟨m0, c0, hzt0, -, -⟩ := hws1 w hw
      have hc0 := (hent w hw m0 c0 hzt0).mp hwt
      rw [hc0] at hzt0
      exact hex ⟨w.node, m0, hzt0⟩
    rw [hL]
    rfl

/-- With a virtual root: reading the stream at a time t <= s gives exactly
the nodes reachable at t, each with a version that is good with Rule R. -/
theorem Inv.readAt_spec_virt (hinv : Inv sp db k) (hls : LiveSub sp) (hv : sp.virt = true)
    {t : Time} (ht : t ≤ lastSp db.S) :
    (SIS.readAt sp db.S (lastSp db.S) true t).map (·.1) = reachList sp db.P t ∧
    ∀ p ∈ SIS.readAt sp db.S (lastSp db.S) true t,
      GoodR sp db.S db.P (lastSp db.S) t p.2 ∧ p.2.node = p.1 ∧ VersionOf db.P p.1 p.2 := by
  have hvi := hinv.vr hv
  have hsk : lastSp db.S ≤ k := by have := hinv.spLt; omega
  obtain ⟨n0, h0⟩ := Option.isSome_iff_exists.mp hinv.rootIn
  -- The root children read.
  obtain ⟨ws, hws, hws1, hws2⟩ : ∃ ws, ws = topsRead sp db.S (lastSp db.S) true ∧
      (∀ w ∈ ws, TopRead sp db w) ∧
      (∀ y m c, TopAt sp db.P y m c → c ≤ lastSp db.S → ∃ w ∈ ws, w.node = y) := by
    rcases hinv.topVersion_virt hv h0 with ⟨hnil, htv⟩ | ⟨zs, ms, cs, us, hzt, hcs, hmax, hus, htv⟩
    · refine ⟨[], by unfold topsRead; rw [htv], by simp, ?_⟩
      intro y m c hyt hc
      have : (⟨c, sp.rootVal y⟩ : Entry V) ∈ n0.hist.upTo (lastSp db.S) :=
        mem_upTo.mpr ⟨hvi.topEntry y m c hyt n0 h0, hc⟩
      rw [hnil] at this; simp at this
    · obtain ⟨husn, -⟩ := hinv.version_node (hinv.lv_at hus)
      have hread : TopRead sp db us := ⟨ms, cs, by rw [husn]; exact hzt, hcs, by rw [husn]; exact hus⟩
      refine ⟨readTops sp db.S (lastSp db.S) true us, by unfold topsRead; rw [htv],
        hinv.readTops_read hv (us.level + 1) us (by omega) hread, ?_⟩
      intro y m c hyt hc
      rcases Nat.lt_or_ge c cs with hlt | hge
      · have hy := hvi.closed zs ms cs y m c hzt hyt hlt
        rw [← husn] at hzt hy
        exact hinv.readTops_all hv (ms.level + 1) us ms cs (by omega) hzt hcs (by rw [husn]; exact hus) y hy
      · have hc' : c = cs := Nat.le_antisymm (hmax y m c hyt hc) hge
        subst hc'
        have := hinv.topAt_unique hv hyt hzt
        subst this
        exact ⟨us, by rw [readTops_eq]; exact List.mem_cons_self, husn⟩
  -- The rebuilt root.
  obtain ⟨hidx0, hlev0⟩ := hvi.rootIdx n0 h0
  have hvh := hinv.rootHist_virt hv h0 ws hws1 hws2
  have hread : SIS.readAt sp db.S (lastSp db.S) true t =
      readFrom sp db.S (lastSp db.S) true t (rootVersion sp (lastSp db.S) ws) := by
    unfold SIS.readAt startVersion
    simp only [hv, ↓reduceIte]
    rw [← hws]
  have hlev : (rootVersion sp (lastSp db.S) ws).level = n0.level := by
    simp only [rootVersion]; rw [hlev0]
  have hdata : (rootVersion sp (lastSp db.S) ws).isData = n0.isData := by
    simp only [rootVersion]; rw [hidx0]
  have hnode : (rootVersion sp (lastSp db.S) ws).node = root := rfl
  -- It is good with Rule R at t.
  have hrecon := hinv.recon hls
  have hg : GoodR sp db.S db.P (lastSp db.S) t (rootVersion sp (lastSp db.S) ws) := by
    apply GoodR.intro _ n0 h0 (by rw [hvh, upTo_upTo _ ht])
    intro y hy
    have hy' : y ∈ sp.live (n0.hist.upTo t) := by rw [hvh, upTo_upTo _ ht] at hy; exact hy
    obtain ⟨e, he, hye⟩ := hls _ _ hy'
    obtain ⟨he1, he2⟩ := mem_upTo.mp he
    obtain ⟨z, m, hzt, hval⟩ := hvi.rootEntry n0 h0 e he1
    have hyz : y = z := by rw [hval, hvi.rootPtrs] at hye; simpa using hye
    subst hyz
    obtain ⟨my, hmy, hlt⟩ := hinv.ptrs root n0 h0 e he1 y (by rw [hval, hvi.rootPtrs]; simp)
    have hry : reachable sp db.P t y = true :=
      (reachable_iff _ _ _ _).mpr (Reach.child (Reach.root n0 h0) h0 hy' hmy hlt)
    obtain ⟨u, hu⟩ := hinv.topAt_lv hzt (by omega)
    have href : (rootVersion sp (lastSp db.S) ws).ref? y = some u.recNo := by
      unfold Version.ref?
      simp only [rootVersion]
      apply lookup_refs
      · exact hws2 y m e.time hzt (by omega)
      · intro w hw hwy
        obtain ⟨-, -, -, -, hlvw⟩ := hws1 w hw
        rw [hwy, hu] at hlvw
        exact (Option.some.inj hlvw).symm
    obtain ⟨huy, -, my2, hmy2, -, hul, -⟩ := hinv.version_node (hinv.lv_at hu)
    rw [hmy, Option.some.injEq] at hmy2
    subst hmy2
    refine ⟨u, by rw [href]; exact hinv.follow_lv hu, by rw [hlev]; omega, ?_⟩
    rcases Nat.lt_or_ge u.recNo (lastSp db.S) with hlt' | hge'
    · exact (hrecon (u.level + 1)).2 u.recNo u (by rw [huy]; exact hinv.lv_at hu) (by omega) t ht
        (by rw [huy]; exact hry) (hinv.lout hls hu (by omega) ht hry)
    · exact (hrecon (u.level + 1)).1 u.recNo u hge' (by rw [huy]; exact hinv.lv_at hu) (by omega) t
        ht (by rw [huy]; exact hry)
  have hR := hinv.read t (n0.level + 1) (rootVersion sp (lastSp db.S) ws) n0 (by omega) hg h0 hlev
    ⟨lastSp db.S, n0, h0, hvh, hlev, hdata⟩
  rw [hread]
  refine ⟨?_, hR.2⟩
  rw [hR.1]
  simp only [reachList, h0, hnode]

end VStart

end SIS
