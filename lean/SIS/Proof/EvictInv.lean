/-
Proofs for stage 2 (bergdb item 001, WP E3), part 3: the invariant of the memory
with eviction (bergdb 001-08, 5.3 and 5.4), and that unswizzling and
release keep it.
-/
import SIS.Proof.EvictWrite
import SIS.Proof.PhysT2

set_option linter.unusedSectionVars false

namespace SIS

variable {V T : Type} [DecidableEq V]

/-! ## The invariant -/

/-- The got-dirty index of x in D, if x is in D. -/
def dOf (D : Dirty) (x : NodeId) : Option Nat := (D.find? (fun e => e.1 == x)).map (·.2)

/-! ## Basic facts -/

theorem ruleRRef_some_ge {S0 : Stream V T} {s : Nat} {y : NodeId} {r r0 : Nat}
    (h : ruleRRef S0 s y (some r) = some r0) : r ≤ r0 := by
  unfold ruleRRef at h
  cases hn : newest S0 s y with
  | none => rw [hn] at h; simp at h; omega
  | some w =>
    rw [hn] at h
    simp only at h
    split at h
    · simp at h; omega
    · simp at h; omega

section Facts

variable {sp : Spec V T} {db : DB V T} {k : Nat}

/-- The reference of a version names a version of the pointee. -/
theorem Inv.ref_versionAt (hinv : Inv sp db k) {r : Nat} {x : NodeId} {v : Version V}
    (hv : db.S.versionAt r x = some v) {y : NodeId} {r1 : Nat} (h1 : v.ref? y = some r1) :
    ∃ u, db.S.versionAt r1 y = some u := by
  obtain ⟨R, hR, hvR, -⟩ := versionAt_spec hv
  obtain ⟨pre, hpre, href⟩ := hinv.ref r R hR v hvR
  rw [href y] at h1
  split at h1
  · cases hl : (Stream.building (db.S.take r) pre).lv y with
    | none => rw [hl] at h1; cases h1
    | some u =>
      rw [hl] at h1
      simp only [Option.map_some, Option.some.injEq] at h1
      obtain ⟨r0, hr0⟩ := lv_versionAt hl
      have hu0 := (sext_building_take hR hpre).versionAt hr0
      obtain ⟨-, hur, -⟩ := hinv.version_node hu0
      rw [← h1, hur]
      exact ⟨u, hu0⟩
  · cases h1

/-- Rule R of the stream of the last startup, a prefix of the stream, leaves the
reference to the latest version. -/
theorem Inv.ruleR_lv0 (hinv : Inv sp db k) {S0 : Stream V T} (hpre : S0 <+: db.S) (s : Nat)
    (y : NodeId) : ruleRRef S0 s y ((db.S.lv y).map (·.recNo)) = (db.S.lv y).map (·.recNo) := by
  unfold ruleRRef
  cases hn : newest S0 s y with
  | none => rfl
  | some w =>
    simp only
    obtain ⟨r0, -, hr0⟩ := newest_some hn
    have hr0' := versionAt_prefix hpre hr0
    obtain ⟨-, hrec, -⟩ := hinv.version_node hr0'
    obtain ⟨v, hv, hle⟩ := hinv.le_lv hr0'
    rw [hv]
    simp only [Option.map_some]
    have : ¬ v.recNo < w.recNo := by omega
    simp [this]

/-- Rule R of the stream of the last startup on a reference to a version gives a
version, at most the latest. -/
theorem Inv.ruleR_bound (hinv : Inv sp db k) {S0 : Stream V T} (hpre : S0 <+: db.S) (s : Nat)
    {y : NodeId} {r : Option Nat} (hr : ∀ r', r = some r' → ∃ u, db.S.versionAt r' y = some u)
    {r0 : Nat} (h : ruleRRef S0 s y r = some r0) :
    (∃ u, db.S.versionAt r0 y = some u) ∧ ∃ v, db.S.lv y = some v ∧ r0 ≤ v.recNo := by
  have hver : ∃ u, db.S.versionAt r0 y = some u := by
    unfold ruleRRef at h
    cases hn : newest S0 s y with
    | none => rw [hn] at h; exact hr r0 h
    | some w =>
      rw [hn] at h
      obtain ⟨r1, -, hr1⟩ := newest_some hn
      have hr1' := versionAt_prefix hpre hr1
      obtain ⟨-, hrec, -⟩ := hinv.version_node hr1'
      simp only at h
      cases r with
      | none =>
        simp only [Option.some.injEq] at h
        rw [← h, hrec]; exact ⟨w, hr1'⟩
      | some r' =>
        simp only at h
        split at h
        · simp only [Option.some.injEq] at h
          rw [← h, hrec]; exact ⟨w, hr1'⟩
        · simp only [Option.some.injEq] at h
          rw [← h]; exact hr r' rfl
  obtain ⟨u, hu⟩ := hver
  exact ⟨⟨u, hu⟩, hinv.le_lv hu⟩

/-- A clean node's latest version holds its whole history. -/
theorem Inv.lv_whole (hinv : Inv sp db k) {y : NodeId} {n : Node V} (hn : db.P.get? y = some n)
    (hw : written sp y = true) (hD : inD db.D y = false) (hr : reachable sp db.P k y = true) :
    ∃ v, db.S.lv y = some v ∧ v.hist = n.hist ∧ v.level = n.level ∧ v.isData = n.isData := by
  have hwhole : ∀ v, db.S.lv y = some v → v.hist.upTo k = n.hist.upTo k →
      v.hist = n.hist ∧ v.level = n.level ∧ v.isData = n.isData := by
    intro v hv hup
    have hva := hinv.lv_at hv
    obtain ⟨-, hrec, n', hn', hh, hl, hd⟩ := hinv.version_node hva
    rw [hn, Option.some.injEq] at hn'
    subst hn'
    have hrk : v.recNo ≤ k := by
      obtain ⟨R, hR, -, -⟩ := versionAt_spec hva
      have := (List.getElem?_eq_some_iff.mp hR).1
      rw [hinv.len] at this; omega
    refine ⟨?_, hl, hd⟩
    have h1 : v.hist.upTo k = v.hist := by rw [hh, upTo_upTo' _ hrk]
    have h2 : n.hist.upTo k = n.hist := upTo_of_forall _ _ (hinv.times y n hn)
    rw [← h1, hup, h2]
  by_cases hd : n.isData = true
  · obtain ⟨v, hv, hvh⟩ := hinv.dataV y n hn hd
    obtain ⟨h1, h2, h3⟩ := hwhole v hv (by rw [hvh])
    exact ⟨v, hv, h1, h2, h3⟩
  · have hix : isIndex db.P y = true := by simp [isIndex, hn, hd]
    have hdirty : dirty sp db.S db.P k y = false := by
      cases hdy : dirty sp db.S db.P k y with
      | false => rfl
      | true => rw [hinv.inv2 y hix hw hdy] at hD; cases hD
    obtain ⟨v, hv, hgood⟩ := (dirty_false_iff sp db.S db.P k y).mp hdirty
    have hg := hgood k (Nat.le_refl k) hr
    rw [good_eq] at hg
    simp only [Bool.and_eq_true] at hg
    have hup : v.hist.upTo k = n.hist.upTo k := by
      have h1 := hg.1
      have hvn : v.node = y := by
        obtain ⟨-, -, -⟩ := hinv.version_node (hinv.lv_at hv)
        exact (hinv.version_node (hinv.lv_at hv)).1
      rw [hvn, hn] at h1
      simpa using h1
    obtain ⟨h1, h2, h3⟩ := hwhole v hv hup
    exact ⟨v, hv, h1, h2, h3⟩

end Facts

/-! ## Memories with the same cores -/

section Core

variable {sp : Spec V T} {db : DB V T} {S0 : Stream V T} {k : Nat} {m m' : Mem V}

end Core

/-! ## Changing the slots of one object -/

section SetObj

variable {sp : Spec V T} {db : DB V T} {S0 : Stream V T} {k : Nat} {m : Mem V}

end SetObj

/-! ## Unswizzle and release -/

section Evict

variable {sp : Spec V T} {db : DB V T} {S0 : Stream V T} {k : Nat} {m : Mem V}

theorem lookup_filter_self {β : Type} (l : List (Nat × β)) (h : Nat) :
    List.lookup h (l.filter (fun p => p.1 != h)) = none := by
  apply lookup_none_of_not_mem
  intro hm
  obtain ⟨p, hp, hph⟩ := List.mem_map.mp hm
  have := (List.mem_filter.mp hp).2
  rw [hph] at this
  simp at this

theorem lookup_filter_snd (l : List (NodeId × Nat)) (hnd : (l.map (·.1)).Nodup) (a : NodeId)
    (h : Nat) :
    List.lookup a (l.filter (fun p => p.2 != h)) =
      if List.lookup a l = some h then none else List.lookup a l := by
  induction l with
  | nil => rfl
  | cons q l ih =>
    obtain ⟨b, c⟩ := q
    simp only [List.map_cons, List.nodup_cons] at hnd
    rw [List.filter_cons, lookup_cons_eq]
    by_cases hab : a = b
    · subst hab
      have hl : List.lookup a l = none := lookup_none_of_not_mem hnd.1
      by_cases hc : c = h
      · subst hc
        simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
        rw [ih hnd.2, hl]; simp
      · have : (c != h) = true := by simp [hc]
        simp only [this, ↓reduceIte, lookup_cons_eq, Option.some.injEq, hc]
    · simp only [hab, ↓reduceIte]
      split
      · rw [lookup_cons_eq]; simp only [hab, ↓reduceIte]; exact ih hnd.2
      · exact ih hnd.2

end Evict

end SIS
