import SIS.Tree.ExportHistory

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- The encoder's already emitted entries are chronological and no later
than its current time, including a pending time marker. -/
def EntryAccOrdered (a : KlongEntryState) : Prop :=
  a.1.Pairwise (fun e f => e.time ≤ f.time) ∧ ∀ e ∈ a.1, e.time ≤ a.2.1

theorem history_ordered_snoc (es : History BVal) (t : Time) (v : BVal)
    (hs : es.Pairwise (fun e f => e.time ≤ f.time)) (hb : ∀ e ∈ es, e.time ≤ t) :
    (es ++ [(⟨t,v⟩ : Entry BVal)]).Pairwise (fun e f => e.time ≤ f.time) := by
  apply List.pairwise_append.mpr
  refine ⟨hs, by simp, ?_⟩
  intro e he f hf
  have hh := List.mem_singleton.mp hf
  subst f
  exact hb e he

theorem encodeKlong_ordered (src : List Klong) (a : KlongEntryState) (k : Klong)
    (ha : EntryAccOrdered a) (ht : ∀ t, k = .time t → a.2.1 ≤ t) :
    EntryAccOrdered (encodeKlong src a k) := by
  cases k with
  | time t =>
    have htime := ht t rfl
    simp only [encodeKlong, EntryAccOrdered]
    split
    · exact ⟨ha.1, fun e he => Nat.le_trans (ha.2 e he) htime⟩
    · refine ⟨history_ordered_snoc a.1 a.2.1 marker ha.1 ha.2, ?_⟩
      intro e he
      rcases List.mem_append.mp he with he | he
      · exact Nat.le_trans (ha.2 e he) htime
      · have hh := List.mem_singleton.mp he
        subst e
        exact htime
  | key cv y =>
    refine ⟨history_ordered_snoc a.1 a.2.1 (.key cv y) ha.1 ha.2, ?_⟩
    intro e he
    rcases List.mem_append.mp he with he | he
    · exact ha.2 e he
    · have hh := List.mem_singleton.mp he
      subst e
      exact Nat.le_refl _
  | del bits =>
    refine ⟨history_ordered_snoc a.1 a.2.1 _ ha.1 ha.2, ?_⟩
    intro e he
    rcases List.mem_append.mp he with he | he
    · exact ha.2 e he
    · have hh := List.mem_singleton.mp he
      subst e
      exact Nat.le_refl _

theorem finishKlongEntries_ordered (a : KlongEntryState) (ha : EntryAccOrdered a) :
    (finishKlongEntries a).Pairwise (fun e f => e.time ≤ f.time) ∧
      ∀ e ∈ finishKlongEntries a, e.time ≤ a.2.1 := by
  unfold finishKlongEntries
  split
  · exact ha
  · refine ⟨history_ordered_snoc a.1 a.2.1 marker ha.1 ha.2, ?_⟩
    intro e he
    rcases List.mem_append.mp he with he | he
    · exact ha.2 e he
    · have hh := List.mem_singleton.mp he
      subst e
      exact Nat.le_refl _

theorem klongEntriesState_ordered (ks : List Klong) (hw : klongsWf ks = true)
    (j : Nat) (hj : j ≤ ks.length) : EntryAccOrdered (klongEntriesState ks j) := by
  induction j with
  | zero => exact ⟨.nil, by intro e he; cases he⟩
  | succ j ih =>
    have hj' : j < ks.length := by omega
    have hk : ks[j]? = some ks[j] := List.getElem?_eq_getElem hj'
    have hs := klongsWfState_ok ks hw (j+1)
    rw [klongsWfState_succ ks j ks[j] hk] at hs
    rw [klongEntriesState_step ks j ks[j] hk]
    apply encodeKlong_ordered ks _ _ (ih (by omega))
    intro t hkt
    rw [hkt] at hs
    have he := (parse_encode_prefix ks hw j (by omega)).2.1
    rw [he]
    cases ht : (klongsWfState ks j).2.1 with
    | none => simp
    | some u =>
      simp only [klongsWfStep, ht, Bool.and_eq_true, decide_eq_true_eq] at hs
      simp only [Option.getD_some]
      omega

/-- Well-formed physical histories serialize in chronological order.
Every encoded entry is bounded by the last physical time (or zero for
an empty history). No tree or transaction premise is needed. -/
theorem entriesOf_time_order (ks : List Klong) (hw : klongsWf ks = true) :
    (entriesOf ks).Pairwise (fun e f => e.time ≤ f.time) ∧
      ∀ e ∈ entriesOf ks, e.time ≤ (lastTimeOf ks).getD 0 := by
  have hf := finishKlongEntries_ordered (klongEntriesState ks ks.length)
    (klongEntriesState_ordered ks hw ks.length (Nat.le_refl _))
  have ht := (parse_encode_prefix ks hw ks.length (Nat.le_refl _)).2.1
  have ht' : (klongsWfState ks ks.length).2.1 = lastTimeOf ks := by
    simpa only [klongsWfState, List.take_length] using klongsWf_fold_lastTime ks
  rw [ht, ht'] at hf
  simpa only [entriesOf_eq_encode, klongEntriesState, List.take_length] using hf

/-- Export's time bound follows from the physical time klongs, including
histories whose final time has no physical key or bitmap after it. -/
theorem entriesOf_times_le (ks : List Klong) (hw : klongsWf ks = true) (i : Time)
    (ht : ∀ t, .time t ∈ ks → t ≤ i) : ∀ e ∈ entriesOf ks, e.time ≤ i := by
  have hb : (lastTimeOf ks).getD 0 ≤ i := by
    cases he : lastTimeOf ks with
    | none => exact Nat.zero_le _
    | some t => exact ht t (lastTimeOf_some_mem ks t he)
  intro e he
  exact Nat.le_trans ((entriesOf_time_order ks hw).2 e he) hb

/-- A bounded chronological history is exactly its earlier prefix
followed by the entries exported at the current transaction time. -/
theorem history_past_current (es : History BVal) (i : Time)
    (hs : es.Pairwise (fun e f => e.time ≤ f.time)) (hb : ∀ e ∈ es, e.time ≤ i) :
    es.filter (fun e => decide (e.time < i)) ++ es.filter (fun e => e.time == i) = es := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    have hs' := List.pairwise_cons.mp hs
    by_cases he : e.time < i
    · have hne : e.time ≠ i := by omega
      simp only [List.filter_cons, he, decide_true, ↓reduceIte,
        beq_eq_false_iff_ne.mpr hne, Bool.false_eq_true, List.cons_append]
      rw [ih hs'.2 (fun q hq => hb q (List.mem_cons_of_mem e hq))]
    · have hei : e.time = i := by have hh := hb e List.mem_cons_self; omega
      have hrest : ∀ q ∈ es, q.time = i := by
        intro q hq
        have hlow := hs'.1 q hq
        have hhigh := hb q (List.mem_cons_of_mem e hq)
        omega
      have hpast : es.filter (fun q => decide (q.time < i)) = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro q hq
        simp [hrest q hq]
      have hcurrent : es.filter (fun q => q.time == i) = es := by
        apply List.filter_eq_self.mpr
        intro q hq
        simp [hrest q hq]
      simp [hei, hpast, hcurrent]

/-- The temporal reconstruction equation is implied by equality of the
old encoded prefix and the physical upper-time bound. -/
theorem cached_history_past_current (old : History BVal) (n : KNode) (i : Time)
    (hw : klongsWf n.ks = true) (ht : ∀ t, .time t ∈ n.ks → t ≤ i)
    (hpast : old = (entriesOf n.ks).filter (fun e => decide (e.time < i))) :
    old ++ currentEntries i n = entriesOf n.ks := by
  rw [hpast]
  exact history_past_current (entriesOf n.ks) i (entriesOf_time_order n.ks hw).1
    (entriesOf_times_le n.ks hw i ht)

end SIS.Tree
