/-
The tree model (bergdb 024-12, TP7): the entries of a key node, split at a
time. For well-formed klongs without a time klong after i, the entries
(`entriesOf`) are the entries of the klongs before time i (`prefixAt` at
i - 1) and then the entries of time i (`entriesOf_split`). With it the
entries that a transaction adds to a node of P (`changesOf`: the entries of
time i of the overlay's node) continue the node's history.
-/
import SIS.Tree.CacheGood
import SIS.Tree.KlongRoundTrip

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

theorem mem_takeWhile_pred {α : Type} (p : α → Bool) (l : List α) (x : α)
    (h : x ∈ l.takeWhile p) : p x = true := by
  induction l with
  | nil => cases h
  | cons a l ih =>
    by_cases ha : p a = true
    · simp only [List.takeWhile_cons, ha, ↓reduceIte, List.mem_cons] at h
      rcases h with rfl | h
      · exact ha
      · exact ih h
    · simp [ha] at h

/-- The entries' encoding reads the klongs only at the bits of a bitmap. -/
theorem encodeKlong_fold_prefix (pre post l : List Klong) (S : KlongEntryState)
    (hl : ∀ bits, Klong.del bits ∈ l → ∀ b ∈ bits, b < pre.length) :
    l.foldl (encodeKlong (pre ++ post)) S = l.foldl (encodeKlong pre) S := by
  induction l generalizing S with
  | nil => rfl
  | cons k l ih =>
    simp only [List.foldl_cons]
    have hk : encodeKlong (pre ++ post) S k = encodeKlong pre S k := by
      cases k with
      | time t => rfl
      | key c y => rfl
      | del bits =>
        have hb := hl bits List.mem_cons_self
        have he : bitmapEntryCvs (pre ++ post) S.2.2.1 bits = bitmapEntryCvs pre S.2.2.1 bits := by
          unfold bitmapEntryCvs
          congr 2
          apply filterMap_congr_mem
          intro b hbm
          exact cvAt_append_left pre post b (hb b (List.mem_filter.mp hbm).1)
        simp only [encodeKlong, he]
    rw [hk]
    exact ih _ (fun bits hm => hl bits (List.mem_cons_of_mem _ hm))

/-- The entries of a prefix of well-formed klongs are those of the fold over
the prefix, whatever klongs follow. -/
theorem entriesOf_prefix_fold (pre post : List Klong) (hw : klongsWf (pre ++ post) = true) :
    entriesOf pre = finishKlongEntries (pre.foldl (encodeKlong (pre ++ post)) ([], 0, [], true)) := by
  rw [entriesOf_eq_encode]
  congr 1
  symm
  apply encodeKlong_fold_prefix
  intro bits hm b hb
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hm
  have hjl : j < pre.length := (List.getElem?_eq_some_iff.mp hj).1
  have hj' : (pre ++ post)[j]? = some (.del bits) := by
    rw [List.getElem?_append_left hjl]; exact hj
  have := ((klongsWf_bitmapRules _ hw) j bits hj').1 b hb
  omega

/-- Klongs that are no time klongs add entries of the time before them. -/
theorem encodeKlong_fold_noTime (ks l : List Klong) (E : History BVal) (u : Time)
    (bm : List Nat) (fl : Bool) (hl : ∀ t, Klong.time t ∉ l) :
    ∃ R bm', l.foldl (encodeKlong ks) (E, u, bm, fl) = (E ++ R, u, bm', fl || !l.isEmpty) ∧
      (∀ e ∈ R, e.time = u) ∧ (l = [] → R = []) := by
  induction l generalizing E bm fl with
  | nil => exact ⟨[], bm, by simp, by simp, fun _ => rfl⟩
  | cons k l ih =>
    have hl' : ∀ t, Klong.time t ∉ l := fun t hm => hl t (List.mem_cons_of_mem _ hm)
    cases k with
    | time t => exact (hl t List.mem_cons_self).elim
    | key c y =>
      obtain ⟨R, bm', hf, hR, _⟩ := ih (E ++ [⟨u, .key c y⟩]) bm true hl'
      refine ⟨⟨u, .key c y⟩ :: R, bm', ?_, ?_, by simp⟩
      · simp only [List.foldl_cons, encodeKlong, hf]
        simp
      · intro e he
        rcases List.mem_cons.mp he with rfl | he
        · rfl
        · exact hR e he
    | del bits =>
      obtain ⟨R, bm', hf, hR, _⟩ :=
        ih (E ++ [⟨u, .del (bitmapEntryCvs ks bm bits)⟩]) bits true hl'
      refine ⟨⟨u, .del (bitmapEntryCvs ks bm bits)⟩ :: R, bm', ?_, ?_, by simp⟩
      · simp only [List.foldl_cons, encodeKlong, hf]
        simp
      · intro e he
        rcases List.mem_cons.mp he with rfl | he
        · rfl
        · exact hR e he

/-- The entries' times are bounded by the klongs' times. -/
theorem encodeKlong_fold_times (ks l : List Klong) (S : KlongEntryState) (T : Time)
    (hS : (∀ e ∈ S.1, e.time ≤ T) ∧ S.2.1 ≤ T) (hl : ∀ t, Klong.time t ∈ l → t ≤ T) :
    (∀ e ∈ (l.foldl (encodeKlong ks) S).1, e.time ≤ T) ∧ (l.foldl (encodeKlong ks) S).2.1 ≤ T := by
  induction l generalizing S with
  | nil => exact hS
  | cons k l ih =>
    simp only [List.foldl_cons]
    apply ih
    · rcases S with ⟨E, t, bm, fl⟩
      cases k with
      | time u =>
        have hu := hl u List.mem_cons_self
        cases fl with
        | true => exact ⟨(by simpa [encodeKlong] using hS.1), hu⟩
        | false =>
          refine ⟨?_, hu⟩
          intro e he
          simp only [encodeKlong, Bool.false_eq_true, ↓reduceIte, List.mem_append,
            List.mem_singleton] at he
          rcases he with he | rfl
          · exact hS.1 e he
          · exact hS.2
      | key c y =>
        refine ⟨?_, hS.2⟩
        intro e he
        simp only [encodeKlong, List.mem_append, List.mem_singleton] at he
        rcases he with he | rfl
        · exact hS.1 e he
        · exact hS.2
      | del bits =>
        refine ⟨?_, hS.2⟩
        intro e he
        simp only [encodeKlong, List.mem_append, List.mem_singleton] at he
        rcases he with he | rfl
        · exact hS.1 e he
        · exact hS.2
    · intro t hm
      exact hl t (List.mem_cons_of_mem _ hm)

theorem entriesOf_times (ks : List Klong) (T : Time) (hl : ∀ t, Klong.time t ∈ ks → t ≤ T) :
    ∀ e ∈ entriesOf ks, e.time ≤ T := by
  have h := encodeKlong_fold_times ks ks ([], 0, [], true) T
    ⟨(by intro e he; cases he), Nat.zero_le _⟩ hl
  rw [entriesOf_eq_encode]
  intro e he
  unfold finishKlongEntries at he
  split at he
  · exact h.1 e he
  · rcases List.mem_append.mp he with he | he
    · exact h.1 e he
    · have := List.mem_singleton.mp he
      subst this
      exact h.2

/-- The time klongs of well-formed klongs increase: after a time klong of u,
the time of the walk's state is u or later. -/
theorem klongsWfState_time_ge (ks : List Klong) (hw : klongsWf ks = true) (j : Nat)
    (hj : j ≤ ks.length) (a : Nat) (u : Time) (ha : a < j) (hk : ks[a]? = some (.time u)) :
    ∃ t, (klongsWfState ks j).2.1 = some t ∧ u ≤ t := by
  induction j with
  | zero => omega
  | succ j ih =>
    have hj' : j < ks.length := by omega
    have hkj : ks[j]? = some ks[j] := List.getElem?_eq_getElem hj'
    have hs := klongsWfState_ok ks hw (j + 1)
    rw [klongsWfState_succ ks j ks[j] hkj] at hs ⊢
    rcases Nat.lt_or_ge a j with haj | haj
    · obtain ⟨t, ht, hut⟩ := ih (by omega) haj
      cases he : ks[j] with
      | time t' =>
        simp only [klongsWfStep, he, ht, Bool.and_eq_true, decide_eq_true_eq] at hs ⊢
        exact ⟨t', rfl, by omega⟩
      | key c y => exact ⟨t, by simp only [klongsWfStep, ht], hut⟩
      | del bits => exact ⟨t, by simp only [klongsWfStep, ht], hut⟩
    · have haj' : a = j := by omega
      subst haj'
      rw [hkj] at hk
      have he : ks[a] = .time u := Option.some.inj hk
      exact ⟨u, by simp only [klongsWfStep, he], Nat.le_refl _⟩

theorem klongsWf_times_increase (ks : List Klong) (hw : klongsWf ks = true) (a b : Nat)
    (u u' : Time) (hab : a < b) (ha : ks[a]? = some (.time u)) (hb : ks[b]? = some (.time u')) :
    u < u' := by
  have hbl : b < ks.length := (List.getElem?_eq_some_iff.mp hb).1
  obtain ⟨t, ht, hut⟩ := klongsWfState_time_ge ks hw b (by omega) a u hab ha
  have hs := klongsWfState_ok ks hw (b + 1)
  rw [klongsWfState_succ ks b _ hb] at hs
  simp only [klongsWfStep, ht, Bool.and_eq_true, decide_eq_true_eq] at hs
  omega

/-- The entries of well-formed klongs without a time klong after i: those of
the klongs before time i, all of earlier times, then the entries of time i. -/
theorem entriesOf_split (ks : List Klong) (i : Time) (hpos : 0 < i) (hw : klongsWf ks = true)
    (ht : ∀ t, Klong.time t ∈ ks → t ≤ i) :
    entriesOf ks = entriesOf (prefixAt ks (i - 1)) ++ (entriesOf ks).filter (fun e => e.time == i) ∧
      ∀ e ∈ entriesOf (prefixAt ks (i - 1)), e.time < i := by
  have hlow : ∀ e ∈ entriesOf (prefixAt ks (i - 1)), e.time < i := by
    intro e he
    have := entriesOf_times (prefixAt ks (i - 1)) (i - 1) (by
      intro t hm
      rw [prefixAt_eq_takeWhile] at hm
      have hp := mem_takeWhile_pred _ _ _ hm
      simpa [atOrBefore] using hp) e he
    omega
  refine ⟨?_, hlow⟩
  rcases prefixAt_stop ks (i - 1) with he | ⟨u, hu, hstop⟩
  · rw [he] at hlow ⊢
    have hnone : (entriesOf ks).filter (fun e => e.time == i) = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro e hm
      have := hlow e hm
      simp only [beq_iff_eq]
      omega
    rw [hnone, List.append_nil]
  · obtain ⟨rest, hr⟩ := prefixAt_prefix ks (i - 1)
    generalize hpre : prefixAt ks (i - 1) = pre at hlow hstop hr ⊢
    have hui : u = i := by
      have := ht u (List.mem_of_getElem? hstop)
      omega
    subst hui
    have hrest : ∃ rest', rest = .time u :: rest' := by
      rw [← hr, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self] at hstop
      cases rest with
      | nil => cases hstop
      | cons k rest' =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hstop
        exact ⟨rest', by rw [hstop]⟩
    obtain ⟨rest', rfl⟩ := hrest
    have hno : ∀ t, Klong.time t ∉ rest' := by
      intro t hm
      obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hm
      have hb : ks[pre.length + 1 + j]? = some (.time t) := by
        rw [← hr, List.getElem?_append_right (by omega)]
        have : pre.length + 1 + j - pre.length = j + 1 := by omega
        rw [this]
        simpa using hj
      have hlt := klongsWf_times_increase ks hw pre.length (pre.length + 1 + j) u t (by omega)
        hstop hb
      have := ht t (List.mem_of_getElem? hb)
      omega
    have hwp : klongsWf (pre ++ Klong.time u :: rest') = true := by rw [hr]; exact hw
    have hE : entriesOf ks = entriesOf pre ++ (if rest' = [] then [⟨u, marker⟩] else
        ((rest'.foldl (encodeKlong ks) (entriesOf pre, u,
          (pre.foldl (encodeKlong ks) ([], 0, [], true)).2.2.1, false)).1).drop
            (entriesOf pre).length) ∧
        ∀ e ∈ (if rest' = [] then [(⟨u, marker⟩ : Entry BVal)] else
        ((rest'.foldl (encodeKlong ks) (entriesOf pre, u,
          (pre.foldl (encodeKlong ks) ([], 0, [], true)).2.2.1, false)).1).drop
            (entriesOf pre).length), e.time = u := by
      have hpf := entriesOf_prefix_fold pre (.time u :: rest') hwp
      rw [hr] at hpf
      obtain ⟨R, bm', hf, hR, hnil⟩ := encodeKlong_fold_noTime ks rest' (entriesOf pre) u
        (pre.foldl (encodeKlong ks) ([], 0, [], true)).2.2.1 false hno
      have hfull : ks.foldl (encodeKlong ks) ([], 0, [], true) =
          (entriesOf pre ++ R, u, bm', !rest'.isEmpty) := by
        conv => lhs; arg 3; rw [← hr]
        rw [List.foldl_append, List.foldl_cons]
        have hstep : encodeKlong ks (pre.foldl (encodeKlong ks) ([], 0, [], true)) (.time u) =
            (entriesOf pre, u, (pre.foldl (encodeKlong ks) ([], 0, [], true)).2.2.1, false) := by
          rw [hpf]
          rfl
        rw [hstep, hf]
        simp
      rw [entriesOf_eq_encode, hfull, hf]
      cases rest' with
      | nil =>
        have hRn := hnil rfl
        subst hRn
        simp [finishKlongEntries]
      | cons k r =>
        simp only [finishKlongEntries, List.isEmpty_cons, Bool.not_false, ↓reduceIte,
          reduceCtorEq, List.drop_left]
        exact ⟨trivial, hR⟩
    obtain ⟨hE1, hE2⟩ := hE
    generalize (if rest' = [] then [(⟨u, marker⟩ : Entry BVal)] else
        ((rest'.foldl (encodeKlong ks) (entriesOf pre, u,
          (pre.foldl (encodeKlong ks) ([], 0, [], true)).2.2.1, false)).1).drop
            (entriesOf pre).length) = R at hE1 hE2
    rw [hE1, List.filter_append]
    have h1 : (entriesOf pre).filter (fun e => e.time == u) = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro e hm
      have := hlow e hm
      simp only [beq_iff_eq]
      omega
    have h2 : R.filter (fun e => e.time == u) = R := by
      apply List.filter_eq_self.mpr
      intro e hm
      simp [hE2 e hm]
    rw [h1, h2, List.nil_append]

end SIS.Tree
