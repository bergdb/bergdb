import SIS.Tree.KlongHistoryTime

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

theorem bitmapEntryCvs_prefix_source (pre post : List Klong) (old bits : List Nat)
    (hb : ∀ b ∈ bits, b < pre.length) :
    bitmapEntryCvs (pre ++ post) old bits = bitmapEntryCvs pre old bits := by
  have he : (bits.filter (fun b => !old.contains b)).filterMap (cvAt (pre ++ post)) =
      (bits.filter (fun b => !old.contains b)).filterMap (cvAt pre) := by
    apply filterMap_congr_mem
    intro b hm
    exact cvAt_append_left pre post b (hb b (List.mem_filter.mp hm).1)
  unfold bitmapEntryCvs
  rw [he]

theorem encodeKlong_prefix_source (pre post : List Klong) (a : KlongEntryState)
    (k : Klong) (hk : k ∈ pre) (hr : BitmapRules (pre ++ post)) :
    encodeKlong (pre ++ post) a k = encodeKlong pre a k := by
  cases k with
  | time t => rfl
  | key cv y => rfl
  | del bits =>
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hk
    have hj' := (List.getElem?_eq_some_iff.mp hj).1
    have hfull : (pre ++ post)[j]? = some (.del bits) := by
      rwa [List.getElem?_append_left hj']
    have hb : ∀ b ∈ bits, b < pre.length := by
      intro b hm
      have hh := (hr j bits hfull).1 b hm
      omega
    simp only [encodeKlong, bitmapEntryCvs_prefix_source pre post _ bits hb]

/-- A prefix's encoder uses only physical positions inside that prefix.
Future physical klongs cannot change an earlier bitmap's exported value. -/
theorem entriesOf_prefix_source (pre post : List Klong)
    (hw : klongsWf (pre ++ post) = true) :
    finishKlongEntries (pre.foldl (encodeKlong (pre ++ post)) ([],0,[],true)) =
      entriesOf pre := by
  rw [entriesOf_eq_encode]
  congr 1
  exact foldl_congr_mem pre _ _ ([],0,[],true)
    (fun a k hk => encodeKlong_prefix_source pre post a k hk (klongsWf_bitmapRules _ hw))

theorem klongsWfState_time_succ_le (ks : List Klong) (hw : klongsWf ks = true)
    (j : Nat) (hj : j < ks.length) :
    (klongsWfState ks j).2.1.getD 0 ≤ (klongsWfState ks (j+1)).2.1.getD 0 := by
  have hk : ks[j]? = some ks[j] := List.getElem?_eq_getElem hj
  have hs := klongsWfState_ok ks hw (j+1)
  rw [klongsWfState_succ ks j ks[j] hk] at hs ⊢
  cases he : ks[j] with
  | key cv y => exact Nat.le_refl _
  | del bits => exact Nat.le_refl _
  | time t =>
    cases ht : (klongsWfState ks j).2.1 with
    | none => simp [klongsWfStep, ht]
    | some u =>
      simp only [he, klongsWfStep, ht, Bool.and_eq_true, decide_eq_true_eq] at hs
      simp only [klongsWfStep, ht, Option.getD_some]
      omega

theorem klongsWfState_time_mono (ks : List Klong) (hw : klongsWf ks = true)
    (a b : Nat) (hab : a ≤ b) (hb : b ≤ ks.length) :
    (klongsWfState ks a).2.1.getD 0 ≤ (klongsWfState ks b).2.1.getD 0 := by
  induction b with
  | zero => have ha : a = 0 := by omega; subst a; exact Nat.le_refl _
  | succ b ih =>
    by_cases ha : a ≤ b
    · exact Nat.le_trans (ih ha (by omega))
        (klongsWfState_time_succ_le ks hw b (by omega))
    · have he : a = b+1 := by omega
      subst a
      exact Nat.le_refl _

/-- Every later physical time is at least every earlier physical time.
This weaker consequence of strict time ordering suffices for cutoffs. -/
theorem klongsWf_time_index_le (ks : List Klong) (hw : klongsWf ks = true)
    (j k : Nat) (u v : Time) (hj : ks[j]? = some (.time u))
    (hk : ks[k]? = some (.time v)) (hjk : j ≤ k) : u ≤ v := by
  have hb := (List.getElem?_eq_some_iff.mp hk).1
  have hh := klongsWfState_time_mono ks hw (j+1) (k+1) (by omega) (by omega)
  rw [klongsWfState_succ ks j (.time u) hj,
    klongsWfState_succ ks k (.time v) hk] at hh
  exact hh

theorem klongsWf_suffix_times (pre tail : List Klong) (u : Time)
    (hw : klongsWf (pre ++ .time u :: tail) = true) :
    ∀ v, .time v ∈ tail → u ≤ v := by
  intro v hv
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hv
  have hfirst : (pre ++ .time u :: tail)[pre.length]? = some (.time u) := by simp
  have hlast : (pre ++ .time u :: tail)[pre.length + 1 + j]? = some (.time v) := by
    rw [List.getElem?_append_right (by omega)]
    simpa using hj
  exact klongsWf_time_index_le _ hw pre.length (pre.length+1+j) u v hfirst hlast (by omega)

theorem encodeKlong_future (src : List Klong) (a : KlongEntryState) (k : Klong)
    (t : Time) (ha : t < a.2.1) (hk : ∀ u, k = .time u → t < u) :
    (encodeKlong src a k).1.upTo t = a.1.upTo t ∧ t < (encodeKlong src a k).2.1 := by
  cases k with
  | time u =>
    have hu := hk u rfl
    simp only [encodeKlong]
    split
    · exact ⟨rfl, hu⟩
    · constructor
      · simp [History.upTo, List.filter_append, show ¬ a.2.1 ≤ t by omega]
      · exact hu
  | key cv y =>
    constructor
    · simp [encodeKlong, History.upTo, List.filter_append, show ¬ a.2.1 ≤ t by omega]
    · exact ha
  | del bits =>
    constructor
    · simp [encodeKlong, History.upTo, List.filter_append, show ¬ a.2.1 ≤ t by omega]
    · exact ha

/-- Once the encoder has crossed the read time, all later time blocks
leave the already exported history prefix unchanged. -/
theorem encodeKlongs_future (src rest : List Klong) (a : KlongEntryState) (t : Time)
    (ha : t < a.2.1) (hr : ∀ u, .time u ∈ rest → t < u) :
    (finishKlongEntries (rest.foldl (encodeKlong src) a)).upTo t = a.1.upTo t := by
  induction rest generalizing a with
  | nil =>
    simp only [List.foldl_nil, finishKlongEntries]
    split
    · rfl
    · simp [History.upTo, List.filter_append, show ¬ a.2.1 ≤ t by omega]
  | cons k rest ih =>
    have hh := encodeKlong_future src a k t ha (by
      intro u hu; subst k; exact hr u List.mem_cons_self)
    rw [List.foldl_cons, ih _ hh.2 (by
      intro u hu; exact hr u (List.mem_cons_of_mem k hu)), hh.1]

/-- Cutting a well-formed physical history at any time gives exactly
its encoded history at that time, including pending and lone time markers. -/
theorem entriesOf_prefixAt (ks : List Klong) (t : Time) (hw : klongsWf ks = true) :
    entriesOf (prefixAt ks t) = (entriesOf ks).upTo t := by
  let pred : Klong → Bool := fun k => match k with
    | .time u => decide (u ≤ t)
    | _ => true
  let pre := ks.takeWhile pred
  let rest := ks.dropWhile pred
  have hks : pre ++ rest = ks := List.takeWhile_append_dropWhile
  have hpre : prefixAt ks t = pre := rfl
  have htime : ∀ u, .time u ∈ pre → u ≤ t := by
    intro u hu
    have hh := List.all_eq_true.mp (List.all_takeWhile (p := pred) (l := ks)) (.time u) hu
    exact of_decide_eq_true hh
  have hwpre : klongsWf pre = true := klongsWf_of_prefix pre ks
    (List.takeWhile_prefix pred) hw
  have hentries : (entriesOf pre).upTo t = entriesOf pre :=
    upTo_of_forall _ _ (entriesOf_times_le pre hwpre t htime)
  rw [hpre]
  cases hr : rest with
  | nil =>
    have he : pre = ks := by simpa only [hr, List.append_nil] using hks
    rw [← he, hentries]
  | cons k tail =>
    have hbad := List.head?_dropWhile_not pred ks
    change (match rest.head? with | some k => pred k = false | none => True) at hbad
    rw [hr] at hbad
    cases k with
    | key cv y => simp [pred] at hbad
    | del bits => simp [pred] at hbad
    | time u =>
      have hu : t < u := by simpa only [pred, decide_eq_false_iff_not, Nat.not_le] using hbad
      have he : pre ++ .time u :: tail = ks := by simpa only [hr] using hks
      have hwfull : klongsWf (pre ++ .time u :: tail) = true := by rwa [he]
      have hfuture : ∀ v, .time v ∈ tail → t < v := by
        intro v hv
        have hh := klongsWf_suffix_times pre tail u hwfull v hv
        omega
      have hsrc := entriesOf_prefix_source pre (.time u :: tail) hwfull
      let a := pre.foldl (encodeKlong (pre ++ .time u :: tail)) ([],0,[],true)
      have hh := encodeKlongs_future (pre ++ .time u :: tail) tail
        (encodeKlong (pre ++ .time u :: tail) a (.time u)) t hu hfuture
      have hbase : (encodeKlong (pre ++ .time u :: tail) a (.time u)).1 =
          finishKlongEntries a := rfl
      rw [hbase] at hh
      have hsrc' : finishKlongEntries a = entriesOf pre := hsrc
      rw [hsrc', hentries] at hh
      rw [← he, entriesOf_eq_encode, List.foldl_append, List.foldl_cons]
      exact hh.symm

/-- Export reconstructs a cached node from its old physical prefix and
its current entries. Only the old-prefix equation and an upper time bound
remain as temporal premises. -/
theorem cached_history_of_physical_prefix (old : History BVal) (n : KNode) (i : Time)
    (hi : 0 < i) (hw : klongsWf n.ks = true) (ht : ∀ t, .time t ∈ n.ks → t ≤ i)
    (hpast : old = entriesOf (prefixAt n.ks (i-1))) :
    old ++ currentEntries i n = entriesOf n.ks := by
  apply cached_history_past_current old n i hw ht
  rw [hpast, entriesOf_prefixAt n.ks (i-1) hw]
  unfold History.upTo
  apply List.filter_congr
  intro e he
  simp only [decide_eq_decide]
  omega

end SIS.Tree
