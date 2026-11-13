import SIS.Tree.KlongDeleteAppend

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- A checked prefix reads the same compare values in the full physical
array as in the prefix itself: every bitmap bit points backwards. -/
theorem klongsWfStep_prefix_source (pre post : List Klong)
    (hr : BitmapRules (pre ++ post)) (acc : Bool × Option Time × List Nat)
    (q : Klong × Nat) (hq : q ∈ pre.zipIdx) :
    klongsWfStep (pre ++ post) acc q = klongsWfStep pre acc q := by
  rcases q with ⟨k, i⟩
  have hk := List.mem_zipIdx_iff_getElem?.mp hq
  have hi : i < pre.length := (List.getElem?_eq_some_iff.mp hk).1
  cases k with
  | time t => rfl
  | key cv y => rfl
  | del bits =>
    have hk' : (pre ++ post)[i]? = some (.del bits) := by
      rwa [List.getElem?_append_left hi]
    have hb := (hr i bits hk').1
    have hnew : (bits.filter (fun b => !acc.2.2.contains b)).filterMap
          (cvAt (pre ++ post)) =
        (bits.filter (fun b => !acc.2.2.contains b)).filterMap (cvAt pre) := by
      apply filterMap_congr_mem
      intro b hm
      have hbit := (List.mem_filter.mp hm).1
      exact cvAt_append_left pre post b (by have hh := (hb b hbit).1; omega)
    have hall : bits.all (fun b => decide (b < i) && (cvAt (pre ++ post) b).isSome) =
        bits.all (fun b => decide (b < i) && (cvAt pre b).isSome) := by
      apply all_congr_mem
      intro b hbit
      rw [cvAt_append_left pre post b (by have hh := (hb b hbit).1; omega)]
    have hclosed : (List.range i).all (fun j => match cvAt (pre ++ post) j with
          | some cv => !((bits.filter (fun b => !acc.2.2.contains b)).filterMap
              (cvAt pre)).contains cv || bits.contains j
          | none => true) =
        (List.range i).all (fun j => match cvAt pre j with
          | some cv => !((bits.filter (fun b => !acc.2.2.contains b)).filterMap
              (cvAt pre)).contains cv || bits.contains j
          | none => true) := by
      apply all_congr_mem
      intro j hj
      rw [cvAt_append_left pre post j (by have hh := List.mem_range.mp hj; omega)]
    simp only [klongsWfStep, hnew, hall]
    congr 2

/-- Truncating a physical history preserves every klong-format check. -/
theorem klongsWf_of_prefix (pre ks : List Klong) (hp : pre.IsPrefix ks)
    (hw : klongsWf ks = true) : klongsWf pre = true := by
  obtain ⟨post, rfl⟩ := hp
  have hs := klongsWfState_ok (pre ++ post) hw pre.length
  simp only [klongsWfState, List.take_left] at hs
  rw [klongsWf_eq_fold]
  rw [foldl_congr_mem pre.zipIdx _ _ (true, none, [])
    (fun acc q hq => klongsWfStep_prefix_source pre post
      (klongsWf_bitmapRules _ hw) acc q hq)] at hs
  exact hs

theorem KNode.toPrev_wf (n : KNode) (t : Time) (hw : klongsWf n.ks = true) :
    klongsWf (n.toPrev t).ks = true :=
  klongsWf_of_prefix _ _ (List.takeWhile_prefix _) hw

/-- Growing the final bitmap keeps the earlier history and its bitmap
checks. Newly deleted compare values must delete all their occurrences. -/
theorem klongsWf_grow_last_bitmap (pre : List Klong) (old bits : List Nat)
    (hw : klongsWf (pre ++ [.del old]) = true)
    (hs : bits.Pairwise (· < ·)) (hm : ∀ b ∈ old, b ∈ bits)
    (hb : ∀ b ∈ bits, b < pre.length ∧ (cvAt pre b).isSome = true)
    (hc : ∀ b ∈ bits, b ∉ old → ∀ cv, cvAt pre b = some cv →
      ∀ j < pre.length, cvAt pre j = some cv → j ∈ bits) :
    klongsWf (pre ++ [.del bits]) = true := by
  have hp : pre.IsPrefix (pre ++ [.del old]) := ⟨_, rfl⟩
  have hpre := klongsWf_of_prefix _ _ hp hw
  have hk : (pre ++ [.del old])[pre.length]? = some (.del old) := by simp
  have hr := klongsWf_bitmapRules _ hw pre.length old hk
  simp only [List.take_left] at hr
  have hstate := klongsWfState_ok _ hw (pre.length + 1)
  rw [klongsWfState_succ _ _ _ hk] at hstate
  simp only [klongsWfStep, Bool.and_eq_true] at hstate
  have ht : (lastTimeOf pre).isSome = true := by
    have hh := hstate.1.1.1.1.1.2
    simp only [klongsWfState, List.take_left] at hh
    change ((pre.zipIdx.foldl (klongsWfStep (pre ++ [.del old]))
      (true, none, [])).2.1).isSome = true at hh
    rw [klongsWf_fold_append_source pre [.del old] hpre,
      klongsWf_fold_lastTime] at hh
    exact hh
  have hlen : (lastBitmapOf pre).length < old.length := by
    simpa only [klongsWfState_bitmap, List.take_left, decide_eq_true_eq]
      using hstate.1.1.1.2
  have hold := (klongsWf_bitmap_order _ hw pre.length old hk).2
  have hnd : old.Nodup := hold.imp (by intro a b h; omega)
  have hle : old.length ≤ bits.length :=
    hnd.length_le_of_subset hm
  apply klongsWf_append_bitmap pre bits hpre ht hs
  · intro b hmem
    apply hm b
    exact hr.2.1 b hmem
  · omega
  · exact hb
  · intro b hmem hnot cv hcv j hj hjcv
    by_cases hbold : b ∈ old
    · apply hm j
      apply hr.2.2 b hbold
      · exact hnot
      · rwa [cvAt_append_left pre [.del old] b (hb b hmem).1]
      · exact hj
      · rwa [cvAt_append_left pre [.del old] j hj]
    · exact hc b hmem hbold cv hcv j hj hjcv

/-- The delete's in-place bitmap mode preserves physical well-formedness. -/
theorem KNode.setAt_delete_wf (n : KNode) (cv : Nat) (old : List Nat)
    (hw : klongsWf n.ks = true) (hlast : n.ks.getLast? = some (.del old)) :
    klongsWf (n.setAt (n.size - 1)
      (.del (bitsUnion n.lastBitmap (n.bitsOf cv)))).ks = true := by
  obtain ⟨pre, hpre⟩ := List.getLast?_eq_some_iff.mp hlast
  have hnew : (n.setAt (n.size - 1)
      (.del (bitsUnion n.lastBitmap (n.bitsOf cv)))).ks =
      pre ++ [.del (bitsUnion n.lastBitmap (n.bitsOf cv))] := by
    simp [KNode.setAt, KNode.size, hpre]
  have hbitmap : n.lastBitmap = old := by
    simp only [KNode.lastBitmap, hpre, lastBitmapOf_append_delete]
  rw [hnew, hbitmap]
  apply klongsWf_grow_last_bitmap pre old _ (by rwa [← hpre])
  · exact bitsUnion_pairwise _ _
  · intro b hb
    exact (mem_bitsUnion_iff _ _ _).mpr (Or.inl hb)
  · intro b hb
    rcases (mem_bitsUnion_iff _ _ _).mp hb with hb | hb
    · have hk : n.ks[pre.length]? = some (.del old) := by simp [hpre]
      have hh := (klongsWf_bitmapRules n.ks hw pre.length old hk).1 b hb
      refine ⟨hh.1, ?_⟩
      have hhcv := hh.2
      rwa [hpre, cvAt_append_left pre [.del old] b hh.1] at hhcv
    · obtain ⟨y, hy⟩ := (n.mem_bitsOf_iff cv b).mp hb
      rw [hpre, key_mem_zipIdx_append_delete_iff] at hy
      have hk := List.mem_zipIdx_iff_getElem?.mp hy
      exact ⟨(List.getElem?_eq_some_iff.mp hk).1,
        by simp only [cvAt, hk, Option.isSome_some]⟩
  · intro b hb hnot a hcv j hj hjcv
    have hbit : b ∈ n.bitsOf cv := by
      rcases (mem_bitsUnion_iff _ _ _).mp hb with hb | hb
      · exact (hnot hb).elim
      · exact hb
    obtain ⟨y, hy⟩ := (n.mem_bitsOf_iff cv b).mp hbit
    rw [hpre, key_mem_zipIdx_append_delete_iff] at hy
    have hbcv : cvAt pre b = some cv :=
      (cvAt_eq_some_iff pre b cv).mpr ⟨y, List.mem_zipIdx_iff_getElem?.mp hy⟩
    have hac : a = cv := Option.some.inj (hcv.symm.trans hbcv)
    subst a
    obtain ⟨z, hz⟩ := (cvAt_eq_some_iff pre j cv).mp hjcv
    apply (mem_bitsUnion_iff _ _ _).mpr
    apply Or.inr
    apply (n.mem_bitsOf_iff cv j).mpr
    refine ⟨z, ?_⟩
    rw [hpre, key_mem_zipIdx_append_delete_iff]
    exact List.mem_zipIdx_iff_getElem?.mpr hz

theorem KNode.append_time_bitsOf (n : KNode) (t : Time) (cv : Nat) :
    ({n with ks := n.ks ++ [.time t]} : KNode).bitsOf cv = n.bitsOf cv := by
  simp [KNode.bitsOf, List.zipIdx_append, List.filterMap_append]

/-- The ordinary bitmap append, including insertion of a fresh time klong,
preserves physical well-formedness whenever the bitmap changes. -/
theorem KNode.add_delete_wf (n : KNode) (t : Time) (cv : Nat)
    (hw : klongsWf n.ks = true)
    (hne : bitsUnion n.lastBitmap (n.bitsOf cv) ≠ n.lastBitmap) :
    klongsWf (n.add t (.del (bitsUnion n.lastBitmap (n.bitsOf cv)))).ks = true := by
  have htime (ht : ∀ u, lastTimeOf n.ks = some u → u < t) :
      klongsWf (n.ks ++ [.time t, .del (bitsUnion n.lastBitmap (n.bitsOf cv))]) = true := by
    let base : KNode := {n with ks := n.ks ++ [.time t]}
    have hbase : klongsWf base.ks = true := klongsWf_append_time n.ks t hw ht
    have hbits : base.bitsOf cv = n.bitsOf cv := n.append_time_bitsOf t cv
    have hbitmap : base.lastBitmap = n.lastBitmap := by
      simp only [base, KNode.lastBitmap, lastBitmapOf, List.foldl_append,
        List.foldl_cons, List.foldl_nil]
    have hh := base.append_delete_wf cv hbase (by
      change (lastTimeOf (n.ks ++ [.time t])).isSome = true
      rw [lastTimeOf_append_time]; rfl)
      (by rwa [hbits, hbitmap])
    simpa only [base, hbits, hbitmap, List.append_assoc, List.singleton_append] using hh
  unfold KNode.add
  cases he : n.lastTime with
  | none =>
    apply htime
    intro u hu
    change n.lastTime = some u at hu
    rw [he] at hu
    cases hu
  | some u =>
    by_cases hu : u < t
    · simp only [hu, ↓reduceIte]
      apply htime
      intro a ha
      have hh : a = u := Option.some.inj (ha.symm.trans he)
      omega
    · simp only [hu, ↓reduceIte]
      exact n.append_delete_wf cv hw (by change n.lastTime.isSome = true; rw [he]; rfl) hne

end SIS.Tree
