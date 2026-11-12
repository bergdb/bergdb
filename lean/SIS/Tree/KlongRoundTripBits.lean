import SIS.Tree.SearchEqProof

namespace SIS.Tree

open SIS SIS.Check

theorem nat_adjacent_head_lt (a : Nat) (xs : List Nat)
    (h : ((a :: xs).zip xs).all (fun q => decide (q.1 < q.2)) = true) :
    ∀ b ∈ xs, a < b := by
  induction xs generalizing a with
  | nil => simp
  | cons b xs ih =>
    simp only [List.zip_cons_cons,List.all_cons,Bool.and_eq_true,decide_eq_true_eq] at h
    intro c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · exact h.1
    · exact Nat.lt_trans h.1 (ih b h.2 c hc)

theorem nat_adjacent_pairwise (xs : List Nat)
    (h : (xs.zip (xs.drop 1)).all (fun q => decide (q.1 < q.2)) = true) :
    xs.Pairwise (· < ·) := by
  induction xs with
  | nil => exact .nil
  | cons a xs ih =>
    simp only [List.drop_succ_cons,List.drop_zero] at h
    refine List.pairwise_cons.mpr ⟨nat_adjacent_head_lt a xs h,ih ?_⟩
    cases xs with
    | nil => rfl
    | cons b xs =>
      simp only [List.zip_cons_cons,List.all_cons,Bool.and_eq_true] at h
      exact h.2

theorem klongsWf_bitmap_order (ks : List Klong) (hw : klongsWf ks = true)
    (i : Nat) (bits : List Nat) (hk : ks[i]? = some (.del bits)) :
    (lastBitmapOf (ks.take i)).length < bits.length ∧ bits.Pairwise (· < ·) := by
  have hs := klongsWfState_ok ks hw (i+1)
  rw [klongsWfState_succ ks i (.del bits) hk] at hs
  simp only [klongsWfStep,Bool.and_eq_true] at hs
  refine ⟨?_,nat_adjacent_pairwise bits hs.1.1.2⟩
  simpa only [klongsWfState_bitmap,decide_eq_true_eq] using hs.1.1.1.2

theorem sorted_nat_lists_eq (a b : List Nat) (ha : a.Pairwise (· < ·))
    (hb : b.Pairwise (· < ·)) (hm : ∀ i, i ∈ a ↔ i ∈ b) : a = b := by
  have hna : a.Nodup := ha.imp (by intro x y hxy; omega)
  have hnb : b.Nodup := hb.imp (by intro x y hxy; omega)
  have hp : a.Perm b := (List.perm_ext_iff_of_nodup hna hnb).mpr hm
  exact List.Perm.eq_of_pairwise (le := (· ≤ ·)) (by intro x y _ _ hxy hyx; omega)
    (ha.imp (by intro x y hxy; omega)) (hb.imp (by intro x y hxy; omega)) hp

def bitmapEntryCvs (ks : List Klong) (old bits : List Nat) : List Nat :=
  ((bits.filter (fun b => !old.contains b)).filterMap (cvAt ks)).eraseDups.mergeSort
    (fun x y => decide (x ≤ y))

theorem mem_bitmapEntryCvs (ks : List Klong) (old bits : List Nat) (c : Nat) :
    c ∈ bitmapEntryCvs ks old bits ↔ ∃ b ∈ bits, b ∉ old ∧ cvAt ks b = some c := by
  simp [bitmapEntryCvs,List.mem_filterMap,List.mem_filter,and_assoc]

theorem cvAt_eq_some_iff (ks : List Klong) (i c : Nat) :
    cvAt ks i = some c ↔ ∃ y, ks[i]? = some (.key c y) := by
  unfold cvAt
  cases he : ks[i]? with
  | none => simp
  | some k => cases k <;> simp [Klong.key.injEq]

def bitmapMore (pre : List Klong) (cs : List Nat) : List Nat :=
  pre.zipIdx.filterMap (fun (k,i) => match k with
    | .key c _ => if cs.contains c then some i else none
    | _ => none)

theorem mem_bitmapMore (pre : List Klong) (cs : List Nat) (j : Nat) :
    j ∈ bitmapMore pre cs ↔ ∃ c y, pre[j]? = some (.key c y) ∧ c ∈ cs := by
  constructor
  · intro hj
    obtain ⟨⟨k,i⟩,hi,hf⟩ := List.mem_filterMap.mp hj
    cases k with
    | time t => simp at hf
    | del bits => simp at hf
    | key c y =>
      simp only at hf
      split at hf
      · rename_i hc
        have he : i = j := Option.some.inj hf
        subst i
        exact ⟨c,y,List.mem_zipIdx_iff_getElem?.mp hi,by simpa using hc⟩
      · cases hf
  · rintro ⟨c,y,hkey,hc⟩
    apply List.mem_filterMap.mpr
    refine ⟨(.key c y,j),List.mem_zipIdx_iff_getElem?.mpr hkey,?_⟩
    simp [hc]

/-- A well-formed bitmap writes a nonempty compare-value delete entry, so
it cannot be confused with the marker entry. -/
theorem bitmapEntryCvs_ne_nil (ks : List Klong) (hw : klongsWf ks = true)
    (i : Nat) (bits : List Nat) (hk : ks[i]? = some (.del bits)) :
    bitmapEntryCvs ks (lastBitmapOf (ks.take i)) bits ≠ [] := by
  obtain ⟨hlen,horder⟩ := klongsWf_bitmap_order ks hw i bits hk
  have hbits := (klongsWf_bitmapRules ks hw i bits hk).1
  intro hnil
  have hsub : ∀ b ∈ bits, b ∈ lastBitmapOf (ks.take i) := by
    intro b hb
    by_cases hn : b ∈ lastBitmapOf (ks.take i)
    · exact hn
    · have hsome := (hbits b hb).2
      cases hc : cvAt ks b with
      | none => simp [hc] at hsome
      | some c =>
        have hm := (mem_bitmapEntryCvs ks _ bits c).mpr ⟨b,hb,hn,hc⟩
        simp [hnil] at hm
  have hn : bits.Nodup := horder.imp (by intro x y hxy; omega)
  have := hn.length_le_of_subset hsub
  omega

theorem nat_eraseDups_nodup (xs : List Nat) : xs.eraseDups.Nodup := by
  cases xs with
  | nil => simp
  | cons a xs =>
    rw [List.eraseDups_cons]
    refine List.nodup_cons.mpr ⟨?_,nat_eraseDups_nodup _⟩
    simp
termination_by xs.length
decreasing_by
  have := List.length_filter_le (fun b : Nat => !(b == a)) xs
  simp only [List.length_cons]
  omega

theorem bitsUnion_pairwise (old more : List Nat) :
    (bitsUnion old more).Pairwise (· < ·) := by
  have hs : (bitsUnion old more).Pairwise (· ≤ ·) := by
    simpa only [bitsUnion,decide_eq_true_eq] using
      List.pairwise_mergeSort (le := fun (a b : Nat) => decide (a ≤ b))
        (by intro a b c hab hbc; simp only [decide_eq_true_eq] at *; omega)
        (by intro a b; simp only [Bool.or_eq_true,decide_eq_true_eq]; omega)
        ((old ++ more).eraseDups)
  have hn : (bitsUnion old more).Nodup := by
    exact (List.mergeSort_perm _ _).nodup_iff.mpr (nat_eraseDups_nodup _)
  exact (hs.and hn).imp (by intro a b hab; omega)

/-- Decoding the compare values of a valid bitmap reconstructs its exact
physical bit list, including previously deleted occurrences. -/
theorem bitmapEntryCvs_roundTrip (ks : List Klong) (hw : klongsWf ks = true)
    (i : Nat) (bits : List Nat) (hk : ks[i]? = some (.del bits)) :
    bitsUnion (lastBitmapOf (ks.take i))
      (bitmapMore (ks.take i) (bitmapEntryCvs ks (lastBitmapOf (ks.take i)) bits)) = bits := by
  obtain ⟨hb,hm,hc⟩ := klongsWf_bitmapRules ks hw i bits hk
  have ho := (klongsWf_bitmap_order ks hw i bits hk).2
  apply sorted_nat_lists_eq _ bits (bitsUnion_pairwise _ _) ho
  intro j
  simp only [bitsUnion,List.mem_mergeSort,List.mem_eraseDups,List.mem_append]
  constructor
  · rintro (hj | hj)
    · exact hm j hj
    · obtain ⟨c,y,hkey,hcs⟩ := (mem_bitmapMore _ _ j).mp hj
      have hji : j < i := by
        have := (List.getElem?_eq_some_iff.mp hkey).1
        simp only [List.length_take] at this
        omega
      have hget : ks[j]? = some (.key c y) := by
        simpa only [List.getElem?_take,hji,↓reduceIte] using hkey
      obtain ⟨b,hbb,hbold,hbc⟩ := (mem_bitmapEntryCvs ks _ bits c).mp hcs
      exact hc b hbb hbold c hbc j hji (by simp only [cvAt,hget])
  · intro hj
    by_cases hjold : j ∈ lastBitmapOf (ks.take i)
    · exact Or.inl hjold
    · right
      have hji := (hb j hj).1
      have hsome := (hb j hj).2
      cases hcv : cvAt ks j with
      | none => simp [hcv] at hsome
      | some c =>
        obtain ⟨y,hkey⟩ := (cvAt_eq_some_iff ks j c).mp hcv
        apply (mem_bitmapMore _ _ j).mpr
        refine ⟨c,y,?_,(mem_bitmapEntryCvs ks _ bits c).mpr ⟨j,hj,hjold,hcv⟩⟩
        simpa only [List.getElem?_take,hji,↓reduceIte] using hkey

end SIS.Tree
