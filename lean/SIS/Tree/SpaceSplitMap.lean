import SIS.Tree.TimeSplitMap
import SIS.Tree.SplitLiveFill
import SIS.Tree.SegmentRange

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- Physical duplicate keys select the last pointer, including in a split
output whose inserted klongs have not been normalized. -/
theorem KNode.newKlongs_live_lookup_fold (leaf : Bool) (t : Time)
    (pairs : List (Nat × NodeId)) (c : Nat) :
    (⟨leaf, newKlongs t pairs⟩ : KNode).live.lookup c =
      pairs.foldl (pairLookupStep c) none := by
  rw [KNode.live_lookup]
  change keyLookup (newKlongs t pairs) (lastBitmapOf (newKlongs t pairs)) c = _
  rw [lastBitmapOf_newKlongs]
  unfold keyLookup
  simp only [newKlongs, List.zipIdx_cons, List.foldl_cons, keyLookupStep]
  exact keyLookup_keys_fold pairs 1 c none

theorem pairLookupFold_eq_lookup (pairs : List (Nat × NodeId)) (c : Nat)
    (hn : (pairs.map Prod.fst).Nodup) :
    pairs.foldl (pairLookupStep c) none = pairs.lookup c := by
  rw [← KNode.newKlongs_live_lookup_fold true 0,
    KNode.newKlongs_live_lookup true 0 pairs hn]

theorem pairLookupFold_miss (pairs : List (Nat × NodeId)) (c : Nat)
    (acc : Option NodeId) (hm : ∀ q ∈ pairs, q.1 ≠ c) :
    pairs.foldl (pairLookupStep c) acc = acc := by
  induction pairs generalizing acc with
  | nil => rfl
  | cons q pairs ih =>
    simp only [List.foldl_cons, pairLookupStep,
      beq_eq_false_iff_ne.mpr (hm q List.mem_cons_self), Bool.false_eq_true, ↓reduceIte]
    exact ih acc (fun r hr => hm r (List.mem_cons_of_mem q hr))

/-- The leaf split's exact physical shape. Its route is determined by the
first inserted compare value, as in the writer. -/
theorem halves_leaf_shape (t : Time) (pairs ins : List (Nat × NodeId))
    (r : Nat × NodeId) (hr : (pairs.drop (pairs.length / 2)).head? = some r) :
    halves true t ⟨true, newKlongs t pairs⟩ ins =
      if (match ins.head? with | some q => decide (r.1 ≤ q.1) | none => false) then
        (⟨true, newKlongs t (pairs.take (pairs.length / 2))⟩,
         ⟨true, newKlongs t (pairs.drop (pairs.length / 2) ++ ins)⟩, r.1)
      else
        (⟨true, newKlongs t (pairs.take (pairs.length / 2) ++ ins)⟩,
         ⟨true, newKlongs t (pairs.drop (pairs.length / 2))⟩, r.1) := by
  cases hd : pairs.drop (pairs.length / 2) with
  | nil => simp [hd] at hr
  | cons q rest =>
    have hqr : q = r := by simpa [hd] using hr
    subst q
    unfold halves
    simp only [newKlongs, KNode.size, List.length_cons, List.length_map,
      Nat.add_sub_cancel, List.drop_succ_cons, List.drop_zero,
      ← List.map_take, ← List.map_drop, hd, List.map_cons,
      List.head?_cons, Bool.not_true, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
    cases ins <;> simp [newKlongs, List.map_append]

theorem halves_right_ge_divider (pairs : List (Nat × NodeId)) (k : Nat)
    (hs : CvSorted pairs) (r : Nat × NodeId) (hr : (pairs.drop k).head? = some r) :
    ∀ q ∈ pairs.drop k, r.1 ≤ q.1 := by
  have hd := hs.sublist (List.drop_sublist k pairs)
  cases he : pairs.drop k with
  | nil => simp [he] at hr
  | cons a rest =>
    have ha : a = r := by simpa [he] using hr
    subst a
    rw [he] at hd
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · omega
    · have hh := (List.pairwise_cons.mp hd).1 q hq
      omega

/-- A leaf space split represents exactly the old map followed by the
inserted overwrites. All inserts must belong to the side chosen by their
first key. Duplicate inserts are allowed and select the last pointer. -/
theorem halves_leaf_lookup (t : Time) (pairs ins : List (Nat × NodeId))
    (hs : CvSorted pairs) (r : Nat × NodeId)
    (hr : (pairs.drop (pairs.length / 2)).head? = some r)
    (hside : ∀ q ∈ ins, decide (r.1 ≤ q.1) =
      (match ins.head? with | some a => decide (r.1 ≤ a.1) | none => false))
    (c : Nat) :
    let out := halves true t ⟨true, newKlongs t pairs⟩ ins
    (if c < out.2.2 then out.1.live.lookup c else out.2.1.live.lookup c) =
      ins.foldl (pairLookupStep c) (pairs.lookup c) := by
  have hn : (pairs.map Prod.fst).Nodup :=
    List.pairwise_map.mpr (hs.imp (by intro a b hab; omega))
  have hleft := halves_left_lt_divider pairs (pairs.length / 2) hs r hr
  have hright := halves_right_ge_divider pairs (pairs.length / 2) hs r hr
  have hmap : pairs.lookup c =
      (pairs.take (pairs.length / 2) ++ pairs.drop (pairs.length / 2)).foldl
        (pairLookupStep c) none := by
    rw [List.take_append_drop, pairLookupFold_eq_lookup pairs c hn]
  rw [halves_leaf_shape t pairs ins r hr]
  cases hroute : (match ins.head? with | some a => decide (r.1 ≤ a.1) | none => false) with
  | true =>
    simp only [hroute, ↓reduceIte]
    rw [hmap, List.foldl_append]
    have hin : ∀ q ∈ ins, r.1 ≤ q.1 := by
      intro q hq
      have hh := hside q hq
      rw [hroute] at hh
      exact of_decide_eq_true hh
    by_cases hc : c < r.1
    · simp only [hc, ↓reduceIte, KNode.newKlongs_live_lookup_fold]
      rw [pairLookupFold_miss (pairs.drop _) c _ (by
        intro q hq he; have hh := hright q hq; omega)]
      rw [pairLookupFold_miss ins c _ (by
        intro q hq he; have hh := hin q hq; omega)]
    · simp only [hc, ↓reduceIte, KNode.newKlongs_live_lookup_fold, List.foldl_append]
      rw [pairLookupFold_miss (pairs.take _) c _ (by
        intro q hq he; have hh := hleft q hq; omega)]
  | false =>
    simp only [hroute, Bool.false_eq_true, ↓reduceIte]
    rw [hmap, List.foldl_append]
    have hin : ∀ q ∈ ins, q.1 < r.1 := by
      intro q hq
      have hh := hside q hq
      rw [hroute] at hh
      have hh' := of_decide_eq_false hh
      omega
    by_cases hc : c < r.1
    · simp only [hc, ↓reduceIte, KNode.newKlongs_live_lookup_fold, List.foldl_append]
      rw [pairLookupFold_miss (pairs.drop _) c _ (by
        intro q hq he; have hh := hright q hq; omega)]
    · simp only [hc, ↓reduceIte, KNode.newKlongs_live_lookup_fold]
      rw [pairLookupFold_miss (pairs.take _) c _ (by
        intro q hq he; have hh := hleft q hq; omega)]
      rw [pairLookupFold_miss ins c _ (by
        intro q hq he; have hh := hin q hq; omega)]

/-- The local compare value in the right half of an inner split. -/
def splitLocalCv (leaf : Bool) (sc c : Nat) : Nat :=
  if !leaf && c == sc then 0 else c

theorem splitLocalCv_eq_iff (leaf : Bool) (sc a b : Nat)
    (hsc : 0 < sc) (ha : sc ≤ a) (hb : sc ≤ b) :
    splitLocalCv leaf sc a = splitLocalCv leaf sc b ↔ a = b := by
  cases leaf <;> by_cases h₁ : a = sc <;> by_cases h₂ : b = sc <;>
    simp_all [splitLocalCv] <;> omega

theorem pairLookupFold_splitLocalCv (leaf : Bool) (sc c : Nat)
    (pairs : List (Nat × NodeId)) (acc : Option NodeId)
    (hsc : 0 < sc) (hc : sc ≤ c) (hp : ∀ q ∈ pairs, sc ≤ q.1) :
    (pairs.map (fun q => (splitLocalCv leaf sc q.1, q.2))).foldl
      (pairLookupStep (splitLocalCv leaf sc c)) acc =
      pairs.foldl (pairLookupStep c) acc := by
  induction pairs generalizing acc with
  | nil => rfl
  | cons q pairs ih =>
    simp only [List.map_cons, List.foldl_cons]
    have hstep : pairLookupStep (splitLocalCv leaf sc c) acc
        (splitLocalCv leaf sc q.1, q.2) = pairLookupStep c acc q := by
      simp only [pairLookupStep]
      have he := splitLocalCv_eq_iff leaf sc q.1 c hsc (hp q List.mem_cons_self) hc
      by_cases hh : q.1 = c
      · simp [hh]
      · have hm : splitLocalCv leaf sc q.1 ≠ splitLocalCv leaf sc c := by
          intro hh'; exact hh (he.mp hh')
        simp [hm, hh]
    rw [hstep]
    exact ih _ (fun r hr => hp r (List.mem_cons_of_mem q hr))

theorem secondSplitPairs_eq_map (leaf : Bool) (pairs : List (Nat × NodeId))
    (hs : CvSorted pairs) (r : Nat × NodeId)
    (hr : (pairs.drop (pairs.length / 2)).head? = some r) :
    secondSplitPairs leaf pairs = (pairs.drop (pairs.length / 2)).map
      (fun q => (splitLocalCv leaf r.1 q.1, q.2)) := by
  cases leaf with
  | true => simp [secondSplitPairs, splitLocalCv]
  | false =>
    have hd := hs.sublist (List.drop_sublist (pairs.length / 2) pairs)
    cases he : pairs.drop (pairs.length / 2) with
    | nil => simp [he] at hr
    | cons a rest =>
      have ha : a = r := by simpa [he] using hr
      subst a
      rw [he] at hd
      simp only [secondSplitPairs, Bool.false_eq_true, ↓reduceIte, he, renameHead,
        List.map_cons, splitLocalCv, Bool.not_false, Bool.true_and, beq_self_eq_true]
      congr 1
      symm
      calc
        _ = rest.map (fun q => q) := by
          apply List.map_congr_left
          intro q hq
          have hq' := (List.pairwise_cons.mp hd).1 q hq
          have hne : q.1 ≠ r.1 := by omega
          simp [beq_eq_false_iff_ne.mpr hne]
        _ = rest := List.map_id' rest

theorem halves_shape (leaf : Bool) (t : Time) (pairs ins : List (Nat × NodeId))
    (r : Nat × NodeId) (hr : (pairs.drop (pairs.length / 2)).head? = some r) :
    halves leaf t ⟨leaf, newKlongs t pairs⟩ ins =
      if (match ins.head? with | some q => decide (r.1 ≤ q.1) | none => false) then
        (⟨leaf, newKlongs t (pairs.take (pairs.length / 2))⟩,
         ⟨leaf, newKlongs t (secondSplitPairs leaf pairs ++
           ins.map (fun q => (splitLocalCv leaf r.1 q.1, q.2)))⟩, r.1)
      else
        (⟨leaf, newKlongs t (pairs.take (pairs.length / 2) ++ ins)⟩,
         ⟨leaf, newKlongs t (secondSplitPairs leaf pairs)⟩, r.1) := by
  cases hd : pairs.drop (pairs.length / 2) with
  | nil => simp [hd] at hr
  | cons q rest =>
    have hqr : q = r := by simpa [hd] using hr
    subst q
    unfold halves
    simp only [newKlongs, KNode.size, List.length_cons, List.length_map,
      Nat.add_sub_cancel, List.drop_succ_cons, List.drop_zero,
      ← List.map_take, ← List.map_drop, hd, List.map_cons, List.head?_cons]
    cases leaf <;> cases ins with
    | nil => simp [newKlongs, List.map_append, secondSplitPairs, hd, renameHead, splitLocalCv]
    | cons a more =>
      by_cases hc : r.1 ≤ a.1 <;>
        simp [newKlongs, List.map_append, secondSplitPairs, hd, renameHead,
          splitLocalCv, List.map_map, Function.comp_def, hc]
      all_goals
        simp only [apply_ite (Klong.key · a.2)]
        constructor
        · trivial
        · intro q y hq; split <;> rfl

/-- Both leaf and inner space splits preserve their compare-value map. On
the right of an inner split, the separator's local name is the empty key.
The side condition is exactly the writer's common-side requirement. -/
theorem halves_lookup (leaf : Bool) (t : Time) (pairs ins : List (Nat × NodeId))
    (hs : CvSorted pairs) (r : Nat × NodeId)
    (hr : (pairs.drop (pairs.length / 2)).head? = some r) (hsc : 0 < r.1)
    (hside : ∀ q ∈ ins, decide (r.1 ≤ q.1) =
      (match ins.head? with | some a => decide (r.1 ≤ a.1) | none => false))
    (c : Nat) :
    let out := halves leaf t ⟨leaf, newKlongs t pairs⟩ ins
    (if c < out.2.2 then out.1.live.lookup c
      else out.2.1.live.lookup (splitLocalCv leaf out.2.2 c)) =
      ins.foldl (pairLookupStep c) (pairs.lookup c) := by
  have hn : (pairs.map Prod.fst).Nodup :=
    List.pairwise_map.mpr (hs.imp (by intro a b hab; omega))
  have hleft := halves_left_lt_divider pairs (pairs.length / 2) hs r hr
  have hright := halves_right_ge_divider pairs (pairs.length / 2) hs r hr
  have hmap : pairs.lookup c =
      (pairs.take (pairs.length / 2) ++ pairs.drop (pairs.length / 2)).foldl
        (pairLookupStep c) none := by
    rw [List.take_append_drop, pairLookupFold_eq_lookup pairs c hn]
  rw [halves_shape leaf t pairs ins r hr]
  cases hroute : (match ins.head? with | some a => decide (r.1 ≤ a.1) | none => false) with
  | true =>
    simp only [↓reduceIte]
    rw [hmap, List.foldl_append]
    have hin : ∀ q ∈ ins, r.1 ≤ q.1 := by
      intro q hq
      have hh := hside q hq
      rw [hroute] at hh
      exact of_decide_eq_true hh
    by_cases hc : c < r.1
    · simp only [hc, ↓reduceIte, KNode.newKlongs_live_lookup_fold]
      rw [pairLookupFold_miss (pairs.drop _) c _ (by
        intro q hq he; have hh := hright q hq; omega)]
      rw [pairLookupFold_miss ins c _ (by
        intro q hq he; have hh := hin q hq; omega)]
    · simp only [hc, ↓reduceIte, KNode.newKlongs_live_lookup_fold, List.foldl_append]
      rw [secondSplitPairs_eq_map leaf pairs hs r hr,
        pairLookupFold_splitLocalCv leaf r.1 c _ _ hsc (by omega) hright,
        pairLookupFold_splitLocalCv leaf r.1 c _ _ hsc (by omega) hin]
      rw [pairLookupFold_miss (pairs.take _) c _ (by
        intro q hq he; have hh := hleft q hq; omega)]
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [hmap, List.foldl_append]
    have hin : ∀ q ∈ ins, q.1 < r.1 := by
      intro q hq
      have hh := hside q hq
      rw [hroute] at hh
      have hh' := of_decide_eq_false hh
      omega
    by_cases hc : c < r.1
    · simp only [hc, ↓reduceIte, KNode.newKlongs_live_lookup_fold, List.foldl_append]
      rw [pairLookupFold_miss (pairs.drop _) c _ (by
        intro q hq he; have hh := hright q hq; omega)]
    · simp only [hc, ↓reduceIte, KNode.newKlongs_live_lookup_fold]
      rw [secondSplitPairs_eq_map leaf pairs hs r hr,
        pairLookupFold_splitLocalCv leaf r.1 c _ _ hsc (by omega) hright]
      rw [pairLookupFold_miss (pairs.take _) c _ (by
        intro q hq he; have hh := hleft q hq; omega)]
      rw [pairLookupFold_miss ins c _ (by
        intro q hq he; have hh := hin q hq; omega)]

/-- A separator cannot cut through one of the parent's existing child
intervals. This derives the split route from the child's checked range. -/
theorem divider_side_of_child_range (pairs : List (Nat × NodeId)) (hi : Option Nat)
    (hs : CvSorted pairs) (q : Nat × NodeId) (b : Option Nat)
    (hq : (q,b) ∈ childBounds pairs hi) (r : Nat × NodeId) (hr : r ∈ pairs)
    (cv : Nat) (hlo : q.1 ≤ cv) (hhi : UpperBound b cv) :
    decide (r.1 ≤ cv) = decide (r.1 ≤ q.1) := by
  by_cases hc : r.1 ≤ cv
  · have hh := childBounds_dominates pairs hi hs q b hq cv hhi r hr hc
    simp [hc, hh]
  · have hh : ¬ r.1 ≤ q.1 := by omega
    simp [hc, hh]

theorem halves_common_side_of_child_range (pairs ins : List (Nat × NodeId))
    (hi : Option Nat) (hs : CvSorted pairs) (q : Nat × NodeId) (b : Option Nat)
    (hq : (q,b) ∈ childBounds pairs hi) (r : Nat × NodeId)
    (hr : (pairs.drop (pairs.length / 2)).head? = some r)
    (hins : ∀ a ∈ ins, q.1 ≤ a.1 ∧ UpperBound b a.1) :
    ∀ a ∈ ins, decide (r.1 ≤ a.1) =
      (match ins.head? with | some first => decide (r.1 ≤ first.1) | none => false) := by
  have hrmem : r ∈ pairs := List.mem_of_mem_drop (List.mem_of_head? hr)
  intro a ha
  have hside := divider_side_of_child_range pairs hi hs q b hq r hrmem a.1 (hins a ha).1 (hins a ha).2
  cases hh : ins.head? with
  | none =>
    have he : ins = [] := List.head?_eq_none_iff.mp hh
    simp [he] at ha
  | some first =>
    have hf := hins first (List.mem_of_head? hh)
    exact hside.trans (divider_side_of_child_range pairs hi hs q b hq r hrmem first.1 hf.1 hf.2).symm

/-- When inserts replace children within one checked old interval, the
pure split map theorem needs no separate common-side assumption. -/
theorem halves_lookup_of_child_range (leaf : Bool) (t : Time)
    (pairs ins : List (Nat × NodeId)) (hi : Option Nat) (hs : CvSorted pairs)
    (q : Nat × NodeId) (b : Option Nat) (hq : (q,b) ∈ childBounds pairs hi)
    (r : Nat × NodeId) (hr : (pairs.drop (pairs.length / 2)).head? = some r)
    (hsc : 0 < r.1) (hins : ∀ a ∈ ins, q.1 ≤ a.1 ∧ UpperBound b a.1) (cv : Nat) :
    let out := halves leaf t ⟨leaf, newKlongs t pairs⟩ ins
    (if cv < out.2.2 then out.1.live.lookup cv
      else out.2.1.live.lookup (splitLocalCv leaf out.2.2 cv)) =
      ins.foldl (pairLookupStep cv) (pairs.lookup cv) :=
  halves_lookup leaf t pairs ins hs r hr hsc
    (halves_common_side_of_child_range pairs ins hi hs q b hq r hr hins) cv

end SIS.Tree
