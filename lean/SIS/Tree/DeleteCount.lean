import SIS.Tree.KlongRoundTripBits
import SIS.Tree.MergeLiveKeys

namespace SIS.Tree

open SIS SIS.Check

def KNode.liveCvsGivenDel (n : KNode) (del : List Nat) : List Nat :=
  (n.lastVersionGivenDel 0 del).ks.filterMap (fun k => match k with
    | .key c _ => some c | _ => none)

theorem KNode.liveCvsGivenDel_order (n : KNode) (del : List Nat) :
    (n.liveCvsGivenDel del).Pairwise (· < ·) := by
  obtain ⟨pairs,he,hs⟩ := n.lastVersionGivenDel_order 0 del
  have he' : n.liveCvsGivenDel del = pairs.map Prod.fst := by
    simp [KNode.liveCvsGivenDel,he,List.filterMap_map,Function.comp_def]
  rw [he']
  exact List.pairwise_map.mpr hs

theorem KNode.mem_liveCvsGivenDel (n : KNode) (del : List Nat) (a : Nat) :
    a ∈ n.liveCvsGivenDel del ↔ ∃ y i, (.key a y,i) ∈ n.ks.zipIdx ∧ i ∉ del := by
  refine Iff.trans ?_ (n.lastVersionGivenDel_has_key 0 del a)
  apply Iff.of_eq
  unfold KNode.liveCvsGivenDel
  congr 1

theorem KNode.mem_bitsOf_iff (n : KNode) (c i : Nat) :
    i ∈ n.bitsOf c ↔ ∃ y, (.key c y,i) ∈ n.ks.zipIdx := by
  constructor
  · intro hi
    obtain ⟨⟨k,j⟩,hj,hf⟩ := List.mem_filterMap.mp hi
    cases k with
    | time t => simp at hf
    | del bits => simp at hf
    | key a y =>
      simp only at hf
      split at hf
      · rename_i hac
        have hac' : a = c := by simpa using hac
        have hji : j = i := Option.some.inj hf
        subst a
        subst j
        exact ⟨y,hj⟩
      · cases hf
  · rintro ⟨y,hy⟩
    exact List.mem_filterMap.mpr ⟨(.key c y,i),hy,by simp⟩

theorem KNode.delete_liveCvs_mem (n : KNode) (cv a : Nat) :
    a ∈ n.liveCvsGivenDel (bitsUnion n.lastBitmap (n.bitsOf cv)) ↔
      a ∈ n.live.map Prod.fst ∧ a ≠ cv := by
  rw [n.mem_liveCvsGivenDel]
  constructor
  · rintro ⟨y,i,hk,hi⟩
    rw [mem_bitsUnion_iff] at hi
    have hh := not_or.mp hi
    refine ⟨(n.live_has_key a).mpr ⟨y,i,hk,hh.1⟩,?_⟩
    intro he
    subst a
    exact hh.2 ((n.mem_bitsOf_iff cv i).mpr ⟨y,hk⟩)
  · rintro ⟨ha,hac⟩
    obtain ⟨y,i,hk,hi⟩ := (n.live_has_key a).mp ha
    refine ⟨y,i,hk,?_⟩
    rw [mem_bitsUnion_iff]
    exact not_or.mpr ⟨hi,n.not_mem_bitsOf_of_key_ne a cv y i hk hac⟩

/-- A bitmap delete removes exactly its compare value from the live set,
even with shadows and earlier bitmaps in an arbitrary physical node. -/
theorem KNode.delete_liveCvs (n : KNode) (cv : Nat) :
    n.liveCvsGivenDel (bitsUnion n.lastBitmap (n.bitsOf cv)) =
      (n.live.map Prod.fst).filter (fun a => a != cv) := by
  apply sorted_nat_lists_eq
  · exact n.liveCvsGivenDel_order _
  · exact List.Pairwise.filter _ (List.pairwise_map.mpr n.live_order)
  · intro a
    rw [n.delete_liveCvs_mem]
    simp

theorem KNode.lastVersionGivenDel_cnt (n : KNode) (t : Time) (del : List Nat) :
    (n.lastVersionGivenDel t del).cnt = (n.liveCvsGivenDel del).length := by
  obtain ⟨pairs,he,hs⟩ := n.lastVersionGivenDel_order t del
  have hd : (pairs.map Prod.fst).Nodup := List.pairwise_map.mpr
    (hs.imp (by intro a b hab; omega))
  have hc := KNode.newKlongs_cnt n.leaf t pairs hd
  have hleaf : (n.lastVersionGivenDel t del).leaf = n.leaf := rfl
  have hn : n.lastVersionGivenDel t del = ⟨n.leaf,newKlongs t pairs⟩ := by
    cases hnode : n.lastVersionGivenDel t del
    simp only [hnode] at he hleaf
    cases he
    cases hleaf
    rfl
  rw [hn,hc]
  have he0 : (n.lastVersionGivenDel 0 del).ks = .time 0 :: pairs.map (fun q => .key q.1 q.2) := by
    have ht : (n.lastVersionGivenDel t del).ks.drop 1 =
        (n.lastVersionGivenDel 0 del).ks.drop 1 := rfl
    rw [he] at ht
    have hp : (n.lastVersionGivenDel 0 del).ks =
        .time 0 :: (n.lastVersionGivenDel 0 del).ks.drop 1 := rfl
    rw [hp,← ht]
    rfl
  simp [KNode.liveCvsGivenDel,he0,List.filterMap_map,Function.comp_def]

theorem nodup_filter_ne_length (xs : List Nat) (hn : xs.Nodup) (a : Nat) :
    (xs.filter (fun b => b != a)).length + (if a ∈ xs then 1 else 0) = xs.length := by
  induction xs with
  | nil => simp
  | cons b xs ih =>
    simp only [List.nodup_cons] at hn
    have ht := ih hn.2
    by_cases hba : b = a
    · subst b
      simp only [List.filter_cons,show (a != a) = false from by simp,
        Bool.false_eq_true,↓reduceIte,
        List.mem_cons_self,List.length_cons]
      simp only [hn.1,↓reduceIte,Nat.add_zero] at ht
      omega
    · have hab : a ≠ b := Ne.symm hba
      simp only [List.filter_cons,show (b != a) = true from by simp [hba],↓reduceIte,
        List.length_cons,List.mem_cons,hab,false_or]
      omega

/-- The normalized delete decreases count by exactly one if its compare
value was live, and by zero otherwise. No klong well-formedness is needed. -/
theorem KNode.delete_count_exact (n : KNode) (t : Time) (cv : Nat) :
    (n.lastVersionGivenDel t (bitsUnion n.lastBitmap (n.bitsOf cv))).cnt +
      (if cv ∈ n.live.map Prod.fst then 1 else 0) = n.cnt := by
  rw [n.lastVersionGivenDel_cnt,n.delete_liveCvs]
  simpa only [List.length_map,KNode.cnt] using
    nodup_filter_ne_length (n.live.map Prod.fst) n.live_keys_nodup cv

theorem KNode.delete_count_bounds (n : KNode) (t : Time) (cv : Nat) :
    let k := (n.lastVersionGivenDel t (bitsUnion n.lastBitmap (n.bitsOf cv))).cnt
    k ≤ n.cnt ∧ n.cnt ≤ k+1 := by
  have h := n.delete_count_exact t cv
  split at h <;> dsimp only <;> omega

theorem KNode.cnt_of_bitmap_and_keys (n changed : KNode) (del : List Nat)
    (hd : changed.lastBitmap = del)
    (hk : ∀ c y i, (.key c y,i) ∈ changed.ks.zipIdx ↔ (.key c y,i) ∈ n.ks.zipIdx) :
    changed.cnt = (n.liveCvsGivenDel del).length := by
  have he : changed.live.map Prod.fst = n.liveCvsGivenDel del := by
    apply sorted_nat_lists_eq
    · exact List.pairwise_map.mpr changed.live_order
    · exact n.liveCvsGivenDel_order del
    · intro a
      rw [changed.live_has_key,n.mem_liveCvsGivenDel,hd]
      constructor
      · rintro ⟨y,i,hi,hid⟩
        exact ⟨y,i,(hk a y i).mp hi,hid⟩
      · rintro ⟨y,i,hi,hid⟩
        exact ⟨y,i,(hk a y i).mpr hi,hid⟩
  simpa only [List.length_map,KNode.cnt] using congrArg List.length he

theorem key_mem_zipIdx_append_time_delete_iff (ks : List Klong) (t : Time)
    (bits : List Nat) (c : Nat) (y : NodeId) (i : Nat) :
    (Klong.key c y,i) ∈ (ks ++ [Klong.time t,Klong.del bits]).zipIdx ↔
      (Klong.key c y,i) ∈ ks.zipIdx := by
  simp [List.zipIdx_append]

theorem KNode.add_delete_preserves_key_indices (n : KNode) (t : Time) (bits : List Nat)
    (c : Nat) (y : NodeId) (i : Nat) :
    (.key c y,i) ∈ (n.add t (.del bits)).ks.zipIdx ↔ (.key c y,i) ∈ n.ks.zipIdx := by
  unfold KNode.add
  split
  · split
    · exact key_mem_zipIdx_append_time_delete_iff _ _ _ _ _ _
    · exact key_mem_zipIdx_append_delete_iff _ _ _ _ _
  · exact key_mem_zipIdx_append_time_delete_iff _ _ _ _ _ _

/-- The ordinary bitmap append has the same exact one-key count decrease
as normalization. It includes either choice of the added time klong. -/
theorem KNode.add_delete_count_exact (n : KNode) (t : Time) (cv : Nat) :
    (n.add t (.del (bitsUnion n.lastBitmap (n.bitsOf cv)))).cnt +
      (if cv ∈ n.live.map Prod.fst then 1 else 0) = n.cnt := by
  rw [n.cnt_of_bitmap_and_keys _ _ (n.add_delete_lastBitmap _ _)
    (n.add_delete_preserves_key_indices _ _)]
  have h := n.delete_count_exact t cv
  rwa [n.lastVersionGivenDel_cnt] at h

/-- Updating an existing last bitmap in place has that same count decrease. -/
theorem KNode.setAt_delete_count_exact (n : KNode) (cv : Nat) (old : List Nat)
    (hlast : n.ks.getLast? = some (.del old)) :
    (n.setAt (n.size-1) (.del (bitsUnion n.lastBitmap (n.bitsOf cv)))).cnt +
      (if cv ∈ n.live.map Prod.fst then 1 else 0) = n.cnt := by
  obtain ⟨pre,hpre⟩ := List.getLast?_eq_some_iff.mp hlast
  have hnew := n.setAt_last_delete_ks pre old (bitsUnion n.lastBitmap (n.bitsOf cv)) hpre
  have hd : (n.setAt (n.size-1) (.del (bitsUnion n.lastBitmap (n.bitsOf cv)))).lastBitmap =
      bitsUnion n.lastBitmap (n.bitsOf cv) := by
    change lastBitmapOf _ = _
    rw [hnew,lastBitmapOf_append_delete]
  have hk : ∀ c y i,
      (.key c y,i) ∈ (n.setAt (n.size-1) (.del (bitsUnion n.lastBitmap (n.bitsOf cv)))).ks.zipIdx ↔
        (.key c y,i) ∈ n.ks.zipIdx := by
    intro c y i
    rw [hnew,hpre,key_mem_zipIdx_append_delete_iff,key_mem_zipIdx_append_delete_iff]
  rw [n.cnt_of_bitmap_and_keys _ _ hd hk]
  have h := n.delete_count_exact 0 cv
  rwa [n.lastVersionGivenDel_cnt] at h

end SIS.Tree
