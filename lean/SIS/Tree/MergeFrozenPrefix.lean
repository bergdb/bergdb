import SIS.Tree.MergeLiveOrder
import SIS.Tree.SortedKeys
import SIS.Tree.KeyWellFormed
import SIS.Tree.MergeHeightOrigins
import SIS.Tree.MergeLiveKeys

namespace SIS.Tree

open SIS SIS.Check

private theorem take_prefix_take {α : Type} (xs : List α) (a b : Nat) (hab : a ≤ b) :
    (xs.take a).IsPrefix (xs.take b) := by
  have hh := List.take_prefix a (xs.take b)
  simpa only [List.take_take,Nat.min_eq_left hab] using hh

private theorem prefix_time_map (t : Time) (xs ys : List (Nat × NodeId))
    (hp : xs.IsPrefix ys) :
    (Klong.time t :: xs.map (fun q => .key q.1 q.2)).IsPrefix
      (.time t :: ys.map (fun q => .key q.1 q.2)) := by
  obtain ⟨rest,hr⟩ := hp
  refine ⟨rest.map (fun q => .key q.1 q.2),?_⟩
  simp only [List.cons_append,← List.map_append,hr]

/-- A space split retains m original klongs below its divider in the first
node. These klongs do not come from the upward write that triggered it. -/
theorem halves_first_protected_prefix (p : Params) (hp : MergeParamsOK p)
    (leaf : Bool) (t : Time) (pairs ins : List (Nat × NodeId))
    (hs : pairs.Pairwise (fun a b => a.1 < b.1))
    (hfull : p.splitAbove < (⟨leaf,.time t :: pairs.map (fun q => .key q.1 q.2)⟩ : KNode).size) :
    let result := halves leaf t ⟨leaf,.time t :: pairs.map (fun q => .key q.1 q.2)⟩ ins
    (pairs.take p.mergeBelow).length = p.mergeBelow ∧
      (∀ q ∈ pairs.take p.mergeBelow, q.1 < result.2.2) ∧
      (Klong.time t :: (pairs.take p.mergeBelow).map (fun q => .key q.1 q.2)).IsPrefix result.1.ks := by
  have hcount : p.mergeBelow ≤ (pairs.take (pairs.length/2)).length :=
    halves_first_count p hp pairs hfull
  have hm : p.mergeBelow ≤ pairs.length/2 := by
    simp only [List.length_take] at hcount
    omega
  have hlen : p.mergeBelow ≤ pairs.length := by omega
  have hne : pairs.drop (pairs.length/2) ≠ [] := by
    have htwo := hp.1
    intro he
    have hh := congrArg List.length he
    simp only [List.length_drop,List.length_nil] at hh
    omega
  obtain ⟨r,rest,hr⟩ := List.exists_cons_of_ne_nil hne
  have hhead : (pairs.drop (pairs.length/2)).head? = some r := by rw [hr]; rfl
  have hdivider :
      (halves leaf t ⟨leaf,.time t :: pairs.map (fun q => .key q.1 q.2)⟩ ins).2.2 = r.1 := by
    cases ins with
    | nil => simp [halves,KNode.size,← List.map_drop,hr]
    | cons q ins =>
      by_cases hc : r.1 ≤ q.1 <;> simp [halves,KNode.size,← List.map_drop,hr,hc]
  refine ⟨by simp only [List.length_take,Nat.min_eq_left hlen],?_,?_⟩
  · intro q hq
    rw [hdivider]
    exact halves_left_lt_divider pairs (pairs.length/2) hs r hhead q
      ((take_prefix_take pairs _ _ hm).sublist.subset hq)
  · exact (prefix_time_map t _ _ (take_prefix_take pairs _ _ hm)).trans
      (halves_first_prefix leaf t pairs ins)

/-- If the left input to a merge starts with m protected klongs, the first
output starts with those same klongs, whether the merge makes one node or two. -/
theorem mergeKlongs_first_protected_prefix (p : Params) (hp : MergeParamsOK p)
    (inner : Bool) (cR : Nat) (left right : List (Nat × NodeId))
    (hleft : p.mergeBelow ≤ left.length) :
    (left.take p.mergeBelow).IsPrefix (mergeKlongs inner p.mergeMax cR left right).1 := by
  have hm : p.mergeBelow ≤ (p.mergeMax+1)/2 := hp.2.1
  unfold mergeKlongs splitMerged
  split
  · exact (List.take_prefix _ left).trans (List.prefix_append _ _)
  · rename_i hbig
    have hn : p.mergeBelow ≤ (mergeList inner cR left right).length := by
      rw [mergeList_length]
      omega
    have htake : p.mergeBelow ≤ ((mergeList inner cR left right).length+1)/2 := by omega
    have he : (mergeList inner cR left right).take p.mergeBelow = left.take p.mergeBelow :=
      List.take_append_of_le_length hleft
    rw [← he]
    exact take_prefix_take _ _ _ htake

theorem halves_first_no_delete (leaf : Bool) (t : Time)
    (pairs ins : List (Nat × NodeId)) :
    (halves leaf t ⟨leaf,newKlongs t pairs⟩ ins).1.lastBitmap = [] := by
  have he : (halves leaf t ⟨leaf,newKlongs t pairs⟩ ins).1.ks =
      newKlongs t (pairs.take (pairs.length/2)) ∨
      (halves leaf t ⟨leaf,newKlongs t pairs⟩ ins).1.ks =
        newKlongs t (pairs.take (pairs.length/2) ++ ins) := by
    cases hdrop : pairs.drop (pairs.length/2) with
    | nil =>
      cases ins <;>
        simp [halves,newKlongs,KNode.size,← List.map_take,← List.map_drop,hdrop]
    | cons q rest =>
      cases ins with
      | nil => simp [halves,newKlongs,KNode.size,← List.map_take,← List.map_drop,hdrop]
      | cons a ins =>
        by_cases hc : q.1 ≤ a.1 <;>
          simp [halves,newKlongs,KNode.size,← List.map_take,← List.map_drop,hdrop,hc]
  rcases he with he | he <;>
    simp only [KNode.lastBitmap,he,lastBitmapOf_newKlongs]

/-- The protected original klongs are live in the first half, even if the
upward write appends duplicate compare values after them. -/
theorem halves_first_protected_fill (p : Params) (hp : MergeParamsOK p)
    (leaf : Bool) (t : Time) (pairs ins : List (Nat × NodeId))
    (hs : pairs.Pairwise (fun a b => a.1 < b.1))
    (hfull : p.splitAbove < (⟨leaf,newKlongs t pairs⟩ : KNode).size) :
    p.mergeBelow ≤ (halves leaf t ⟨leaf,newKlongs t pairs⟩ ins).1.cnt := by
  obtain ⟨hlen,_,hprefix⟩ := halves_first_protected_prefix p hp leaf t pairs ins hs hfull
  have hn : ((pairs.take p.mergeBelow).map Prod.fst).Nodup := by
    apply List.pairwise_map.mpr
    apply List.Pairwise.imp _ (hs.sublist (List.take_sublist p.mergeBelow pairs))
    intro a b hab
    omega
  have hc := KNode.cnt_ge_key_prefix _ t (pairs.take p.mergeBelow) hn hprefix
    (halves_first_no_delete leaf t pairs ins)
  simpa only [hlen,newKlongs] using hc

/-- The first node made by a merge still has at least m live compare values
from its left input. Repeated compare values in the right input cannot erase
them. -/
theorem mergeKlongs_first_protected_fill (p : Params) (hp : MergeParamsOK p)
    (inner : Bool) (t : Time) (cR : Nat) (left right : List (Nat × NodeId))
    (hn : (left.map Prod.fst).Nodup) (hleft : p.mergeBelow ≤ left.length) :
    p.mergeBelow ≤
      (⟨!inner,newKlongs t (mergeKlongs inner p.mergeMax cR left right).1⟩ : KNode).cnt := by
  have hprefix := mergeKlongs_first_protected_prefix p hp inner cR left right hleft
  have hnodup : ((left.take p.mergeBelow).map Prod.fst).Nodup := by
    rw [List.map_take]
    exact hn.sublist (List.take_sublist _ _)
  have hc := KNode.cnt_ge_key_prefix
    ⟨!inner,newKlongs t (mergeKlongs inner p.mergeMax cR left right).1⟩
    t (left.take p.mergeBelow) hnodup
    (prefix_time_map t _ _ hprefix) (lastBitmapOf_newKlongs _ _)
  have hlen : (left.take p.mergeBelow).length = p.mergeBelow := by
    simp only [List.length_take,Nat.min_eq_left hleft]
  simpa only [hlen] using hc

end SIS.Tree
