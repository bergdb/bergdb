import SIS.Tree.MergeSearchOrder
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

/-- In a strictly ordered live list, enough keys below a cut force the
whole initial prefix of that length below the cut. -/
theorem ordered_take_below (pairs : List (Nat × NodeId)) (m cut : Nat)
    (hs : pairs.Pairwise (fun a b => a.1 < b.1))
    (hcount : m ≤ (pairs.filter (fun q => decide (q.1 < cut))).length) :
    ∀ q ∈ pairs.take m, q.1 < cut := by
  induction m generalizing pairs with
  | zero => simp
  | succ m ih =>
    cases pairs with
    | nil => simp at hcount
    | cons a pairs =>
      obtain ⟨hhead,htail⟩ := List.pairwise_cons.mp hs
      by_cases ha : a.1 < cut
      · have hc : m ≤ (pairs.filter (fun q => decide (q.1 < cut))).length := by
          simp only [List.filter_cons,ha,decide_true,↓reduceIte,List.length_cons] at hcount
          omega
        intro q hq
        simp only [List.take_succ_cons,List.mem_cons] at hq
        rcases hq with rfl | hq
        · exact ha
        · exact ih pairs htail hc q hq
      · have hf : pairs.filter (fun q => decide (q.1 < cut)) = [] := by
          apply List.filter_eq_nil_iff.mpr
          intro q hq
          have hqa := hhead q hq
          simp only [decide_eq_true_eq]
          omega
        simp only [List.filter_cons,ha,decide_false,Bool.false_eq_true,↓reduceIte,hf,
          List.length_nil] at hcount
        omega

/-- Normalizing a delete preserves an initial list of earlier live keys.
The result need not keep their old pointers, which may have been shadowed. -/
theorem KNode.delete_lastVersion_earlier_prefix (n : KNode) (t : Time)
    (cut cv : Nat) (keys : List Nat) (hn : keys.Nodup)
    (hcut : ∀ c ∈ keys, c < cut) (hcv : cut ≤ cv)
    (hk : ∀ c ∈ keys, ∃ y i, (.key c y,i) ∈ n.ks.zipIdx ∧ i ∉ n.lastBitmap) :
    ∃ pairs : List (Nat × NodeId),
      (n.lastVersionGivenDel t (bitsUnion n.lastBitmap (n.bitsOf cv))).ks = newKlongs t pairs ∧
      pairs.Pairwise (fun a b => a.1 < b.1) ∧
      (pairs.take keys.length).length = keys.length ∧
      ∀ q ∈ pairs.take keys.length, q.1 < cut := by
  let del := bitsUnion n.lastBitmap (n.bitsOf cv)
  obtain ⟨pairs,hpairs,hs⟩ := n.lastVersionGivenDel_order t del
  have hsub : ∀ c ∈ keys, c ∈ pairs.map Prod.fst := by
    intro c hc
    obtain ⟨y,i,hm,hi⟩ := hk c hc
    have hd := n.delete_preserves_earlier_key c cv y i hm hi (by have := hcut c hc; omega)
    have hh := (n.lastVersionGivenDel_has_key t del c).mpr ⟨y,i,hm,hd⟩
    rw [hpairs] at hh
    simpa only [List.filterMap_cons,List.filterMap_map,Function.comp_def,
      List.filterMap_eq_map'] using hh
  have hsubLow : ∀ c ∈ keys,
      c ∈ (pairs.filter (fun q => decide (q.1 < cut))).map Prod.fst := by
    intro c hc
    obtain ⟨q,hq,hqc⟩ := List.mem_map.mp (hsub c hc)
    refine List.mem_map.mpr ⟨q,List.mem_filter.mpr ⟨hq,?_⟩,hqc⟩
    simpa only [decide_eq_true_eq,hqc] using hcut c hc
  have hlen := hn.length_le_of_subset hsub
  have hcount := hn.length_le_of_subset hsubLow
  simp only [List.length_map] at hlen hcount
  exact ⟨pairs,hpairs,hs,by simp only [List.length_take,Nat.min_eq_left hlen],
    ordered_take_below pairs keys.length cut hs hcount⟩

theorem KNode.delete_lastVersion_sorted_terminal_prefix (n : KNode) (t : Time) (g : Nat)
    (keys : List Key) (key : Key) (cv : Nat)
    (hs : sortedKeys (keys ++ [key]) = true)
    (hw : ∀ a ∈ keys, keyWf a = true) (hkey : keyWf key = true)
    (hlen : ∀ a ∈ keys, a.length = g+1)
    (hp : ∀ a ∈ keys, a.take g = key.take g) (hcv : key[g]? = some cv)
    (hk : ∀ a ∈ keys, ∃ y i, (.key a[g]! y,i) ∈ n.ks.zipIdx ∧ i ∉ n.lastBitmap) :
    ∃ pairs : List (Nat × NodeId),
      (n.lastVersionGivenDel t (bitsUnion n.lastBitmap (n.bitsOf cv))).ks = newKlongs t pairs ∧
      pairs.Pairwise (fun a b => a.1 < b.1) ∧
      (pairs.take keys.length).length = keys.length ∧
      ∀ q ∈ pairs.take keys.length, q.1 < cv := by
  obtain ⟨hnd,hbefore⟩ := terminal_prefix_values_before keys key g cv hs hw hkey hlen hp hcv
  have he := n.delete_lastVersion_earlier_prefix t cv cv
    (keys.map (fun a => a[g]!)) hnd hbefore (Nat.le_refl _) (by
      intro c hc
      obtain ⟨a,ha,he⟩ := List.mem_map.mp hc
      subst c
      exact hk a ha)
  simpa only [List.length_map] using he

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

/-- A space split of a delete's normalized version retains m live keys
below the earlier cut whenever m such keys survived before the delete. -/
theorem KNode.halves_delete_earlier_prefix (n : KNode) (t : Time) (p : Params)
    (hp : MergeParamsOK p) (cut cv : Nat) (keys : List Nat)
    (hlen : keys.length = p.mergeBelow) (hn : keys.Nodup)
    (hcut : ∀ c ∈ keys, c < cut) (hcv : cut ≤ cv)
    (hk : ∀ c ∈ keys, ∃ y i, (.key c y,i) ∈ n.ks.zipIdx ∧ i ∉ n.lastBitmap)
    (ins : List (Nat × NodeId))
    (hfull : p.splitAbove < (n.lastVersionGivenDel t (bitsUnion n.lastBitmap (n.bitsOf cv))).size) :
    ∃ kept : List (Nat × NodeId),
      kept.length = p.mergeBelow ∧ kept.Pairwise (fun a b => a.1 < b.1) ∧
      (∀ q ∈ kept, q.1 < cut) ∧
      (newKlongs t kept).IsPrefix
        (halves n.leaf t (n.lastVersionGivenDel t (bitsUnion n.lastBitmap (n.bitsOf cv))) ins).1.ks ∧
      p.mergeBelow ≤
        (halves n.leaf t (n.lastVersionGivenDel t (bitsUnion n.lastBitmap (n.bitsOf cv))) ins).1.cnt := by
  obtain ⟨pairs,hpairs,hs,htake,hbefore⟩ :=
    n.delete_lastVersion_earlier_prefix t cut cv keys hn hcut hcv hk
  have hnode : n.lastVersionGivenDel t (bitsUnion n.lastBitmap (n.bitsOf cv)) =
      ⟨n.leaf,newKlongs t pairs⟩ := by
    change (⟨n.leaf,(n.lastVersionGivenDel t (bitsUnion n.lastBitmap (n.bitsOf cv))).ks⟩ : KNode) = _
    rw [hpairs]
  rw [hnode] at hfull ⊢
  obtain ⟨_,_,hprefix⟩ := halves_first_protected_prefix p hp n.leaf t pairs ins hs hfull
  rw [hlen] at htake hbefore
  exact ⟨pairs.take p.mergeBelow,htake,hs.sublist (List.take_sublist _ _),hbefore,
    hprefix,halves_first_protected_fill p hp n.leaf t pairs ins hs hfull⟩

end SIS.Tree
