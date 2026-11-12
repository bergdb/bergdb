import SIS.Tree.MergeFrozenPrefix

namespace SIS.Tree

open SIS SIS.Check

def secondSplitPairs (leaf : Bool) (pairs : List (Nat × NodeId)) : List (Nat × NodeId) :=
  if leaf then pairs.drop (pairs.length/2) else renameHead 0 (pairs.drop (pairs.length/2))

def splitInsertPairs (leaf : Bool) (sc : Nat) (ins : List (Nat × NodeId)) : List (Nat × NodeId) :=
  ins.map (fun q => (if !leaf && q.1 == sc then 0 else q.1,q.2))

theorem splitInsertPairs_klongs (leaf : Bool) (sc : Nat) (ins : List (Nat × NodeId)) :
    (splitInsertPairs leaf sc ins).map (fun q => Klong.key q.1 q.2) =
      ins.map (fun q => if !leaf && q.1 == sc then Klong.key 0 q.2 else Klong.key q.1 q.2) := by
  simp only [splitInsertPairs,List.map_map,Function.comp_def]
  congr 1
  funext q
  split <;> rfl

theorem key_zero_ite (c y : Nat) :
    (if c = 0 then Klong.key 0 y else Klong.key c y) = Klong.key c y := by
  by_cases hc : c = 0 <;> simp [hc]

theorem halves_second_shape (leaf : Bool) (t : Time) (pairs ins : List (Nat × NodeId)) :
    ∃ extra : List (Nat × NodeId),
      (halves leaf t ⟨leaf,newKlongs t pairs⟩ ins).2.1.ks =
        newKlongs t (secondSplitPairs leaf pairs ++ extra) := by
  cases hdrop : pairs.drop (pairs.length/2) with
  | nil =>
    cases ins with
    | nil => exact ⟨[],by cases leaf <;> simp [halves,newKlongs,KNode.size,← List.map_drop,hdrop,secondSplitPairs,renameHead]⟩
    | cons a ins =>
      refine ⟨a :: ins,?_⟩
      cases leaf <;> simp [halves,newKlongs,KNode.size,← List.map_drop,hdrop,secondSplitPairs,
        renameHead,key_zero_ite]
  | cons b rest =>
    cases ins with
    | nil => exact ⟨[],by cases leaf <;> simp [halves,newKlongs,KNode.size,← List.map_drop,hdrop,secondSplitPairs,renameHead]⟩
    | cons a ins =>
      by_cases ha : b.1 ≤ a.1
      · refine ⟨splitInsertPairs leaf b.1 (a :: ins),?_⟩
        cases leaf <;> simp [halves,newKlongs,KNode.size,← List.map_drop,hdrop,secondSplitPairs,
          renameHead,ha,splitInsertPairs_klongs]
      · exact ⟨[],by cases leaf <;> simp [halves,newKlongs,KNode.size,← List.map_drop,hdrop,
          secondSplitPairs,renameHead,ha]⟩

theorem secondSplitPairs_order (leaf : Bool) (pairs : List (Nat × NodeId))
    (hs : CvSorted pairs) : CvSorted (secondSplitPairs leaf pairs) := by
  have hd : CvSorted (pairs.drop (pairs.length/2)) := hs.sublist (List.drop_sublist _ _)
  cases leaf with
  | true => exact hd
  | false =>
    apply renameHead_sorted 0 _ hd
    intro q hq
    cases he : pairs.drop (pairs.length/2) with
    | nil => simp [he] at hq
    | cons b rest =>
      simp only [he,List.tail_cons] at hq
      rw [he] at hd
      have hh := (List.pairwise_cons.mp hd).1 q hq
      omega

theorem secondSplitPairs_length (leaf : Bool) (pairs : List (Nat × NodeId)) :
    (secondSplitPairs leaf pairs).length = pairs.length-pairs.length/2 := by
  cases leaf <;> simp [secondSplitPairs,renameHead_length]

/-- The split's second half has at least m live compare values, including
the inner-node empty-key rename and arbitrary duplicate upward inserts. -/
theorem halves_second_live_fill (p : Params) (hp : MergeParamsOK p)
    (leaf : Bool) (t : Time) (pairs ins : List (Nat × NodeId))
    (hs : CvSorted pairs)
    (hfull : p.splitAbove < (⟨leaf,newKlongs t pairs⟩ : KNode).size) :
    p.mergeBelow ≤ (halves leaf t ⟨leaf,newKlongs t pairs⟩ ins).2.1.cnt := by
  obtain ⟨extra,hshape⟩ := halves_second_shape leaf t pairs ins
  have hnd : ((secondSplitPairs leaf pairs).map Prod.fst).Nodup :=
    List.pairwise_map.mpr ((secondSplitPairs_order leaf pairs hs).imp
      (by intro a b hab; omega))
  have hprefix : (newKlongs t (secondSplitPairs leaf pairs)).IsPrefix
      (halves leaf t ⟨leaf,newKlongs t pairs⟩ ins).2.1.ks := by
    rw [hshape]
    simp only [newKlongs,List.map_append]
    exact List.prefix_append _ _
  have hdel : (halves leaf t ⟨leaf,newKlongs t pairs⟩ ins).2.1.lastBitmap = [] := by
    change lastBitmapOf _ = []
    rw [hshape]
    exact lastBitmapOf_newKlongs t _
  have hc := KNode.cnt_ge_key_prefix _ t (secondSplitPairs leaf pairs) hnd hprefix hdel
  rw [secondSplitPairs_length] at hc
  have hm := halves_first_count p hp pairs hfull
  simp only [List.length_take] at hm
  omega

theorem halves_live_fill (p : Params) (hp : MergeParamsOK p)
    (leaf : Bool) (t : Time) (pairs ins : List (Nat × NodeId))
    (hs : CvSorted pairs)
    (hfull : p.splitAbove < (⟨leaf,newKlongs t pairs⟩ : KNode).size) :
    p.mergeBelow ≤ (halves leaf t ⟨leaf,newKlongs t pairs⟩ ins).1.cnt ∧
      p.mergeBelow ≤ (halves leaf t ⟨leaf,newKlongs t pairs⟩ ins).2.1.cnt := by
  exact ⟨halves_first_protected_fill p hp leaf t pairs ins hs hfull,
    halves_second_live_fill p hp leaf t pairs ins hs hfull⟩

/-- Both outputs of a space split of an actual normalized last version
satisfy the live-count part of V1. Only the threshold condition is assumed. -/
theorem halves_lastVersionGivenDel_live_fill (p : Params) (hp : MergeParamsOK p)
    (n : KNode) (t : Time) (del : List Nat) (ins : List (Nat × NodeId))
    (hfull : p.splitAbove < (n.lastVersionGivenDel t del).size) :
    p.mergeBelow ≤ (halves n.leaf t (n.lastVersionGivenDel t del) ins).1.cnt ∧
      p.mergeBelow ≤ (halves n.leaf t (n.lastVersionGivenDel t del) ins).2.1.cnt := by
  obtain ⟨pairs,he,hs⟩ := n.lastVersionGivenDel_order t del
  have hleaf : (n.lastVersionGivenDel t del).leaf = n.leaf := rfl
  have hn : n.lastVersionGivenDel t del = ⟨n.leaf,newKlongs t pairs⟩ := by
    generalize n.lastVersionGivenDel t del = out at he hleaf ⊢
    cases out
    simp_all [newKlongs]
  rw [hn] at hfull ⊢
  exact halves_live_fill p hp n.leaf t pairs ins hs hfull

end SIS.Tree
