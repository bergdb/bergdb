import SIS.Tree.MergeProps

namespace SIS.Tree

open SIS SIS.Check

theorem setCv_keys (m : List (Nat × NodeId)) (c : Nat) (y : NodeId) :
    (setCv m c y).map Prod.fst =
      if m.any (fun q => q.1 == c) then m.map Prod.fst else m.map Prod.fst ++ [c] := by
  unfold setCv
  split
  · simp only [List.map_map]
    congr 1
    funext q
    rcases q with ⟨a,b⟩
    by_cases h : a = c <;> simp [h]
  · simp

theorem setCv_keys_nodup (m : List (Nat × NodeId)) (c : Nat) (y : NodeId)
    (hm : (m.map Prod.fst).Nodup) : ((setCv m c y).map Prod.fst).Nodup := by
  rw [setCv_keys]
  split
  · exact hm
  · rename_i hn
    have hc : c ∉ m.map Prod.fst := by
      intro hc
      obtain ⟨q,hq,hqc⟩ := List.mem_map.mp hc
      have ha : m.any (fun q => q.1 == c) = true :=
        List.any_eq_true.mpr ⟨q,hq,by simp [hqc]⟩
      exact hn ha
    apply List.nodup_append.mpr
    refine ⟨hm, by simp, ?_⟩
    intro a ha b hb he
    simp only [List.mem_singleton] at hb
    exact hc (hb ▸ he ▸ ha)

/-- The compare-value map used by lastVersionGivenDel has one entry a key. -/
theorem liveFold_keys_nodup (ks : List (Klong × Nat)) (del : List Nat)
    (m : List (Nat × NodeId)) (hm : (m.map Prod.fst).Nodup) :
    ((ks.foldl (fun more (k,i) => match k with
      | .key c y => if del.contains i then more else setCv more c y
      | _ => more) m).map Prod.fst).Nodup := by
  induction ks generalizing m with
  | nil => exact hm
  | cons ki ks ih =>
    rcases ki with ⟨k,i⟩
    cases k with
    | time t => exact ih m hm
    | del bits => exact ih m hm
    | key c y =>
      simp only [List.foldl_cons]
      apply ih
      split
      · exact hm
      · exact setCv_keys_nodup m c y hm

theorem sortedPairs_keys_nodup (pairs : List (Nat × NodeId))
    (hp : (pairs.map Prod.fst).Nodup) :
    ((pairs.mergeSort (fun a b => decide (a.1 ≤ b.1))).map Prod.fst).Nodup := by
  exact ((List.mergeSort_perm pairs _).map Prod.fst).nodup_iff.mpr hp

/-- A last version consists of its time klong and strictly ordered key klongs,
regardless of the order of physical klongs in the input node. -/
theorem KNode.lastVersionGivenDel_order (n : KNode) (t : Time) (del : List Nat) :
    ∃ pairs : List (Nat × NodeId),
      (n.lastVersionGivenDel t del).ks = .time t :: pairs.map (fun q => .key q.1 q.2) ∧
      pairs.Pairwise (fun a b => a.1 < b.1) := by
  let m := n.ks.zipIdx.foldl (fun more (k,i) => match k with
    | .key c y => if del.contains i then more else setCv more c y
    | _ => more) []
  let s := m.mergeSort (fun a b => decide (a.1 ≤ b.1))
  refine ⟨s,rfl,?_⟩
  have hn : (s.map Prod.fst).Nodup :=
    sortedPairs_keys_nodup m (liveFold_keys_nodup n.ks.zipIdx del [] (by simp))
  have hs : s.Pairwise (fun a b => a.1 ≤ b.1) := by
    have hh := List.pairwise_mergeSort (le := fun (a b : Nat × NodeId) => decide (a.1 ≤ b.1))
      (by intro a b c hab hbc; simp only [decide_eq_true_eq] at *; omega)
      (by intro a b; simp only [Bool.or_eq_true,decide_eq_true_eq]; omega) m
    simpa only [decide_eq_true_eq] using hh
  have hd : s.Pairwise (fun a b => a.1 ≠ b.1) := List.pairwise_map.mp hn
  apply List.Pairwise.imp _ (hs.and hd)
  intro a b hab
  omega

theorem KNode.lastVersion_keys (n : KNode) (t : Time) :
    (n.lastVersion t).ks = .time t :: n.live.map (fun q => .key q.1 q.2) := by
  simp [KNode.live,KNode.lastVersion,KNode.lastVersionGivenDel,List.filterMap_map,Function.comp_def]

theorem KNode.lastVersion_size (n : KNode) (t : Time) :
    (n.lastVersion t).size = n.cnt+1 := by
  simp [KNode.size,KNode.cnt,n.lastVersion_keys t]

theorem KNode.live_order (n : KNode) : n.live.Pairwise (fun a b => a.1 < b.1) := by
  obtain ⟨pairs,hp,hs⟩ := n.lastVersionGivenDel_order 0 n.lastBitmap
  have he : n.live = pairs := by
    unfold KNode.live KNode.lastVersion
    rw [hp]
    simp [List.filterMap_map,Function.comp_def]
  simpa only [he] using hs

theorem KNode.live_keys_nodup (n : KNode) : (n.live.map Prod.fst).Nodup := by
  apply List.pairwise_map.mpr
  apply List.Pairwise.imp _ n.live_order
  intro a b hab
  omega

/-- The split's first node keeps the whole original first half, before any
klongs that the upward write inserts. -/
theorem halves_first_prefix (leaf : Bool) (t : Time) (pairs ins : List (Nat × NodeId)) :
    (Klong.time t :: (pairs.take (pairs.length/2)).map (fun q => .key q.1 q.2)).IsPrefix
      (halves leaf t ⟨leaf,.time t :: pairs.map (fun q => .key q.1 q.2)⟩ ins).1.ks := by
  unfold halves
  simp only [KNode.size,List.length_cons,List.length_map,Nat.add_sub_cancel,
    List.drop_succ_cons,List.drop_zero,← List.map_take,← List.map_drop]
  repeat' first
    | exact List.prefix_refl _
    | exact List.prefix_append _ _
    | simp_all only [Bool.false_eq_true,Bool.true_eq_true,↓reduceIte]
    | split

/-- Every original key in the first half precedes the divider. -/
theorem halves_left_lt_divider (pairs : List (Nat × NodeId)) (k : Nat)
    (hs : pairs.Pairwise (fun a b => a.1 < b.1)) (r : Nat × NodeId)
    (hr : (pairs.drop k).head? = some r) :
    ∀ q ∈ pairs.take k, q.1 < r.1 := by
  have ha : (pairs.take k ++ pairs.drop k).Pairwise (fun a b => a.1 < b.1) := by
    simpa only [List.take_append_drop] using hs
  have hc := (List.pairwise_append.mp ha).2.2
  intro q hq
  exact hc q hq r (List.mem_of_head? hr)

/-- The threshold conditions leave at least m original key klongs in the
first half of a space split. -/
theorem halves_first_count (p : Params) (hp : MergeParamsOK p)
    (pairs : List (Nat × NodeId))
    (hfull : p.splitAbove < (⟨true,.time 0 :: pairs.map (fun q => .key q.1 q.2)⟩ : KNode).size) :
    p.mergeBelow ≤ (pairs.take (pairs.length/2)).length := by
  obtain ⟨hm,hmc,hmh,hcM,hhM,hfit⟩ := hp
  simp only [KNode.size,List.length_cons,List.length_map] at hfull
  simp only [List.length_take]
  omega

end SIS.Tree
