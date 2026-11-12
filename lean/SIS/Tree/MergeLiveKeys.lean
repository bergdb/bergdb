import SIS.Tree.MergeLiveOrder
import SIS.Tree.SortedSegments

namespace SIS.Tree

open SIS SIS.Check

private def liveKeyFold (del : List Nat) (m : List (Nat × NodeId))
    (q : Klong × Nat) : List (Nat × NodeId) :=
  match q.1 with
  | .key c y => if del.contains q.2 then m else setCv m c y
  | _ => m

private theorem setCv_preserves_key (m : List (Nat × NodeId)) (c a : Nat) (y : NodeId)
    (hc : c ∈ m.map Prod.fst) : c ∈ (setCv m a y).map Prod.fst := by
  rw [setCv_keys]
  split
  · exact hc
  · exact List.mem_append_left _ hc

private theorem setCv_contains_key (m : List (Nat × NodeId)) (c : Nat) (y : NodeId) :
    c ∈ (setCv m c y).map Prod.fst := by
  rw [setCv_keys]
  split
  · rename_i hc
    obtain ⟨q,hq,hqc⟩ := List.any_eq_true.mp hc
    exact List.mem_map.mpr ⟨q,hq,by simpa using hqc⟩
  · simp

private theorem liveKeyFold_preserves_key (del : List Nat) (ks : List (Klong × Nat))
    (m : List (Nat × NodeId)) (c : Nat) (hc : c ∈ m.map Prod.fst) :
    c ∈ (ks.foldl (liveKeyFold del) m).map Prod.fst := by
  induction ks generalizing m with
  | nil => exact hc
  | cons q ks ih =>
    apply ih
    rcases q with ⟨k,i⟩
    cases k with
    | time t => exact hc
    | del bits => exact hc
    | key a y =>
      unfold liveKeyFold
      dsimp only
      split
      · exact hc
      · exact setCv_preserves_key m c a y hc

private theorem liveKeyFold_hit (del : List Nat) (ks : List (Klong × Nat))
    (m : List (Nat × NodeId)) (c : Nat) (y : NodeId) (i : Nat)
    (hm : (.key c y,i) ∈ ks) (hi : i ∉ del) :
    c ∈ (ks.foldl (liveKeyFold del) m).map Prod.fst := by
  induction ks generalizing m with
  | nil => simp at hm
  | cons q ks ih =>
    simp only [List.mem_cons] at hm
    rcases hm with rfl | hm
    · simp only [List.foldl_cons]
      apply liveKeyFold_preserves_key
      simp only [liveKeyFold,List.contains_eq_mem,hi,decide_false,Bool.false_eq_true,↓reduceIte]
      exact setCv_contains_key m c y
    · exact ih _ hm

private theorem liveKeyFold_origin (del : List Nat) (ks : List (Klong × Nat))
    (m : List (Nat × NodeId)) (c : Nat)
    (hc : c ∈ (ks.foldl (liveKeyFold del) m).map Prod.fst) :
    c ∈ m.map Prod.fst ∨ ∃ y i, (.key c y,i) ∈ ks ∧ i ∉ del := by
  induction ks generalizing m with
  | nil => exact Or.inl hc
  | cons q ks ih =>
    rcases ih _ hc with hc | ⟨y,i,hm,hi⟩
    · rcases q with ⟨k,i⟩
      cases k with
      | time t => exact Or.inl hc
      | del bits => exact Or.inl hc
      | key a y =>
        unfold liveKeyFold at hc
        dsimp only at hc
        split at hc
        · exact Or.inl hc
        · rename_i hi
          rw [setCv_keys] at hc
          split at hc
          · exact Or.inl hc
          · simp only [List.mem_append,List.mem_singleton] at hc
            rcases hc with hc | rfl
            · exact Or.inl hc
            · exact Or.inr ⟨y,i,List.mem_cons_self,by
                simpa only [List.contains_eq_mem,decide_eq_true_eq] using hi⟩
    · exact Or.inr ⟨y,i,List.mem_cons_of_mem _ hm,hi⟩

/-- A physical key klong survives normalization exactly when at least one
klong of that compare value is outside the supplied delete bitmap. -/
theorem KNode.lastVersionGivenDel_has_key (n : KNode) (t : Time) (del : List Nat)
    (c : Nat) :
    c ∈ ((n.lastVersionGivenDel t del).ks.filterMap (fun k => match k with
      | .key a _ => some a | _ => none)) ↔
      ∃ y i, (.key c y,i) ∈ n.ks.zipIdx ∧ i ∉ del := by
  let m := n.ks.zipIdx.foldl (liveKeyFold del) []
  have he : ((n.lastVersionGivenDel t del).ks.filterMap (fun k => match k with
      | .key a _ => some a | _ => none)) =
      (m.mergeSort (fun a b => decide (a.1 ≤ b.1))).map Prod.fst := by
    simp only [KNode.lastVersionGivenDel,List.filterMap_cons,List.filterMap_map,
      Function.comp_def]
    change List.filterMap (fun q : Nat × NodeId => some q.1) _ = _
    rw [List.filterMap_eq_map']
    rfl
  rw [he]
  have hperm := (List.mergeSort_perm m (fun a b => decide (a.1 ≤ b.1))).map Prod.fst
  rw [hperm.mem_iff]
  constructor
  · intro hc
    rcases liveKeyFold_origin del n.ks.zipIdx [] c hc with hc | hc
    · simp at hc
    · exact hc
  · rintro ⟨y,i,hm,hi⟩
    exact liveKeyFold_hit del n.ks.zipIdx [] c y i hm hi

/-- The writer's live compare values have the same physical characterization. -/
theorem KNode.live_has_key (n : KNode) (c : Nat) :
    c ∈ n.live.map Prod.fst ↔
      ∃ y i, (.key c y,i) ∈ n.ks.zipIdx ∧ i ∉ n.lastBitmap := by
  have he : n.live.map Prod.fst =
      (n.lastVersionGivenDel 0 n.lastBitmap).ks.filterMap (fun k => match k with
        | .key a _ => some a | _ => none) := by
    simp only [KNode.live,KNode.lastVersion,List.map_filterMap]
    congr 1
    funext k
    cases k <;> rfl
  rw [he]
  exact n.lastVersionGivenDel_has_key 0 n.lastBitmap c

/-- Distinct protected compare values give a lower bound on the live count. -/
theorem KNode.cnt_ge_protected_keys (n : KNode) (keys : List Nat) (hn : keys.Nodup)
    (hk : ∀ c ∈ keys, ∃ y i, (.key c y,i) ∈ n.ks.zipIdx ∧ i ∉ n.lastBitmap) :
    keys.length ≤ n.cnt := by
  have hs : ∀ c ∈ keys, c ∈ n.live.map Prod.fst := by
    intro c hc
    exact (n.live_has_key c).mpr (hk c hc)
  have hlen := hn.length_le_of_subset hs
  simpa only [List.length_map,KNode.cnt] using hlen

/-- A klong of another compare value cannot be in bitsOf c. -/
theorem KNode.not_mem_bitsOf_of_key_ne (n : KNode) (a c : Nat) (y : NodeId) (i : Nat)
    (hm : (.key a y,i) ∈ n.ks.zipIdx) (hac : a ≠ c) : i ∉ n.bitsOf c := by
  intro hi
  obtain ⟨⟨k,j⟩,hkj,hki⟩ := List.mem_filterMap.mp hi
  cases k with
  | time t => simp at hki
  | del bits => simp at hki
  | key b z =>
    simp only at hki
    split at hki
    · rename_i hbc
      have hb : b = c := by simpa only [beq_iff_eq] using hbc
      have hj : j = i := by simpa only [Option.some.injEq] using hki
      subst b
      subst j
      have he1 := List.mem_zipIdx_iff_getElem?.mp hm
      have he2 := List.mem_zipIdx_iff_getElem?.mp hkj
      rw [he1] at he2
      simp only [Option.some.injEq,Klong.key.injEq] at he2
      exact hac he2.1
    · cases hki

theorem mem_bitsUnion_iff (a b : List Nat) (i : Nat) :
    i ∈ bitsUnion a b ↔ i ∈ a ∨ i ∈ b := by
  simp [bitsUnion]

/-- Deleting a later compare value does not delete an earlier physical klong. -/
theorem KNode.delete_preserves_earlier_key (n : KNode) (a c : Nat) (y : NodeId) (i : Nat)
    (hm : (.key a y,i) ∈ n.ks.zipIdx) (hi : i ∉ n.lastBitmap) (hac : a < c) :
    i ∉ bitsUnion n.lastBitmap (n.bitsOf c) := by
  rw [mem_bitsUnion_iff]
  exact not_or.mpr ⟨hi,n.not_mem_bitsOf_of_key_ne a c y i hm (by omega)⟩

theorem lastBitmapOf_newKlongs (t : Time) (pairs : List (Nat × NodeId)) :
    lastBitmapOf (newKlongs t pairs) = [] := by
  simp only [newKlongs,lastBitmapOf,List.foldl_cons,List.foldl_map]
  induction pairs with
  | nil => rfl
  | cons q pairs ih => exact ih

theorem lastBitmapOf_no_delete (ks : List Klong)
    (hd : ∀ bits, .del bits ∉ ks) : lastBitmapOf ks = [] := by
  induction ks with
  | nil => rfl
  | cons k ks ih =>
    have htail : ∀ bits, Klong.del bits ∉ ks := by
      intro bits hb
      exact hd bits (List.mem_cons_of_mem _ hb)
    cases k with
    | time t => exact ih htail
    | key c y => exact ih htail
    | del bits => exact (hd bits List.mem_cons_self).elim

theorem KNode.cnt_ge_key_prefix (n : KNode) (t : Time) (pairs : List (Nat × NodeId))
    (hn : (pairs.map Prod.fst).Nodup)
    (hp : (Klong.time t :: pairs.map (fun q => .key q.1 q.2)).IsPrefix n.ks)
    (hd : n.lastBitmap = []) : pairs.length ≤ n.cnt := by
  have hbound := n.cnt_ge_protected_keys (pairs.map Prod.fst) hn (by
    intro c hc
    obtain ⟨⟨a,y⟩,hq,he⟩ := List.mem_map.mp hc
    dsimp only at he
    subst a
    have hk : Klong.key c y ∈ n.ks := hp.sublist.subset
      (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨(c,y),hq,rfl⟩))
    obtain ⟨i,hi⟩ := List.mem_iff_getElem?.mp hk
    exact ⟨y,i,List.mem_zipIdx_iff_getElem?.mpr hi,by simp only [hd,List.not_mem_nil,not_false_eq_true]⟩)
  simpa only [List.length_map] using hbound

theorem mem_key_newKlongs (t : Time) (pairs : List (Nat × NodeId)) (c : Nat) (y : NodeId) :
    .key c y ∈ newKlongs t pairs ↔ (c,y) ∈ pairs := by
  simp [newKlongs]

/-- A newly written last version has exactly its distinct input compare
values live; its time klong deletes none of them. -/
theorem KNode.newKlongs_live_has_key (leaf : Bool) (t : Time)
    (pairs : List (Nat × NodeId)) (c : Nat) :
    c ∈ (⟨leaf,newKlongs t pairs⟩ : KNode).live.map Prod.fst ↔ c ∈ pairs.map Prod.fst := by
  rw [KNode.live_has_key]
  constructor
  · rintro ⟨y,i,hm,_⟩
    have hk : .key c y ∈ newKlongs t pairs :=
      List.mem_iff_getElem?.mpr ⟨i,List.mem_zipIdx_iff_getElem?.mp hm⟩
    exact List.mem_map.mpr ⟨(c,y),(mem_key_newKlongs t pairs c y).mp hk,rfl⟩
  · intro hc
    obtain ⟨⟨a,y⟩,hq,heq⟩ := List.mem_map.mp hc
    dsimp only at heq
    subst a
    have hk := (mem_key_newKlongs t pairs c y).mpr hq
    obtain ⟨i,hi⟩ := List.mem_iff_getElem?.mp hk
    refine ⟨y,i,List.mem_zipIdx_iff_getElem?.mpr hi,?_⟩
    simp only [KNode.lastBitmap,lastBitmapOf_newKlongs,List.not_mem_nil,not_false_eq_true]

theorem KNode.newKlongs_cnt (leaf : Bool) (t : Time) (pairs : List (Nat × NodeId))
    (hn : (pairs.map Prod.fst).Nodup) :
    (⟨leaf,newKlongs t pairs⟩ : KNode).cnt = pairs.length := by
  let n : KNode := ⟨leaf,newKlongs t pairs⟩
  have hs := fun c => KNode.newKlongs_live_has_key leaf t pairs c
  have hlow := hn.length_le_of_subset (fun c hc => (hs c).mpr hc)
  have hhigh := n.live_keys_nodup.length_le_of_subset (fun c hc => (hs c).mp hc)
  simp only [List.length_map] at hlow hhigh
  exact Nat.le_antisymm hhigh hlow

/-- A normalized last version retains enough space for every protected
distinct compare value, as well as its time klong. -/
theorem KNode.lastVersionGivenDel_size_ge_protected (n : KNode) (t : Time)
    (del : List Nat) (keys : List Nat) (hn : keys.Nodup)
    (hk : ∀ c ∈ keys, ∃ y i, (.key c y,i) ∈ n.ks.zipIdx ∧ i ∉ del) :
    keys.length+1 ≤ (n.lastVersionGivenDel t del).size := by
  obtain ⟨pairs,hpairs,_⟩ := n.lastVersionGivenDel_order t del
  have hsub : ∀ c ∈ keys, c ∈ pairs.map Prod.fst := by
    intro c hc
    have hm := (n.lastVersionGivenDel_has_key t del c).mpr (hk c hc)
    rw [hpairs] at hm
    simpa only [List.filterMap_cons,List.filterMap_map,Function.comp_def,
      List.filterMap_eq_map'] using hm
  have hlen := hn.length_le_of_subset hsub
  simp only [List.length_map] at hlen
  simp only [KNode.size,hpairs,List.length_cons,List.length_map]
  omega

/-- Deleting at or beyond a divider preserves the normalized size required
by any distinct protected keys below that divider. -/
theorem KNode.delete_size_ge_protected_prefix (n : KNode) (t : Time)
    (cut cv : Nat) (keys : List Nat) (hn : keys.Nodup)
    (hcut : ∀ c ∈ keys, c < cut) (hcv : cut ≤ cv)
    (hk : ∀ c ∈ keys, ∃ y i, (.key c y,i) ∈ n.ks.zipIdx ∧ i ∉ n.lastBitmap) :
    keys.length+1 ≤ (n.lastVersionGivenDel t (bitsUnion n.lastBitmap (n.bitsOf cv))).size := by
  apply n.lastVersionGivenDel_size_ge_protected t _ keys hn
  intro c hc
  obtain ⟨y,i,hm,hi⟩ := hk c hc
  exact ⟨y,i,hm,n.delete_preserves_earlier_key c cv y i hm hi (by have := hcut c hc; omega)⟩

/-- Sorted, well-formed terminal writes already passed by the current key
survive its delete, when their klongs are still live in this node. -/
theorem KNode.delete_size_ge_sorted_terminal_keys (n : KNode) (t : Time) (g : Nat)
    (keys : List Key) (key : Key) (cv : Nat)
    (hs : sortedKeys (keys ++ [key]) = true)
    (hw : ∀ a ∈ keys, keyWf a = true) (hkey : keyWf key = true)
    (hlen : ∀ a ∈ keys, a.length = g+1)
    (hp : ∀ a ∈ keys, a.take g = key.take g) (hcv : key[g]? = some cv)
    (hk : ∀ a ∈ keys, ∃ y i,
      (.key a[g]! y,i) ∈ n.ks.zipIdx ∧ i ∉ n.lastBitmap) :
    keys.length+1 ≤ (n.lastVersionGivenDel t (bitsUnion n.lastBitmap (n.bitsOf cv))).size := by
  have hpair := List.pairwise_append.mp (sortedKeys_pairwise (keys ++ [key]) hs)
  have hvalues := terminal_segment_values_pairwise keys g (key.take g) hpair.1 hw hlen hp
  have hnd : (keys.map (fun a => a[g]!)).Nodup := hvalues.imp (by intro a b hab; omega)
  have hbound := n.lastVersionGivenDel_size_ge_protected t _ (keys.map (fun a => a[g]!)) hnd (by
    intro a ha
    obtain ⟨old,hold,he⟩ := List.mem_map.mp ha
    subst a
    obtain ⟨y,i,hm,hi⟩ := hk old hold
    have hbefore : keyLt old key = true := hpair.2.2 old hold key List.mem_cons_self
    have hlt := keyLt_terminal_segment_strict g old key old[g]! cv
      (hw old hold) hkey hbefore (hp old hold)
      (terminal_segment_get old g (hlen old hold)) hcv (hlen old hold)
    exact ⟨y,i,hm,n.delete_preserves_earlier_key old[g]! cv y i hm hi hlt⟩)
  simpa only [List.length_map] using hbound

theorem prefix_mem_zipIdx {ks more : List Klong} (hp : ks.IsPrefix more)
    (c : Nat) (y : NodeId) (i : Nat) (hm : (.key c y,i) ∈ ks.zipIdx) :
    (.key c y,i) ∈ more.zipIdx := by
  obtain ⟨suffix,hs⟩ := hp
  have hi : i < ks.length := by simpa using (List.mem_zipIdx hm).2.1
  apply List.mem_zipIdx_iff_getElem?.mpr
  rw [← hs,List.getElem?_append_left hi]
  exact List.mem_zipIdx_iff_getElem?.mp hm

theorem KNode.add_prefix (n : KNode) (t : Time) (k : Klong) :
    n.ks.IsPrefix (n.add t k).ks := by
  unfold KNode.add
  split
  · split <;> exact List.prefix_append _ _
  · exact List.prefix_append _ _

theorem lastBitmapOf_append_delete (ks : List Klong) (bits : List Nat) :
    lastBitmapOf (ks ++ [.del bits]) = bits := by
  simp only [lastBitmapOf,List.foldl_append,List.foldl_cons,List.foldl_nil]

theorem KNode.add_delete_lastBitmap (n : KNode) (t : Time) (bits : List Nat) :
    (n.add t (.del bits)).lastBitmap = bits := by
  unfold KNode.add
  split
  · split
    · simp only [KNode.lastBitmap,lastBitmapOf,List.foldl_append,List.foldl_cons,List.foldl_nil]
    · exact lastBitmapOf_append_delete _ _
  · simp only [KNode.lastBitmap,lastBitmapOf,List.foldl_append,List.foldl_cons,List.foldl_nil]

/-- The ordinary bitmap append preserves the actual live count supported by
earlier keys, before any compaction or split is considered. -/
theorem KNode.add_delete_cnt_ge_earlier_prefix (n : KNode) (t : Time)
    (cut cv : Nat) (keys : List Nat) (hn : keys.Nodup)
    (hcut : ∀ c ∈ keys, c < cut) (hcv : cut ≤ cv)
    (hk : ∀ c ∈ keys, ∃ y i, (.key c y,i) ∈ n.ks.zipIdx ∧ i ∉ n.lastBitmap) :
    keys.length ≤ (n.add t (.del (bitsUnion n.lastBitmap (n.bitsOf cv)))).cnt := by
  apply KNode.cnt_ge_protected_keys _ keys hn
  intro c hc
  obtain ⟨y,i,hm,hi⟩ := hk c hc
  refine ⟨y,i,prefix_mem_zipIdx (n.add_prefix t _) c y i hm,?_⟩
  rw [n.add_delete_lastBitmap]
  exact n.delete_preserves_earlier_key c cv y i hm hi (by have := hcut c hc; omega)

theorem key_mem_zipIdx_append_delete_iff (ks : List Klong) (bits : List Nat)
    (c : Nat) (y : NodeId) (i : Nat) :
    (Klong.key c y,i) ∈ (ks ++ [Klong.del bits]).zipIdx ↔ (Klong.key c y,i) ∈ ks.zipIdx := by
  simp [List.zipIdx_append]

theorem KNode.setAt_last_delete_ks (n : KNode) (pre : List Klong) (old bits : List Nat)
    (hp : n.ks = pre ++ [.del old]) :
    (n.setAt (n.size-1) (.del bits)).ks = pre ++ [.del bits] := by
  simp [KNode.setAt,KNode.size,hp]

/-- Updating the transaction's last bitmap in place preserves the same
earlier keys as an appended bitmap. -/
theorem KNode.setAt_delete_cnt_ge_earlier_prefix (n : KNode)
    (cut cv : Nat) (keys : List Nat) (hn : keys.Nodup)
    (hcut : ∀ c ∈ keys, c < cut) (hcv : cut ≤ cv)
    (hk : ∀ c ∈ keys, ∃ y i, (.key c y,i) ∈ n.ks.zipIdx ∧ i ∉ n.lastBitmap)
    (old : List Nat) (hlast : n.ks.getLast? = some (.del old)) :
    keys.length ≤
      (n.setAt (n.size-1) (.del (bitsUnion n.lastBitmap (n.bitsOf cv)))).cnt := by
  obtain ⟨pre,hpre⟩ := List.getLast?_eq_some_iff.mp hlast
  have hnew := n.setAt_last_delete_ks pre old (bitsUnion n.lastBitmap (n.bitsOf cv)) hpre
  apply KNode.cnt_ge_protected_keys _ keys hn
  intro c hc
  obtain ⟨y,i,hm,hi⟩ := hk c hc
  refine ⟨y,i,?_,?_⟩
  · rw [hnew]
    rw [hpre,key_mem_zipIdx_append_delete_iff] at hm
    exact (key_mem_zipIdx_append_delete_iff pre _ c y i).mpr hm
  · change i ∉ lastBitmapOf _
    rw [hnew,lastBitmapOf_append_delete]
    exact n.delete_preserves_earlier_key c cv y i hm hi (by have := hcut c hc; omega)

end SIS.Tree
