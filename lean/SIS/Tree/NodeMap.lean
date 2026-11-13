import SIS.Tree.DeleteCount
import SIS.Tree.SearchFold
import SIS.Tree.KlongShape

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- Normalization preserves every pointer selected by the physical-key fold,
not just the set or count of live compare values. -/
theorem KNode.lastVersionGivenDel_pairs_lookup (n : KNode) (t : Time) (del : List Nat) (c : Nat) :
    ((n.lastVersionGivenDel t del).ks.filterMap (fun k => match k with
      | .key a y => some (a, y) | _ => none)).lookup c = keyLookup n.ks del c := by
  let xs := n.ks.zipIdx
  let m := xs.foldl (fun more (k, i) => match k with
    | .key a y => if del.contains i then more else setCv more a y
    | _ => more) []
  have hn : (m.map Prod.fst).Nodup := liveFold_keys_nodup xs del [] (by simp)
  have he : (n.lastVersionGivenDel t del).ks.filterMap (fun k => match k with
      | .key a y => some (a, y) | _ => none) = m.mergeSort (fun a b => decide (a.1 ≤ b.1)) := by
    simp [KNode.lastVersionGivenDel, m, xs, List.filterMap_map, Function.comp_def]
    rfl
  rw [he, lookup_eq_of_perm (List.mergeSort_perm m _) (sortedPairs_keys_nodup m hn)]
  exact lookup_liveFold xs del c []

theorem KNode.live_lookup (n : KNode) (c : Nat) :
    n.live.lookup c = keyLookup n.ks n.lastBitmap c :=
  n.lastVersionGivenDel_pairs_lookup 0 n.lastBitmap c

def pairLookupStep (c : Nat) (acc : Option NodeId) (q : Nat × NodeId) : Option NodeId :=
  if q.1 == c then some q.2 else acc

theorem pairLookupFold_reverse (pairs : List (Nat × NodeId)) (c : Nat) (acc : Option NodeId) :
    pairs.foldl (pairLookupStep c) acc = (pairs.reverse.lookup c).or acc := by
  induction pairs generalizing acc with
  | nil => rfl
  | cons q pairs ih =>
    rcases q with ⟨a, y⟩
    rw [List.foldl_cons, ih, List.reverse_cons, List.lookup_append]
    cases hh : pairs.reverse.lookup c with
    | none =>
      by_cases ha : a = c
      · subst a; simp [List.lookup_cons, pairLookupStep]
      · simp [List.lookup_cons, pairLookupStep, ha]
        rw [beq_eq_false_iff_ne.mpr (Ne.symm ha)]
        rfl
    | some y => simp [hh]

theorem keyLookup_keys_fold (pairs : List (Nat × NodeId)) (start c : Nat) (acc : Option NodeId) :
    ((pairs.map (fun q => Klong.key q.1 q.2)).zipIdx start).foldl (keyLookupStep [] c) acc =
      pairs.foldl (pairLookupStep c) acc := by
  induction pairs generalizing start acc with
  | nil => rfl
  | cons q pairs ih =>
    simp only [List.map_cons, List.zipIdx_cons, List.foldl_cons, keyLookupStep,
      List.contains_nil, Bool.false_eq_true, ↓reduceIte, pairLookupStep]
    exact ih (start + 1) _

theorem keyLookup_newKlongs (t : Time) (pairs : List (Nat × NodeId)) (c : Nat)
    (hn : (pairs.map Prod.fst).Nodup) : keyLookup (newKlongs t pairs) [] c = pairs.lookup c := by
  unfold keyLookup
  simp only [newKlongs, List.zipIdx_cons, List.foldl_cons, keyLookupStep]
  rw [keyLookup_keys_fold, pairLookupFold_reverse]
  have hr : (pairs.reverse.map Prod.fst).Nodup := by
    exact ((List.reverse_perm pairs).map Prod.fst).nodup_iff.mpr hn
  rw [lookup_eq_of_perm (List.reverse_perm pairs) hr]
  cases pairs.lookup c <;> rfl

theorem KNode.lastVersionGivenDel_live_lookup (n : KNode) (t : Time) (del : List Nat) (c : Nat) :
    (n.lastVersionGivenDel t del).live.lookup c = keyLookup n.ks del c := by
  obtain ⟨pairs, he, horder⟩ := n.lastVersionGivenDel_order t del
  have hn : (pairs.map Prod.fst).Nodup := List.pairwise_map.mpr
    (horder.imp (by intro a b hab; omega))
  rw [KNode.live_lookup]
  have hd : (n.lastVersionGivenDel t del).lastBitmap = [] := by
    change lastBitmapOf _ = []
    rw [he]
    exact lastBitmapOf_newKlongs t pairs
  rw [hd, he]
  change keyLookup (newKlongs t pairs) [] c = _
  rw [keyLookup_newKlongs t pairs c hn]
  have hp := n.lastVersionGivenDel_pairs_lookup t del c
  simpa [he, newKlongs, List.filterMap_map, Function.comp_def] using hp

theorem KNode.lastVersion_live_lookup (n : KNode) (t : Time) (c : Nat) :
    (n.lastVersion t).live.lookup c = n.live.lookup c := by
  calc
    _ = keyLookup n.ks n.lastBitmap c := n.lastVersionGivenDel_live_lookup t n.lastBitmap c
    _ = n.live.lookup c := (n.live_lookup c).symm

theorem keyLookupStep_delete_other (n : KNode) (cv c : Nat) (hc : c ≠ cv)
    (q : Klong × Nat) (hq : q ∈ n.ks.zipIdx) (acc : Option NodeId) :
    keyLookupStep (bitsUnion n.lastBitmap (n.bitsOf cv)) c acc q =
      keyLookupStep n.lastBitmap c acc q := by
  rcases q with ⟨k, i⟩
  cases k with
  | time t => rfl
  | del bits => rfl
  | key a y =>
    by_cases he : a = c
    · subst a
      have hi := n.not_mem_bitsOf_of_key_ne c cv y i hq hc
      have hb : (bitsUnion n.lastBitmap (n.bitsOf cv)).contains i = n.lastBitmap.contains i := by
        simp only [List.contains_eq_mem, mem_bitsUnion_iff, hi, or_false]
      simp only [keyLookupStep, hb]
    · simp [keyLookupStep, he]

theorem keyLookup_delete_union (n : KNode) (cv c : Nat) :
    keyLookup n.ks (bitsUnion n.lastBitmap (n.bitsOf cv)) c =
      if c == cv then none else n.live.lookup c := by
  by_cases he : c = cv
  · subst c
    simp only [beq_self_eq_true, ↓reduceIte]
    apply keyLookup_fold_none
    intro y i hi
    rw [mem_bitsUnion_iff]
    exact Or.inr ((n.mem_bitsOf_iff cv i).mpr ⟨y, hi⟩)
  · simp only [beq_eq_false_iff_ne.mpr he, Bool.false_eq_true, ↓reduceIte, KNode.live_lookup]
    have hfold : ∀ (xs : List (Klong × Nat)) (acc : Option NodeId), xs ⊆ n.ks.zipIdx →
        xs.foldl (keyLookupStep (bitsUnion n.lastBitmap (n.bitsOf cv)) c) acc =
          xs.foldl (keyLookupStep n.lastBitmap c) acc := by
      intro xs
      induction xs with
      | nil => intro acc _; rfl
      | cons q qs ih =>
        intro acc hs
        rw [List.foldl_cons, List.foldl_cons, keyLookupStep_delete_other n cv c he q
          (hs List.mem_cons_self) acc]
        exact ih _ (fun a ha => hs (List.mem_cons_of_mem q ha))
    exact hfold _ none (fun _ h => h)

/-- The normalized delete removes precisely the requested entry; all other
live pointers are unchanged, even with shadows and arbitrary input klongs. -/
theorem KNode.delete_live_lookup (n : KNode) (t : Time) (cv c : Nat) :
    (n.lastVersionGivenDel t (bitsUnion n.lastBitmap (n.bitsOf cv))).live.lookup c =
      if c == cv then none else n.live.lookup c := by
  rw [n.lastVersionGivenDel_live_lookup, keyLookup_delete_union]

theorem keyLookup_append_time (ks : List Klong) (del : List Nat) (c t : Nat) :
    keyLookup (ks ++ [.time t]) del c = keyLookup ks del c := by
  simp [keyLookup, List.zipIdx_append, keyLookupStep]

theorem keyLookup_append_delete (ks : List Klong) (del bits : List Nat) (c : Nat) :
    keyLookup (ks ++ [.del bits]) del c = keyLookup ks del c := by
  simp [keyLookup, List.zipIdx_append, keyLookupStep]

theorem keyLookup_append_time_delete (ks : List Klong) (del bits : List Nat) (c t : Nat) :
    keyLookup (ks ++ [.time t, .del bits]) del c = keyLookup ks del c := by
  simp [keyLookup, List.zipIdx_append, keyLookupStep]

theorem KNode.add_delete_live_lookup (n : KNode) (t : Time) (cv c : Nat) :
    (n.add t (.del (bitsUnion n.lastBitmap (n.bitsOf cv)))).live.lookup c =
      if c == cv then none else n.live.lookup c := by
  rw [KNode.live_lookup, n.add_delete_lastBitmap]
  have he : keyLookup (n.add t (.del (bitsUnion n.lastBitmap (n.bitsOf cv)))).ks
      (bitsUnion n.lastBitmap (n.bitsOf cv)) c =
      keyLookup n.ks (bitsUnion n.lastBitmap (n.bitsOf cv)) c := by
    unfold KNode.add
    split
    · split
      · exact keyLookup_append_time_delete _ _ _ _ _
      · exact keyLookup_append_delete _ _ _ _
    · exact keyLookup_append_time_delete _ _ _ _ _
  rw [he, keyLookup_delete_union]

theorem KNode.setAt_delete_live_lookup (n : KNode) (cv c : Nat) (old : List Nat)
    (hlast : n.ks.getLast? = some (.del old)) :
    (n.setAt (n.size - 1) (.del (bitsUnion n.lastBitmap (n.bitsOf cv)))).live.lookup c =
      if c == cv then none else n.live.lookup c := by
  obtain ⟨pre, hpre⟩ := List.getLast?_eq_some_iff.mp hlast
  have hnew := n.setAt_last_delete_ks pre old (bitsUnion n.lastBitmap (n.bitsOf cv)) hpre
  rw [KNode.live_lookup]
  have hd : (n.setAt (n.size - 1) (.del (bitsUnion n.lastBitmap (n.bitsOf cv)))).lastBitmap =
      bitsUnion n.lastBitmap (n.bitsOf cv) := by
    change lastBitmapOf _ = _
    rw [hnew, lastBitmapOf_append_delete]
  rw [hd, hnew, keyLookup_append_delete]
  have he := keyLookup_delete_union n cv c
  rw [hpre, keyLookup_append_delete] at he
  exact he

theorem keyLookup_append_key (ks : List Klong) (del : List Nat) (cv c : Nat) (y : NodeId)
    (hd : ks.length ∉ del) :
    keyLookup (ks ++ [.key cv y]) del c =
      if cv == c then some y else keyLookup ks del c := by
  simp [keyLookup, List.zipIdx_append, keyLookupStep, List.contains_eq_mem, hd]

theorem keyLookup_append_time_key (ks : List Klong) (del : List Nat) (t cv c : Nat) (y : NodeId)
    (hd : ks.length + 1 ∉ del) :
    keyLookup (ks ++ [.time t, .key cv y]) del c =
      if cv == c then some y else keyLookup ks del c := by
  simp [keyLookup, List.zipIdx_append, keyLookupStep, List.contains_eq_mem, hd]

/-- A physical append overwrites exactly its compare value. Bounding the
old bitmap rules out a spurious bit masking the newly appended key. -/
theorem KNode.add_key_live_lookup (n : KNode) (t : Time) (cv c : Nat) (y : NodeId)
    (hd : ∀ i ∈ n.lastBitmap, i < n.size) :
    (n.add t (.key cv y)).live.lookup c = if cv == c then some y else n.live.lookup c := by
  rw [KNode.live_lookup, n.add_key_lastBitmap, n.live_lookup]
  have h0 : n.ks.length ∉ n.lastBitmap := by
    intro h; have hh := hd _ h; change n.ks.length < n.ks.length at hh; omega
  have h1 : n.ks.length + 1 ∉ n.lastBitmap := by
    intro h; have hh := hd _ h; change n.ks.length + 1 < n.ks.length at hh; omega
  unfold KNode.add
  split
  · split
    · exact keyLookup_append_time_key _ _ _ _ _ _ h1
    · exact keyLookup_append_key _ _ _ _ _ h0
  · exact keyLookup_append_time_key _ _ _ _ _ _ h1

theorem KNode.wf_bitmap_bounds (n : KNode) (hw : klongsWf n.ks = true) :
    ∀ i ∈ n.lastBitmap, i < n.size := by
  have hb := bitmapRules_bounds n.ks (klongsWf_bitmapRules n.ks hw) n.ks.length (Nat.le_refl _)
  intro i hi
  exact (hb i (by simpa [KNode.lastBitmap] using hi)).1

theorem KNode.add_key_live_lookup_of_wf (n : KNode) (t : Time) (cv c : Nat) (y : NodeId)
    (hw : klongsWf n.ks = true) :
    (n.add t (.key cv y)).live.lookup c = if cv == c then some y else n.live.lookup c :=
  n.add_key_live_lookup t cv c y (n.wf_bitmap_bounds hw)

theorem KNode.live_with_leaf (n : KNode) (leaf : Bool) :
    ({n with leaf := leaf} : KNode).live = n.live := rfl

theorem KNode.delete_lookup_noop (n : KNode) (cv : Nat)
    (hu : bitsUnion n.lastBitmap (n.bitsOf cv) = n.lastBitmap) (c : Nat) :
    n.live.lookup c = if c == cv then none else n.live.lookup c := by
  have hh := keyLookup_delete_union n cv c
  rw [hu, ← n.live_lookup] at hh
  exact hh

end SIS.Tree
