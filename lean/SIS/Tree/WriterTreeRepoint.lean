/-
A key klong's pointer changed in place (`KNode.repoint`): every live klong at
any time is the node's, or names the new pointer (`KNode.repoint_liveAt`). For
the rules that point a klong of the transaction in place (bergdb 024-22: LE-b,
the merge's parent, the take-back, a segment root's split, root collapse).
-/
import SIS.Tree.WriterTreeDelete

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

theorem prefix_getElem?_some {α : Type} (l L : List α) (h : l <+: L) (j : Nat) (k : α)
    (hj : l[j]? = some k) : L[j]? = some k := by
  obtain ⟨t1, ht1⟩ := h
  rw [← ht1, List.getElem?_append_left (by
    rw [List.getElem?_eq_some_iff] at hj; exact hj.1)]
  exact hj

theorem takeWhile_set {α : Type} (p : α → Bool) (l : List α) (i : Nat) (a : α)
    (hp : ∀ b, l[i]? = some b → p b = p a) :
    (l.set i a).takeWhile p = (l.takeWhile p).set i a := by
  induction l generalizing i with
  | nil => simp
  | cons b l ih =>
    cases i with
    | zero =>
      have hb := hp b rfl
      simp only [List.set_cons_zero, List.takeWhile_cons, hb]
      split <;> simp
    | succ i =>
      simp only [List.set_cons_succ, List.takeWhile_cons]
      split
      · rw [ih i (fun b' h => hp b' (by simpa using h))]
        simp
      · simp

theorem lastBitmapOf_set_key (l : List Klong) (i : Nat) (c0 : Nat) (y : NodeId)
    (hk : ∃ old, l[i]? = some (.key c0 old)) : lastBitmapOf (l.set i (.key c0 y)) = lastBitmapOf l := by
  unfold lastBitmapOf
  generalize ([] : List Nat) = d
  induction l generalizing i d with
  | nil => simp
  | cons b l ih =>
    cases i with
    | zero =>
      obtain ⟨old, hold⟩ := hk
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hold
      subst hold
      simp
    | succ i =>
      simp only [List.set_cons_succ, List.foldl_cons]
      exact ih i (by simpa using hk) _

/-- The key-lookup fold with one key klong's pointer changed: the same result,
or the new pointer. -/
theorem keyLookupFold_set (del : List Nat) (c : Nat) (y : NodeId) :
    ∀ (xs : List (Klong × Nat)) (i : Nat) (c0 old : Nat) (v v' : Option NodeId),
      (v' = v ∨ v' = some y) →
      (∀ k j, (k, j) ∈ xs → j = i → k = .key c0 old) →
      (xs.map (fun q => if q.2 = i then (Klong.key c0 y, q.2) else q)).foldl (keyLookupStep del c) v' =
        xs.foldl (keyLookupStep del c) v ∨
      (xs.map (fun q => if q.2 = i then (Klong.key c0 y, q.2) else q)).foldl (keyLookupStep del c) v' =
        some y := by
  intro xs
  induction xs with
  | nil => intro i c0 old v v' hv _; simpa using hv
  | cons q qs ih =>
    intro i c0 old v v' hv hi
    rcases q with ⟨k, j⟩
    simp only [List.map_cons, List.foldl_cons]
    apply ih i c0 old _ _ _ (fun k' j' h hj => hi k' j' (List.mem_cons_of_mem _ h) hj)
    by_cases hj : j = i
    · have hk := hi k j List.mem_cons_self hj
      subst hk
      simp only [hj, ↓reduceIte, keyLookupStep]
      split
      · exact hv
      · split
        · exact Or.inr rfl
        · exact hv
    · simp only [hj, ↓reduceIte, keyLookupStep]
      cases k with
      | key a z =>
        simp only
        split
        · exact hv
        · split
          · exact Or.inl rfl
          · exact hv
      | time t => exact hv
      | del b => exact hv

/-- A key klong pointed to y in place: a live klong at any time is the node's
or names y. -/
theorem KNode.repoint_liveAt (n : KNode) (i : Nat) (y : NodeId) (t : Time) (c : Nat) (z : NodeId)
    (h : (c, z) ∈ (n.repoint i y).liveAt t) : (c, z) ∈ n.liveAt t ∨ z = y := by
  unfold KNode.repoint at h
  split at h
  · rename_i c0 old hk
    have hn := KNode.liveAt_keys_nodup ({ n with ks := n.ks.set i (.key c0 y) } : KNode) t
    have hl := lookup_of_mem_nodup _ hn c z h
    rw [KNode.liveAt_lookup] at hl
    -- the prefix and the bitmap
    have hp : ∀ b, n.ks[i]? = some b → (fun k => match k with
        | Klong.time x => decide (x ≤ t)
        | _ => true) b = (fun k => match k with
        | Klong.time x => decide (x ≤ t)
        | _ => true) (Klong.key c0 y) := by
      intro b hb; rw [hk] at hb; simp only [Option.some.injEq] at hb; subst hb; rfl
    have hpre : prefixAt (n.ks.set i (.key c0 y)) t = (prefixAt n.ks t).set i (.key c0 y) := by
      unfold prefixAt
      exact takeWhile_set _ n.ks i _ hp
    have hpk : (prefixAt n.ks t)[i]? = some (.key c0 old) ∨ (prefixAt n.ks t)[i]? = none := by
      cases hq : (prefixAt n.ks t)[i]? with
      | none => exact Or.inr rfl
      | some b =>
        left
        have hpf : (prefixAt n.ks t).IsPrefix n.ks := prefixAt_prefix n.ks t
        have := prefix_getElem?_some _ _ hpf i b hq
        rw [hk] at this
        simp only [Option.some.injEq] at this
        rw [← this]
    have hdel : ({ n with ks := n.ks.set i (.key c0 y) } : KNode).delAt t = n.delAt t := by
      unfold KNode.delAt
      simp only
      rw [hpre]
      cases hq : (prefixAt n.ks t)[i]? with
      | none => simp [List.set_eq_of_length_le (by
          rw [List.getElem?_eq_none_iff] at hq; exact hq)]
      | some b =>
        rcases hpk with h1 | h1
        · exact lastBitmapOf_set_key _ i c0 y ⟨old, h1⟩
        · rw [h1] at hq; cases hq
    simp only at hl
    rw [hpre, hdel] at hl
    unfold keyLookup at hl
    have hz : (List.set (prefixAt n.ks t) i (Klong.key c0 y)).zipIdx =
        (prefixAt n.ks t).zipIdx.map (fun q => if q.2 = i then (Klong.key c0 y, q.2) else q) := by
      apply List.ext_getElem
      · simp
      · intro j h1 h2
        simp only [List.getElem_zipIdx, List.getElem_map, List.getElem_set, Nat.zero_add]
        by_cases hji : j = i
        · simp [hji]
        · simp [hji, Ne.symm hji]
    rw [hz] at hl
    have hsrc : ∀ k j, (k, j) ∈ (prefixAt n.ks t).zipIdx → j = i → k = .key c0 old := by
      intro k j hm hj
      subst hj
      have h1 : (prefixAt n.ks t)[j]? = some k := List.mem_zipIdx_iff_getElem?.mp hm
      have hpf : (prefixAt n.ks t).IsPrefix n.ks := prefixAt_prefix n.ks t
      have h2 := prefix_getElem?_some _ _ hpf j k h1
      rw [hk] at h2
      simp only [Option.some.injEq] at h2
      exact h2.symm
    rcases keyLookupFold_set (n.delAt t) c y _ i c0 old none none (Or.inl rfl) hsrc with h1 | h1
    · rw [hl] at h1
      left
      apply mem_of_lookup_nodup _ c z
      rw [KNode.liveAt_lookup]
      exact h1.symm
    · rw [hl] at h1
      simp only [Option.some.injEq] at h1
      exact Or.inr h1
  · exact Or.inl h

end SIS.Tree
