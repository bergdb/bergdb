/-
The live klongs of a node after the writer's node functions (bergdb 024-22,
step 4; the walk of the heights, SIS/Tree/OverlayHeights.lean): with no premise
on the node, a live klong after a change is a live klong before it or one that
the change wrote. A node's live klongs are `KNode.live`, the key klongs of its
last version at its last bitmap.
-/
import SIS.Tree.OverlayHeights

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-! ## The key lookup -/

/-- The key lookup ends with its start or with the pointer of a key klong of
the compare value. -/
theorem ht_lookup_fold (del : List Nat) (c : Nat) :
    ∀ (xs : List (Klong × Nat)) (v : Option NodeId) (z : NodeId),
      xs.foldl (keyLookupStep del c) v = some z → v = some z ∨ ∃ i, (Klong.key c z, i) ∈ xs
  | [], v, z, h => Or.inl h
  | q :: qs, v, z, h => by
    rw [List.foldl_cons] at h
    rcases ht_lookup_fold del c qs _ z h with h1 | ⟨i, hi⟩
    · rcases q with ⟨k, j⟩
      unfold keyLookupStep at h1
      cases k with
      | time t => exact Or.inl h1
      | del b => exact Or.inl h1
      | key a y =>
        simp only at h1
        split at h1
        · exact Or.inl h1
        · split at h1
          · rename_i ha
            cases h1
            have hac : a = c := by simpa using ha
            subst hac
            exact Or.inr ⟨j, List.mem_cons_self⟩
          · exact Or.inl h1
    · exact Or.inr ⟨i, List.mem_cons_of_mem _ hi⟩

theorem ht_mem_of_zipIdx {x : Klong} {i k : Nat} {xs : List Klong} (h : (x, i) ∈ xs.zipIdx k) :
    x ∈ xs := by
  obtain ⟨h1, h2, h3⟩ := List.mem_zipIdx h
  rw [h3]
  exact List.getElem_mem _

/-- A pointer that the lookup gives is a key klong's. -/
theorem ht_keyLookup_mem {ks : List Klong} {del : List Nat} {c : Nat} {z : NodeId}
    (h : keyLookup ks del c = some z) : Klong.key c z ∈ ks := by
  unfold keyLookup at h
  rcases ht_lookup_fold del c _ none z h with h1 | ⟨i, hi⟩
  · cases h1
  · exact ht_mem_of_zipIdx hi

/-- After klongs appended: the lookup before, or a key klong appended. -/
theorem ht_keyLookup_append {ks more : List Klong} {del : List Nat} {c : Nat} {z : NodeId}
    (h : keyLookup (ks ++ more) del c = some z) :
    keyLookup ks del c = some z ∨ Klong.key c z ∈ more := by
  unfold keyLookup at h ⊢
  rw [List.zipIdx_append, List.foldl_append] at h
  rcases ht_lookup_fold del c _ _ z h with h1 | ⟨i, hi⟩
  · exact Or.inl h1
  · exact Or.inr (ht_mem_of_zipIdx hi)

/-- Two klongs alike but maybe for the pointer of a key klong, which then is in S. -/
def PtrSwap (S : NodeId → Prop) (k k' : Klong) : Prop :=
  k' = k ∨ ∃ a y y', k = .key a y ∧ k' = .key a y' ∧ S y'

/-- Two lists of klongs alike klong by klong (`PtrSwap`). -/
def PtrSwapL (S : NodeId → Prop) : List Klong → List Klong → Prop
  | [], [] => True
  | a :: as, b :: bs => PtrSwap S a b ∧ PtrSwapL S as bs
  | _, _ => False

theorem ht_swap_fold (S : NodeId → Prop) (del : List Nat) (c : Nat) :
    ∀ (ks ks' : List Klong) (k : Nat) (v v' : Option NodeId),
      PtrSwapL S ks ks' → (v' = v ∨ ∃ y', v' = some y' ∧ S y') →
      ((ks'.zipIdx k).foldl (keyLookupStep del c) v' = (ks.zipIdx k).foldl (keyLookupStep del c) v ∨
        ∃ y', (ks'.zipIdx k).foldl (keyLookupStep del c) v' = some y' ∧ S y')
  | [], [], k, v, v', _, hv => by simpa using hv
  | [], _ :: _, _, _, _, hf, _ => by simp [PtrSwapL] at hf
  | _ :: _, [], _, _, _, hf, _ => by simp [PtrSwapL] at hf
  | a :: as, b :: bs, k, v, v', hf, hv => by
    obtain ⟨hab, hrest⟩ := hf
    simp only [List.zipIdx_cons, List.foldl_cons]
    apply ht_swap_fold S del c as bs (k + 1) _ _ hrest
    rcases hab with hab | ⟨a', y, y', rfl, rfl, hs⟩
    · subst hab
      unfold keyLookupStep
      cases b with
      | time t => exact hv
      | del d => exact hv
      | key a y =>
        simp only
        split
        · exact hv
        · split
          · exact Or.inl rfl
          · exact hv
    · unfold keyLookupStep
      simp only
      split
      · exact hv
      · split
        · exact Or.inr ⟨y', rfl, hs⟩
        · exact hv

theorem ht_keyLookup_swap {S : NodeId → Prop} {ks ks' : List Klong} {del : List Nat} {c : Nat}
    {z : NodeId} (hf : PtrSwapL S ks ks') (h : keyLookup ks' del c = some z) :
    keyLookup ks del c = some z ∨ S z := by
  unfold keyLookup at h ⊢
  rcases ht_swap_fold S del c ks ks' 0 none none hf (Or.inl rfl) with h1 | ⟨y', h1, hs⟩
  · rw [h1] at h
    exact Or.inl h
  · rw [h1] at h
    cases h
    exact Or.inr hs

theorem ht_lastBitmapOf_swap {S : NodeId → Prop} :
    ∀ {ks ks' : List Klong}, PtrSwapL S ks ks' → ∀ (d : List Nat),
      ks.foldl (fun d k => match k with | .del b => b | _ => d) d =
        ks'.foldl (fun d k => match k with | .del b => b | _ => d) d
  | [], [], _, d => rfl
  | [], _ :: _, hf, _ => by simp [PtrSwapL] at hf
  | _ :: _, [], hf, _ => by simp [PtrSwapL] at hf
  | a :: as, b :: bs, hf, d => by
    obtain ⟨hab, hrest⟩ := hf
    simp only [List.foldl_cons]
    rcases hab with hab | ⟨a', y, y', rfl, rfl, _⟩
    · subst hab
      exact ht_lastBitmapOf_swap hrest _
    · exact ht_lastBitmapOf_swap hrest _

/-! ## Live klongs -/

theorem ht_live_iff (n : KNode) (c : Nat) (z : NodeId) :
    (c, z) ∈ n.live ↔ keyLookup n.ks n.lastBitmap c = some z := by
  rw [← KNode.live_lookup]
  exact ⟨lookup_of_mem_nodup _ (KNode.live_keys_nodup n) c z, mem_of_lookup_nodup _ c z⟩

/-- A live klong is a key klong of the node. -/
theorem ht_live_mem {n : KNode} {c : Nat} {z : NodeId} (h : (c, z) ∈ n.live) :
    Klong.key c z ∈ n.ks :=
  ht_keyLookup_mem ((ht_live_iff n c z).mp h)

theorem ht_lastBitmapOf_append_keys (ks : List Klong) (more : List Klong)
    (hm : ∀ k ∈ more, ∀ b, k ≠ .del b) : lastBitmapOf (ks ++ more) = lastBitmapOf ks := by
  unfold lastBitmapOf
  rw [List.foldl_append]
  generalize ks.foldl _ [] = d
  induction more generalizing d with
  | nil => rfl
  | cons k more ih =>
    simp only [List.foldl_cons]
    have hk := hm k List.mem_cons_self
    have hrest : ∀ k ∈ more, ∀ b, k ≠ .del b := fun k' hk' => hm k' (List.mem_cons_of_mem _ hk')
    cases k with
    | time t => exact ih hrest d
    | key a y => exact ih hrest d
    | del b => exact absurd rfl (hk b)

/-- A live klong after a key klong added: one before, or the one added. -/
theorem ht_live_add_key {n : KNode} {t : Time} {cv : Nat} {y : NodeId} {c : Nat} {z : NodeId}
    (h : (c, z) ∈ (n.add t (.key cv y)).live) : (c, z) ∈ n.live ∨ (c = cv ∧ z = y) := by
  rw [ht_live_iff] at h
  have hks : ∃ more, (n.add t (.key cv y)).ks = n.ks ++ more ∧ (∀ k ∈ more, ∀ b, k ≠ .del b) ∧
      ∀ a z, Klong.key a z ∈ more → a = cv ∧ z = y := by
    unfold KNode.add
    split
    · split
      · refine ⟨[.time t, .key cv y], rfl, ?_, ?_⟩
        · intro k hk b; simp at hk; rcases hk with rfl | rfl <;> simp
        · intro a z hm; simp at hm; exact hm
      · refine ⟨[.key cv y], rfl, ?_, ?_⟩
        · intro k hk b; simp at hk; subst hk; simp
        · intro a z hm; simp at hm; exact hm
    · refine ⟨[.time t, .key cv y], rfl, ?_, ?_⟩
      · intro k hk b; simp at hk; rcases hk with rfl | rfl <;> simp
      · intro a z hm; simp at hm; exact hm
  obtain ⟨more, he, hnd, hkey⟩ := hks
  have hlb : (n.add t (.key cv y)).lastBitmap = n.lastBitmap := by
    unfold KNode.lastBitmap
    rw [he]
    exact ht_lastBitmapOf_append_keys n.ks more hnd
  rw [hlb, he] at h
  rcases ht_keyLookup_append h with h1 | h1
  · exact Or.inl ((ht_live_iff n c z).mpr h1)
  · exact Or.inr (hkey c z h1)

/-- After key klongs added in turn: a live klong before, or a pair added. -/
theorem ht_live_addFold (t : Time) :
    ∀ (ins : List (Nat × NodeId)) (n : KNode) (c : Nat) (z : NodeId),
      (c, z) ∈ (ins.foldl (fun n (q : Nat × NodeId) => n.add t (.key q.1 q.2)) n).live →
      (c, z) ∈ n.live ∨ (c, z) ∈ ins
  | [], n, c, z, h => Or.inl h
  | q :: ins, n, c, z, h => by
    rw [List.foldl_cons] at h
    rcases ht_live_addFold t ins _ c z h with h1 | h1
    · rcases ht_live_add_key h1 with h2 | ⟨rfl, rfl⟩
      · exact Or.inl h2
      · exact Or.inr List.mem_cons_self
    · exact Or.inr (List.mem_cons_of_mem _ h1)

/-- A node whose klongs are another's with some pointers changed: a live klong
is one of the other's, or names a new pointer. -/
theorem ht_live_swap {S : NodeId → Prop} {n n' : KNode} (hf : PtrSwapL S n.ks n'.ks)
    {c : Nat} {z : NodeId} (h : (c, z) ∈ n'.live) : (c, z) ∈ n.live ∨ S z := by
  rw [ht_live_iff] at h
  have hlb : n'.lastBitmap = n.lastBitmap := by
    unfold KNode.lastBitmap lastBitmapOf
    exact (ht_lastBitmapOf_swap hf []).symm
  rw [hlb] at h
  rcases ht_keyLookup_swap hf h with h1 | h1
  · exact Or.inl ((ht_live_iff n c z).mpr h1)
  · exact Or.inr h1

theorem ht_swapL_refl {S : NodeId → Prop} : ∀ (ks : List Klong), PtrSwapL S ks ks
  | [] => trivial
  | _ :: ks => ⟨Or.inl rfl, ht_swapL_refl ks⟩

theorem ht_swapL_set {S : NodeId → Prop} :
    ∀ (ks : List Klong) (j a : Nat) (y y' : NodeId), ks[j]? = some (.key a y) → S y' →
      PtrSwapL S ks (ks.set j (.key a y'))
  | [], j, a, y, y', h, _ => by simp at h
  | k :: ks, 0, a, y, y', h, hs => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    exact ⟨Or.inr ⟨a, y, y', rfl, rfl, hs⟩, ht_swapL_refl ks⟩
  | k :: ks, j + 1, a, y, y', h, hs => by
    simp only [List.getElem?_cons_succ] at h
    exact ⟨Or.inl rfl, ht_swapL_set ks j a y y' h hs⟩

/-! ## The klongs before the transaction -/

theorem ht_prefixAt_time_cons (t i : Time) (hi : t < i) (r : List Klong) :
    prefixAt (.time i :: r) t = [] := by
  unfold prefixAt
  simp only [List.takeWhile_cons]
  have : decide (i ≤ t) = false := by simp; omega
  simp [this]

theorem ht_toPrev_toPrev (n : KNode) (t : Time) : (n.toPrev t).toPrev t = n.toPrev t := by
  unfold KNode.toPrev
  simp only [prefixAt_idem]

end SIS.Tree
