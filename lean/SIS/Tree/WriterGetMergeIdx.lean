/-
The merge's siblings are neighbours (bergdb 024-22): `mergeIdx`'s right
choice has the smallest live compare value above the merged node's, its left
choice the largest below (`mergeIdx_right_min`, `mergeIdx_left_max`), so no
live klong of the parent lies between the two klongs that the merge joins.
-/
import SIS.Tree.WriterGetMerge

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- What `mergeIdx`'s fold has chosen so far is the smallest kept compare value
above cx, and the largest below; with none chosen, there is none. -/
def MergeMinMaxOK (ks : List Klong) (del : List Nat) (cx : Nat)
    (acc : Option Nat × Option (Nat × Nat) × Option (Nat × Nat)) : Prop :=
  (∀ i cv, acc.2.1 = some (i, cv) → ∀ j c' y', ks[j]? = some (.key c' y') → j ∉ del → cx < c' →
    cv ≤ c') ∧
  (∀ i cv, acc.2.2 = some (i, cv) → ∀ j c' y', ks[j]? = some (.key c' y') → j ∉ del → c' < cx →
    c' ≤ cv) ∧
  (acc.2.1 = none → ∀ j c' y', ks[j]? = some (.key c' y') → j ∉ del → ¬ cx < c') ∧
  (acc.2.2 = none → ∀ j c' y', ks[j]? = some (.key c' y') → j ∉ del → ¬ c' < cx)

theorem mergeMinMaxOK_step (ks : List Klong) (del : List Nat) (cx : Nat)
    (acc : Option Nat × Option (Nat × Nat) × Option (Nat × Nat)) (k : Klong)
    (ha : MergeMinMaxOK ks del cx acc) :
    MergeMinMaxOK (ks ++ [k]) del cx (mergePhysicalStep del cx acc (k, ks.length)) := by
  obtain ⟨h1, h2, h3, h4⟩ := ha
  -- the klongs before
  have hold : ∀ j c' y', (ks ++ [k])[j]? = some (.key c' y') →
      (ks[j]? = some (.key c' y')) ∨ (j = ks.length ∧ k = .key c' y') := by
    intro j c' y' h
    rcases Nat.lt_or_ge j ks.length with hj | hj
    · left; rw [getElem?_append_single_lt _ _ _ hj] at h; exact h
    · rcases Nat.lt_or_ge ks.length j with hj' | hj'
      · rw [getElem?_append_single_gt _ _ _ hj'] at h; cases h
      · have : j = ks.length := by omega
        subst this
        rw [getElem?_append_single_eq] at h
        simp only [Option.some.injEq] at h
        exact Or.inr ⟨rfl, h⟩
  cases k with
  | time t =>
    refine ⟨fun i cv h j c' y' hj hd hc => ?_, fun i cv h j c' y' hj hd hc => ?_,
      fun h j c' y' hj hd => ?_, fun h j c' y' hj hd => ?_⟩ <;>
    rcases hold j c' y' hj with hj | ⟨_, hk⟩ <;> (try cases hk)
    · exact h1 i cv h j c' y' hj hd hc
    · exact h2 i cv h j c' y' hj hd hc
    · exact h3 h j c' y' hj hd
    · exact h4 h j c' y' hj hd
  | del b =>
    refine ⟨fun i cv h j c' y' hj hd hc => ?_, fun i cv h j c' y' hj hd hc => ?_,
      fun h j c' y' hj hd => ?_, fun h j c' y' hj hd => ?_⟩ <;>
    rcases hold j c' y' hj with hj | ⟨_, hk⟩ <;> (try cases hk)
    · exact h1 i cv h j c' y' hj hd hc
    · exact h2 i cv h j c' y' hj hd hc
    · exact h3 h j c' y' hj hd
    · exact h4 h j c' y' hj hd
  | key cv' y0 =>
    by_cases hd0 : ks.length ∈ del
    · simp only [mergePhysicalStep, List.contains_eq_mem, hd0, decide_true, ↓reduceIte]
      refine ⟨fun i cv h j c' y' hj hd hc => ?_, fun i cv h j c' y' hj hd hc => ?_,
        fun h j c' y' hj hd => ?_, fun h j c' y' hj hd => ?_⟩ <;>
      rcases hold j c' y' hj with hj | ⟨hjl, _⟩
      · exact h1 i cv h j c' y' hj hd hc
      · exact absurd (hjl ▸ hd0) hd
      · exact h2 i cv h j c' y' hj hd hc
      · exact absurd (hjl ▸ hd0) hd
      · exact h3 h j c' y' hj hd
      · exact absurd (hjl ▸ hd0) hd
      · exact h4 h j c' y' hj hd
      · exact absurd (hjl ▸ hd0) hd
    · simp only [mergePhysicalStep, List.contains_eq_mem, hd0, decide_false, Bool.false_eq_true,
        ↓reduceIte]
      have hnew : ∀ j c' y', (ks ++ [Klong.key cv' y0])[j]? = some (.key c' y') → j ∉ del →
          (ks[j]? = some (.key c' y') ∧ j ∉ del) ∨ c' = cv' := by
        intro j c' y' hj hd
        rcases hold j c' y' hj with hj | ⟨_, hk⟩
        · exact Or.inl ⟨hj, hd⟩
        · simp only [Klong.key.injEq] at hk; exact Or.inr hk.1.symm
      by_cases hc : cv' = cx
      · subst hc
        simp only [beq_self_eq_true, ↓reduceIte]
        refine ⟨fun i cv h j c' y' hj hd hc' => ?_, fun i cv h j c' y' hj hd hc' => ?_,
          fun h j c' y' hj hd => ?_, fun h j c' y' hj hd => ?_⟩ <;>
        rcases hnew j c' y' hj hd with ⟨hj', hd'⟩ | hce
        · exact h1 i cv h j c' y' hj' hd' hc'
        · omega
        · exact h2 i cv h j c' y' hj' hd' hc'
        · omega
        · exact h3 h j c' y' hj' hd'
        · omega
        · exact h4 h j c' y' hj' hd'
        · omega
      · have hb : (cv' == cx) = false := by simpa using hc
        simp only [hb, Bool.false_eq_true, ↓reduceIte]
        by_cases hlt : cx < cv'
        · simp only [hlt, ↓reduceIte]
          refine ⟨fun i cv h j c' y' hj hd hc' => ?_, fun i cv h j c' y' hj hd hc' => ?_,
            fun h j c' y' hj hd => ?_, fun h j c' y' hj hd => ?_⟩
          · -- the new right choice
            simp only at h
            cases ha1 : acc.2.1 with
            | none =>
              rw [ha1] at h
              simp only [Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨_, rfl⟩ := h
              rcases hnew j c' y' hj hd with ⟨hj', hd'⟩ | hce
              · exact absurd hc' (h3 ha1 j c' y' hj' hd')
              · omega
            | some p0 =>
              obtain ⟨i0, cva⟩ := p0
              rw [ha1] at h
              simp only at h
              by_cases hle : cv' ≤ cva
              · simp only [hle, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
                obtain ⟨_, rfl⟩ := h
                rcases hnew j c' y' hj hd with ⟨hj', hd'⟩ | hce
                · have := h1 i0 cva ha1 j c' y' hj' hd' hc'; omega
                · omega
              · simp only [hle, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
                obtain ⟨_, hcv⟩ := h
                rcases hnew j c' y' hj hd with ⟨hj', hd'⟩ | hce
                · rw [← hcv]; exact h1 i0 cva ha1 j c' y' hj' hd' hc'
                · omega
          · rcases hnew j c' y' hj hd with ⟨hj', hd'⟩ | hce
            · exact h2 i cv h j c' y' hj' hd' hc'
            · omega
          · simp only at h
            cases ha1 : acc.2.1 with
            | none => rw [ha1] at h; cases h
            | some p0 =>
              obtain ⟨i0, cva⟩ := p0
              rw [ha1] at h
              simp only at h
              split at h <;> cases h
          · rcases hnew j c' y' hj hd with ⟨hj', hd'⟩ | hce
            · exact h4 h j c' y' hj' hd'
            · omega
        · simp only [hlt, ↓reduceIte]
          have hlt' : cv' < cx := by omega
          refine ⟨fun i cv h j c' y' hj hd hc' => ?_, fun i cv h j c' y' hj hd hc' => ?_,
            fun h j c' y' hj hd => ?_, fun h j c' y' hj hd => ?_⟩
          · rcases hnew j c' y' hj hd with ⟨hj', hd'⟩ | hce
            · exact h1 i cv h j c' y' hj' hd' hc'
            · omega
          · -- the new left choice
            simp only at h
            cases ha2 : acc.2.2 with
            | none =>
              rw [ha2] at h
              simp only [Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨_, rfl⟩ := h
              rcases hnew j c' y' hj hd with ⟨hj', hd'⟩ | hce
              · exact absurd hc' (h4 ha2 j c' y' hj' hd')
              · omega
            | some p0 =>
              obtain ⟨i0, cvb⟩ := p0
              rw [ha2] at h
              simp only at h
              by_cases hle : cvb ≤ cv'
              · simp only [hle, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
                obtain ⟨_, rfl⟩ := h
                rcases hnew j c' y' hj hd with ⟨hj', hd'⟩ | hce
                · have := h2 i0 cvb ha2 j c' y' hj' hd' hc'; omega
                · omega
              · simp only [hle, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
                obtain ⟨_, hcv⟩ := h
                rcases hnew j c' y' hj hd with ⟨hj', hd'⟩ | hce
                · rw [← hcv]; exact h2 i0 cvb ha2 j c' y' hj' hd' hc'
                · omega
          · rcases hnew j c' y' hj hd with ⟨hj', hd'⟩ | hce
            · exact h3 h j c' y' hj' hd'
            · omega
          · simp only at h
            cases ha2 : acc.2.2 with
            | none => rw [ha2] at h; cases h
            | some p0 =>
              obtain ⟨i0, cvb⟩ := p0
              rw [ha2] at h
              simp only at h
              split at h <;> cases h

theorem mergeMinMaxOK_fold (del : List Nat) (cx : Nat) (ks : List Klong) :
    MergeMinMaxOK ks del cx (ks.zipIdx.foldl (mergePhysicalStep del cx) (none, none, none)) := by
  have key : ∀ rs : List Klong, MergeMinMaxOK rs.reverse del cx
      (rs.reverse.zipIdx.foldl (mergePhysicalStep del cx) (none, none, none)) := by
    intro rs
    induction rs with
    | nil =>
      refine ⟨fun i cv h => ?_, fun i cv h => ?_, fun _ j c' y' hj => ?_, fun _ j c' y' hj => ?_⟩
      · cases h
      · cases h
      · simp at hj
      · simp at hj
    | cons k rs ih =>
      rw [List.reverse_cons, List.zipIdx_append, List.foldl_append]
      simp only [List.zipIdx_cons, List.zipIdx_nil, Nat.zero_add, List.foldl_cons, List.foldl_nil]
      exact mergeMinMaxOK_step rs.reverse del cx _ k ih
  have := key ks.reverse
  rwa [List.reverse_reverse] at this

/-- A live klong of a node is a key klong that the last bitmap keeps. -/
theorem keyLookup_some_kept (del : List Nat) (c : Nat) (z : NodeId) :
    ∀ ks : List Klong, keyLookup ks del c = some z → ∃ j, ks[j]? = some (.key c z) ∧ j ∉ del := by
  have key : ∀ rs : List Klong, keyLookup rs.reverse del c = some z →
      ∃ j, rs.reverse[j]? = some (.key c z) ∧ j ∉ del := by
    intro rs
    induction rs with
    | nil => intro h; simp [keyLookup] at h
    | cons k rs ih =>
      intro h
      rw [List.reverse_cons, keyLookup_append_single] at h
      unfold keyLookupStep at h
      cases k with
      | key a y =>
        simp only at h
        by_cases hd : del.contains rs.reverse.length
        · rw [hd] at h
          simp only [↓reduceIte] at h
          obtain ⟨j, hj, hjd⟩ := ih h
          refine ⟨j, ?_, hjd⟩
          rw [List.reverse_cons]
          rw [getElem?_append_single_lt _ _ _ (List.getElem?_eq_some_iff.mp hj).1]
          exact hj
        · simp only [hd, Bool.false_eq_true, ↓reduceIte] at h
          by_cases ha : a = c
          · subst ha
            simp only [beq_self_eq_true, ↓reduceIte, Option.some.injEq] at h
            subst h
            refine ⟨rs.reverse.length, ?_, by simpa using hd⟩
            rw [List.reverse_cons, getElem?_append_single_eq]
          · have hb : (a == c) = false := by simpa using ha
            simp only [hb, Bool.false_eq_true, ↓reduceIte] at h
            obtain ⟨j, hj, hjd⟩ := ih h
            refine ⟨j, ?_, hjd⟩
            rw [List.reverse_cons, getElem?_append_single_lt _ _ _ (List.getElem?_eq_some_iff.mp hj).1]
            exact hj
      | time t =>
        simp only at h
        obtain ⟨j, hj, hjd⟩ := ih h
        refine ⟨j, ?_, hjd⟩
        rw [List.reverse_cons, getElem?_append_single_lt _ _ _ (List.getElem?_eq_some_iff.mp hj).1]
        exact hj
      | del b =>
        simp only at h
        obtain ⟨j, hj, hjd⟩ := ih h
        refine ⟨j, ?_, hjd⟩
        rw [List.reverse_cons, getElem?_append_single_lt _ _ _ (List.getElem?_eq_some_iff.mp hj).1]
        exact hj
  intro ks h
  have := key ks.reverse (by rw [List.reverse_reverse]; exact h)
  rwa [List.reverse_reverse] at this

/-- `mergeIdx`'s right choice: the smallest live compare value above cx. -/
theorem mergeIdx_right_min (n : KNode) (cx : Nat) (ia : Nat) (ca : Nat)
    (h : (mergeIdx n cx).2.1 = some (ia, ca)) :
    ∀ c z, (c, z) ∈ n.live → cx < c → ca ≤ c := by
  intro c z hm hc
  have hlk := lookup_of_mem_nodup _ (KNode.live_keys_nodup n) c z hm
  rw [KNode.live_lookup] at hlk
  obtain ⟨j, hj, hjd⟩ := keyLookup_some_kept n.lastBitmap c z n.ks hlk
  exact (mergeMinMaxOK_fold n.lastBitmap cx n.ks).1 ia ca h j c z hj hjd hc

/-- `mergeIdx`'s left choice: the largest live compare value below cx. -/
theorem mergeIdx_left_max (n : KNode) (cx : Nat) (ib : Nat) (cb : Nat)
    (h : (mergeIdx n cx).2.2 = some (ib, cb)) :
    ∀ c z, (c, z) ∈ n.live → c < cx → c ≤ cb := by
  intro c z hm hc
  have hlk := lookup_of_mem_nodup _ (KNode.live_keys_nodup n) c z hm
  rw [KNode.live_lookup] at hlk
  obtain ⟨j, hj, hjd⟩ := keyLookup_some_kept n.lastBitmap c z n.ks hlk
  exact (mergeMinMaxOK_fold n.lastBitmap cx n.ks).2.1 ib cb h j c z hj hjd hc

end SIS.Tree
