/-
The contract package (bergdb 030-10): the node algebra of a klong pointed in
place (`KNode.linkIndex`, `KNode.repoint`; Java's `Dag.linkIndex`,
`KeyNode.repointKlong`): the live klong of a compare value that names a node
gets another pointee.
-/
import Contract.Proof.NodeAlg3

namespace Contract

/-! ## Helpers -/

/-- What `linkIndex` finds: klong j is a key klong of c naming y, the last
bitmap does not delete it, and no later klong is a key klong of c. -/
theorem linkIndex_facts {n : MNode} {y : NodeId} {c j : Nat} (h : n.linkIndex y c = some j) :
    n.ks[j]? = some (.key c y) ∧ j ∉ n.lastBitmap ∧
      ∀ j' y', j < j' → n.ks[j']? ≠ some (.key c y') := by
  unfold SIS.Tree.KNode.linkIndex at h
  split at h
  · rename_i c0 y0 i0 heq
    simp only at h
    split at h
    · rename_i hc
      simp only [Option.some.injEq] at h
      subst h
      simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at hc
      obtain ⟨hp, as, bs, hxs, has⟩ := List.find?_eq_some_iff_append.mp heq
      simp only [beq_iff_eq] at hp
      subst hp
      have hm : (SIS.Tree.Klong.key c0 y0, i0) ∈ n.ks.zipIdx := by
        rw [← List.mem_reverse, hxs]
        exact List.mem_append_right _ List.mem_cons_self
      have hi := List.mem_zipIdx_iff_getElem?.mp hm
      simp only at hi
      refine ⟨by rw [hi, hc.2], by simpa using hc.1, ?_⟩
      intro j' y' hlt hj'
      have hm' : (SIS.Tree.Klong.key c0 y', j') ∈ n.ks.zipIdx :=
        List.mem_zipIdx_iff_getElem?.mpr hj'
      rw [← List.mem_reverse, hxs] at hm'
      have hsr : (n.ks.zipIdx.reverse).Pairwise (fun a b => b.2 < a.2) :=
        List.pairwise_reverse.mpr (zipIdx_sorted n.ks 0)
      rw [hxs, List.pairwise_append, List.pairwise_cons] at hsr
      rcases List.mem_append.mp hm' with h1 | h1
      · have := has _ h1
        simp at this
      · rcases List.mem_cons.mp h1 with h1 | h1
        · simp only [Prod.mk.injEq] at h1
          omega
        · have := hsr.2.1.1 _ h1
          simp only at this
          omega
    · simp at h
  · simp at h

theorem liveWith_eq_foldl (d : List Nat) (L : List (Klong × Nat)) :
    liveWith d L = L.foldl (n3LiveStep d) [] := by
  unfold liveWith
  congr 1

theorem insertCv_twice {m : List (Nat × NodeId)} (hs : m.Pairwise CvLt) (c : Nat)
    (y y' : NodeId) : insertCv c y' (insertCv c y m) = insertCv c y' m := by
  refine cvSorted_ext (insertCv_sorted _ _ (insertCv_sorted _ _ hs)) (insertCv_sorted _ _ hs)
    (fun p => ?_)
  rw [mem_insertCv_iff (insertCv_sorted _ _ hs), mem_insertCv_iff hs, mem_insertCv_iff hs]
  constructor
  · rintro (h | ⟨h | ⟨h1, h2⟩, h3⟩)
    · exact Or.inl h
    · exact absurd (by rw [h] : p.1 = c) h3
    · exact Or.inr ⟨h1, h2⟩
  · rintro (h | ⟨h1, h2⟩)
    · exact Or.inl h
    · exact Or.inr ⟨Or.inr ⟨h1, h2⟩, h2⟩

theorem insertCv_comm {m : List (Nat × NodeId)} (hs : m.Pairwise CvLt) {c d : Nat} (hdc : d ≠ c)
    (y z : NodeId) : insertCv d z (insertCv c y m) = insertCv c y (insertCv d z m) := by
  refine cvSorted_ext (insertCv_sorted _ _ (insertCv_sorted _ _ hs))
    (insertCv_sorted _ _ (insertCv_sorted _ _ hs)) (fun p => ?_)
  rw [mem_insertCv_iff (insertCv_sorted _ _ hs), mem_insertCv_iff hs,
    mem_insertCv_iff (insertCv_sorted _ _ hs), mem_insertCv_iff hs]
  constructor
  · rintro (h | ⟨h | ⟨h1, h2⟩, h3⟩)
    · subst h
      exact Or.inr ⟨Or.inl rfl, hdc⟩
    · exact Or.inl h
    · exact Or.inr ⟨Or.inr ⟨h1, h3⟩, h2⟩
  · rintro (h | ⟨h | ⟨h1, h2⟩, h3⟩)
    · subst h
      exact Or.inr ⟨Or.inl rfl, Ne.symm hdc⟩
    · exact Or.inl h
    · exact Or.inr ⟨Or.inr ⟨h1, h3⟩, h2⟩

/-- Over klongs with no key klong of c, setting c first or last is the same. -/
theorem foldl_step_rel (D : List Nat) (c : Nat) (y' : NodeId) :
    ∀ (L : List (Klong × Nat)), (∀ z i, (Klong.key c z, i) ∉ L) →
      ∀ m : List (Nat × NodeId), m.Pairwise CvLt →
        L.foldl (n3LiveStep D) (insertCv c y' m) = insertCv c y' (L.foldl (n3LiveStep D) m)
  | [], _, _, _ => rfl
  | (k, i) :: L, hL, m, hm => by
    have hL' : ∀ z i', (Klong.key c z, i') ∉ L := fun z i' h => hL z i' (List.mem_cons_of_mem _ h)
    simp only [List.foldl_cons]
    cases k with
    | key d z =>
      have hd : d ≠ c := by
        rintro rfl
        exact hL z i List.mem_cons_self
      have e1 : n3LiveStep D (insertCv c y' m) (Klong.key d z, i) =
          if D.contains i then insertCv c y' m else insertCv d z (insertCv c y' m) := rfl
      have e2 : n3LiveStep D m (Klong.key d z, i) =
          if D.contains i then m else insertCv d z m := rfl
      rw [e1, e2]
      split
      · exact foldl_step_rel D c y' L hL' m hm
      · rw [insertCv_comm hm hd]
        exact foldl_step_rel D c y' L hL' _ (insertCv_sorted _ _ hm)
    | time x => exact foldl_step_rel D c y' L hL' m hm
    | del b => exact foldl_step_rel D c y' L hL' m hm

/-- Over klongs with no key klong of c, the pointee of c is kept. -/
theorem foldl_step_mem (D : List Nat) (c : Nat) (y : NodeId) :
    ∀ (L : List (Klong × Nat)), (∀ z i, (Klong.key c z, i) ∉ L) →
      ∀ m : List (Nat × NodeId), m.Pairwise CvLt → (c, y) ∈ m →
        (c, y) ∈ L.foldl (n3LiveStep D) m
  | [], _, _, _, hy => hy
  | (k, i) :: L, hL, m, hm, hy => by
    have hL' : ∀ z i', (Klong.key c z, i') ∉ L := fun z i' h => hL z i' (List.mem_cons_of_mem _ h)
    simp only [List.foldl_cons]
    cases k with
    | key d z =>
      have hd : d ≠ c := by
        rintro rfl
        exact hL z i List.mem_cons_self
      have e : n3LiveStep D m (Klong.key d z, i) =
          if D.contains i then m else insertCv d z m := rfl
      rw [e]
      split
      · exact foldl_step_mem D c y L hL' m hm hy
      · refine foldl_step_mem D c y L hL' _ (insertCv_sorted _ _ hm) ?_
        rw [mem_insertCv_iff hm]
        exact Or.inr ⟨hy, fun e => hd e.symm⟩
    | time x => exact foldl_step_mem D c y L hL' m hm hy
    | del b => exact foldl_step_mem D c y L hL' m hm hy

/-- The live klongs of klongs with one klong marked: the fold before it, its
step, and the fold after it. -/
theorem n4live_split (A B : List Klong) (x : Klong) :
    live (A ++ x :: B) = (B.zipIdx (A.length + 1)).foldl (n3LiveStep (lastBitmap (A ++ x :: B)))
      (n3LiveStep (lastBitmap (A ++ x :: B))
        (A.zipIdx.foldl (n3LiveStep (lastBitmap (A ++ x :: B))) []) (x, A.length)) := by
  unfold live
  rw [liveWith_eq_foldl, List.zipIdx_append, List.foldl_append, List.zipIdx_cons, List.foldl_cons,
    Nat.zero_add]

theorem lastBitmap_keyswap (A B : List Klong) (c : Nat) (y y' : NodeId) :
    lastBitmap (A ++ Klong.key c y :: B) = lastBitmap (A ++ Klong.key c y' :: B) := by
  unfold lastBitmap
  rw [List.foldl_append, List.foldl_append, List.foldl_cons, List.foldl_cons]

theorem cvAt_keyswap (A B : List Klong) (c : Nat) (y y' : NodeId) :
    cvAt (A ++ Klong.key c y :: B) = cvAt (A ++ Klong.key c y' :: B) := by
  funext j
  unfold cvAt
  by_cases hj : j < A.length
  · rw [List.getElem?_append_left hj, List.getElem?_append_left hj]
  · rw [List.getElem?_append_right (Nat.le_of_not_lt hj),
      List.getElem?_append_right (Nat.le_of_not_lt hj)]
    cases j - A.length with
    | zero => rfl
    | succ m => rfl

theorem klongsWf_keyswap (A B : List Klong) (c : Nat) (y y' : NodeId) :
    klongsWf (A ++ Klong.key c y :: B) = klongsWf (A ++ Klong.key c y' :: B) := by
  have hcv := cvAt_keyswap A B c y y'
  have hbo : bitmapOk (A ++ Klong.key c y :: B) = bitmapOk (A ++ Klong.key c y' :: B) := by
    funext i before bits
    unfold bitmapOk
    rw [hcv]
  have hbs : bmStep (A ++ Klong.key c y :: B) = bmStep (A ++ Klong.key c y' :: B) := by
    funext acc k i
    unfold bmStep
    rw [hbo]
  have ht : timesOk (A ++ Klong.key c y :: B) = timesOk (A ++ Klong.key c y' :: B) := by
    rw [timesOk_eq, timesOk_eq, List.foldl_append, List.foldl_append, List.foldl_cons,
      List.foldl_cons]
    cases A with
    | nil => rfl
    | cons a A' =>
      rw [headOk_append (List.cons_ne_nil _ _), headOk_append (List.cons_ne_nil _ _)]
      rfl
  have hb : bitmapsOk (A ++ Klong.key c y :: B) = bitmapsOk (A ++ Klong.key c y' :: B) := by
    unfold bitmapsOk
    rw [hbs, List.zipIdx_append, List.zipIdx_append, List.foldl_append, List.foldl_append,
      List.zipIdx_cons, List.zipIdx_cons, List.foldl_cons, List.foldl_cons]
    rfl
  unfold klongsWf
  rw [ht, hb]

/-- Klong j of a node, a key klong, splits the contract's klongs. -/
theorem ksOf_split {n : MNode} {j c : Nat} {y : NodeId} (hj : n.ks[j]? = some (.key c y)) :
    ksOf n = (ksOf n).take j ++ Klong.key c y :: (ksOf n).drop (j + 1) ∧
      ((ksOf n).take j).length = j := by
  have hj' : (ksOf n)[j]? = some (Klong.key c y) := by
    rw [ksOf_getElem?, hj]
    rfl
  obtain ⟨hlt, hget⟩ := List.getElem?_eq_some_iff.mp hj'
  constructor
  · conv_lhs => rw [← List.take_append_drop j (ksOf n)]
    rw [List.drop_eq_getElem_cons hlt, hget]
  · rw [List.length_take]
    omega

theorem ksOf_repoint_set {n : MNode} {j c : Nat} {y : NodeId} (hj : n.ks[j]? = some (.key c y))
    (y' : NodeId) : ksOf (n.repoint j y') = (ksOf n).set j (Klong.key c y') := by
  unfold SIS.Tree.KNode.repoint
  rw [hj]
  show (n.ks.set j (.key c y')).map kOf = _
  rw [List.map_set]
  rfl

/-- No key klong of c after klong j. -/
theorem drop_no_key {n : MNode} {j c : Nat}
    (hlast : ∀ j' y', j < j' → n.ks[j']? ≠ some (.key c y')) :
    ∀ z i, (Klong.key c z, i) ∉ ((ksOf n).drop (j + 1)).zipIdx (j + 1) := by
  intro z i hm
  have h3 := List.mem_zipIdx hm
  have hz : Klong.key c z ∈ (ksOf n).drop (j + 1) := by
    rw [h3.2.2]
    exact List.getElem_mem _
  obtain ⟨i', hi'⟩ := List.mem_iff_getElem?.mp hz
  rw [List.getElem?_drop, ksOf_getElem?] at hi'
  obtain ⟨k, hk, hkk⟩ := Option.map_eq_some_iff.mp hi'
  cases k with
  | key c1 z1 =>
    simp only [kOf, Klong.key.injEq] at hkk
    exact hlast (j + 1 + i') z1 (by omega) (by rw [hk, hkk.1])
  | time x => simp [kOf] at hkk
  | del b => simp [kOf] at hkk

/-- `linkIndex y c = some j`: klong j is the last key klong of compare value
c, it names y, and it is live. -/
theorem linkIndex_some {n : MNode} (_hwf : klongsWf (ksOf n) = true) {y : NodeId} {c j : Nat}
    (h : n.linkIndex y c = some j) :
    n.ks[j]? = some (.key c y) ∧ (c, y) ∈ live (ksOf n) ∧
      ∀ j' y', j < j' → n.ks[j']? ≠ some (.key c y') := by
  obtain ⟨hj, hD, hlast⟩ := linkIndex_facts h
  refine ⟨hj, ?_, hlast⟩
  obtain ⟨hsplit, hlen⟩ := ksOf_split hj
  have hB := drop_no_key hlast
  have hD' : j ∉ lastBitmap (ksOf n) := by
    rw [lastBitmap_ksOf]
    exact hD
  generalize (ksOf n).take j = A at hsplit hlen
  generalize (ksOf n).drop (j + 1) = B at hsplit hB
  rw [hsplit] at hD' ⊢
  rw [n4live_split, hlen]
  have hstep : ∀ m, n3LiveStep (lastBitmap (A ++ Klong.key c y :: B)) m (Klong.key c y, j) =
      insertCv c y m := by
    intro m
    simp [n3LiveStep, hD']
  rw [hstep]
  have hM0 : (A.zipIdx.foldl (n3LiveStep (lastBitmap (A ++ Klong.key c y :: B))) []).Pairwise
      CvLt := by
    rw [← liveWith_eq_foldl]
    exact liveWith_sorted _ _
  exact foldl_step_mem _ c y _ hB _ (insertCv_sorted _ _ hM0)
    ((mem_insertCv_iff hM0).mpr (Or.inl rfl))

theorem repoint_live {n : MNode} (_hwf : klongsWf (ksOf n) = true) {y : NodeId} {c j : Nat}
    (h : n.linkIndex y c = some j) (y' : NodeId) :
    live (ksOf (n.repoint j y')) = insertCv c y' (live (ksOf n)) := by
  obtain ⟨hj, hD, hlast⟩ := linkIndex_facts h
  obtain ⟨hsplit, hlen⟩ := ksOf_split hj
  have hB := drop_no_key hlast
  have hD' : j ∉ lastBitmap (ksOf n) := by
    rw [lastBitmap_ksOf]
    exact hD
  rw [ksOf_repoint_set hj]
  generalize (ksOf n).take j = A at hsplit hlen
  generalize (ksOf n).drop (j + 1) = B at hsplit hB
  rw [hsplit] at hD' ⊢
  rw [List.set_append_right _ _ (by omega), hlen, Nat.sub_self, List.set_cons_zero,
    n4live_split, n4live_split, hlen, ← lastBitmap_keyswap A B c y y']
  have hstep : ∀ m (z : NodeId),
      n3LiveStep (lastBitmap (A ++ Klong.key c y :: B)) m (Klong.key c z, j) = insertCv c z m := by
    intro m z
    simp [n3LiveStep, hD']
  rw [hstep, hstep]
  have hM0 : (A.zipIdx.foldl (n3LiveStep (lastBitmap (A ++ Klong.key c y :: B))) []).Pairwise
      CvLt := by
    rw [← liveWith_eq_foldl]
    exact liveWith_sorted _ _
  rw [← insertCv_twice hM0 c y y']
  exact foldl_step_rel _ c y' _ hB _ (insertCv_sorted _ _ hM0)

theorem repoint_wf {n : MNode} (hwf : klongsWf (ksOf n) = true) {y : NodeId} {c j : Nat}
    (h : n.linkIndex y c = some j) (y' : NodeId) : klongsWf (ksOf (n.repoint j y')) = true := by
  obtain ⟨hj, _, _⟩ := linkIndex_facts h
  obtain ⟨hsplit, hlen⟩ := ksOf_split hj
  rw [ksOf_repoint_set hj]
  generalize (ksOf n).take j = A at hsplit hlen
  generalize (ksOf n).drop (j + 1) = B at hsplit
  rw [hsplit] at hwf ⊢
  rw [List.set_append_right _ _ (by omega), hlen, Nat.sub_self, List.set_cons_zero,
    ← klongsWf_keyswap A B c y y']
  exact hwf

theorem repoint_size (n : MNode) (j : Nat) (y' : NodeId) : (n.repoint j y').size = n.size := by
  unfold SIS.Tree.KNode.repoint
  split
  · simp [SIS.Tree.KNode.size, SIS.Tree.KNode.setAt]
  · rfl

theorem repoint_leaf (n : MNode) (j : Nat) (y' : NodeId) : (n.repoint j y').leaf = n.leaf := by
  unfold SIS.Tree.KNode.repoint
  split <;> rfl

theorem repoint_timesLe {n : MNode} {t : Time} (h : TimesLe n t) (j : Nat) (y' : NodeId) :
    TimesLe (n.repoint j y') t := by
  unfold SIS.Tree.KNode.repoint
  split
  · rename_i c0 y0 _
    intro t' ht'
    have e : ksOf (n.setAt j (.key c0 y')) = (ksOf n).set j (Klong.key c0 y') := by
      simp [ksOf, SIS.Tree.KNode.setAt, List.map_set, kOf]
    rw [e] at ht'
    rcases List.mem_or_eq_of_mem_set ht' with h1 | h1
    · exact h t' h1
    · simp at h1
  · exact h

theorem repoint_first {n : MNode} {t0 : Time} {rest : List MKlong} (h : n.ks = .time t0 :: rest)
    (j : Nat) (y' : NodeId) : ∃ rest', (n.repoint j y').ks = .time t0 :: rest' := by
  unfold SIS.Tree.KNode.repoint
  split
  · rename_i c0 y0 heq
    cases j with
    | zero =>
      rw [h] at heq
      simp at heq
    | succ j' =>
      show ∃ rest', n.ks.set (j' + 1) _ = _
      rw [h, List.set_cons_succ]
      exact ⟨_, rfl⟩
  · exact ⟨rest, h⟩

/-- The key klongs after it: those before, or the klong pointed. -/
theorem repoint_key_mem {n : MNode} {y : NodeId} {c j : Nat} (h : n.linkIndex y c = some j)
    {y' : NodeId} {c' : Nat} {z : NodeId} (hm : Klong.key c' z ∈ ksOf (n.repoint j y')) :
    Klong.key c' z ∈ ksOf n ∨ (c' = c ∧ z = y') := by
  obtain ⟨hj, _, _⟩ := linkIndex_facts h
  rw [ksOf_repoint_set hj] at hm
  rcases List.mem_or_eq_of_mem_set hm with h1 | h1
  · exact Or.inl h1
  · simp only [Klong.key.injEq] at h1
    exact Or.inr h1

/-- The frame: if no klong of before the transaction (ks0) names y, the klong
pointed is one after the time klong of i. -/
theorem repoint_ext {n : MNode} {i : Time} {ks0 : List Klong} {y : NodeId} {c j : Nat}
    (h : n.linkIndex y c = some j) (hy : ∀ c', Klong.key c' y ∉ ks0)
    (he : ksOf n = ks0 ∨ ∃ more, ksOf n = ks0 ++ Klong.time i :: more) (y' : NodeId) :
    ∃ more, ksOf (n.repoint j y') = ks0 ++ Klong.time i :: more := by
  obtain ⟨hj, _, _⟩ := linkIndex_facts h
  have hj' : (ksOf n)[j]? = some (Klong.key c y) := by
    rw [ksOf_getElem?, hj]
    rfl
  rw [ksOf_repoint_set hj]
  rcases he with he | ⟨more, he⟩
  · exfalso
    rw [he] at hj'
    exact hy c (List.mem_of_getElem? hj')
  · rw [he] at hj' ⊢
    by_cases h1 : j < ks0.length
    · rw [List.getElem?_append_left h1] at hj'
      exact absurd (List.mem_of_getElem? hj') (hy c)
    · rw [List.getElem?_append_right (Nat.le_of_not_lt h1)] at hj'
      rw [List.set_append_right _ _ (Nat.le_of_not_lt h1)]
      cases hjm : j - ks0.length with
      | zero =>
        rw [hjm] at hj'
        simp at hj'
      | succ m =>
        rw [List.set_cons_succ]
        exact ⟨_, rfl⟩

end Contract
