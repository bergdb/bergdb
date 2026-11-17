/-
The contract package (bergdb 030-04): one node. The live klongs of a node are
in strictly increasing order of their compare values, and Java's searches
(Tree.lean) are lookups in the live klongs.
-/
import Mathlib.Tactic
import Contract.Statement

namespace Contract

/-- The order of live klongs: by compare value, strictly. -/
abbrev CvLt (a b : Nat × NodeId) : Prop := a.1 < b.1

/-! ## The live klongs are in order -/

theorem mem_insertCv {c : Nat} {y : NodeId} {a : Nat × NodeId} :
    ∀ {m : List (Nat × NodeId)}, a ∈ insertCv c y m → a = (c, y) ∨ a ∈ m
  | [], h => by simp [insertCv] at h; exact Or.inl h
  | (c', y') :: r, h => by
    unfold insertCv at h
    split at h
    · rcases List.mem_cons.mp h with h | h
      · exact Or.inl h
      · exact Or.inr h
    · split at h
      · rcases List.mem_cons.mp h with h | h
        · exact Or.inl h
        · exact Or.inr (List.mem_cons_of_mem _ h)
      · rcases List.mem_cons.mp h with h | h
        · exact Or.inr (by rw [h]; exact List.mem_cons_self)
        · rcases mem_insertCv h with h | h
          · exact Or.inl h
          · exact Or.inr (List.mem_cons_of_mem _ h)

theorem insertCv_sorted (c : Nat) (y : NodeId) :
    ∀ {m : List (Nat × NodeId)}, m.Pairwise CvLt → (insertCv c y m).Pairwise CvLt
  | [], _ => by simp [insertCv]
  | (c', y') :: r, h => by
    rw [List.pairwise_cons] at h
    unfold insertCv
    split
    · rename_i hlt
      rw [List.pairwise_cons, List.pairwise_cons]
      refine ⟨?_, h⟩
      intro a ha
      rcases List.mem_cons.mp ha with rfl | ha
      · exact hlt
      · exact lt_trans hlt (h.1 a ha)
    · split
      · rename_i heq
        rw [List.pairwise_cons]
        refine ⟨?_, h.2⟩
        intro a ha
        have := h.1 a ha
        show c < a.1
        rw [heq]; exact this
      · rename_i hnlt hne
        rw [List.pairwise_cons]
        refine ⟨?_, insertCv_sorted c y h.2⟩
        intro a ha
        rcases mem_insertCv ha with rfl | ha
        · show c' < c
          omega
        · exact h.1 a ha

/-- In a list in order, what `insertCv` leaves: the new pair, and the pairs of
other compare values. -/
theorem mem_insertCv_iff {c : Nat} {y : NodeId} {a : Nat × NodeId} :
    ∀ {m : List (Nat × NodeId)}, m.Pairwise CvLt →
      (a ∈ insertCv c y m ↔ a = (c, y) ∨ (a ∈ m ∧ a.1 ≠ c))
  | [], _ => by simp [insertCv]
  | (c', y') :: r, h => by
    rw [List.pairwise_cons] at h
    unfold insertCv
    split
    · rename_i hlt
      simp only [List.mem_cons]
      constructor
      · rintro (h1 | h1 | h1)
        · exact Or.inl h1
        · exact Or.inr ⟨Or.inl h1, by rw [h1]; show c' ≠ c; omega⟩
        · exact Or.inr ⟨Or.inr h1, by have := h.1 a h1; show a.1 ≠ c; unfold CvLt at this; simp at this; omega⟩
      · rintro (h1 | ⟨h1 | h1, _⟩)
        · exact Or.inl h1
        · exact Or.inr (Or.inl h1)
        · exact Or.inr (Or.inr h1)
    · split
      · rename_i heq
        simp only [List.mem_cons]
        constructor
        · rintro (h1 | h1)
          · exact Or.inl h1
          · exact Or.inr ⟨Or.inr h1, by have := h.1 a h1; show a.1 ≠ c; unfold CvLt at this; simp at this; omega⟩
        · rintro (h1 | ⟨h1 | h1, h2⟩)
          · exact Or.inl h1
          · exact absurd (by rw [h1]; exact heq.symm) h2
          · exact Or.inr h1
      · rename_i hnlt hne
        simp only [List.mem_cons]
        rw [mem_insertCv_iff h.2]
        constructor
        · rintro (h1 | h1 | ⟨h1, h2⟩)
          · exact Or.inr ⟨Or.inl h1, by rw [h1]; show c' ≠ c; omega⟩
          · exact Or.inl h1
          · exact Or.inr ⟨Or.inr h1, h2⟩
        · rintro (h1 | ⟨h1 | h1, h2⟩)
          · exact Or.inr (Or.inl h1)
          · exact Or.inl h1
          · exact Or.inr (Or.inr ⟨h1, h2⟩)

/-- Two folds over one list keep a relation that each step keeps. -/
theorem foldl_sim {α β γ : Type} (f : β → α → β) (g : γ → α → γ) (R : β → γ → Prop)
    (h : ∀ b c a, R b c → R (f b a) (g c a)) :
    ∀ (l : List α) (b : β) (c : γ), R b c → R (l.foldl f b) (l.foldl g c)
  | [], _, _, hr => hr
  | a :: l, b, c, hr => foldl_sim f g R h l (f b a) (g c a) (h b c a hr)

theorem liveWith_sorted (del : List Nat) (l : List (Klong × Nat)) :
    (liveWith del l).Pairwise CvLt := by
  unfold liveWith
  refine foldl_sim (γ := Unit) _ (fun _ _ => ()) (fun m _ => m.Pairwise CvLt) ?_ l [] ()
    List.Pairwise.nil
  rintro m _ ⟨k, i⟩ hm
  cases k with
  | key c y =>
    dsimp only
    split
    · exact hm
    · exact insertCv_sorted c y hm
  | _ => exact hm

theorem live_sorted (ks : List Klong) : (live ks).Pairwise CvLt :=
  liveWith_sorted _ _

/-! ## The four searches by order -/

/-- o is the best live klong among those whose compare value meets q, in the
order `le`: none if there is none. -/
def Best (le : Nat → Nat → Prop) (q : Nat → Bool) (m : List (Nat × NodeId)) :
    Option (Nat × NodeId) → Prop
  | none => ∀ b ∈ m, q b.1 = false
  | some a => a ∈ m ∧ q a.1 = true ∧ ∀ b ∈ m, q b.1 = true → le b.1 a.1

theorem sorted_unique {m : List (Nat × NodeId)} (hs : m.Pairwise CvLt) {a b : Nat × NodeId}
    (ha : a ∈ m) (hb : b ∈ m) (h : a.1 = b.1) : a = b := by
  obtain ⟨pre, post, he⟩ := List.append_of_mem ha
  rw [he, List.pairwise_append, List.pairwise_cons] at hs
  rw [he] at hb
  rcases List.mem_append.mp hb with hp | hp
  · have := hs.2.2 b hp a List.mem_cons_self
    unfold CvLt at this; omega
  · rcases List.mem_cons.mp hp with hp | hp
    · exact hp.symm
    · have := hs.2.1.1 b hp
      unfold CvLt at this; omega

theorem Best.unique {le : Nat → Nat → Prop} (hanti : ∀ a b, le a b → le b a → a = b)
    {q : Nat → Bool} {m : List (Nat × NodeId)} (hs : m.Pairwise CvLt)
    {o₁ o₂ : Option (Nat × NodeId)} (h₁ : Best le q m o₁) (h₂ : Best le q m o₂) : o₁ = o₂ := by
  cases o₁ with
  | none =>
    cases o₂ with
    | none => rfl
    | some a => have := h₁ a h₂.1; rw [h₂.2.1] at this; simp at this
  | some a =>
    cases o₂ with
    | none => have := h₂ a h₁.1; rw [h₁.2.1] at this; simp at this
    | some b =>
      have h3 := h₁.2.2 b h₂.1 h₂.2.1
      have h4 := h₂.2.2 a h₁.1 h₁.2.1
      rw [sorted_unique hs h₁.1 h₂.1 (hanti _ _ h4 h3)]

/-- One step of a search keeps `Best`, as one step of `liveWith` adds a klong. -/
theorem Best.step {le : Nat → Nat → Prop} [DecidableRel le] (hrefl : ∀ a, le a a)
    (htrans : ∀ a b c, le a b → le b c → le a c) (htotal : ∀ a b, le a b ∨ le b a)
    {q : Nat → Bool} {m : List (Nat × NodeId)} (hs : m.Pairwise CvLt)
    {o : Option (Nat × NodeId)} (ho : Best le q m o) (c : Nat) (y : NodeId) :
    Best le q (insertCv c y m)
      (if bestOr (o.map (·.1)) (fun b => decide (le b c)) && q c then some (c, y) else o) := by
  have hmem := fun a => mem_insertCv_iff (c := c) (y := y) (a := a) hs
  cases hq : q c with
  | false =>
    simp only [Bool.and_false, Bool.false_eq_true, ite_false]
    cases o with
    | none =>
      intro b hb
      rcases (hmem b).mp hb with rfl | ⟨hb, _⟩
      · exact hq
      · exact ho b hb
    | some a =>
      refine ⟨(hmem a).mpr (Or.inr ⟨ho.1, ?_⟩), ho.2.1, ?_⟩
      · intro h; have h2 := ho.2.1; rw [h, hq] at h2; simp at h2
      · intro b hb hqb
        rcases (hmem b).mp hb with rfl | ⟨hb, _⟩
        · rw [hq] at hqb; simp at hqb
        · exact ho.2.2 b hb hqb
  | true =>
    cases o with
    | none =>
      simp only [Option.map_none, bestOr, Bool.and_true, ite_true]
      refine ⟨(hmem _).mpr (Or.inl rfl), hq, ?_⟩
      intro b hb hqb
      rcases (hmem b).mp hb with rfl | ⟨hb, _⟩
      · exact hrefl _
      · have := ho b hb; rw [hqb] at this; simp at this
    | some a =>
      simp only [Option.map_some, bestOr, Bool.and_true]
      by_cases hle : le a.1 c
      · simp only [hle, decide_true, ite_true]
        refine ⟨(hmem _).mpr (Or.inl rfl), hq, ?_⟩
        intro b hb hqb
        rcases (hmem b).mp hb with rfl | ⟨hb, _⟩
        · exact hrefl _
        · exact htrans _ _ _ (ho.2.2 b hb hqb) hle
      · simp only [hle, decide_false, Bool.false_eq_true, ite_false]
        have hca : le c a.1 := (htotal c a.1).resolve_right hle
        refine ⟨(hmem a).mpr (Or.inr ⟨ho.1, ?_⟩), ho.2.1, ?_⟩
        · intro h; rw [h] at hle; exact hle (hrefl c)
        · intro b hb hqb
          rcases (hmem b).mp hb with rfl | ⟨hb, _⟩
          · exact hca
          · exact ho.2.2 b hb hqb

/-- A search by order finds the best live klong. -/
theorem searchBy_best {le : Nat → Nat → Prop} [DecidableRel le] (hrefl : ∀ a, le a a)
    (htrans : ∀ a b c, le a b → le b c → le a c) (htotal : ∀ a b, le a b ∨ le b a)
    (q : Nat → Bool) (ks : List Klong) :
    Best le q (live ks)
      (searchBy ks (fun c best => bestOr best (fun b => decide (le b c)) && q c)) := by
  unfold live liveWith searchBy
  refine (foldl_sim _ _ (fun m o => m.Pairwise CvLt ∧ Best le q m o) ?_ ks.zipIdx [] none
    ⟨List.Pairwise.nil, by simp [Best]⟩).2
  rintro m o ⟨k, i⟩ ⟨hm, ho⟩
  cases k with
  | key c y =>
    dsimp only
    split
    · exact ⟨hm, ho⟩
    · exact ⟨insertCv_sorted c y hm, ho.step hrefl htrans htotal hm c y⟩
  | time t => dsimp only; split <;> exact ⟨hm, ho⟩
  | del b => dsimp only; split <;> exact ⟨hm, ho⟩

theorem best_getLast? {q : Nat → Bool} {m : List (Nat × NodeId)} (hs : m.Pairwise CvLt) :
    Best (· ≤ ·) q m (m.filter (fun cy => q cy.1)).getLast? := by
  cases h : (m.filter (fun cy => q cy.1)).getLast? with
  | none =>
    rw [List.getLast?_eq_none_iff, List.filter_eq_nil_iff] at h
    intro b hb
    simpa using h b hb
  | some a =>
    obtain ⟨ys, hys⟩ := List.getLast?_eq_some_iff.mp h
    have ha : a ∈ m.filter (fun cy => q cy.1) := by rw [hys]; simp
    have hsf := hs.filter (fun cy => q cy.1)
    rw [hys, List.pairwise_append] at hsf
    refine ⟨(List.mem_filter.mp ha).1, (List.mem_filter.mp ha).2, ?_⟩
    intro b hb hqb
    have hbf : b ∈ m.filter (fun cy => q cy.1) := List.mem_filter.mpr ⟨hb, hqb⟩
    rw [hys] at hbf
    rcases List.mem_append.mp hbf with h1 | h1
    · exact le_of_lt (hsf.2.2 b h1 a (by simp))
    · simp at h1; rw [h1]

theorem best_head? {q : Nat → Bool} {m : List (Nat × NodeId)} (hs : m.Pairwise CvLt) :
    Best (· ≥ ·) q m (m.filter (fun cy => q cy.1)).head? := by
  cases h : (m.filter (fun cy => q cy.1)).head? with
  | none =>
    rw [List.head?_eq_none_iff, List.filter_eq_nil_iff] at h
    intro b hb
    simpa using h b hb
  | some a =>
    obtain ⟨ys, hys⟩ := List.head?_eq_some_iff.mp h
    have ha : a ∈ m.filter (fun cy => q cy.1) := by rw [hys]; simp
    have hsf := hs.filter (fun cy => q cy.1)
    rw [hys, List.pairwise_cons] at hsf
    refine ⟨(List.mem_filter.mp ha).1, (List.mem_filter.mp ha).2, ?_⟩
    intro b hb hqb
    have hbf : b ∈ m.filter (fun cy => q cy.1) := List.mem_filter.mpr ⟨hb, hqb⟩
    rw [hys] at hbf
    rcases List.mem_cons.mp hbf with h1 | h1
    · rw [h1]
    · exact le_of_lt (hsf.1 b h1)

/-- In a list in strictly increasing order of its keys, a lookup finds
exactly the pairs of the list. -/
theorem lookup_iff_mem {α β : Type} [BEq α] [LawfulBEq α] [Preorder α] {l : List (α × β)}
    (h : l.Pairwise (fun a b => a.1 < b.1)) (k : α) (v : β) :
    l.lookup k = some v ↔ (k, v) ∈ l := by
  induction l with
  | nil => simp
  | cons a r ih =>
    obtain ⟨k0, v0⟩ := a
    rw [List.pairwise_cons] at h
    rw [List.lookup_cons]
    by_cases hk : k = k0
    · subst hk
      simp only [beq_self_eq_true, Option.some.injEq, List.mem_cons, Prod.mk.injEq, true_and]
      constructor
      · intro h1; exact Or.inl h1.symm
      · rintro (h1 | h1)
        · exact h1.symm
        · exact absurd (h.1 _ h1) (lt_irrefl k)
    · have hb : (k == k0) = false := by simpa using hk
      simp only [hb, List.mem_cons, Prod.mk.injEq, hk, false_and, false_or]
      exact ih h.2


/-! ## The search for one compare value -/

theorem lookup_insertCv {m : List (Nat × NodeId)} (hs : m.Pairwise CvLt) (c c' : Nat)
    (y : NodeId) : (insertCv c' y m).lookup c = if c = c' then some y else m.lookup c := by
  apply Option.ext
  intro v
  rw [lookup_iff_mem (insertCv_sorted c' y hs), mem_insertCv_iff hs]
  by_cases hc : c = c'
  · subst hc
    simp
    exact eq_comm
  · simp only [hc, ite_false, Prod.mk.injEq, false_and, false_or, ne_eq, not_false_eq_true,
      and_true]
    exact (lookup_iff_mem hs c v).symm

/-- The key klongs of compare value c among indexed klongs: index and pointee. -/
def kc (c : Nat) (l : List (Klong × Nat)) : List (Nat × NodeId) :=
  l.filterMap (fun ki => match ki.1 with
    | .key c' y => if c' = c then some (ki.2, y) else none
    | _ => none)

theorem foldl_zipIdx_snoc {α β : Type} (f : β → α × Nat → β) (b : β) (l : List α) (a : α) :
    (l ++ [a]).zipIdx.foldl f b = f (l.zipIdx.foldl f b) (a, l.length) := by
  rw [List.zipIdx_append, List.foldl_append]
  simp

theorem lastBitmap_snoc (l : List Klong) (k : Klong) :
    lastBitmap (l ++ [k]) = match k with
      | .del b => b
      | _ => lastBitmap l := by
  unfold lastBitmap
  rw [List.foldl_append]
  cases k <;> rfl

theorem kc_snoc (c : Nat) (l : List Klong) (k : Klong) :
    kc c (l ++ [k]).zipIdx = kc c l.zipIdx ++ match k with
      | .key c' y => if c' = c then [(l.length, y)] else []
      | _ => [] := by
  unfold kc
  rw [List.zipIdx_append, List.filterMap_append]
  cases k with
  | key c' y => by_cases h : c' = c <;> simp [h]
  | _ => simp

/-- W2 and W3 for every bitmap of a list of klongs. -/
def BmW (l : List Klong) : Prop :=
  ∀ l1 b l2, l = l1 ++ Klong.del b :: l2 →
    (∀ j ∈ b, j < l1.length) ∧ (∀ j ∈ lastBitmap l1, j ∈ b)

theorem BmW.init {l : List Klong} {k : Klong} (h : BmW (l ++ [k])) : BmW l :=
  fun l1 b l2 he => h l1 b (l2 ++ [k]) (by rw [he]; simp)

theorem lastBitmap_cases (l : List Klong) :
    lastBitmap l = [] ∨ ∃ l1 b l2, l = l1 ++ Klong.del b :: l2 ∧ lastBitmap l = b := by
  induction l using List.reverseRecOn with
  | nil => exact Or.inl rfl
  | append_singleton l k ih =>
    rw [lastBitmap_snoc]
    cases k with
    | del b => exact Or.inr ⟨l, b, [], rfl, rfl⟩
    | time t =>
      rcases ih with h | ⟨l1, b, l2, he, hb⟩
      · exact Or.inl h
      · exact Or.inr ⟨l1, b, l2 ++ [Klong.time t], by rw [he]; simp, hb⟩
    | key c y =>
      rcases ih with h | ⟨l1, b, l2, he, hb⟩
      · exact Or.inl h
      · exact Or.inr ⟨l1, b, l2 ++ [Klong.key c y], by rw [he]; simp, hb⟩

theorem BmW.lt_length {l : List Klong} (h : BmW l) : ∀ j ∈ lastBitmap l, j < l.length := by
  rcases lastBitmap_cases l with h0 | ⟨l1, b, l2, he, hb⟩
  · simp [h0]
  · intro j hj
    rw [hb] at hj
    have := (h l1 b l2 he).1 j hj
    rw [he]
    simp only [List.length_append, List.length_cons]
    omega

/-- The loop of `searchEq` over well-formed klongs: the bitmap so far is the
last one, and the match is the last key klong of c, unless the last bitmap
deletes it. -/
theorem eqFold_spec (c : Nat) (l : List Klong) : BmW l →
    l.zipIdx.foldl (fun acc ki => eqStep c acc ki.1 ki.2) ([], none) =
      (lastBitmap l,
        ((kc c l.zipIdx).getLast?).filter (fun a => !(lastBitmap l).contains a.1)) := by
  induction l using List.reverseRecOn with
  | nil => intro _; rfl
  | append_singleton l k ih =>
    intro hw
    have ih := ih hw.init
    have hlt := hw.init.lt_length
    rw [foldl_zipIdx_snoc, ih]
    have hns : l.length ∉ lastBitmap l := by
      intro hc
      have := hlt _ hc
      omega
    rw [lastBitmap_snoc, kc_snoc]
    cases k with
    | time t => simp [eqStep, hns]
    | key c' y =>
      by_cases hc : c' = c
      · subst hc
        simp [eqStep, hns, Option.filter]
      · simp [eqStep, hns, hc]
    | del b =>
      have hsub := (hw l b [] rfl).2
      cases h : (kc c l.zipIdx).getLast? with
      | none => simp [eqStep, hns, h]
      | some a =>
        by_cases h1 : a.1 ∈ lastBitmap l
        · have h2 : a.1 ∈ b := hsub _ h1
          simp [eqStep, hns, h, Option.filter, h1, h2]
        · by_cases h2 : a.1 ∈ b
          · simp [eqStep, hns, h, Option.filter, h1, h2]
          · simp [eqStep, hns, h, Option.filter, h1, h2]

/-- A lookup in the live klongs: the last key klong of c that the bitmap does
not delete. -/
theorem lookup_liveWith (del : List Nat) (c : Nat) :
    ∀ (l : List (Klong × Nat)) (m : List (Nat × NodeId)), m.Pairwise CvLt →
      (l.foldl (fun m (ki : Klong × Nat) => match ki with
        | (k, i) => match k with
          | .key c y => if del.contains i then m else insertCv c y m
          | _ => m) m).lookup c =
      match ((kc c l).filter (fun a => !del.contains a.1)).getLast? with
      | some a => some a.2
      | none => m.lookup c
  | [], m, _ => by simp [kc]
  | (k, i) :: r, m, hm => by
    simp only [List.foldl_cons]
    cases k with
    | time t =>
      rw [lookup_liveWith del c r m hm]
      simp [kc]
    | del b =>
      rw [lookup_liveWith del c r m hm]
      simp [kc]
    | key c' y =>
      by_cases hd : del.contains i = true
      · simp only [hd, ite_true]
        rw [lookup_liveWith del c r m hm]
        by_cases hc : c' = c
        · subst hc
          have : kc c' ((Klong.key c' y, i) :: r) = (i, y) :: kc c' r := by simp [kc]
          rw [this]
          simp only [List.filter_cons, hd, Bool.not_true, Bool.false_eq_true, ite_false]
        · simp [kc, hc]
      · simp only [Bool.not_eq_true] at hd
        simp only [hd, Bool.false_eq_true, ite_false]
        rw [lookup_liveWith del c r _ (insertCv_sorted c' y hm), lookup_insertCv hm]
        by_cases hc : c' = c
        · subst hc
          have : kc c' ((Klong.key c' y, i) :: r) = (i, y) :: kc c' r := by simp [kc]
          rw [this]
          simp only [List.filter_cons, hd, Bool.not_false, ite_true, List.getLast?_cons]
          cases ((kc c' r).filter (fun a => !del.contains a.1)).getLast? <;> simp
        · have : kc c ((Klong.key c' y, i) :: r) = kc c r := by simp [kc, hc]
          rw [this]
          have hc' : ¬ c = c' := fun h => hc h.symm
          simp [hc']

theorem snoc_eq_append_cons {α : Type} {l : List α} {k : α} {l1 : List α} {a : α} {l2 : List α}
    (h : l ++ [k] = l1 ++ a :: l2) :
    (l2 = [] ∧ l = l1 ∧ k = a) ∨ ∃ l2', l2 = l2' ++ [k] ∧ l = l1 ++ a :: l2' := by
  rcases List.eq_nil_or_concat l2 with rfl | ⟨l2', x, rfl⟩
  · have := List.append_inj' h rfl
    exact Or.inl ⟨rfl, this.1, by simpa using this.2⟩
  · rw [List.concat_eq_append] at h ⊢
    have h' : l ++ [k] = (l1 ++ a :: l2') ++ [x] := by rw [h]; simp
    have := List.append_inj' h' rfl
    have hx : k = x := by simpa using this.2
    exact Or.inr ⟨l2', by rw [hx], this.1⟩

/-- What the check of the bitmaps computes: every bitmap of the list meets
`bitmapOk` with the bitmap before it. -/
theorem bmFold_spec (ks : List Klong) (l : List Klong) :
    (l.zipIdx.foldl (fun acc ki => bmStep ks acc ki.1 ki.2) (true, [])).2 = lastBitmap l ∧
    ((l.zipIdx.foldl (fun acc ki => bmStep ks acc ki.1 ki.2) (true, [])).1 = true →
      ∀ l1 b l2, l = l1 ++ Klong.del b :: l2 →
        bitmapOk ks l1.length (lastBitmap l1) b = true) := by
  induction l using List.reverseRecOn with
  | nil =>
    refine ⟨rfl, ?_⟩
    intro _ l1 b l2 he
    simp at he
  | append_singleton l k ih =>
    rw [foldl_zipIdx_snoc, lastBitmap_snoc]
    obtain ⟨ih1, ih2⟩ := ih
    cases k with
    | time t =>
      refine ⟨ih1, ?_⟩
      intro hok l1 b l2 he
      rcases snoc_eq_append_cons he with ⟨_, _, h3⟩ | ⟨l2', _, h2⟩
      · simp at h3
      · exact ih2 hok l1 b l2' h2
    | key c y =>
      refine ⟨ih1, ?_⟩
      intro hok l1 b l2 he
      rcases snoc_eq_append_cons he with ⟨_, _, h3⟩ | ⟨l2', _, h2⟩
      · simp at h3
      · exact ih2 hok l1 b l2' h2
    | del bits =>
      refine ⟨rfl, ?_⟩
      intro hok l1 b l2 he
      simp only [bmStep, Bool.and_eq_true] at hok
      rcases snoc_eq_append_cons he with ⟨_, h2, h3⟩ | ⟨l2', _, h2⟩
      · injection h3 with h3
        subst h2 h3
        rw [← ih1]
        exact hok.2
      · exact ih2 hok.1 l1 b l2' h2

theorem bitmapOk_iff {ks : List Klong} {i : Nat} {before bits : List Nat}
    (h : bitmapOk ks i before bits = true) :
    (∀ j ∈ bits, j < i) ∧ (∀ j ∈ before, j ∈ bits) ∧
    (∀ j ∈ bits, ∀ j', j' < j → cvAt ks j' = cvAt ks j → j' ∈ bits) := by
  simp only [bitmapOk, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, List.mem_range,
    Bool.or_eq_true, bne_iff_ne, ne_eq, List.contains_iff_mem] at h
  refine ⟨fun j hj => (h.1.1 j hj).1, h.1.2, ?_⟩
  intro j hj j' hlt heq
  rcases h.2 j hj j' hlt with h1 | h1
  · exact absurd heq h1
  · exact h1

theorem mem_kc {c : Nat} {l : List Klong} {j : Nat} {y : NodeId} (h : (j, y) ∈ kc c l.zipIdx) :
    cvAt l j = some c := by
  simp only [kc, List.mem_filterMap, Prod.exists] at h
  obtain ⟨k, i, hm, hk⟩ := h
  have hi := List.mem_zipIdx_iff_getElem?.mp hm
  cases k with
  | key c' y' =>
    by_cases hc : c' = c
    · simp only [hc, ite_true, Option.some.injEq, Prod.mk.injEq] at hk
      obtain ⟨rfl, rfl⟩ := hk
      simp only at hi
      simp [cvAt, hi, hc]
    · simp [hc] at hk
  | time t => simp at hk
  | del b => simp at hk

theorem zipIdx_sorted {α : Type} (l : List α) (k : Nat) :
    (l.zipIdx k).Pairwise (fun a b => a.2 < b.2) := by
  induction l generalizing k with
  | nil => simp
  | cons a r ih =>
    simp only [List.zipIdx_cons, List.pairwise_cons]
    refine ⟨?_, ih _⟩
    intro b hb
    have := List.le_snd_of_mem_zipIdx hb
    omega

theorem kc_sorted (c : Nat) (l : List Klong) :
    (kc c l.zipIdx).Pairwise (fun a b => a.1 < b.1) := by
  unfold kc
  refine List.Pairwise.filterMap _ ?_ (zipIdx_sorted l 0)
  rintro ⟨k, i⟩ ⟨k', i'⟩ hlt b hb b' hb'
  cases k with
  | key c1 y1 =>
    cases k' with
    | key c2 y2 =>
      by_cases h1 : c1 = c <;> by_cases h2 : c2 = c <;> simp [h1, h2] at hb hb'
      rw [← hb, ← hb']
      exact hlt
    | time t => simp at hb'
    | del d => simp at hb'
  | time t => simp at hb
  | del d => simp at hb

/-- The last of the klongs that p keeps: the last klong, if p keeps it, when p
drops every klong before one that it drops. -/
theorem filter_getLast_comm {l : List (Nat × NodeId)} {p : Nat × NodeId → Bool}
    (hs : l.Pairwise (fun a b => a.1 < b.1))
    (hp : ∀ a ∈ l, p a = false → ∀ a' ∈ l, a'.1 < a.1 → p a' = false) :
    l.getLast?.filter p = (l.filter p).getLast? := by
  rcases List.eq_nil_or_concat l with rfl | ⟨A, a, rfl⟩
  · rfl
  · rw [List.concat_eq_append] at hs hp ⊢
    rw [List.getLast?_concat, List.filter_append]
    rw [List.pairwise_append] at hs
    by_cases ha : p a = true
    · simp [Option.filter, ha]
    · simp only [Bool.not_eq_true] at ha
      have hA : A.filter p = [] := by
        rw [List.filter_eq_nil_iff]
        intro a' ha'
        have := hp a (by simp) ha a' (by simp [ha']) (hs.2.2 a' ha' a (by simp))
        simp [this]
      simp [Option.filter, ha, hA]

/-- `searchEq` is a lookup in the live klongs of a well-formed node. -/
theorem searchEq_spec (ks : List Klong) (h : klongsWf ks = true) (c : Nat) :
    searchEq ks c = (live ks).lookup c := by
  simp only [klongsWf, Bool.and_eq_true] at h
  have hb := (bmFold_spec ks ks).2 h.2
  have hw : BmW ks := by
    intro l1 b l2 he
    have := bitmapOk_iff (hb l1 b l2 he)
    exact ⟨this.1, this.2.1⟩
  have h4 : ∀ a ∈ kc c ks.zipIdx, (!(lastBitmap ks).contains a.1) = false →
      ∀ a' ∈ kc c ks.zipIdx, a'.1 < a.1 → (!(lastBitmap ks).contains a'.1) = false := by
    rintro ⟨j, y⟩ ha hd ⟨j', y'⟩ ha' hlt
    simp only [Bool.not_eq_false', List.contains_iff_mem] at hd ⊢
    rcases lastBitmap_cases ks with h0 | ⟨l1, b, l2, he, hlb⟩
    · rw [h0] at hd; simp at hd
    · rw [hlb] at hd ⊢
      have := (bitmapOk_iff (hb l1 b l2 he)).2.2 j hd j' hlt
      exact this (by rw [mem_kc ha, mem_kc ha'])
  have h1 : (live ks).lookup c =
      match ((kc c ks.zipIdx).filter (fun a => !(lastBitmap ks).contains a.1)).getLast? with
      | some a => some a.2
      | none => none :=
    lookup_liveWith (lastBitmap ks) c ks.zipIdx [] List.Pairwise.nil
  rw [h1]
  unfold searchEq
  rw [eqFold_spec c ks hw]
  simp only
  rw [filter_getLast_comm (kc_sorted c ks) h4]
  cases ((kc c ks.zipIdx).filter (fun a => !(lastBitmap ks).contains a.1)).getLast? <;> rfl

theorem searchLte_spec (ks : List Klong) (p : Pos) :
    searchLte ks p = ((live ks).filter (fun cy => !p.below cy.1)).getLast? :=
  Best.unique (fun _ _ h1 h2 => le_antisymm h1 h2) (live_sorted ks)
    (searchBy_best (le := (· ≤ ·)) le_refl (fun _ _ _ => le_trans) le_total _ ks)
    (best_getLast? (live_sorted ks))

theorem searchLt_spec (ks : List Klong) (p : Pos) :
    searchLt ks p = ((live ks).filter (fun cy => p.above cy.1)).getLast? :=
  Best.unique (fun _ _ h1 h2 => le_antisymm h1 h2) (live_sorted ks)
    (searchBy_best (le := (· ≤ ·)) le_refl (fun _ _ _ => le_trans) le_total _ ks)
    (best_getLast? (live_sorted ks))

theorem searchGt_spec (ks : List Klong) (p : Pos) :
    searchGt ks p = ((live ks).filter (fun cy => p.below cy.1)).head? :=
  Best.unique (fun _ _ h1 h2 => le_antisymm h2 h1) (live_sorted ks)
    (searchBy_best (le := (· ≥ ·)) le_refl (fun _ _ _ h1 h2 => le_trans h2 h1)
      (fun a b => le_total b a) _ ks)
    (best_head? (live_sorted ks))

theorem searchGte_spec (ks : List Klong) (p : Pos) :
    searchGte ks p = ((live ks).filter (fun cy => !p.above cy.1)).head? :=
  Best.unique (fun _ _ h1 h2 => le_antisymm h2 h1) (live_sorted ks)
    (searchBy_best (le := (· ≥ ·)) le_refl (fun _ _ _ h1 h2 => le_trans h2 h1)
      (fun a b => le_total b a) _ ks)
    (best_head? (live_sorted ks))

theorem searchLte_best (ks : List Klong) (p : Pos) :
    Best (· ≤ ·) (fun c => !p.below c) (live ks) (searchLte ks p) :=
  searchBy_best (le := (· ≤ ·)) le_refl (fun _ _ _ => le_trans) le_total _ ks

theorem searchLt_best (ks : List Klong) (p : Pos) :
    Best (· ≤ ·) (fun c => p.above c) (live ks) (searchLt ks p) :=
  searchBy_best (le := (· ≤ ·)) le_refl (fun _ _ _ => le_trans) le_total _ ks

theorem searchGt_best (ks : List Klong) (p : Pos) :
    Best (· ≥ ·) (fun c => p.below c) (live ks) (searchGt ks p) :=
  searchBy_best (le := (· ≥ ·)) le_refl (fun _ _ _ h1 h2 => le_trans h2 h1)
    (fun a b => le_total b a) _ ks

theorem searchGte_best (ks : List Klong) (p : Pos) :
    Best (· ≥ ·) (fun c => !p.above c) (live ks) (searchGte ks p) :=
  searchBy_best (le := (· ≥ ·)) le_refl (fun _ _ _ h1 h2 => le_trans h2 h1)
    (fun a b => le_total b a) _ ks

end Contract
