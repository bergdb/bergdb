/-
The contract package (bergdb 030-10): more of the node algebra of the model's
writer, for its splits. What the writer's `addKeys` (`addAll`),
`KNode.toPrev` and `halves` (the two halves of a space split) do to a key node
as the contract sees it: its live klongs, its well-formedness, its size, its
times and its key klongs. And the arithmetic of the levels
(`Params.keyLevel`, `heightOf`, `segOf`).
-/
import Contract.Proof.WriterState
import Contract.Proof.WriterRun

namespace Contract

/-! ## 1. Key klongs added (`addAll`) -/

theorem ksOf_length (n : MNode) : (ksOf n).length = n.size := List.length_map _

theorem firstTime_eq {n : MNode} {t0 : Time} {rest : List MKlong}
    (h : n.ks = .time t0 :: rest) : n.firstTime = some t0 := by
  simp [SIS.Tree.KNode.firstTime, h]

theorem foldl_count {α : Type} : ∀ (L : List α) (k : Nat),
    L.foldl (fun n _ => n + 1) k = k + L.length
  | [], _ => rfl
  | _ :: L, k => by
    rw [List.foldl_cons, foldl_count L, List.length_cons]
    omega

theorem liveWith_length (d : List Nat) (L : List (Klong × Nat)) :
    (liveWith d L).length ≤ L.length := by
  have h := foldl_sim (fun m (ki : Klong × Nat) => match ki with
      | (k, i) => match k with
        | .key c y => if d.contains i then m else insertCv c y m
        | _ => m) (fun n _ => n + 1) (fun (m : List (Nat × NodeId)) n => m.length ≤ n) ?_ L [] 0
    (by simp)
  · rw [foldl_count, Nat.zero_add] at h
    exact h
  · rintro m n ⟨k, i⟩ hm
    cases k with
    | key c y =>
      dsimp only
      split
      · omega
      · have := length_insertCv c y m
        omega
    | time t => dsimp only; omega
    | del b => dsimp only; omega

/-- The live klongs of klongs that start with a time klong: fewer than the
klongs. -/
theorem live_length_le {ks : List Klong} (h : ∃ t rest, ks = Klong.time t :: rest) :
    (live ks).length + 1 ≤ ks.length := by
  obtain ⟨t, rest, rfl⟩ := h
  have h1 : live (Klong.time t :: rest) =
      liveWith (lastBitmap (Klong.time t :: rest)) (rest.zipIdx 1) := rfl
  rw [h1]
  have := liveWith_length (lastBitmap (Klong.time t :: rest)) (rest.zipIdx 1)
  simp only [List.length_zipIdx] at this
  simp only [List.length_cons]
  omega

theorem addAll_nil (i : Time) (n : MNode) : addAll i n [] = n := rfl

theorem addAll_cons (i : Time) (n : MNode) (cy : Nat × NodeId) (ins : List (Nat × NodeId)) :
    addAll i n (cy :: ins) = addAll i (n.add i (.key cy.1 cy.2)) ins := rfl

theorem addAll_live {i : Time} {n : MNode} (hwf : klongsWf (ksOf n) = true)
    (ins : List (Nat × NodeId)) :
    live (ksOf (addAll i n ins)) =
      ins.foldl (fun m cy => insertCv cy.1 cy.2 m) (live (ksOf n)) := by
  induction ins generalizing n with
  | nil => rfl
  | cons cy ins ih =>
    rw [addAll_cons, ih (add_key_wf hwf _ _), add_key_live hwf]
    rfl

theorem addAll_wf {i : Time} {n : MNode} (hwf : klongsWf (ksOf n) = true)
    (ins : List (Nat × NodeId)) : klongsWf (ksOf (addAll i n ins)) = true := by
  induction ins generalizing n with
  | nil => exact hwf
  | cons cy ins ih => exact ih (add_key_wf hwf _ _)

theorem addAll_leaf (i : Time) (n : MNode) (ins : List (Nat × NodeId)) :
    (addAll i n ins).leaf = n.leaf := by
  induction ins generalizing n with
  | nil => rfl
  | cons cy ins ih => rw [addAll_cons, ih, add_leaf]

theorem lastT_append_time (ks : List Klong) (t : Time) (k : Klong) (hk : ∀ t', k ≠ .time t') :
    lastT (ks ++ [.time t, k]) = some t := by
  unfold lastT
  rw [List.foldl_append]
  cases k with
  | time t' => exact absurd rfl (hk t')
  | key c y => rfl
  | del b => rfl

theorem lastT_append_key (ks : List Klong) (c : Nat) (y : NodeId) :
    lastT (ks ++ [.key c y]) = lastT ks := by
  unfold lastT
  rw [List.foldl_append]
  rfl

/-- After `add` of a key klong at time i, the last time is at least i. -/
theorem add_lastTime (n : MNode) (i : Time) (c : Nat) (y : NodeId) :
    ∃ lt, (n.add i (.key c y)).lastTime = some lt ∧ i ≤ lt := by
  rcases ksOf_add n i (.key c y) with ⟨h, _⟩ | ⟨h, lt, hl, hle⟩
  · refine ⟨i, ?_, Nat.le_refl _⟩
    rw [← lastT_ksOf, h]
    exact lastT_append_time _ _ _ (by simp [kOf])
  · refine ⟨lt, ?_, hle⟩
    rw [← lastT_ksOf, h, ← hl, ← lastT_ksOf]
    exact lastT_append_key _ _ _

theorem addAll_size_late {i : Time} (ins : List (Nat × NodeId)) : ∀ (n : MNode),
    (∃ lt, n.lastTime = some lt ∧ i ≤ lt) → (addAll i n ins).size ≤ n.size + ins.length := by
  induction ins with
  | nil => intro n _; simp [addAll_nil]
  | cons cy ins ih =>
    intro n ⟨lt, hl, hle⟩
    rw [addAll_cons]
    have h1 := ih _ (add_lastTime n i cy.1 cy.2)
    have h2 : (n.add i (.key cy.1 cy.2)).size = n.size + 1 := by
      rcases add_ks n i (.key cy.1 cy.2) with ⟨_, h⟩ | ⟨h, _⟩
      · exact absurd (h lt hl) (Nat.not_lt.mpr hle)
      · unfold SIS.Tree.KNode.size
        rw [h, List.length_append, List.length_singleton]
    rw [h2] at h1
    simp only [List.length_cons]
    omega

/-- `addAll` adds at most one time klong. -/
theorem addAll_size (i : Time) (n : MNode) (ins : List (Nat × NodeId)) :
    (addAll i n ins).size ≤ n.size + ins.length + 1 := by
  cases ins with
  | nil => simp [addAll_nil]
  | cons cy ins =>
    rw [addAll_cons]
    have h1 := addAll_size_late ins _ (add_lastTime n i cy.1 cy.2)
    have h2 := add_size n i (.key cy.1 cy.2)
    simp only [List.length_cons]
    omega

theorem addAll_timesLe {i : Time} {n : MNode} (ht : TimesLe n i) (ins : List (Nat × NodeId)) :
    TimesLe (addAll i n ins) i := by
  induction ins generalizing n with
  | nil => exact ht
  | cons cy ins ih => exact ih (add_timesLe ht _ (fun t' h => by cases h))

theorem addAll_first {i t0 : Time} {n : MNode} {rest : List MKlong}
    (h : n.ks = .time t0 :: rest) (ins : List (Nat × NodeId)) :
    ∃ rest', (addAll i n ins).ks = .time t0 :: rest' := by
  induction ins generalizing n rest with
  | nil => exact ⟨rest, h⟩
  | cons cy ins ih =>
    obtain ⟨rest1, h1⟩ := add_first (t := i) (.key cy.1 cy.2) h
    exact ih h1

theorem addAll_firstTime {i t0 : Time} {n : MNode} {rest : List MKlong}
    (h : n.ks = .time t0 :: rest) (ins : List (Nat × NodeId)) :
    (addAll i n ins).firstTime = n.firstTime := by
  obtain ⟨rest', h'⟩ := addAll_first (i := i) h ins
  rw [firstTime_eq h', firstTime_eq h]

/-- The key klongs after `addAll`: those before, and those added. -/
theorem addAll_key_mem {i : Time} {c' : Nat} {y' : NodeId} (ins : List (Nat × NodeId)) :
    ∀ n : MNode, Klong.key c' y' ∈ ksOf (addAll i n ins) ↔
      Klong.key c' y' ∈ ksOf n ∨ (c', y') ∈ ins := by
  induction ins with
  | nil => intro n; simp [addAll_nil]
  | cons cy ins ih =>
    intro n
    rw [addAll_cons, ih, add_key_mem, List.mem_cons]
    constructor
    · rintro ((h | ⟨rfl, rfl⟩) | h)
      · exact Or.inl h
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr h)
    · rintro (h | rfl | h)
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr ⟨rfl, rfl⟩)
      · exact Or.inr h

/-- The frame of `addAll` (`add_ext`'s form). -/
theorem addAll_ext {n : MNode} {i : Time} {ks0 : List Klong}
    (h0 : ∀ t, Klong.time t ∈ ks0 → t < i)
    (h : ksOf n = ks0 ∨ ∃ more, ksOf n = ks0 ++ Klong.time i :: more)
    (ins : List (Nat × NodeId)) :
    ksOf (addAll i n ins) = ks0 ∨ ∃ more, ksOf (addAll i n ins) = ks0 ++ Klong.time i :: more := by
  induction ins generalizing n with
  | nil => exact h
  | cons cy ins ih => exact ih (add_ext h0 h _)

/-! ## 2. The node before the transaction (`KNode.toPrev`) -/

theorem ksOf_toPrev (n : MNode) (t : Time) : ksOf (n.toPrev t) = prefixAt (ksOf n) t := by
  show (SIS.Tree.prefixAt n.ks t).map kOf = prefixAt (n.ks.map kOf) t
  unfold SIS.Tree.prefixAt prefixAt
  rw [List.takeWhile_map]
  congr 2
  funext k
  cases k <;> rfl

theorem toPrev_leaf (n : MNode) (t : Time) : (n.toPrev t).leaf = n.leaf := rfl

/-- A node that is its klongs ks0 of before the transaction at time i, or
those and then a time klong of i and more, is ks0 at time i - 1. -/
theorem toPrev_ext {n : MNode} {i : Time} {ks0 : List Klong}
    (h0 : ∀ t, Klong.time t ∈ ks0 → t < i) (hf : ∃ t0 rest, ks0 = Klong.time t0 :: rest)
    (h : ksOf n = ks0 ∨ ∃ more, ksOf n = ks0 ++ Klong.time i :: more) :
    ksOf (n.toPrev (i - 1)) = ks0 := by
  obtain ⟨t0, rest, hks0⟩ := hf
  have hi : i ≠ 0 := by
    intro h1
    have := h0 t0 (by rw [hks0]; exact List.mem_cons_self)
    rw [h1] at this
    exact Nat.not_lt_zero _ this
  have hall : prefixAt ks0 (i - 1) = ks0 :=
    prefixAt_all (fun t' ht' => Nat.le_sub_one_of_lt (h0 t' ht'))
  rw [ksOf_toPrev]
  rcases h with h | ⟨more, h⟩
  · rw [h, hall]
  · rw [h, prefixAt_ext _ _ _ _ (Nat.sub_one_lt hi), hall]

/-! ## 3. The two halves of a space split (`halves`) -/

theorem insertCv_append_low {c : Nat} {y : NodeId} {B : List (Nat × NodeId)}
    (hB : ∀ b ∈ B, c < b.1) : ∀ A : List (Nat × NodeId),
    insertCv c y (A ++ B) = insertCv c y A ++ B
  | [] => by
    cases B with
    | nil => rfl
    | cons b B' =>
      obtain ⟨c', y'⟩ := b
      have := hB (c', y') List.mem_cons_self
      simp only at this
      simp [insertCv, this]
  | (c', y') :: A => by
    simp only [List.cons_append]
    unfold insertCv
    split
    · rfl
    · split
      · rfl
      · rw [insertCv_append_low hB A]
        rfl

theorem insertCv_append_high {c : Nat} {y : NodeId} {B : List (Nat × NodeId)} :
    ∀ {A : List (Nat × NodeId)}, (∀ a ∈ A, a.1 < c) →
    insertCv c y (A ++ B) = A ++ insertCv c y B
  | [], _ => rfl
  | (c', y') :: A, hA => by
    have h1 := hA (c', y') List.mem_cons_self
    simp only at h1
    have e : ∀ X : List (Nat × NodeId), insertCv c y ((c', y') :: X) = (c', y') :: insertCv c y X :=
      fun X => by simp [insertCv, show ¬ c < c' by omega, show c ≠ c' by omega]
    rw [List.cons_append, e, insertCv_append_high (fun a ha => hA a (List.mem_cons_of_mem _ ha))]
    rfl

theorem foldl_insertCv_low {B : List (Nat × NodeId)} : ∀ (ins A : List (Nat × NodeId)),
    (∀ cy ∈ ins, ∀ b ∈ B, cy.1 < b.1) →
    ins.foldl (fun m cy => insertCv cy.1 cy.2 m) (A ++ B) =
      ins.foldl (fun m cy => insertCv cy.1 cy.2 m) A ++ B
  | [], _, _ => rfl
  | cy :: ins, A, h => by
    simp only [List.foldl_cons]
    rw [insertCv_append_low (h cy List.mem_cons_self) A]
    exact foldl_insertCv_low ins _ (fun cy' hc => h cy' (List.mem_cons_of_mem _ hc))

theorem foldl_insertCv_high {A : List (Nat × NodeId)} : ∀ (ins B : List (Nat × NodeId)),
    (∀ a ∈ A, ∀ cy ∈ ins, a.1 < cy.1) →
    ins.foldl (fun m cy => insertCv cy.1 cy.2 m) (A ++ B) =
      A ++ ins.foldl (fun m cy => insertCv cy.1 cy.2 m) B
  | [], _, _ => rfl
  | cy :: ins, B, h => by
    simp only [List.foldl_cons]
    rw [insertCv_append_high (fun a ha => h a ha cy List.mem_cons_self)]
    exact foldl_insertCv_high ins _ (fun a ha cy' hc => h a ha cy' (List.mem_cons_of_mem _ hc))

theorem insertCv_ne_nil (c : Nat) (y : NodeId) : ∀ m : List (Nat × NodeId), insertCv c y m ≠ []
  | [] => by simp [insertCv]
  | (c', y') :: r => by
    unfold insertCv
    split
    · simp
    · split <;> simp

theorem foldl_insertCv_ne_nil : ∀ (ins m : List (Nat × NodeId)), m ≠ [] →
    ins.foldl (fun m cy => insertCv cy.1 cy.2 m) m ≠ []
  | [], _, h => h
  | cy :: ins, m, _ => foldl_insertCv_ne_nil ins _ (insertCv_ne_nil cy.1 cy.2 m)

/-- A list in order is its own fold of `insertCv`. -/
theorem foldl_insertCv_self {A : List (Nat × NodeId)} (hA : A.Pairwise CvLt) :
    A.foldl (fun m cy => insertCv cy.1 cy.2 m) [] = A := by
  rw [← live_keys 0 A]
  exact live_version hA 0

/-- Klongs at or above sc set in a list that starts with sc: the list starts
with sc after; and the same with the first compare value 0, and the klongs of
sc given 0 (an inner node's second half). -/
theorem foldl_insertCv_shift (sc : Nat) : ∀ (ins : List (Nat × NodeId)) (y0 : NodeId)
    (R : List (Nat × NodeId)), (∀ cy ∈ ins, sc ≤ cy.1) → (∀ b ∈ R, sc < b.1) →
    ∃ y1 R', ins.foldl (fun m cy => insertCv cy.1 cy.2 m) ((sc, y0) :: R) = (sc, y1) :: R' ∧
      (ins.map (fun cy : Nat × NodeId => if cy.1 = sc then ((0 : Nat), cy.2) else cy)).foldl
        (fun m cy => insertCv cy.1 cy.2 m) ((0, y0) :: R) = (0, y1) :: R' ∧
      ∀ b ∈ R', sc < b.1
  | [], y0, R, _, hR => ⟨y0, R, rfl, rfl, hR⟩
  | (c, y) :: ins, y0, R, hi, hR => by
    have hc : sc ≤ c := hi (c, y) List.mem_cons_self
    have hi' := fun cy hcy => hi cy (List.mem_cons_of_mem _ hcy)
    simp only [List.map_cons, List.foldl_cons]
    by_cases he : c = sc
    · subst he
      have h1 : insertCv c y ((c, y0) :: R) = (c, y) :: R := by simp [insertCv]
      have h2 : insertCv 0 y ((0, y0) :: R) = (0, y) :: R := by simp [insertCv]
      simp only [ite_true, h1, h2]
      exact foldl_insertCv_shift c ins y R hi' hR
    · have hlt : sc < c := by omega
      have h1 : insertCv c y ((sc, y0) :: R) = (sc, y0) :: insertCv c y R := by
        simp [insertCv, Nat.not_lt.mpr hc, he]
      have h2 : insertCv c y ((0, y0) :: R) = (0, y0) :: insertCv c y R := by
        simp [insertCv, show c ≠ 0 by omega]
      simp only [he, ite_false, h1, h2]
      refine foldl_insertCv_shift sc ins y0 _ hi' ?_
      intro b hb
      rcases mem_insertCv hb with rfl | hb
      · exact hlt
      · exact hR b hb

/-- A node of a time klong and key klongs: what the contract sees of it. -/
theorem keys_node_facts {m : MNode} {t : Time} {X : List (Nat × NodeId)}
    (h : m.ks = .time t :: X.map (fun p => SIS.Tree.Klong.key p.1 p.2)) :
    klongsWf (ksOf m) = true ∧ (∃ rest, m.ks = .time t :: rest) ∧
      (∀ t', Klong.time t' ∈ ksOf m → t' = t) ∧ m.size = 1 + X.length ∧
      (∀ c y, Klong.key c y ∈ ksOf m → (c, y) ∈ X) ∧
      live (ksOf m) = X.foldl (fun m cy => insertCv cy.1 cy.2 m) [] := by
  have hk := ksOf_keys h
  refine ⟨by rw [hk]; exact klongsWf_version _ _, ⟨_, h⟩, ?_, ?_, ?_,
    by rw [hk]; exact live_keys _ _⟩
  · intro t' ht'
    rw [hk] at ht'
    simpa using ht'
  · show m.ks.length = _
    rw [h, List.length_cons, List.length_map]
    omega
  · intro c y hc
    rw [hk] at hc
    simpa using hc

/-- `halves leaf t last ins` (a space split) on a last version of time t with
two live klongs or more, l, and klongs `ins` that all go to one half: all below
the compare value sc of klong `l.length / 2` of l, or all at or above it. The
first half holds the live klongs L1 below sc of l with ins set, the second
those from sc on, its first compare value 0 in an inner node; the parent gets
sc. Both halves are well formed, of kind `leaf`, start with a time klong of t
and have no other time; their sizes; their key klongs name nodes that klongs
of l or ins name. -/
theorem halves_spec (leaf : Bool) (t : Time) {last : MNode} {l : List (Nat × NodeId)}
    (hs : l.Pairwise CvLt) (hl : ksOf last = .time t :: l.map (fun cy => Klong.key cy.1 cy.2))
    (h2 : 2 ≤ l.length) {sc : Nat} (hsc : ∃ y, l[l.length / 2]? = some (sc, y))
    (ins : List (Nat × NodeId)) (hins : (∀ cy ∈ ins, cy.1 < sc) ∨ (∀ cy ∈ ins, sc ≤ cy.1))
    {f s2 : MNode} {c : Nat} (hh : SIS.Tree.halves leaf t last ins = (f, s2, c)) :
    c = sc ∧ f.leaf = leaf ∧ s2.leaf = leaf ∧
    ∃ L1 y0 rest, ins.foldl (fun m cy => insertCv cy.1 cy.2 m) l = L1 ++ (sc, y0) :: rest ∧
      L1 ≠ [] ∧ (∀ a ∈ L1, a.1 < sc) ∧ (∀ b ∈ rest, sc < b.1) ∧
      live (ksOf f) = L1 ∧ live (ksOf s2) = (if leaf then sc else 0, y0) :: rest ∧
      klongsWf (ksOf f) = true ∧ klongsWf (ksOf s2) = true ∧
      (∃ rest1, f.ks = .time t :: rest1) ∧ (∃ rest2, s2.ks = .time t :: rest2) ∧
      (∀ t', Klong.time t' ∈ ksOf f → t' = t) ∧ (∀ t', Klong.time t' ∈ ksOf s2 → t' = t) ∧
      f.size ≤ 1 + l.length / 2 + ins.length ∧
      s2.size ≤ 1 + (l.length - l.length / 2) + ins.length ∧
      (∀ c' y', Klong.key c' y' ∈ ksOf f → y' ∈ l.map (·.2) ∨ y' ∈ ins.map (·.2)) ∧
      (∀ c' y', Klong.key c' y' ∈ ksOf s2 → y' ∈ l.map (·.2) ∨ y' ∈ ins.map (·.2)) := by
  obtain ⟨y, hy⟩ := hsc
  have hk : l.length / 2 < l.length := by omega
  have hlk : l[l.length / 2] = (sc, y) := by
    rw [List.getElem?_eq_getElem hk] at hy
    exact Option.some.inj hy
  have hsplit : l = l.take (l.length / 2) ++ (sc, y) :: l.drop (l.length / 2 + 1) := by
    conv_lhs => rw [← List.take_append_drop (l.length / 2) l]
    rw [List.drop_eq_getElem_cons hk, hlk]
  have hAlen : (l.take (l.length / 2)).length = l.length / 2 := by
    rw [List.length_take]
    omega
  have hlast : last.ks = .time t :: l.map (fun p => SIS.Tree.Klong.key p.1 p.2) := by
    apply List.map_injective_iff.mpr kOf_injective
    rw [show last.ks.map kOf = ksOf last from rfl, hl]
    simp [kOf]
  generalize l.take (l.length / 2) = A at hsplit hAlen
  generalize l.drop (l.length / 2 + 1) = R at hsplit
  subst hsplit
  clear hy hlk hl hk
  rw [List.pairwise_append, List.pairwise_cons] at hs
  obtain ⟨hsA, ⟨hyR, hsR⟩, hAyR⟩ := hs
  have hAsc : ∀ a ∈ A, a.1 < sc := fun a ha => hAyR a ha _ List.mem_cons_self
  have hlen : (A ++ (sc, y) :: R).length = A.length + 1 + R.length := by simp; omega
  have hA1 : A ≠ [] := by
    apply List.ne_nil_of_length_pos
    rw [hlen] at h2 hAlen
    omega
  have hlA : (A ++ (sc, y) :: R).length / 2 = A.length := hAlen.symm
  have hmemA : ∀ p ∈ A, p.2 ∈ (A ++ (sc, y) :: R).map (·.2) :=
    fun p hp => List.mem_map_of_mem (List.mem_append_left _ hp)
  have hmemR : ∀ p ∈ R, p.2 ∈ (A ++ (sc, y) :: R).map (·.2) :=
    fun p hp => List.mem_map_of_mem (List.mem_append_right _ (List.mem_cons_of_mem _ hp))
  have hmemy : y ∈ (A ++ (sc, y) :: R).map (·.2) :=
    List.mem_map.mpr ⟨(sc, y), List.mem_append_right _ List.mem_cons_self, rfl⟩
  have hsec : ((if leaf then sc else 0, y) :: R).Pairwise CvLt := by
    rw [List.pairwise_cons]
    refine ⟨fun b hb => ?_, hsR⟩
    have : sc < b.1 := hyR b hb
    show (if leaf then sc else 0) < b.1
    cases leaf
    · simp only [Bool.false_eq_true, ite_false]
      omega
    · exact this
  unfold SIS.Tree.halves SIS.Tree.KNode.size at hh
  simp only [hlast, List.length_cons, List.length_map, Nat.add_sub_cancel,
    List.drop_one, List.tail_cons, hlA, ← List.map_take,
    ← List.map_drop, List.take_left, List.drop_left, List.map_cons, List.head?_cons] at hh
  by_cases hb : ∀ cy ∈ ins, cy.1 < sc
  · -- Below sc: ins goes to the first half.
    have hform : f.ks = .time t :: (A ++ ins).map (fun p => SIS.Tree.Klong.key p.1 p.2) ∧
        s2.ks = .time t :: ((if leaf then sc else 0, y) :: R).map
          (fun p => SIS.Tree.Klong.key p.1 p.2) ∧
        c = sc ∧ f.leaf = leaf ∧ s2.leaf = leaf := by
      cases ins with
      | nil =>
        cases leaf <;> simp at hh <;> obtain ⟨rfl, rfl, rfl⟩ := hh <;> simp
      | cons cy ins' =>
        have hc : ¬ sc ≤ cy.1 := Nat.not_le.mpr (hb cy List.mem_cons_self)
        cases leaf <;> simp [hc] at hh <;> obtain ⟨rfl, rfl, rfl⟩ := hh <;> simp
    obtain ⟨hf, hs2, rfl, hfl, hsl⟩ := hform
    obtain ⟨wf1, st1, ti1, sz1, ke1, li1⟩ := keys_node_facts hf
    obtain ⟨wf2, st2, ti2, sz2, ke2, li2⟩ := keys_node_facts hs2
    refine ⟨rfl, hfl, hsl, ins.foldl (fun m cy => insertCv cy.1 cy.2 m) A, y, R, ?_,
      foldl_insertCv_ne_nil ins A hA1, ?_, hyR, ?_, ?_, wf1, wf2, st1, st2, ti1, ti2,
      ?_, ?_, ?_, ?_⟩
    · refine foldl_insertCv_low ins A (fun cy hcy b hb' => ?_)
      have h1 := hb cy hcy
      rcases List.mem_cons.mp hb' with rfl | hb'
      · exact h1
      · exact lt_trans h1 (hyR b hb')
    · intro a ha
      rcases mem_foldl_insertCv_src ins A ha with ha | ha
      · exact hAsc a ha
      · exact hb a ha
    · rw [li1, List.foldl_append, foldl_insertCv_self hsA]
    · rw [li2, foldl_insertCv_self hsec]
    · rw [sz1, List.length_append, hlA]
      omega
    · rw [sz2, hlA, hlen, List.length_cons]
      omega
    · intro c' y' hk'
      rcases List.mem_append.mp (ke1 c' y' hk') with h1 | h1
      · exact Or.inl (hmemA _ h1)
      · exact Or.inr (List.mem_map_of_mem (f := (·.2)) h1)
    · intro c' y' hk'
      rcases List.mem_cons.mp (ke2 c' y' hk') with h1 | h1
      · rw [Prod.mk.injEq] at h1
        rw [h1.2]
        exact Or.inl hmemy
      · exact Or.inl (hmemR _ h1)
  · -- At or above sc: ins goes to the second half.
    have hhi := hins.resolve_left hb
    obtain ⟨cy, ins', rfl⟩ : ∃ cy ins', ins = cy :: ins' := by
      cases ins with
      | nil => exact absurd (fun _ h => absurd h List.not_mem_nil) hb
      | cons cy ins' => exact ⟨cy, ins', rfl⟩
    have hc : sc ≤ cy.1 := hhi cy List.mem_cons_self
    let g := fun cy : Nat × NodeId => if cy.1 = sc then ((0 : Nat), cy.2) else cy
    have hform : f.ks = .time t :: A.map (fun p => SIS.Tree.Klong.key p.1 p.2) ∧
        s2.ks = .time t :: ((if leaf then sc else 0, y) :: R ++
          (if leaf then cy :: ins' else (cy :: ins').map g)).map
          (fun p => SIS.Tree.Klong.key p.1 p.2) ∧
        c = sc ∧ f.leaf = leaf ∧ s2.leaf = leaf := by
      have hg : ∀ x : Nat × NodeId, SIS.Tree.Klong.key (g x).1 (g x).2 =
          if x.1 = sc then SIS.Tree.Klong.key 0 x.2 else SIS.Tree.Klong.key x.1 x.2 := by
        intro x
        by_cases h : x.1 = sc <;> simp [g, h]
      cases leaf <;> simp [hc] at hh <;> obtain ⟨rfl, rfl, rfl⟩ := hh
      · refine ⟨rfl, ?_, rfl, rfl, rfl⟩
        simp only [Bool.false_eq_true, ite_false, List.cons_append, List.map_cons, List.map_append,
          List.map_map, Function.comp_def, hg]
      · simp
    obtain ⟨hf, hs2, rfl, hfl, hsl⟩ := hform
    obtain ⟨y1, R', hL1, hL2, hR'⟩ := foldl_insertCv_shift c (cy :: ins') y R hhi hyR
    obtain ⟨wf1, st1, ti1, sz1, ke1, li1⟩ := keys_node_facts hf
    obtain ⟨wf2, st2, ti2, sz2, ke2, li2⟩ := keys_node_facts hs2
    refine ⟨rfl, hfl, hsl, A, y1, R', ?_, hA1, hAsc, hR', ?_, ?_, wf1, wf2, st1, st2, ti1, ti2,
      ?_, ?_, ?_, ?_⟩
    · rw [foldl_insertCv_high _ _
        (fun a ha cy' hcy' => lt_of_lt_of_le (hAsc a ha) (hhi cy' hcy')), hL1]
    · rw [li1, foldl_insertCv_self hsA]
    · rw [li2, List.foldl_append, foldl_insertCv_self hsec]
      cases leaf
      · exact hL2
      · exact hL1
    · rw [sz1, hlA]
      omega
    · rw [sz2, hlA, hlen]
      cases leaf <;> simp <;> omega
    · intro c' y' hk'
      exact Or.inl (hmemA _ (ke1 c' y' hk'))
    · intro c' y' hk'
      rcases List.mem_append.mp (ke2 c' y' hk') with h1 | h1
      · rcases List.mem_cons.mp h1 with h1 | h1
        · rw [Prod.mk.injEq] at h1
          rw [h1.2]
          exact Or.inl hmemy
        · exact Or.inl (hmemR _ h1)
      · cases leaf
        · obtain ⟨x, hx, hgx⟩ := List.mem_map.mp h1
          refine Or.inr (List.mem_map.mpr ⟨x, hx, ?_⟩)
          have : (g x).2 = x.2 := by by_cases h : x.1 = c <;> simp [g, h]
          rw [← this, hgx]
        · exact Or.inr (List.mem_map_of_mem (f := (·.2)) h1)

/-! ## 4. The levels -/

theorem keyLevel_succ (p : MParams) (g h : Nat) : p.keyLevel g (h + 1) = p.keyLevel g h + 1 := by
  unfold SIS.Tree.Params.keyLevel
  omega

theorem keyLevel_pos (p : MParams) (g h : Nat) : 0 < p.keyLevel g h := by
  unfold SIS.Tree.Params.keyLevel
  omega

theorem heightOf_keyLevel (p : MParams) {g h : Nat} (hh : h ≤ p.H) :
    p.heightOf (p.keyLevel g h) = h := by
  unfold SIS.Tree.Params.heightOf SIS.Tree.Params.keyLevel
  rw [show 1 + (p.G - g) * (p.H + 1) + h - 1 = (p.H + 1) * (p.G - g) + h by
    rw [Nat.mul_comm]; omega]
  rw [Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]

theorem segOf_keyLevel (p : MParams) {g h : Nat} (hg : g ≤ p.G) (hh : h ≤ p.H) :
    p.segOf (p.keyLevel g h) = g := by
  unfold SIS.Tree.Params.segOf SIS.Tree.Params.keyLevel
  rw [show 1 + (p.G - g) * (p.H + 1) + h - 1 = (p.H + 1) * (p.G - g) + h by
    rw [Nat.mul_comm]; omega]
  rw [Nat.mul_add_div (by omega), Nat.div_eq_of_lt (by omega)]
  omega

theorem keyLevel_le (p : MParams) (g : Nat) {h : Nat} (hh : h ≤ p.H) :
    p.keyLevel g h ≤ p.keyMax := by
  unfold SIS.Tree.Params.keyLevel SIS.Tree.Params.keyMax
  have := Nat.mul_le_mul_right (p.H + 1) (Nat.sub_le p.G g)
  omega

theorem segOf_le (p : MParams) (l : Nat) : p.segOf l ≤ p.G := Nat.sub_le _ _

theorem heightOf_le (p : MParams) (l : Nat) : p.heightOf l ≤ p.H := by
  unfold SIS.Tree.Params.heightOf
  have : (l - 1) % (p.H + 1) < p.H + 1 := Nat.mod_lt _ (by omega)
  omega

theorem keyLevel_segOf (p : MParams) {l : Nat} (hl : 0 < l) (hm : l ≤ p.keyMax) :
    p.keyLevel (p.segOf l) (p.heightOf l) = l := by
  unfold SIS.Tree.Params.keyLevel SIS.Tree.Params.segOf SIS.Tree.Params.heightOf
  unfold SIS.Tree.Params.keyMax at hm
  have hdm := Nat.div_add_mod (l - 1) (p.H + 1)
  have hq : (l - 1) / (p.H + 1) ≤ p.G := by
    apply Nat.le_of_lt_succ
    rw [Nat.div_lt_iff_lt_mul (by omega)]
    have e : (p.G + 1) * (p.H + 1) = p.G * (p.H + 1) + (p.H + 1) := Nat.succ_mul _ _
    rw [Nat.succ_eq_add_one, e]
    omega
  rw [Nat.sub_sub_self hq]
  rw [Nat.mul_comm] at hdm
  omega

end Contract
