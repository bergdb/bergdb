/-
The contract package (bergdb 030-10): the node algebra of the model's writer.
What the writer's changes of one key node (`KNode.add`, `KNode.lastVersion`,
`replaceOrAdd`) do to the node as the contract sees it: its live klongs, its
well-formedness (W1 to W4), its size; and the model's searches
(`KNode.searchLte`, `KNode.searchEq`) as lookups in the live klongs.

Section 1 is about the contract's klongs alone; section 2 about a node of the
model, seen through `ksOf` (its klongs as the contract's).
-/
import Contract.Writer
import Contract.Proof.Node

namespace Contract

/-! ## 1. The contract's klongs -/

theorem live_append_time (ks : List Klong) (t : Time) : live (ks ++ [.time t]) = live ks := by
  unfold live liveWith
  rw [lastBitmap_snoc, foldl_zipIdx_snoc]

/-- A key klong added at an index that the last bitmap does not hold. -/
theorem live_append_key_of {ks : List Klong} (h : ∀ j ∈ lastBitmap ks, j < ks.length) (c : Nat)
    (y : NodeId) : live (ks ++ [.key c y]) = insertCv c y (live ks) := by
  unfold live liveWith
  rw [lastBitmap_snoc, foldl_zipIdx_snoc]
  have hns : (lastBitmap ks).contains ks.length = false := by
    rw [Bool.eq_false_iff]
    intro hc
    have := h _ (List.contains_iff_mem.mp hc)
    omega
  simp only [hns, Bool.false_eq_true, ite_false]

theorem bmW_of_wf {ks : List Klong} (h : klongsWf ks = true) : BmW ks := by
  simp only [klongsWf, Bool.and_eq_true] at h
  have hb := (bmFold_spec ks ks).2 h.2
  intro l1 b l2 he
  have := bitmapOk_iff (hb l1 b l2 he)
  exact ⟨this.1, this.2.1⟩

theorem live_append_key {ks : List Klong} (h : klongsWf ks = true) (c : Nat) (y : NodeId) :
    live (ks ++ [.key c y]) = insertCv c y (live ks) :=
  live_append_key_of (bmW_of_wf h).lt_length c y

/-- Two lists in strictly increasing order of their compare values with the
same members are equal. -/
theorem cvSorted_ext : ∀ {l1 l2 : List (Nat × NodeId)}, l1.Pairwise CvLt → l2.Pairwise CvLt →
    (∀ p, p ∈ l1 ↔ p ∈ l2) → l1 = l2
  | [], [], _, _, _ => rfl
  | [], b :: _, _, _, h => absurd ((h b).mpr List.mem_cons_self) (by simp)
  | a :: _, [], _, _, h => absurd ((h a).mp List.mem_cons_self) (by simp)
  | a :: r1, b :: r2, h1, h2, h => by
    rw [List.pairwise_cons] at h1 h2
    have hab : a = b := by
      rcases List.mem_cons.mp ((h a).mp List.mem_cons_self) with hb | hb
      · exact hb
      · rcases List.mem_cons.mp ((h b).mpr List.mem_cons_self) with ha | ha
        · exact ha.symm
        · have := h1.1 b ha
          have := h2.1 a hb
          unfold CvLt at *
          omega
    subst hab
    rw [cvSorted_ext h1.2 h2.2 (fun p => ?_)]
    constructor
    · intro hp
      rcases List.mem_cons.mp ((h p).mp (List.mem_cons_of_mem _ hp)) with hp2 | hp2
      · subst hp2; have := h1.1 _ hp; unfold CvLt at this; omega
      · exact hp2
    · intro hp
      rcases List.mem_cons.mp ((h p).mpr (List.mem_cons_of_mem _ hp)) with hp2 | hp2
      · subst hp2; have := h2.1 _ hp; unfold CvLt at this; omega
      · exact hp2

/-- The members of a fold of `insertCv` over klongs of distinct compare values. -/
theorem mem_foldl_insertCv {p : Nat × NodeId} :
    ∀ (L : List (Nat × NodeId)) (m : List (Nat × NodeId)),
    m.Pairwise CvLt → L.Pairwise (fun a b => a.1 ≠ b.1) →
    (p ∈ L.foldl (fun m cy => insertCv cy.1 cy.2 m) m ↔ p ∈ L ∨ (p ∈ m ∧ ∀ q ∈ L, q.1 ≠ p.1))
  | [], m, _, _ => by simp
  | a :: L, m, hm, hL => by
    rw [List.pairwise_cons] at hL
    rw [List.foldl_cons, mem_foldl_insertCv L _ (insertCv_sorted _ _ hm) hL.2, mem_insertCv_iff hm]
    constructor
    · rintro (h | ⟨h | ⟨h1, h2⟩, h3⟩)
      · exact Or.inl (List.mem_cons_of_mem _ h)
      · exact Or.inl (by rw [h]; exact List.mem_cons_self)
      · refine Or.inr ⟨h1, ?_⟩
        intro q hq
        rcases List.mem_cons.mp hq with rfl | hq
        · exact fun e => h2 e.symm
        · exact h3 q hq
    · rintro (h | ⟨h1, h2⟩)
      · rcases List.mem_cons.mp h with rfl | h
        · refine Or.inr ⟨Or.inl rfl, ?_⟩
          intro q hq e
          exact hL.1 q hq e.symm
        · exact Or.inl h
      · exact Or.inr ⟨Or.inr ⟨h1, fun e => h2 a List.mem_cons_self e.symm⟩,
          fun q hq => h2 q (List.mem_cons_of_mem _ hq)⟩

theorem lastBitmap_keys (t : Time) (L : List (Nat × NodeId)) :
    lastBitmap (.time t :: L.map (fun cy => Klong.key cy.1 cy.2)) = [] := by
  induction L using List.reverseRecOn with
  | nil => rfl
  | append_singleton L a ih =>
    rw [List.map_append, List.map_singleton, ← List.cons_append, lastBitmap_snoc]
    exact ih

/-- The live klongs of a time klong and key klongs: the fold of `insertCv`. -/
theorem live_keys (t : Time) (L : List (Nat × NodeId)) :
    live (.time t :: L.map (fun cy => Klong.key cy.1 cy.2)) =
      L.foldl (fun m cy => insertCv cy.1 cy.2 m) [] := by
  induction L using List.reverseRecOn with
  | nil => rfl
  | append_singleton L a ih =>
    rw [List.map_append, List.map_singleton, ← List.cons_append,
      live_append_key_of (by rw [lastBitmap_keys]; simp), ih, List.foldl_append]
    rfl

theorem mem_live_keys {L : List (Nat × NodeId)} (hL : L.Pairwise (fun a b => a.1 ≠ b.1)) (t : Time)
    (p : Nat × NodeId) : p ∈ live (.time t :: L.map (fun cy => Klong.key cy.1 cy.2)) ↔ p ∈ L := by
  rw [live_keys, mem_foldl_insertCv L [] List.Pairwise.nil hL]
  simp

theorem CvLt.ne {l : List (Nat × NodeId)} (hs : l.Pairwise CvLt) :
    l.Pairwise (fun a b => a.1 ≠ b.1) :=
  hs.imp (fun h => Nat.ne_of_lt h)

/-- The live klongs of a last version: its key klongs. -/
theorem live_version {l : List (Nat × NodeId)} (hs : l.Pairwise CvLt) (t : Time) :
    live (.time t :: l.map (fun cy => Klong.key cy.1 cy.2)) = l :=
  cvSorted_ext (live_sorted _) hs (mem_live_keys (CvLt.ne hs) t)

/-- The step of the check of the times (W1). -/
def tStep (acc : Bool × Option Time) (k : Klong) : Bool × Option Time :=
  match k with
  | .time t => (acc.1 && (match acc.2 with
      | some t0 => decide (t0 < t)
      | none => true), some t)
  | _ => acc

/-- The check of the first klong (W1). -/
def headOk (ks : List Klong) : Bool :=
  match ks with
  | .time _ :: _ => true
  | [] => true
  | _ => false

theorem timesOk_eq (ks : List Klong) :
    timesOk ks = (headOk ks && (ks.foldl tStep (true, none)).1) := rfl

/-- The step of the last time. -/
def lastStep (o : Option Time) (k : Klong) : Option Time :=
  match k with
  | .time x => some x
  | _ => o

/-- The time of the last time klong. -/
def lastT (ks : List Klong) : Option Time := ks.foldl lastStep none

theorem tfold_snd : ∀ (l : List Klong) (a : Bool × Option Time),
    (l.foldl tStep a).2 = l.foldl lastStep a.2
  | [], _ => rfl
  | k :: l, a => by
    rw [List.foldl_cons, List.foldl_cons, tfold_snd l]
    cases k <;> rfl

theorem lastFold_mem : ∀ (l : List Klong) (o : Option Time) (t0 : Time),
    l.foldl lastStep o = some t0 → o = some t0 ∨ Klong.time t0 ∈ l
  | [], _, _, h => Or.inl h
  | k :: l, o, t0, h => by
    rw [List.foldl_cons] at h
    rcases lastFold_mem l _ t0 h with h1 | h1
    · cases k with
      | time x =>
        simp only [lastStep, Option.some.injEq] at h1
        exact Or.inr (by rw [h1]; exact List.mem_cons_self)
      | key c y => exact Or.inl h1
      | del b => exact Or.inl h1
    · exact Or.inr (List.mem_cons_of_mem _ h1)

theorem lastT_mem {ks : List Klong} {t0 : Time} (h : lastT ks = some t0) : Klong.time t0 ∈ ks := by
  rcases lastFold_mem ks none t0 h with h1 | h1
  · simp at h1
  · exact h1

theorem headOk_append {ks : List Klong} (hne : ks ≠ []) (l : List Klong) :
    headOk (ks ++ l) = headOk ks := by
  cases ks with
  | nil => exact absurd rfl hne
  | cons k r => cases k <;> rfl

theorem timesOk_append_time {ks : List Klong} (h : timesOk ks = true) {t : Time}
    (ht : ∀ t0, lastT ks = some t0 → t0 < t) : timesOk (ks ++ [.time t]) = true := by
  rw [timesOk_eq, Bool.and_eq_true] at h
  rw [timesOk_eq, List.foldl_append, List.foldl_cons, List.foldl_nil]
  have hh : headOk (ks ++ [.time t]) = true := by
    by_cases hne : ks = []
    · subst hne; rfl
    · rw [headOk_append hne]; exact h.1
  rw [hh, Bool.true_and]
  have h2 := tfold_snd ks (true, none)
  simp only [tStep]
  rw [h.2, Bool.true_and]
  cases hl : (ks.foldl tStep (true, none)).2 with
  | none => rfl
  | some t0 =>
    have := ht t0 (by rw [← hl, h2]; rfl)
    simpa using this

theorem timesOk_append_key {ks : List Klong} (h : timesOk ks = true) (hne : ks ≠ [])
    (c : Nat) (y : NodeId) : timesOk (ks ++ [.key c y]) = true := by
  rw [timesOk_eq, Bool.and_eq_true] at h
  rw [timesOk_eq, List.foldl_append, List.foldl_cons, List.foldl_nil, headOk_append hne]
  exact Bool.and_eq_true_iff.mpr ⟨h.1, h.2⟩

theorem all_congr_mem {α : Type} {p q : α → Bool} : ∀ {l : List α}, (∀ a ∈ l, p a = q a) →
    l.all p = l.all q
  | [], _ => rfl
  | a :: l, h => by
    simp only [List.all_cons]
    rw [h a List.mem_cons_self, all_congr_mem (fun b hb => h b (List.mem_cons_of_mem _ hb))]

theorem cvAt_append {ks : List Klong} {j : Nat} (hj : j < ks.length) (l : List Klong) :
    cvAt (ks ++ l) j = cvAt ks j := by
  simp only [cvAt, List.getElem?_append_left hj]

theorem bitmapOk_append {ks : List Klong} {i : Nat} (hi : i ≤ ks.length) (l : List Klong)
    (before bits : List Nat) : bitmapOk (ks ++ l) i before bits = bitmapOk ks i before bits := by
  unfold bitmapOk
  have hA : bits.all (fun j => decide (j < i) && (cvAt (ks ++ l) j).isSome) =
      bits.all (fun j => decide (j < i) && (cvAt ks j).isSome) := by
    refine List.all_congr rfl (fun j => ?_)
    by_cases hj : j < i
    · rw [cvAt_append (by omega)]
    · simp [hj]
  rw [hA]
  cases hA' : bits.all (fun j => decide (j < i) && (cvAt ks j).isSome)
  · rfl
  · simp only [Bool.true_and]
    congr 1
    refine all_congr_mem (fun j hj => ?_)
    have hji : j < i := by
      have := List.all_eq_true.mp hA' j hj
      simp only [Bool.and_eq_true, decide_eq_true_eq] at this
      exact this.1
    refine all_congr_mem (fun j' hj' => ?_)
    have := List.mem_range.mp hj'
    rw [cvAt_append (by omega), cvAt_append (by omega)]

theorem bitmapsOk_append {ks : List Klong} (h : bitmapsOk ks = true) (k : Klong)
    (hk : ∀ b, k ≠ .del b) : bitmapsOk (ks ++ [k]) = true := by
  unfold bitmapsOk at h ⊢
  rw [foldl_zipIdx_snoc]
  have hstep : ∀ acc, bmStep (ks ++ [k]) acc k ks.length = acc := by
    intro acc
    cases k with
    | del b => exact absurd rfl (hk b)
    | time t => rfl
    | key c y => rfl
  rw [hstep]
  rw [List.foldl_ext _ (fun acc ki => bmStep ks acc ki.1 ki.2)]
  · exact h
  · rintro acc ⟨k', i⟩ hm
    have hi := (List.mem_zipIdx hm).2.1
    cases k' with
    | del b =>
      simp only [bmStep]
      rw [bitmapOk_append (by omega)]
    | time t => rfl
    | key c y => rfl

theorem klongsWf_append_time_of {ks : List Klong} (h : klongsWf ks = true) {t : Time}
    (ht : ∀ t0, lastT ks = some t0 → t0 < t) : klongsWf (ks ++ [.time t]) = true := by
  simp only [klongsWf, Bool.and_eq_true] at h ⊢
  exact ⟨timesOk_append_time h.1 ht, bitmapsOk_append h.2 _ (by simp)⟩

theorem klongsWf_append_time {ks : List Klong} (h : klongsWf ks = true) {t : Time}
    (ht : ∀ t', Klong.time t' ∈ ks → t' < t) : klongsWf (ks ++ [.time t]) = true :=
  klongsWf_append_time_of h (fun t0 h0 => ht t0 (lastT_mem h0))

theorem klongsWf_append_key {ks : List Klong} (h : klongsWf ks = true) (hne : ks ≠ []) (c : Nat)
    (y : NodeId) : klongsWf (ks ++ [.key c y]) = true := by
  simp only [klongsWf, Bool.and_eq_true] at h ⊢
  exact ⟨timesOk_append_key h.1 hne c y, bitmapsOk_append h.2 _ (by simp)⟩


theorem klongsWf_version (t : Time) (l : List (Nat × NodeId)) :
    klongsWf (.time t :: l.map (fun cy => Klong.key cy.1 cy.2)) = true := by
  induction l using List.reverseRecOn with
  | nil => rfl
  | append_singleton L a ih =>
    rw [List.map_append, List.map_singleton, ← List.cons_append]
    exact klongsWf_append_key ih (by simp) _ _

/-- Where `insertCv` puts a klong: the klongs below it before, those above it
after, and a klong of its compare value replaced. -/
theorem insertCv_split {l : List (Nat × NodeId)} (hs : l.Pairwise CvLt) (c : Nat) (y : NodeId) :
    ∃ pre post, (∀ a ∈ pre, a.1 < c) ∧ (∀ b ∈ post, c < b.1) ∧
      insertCv c y l = pre ++ (c, y) :: post ∧
      (l = pre ++ post ∨ ∃ y0, l = pre ++ (c, y0) :: post) := by
  induction l with
  | nil => exact ⟨[], [], by simp, by simp, rfl, Or.inl rfl⟩
  | cons a r ih =>
    obtain ⟨c', y'⟩ := a
    rw [List.pairwise_cons] at hs
    unfold insertCv
    by_cases h1 : c < c'
    · refine ⟨[], (c', y') :: r, by simp, ?_, by simp [h1], Or.inl rfl⟩
      intro b hb
      rcases List.mem_cons.mp hb with rfl | hb
      · exact h1
      · have := hs.1 b hb; unfold CvLt at this; simp at this; omega
    · by_cases h2 : c = c'
      · subst h2
        refine ⟨[], r, by simp, ?_, by simp, Or.inr ⟨y', rfl⟩⟩
        intro b hb
        have := hs.1 b hb; unfold CvLt at this; simpa using this
      · obtain ⟨pre, post, hpre, hpost, he, hl⟩ := ih hs.2
        refine ⟨(c', y') :: pre, post, ?_, hpost, by simp [h1, h2, he], ?_⟩
        · intro a ha
          rcases List.mem_cons.mp ha with rfl | ha
          · show c' < c; omega
          · exact hpre a ha
        · rcases hl with hl | ⟨y0, hl⟩
          · exact Or.inl (by rw [hl]; rfl)
          · exact Or.inr ⟨y0, by rw [hl]; rfl⟩

/-! ## 2. A key node of the model -/

/-- The klongs of a key node of the model, as the contract's. -/
def ksOf (n : MNode) : List Klong := n.ks.map kOf

/-- No klong of the node has a time after t. -/
def TimesLe (n : MNode) (t : Time) : Prop := ∀ t', Klong.time t' ∈ ksOf n → t' ≤ t

theorem add_ks (n : MNode) (t : Time) (k : MKlong) :
    ((n.add t k).ks = n.ks ++ [.time t, k] ∧ ∀ lt, n.lastTime = some lt → lt < t) ∨
    ((n.add t k).ks = n.ks ++ [k] ∧ ∃ lt, n.lastTime = some lt ∧ t ≤ lt) := by
  unfold SIS.Tree.KNode.add
  cases h : n.lastTime with
  | none => exact Or.inl ⟨rfl, by simp⟩
  | some lt =>
    by_cases hlt : lt < t
    · refine Or.inl ⟨by simp [hlt], fun lt' h' => ?_⟩
      simp only [Option.some.injEq] at h'
      rw [← h']
      exact hlt
    · exact Or.inr ⟨by simp [hlt], lt, rfl, Nat.le_of_not_lt hlt⟩

theorem ksOf_add (n : MNode) (t : Time) (k : MKlong) :
    (ksOf (n.add t k) = ksOf n ++ [.time t, kOf k] ∧ ∀ lt, n.lastTime = some lt → lt < t) ∨
    (ksOf (n.add t k) = ksOf n ++ [kOf k] ∧ ∃ lt, n.lastTime = some lt ∧ t ≤ lt) := by
  rcases add_ks n t k with ⟨h, h1⟩ | ⟨h, h1⟩
  · exact Or.inl ⟨by simp [ksOf, h, kOf], h1⟩
  · exact Or.inr ⟨by simp [ksOf, h], h1⟩

theorem lastT_ksOf (n : MNode) : lastT (ksOf n) = n.lastTime := by
  unfold lastT ksOf SIS.Tree.KNode.lastTime
  rw [List.foldl_map]
  congr 1
  funext o k
  cases k <;> rfl

theorem ksOf_ne_nil {n : MNode} {lt : Time} (h : n.lastTime = some lt) : ksOf n ≠ [] := by
  intro he
  have := lastT_mem (show lastT (ksOf n) = some lt by rw [lastT_ksOf]; exact h)
  rw [he] at this
  simp at this

theorem kOf_eq_time {k : MKlong} {t : Time} (h : kOf k = .time t) : k = .time t := by
  cases k <;> simp_all [kOf]

/-- `KNode.add` of a key klong at time t, on a well-formed node with no time
after t: the klong is added to the live klongs; the node stays well formed,
with no time after t, and grows by at most two klongs; a first time klong
stays the first. -/
theorem add_key_live {n : MNode} {t : Time} (hwf : klongsWf (ksOf n) = true) (c : Nat)
    (y : NodeId) :
    live (ksOf (n.add t (.key c y))) = insertCv c y (live (ksOf n)) := by
  have hb := (bmW_of_wf hwf).lt_length
  rcases ksOf_add n t (.key c y) with ⟨h, _⟩ | ⟨h, _⟩
  · have he : ksOf (n.add t (.key c y)) = (ksOf n ++ [.time t]) ++ [.key c y] := by
      rw [h]; simp [kOf]
    rw [he, live_append_key_of, live_append_time]
    intro j hj
    rw [lastBitmap_snoc] at hj
    have := hb j hj
    simp only [List.length_append, List.length_singleton]
    omega
  · rw [h]
    exact live_append_key hwf c y

theorem add_key_wf {n : MNode} {t : Time} (hwf : klongsWf (ksOf n) = true) (c : Nat) (y : NodeId) :
    klongsWf (ksOf (n.add t (.key c y))) = true := by
  rcases ksOf_add n t (.key c y) with ⟨h, hl⟩ | ⟨h, lt, hl, _⟩
  · have he : ksOf (n.add t (.key c y)) = (ksOf n ++ [.time t]) ++ [.key c y] := by
      rw [h]; simp [kOf]
    rw [he]
    exact klongsWf_append_key
      (klongsWf_append_time_of hwf (fun t0 h0 => hl t0 (by rw [← lastT_ksOf]; exact h0)))
      (by simp) c y
  · rw [h]
    exact klongsWf_append_key hwf (ksOf_ne_nil hl) c y

theorem add_timesLe {n : MNode} {t : Time} (ht : TimesLe n t) (k : MKlong)
    (hk : ∀ t', k = .time t' → t' ≤ t) : TimesLe (n.add t k) t := by
  intro t' ht'
  rcases ksOf_add n t k with ⟨h, _⟩ | ⟨h, _⟩
  · rw [h] at ht'
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at ht'
    rcases ht' with h1 | h1 | h1
    · exact ht t' h1
    · simp only [Klong.time.injEq] at h1; exact Nat.le_of_eq h1
    · exact hk t' (kOf_eq_time h1.symm)
  · rw [h] at ht'
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at ht'
    rcases ht' with h1 | h1
    · exact ht t' h1
    · exact hk t' (kOf_eq_time h1.symm)

theorem add_size (n : MNode) (t : Time) (k : MKlong) : (n.add t k).size ≤ n.size + 2 := by
  unfold SIS.Tree.KNode.size
  rcases add_ks n t k with ⟨h, _⟩ | ⟨h, _⟩ <;> simp [h]

theorem add_leaf (n : MNode) (t : Time) (k : MKlong) : (n.add t k).leaf = n.leaf := by
  unfold SIS.Tree.KNode.add
  split
  · split <;> rfl
  · rfl

/-- The key klongs after `add` of a key klong: those before, and the one added. -/
theorem add_key_mem {n : MNode} {t : Time} {c : Nat} {y : NodeId} {c' : Nat} {y' : NodeId} :
    Klong.key c' y' ∈ ksOf (n.add t (.key c y)) ↔ Klong.key c' y' ∈ ksOf n ∨ (c' = c ∧ y' = y) := by
  rcases ksOf_add n t (.key c y) with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> simp [kOf]

theorem add_first {n : MNode} {t t0 : Time} {rest : List MKlong} (k : MKlong)
    (h : n.ks = .time t0 :: rest) : ∃ rest', (n.add t k).ks = .time t0 :: rest' := by
  rcases add_ks n t k with ⟨h1, _⟩ | ⟨h1, _⟩ <;> rw [h1, h] <;> exact ⟨_, rfl⟩

/-- The frame of `add`: a node that is its klongs ks0 of before the
transaction at time i (all of them before i), or those and then a time klong
of i and more, is so after an `add` at time i. -/
theorem add_ext {n : MNode} {i : Time} {ks0 : List Klong} (h0 : ∀ t, Klong.time t ∈ ks0 → t < i)
    (h : ksOf n = ks0 ∨ ∃ more, ksOf n = ks0 ++ Klong.time i :: more) (k : MKlong) :
    ksOf (n.add i k) = ks0 ∨ ∃ more, ksOf (n.add i k) = ks0 ++ Klong.time i :: more := by
  rcases h with h | ⟨more, h⟩
  · rcases ksOf_add n i k with ⟨he, _⟩ | ⟨_, lt, hl, hle⟩
    · exact Or.inr ⟨[kOf k], by rw [he, h]⟩
    · have := h0 lt (by rw [← h]; exact lastT_mem (by rw [lastT_ksOf]; exact hl))
      exact absurd this (Nat.not_lt.mpr hle)
  · rcases ksOf_add n i k with ⟨he, _⟩ | ⟨he, _⟩
    · exact Or.inr ⟨more ++ [.time i, kOf k], by rw [he, h]; simp⟩
    · exact Or.inr ⟨more ++ [kOf k], by rw [he, h]; simp⟩

theorem mPrefixAt_self {t : Time} :
    ∀ {ks : List MKlong}, (∀ t', SIS.Tree.Klong.time t' ∈ ks → t' ≤ t) →
    SIS.Tree.prefixAt ks t = ks
  | [], _ => rfl
  | k :: r, h => by
    have ih := mPrefixAt_self (ks := r) (fun t' h' => h t' (List.mem_cons_of_mem _ h'))
    unfold SIS.Tree.prefixAt at ih ⊢
    rw [List.takeWhile_cons]
    cases k with
    | time x => simp [h x List.mem_cons_self, ih]
    | key c y => simp [ih]
    | del b => simp [ih]

theorem timesLe_model {n : MNode} {t : Time} (ht : TimesLe n t) :
    ∀ t', SIS.Tree.Klong.time t' ∈ n.ks → t' ≤ t :=
  fun t' h => ht t' (List.mem_map_of_mem (f := kOf) h)

theorem lastBitmap_ksOf (n : MNode) : lastBitmap (ksOf n) = SIS.Tree.lastBitmapOf n.ks := by
  unfold lastBitmap SIS.Tree.lastBitmapOf ksOf
  rw [List.foldl_map]
  congr 1
  funext d k
  cases k <;> rfl

/-- The model's loop of the searches by order is the contract's. -/
theorem searchBy_ksOf {n : MNode} {t : Time} (ht : TimesLe n t)
    (better : Nat → Option Nat → Bool) :
    searchBy (ksOf n) better = (n.searchBy t better).map (fun f => (f.c, f.y)) := by
  unfold SIS.Tree.KNode.searchBy searchBy
  rw [mPrefixAt_self (timesLe_model ht), lastBitmap_ksOf]
  simp only
  unfold ksOf
  rw [List.zipIdx_map, List.foldl_map]
  refine foldl_sim _ _ (fun b (m : Option Time × Option SIS.Tree.Found) =>
    b = m.2.map (fun f => (f.c, f.y))) ?_ _ _ _ rfl
  rintro b ⟨ot, of⟩ ⟨k, i⟩ hR
  simp only at hR
  subst hR
  by_cases hd : i ∈ SIS.Tree.lastBitmapOf n.ks
  · simp [hd]
  · cases k with
    | time x => simp [hd, kOf]
    | del bs => simp [hd, kOf]
    | key c y =>
      by_cases hb : better c (of.map (·.c)) = true
      · simp [hd, kOf, hb, Option.map_map, Function.comp_def]
      · simp [hd, kOf, hb, Option.map_map, Function.comp_def]

theorem searchLte_ksOf {n : MNode} {t : Time} (ht : TimesLe n t) (cv : Nat) :
    searchLte (ksOf n) (.at cv) = (n.searchLte t (cv : Int)).map (fun f => (f.c, f.y)) := by
  unfold searchLte SIS.Tree.KNode.searchLte
  rw [searchBy_ksOf ht]
  congr 2
  funext c best
  cases best <;> simp [bestOr, SIS.Tree.bestOr, Pos.below] <;> rw [Bool.eq_iff_iff] <;> simp

/-- `KNode.searchLte` at a time t that no klong of the node is after: the last
live klong at or below the compare value cv. -/
theorem searchLte_some {n : MNode} {t : Time} (ht : TimesLe n t) {cv : Nat} {fd : SIS.Tree.Found}
    (h : n.searchLte t (cv : Int) = some fd) :
    (fd.c, fd.y) ∈ live (ksOf n) ∧ fd.c ≤ cv ∧
      ∀ c' y', (c', y') ∈ live (ksOf n) → c' ≤ cv → c' ≤ fd.c := by
  have hs := searchLte_best (ksOf n) (.at cv)
  rw [searchLte_ksOf ht cv, h] at hs
  obtain ⟨h1, h2, h3⟩ := hs
  refine ⟨h1, ?_, ?_⟩
  · simpa [Pos.below] using h2
  · intro c' y' hm hle
    exact h3 (c', y') hm (by simp [Pos.below]; omega)

theorem searchLte_none {n : MNode} {t : Time} (ht : TimesLe n t) {cv : Nat}
    (h : n.searchLte t (cv : Int) = none) : ∀ c' y', (c', y') ∈ live (ksOf n) → cv < c' := by
  have hs := searchLte_best (ksOf n) (.at cv)
  rw [searchLte_ksOf ht cv, h] at hs
  intro c' y' hm
  simpa [Pos.below] using hs (c', y') hm

/-- Two folds over one list keep a relation that each step keeps; what follows
from it at the end. -/
theorem foldl_sim_post {α β γ : Type} (f : β → α → β) (g : γ → α → γ) (R P : β → γ → Prop)
    (h : ∀ b c a, R b c → R (f b a) (g c a)) (hP : ∀ b c, R b c → P b c)
    (l : List α) (b : β) (c : γ) (h0 : R b c) : P (l.foldl f b) (l.foldl g c) :=
  hP _ _ (foldl_sim f g R h l b c h0)

/-- The model's loop of `searchEq` is the contract's. -/
theorem searchEq_ksOf {n : MNode} {t : Time} (ht : TimesLe n t) (c : Nat) :
    searchEq (ksOf n) c = (n.searchEq t c).map (·.y) ∧
      ∀ f, n.searchEq t c = some f → f.c = c := by
  unfold searchEq SIS.Tree.KNode.searchEq
  rw [mPrefixAt_self (timesLe_model ht)]
  unfold ksOf
  rw [List.zipIdx_map, List.foldl_map]
  refine foldl_sim_post _ _
    (fun (b : List Nat × Option (Nat × NodeId))
        (m : Option Time × List Nat × Option SIS.Tree.Found) =>
      b.1 = m.2.1 ∧ b.2 = m.2.2.map (fun f => (f.idx, f.y)) ∧ ∀ f, m.2.2 = some f → f.c = c)
    (fun b m => b.2.map (·.2) = m.2.2.map (·.y) ∧ ∀ f, m.2.2 = some f → f.c = c)
    ?_ ?_ _ _ _ ⟨rfl, rfl, by simp⟩
  · rintro ⟨d, o⟩ ⟨ot, d', of⟩ ⟨k, i⟩ ⟨h1, h2, h3⟩
    simp only at h1 h2 h3
    subst h1 h2
    by_cases hd : i ∈ d
    · simpa [eqStep, hd] using h3
    · cases k with
      | time x => simpa [eqStep, hd, kOf] using h3
      | key c' y =>
        by_cases hc : c' = c
        · simp [eqStep, hd, kOf, hc]
        · simpa [eqStep, hd, kOf, hc] using h3
      | del bs =>
        cases of with
        | none => simp [eqStep, hd, kOf]
        | some f =>
          by_cases hb : f.idx ∈ bs
          · simp [eqStep, hd, kOf, hb]
          · simp [eqStep, hd, kOf, hb, h3]
  · rintro ⟨d, o⟩ ⟨ot, d', of⟩ ⟨_, h2, h3⟩
    simp only at h2 h3 ⊢
    refine ⟨?_, h3⟩
    rw [h2, Option.map_map]
    rfl

/-- `KNode.searchEq` on a well-formed node: the live klong of the compare
value. -/
theorem searchEq_some {n : MNode} {t : Time} (hwf : klongsWf (ksOf n) = true) (ht : TimesLe n t)
    {c : Nat} {fd : SIS.Tree.Found} (h : n.searchEq t c = some fd) :
    fd.c = c ∧ (c, fd.y) ∈ live (ksOf n) := by
  obtain ⟨h1, h2⟩ := searchEq_ksOf ht c
  rw [h] at h1
  refine ⟨h2 fd h, ?_⟩
  rw [searchEq_spec _ hwf] at h1
  exact (lookup_iff_mem (live_sorted _) c fd.y).mp h1

theorem searchEq_none {n : MNode} {t : Time} (hwf : klongsWf (ksOf n) = true) (ht : TimesLe n t)
    {c : Nat} (h : n.searchEq t c = none) : ∀ y, (c, y) ∉ live (ksOf n) := by
  obtain ⟨h1, _⟩ := searchEq_ksOf ht c
  rw [h, searchEq_spec _ hwf] at h1
  intro y hy
  rw [(lookup_iff_mem (live_sorted _) c y).mpr hy] at h1
  simp at h1

/-- `setCv` on a list of distinct compare values: the new pair, and the pairs of
other compare values. -/
theorem setCv_spec {m : List (Nat × NodeId)} (hm : m.Pairwise (fun a b => a.1 ≠ b.1)) (c : Nat)
    (y : NodeId) : (SIS.Tree.setCv m c y).Pairwise (fun a b => a.1 ≠ b.1) ∧
      ∀ p, p ∈ SIS.Tree.setCv m c y ↔ p = (c, y) ∨ (p ∈ m ∧ p.1 ≠ c) := by
  unfold SIS.Tree.setCv
  split
  · rename_i hany
    obtain ⟨q, hq, hqc⟩ : ∃ q ∈ m, q.1 = c := by simpa using hany
    have hfst : ∀ a : Nat × NodeId, (if a.1 == c then (c, y) else a).1 = a.1 := by
      intro a
      by_cases ha : a.1 = c <;> simp [ha]
    constructor
    · rw [List.pairwise_map]
      refine hm.imp ?_
      intro a b hab
      rw [hfst, hfst]
      exact hab
    · intro p
      rw [List.mem_map]
      constructor
      · rintro ⟨a, ha, rfl⟩
        by_cases hac : a.1 = c
        · left; simp [hac]
        · right; simp [hac, ha]
      · rintro (rfl | ⟨hp, hpc⟩)
        · exact ⟨q, hq, by simp [hqc]⟩
        · exact ⟨p, hp, by simp [hpc]⟩
  · rename_i hany
    have hno : ∀ q ∈ m, q.1 ≠ c := by
      intro q hq hqc
      apply hany
      simp only [List.any_eq_true, beq_iff_eq]
      exact ⟨q, hq, hqc⟩
    constructor
    · rw [List.pairwise_append]
      refine ⟨hm, by simp, ?_⟩
      intro a ha b hb
      rw [List.mem_singleton] at hb
      subst hb
      exact hno a ha
    · intro p
      simp only [List.mem_append, List.mem_singleton]
      constructor
      · rintro (hp | hp)
        · exact Or.inr ⟨hp, hno p hp⟩
        · exact Or.inl hp
      · rintro (hp | ⟨hp, _⟩)
        · exact Or.inr hp
        · exact Or.inl hp

/-- The last version: its key klongs are a list of distinct compare values
with the members of the live klongs, sorted. -/
theorem lastVersion_struct (n : MNode) (t : Time) :
    ∃ m : List (Nat × NodeId), (n.lastVersion t).ks =
      .time t :: (m.mergeSort (fun a b => decide (a.1 ≤ b.1))).map (fun p => .key p.1 p.2) ∧
      m.Pairwise (fun a b => a.1 ≠ b.1) ∧ ∀ p, p ∈ m ↔ p ∈ live (ksOf n) := by
  refine ⟨_, rfl, ?_⟩
  unfold SIS.Tree.KNode.lastBitmap live liveWith
  rw [lastBitmap_ksOf]
  unfold ksOf
  rw [List.zipIdx_map, List.foldl_map]
  refine foldl_sim_post _ _
    (fun (b c : List (Nat × NodeId)) =>
      b.Pairwise (fun a b => a.1 ≠ b.1) ∧ c.Pairwise CvLt ∧ ∀ p, p ∈ b ↔ p ∈ c)
    (fun b c => b.Pairwise (fun a b => a.1 ≠ b.1) ∧ ∀ p, p ∈ b ↔ p ∈ c)
    ?_ (fun _ _ h => ⟨h.1, h.2.2⟩) _ _ _ ⟨List.Pairwise.nil, List.Pairwise.nil, fun _ => Iff.rfl⟩
  rintro b c ⟨k, i⟩ ⟨hb, hc, hmem⟩
  cases k with
  | time x => exact ⟨hb, hc, hmem⟩
  | del bs => exact ⟨hb, hc, hmem⟩
  | key c' y =>
    by_cases hd : i ∈ SIS.Tree.lastBitmapOf n.ks
    · simp only [kOf, Prod.map, id, List.contains_iff_mem, hd, ite_true]
      exact ⟨hb, hc, hmem⟩
    · simp only [kOf, Prod.map, id, List.contains_iff_mem, hd, ite_false]
      obtain ⟨h1, h2⟩ := setCv_spec hb c' y
      refine ⟨h1, insertCv_sorted c' y hc, fun p => ?_⟩
      rw [h2, mem_insertCv_iff hc, hmem]

/-- `KNode.lastVersion` of a well-formed node: a time klong and the live
klongs, in their order. -/
theorem lastVersion_ks {n : MNode} (t : Time) :
    ksOf (n.lastVersion t) =
      Klong.time t :: (live (ksOf n)).map (fun cy => Klong.key cy.1 cy.2) := by
  obtain ⟨m, hks, hd, hmem⟩ := lastVersion_struct n t
  rw [show ksOf (n.lastVersion t) = (n.lastVersion t).ks.map kOf from rfl, hks]
  have h1 := List.pairwise_mergeSort (le := fun a b : Nat × NodeId => decide (a.1 ≤ b.1))
    (fun a b c hab hbc => by simp only [decide_eq_true_eq] at hab hbc ⊢; omega)
    (fun a b => by simp only [Bool.or_eq_true, decide_eq_true_eq]; omega) m
  have h2 : (m.mergeSort (fun a b => decide (a.1 ≤ b.1))).Pairwise (fun a b => a.1 ≠ b.1) :=
    ((List.mergeSort_perm m _).pairwise_iff (fun h => Ne.symm h)).mpr hd
  have h3 : (m.mergeSort (fun a b => decide (a.1 ≤ b.1))).Pairwise CvLt :=
    (h1.and h2).imp (fun h => lt_of_le_of_ne (by simpa using h.1) h.2)
  rw [cvSorted_ext h3 (live_sorted _) (fun p => by rw [List.mem_mergeSort, hmem])]
  simp [kOf]

theorem lastVersion_leaf (n : MNode) (t : Time) : (n.lastVersion t).leaf = n.leaf := by
  rfl

theorem go_none (t cv y : Nat) : ∀ (L : List (Nat × NodeId)) (pre : List MKlong),
    (∀ p ∈ L, p.1 ≠ cv) →
    SIS.Tree.replaceKlong.go t cv y pre (L.map (fun p => SIS.Tree.Klong.key p.1 p.2)) (some t) =
      .ok none
  | [], _, _ => rfl
  | a :: L, pre, h => by
    have ha : (a.1 == cv) = false := by simpa using h a List.mem_cons_self
    simp only [List.map_cons, SIS.Tree.replaceKlong.go, ha, Bool.false_and, Bool.false_eq_true,
      ite_false]
    exact go_none t cv y L _ (fun p hp => h p (List.mem_cons_of_mem _ hp))

theorem go_some (t cv y y0 : Nat) (L2 : List (Nat × NodeId)) : ∀ (L1 : List (Nat × NodeId))
    (pre : List MKlong), (∀ p ∈ L1, p.1 ≠ cv) →
    SIS.Tree.replaceKlong.go t cv y pre
      ((L1 ++ (cv, y0) :: L2).map (fun p => SIS.Tree.Klong.key p.1 p.2)) (some t) =
      .ok (some (pre ++ (L1 ++ (cv, y) :: L2).map (fun p => SIS.Tree.Klong.key p.1 p.2)))
  | [], pre, _ => by simp [SIS.Tree.replaceKlong.go]
  | a :: L1, pre, h => by
    have ha : (a.1 == cv) = false := by simpa using h a List.mem_cons_self
    simp only [List.cons_append, List.map_cons, SIS.Tree.replaceKlong.go, ha, Bool.false_and,
      Bool.false_eq_true, ite_false]
    rw [go_some t cv y y0 L2 L1 _ (fun p hp => h p (List.mem_cons_of_mem _ hp))]
    simp

theorem lastT_keys (t : Time) : ∀ (L : List (Nat × NodeId)),
    (L.map (fun cy => Klong.key cy.1 cy.2)).foldl lastStep (some t) = some t
  | [] => rfl
  | _ :: L => lastT_keys t L

/-- A writer's step that gives no error and changes no state, for every klong
of a list, keeps an invariant of the node and of the live klongs set so far. -/
theorem foldlM_exists (F : MNode → Nat × NodeId → SIS.Tree.M MNode) (c : SIS.Tree.Ctx) (w : MW)
    (I : MNode → List (Nat × NodeId) → Prop) (Q : MNode → Prop)
    (hF : ∀ r M (cy : Nat × NodeId), I r M →
      ∃ r', F r cy c w = .ok (r', w) ∧ I r' (insertCv cy.1 cy.2 M))
    (ins : List (Nat × NodeId)) (r0 : MNode) (M0 : List (Nat × NodeId))
    (hQ : ∀ r, I r (ins.foldl (fun m cy => insertCv cy.1 cy.2 m) M0) → Q r) (h0 : I r0 M0) :
    ∃ r, List.foldlM F r0 ins c w = .ok (r, w) ∧ Q r := by
  induction ins generalizing r0 M0 with
  | nil => exact ⟨r0, rfl, hQ r0 h0⟩
  | cons cy ins ih =>
    obtain ⟨r1, h1, hI1⟩ := hF r0 M0 cy h0
    obtain ⟨r, h2, hr⟩ := ih r1 _ hQ hI1
    refine ⟨r, ?_, hr⟩
    rw [List.foldlM_cons]
    simp only [bind, ReaderT.bind, StateT.bind, h1, Except.bind]
    exact h2

theorem mem_foldl_insertCv_src {p : Nat × NodeId} : ∀ (ins : List (Nat × NodeId))
    (m : List (Nat × NodeId)), p ∈ ins.foldl (fun m cy => insertCv cy.1 cy.2 m) m → p ∈ m ∨ p ∈ ins
  | [], _, h => Or.inl h
  | cy :: ins, m, h => by
    rcases mem_foldl_insertCv_src ins _ h with h1 | h1
    · rcases mem_insertCv h1 with h2 | h2
      · exact Or.inr (by rw [h2]; exact List.mem_cons_self)
      · exact Or.inl h2
    · exact Or.inr (List.mem_cons_of_mem _ h1)

theorem length_insertCv (c : Nat) (y : NodeId) :
    ∀ m : List (Nat × NodeId), (insertCv c y m).length ≤ m.length + 1
  | [] => by simp [insertCv]
  | (c', y') :: r => by
    unfold insertCv
    split
    · simp
    · split
      · simp
      · have := length_insertCv c y r
        simp only [List.length_cons]
        omega

theorem length_foldl_insertCv : ∀ (ins m : List (Nat × NodeId)),
    (ins.foldl (fun m cy => insertCv cy.1 cy.2 m) m).length ≤ m.length + ins.length
  | [], _ => by simp
  | cy :: ins, m => by
    have h1 := length_foldl_insertCv ins (insertCv cy.1 cy.2 m)
    have h2 := length_insertCv cy.1 cy.2 m
    simp only [List.foldl_cons, List.length_cons] at h1 ⊢
    omega

theorem kOf_injective : Function.Injective kOf := by
  intro a b h
  cases a <;> cases b <;> simp_all [kOf]

theorem ksOf_keys {r : MNode} {t : Time} {L : List (Nat × NodeId)}
    (h : r.ks = .time t :: L.map (fun p => SIS.Tree.Klong.key p.1 p.2)) :
    ksOf r = .time t :: L.map (fun p => Klong.key p.1 p.2) := by
  simp [ksOf, h, kOf]

/-- `replaceOrAdd` (the loop of `Dag.timeSplit`) on a last version of time
`c.i`, the transaction's: it gives no error and changes no state; the result
is well formed, its live klongs are the last version's with the klongs `ins`
set in their order, it has no time but `c.i`, starts with its time klong, and
has one klong more than its live klongs, or more by at most the klongs
added. -/
theorem replaceOrAdd_spec (c : SIS.Tree.Ctx) (w : MW) {last : MNode} {l : List (Nat × NodeId)}
    (hs : l.Pairwise CvLt)
    (hl : ksOf last = Klong.time c.i :: l.map (fun cy => Klong.key cy.1 cy.2))
    (ins : List (Nat × NodeId)) :
    ∃ r, SIS.Tree.replaceOrAdd last ins c w = .ok (r, w) ∧ r.leaf = last.leaf ∧
      klongsWf (ksOf r) = true ∧
      live (ksOf r) = ins.foldl (fun m cy => insertCv cy.1 cy.2 m) l ∧
      (∃ rest, r.ks = SIS.Tree.Klong.time c.i :: rest) ∧ TimesLe r c.i ∧
      (∀ t, Klong.time t ∈ ksOf r → t = c.i) ∧
      r.size ≤ 1 + l.length + ins.length ∧
      (∀ c' y', Klong.key c' y' ∈ ksOf r → (c', y') ∈ l ∨ (c', y') ∈ ins) := by
  have hlast : last.ks = .time c.i :: l.map (fun p => SIS.Tree.Klong.key p.1 p.2) := by
    apply List.map_injective_iff.mpr kOf_injective
    rw [show last.ks.map kOf = ksOf last from rfl, hl]
    simp [kOf]
  unfold SIS.Tree.replaceOrAdd
  simp only [bind, ReaderT.bind, read, readThe, MonadReaderOf.read, ReaderT.read, pure,
    StateT.pure, StateT.bind, Except.pure, Except.bind]
  refine foldlM_exists _ c w
    (fun r M => ∃ L : List (Nat × NodeId),
      r.ks = .time c.i :: L.map (fun p => SIS.Tree.Klong.key p.1 p.2) ∧
      L.Pairwise (fun a b => a.1 ≠ b.1) ∧ (∀ p, p ∈ L ↔ p ∈ M) ∧ M.Pairwise CvLt ∧
      r.leaf = last.leaf) _ ?_ ins last l ?_ ⟨l, hlast, CvLt.ne hs, fun _ => Iff.rfl, hs, rfl⟩
  · rintro r M ⟨cv, y⟩ ⟨L, hks, hL, hmem, hM, hleaf⟩
    simp only
    by_cases hex : ∃ p ∈ L, p.1 = cv
    · obtain ⟨p, hp, hpc⟩ := hex
      obtain ⟨L1, L2, rfl⟩ := List.append_of_mem hp
      obtain ⟨cv', y0⟩ := p
      simp only at hpc
      subst hpc
      rw [List.pairwise_append, List.pairwise_cons] at hL
      obtain ⟨h1, ⟨h2, h3⟩, h4⟩ := hL
      have hL1 : ∀ q ∈ L1, q.1 ≠ cv' := fun q hq => h4 q hq _ List.mem_cons_self
      have hL2 : ∀ q ∈ L2, q.1 ≠ cv' := fun q hq e => h2 q hq e.symm
      have hrk : SIS.Tree.replaceKlong r.ks c.i cv' y = .ok (some (.time c.i ::
          (L1 ++ (cv', y) :: L2).map (fun p => SIS.Tree.Klong.key p.1 p.2))) := by
        rw [hks]
        show SIS.Tree.replaceKlong.go c.i cv' y [] (.time c.i :: _) none = _
        simp only [SIS.Tree.replaceKlong.go]
        rw [go_some c.i cv' y y0 L2 L1 _ hL1]
        rfl
      refine ⟨⟨r.leaf, .time c.i :: (L1 ++ (cv', y) :: L2).map
        (fun p => SIS.Tree.Klong.key p.1 p.2)⟩, ?_, L1 ++ (cv', y) :: L2, rfl, ?_, ?_,
        insertCv_sorted _ _ hM, hleaf⟩
      · rw [hrk]
        rfl
      · rw [List.pairwise_append, List.pairwise_cons]
        refine ⟨h1, ⟨fun q hq e => hL2 q hq e.symm, h3⟩, ?_⟩
        intro a ha b hb
        rcases List.mem_cons.mp hb with rfl | hb
        · exact hL1 a ha
        · exact h4 a ha b (List.mem_cons_of_mem _ hb)
      · intro q
        rw [mem_insertCv_iff hM, ← hmem]
        simp only [List.mem_append, List.mem_cons]
        constructor
        · rintro (hq | rfl | hq)
          · exact Or.inr ⟨Or.inl hq, hL1 q hq⟩
          · exact Or.inl rfl
          · exact Or.inr ⟨Or.inr (Or.inr hq), hL2 q hq⟩
        · rintro (rfl | ⟨hq | rfl | hq, hne⟩)
          · exact Or.inr (Or.inl rfl)
          · exact Or.inl hq
          · exact absurd rfl hne
          · exact Or.inr (Or.inr hq)
    · have hno : ∀ p ∈ L, p.1 ≠ cv := fun p hp e => hex ⟨p, hp, e⟩
      have hrk : SIS.Tree.replaceKlong r.ks c.i cv y = .ok none := by
        rw [hks]
        show SIS.Tree.replaceKlong.go c.i cv y [] (.time c.i :: _) none = _
        simp only [SIS.Tree.replaceKlong.go]
        exact go_none c.i cv y L _ hno
      have hlt : r.lastTime = some c.i := by
        rw [← lastT_ksOf, ksOf_keys hks]
        exact lastT_keys c.i L
      have hadd : (r.add c.i (.key cv y)).ks = r.ks ++ [.key cv y] := by
        rcases add_ks r c.i (.key cv y) with ⟨_, h⟩ | ⟨h, _⟩
        · exact absurd (h c.i hlt) (Nat.lt_irrefl _)
        · exact h
      refine ⟨r.add c.i (.key cv y), ?_, L ++ [(cv, y)], ?_, ?_, ?_, insertCv_sorted _ _ hM, ?_⟩
      · rw [hrk]
        rfl
      · rw [hadd, hks]
        simp
      · rw [List.pairwise_append]
        refine ⟨hL, by simp, ?_⟩
        intro a ha b hb
        rw [List.mem_singleton] at hb
        subst hb
        exact hno a ha
      · intro q
        rw [mem_insertCv_iff hM, ← hmem]
        simp only [List.mem_append, List.mem_singleton]
        constructor
        · rintro (hq | hq)
          · exact Or.inr ⟨hq, hno q hq⟩
          · exact Or.inl hq
        · rintro (hq | ⟨hq, _⟩)
          · exact Or.inr hq
          · exact Or.inl hq
      · rw [add_leaf]
        exact hleaf
  · rintro r ⟨L, hks, hL, hmem, hM, hleaf⟩
    have hk := ksOf_keys hks
    have hnd : L.Nodup := hL.imp (fun h e => h (congrArg Prod.fst e))
    refine ⟨hleaf, by rw [hk]; exact klongsWf_version _ _, ?_, ⟨_, hks⟩, ?_, ?_, ?_, ?_⟩
    · rw [hk]
      exact cvSorted_ext (live_sorted _) hM (fun p => (mem_live_keys hL _ p).trans (hmem p))
    · intro t' ht'
      rw [hk] at ht'
      simp at ht'
      exact Nat.le_of_eq ht'
    · intro t' ht'
      rw [hk] at ht'
      simpa using ht'
    · show r.ks.length ≤ _
      rw [hks, List.length_cons, List.length_map]
      have h1 := hnd.length_le_of_subset (fun p hp => (hmem p).mp hp)
      have h3 : L.length ≤ l.length + ins.length := le_trans h1 (length_foldl_insertCv ins l)
      omega
    · intro c' y' hc
      rw [hk] at hc
      simp at hc
      exact mem_foldl_insertCv_src ins l ((hmem _).mp hc)

end Contract
