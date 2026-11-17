/-
The contract package (bergdb 030-10): the node algebra of a delete's bitmap
(`Dag.appendDeleteKlong`): the union of the node's last bitmap and the bits
of a compare value, added as a new bitmap klong (`KNode.add`) or set in the
transaction's own bitmap, the node's last klong (`KNode.setAt`). What it does
to the node as the contract sees it: the live klongs lose the compare value;
the node stays well formed (W1 to W4); its key klongs, kind and first klong
are kept; the frame.
-/
import Contract.Proof.NodeAlg2

namespace Contract

/-- The bitmap that deletes compare value cv in node n (`Dag.appendDeleteKlong`'s
`union`). -/
def delUnion (n : MNode) (cv : Nat) : List Nat := SIS.Tree.bitsUnion n.lastBitmap (n.bitsOf cv)

/-- The node's last klong is a bitmap of the transaction's time t
(`hasTransDel`). -/
def hasTransDel (n : MNode) (t : Time) : Bool :=
  (match n.ks.getLast? with
    | some (.del _) => true
    | _ => false) && n.lastTime == some t

/-- The live klongs without compare value cv. -/
def dropCv (cv : Nat) (l : List (Nat × NodeId)) : List (Nat × NodeId) :=
  l.filter (fun a => a.1 != cv)

/-! ## Helpers: the live klongs under a larger bitmap -/

theorem dropCv_insertCv_same (cv : Nat) (y : NodeId) :
    ∀ m : List (Nat × NodeId), dropCv cv (insertCv cv y m) = dropCv cv m
  | [] => by simp [dropCv, insertCv]
  | (c', y') :: r => by
    unfold insertCv
    by_cases h1 : cv < c'
    · simp [dropCv, h1, show c' ≠ cv by omega]
    · by_cases h2 : cv = c'
      · subst h2
        simp [dropCv]
      · have ih := dropCv_insertCv_same cv y r
        simp only [dropCv] at ih
        simp [dropCv, h1, h2, Ne.symm h2, ih]

/-- Every klong of m is above c: `insertCv` puts c first. -/
theorem insertCv_front {c : Nat} {y : NodeId} :
    ∀ {m : List (Nat × NodeId)}, (∀ b ∈ m, c < b.1) → insertCv c y m = (c, y) :: m
  | [], _ => rfl
  | (c', y') :: r, h => by
    have := h (c', y') List.mem_cons_self
    simp only at this
    simp [insertCv, this]

theorem dropCv_insertCv_ne {cv c : Nat} (hc : c ≠ cv) (y : NodeId) :
    ∀ {m : List (Nat × NodeId)}, m.Pairwise CvLt →
      dropCv cv (insertCv c y m) = insertCv c y (dropCv cv m)
  | [], _ => by simp [dropCv, insertCv, hc]
  | (c', y') :: r, hs => by
    rw [List.pairwise_cons] at hs
    by_cases h1 : c < c'
    · rw [show insertCv c y ((c', y') :: r) = (c, y) :: (c', y') :: r by simp [insertCv, h1]]
      by_cases h3 : c' = cv
      · subst h3
        have e1 : dropCv c' ((c, y) :: (c', y') :: r) = (c, y) :: dropCv c' r := by
          simp [dropCv, hc]
        have e2 : dropCv c' ((c', y') :: r) = dropCv c' r := by simp [dropCv]
        rw [e1, e2, insertCv_front]
        intro b hb
        have := hs.1 b (List.mem_filter.mp hb).1
        unfold CvLt at this
        omega
      · have e1 : dropCv cv ((c, y) :: (c', y') :: r) = (c, y) :: (c', y') :: dropCv cv r := by
          simp [dropCv, hc, h3]
        have e2 : dropCv cv ((c', y') :: r) = (c', y') :: dropCv cv r := by simp [dropCv, h3]
        rw [e1, e2]
        simp [insertCv, h1]
    · by_cases h2 : c = c'
      · subst h2
        rw [show insertCv c y ((c, y') :: r) = (c, y) :: r by simp [insertCv]]
        have e1 : dropCv cv ((c, y) :: r) = (c, y) :: dropCv cv r := by simp [dropCv, hc]
        have e2 : dropCv cv ((c, y') :: r) = (c, y') :: dropCv cv r := by simp [dropCv, hc]
        rw [e1, e2]
        simp [insertCv]
      · rw [show insertCv c y ((c', y') :: r) = (c', y') :: insertCv c y r by
          simp [insertCv, h1, h2]]
        have ih := dropCv_insertCv_ne hc y hs.2
        by_cases h3 : c' = cv
        · subst h3
          have e1 : dropCv c' ((c', y') :: insertCv c y r) = dropCv c' (insertCv c y r) := by
            simp [dropCv]
          have e2 : dropCv c' ((c', y') :: r) = dropCv c' r := by simp [dropCv]
          rw [e1, e2, ih]
        · have e1 : dropCv cv ((c', y') :: insertCv c y r) =
              (c', y') :: dropCv cv (insertCv c y r) := by simp [dropCv, h3]
          have e2 : dropCv cv ((c', y') :: r) = (c', y') :: dropCv cv r := by simp [dropCv, h3]
          rw [e1, e2, ih]
          simp [insertCv, h1, h2]

/-- Two folds over one list keep a relation that each step for a member of
the list keeps; what follows from it at the end. -/
theorem foldl_sim_mem {α β γ : Type} (f : β → α → β) (g : γ → α → γ) (R P : β → γ → Prop)
    (hP : ∀ b c, R b c → P b c) :
    ∀ (l : List α), (∀ b c a, a ∈ l → R b c → R (f b a) (g c a)) →
      ∀ (b : β) (c : γ), R b c → P (l.foldl f b) (l.foldl g c)
  | [], _, b, c, h0 => hP b c h0
  | a :: l, h, b, c, h0 =>
    foldl_sim_mem f g R P hP l (fun b c a' ha' => h b c a' (List.mem_cons_of_mem _ ha'))
      (f b a) (g c a) (h b c a List.mem_cons_self h0)

/-- The live klongs under a bitmap U that deletes what D deletes and every
key klong of compare value cv: those under D without cv. -/
theorem liveWith_union (cv : Nat) (D U : List Nat) (L : List (Klong × Nat))
    (hU : ∀ c y i, (Klong.key c y, i) ∈ L → (i ∈ U ↔ i ∈ D ∨ c = cv)) :
    liveWith U L = dropCv cv (liveWith D L) := by
  unfold liveWith
  refine foldl_sim_mem _ _
    (fun (m m' : List (Nat × NodeId)) => m = dropCv cv m' ∧ m'.Pairwise CvLt)
    (fun m m' => m = dropCv cv m') (fun _ _ h => h.1) L ?_ [] [] ⟨rfl, List.Pairwise.nil⟩
  rintro m m' ⟨k, i⟩ hmem ⟨hm, hs⟩
  cases k with
  | time x => exact ⟨hm, hs⟩
  | del b => exact ⟨hm, hs⟩
  | key c y =>
    have hu := hU c y i hmem
    simp only [List.contains_iff_mem]
    by_cases hc : c = cv
    · subst hc
      have hiU : i ∈ U := hu.mpr (Or.inr rfl)
      simp only [hiU, ite_true]
      by_cases hiD : i ∈ D
      · simp only [hiD, ite_true]
        exact ⟨hm, hs⟩
      · simp only [hiD, ite_false]
        exact ⟨by rw [dropCv_insertCv_same, hm], insertCv_sorted _ _ hs⟩
    · have hiff : i ∈ U ↔ i ∈ D := by
        rw [hu]
        exact or_iff_left hc
      by_cases hiD : i ∈ D
      · simp only [hiD, hiff.mpr hiD, ite_true]
        exact ⟨hm, hs⟩
      · have hiU : i ∉ U := fun h => hiD (hiff.mp h)
        simp only [hiD, hiU, ite_false]
        exact ⟨by rw [dropCv_insertCv_ne hc y hs, hm], insertCv_sorted _ _ hs⟩

/-! ## Helpers: the klongs of the node -/

theorem cvAt_of_key {ks : List Klong} {i c : Nat} {y : NodeId} (h : ks[i]? = some (Klong.key c y)) :
    cvAt ks i = some c := by
  simp [cvAt, h]

theorem cvAt_lt {ks : List Klong} {j c : Nat} (h : cvAt ks j = some c) : j < ks.length := by
  unfold cvAt at h
  cases hj : ks[j]? with
  | none => rw [hj] at h; simp at h
  | some k => exact (List.getElem?_eq_some_iff.mp hj).1

theorem cvAt_snoc {ks : List Klong} {k : Klong} (hk : ∀ c y, k ≠ .key c y) (j : Nat) :
    cvAt (ks ++ [k]) j = cvAt ks j := by
  unfold cvAt
  by_cases hj : j < ks.length
  · rw [List.getElem?_append_left hj]
  · rw [List.getElem?_append_right (Nat.le_of_not_lt hj),
      List.getElem?_eq_none (Nat.le_of_not_lt hj)]
    cases hj2 : j - ks.length with
    | zero =>
      cases k with
      | key c y => exact absurd rfl (hk c y)
      | time t => rfl
      | del b => rfl
    | succ m => simp

theorem ksOf_getElem? (n : MNode) (i : Nat) : (ksOf n)[i]? = n.ks[i]?.map kOf := by
  simp [ksOf]

theorem mem_bitsOf {n : MNode} {cv j : Nat} : j ∈ n.bitsOf cv ↔ cvAt (ksOf n) j = some cv := by
  unfold SIS.Tree.KNode.bitsOf
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨⟨k, i⟩, hm, hf⟩
    have hi := List.mem_zipIdx_iff_getElem?.mp hm
    simp only at hi
    cases k with
    | key c' y' =>
      simp only at hf
      by_cases hc : c' = cv
      · simp only [hc, beq_self_eq_true, ite_true, Option.some.injEq] at hf
        subst hf
        simp [cvAt, ksOf_getElem?, hi, kOf, hc]
      · simp [hc] at hf
    | time x => simp at hf
    | del b => simp at hf
  · intro h
    unfold cvAt at h
    rw [ksOf_getElem?] at h
    cases hj : n.ks[j]? with
    | none => rw [hj] at h; simp at h
    | some k =>
      rw [hj] at h
      cases k with
      | key c y =>
        simp only [Option.map_some, kOf, Option.some.injEq] at h
        refine ⟨(SIS.Tree.Klong.key c y, j), List.mem_zipIdx_iff_getElem?.mpr hj, ?_⟩
        simp [h]
      | time x => simp [kOf] at h
      | del b => simp [kOf] at h

theorem mem_delUnion {n : MNode} {cv j : Nat} :
    j ∈ delUnion n cv ↔ j ∈ lastBitmap (ksOf n) ∨ cvAt (ksOf n) j = some cv := by
  unfold delUnion SIS.Tree.bitsUnion
  rw [List.mem_mergeSort, List.mem_eraseDups, List.mem_append, mem_bitsOf, lastBitmap_ksOf]
  rfl

/-- A key klong of the klongs of a list of indexed klongs. -/
theorem getElem?_of_mem_zipIdx {ks : List Klong} {k : Klong} {i : Nat} (h : (k, i) ∈ ks.zipIdx) :
    ks[i]? = some k :=
  List.mem_zipIdx_iff_getElem?.mp h

theorem union_cond (n : MNode) (cv : Nat) {L : List Klong}
    (hL : ∀ (i : Nat) (k : Klong), L[i]? = some k → (ksOf n)[i]? = some k) :
    ∀ c y i, (Klong.key c y, i) ∈ L.zipIdx →
      (i ∈ delUnion n cv ↔ i ∈ lastBitmap (ksOf n) ∨ c = cv) := by
  intro c y i hm
  have h1 := cvAt_of_key (hL i _ (getElem?_of_mem_zipIdx hm))
  rw [mem_delUnion, h1, Option.some.injEq]

theorem live_snoc_del (ks : List Klong) (U : List Nat) :
    live (ks ++ [.del U]) = liveWith U ks.zipIdx := by
  unfold live liveWith
  rw [lastBitmap_snoc, foldl_zipIdx_snoc]

theorem liveWith_snoc_time (d : List Nat) (ks : List Klong) (t : Time) :
    liveWith d (ks ++ [Klong.time t]).zipIdx = liveWith d ks.zipIdx := by
  unfold liveWith
  rw [foldl_zipIdx_snoc]

/-- One step of `liveWith`. -/
def liveStep (d : List Nat) (m : List (Nat × NodeId)) (ki : Klong × Nat) : List (Nat × NodeId) :=
  match ki.1 with
  | .key c y => if d.contains ki.2 then m else insertCv c y m
  | _ => m

theorem liveWith_snoc (d : List Nat) (L : List (Klong × Nat)) (x : Klong × Nat) :
    liveWith d (L ++ [x]) = liveStep d (liveWith d L) x := by
  unfold liveWith
  rw [List.foldl_append]
  obtain ⟨k, i⟩ := x
  cases k <;> rfl

theorem liveWith_nil_iff (d : List Nat) (L : List (Klong × Nat)) :
    liveWith d L = [] ↔ ∀ c y i, (Klong.key c y, i) ∈ L → i ∈ d := by
  induction L using List.reverseRecOn with
  | nil => simp [liveWith]
  | append_singleton L x ih =>
    rw [liveWith_snoc]
    obtain ⟨k, i⟩ := x
    cases k with
    | key c y =>
      unfold liveStep
      simp only [List.contains_iff_mem]
      by_cases hi : i ∈ d
      · simp only [hi, ite_true, ih, List.mem_append, List.mem_singleton]
        constructor
        · rintro h c' y' i' (h1 | h1)
          · exact h c' y' i' h1
          · simp only [Prod.mk.injEq, Klong.key.injEq] at h1
            rw [h1.2]
            exact hi
        · intro h c' y' i' h1
          exact h c' y' i' (Or.inl h1)
      · simp only [hi, ite_false]
        constructor
        · intro h
          exact absurd h (insertCv_ne_nil c y _)
        · intro h
          exact absurd (h c y i (List.mem_append_right _ List.mem_cons_self)) hi
    | time t =>
      simp only [liveStep, ih, List.mem_append, List.mem_singleton]
      constructor
      · rintro h c' y' i' (h1 | h1)
        · exact h c' y' i' h1
        · simp at h1
      · intro h c' y' i' h1
        exact h c' y' i' (Or.inl h1)
    | del b =>
      simp only [liveStep, ih, List.mem_append, List.mem_singleton]
      constructor
      · rintro h c' y' i' (h1 | h1)
        · exact h c' y' i' h1
        · simp at h1
      · intro h c' y' i' h1
        exact h c' y' i' (Or.inl h1)

/-- The node's last klong is the transaction's bitmap. -/
theorem hasTransDel_ks {n : MNode} {t : Time} (ht : hasTransDel n t = true) :
    ∃ ks0 B, n.ks = ks0 ++ [.del B] ∧ n.lastTime = some t := by
  unfold hasTransDel at ht
  rw [Bool.and_eq_true, beq_iff_eq] at ht
  rcases List.eq_nil_or_concat n.ks with h | ⟨L, b, h⟩
  · rw [h] at ht
    simp at ht
  · rw [h] at ht
    simp only [List.concat_eq_append, List.getLast?_append, List.getLast?_singleton,
      Option.some_or] at ht h
    cases b with
    | del B => exact ⟨L, B, h, ht.2⟩
    | time x => simp at ht
    | key c y => simp at ht

theorem setAt_last {n : MNode} {ks0 : List MKlong} {k : MKlong} (h : n.ks = ks0 ++ [k])
    (k' : MKlong) : (n.setAt (n.size - 1) k').ks = ks0 ++ [k'] := by
  unfold SIS.Tree.KNode.setAt SIS.Tree.KNode.size
  rw [h]
  simp

/-! ## Helpers: well-formed bitmaps -/

theorem bitmapOk_iff_all {ks : List Klong} {i : Nat} {before bits : List Nat} :
    bitmapOk ks i before bits = true ↔
      (∀ j ∈ bits, j < i ∧ (cvAt ks j).isSome = true) ∧ (∀ j ∈ before, j ∈ bits) ∧
      (∀ j ∈ bits, ∀ j', j' < j → cvAt ks j' = cvAt ks j → j' ∈ bits) := by
  simp only [bitmapOk, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, List.mem_range,
    Bool.or_eq_true, bne_iff_ne, ne_eq, List.contains_iff_mem]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    refine ⟨h1, h2, fun j hj j' hlt heq => ?_⟩
    rcases h3 j hj j' hlt with h | h
    · exact absurd heq h
    · exact h
  · rintro ⟨h1, h2, h3⟩
    refine ⟨⟨h1, h2⟩, fun j hj j' hlt => ?_⟩
    by_cases heq : cvAt ks j' = cvAt ks j
    · exact Or.inr (h3 j hj j' hlt heq)
    · exact Or.inl heq

theorem bmFold_append (ks0 l : List Klong) (init : Bool × List Nat) :
    ks0.zipIdx.foldl (fun acc ki => bmStep (ks0 ++ l) acc ki.1 ki.2) init =
      ks0.zipIdx.foldl (fun acc ki => bmStep ks0 acc ki.1 ki.2) init := by
  apply List.foldl_ext
  rintro acc ⟨k', i⟩ hm
  have hi := (List.mem_zipIdx hm).2.1
  cases k' with
  | del b =>
    simp only [bmStep]
    rw [bitmapOk_append (by omega)]
  | time t => rfl
  | key c y => rfl

theorem bitmapsOk_snoc_del (ks : List Klong) (U : List Nat) :
    bitmapsOk (ks ++ [.del U]) =
      (bitmapsOk ks && bitmapOk (ks ++ [.del U]) ks.length (lastBitmap ks) U) := by
  unfold bitmapsOk
  rw [foldl_zipIdx_snoc, bmFold_append]
  have e := (bmFold_spec ks ks).1
  generalize ks.zipIdx.foldl (fun acc ki => bmStep ks acc ki.1 ki.2) (true, []) = F at e ⊢
  rw [← e]
  rfl

theorem timesOk_snoc_del {ks : List Klong} (hne : ks ≠ []) (b : List Nat) :
    timesOk (ks ++ [.del b]) = timesOk ks := by
  rw [timesOk_eq, timesOk_eq, List.foldl_append, List.foldl_cons, List.foldl_nil,
    headOk_append hne]
  rfl

/-- A bitmap that holds B, and every key klong of compare value cv, set after
klongs where B is well formed: it is well formed there. -/
theorem bitmapOk_union {ks0 : List Klong} {before B U : List Nat} {cv : Nat}
    (hB : ∀ j ∈ B, j < ks0.length ∧ (cvAt ks0 j).isSome = true ∧
      ∀ j', j' < j → cvAt ks0 j' = cvAt ks0 j → j' ∈ B)
    (hbefore : ∀ j ∈ before, j ∈ B) (hU : ∀ j, j ∈ U ↔ j ∈ B ∨ cvAt ks0 j = some cv) :
    bitmapOk (ks0 ++ [.del U]) ks0.length before U = true := by
  have hcv : ∀ j, cvAt (ks0 ++ [.del U]) j = cvAt ks0 j := cvAt_snoc (by simp)
  rw [bitmapOk_iff_all]
  simp only [hcv]
  refine ⟨fun j hj => ?_, fun j hj => (hU j).mpr (Or.inl (hbefore j hj)), fun j hj j' hlt heq => ?_⟩
  · rcases (hU j).mp hj with h | h
    · exact ⟨(hB j h).1, (hB j h).2.1⟩
    · exact ⟨cvAt_lt h, by rw [h]; rfl⟩
  · rcases (hU j).mp hj with h | h
    · exact (hU j').mpr (Or.inl ((hB j h).2.2 j' hlt heq))
    · exact (hU j').mpr (Or.inr (heq.trans h))

theorem klongsWf_snoc_union {ks1 : List Klong} (h : klongsWf ks1 = true) (hne : ks1 ≠ [])
    {B U : List Nat} {cv : Nat}
    (hB : ∀ j ∈ B, j < ks1.length ∧ (cvAt ks1 j).isSome = true ∧
      ∀ j', j' < j → cvAt ks1 j' = cvAt ks1 j → j' ∈ B)
    (hbefore : ∀ j ∈ lastBitmap ks1, j ∈ B) (hU : ∀ j, j ∈ U ↔ j ∈ B ∨ cvAt ks1 j = some cv) :
    klongsWf (ks1 ++ [.del U]) = true := by
  simp only [klongsWf, Bool.and_eq_true] at h ⊢
  rw [timesOk_snoc_del hne, bitmapsOk_snoc_del, h.2, Bool.true_and]
  exact ⟨h.1, bitmapOk_union hB hbefore hU⟩

/-- The last bitmap of well-formed klongs: W2 and W4. -/
theorem lastBitmap_facts {ks : List Klong} (h : klongsWf ks = true) :
    ∀ j ∈ lastBitmap ks, j < ks.length ∧ (cvAt ks j).isSome = true ∧
      ∀ j', j' < j → cvAt ks j' = cvAt ks j → j' ∈ lastBitmap ks := by
  simp only [klongsWf, Bool.and_eq_true] at h
  rcases lastBitmap_cases ks with h0 | ⟨l1, b, l2, he, hb⟩
  · simp [h0]
  · have hok := (bmFold_spec ks ks).2 h.2 l1 b l2 he
    rw [bitmapOk_iff_all] at hok
    rw [hb]
    intro j hj
    have hl : l1.length < ks.length := by rw [he]; simp
    exact ⟨lt_trans (hok.1 j hj).1 hl, (hok.1 j hj).2, hok.2.2 j hj⟩

/-! ## A new bitmap klong -/

theorem addDel_live {n : MNode} {t : Time} (_hwf : klongsWf (ksOf n) = true) (cv : Nat) :
    live (ksOf (n.add t (.del (delUnion n cv)))) = dropCv cv (live (ksOf n)) := by
  have hU := union_cond n cv (L := ksOf n) (fun _ _ h => h)
  rcases ksOf_add n t (.del (delUnion n cv)) with ⟨h, _⟩ | ⟨h, _⟩
  · rw [h, show ksOf n ++ [Klong.time t, kOf (.del (delUnion n cv))] =
        (ksOf n ++ [Klong.time t]) ++ [Klong.del (delUnion n cv)] by simp [kOf],
      live_snoc_del, liveWith_snoc_time, liveWith_union cv _ _ _ hU]
    rfl
  · rw [h, show kOf (.del (delUnion n cv)) = Klong.del (delUnion n cv) from rfl, live_snoc_del,
      liveWith_union cv _ _ _ hU]
    rfl

theorem addDel_wf {n : MNode} {t : Time} (hwf : klongsWf (ksOf n) = true) (cv : Nat) :
    klongsWf (ksOf (n.add t (.del (delUnion n cv)))) = true := by
  have hD := lastBitmap_facts hwf
  have hUm : ∀ j, j ∈ delUnion n cv ↔ j ∈ lastBitmap (ksOf n) ∨ cvAt (ksOf n) j = some cv :=
    fun j => mem_delUnion
  rcases ksOf_add n t (.del (delUnion n cv)) with ⟨h, hl⟩ | ⟨h, lt, hl, _⟩
  · rw [h, show ksOf n ++ [Klong.time t, kOf (.del (delUnion n cv))] =
        (ksOf n ++ [Klong.time t]) ++ [Klong.del (delUnion n cv)] by simp [kOf]]
    have hcv : ∀ j, cvAt (ksOf n ++ [Klong.time t]) j = cvAt (ksOf n) j := cvAt_snoc (by simp)
    refine klongsWf_snoc_union (B := lastBitmap (ksOf n)) (cv := cv)
      (klongsWf_append_time_of hwf (fun t0 h0 => hl t0 (by rw [← lastT_ksOf]; exact h0)))
      (by simp) ?_ ?_ ?_
    · intro j hj
      simp only [hcv, List.length_append, List.length_singleton]
      obtain ⟨h1, h2, h3⟩ := hD j hj
      exact ⟨by omega, h2, h3⟩
    · intro j hj
      rw [lastBitmap_snoc] at hj
      exact hj
    · intro j
      rw [hcv]
      exact hUm j
  · rw [h]
    exact klongsWf_snoc_union hwf (ksOf_ne_nil hl) hD (fun j hj => hj) hUm

/-- The key klongs are kept. -/
theorem addDel_key_mem {n : MNode} {t : Time} {bits : List Nat} {c : Nat} {y : NodeId} :
    Klong.key c y ∈ ksOf (n.add t (.del bits)) ↔ Klong.key c y ∈ ksOf n := by
  rcases ksOf_add n t (.del bits) with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> simp [kOf]

/-! ## The transaction's own bitmap, in place -/

theorem setDel_live {n : MNode} {t : Time} (_hwf : klongsWf (ksOf n) = true)
    (ht : hasTransDel n t = true) (cv : Nat) :
    live (ksOf (n.setAt (n.size - 1) (.del (delUnion n cv)))) = dropCv cv (live (ksOf n)) := by
  obtain ⟨ks0, B, hks, _⟩ := hasTransDel_ks ht
  have hn : ksOf n = ks0.map kOf ++ [Klong.del B] := by simp [ksOf, hks, kOf]
  have hs : ksOf (n.setAt (n.size - 1) (.del (delUnion n cv))) =
      ks0.map kOf ++ [Klong.del (delUnion n cv)] := by
    simp [ksOf, setAt_last hks, kOf]
  have hU := union_cond n cv (L := ks0.map kOf) (fun i k h => by
    rw [hn, List.getElem?_append_left (List.getElem?_eq_some_iff.mp h).1]
    exact h)
  rw [hs, live_snoc_del, liveWith_union cv _ _ _ hU, hn, live_snoc_del, lastBitmap_snoc]

theorem setDel_wf {n : MNode} {t : Time} (hwf : klongsWf (ksOf n) = true)
    (ht : hasTransDel n t = true) (cv : Nat) :
    klongsWf (ksOf (n.setAt (n.size - 1) (.del (delUnion n cv)))) = true := by
  obtain ⟨ks0, B, hks, hlt⟩ := hasTransDel_ks ht
  have hn : ksOf n = ks0.map kOf ++ [Klong.del B] := by simp [ksOf, hks, kOf]
  have hs : ksOf (n.setAt (n.size - 1) (.del (delUnion n cv))) =
      ks0.map kOf ++ [Klong.del (delUnion n cv)] := by
    simp [ksOf, setAt_last hks, kOf]
  rw [hs]
  have hne : ks0.map kOf ≠ [] := by
    intro h0
    have := lastT_mem (show lastT (ksOf n) = some t by rw [lastT_ksOf]; exact hlt)
    rw [hn, h0] at this
    simp at this
  have hwf' := hwf
  rw [hn] at hwf'
  simp only [klongsWf, Bool.and_eq_true] at hwf'
  rw [timesOk_snoc_del hne, bitmapsOk_snoc_del, Bool.and_eq_true] at hwf'
  obtain ⟨hto, hbo, hok⟩ := hwf'
  rw [bitmapOk_iff_all] at hok
  have hcv : ∀ j, cvAt (ks0.map kOf ++ [Klong.del B]) j = cvAt (ks0.map kOf) j :=
    cvAt_snoc (by simp)
  simp only [hcv] at hok
  refine klongsWf_snoc_union (B := B) (cv := cv) (by simp [klongsWf, hto, hbo]) hne ?_ hok.2.1 ?_
  · intro j hj
    exact ⟨(hok.1 j hj).1, (hok.1 j hj).2, hok.2.2 j hj⟩
  · intro j
    rw [mem_delUnion, hn]
    simp only [lastBitmap_snoc, hcv]

theorem setDel_key_mem {n : MNode} {t : Time} (ht : hasTransDel n t = true) {bits : List Nat}
    {c : Nat} {y : NodeId} :
    Klong.key c y ∈ ksOf (n.setAt (n.size - 1) (.del bits)) ↔ Klong.key c y ∈ ksOf n := by
  obtain ⟨ks0, B, hks, _⟩ := hasTransDel_ks ht
  unfold ksOf
  rw [setAt_last hks, hks]
  simp [kOf]

theorem setDel_size (n : MNode) (bits : List Nat) :
    (n.setAt (n.size - 1) (.del bits)).size = n.size := by
  unfold SIS.Tree.KNode.size SIS.Tree.KNode.setAt
  simp

theorem setDel_leaf (n : MNode) (bits : List Nat) :
    (n.setAt (n.size - 1) (.del bits)).leaf = n.leaf := by
  rfl

theorem setDel_timesLe {n : MNode} {t : Time} (h : TimesLe n t) (bits : List Nat) :
    TimesLe (n.setAt (n.size - 1) (.del bits)) t := by
  intro t' ht'
  have e : ksOf (n.setAt (n.size - 1) (.del bits)) =
      (ksOf n).set (n.size - 1) (Klong.del bits) := by
    simp [ksOf, SIS.Tree.KNode.setAt, List.map_set, kOf]
  rw [e] at ht'
  rcases List.mem_or_eq_of_mem_set ht' with h1 | h1
  · exact h t' h1
  · simp at h1

/-- A first time klong stays the first (the node has two klongs or more: a
time klong of t and its bitmap). -/
theorem setDel_first {n : MNode} {t t0 : Time} {rest : List MKlong} (ht : hasTransDel n t = true)
    (h : n.ks = .time t0 :: rest) (bits : List Nat) :
    ∃ rest', (n.setAt (n.size - 1) (.del bits)).ks = .time t0 :: rest' := by
  obtain ⟨ks0, B, hks, _⟩ := hasTransDel_ks ht
  rw [setAt_last hks]
  cases ks0 with
  | nil =>
    rw [h] at hks
    simp at hks
  | cons k r =>
    rw [h] at hks
    simp only [List.cons_append, List.cons.injEq] at hks
    rw [← hks.1]
    exact ⟨_, rfl⟩

/-- The frame: the bitmap set in place is a klong after the time klong of i. -/
theorem setDel_ext {n : MNode} {i : Time} {ks0 : List Klong}
    (h0 : ∀ t, Klong.time t ∈ ks0 → t < i) (ht : hasTransDel n i = true)
    (h : ksOf n = ks0 ∨ ∃ more, ksOf n = ks0 ++ Klong.time i :: more) (bits : List Nat) :
    ∃ more, ksOf (n.setAt (n.size - 1) (.del bits)) = ks0 ++ Klong.time i :: more := by
  obtain ⟨ks1, B, hks, hlt⟩ := hasTransDel_ks ht
  have hn : ksOf n = ks1.map kOf ++ [Klong.del B] := by simp [ksOf, hks, kOf]
  have hs : ksOf (n.setAt (n.size - 1) (.del bits)) = ks1.map kOf ++ [Klong.del bits] := by
    simp [ksOf, setAt_last hks, kOf]
  rw [hs]
  rcases h with h | ⟨more, h⟩
  · exfalso
    have := lastT_mem (show lastT (ksOf n) = some i by rw [lastT_ksOf]; exact hlt)
    rw [h] at this
    exact Nat.lt_irrefl _ (h0 i this)
  · rw [hn] at h
    rcases snoc_eq_append_cons h with ⟨_, _, h3⟩ | ⟨l2', _, h2⟩
    · simp at h3
    · exact ⟨l2' ++ [Klong.del bits], by rw [h2]; simp⟩

/-! ## The writer's tests -/

/-- `Dag.allKeysIn` of the union: no live klong is left. -/
theorem allKeysIn_iff {n : MNode} (_hwf : klongsWf (ksOf n) = true) (cv : Nat) :
    n.allKeysIn (delUnion n cv) = true ↔ dropCv cv (live (ksOf n)) = [] := by
  have hU := union_cond n cv (L := ksOf n) (fun _ _ h => h)
  rw [show live (ksOf n) = liveWith (lastBitmap (ksOf n)) (ksOf n).zipIdx from rfl,
    ← liveWith_union cv _ _ _ hU, liveWith_nil_iff]
  unfold SIS.Tree.KNode.allKeysIn
  rw [List.all_eq_true]
  constructor
  · intro hall c y i hm
    have h1 := getElem?_of_mem_zipIdx hm
    rw [ksOf_getElem?] at h1
    obtain ⟨k, hk, hkk⟩ := Option.map_eq_some_iff.mp h1
    have := hall (k, i) (List.mem_zipIdx_iff_getElem?.mpr hk)
    cases k with
    | key c' y' => simpa using this
    | time x => simp [kOf] at hkk
    | del b => simp [kOf] at hkk
  · rintro hall ⟨k, i⟩ hm
    have hk := List.mem_zipIdx_iff_getElem?.mp hm
    simp only at hk
    cases k with
    | key c y =>
      have := hall c y i (List.mem_zipIdx_iff_getElem?.mpr (by rw [ksOf_getElem?, hk]; rfl))
      simpa using this
    | time x => rfl
    | del b => rfl

/-- The delete is a noop for the writer (the union is the last bitmap) only
if the node has no live klong of the compare value. -/
theorem delUnion_noop {n : MNode} (_hwf : klongsWf (ksOf n) = true) {cv : Nat}
    (h : (delUnion n cv == n.lastBitmap) = true) : dropCv cv (live (ksOf n)) = live (ksOf n) := by
  have hU := union_cond n cv (L := ksOf n) (fun _ _ h => h)
  have he : delUnion n cv = lastBitmap (ksOf n) := by
    rw [lastBitmap_ksOf]
    exact beq_iff_eq.mp h
  rw [show live (ksOf n) = liveWith (lastBitmap (ksOf n)) (ksOf n).zipIdx from rfl,
    ← liveWith_union cv _ _ _ hU, he]

/-- The model's live klongs are the contract's. -/
theorem mlive_eq (n : MNode) : n.live = live (ksOf n) := by
  have hv := lastVersion_ks (n := n) 0
  have hks : (n.lastVersion 0).ks = SIS.Tree.Klong.time 0 ::
      (live (ksOf n)).map (fun cy => SIS.Tree.Klong.key cy.1 cy.2) := by
    apply List.map_injective_iff.mpr kOf_injective
    rw [show (n.lastVersion 0).ks.map kOf = ksOf (n.lastVersion 0) from rfl, hv]
    simp [kOf]
  unfold SIS.Tree.KNode.live
  rw [hks]
  simp

end Contract
