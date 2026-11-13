/-
Proofs for bounds, part 2 (bergdb item 007): T4's debt with BergDB's
still-dirty test (`DebtByChains`, SIS/BoundT4Java.lean). Added 2026-11-13.

The argument, by induction on the level. A node y of D after T(j), with
d(y) = i + 1, got into D in step 3 of T(i + 1), on the access path of the
change (or touched), or in step 7 of T(i + 1): taken and put back because a
pointee y1 of y, live or dead, was in D then (`step_r7_java`), so in D after
T(i + 1), on a lower level (A4). The induction gives y1 a node below it on the
access path of a change of the last lev(y1) + 1 sections before i + 1, which
are within the last lev(y) + 1 sections before j, since s(j) < i + 1.
-/
import SIS.BoundT4Java
import SIS.Proof.BoundT4Tree

set_option linter.unusedSectionVars false

namespace SIS

variable {V T : Type} [DecidableEq V]

/-! ### Step 7 with BergDB's test -/

section Fold

variable (al : Algo V T) (S : Stream V T) (P : Struct V) (i : Time)

/-- Step 7's fold keeps what D held. -/
theorem fold7_sub : ∀ (l : List NodeId) (D : Dirty) (L : List NodeId), ∀ e ∈ D,
    e ∈ (l.foldl (fun (acc : Dirty × List NodeId) x =>
      if al.stillDirty S P acc.1 i x then (acc.1 ++ [(x, i)], acc.2 ++ [x]) else acc) (D, L)).1 := by
  intro l
  induction l with
  | nil => intro D L e he; exact he
  | cons y l ih =>
    intro D L e he
    simp only [List.foldl_cons]
    split
    · exact ih _ _ e (List.mem_append_left _ he)
    · exact ih _ _ e he

/-- A node that step 7's fold puts back passed the test with a D that the
fold's result holds. -/
theorem fold7_test : ∀ (l : List NodeId) (D : Dirty) (L : List NodeId) (x : NodeId),
    x ∈ (l.foldl (fun (acc : Dirty × List NodeId) x =>
      if al.stillDirty S P acc.1 i x then (acc.1 ++ [(x, i)], acc.2 ++ [x]) else acc) (D, L)).2 →
    x ∈ L ∨ ∃ D' : Dirty, (∀ e ∈ D', e ∈ (l.foldl (fun (acc : Dirty × List NodeId) x =>
      if al.stillDirty S P acc.1 i x then (acc.1 ++ [(x, i)], acc.2 ++ [x]) else acc) (D, L)).1) ∧
      al.stillDirty S P D' i x = true := by
  intro l
  induction l with
  | nil => intro D L x h; exact Or.inl h
  | cons y l ih =>
    intro D L x h
    simp only [List.foldl_cons] at h ⊢
    by_cases hy : al.stillDirty S P D i y = true
    · simp only [hy, ite_true] at h ⊢
      rcases ih _ _ x h with h1 | h1
      · rcases List.mem_append.mp h1 with h2 | h2
        · exact Or.inl h2
        · rw [List.mem_singleton] at h2
          subst h2
          exact Or.inr ⟨D, fun e he => fold7_sub al S P i l _ _ e (List.mem_append_left _ he), hy⟩
      · exact Or.inr h1
    · simp only [hy, Bool.false_eq_true, ite_false] at h ⊢
      exact ih D L x h

end Fold

section Step

variable {sp : Spec V T} {al : Algo V T} {db : DB V T} {tr : T}

/-- With BergDB's test, a node that step 7 puts back has a pointee, live or
dead, that is in D after the step. -/
theorem step_r7_java (hj : al.stillDirty = javaTest sp) {k : Nat} (hinv : Inv sp db k)
    {x : NodeId} (hx : x ∈ (parts sp al db tr).r7.2) :
    ∃ n, (parts sp al db tr).P.get? x = some n ∧
      ∃ y ∈ pointees sp n.hist, inD (parts sp al db tr).r7.1 y = true := by
  have ht : x ∈ (parts sp al db tr).taken := (step_r7_shape sp al db tr hinv.len).2.subset hx
  obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp
    (isSome_of_isIndex (step_taken_index sp al db tr hinv ht))
  refine ⟨n, hn, ?_⟩
  rw [parts_r7] at hx ⊢
  unfold stillDirtyOf at hx ⊢
  rcases fold7_test al _ _ _ _ _ _ x hx with h | ⟨D', hsub, htest⟩
  · cases h
  · rw [hj] at htest
    unfold javaTest at htest
    rw [hn] at htest
    simp only [List.any_eq_true] at htest
    obtain ⟨y, hy, hyD⟩ := htest
    refine ⟨y, hy, ?_⟩
    rw [inD_iff] at hyD ⊢
    obtain ⟨d, hd⟩ := hyD
    exact ⟨d, hsub _ hd⟩

end Step

/-! ### The induction -/

section Chain

variable {sp : Spec V T} {al : Algo V T} {ts : List T}

/-- The entries of a node of a state are entries of the node in a later state. -/
theorem st_hist_sub (hok : RunOK sp al ts) (hst : AlgOK sp al) {j K : Nat} (hjK : j ≤ K)
    (hK : K ≤ ts.length) {y : NodeId} {n : Node V} (hn : (st sp al ts j).P.get? y = some n) :
    ∃ nK, (st sp al ts K).P.get? y = some nK ∧ nK.level = n.level ∧ ∀ e ∈ n.hist, e ∈ nK.hist := by
  have hinvj := inv_st sp al ts hok hst j (by omega)
  obtain ⟨nK, hnK, hl, -, hh⟩ := st_grow sp al ts hok hst hjK hK y n hn
  refine ⟨nK, hnK, hl, fun e he => ?_⟩
  have he' : e ∈ n.hist.upTo j := mem_upTo.mpr ⟨he, hinvj.times y n hn e he⟩
  rw [← hh] at he'
  exact (mem_upTo.mp he').1

/-- The induction (BergDB's test), in the state after T(K): a node y of D after
T(j), j ≤ K, reaches through pointers a node on the access path of the change
of some T(τ), spIter (lev y + 1) j < τ ≤ j; for the nodes on levels below b, by
induction on b. -/
theorem java_chain (hok : RunOK sp al ts) (hst : AlgOK sp al) (hj : al.stillDirty = javaTest sp)
    {K : Nat} (hK : K ≤ ts.length) : ∀ b, ∀ y, levelOf (st sp al ts K).P y < b →
      ∀ j ≤ K, ∀ d, (y, d) ∈ (st sp al ts j).D →
      ∃ τ z, spIter (st sp al ts K).S (levelOf (st sp al ts K).P y + 1) j < τ ∧ τ ≤ j ∧
        PtrBelow sp (st sp al ts K).P y z ∧ onAccessPath sp al ts τ z := by
  have hle := spAt_st_le hok hst hK
  have hmono := spAt_st_mono hok hst hK
  intro b
  induction b with
  | zero => intro y h; omega
  | succ b ih =>
    intro y hyb j hjK d hyd
    have hinvj := inv_st sp al ts hok hst j (by omega)
    have hyd' := hyd
    rw [hinvj.inv1] at hyd'
    obtain ⟨hsd, hdl, R, hR, hyR⟩ := sectionD_mem hyd'
    have hlenj := hinvj.len
    obtain ⟨i, rfl⟩ : ∃ i, d = i + 1 := ⟨d - 1, by omega⟩
    have hi : i < ts.length := by omega
    rw [st_rec hok hst (i := i) (j := j) (by omega) (by omega), Option.some.injEq] at hR
    subst hR
    rw [parts_R] at hyR
    have hsj : spAt (st sp al ts K).S j = lastSp (st sp al ts j).S := spAt_st hok hst hK hjK
    have hsplit : spIter (st sp al ts K).S (levelOf (st sp al ts K).P y + 1) j =
        spIter (st sp al ts K).S (levelOf (st sp al ts K).P y) (spAt (st sp al ts K).S j) := rfl
    rcases List.mem_append.mp hyR with hg3 | hr7
    · have h1 := spIter_le (st sp al ts K).S K hle (levelOf (st sp al ts K).P y)
        (spAt (st sp al ts K).S j) (by have := hle j hjK; omega)
      exact ⟨i + 1, y, by omega, by omega, PtrBelow.refl y, onAccessPath_gd3 hok hst hi hg3⟩
    · have hinvi := inv_st sp al ts hok hst i (by omega)
      obtain ⟨n, hn, y1, hy1, hy1D⟩ := step_r7_java hj hinvi hr7
      have hPn : (parts sp al (st sp al ts i) ts[i]).P = (st sp al ts (i + 1)).P := by
        rw [st_succ sp al ts hi]; rfl
      have hDn : (parts sp al (st sp al ts i) ts[i]).r7.1 = (st sp al ts (i + 1)).D := by
        rw [st_succ sp al ts hi]; rfl
      rw [hPn] at hn
      rw [hDn, inD_iff] at hy1D
      obtain ⟨d1, hd1⟩ := hy1D
      have hinv1 := inv_st sp al ts hok hst (i + 1) (by omega)
      obtain ⟨e, he, hye⟩ := (mem_pointees sp n.hist y1).mp hy1
      obtain ⟨m1, hm1, hlt⟩ := hinv1.ptrs y n hn e he y1 hye
      obtain ⟨nK, hnK, hnKl, hnKh⟩ := st_hist_sub hok hst (j := i + 1) (K := K) (by omega) hK hn
      obtain ⟨mK, hmK, hmKl, -⟩ := st_hist_sub hok hst (j := i + 1) (K := K) (by omega) hK hm1
      have hly : levelOf (st sp al ts K).P y = n.level := by rw [levelOf_of_get hnK, hnKl]
      have hly1 : levelOf (st sp al ts K).P y1 = m1.level := by rw [levelOf_of_get hmK, hmKl]
      obtain ⟨τ, z, h1, h2, h3, h4⟩ := ih y1 (by omega) (i + 1) (by omega) d1 hd1
      refine ⟨τ, z, ?_, by omega, PtrBelow.step nK hnK ?_ h3, h4⟩
      · have hm := spIter_mono (st sp al ts K).S K hle hmono (levelOf (st sp al ts K).P y)
          (spAt (st sp al ts K).S j) (i + 1) (by omega) (by omega)
        have ha := spIter_anti (st sp al ts K).S K hle hmono (i + 1) (by omega)
          (levelOf (st sp al ts K).P y - (levelOf (st sp al ts K).P y1 + 1))
          (levelOf (st sp al ts K).P y1 + 1)
        rw [show levelOf (st sp al ts K).P y1 + 1 +
          (levelOf (st sp al ts K).P y - (levelOf (st sp al ts K).P y1 + 1)) =
            levelOf (st sp al ts K).P y by omega] at ha
        omega
      · exact (mem_pointees sp nK.hist y1).mpr ⟨e, hnKh e he, hye⟩

end Chain

/-- T4, the debt of D, with BergDB's test. -/
theorem debtByChains_java (sp : Spec V T) (al : Algo V T) (ts : List T) (hok : RunOK sp al ts)
    (hj : al.stillDirty = javaTest sp) : DebtByChains sp al ts := by
  have hst : AlgOK sp al := algOK_of sp al (Or.inl hj)
  have hK : ts.length ≤ ts.length := Nat.le_refl _
  show ∀ e ∈ (run sp al ts).D, ∃ τ z,
    spIter (run sp al ts).S (levelOf (run sp al ts).P e.1 + 1) ts.length < τ ∧ τ ≤ ts.length ∧
      PtrBelow sp (run sp al ts).P e.1 z ∧ onAccessPath sp al ts τ z
  rw [← st_length sp al ts]
  rintro ⟨x, d⟩ hxd
  exact java_chain hok hst hj hK (levelOf (st sp al ts ts.length).P x + 1) x (by omega)
    ts.length hK d hxd

/-! ### Counting -/

section Count

variable {sp : Spec V T} {P : Struct V}

theorem mem_ptrParents {z x : NodeId} :
    x ∈ ptrParents sp P z ↔ ∃ n, P.get? x = some n ∧ z ∈ pointees sp n.hist := by
  unfold ptrParents
  rw [List.mem_filter, mem_allIds]
  constructor
  · rintro ⟨-, h⟩
    cases hx : P.get? x with
    | none => rw [hx] at h; cases h
    | some n => rw [hx] at h; exact ⟨n, rfl, by simpa using h⟩
  · rintro ⟨n, hn, hz⟩
    rw [hn]
    exact ⟨rfl, by simpa using hz⟩

/-- `PtrBelow` from its bottom: z itself, or below a pointer parent of z. -/
theorem ptrBelow_last {x z : NodeId} (h : PtrBelow sp P x z) :
    x = z ∨ ∃ p ∈ ptrParents sp P z, PtrBelow sp P x p := by
  induction h with
  | refl x => exact Or.inl rfl
  | @step x y z n hn hy _ ih =>
    rcases ih with rfl | ⟨p, hp, hyp⟩
    · exact Or.inr ⟨x, mem_ptrParents.mpr ⟨n, hn, hy⟩, PtrBelow.refl x⟩
    · exact Or.inr ⟨p, hp, PtrBelow.step n hn hy hyp⟩

/-- A pointer parent is on a higher level (A4). -/
theorem ptrParents_level (hp : PtrsOK sp P) {z p : NodeId} (h : p ∈ ptrParents sp P z) :
    levelOf P z < levelOf P p := by
  obtain ⟨n, hn, hz⟩ := mem_ptrParents.mp h
  obtain ⟨e, he, hze⟩ := (mem_pointees sp n.hist z).mp hz
  obtain ⟨m, hm, hlt⟩ := hp p n hn e he z hze
  rw [levelOf_of_get hn, levelOf_of_get hm]
  exact hlt

theorem ptrBelow_level (hp : PtrsOK sp P) {x z : NodeId} (h : PtrBelow sp P x z) :
    levelOf P z ≤ levelOf P x := by
  induction h with
  | refl x => exact Nat.le_refl _
  | @step x y z n hn hy _ ih =>
    have := ptrParents_level hp (mem_ptrParents.mpr ⟨n, hn, hy⟩)
    omega

/-- The nodes on levels up to H that reach z through pointers, without repeats,
are at most 1 + Q + ... + Q^m if H ≤ lev z + m and every node has at most Q
pointer parents. -/
theorem ptrAnc_count (hp : PtrsOK sp P) (Q H : Nat) (hQ : ∀ z, (ptrParents sp P z).length ≤ Q) :
    ∀ m z (L : List NodeId), H ≤ levelOf P z + m → L.Nodup →
      (∀ x ∈ L, PtrBelow sp P x z ∧ levelOf P x ≤ H) → L.length ≤ geomSum Q m := by
  intro m
  induction m with
  | zero =>
    intro z L hH hnd hL
    have key : ∀ x ∈ L, x = z := by
      intro x hx
      obtain ⟨hb, hl⟩ := hL x hx
      rcases ptrBelow_last hb with h | ⟨p, hpp, hxp⟩
      · exact h
      · exfalso
        have h1 := ptrParents_level hp hpp
        have h2 := ptrBelow_level hp hxp
        omega
    exact length_le_one_of_nodup hnd (fun a ha b hb => by rw [key a ha, key b hb])
  | succ m ih =>
    intro z L hH hnd hL
    rw [length_filter_add L (fun x => x == z)]
    have h1 : (L.filter (fun x => x == z)).length ≤ 1 :=
      length_le_one_of_nodup (hnd.filter _) (fun a ha b hb => by
        simp only [List.mem_filter, beq_iff_eq] at ha hb
        rw [ha.2, hb.2])
    have h2 := nodup_length_le_sum
      (fun p x => p ∈ ptrParents sp P z ∧ PtrBelow sp P x p ∧ levelOf P x ≤ H)
      (fun _ => geomSum Q m)
      (fun p L' hnd' hL' => by
        cases L' with
        | nil => exact Nat.zero_le _
        | cons x0 L'' =>
          have hpp := (hL' x0 (by simp)).1
          have := ptrParents_level hp hpp
          exact ih p (x0 :: L'') (by omega) hnd' (fun x hx => (hL' x hx).2))
      (ptrParents sp P z) (L.filter (fun x => !(x == z))) (hnd.filter _) (by
        intro x hx
        obtain ⟨hxL, hne⟩ := List.mem_filter.mp hx
        obtain ⟨hb, hl⟩ := hL x hxL
        rcases ptrBelow_last hb with h | ⟨p, hpp, hxp⟩
        · simp [h] at hne
        · exact ⟨p, hpp, hpp, hxp, hl⟩)
    rw [sum_map_const] at h2
    have h3 := Nat.mul_le_mul_right (geomSum Q m) (hQ z)
    show _ ≤ 1 + Q * geomSum Q m
    omega

/-- The nodes on levels up to H that reach a node with property A through
pointers, without repeats: at most NA (1 + Q + ... + Q^H), if every list of
distinct nodes with A has at most NA nodes. -/
theorem ptrAnc_count_set (hp : PtrsOK sp P) (Q H : Nat) (hQ : ∀ z, (ptrParents sp P z).length ≤ Q)
    (A : NodeId → Prop) (NA : Nat)
    (hA : ∀ Z : List NodeId, Z.Nodup → (∀ z ∈ Z, A z) → Z.length ≤ NA)
    (L : List NodeId) (hnd : L.Nodup)
    (hL : ∀ x ∈ L, (∃ z, PtrBelow sp P x z ∧ A z) ∧ levelOf P x ≤ H) :
    L.length ≤ NA * geomSum Q H := by
  classical
  let w : {x // x ∈ L} → NodeId := fun x => Classical.choose (hL x.1 x.2).1
  have hw : ∀ x (hx : x ∈ L), PtrBelow sp P x (w ⟨x, hx⟩) ∧ A (w ⟨x, hx⟩) :=
    fun x hx => Classical.choose_spec (hL x hx).1
  let Z := (L.attach.map w).eraseDups
  have hZnd : Z.Nodup := nodup_eraseDups _
  have hZA : ∀ z ∈ Z, A z := by
    intro z hz
    obtain ⟨⟨x, hx⟩, -, rfl⟩ := List.mem_map.mp (List.mem_eraseDups.mp hz)
    exact (hw x hx).2
  have h1 := nodup_length_le_sum (fun z x => PtrBelow sp P x z ∧ levelOf P x ≤ H)
    (fun _ => geomSum Q H)
    (fun z L' hnd' hL' => ptrAnc_count hp Q H hQ H z L' (by omega) hnd' hL')
    Z L hnd (by
      intro x hx
      refine ⟨w ⟨x, hx⟩, ?_, (hw x hx).1, (hL x hx).2⟩
      exact List.mem_eraseDups.mpr (List.mem_map.mpr ⟨⟨x, hx⟩, List.mem_attach _ _, rfl⟩))
  rw [sum_map_const] at h1
  have := Nat.mul_le_mul_right (geomSum Q H) (hA Z hZnd hZA)
  omega

end Count

theorem sum_map_mul_left (l : List Nat) (f : Nat → Nat) (c : Nat) :
    (l.map (fun τ => c * f τ)).sum = c * (l.map f).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, List.sum_cons, ih, Nat.mul_add]

/-- T4's debt with BergDB's test, counted: with every node of D on a level up to
H, D has at most as many nodes as there are nodes on levels up to H that reach,
through pointers, the access paths of the last H + 1 sections, for any bound N τ
on those of T(τ). -/
theorem debt_count_java (sp : Spec V T) (al : Algo V T) (ts : List T) (hok : RunOK sp al ts)
    (hj : al.stillDirty = javaTest sp) (H : Nat)
    (hH : ∀ e ∈ (run sp al ts).D, levelOf (run sp al ts).P e.1 ≤ H) (N : Nat → Nat)
    (hN : ∀ τ (L : List NodeId), L.Nodup →
      (∀ x ∈ L, (∃ z, PtrBelow sp (run sp al ts).P x z ∧ onAccessPath sp al ts τ z) ∧
        levelOf (run sp al ts).P x ≤ H) → L.length ≤ N τ) :
    (run sp al ts).D.length ≤
      ((List.range' (spIter (run sp al ts).S (H + 1) ts.length + 1)
        (ts.length - spIter (run sp al ts).S (H + 1) ts.length)).map N).sum := by
  have hst : AlgOK sp al := algOK_of sp al (Or.inl hj)
  have hK : ts.length ≤ ts.length := Nat.le_refl _
  have hinvK := inv_st sp al ts hok hst ts.length hK
  rw [st_length] at hinvK
  have hle := spAt_st_le hok hst hK
  have hmono := spAt_st_mono hok hst hK
  rw [st_length] at hle hmono
  have hdebt := debtByChains_java sp al ts hok hj
  rw [← List.length_map (f := (·.1))]
  apply nodup_length_le_sum (fun τ x => (∃ z, PtrBelow sp (run sp al ts).P x z ∧
    onAccessPath sp al ts τ z) ∧ levelOf (run sp al ts).P x ≤ H) N hN _ _ hinvK.dNodup
  intro x hx
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hx
  obtain ⟨τ, z, h1, h2, h3, h4⟩ := hdebt e he
  have hanti := spIter_anti (run sp al ts).S ts.length hle hmono ts.length hK
    (H - levelOf (run sp al ts).P e.1) (levelOf (run sp al ts).P e.1 + 1)
  have hlv := hH e he
  rw [show levelOf (run sp al ts).P e.1 + 1 + (H - levelOf (run sp al ts).P e.1) = H + 1 by omega]
    at hanti
  refine ⟨τ, ?_, ⟨z, h3, h4⟩, hlv⟩
  rw [List.mem_range'_1]
  omega

/-- T4's debt with BergDB's test and TREE, counted: with at most Q pointer
parents per node, D has at most (1 + Q + ... + Q^H) times the bound of
`T4_debt_tree` on the access paths of the last H + 1 sections. -/
theorem debt_tree_java (sp : Spec V T) (al : Algo V T) (ts : List T) (hok : RunOK sp al ts)
    (hj : al.stillDirty = javaTest sp) (htree : TreeRunOK sp al ts)
    (n0 : Node V) (h0 : (run sp al ts).P.get? root = some n0) (Q : Nat)
    (hQ : ∀ z, (ptrParents sp (run sp al ts).P z).length ≤ Q) :
    (run sp al ts).D.length ≤ geomSum Q n0.level *
      ((List.range' (spIter (run sp al ts).S (n0.level + 1) ts.length + 1)
        (ts.length - spIter (run sp al ts).S (n0.level + 1) ts.length)).map (fun τ =>
          (n0.level + 1) * ((changeAt sp al ts τ).new.length + (changeAt sp al ts τ).adds.length) +
            (changeAt sp al ts τ).touch.length)).sum := by
  have hst : AlgOK sp al := algOK_of sp al (Or.inl hj)
  have hK : ts.length ≤ ts.length := Nat.le_refl _
  have hinvK := inv_st sp al ts hok hst ts.length hK
  rw [st_length] at hinvK
  rw [← sum_map_mul_left]
  apply debt_count_java sp al ts hok hj n0.level
  · intro e he
    obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp (isSome_of_isIndex (hinvK.dIndex e he))
    obtain ⟨t, -, hr⟩ := hinvK.born e.1 (by rw [hn]; rfl)
    rw [reachable_iff] at hr
    rw [levelOf_of_get hn]
    rcases reach_level_root hr h0 n hn with h | h
    · rw [h, h0, Option.some.injEq] at hn; subst hn; omega
    · omega
  · intro τ L hnd hL
    rw [Nat.mul_comm]
    apply ptrAnc_count_set hinvK.ptrs Q n0.level hQ (fun z => onAccessPath sp al ts τ z) _ _ L hnd hL
    intro Z hZnd hZ
    cases Z with
    | nil => exact Nat.zero_le _
    | cons x Z' =>
      obtain ⟨j, hj', rfl, -⟩ := onAccessPath_elim hok hst (hZ x (by simp))
      rw [changeAt_succ j hj']
      have hinv1 := inv_st sp al ts hok hst (j + 1) (by omega)
      obtain ⟨n1, hn1⟩ := Option.isSome_iff_exists.mp hinv1.rootIn
      have hg := st_grow sp al ts hok hst (j := j + 1) (j' := ts.length) (by omega) hK
      obtain ⟨n1K, hn1K, hl, -, -⟩ := hg root n1 hn1
      rw [st_length, h0, Option.some.injEq] at hn1K
      subst hn1K
      have := accessPath_count hok hst hj' (by have := htree j hj'; simpa [st] using this) hn1
        (x :: Z') hZnd hZ
      rw [← hl] at this
      exact this

/-- T4's debt with BergDB's test, with restarts after any transactions: D, the
stream and the nodes are those of the run without restarts (T1, T2). -/
theorem debtByChains_restarts (sp : Spec V T) (al : Algo V T) (ts : List (T × Bool))
    (hok : RunOK sp al (ts.map (·.1))) (hj : al.stillDirty = javaTest sp) :
    ∀ e ∈ (runRestarts sp al ts).D, ∃ τ z,
      spIter (runRestarts sp al ts).S (levelOf (runRestarts sp al ts).P e.1 + 1) ts.length < τ ∧
        τ ≤ ts.length ∧ PtrBelow sp (runRestarts sp al ts).P e.1 z ∧
          onAccessPath sp al (ts.map (·.1)) τ z := by
  have hst : AlgOK sp al := algOK_of sp al (Or.inl hj)
  have h := T2_strong sp al ts hok hst ts.length (Nat.le_refl _)
  rw [List.take_length] at h
  have hl : (ts.map (·.1)).length = ts.length := List.length_map _
  rw [← hl, st_length] at h
  obtain ⟨hS, hD, hP⟩ := h
  have hdebt := debtByChains_java sp al (ts.map (·.1)) hok hj
  have hpb : ∀ x z, PtrBelow sp (run sp al (ts.map (·.1))).P x z →
      PtrBelow sp (runRestarts sp al ts).P x z := by
    intro x z hb
    induction hb with
    | refl x => exact PtrBelow.refl x
    | @step x y z n hn hy _ ih => exact PtrBelow.step n (by rw [hP x]; exact hn) hy ih
  intro e he
  rw [hD] at he
  obtain ⟨τ, z, h1, h2, h3, h4⟩ := hdebt e he
  have hlv : levelOf (runRestarts sp al ts).P e.1 = levelOf (run sp al (ts.map (·.1))).P e.1 := by
    unfold levelOf; rw [hP e.1]
  refine ⟨τ, z, ?_, by rw [← hl]; exact h2, hpb _ _ h3, h4⟩
  rw [hS, hlv, ← hl]
  exact h1

end SIS
