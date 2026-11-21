/-
bergdb 030-37: the complete loop at one level of inner joins. Each join
includes its recursive rebalance of leaves. Untouched neighbours and
groups already joined satisfy the same invariant.
-/
import Contract.Proof.DnbInnerJoins

namespace Contract.PE

open DNB PeProof

variable {i : Time} {s : Tree}

theorem ents_node_none_added (lb : List (Nat × NodeId)) (c g h : Nat) (j : Bool)
    (es : List (Nat × VN)) (F : List (Nat × Option NodeId)) (d : Dec) :
    ((ents c (.node none g h j es F d)).filter (isAdded lb)).length =
      noneCount c (.node none g h j es F d) := by
  have ha : ∀ e ∈ ents c (.node none g h j es F d), e.2 = none := by
    cases d with
    | same => simp [ents]
    | append => simp [ents]
    | parts k =>
      simp only [ents]
      split
      · exact partEnts_none _ _ _ _
      · simp
  unfold noneCount
  congr 1
  apply List.filter_congr
  intro e he
  simp [isAdded, ha e he]

theorem mkNode_none_added_inner {cf : Cfg} {g : Nat} {es : List (Nat × VN)} {v : VN}
    (hm : mkNode cf i s none g 1 true es = some v) (lb : List (Nat × NodeId)) (c : Nat) :
    ((ents c v).filter (isAdded lb)).length = noneCount c v := by
  unfold mkNode at hm
  simp only [Nat.one_ne_zero, beq_iff_eq, ↓reduceIte] at hm
  split at hm
  · cases hm
  · cases hm
    exact ents_node_none_added _ _ _ _ _ _ _ _

theorem joinAt_inner_leaf_account {b G H : Nat} (hb : 8 ≤ b) {f g ix : Nat}
    {es es' : List (Nat × VN)}
    (hsmall : findSmall (Cfg.java b G H) es = some ix)
    (hes : ∀ e ∈ es, JoinInner b G H i s e.2)
    (hj : joinAt (Cfg.java b G H) i s g 1
      (fun J => rebalance (Cfg.java b G H) i s f g 0 J) es ix = some es') :
    (∀ e ∈ es', JoinInner b G H i s e.2) ∧
      vcostL es' ≤ vcostL es + 4 ∧ newEntries es' ≤ newEntries es + 3 ∧
      es'.length + 1 = es.length ∧
      innerPotentials (Cfg.java b G H) s es' + 1 ≤ innerPotentials (Cfg.java b G H) s es ∧
      (es'.map (·.1)).Sublist (es.map (·.1)) ∧
      es'.head?.map (·.1) = es.head?.map (·.1) ∧
      ∀ lb, addedEntries lb es' ≤ addedEntries lb es + 3 := by
  obtain ⟨x, hx, hxs⟩ := findSmall_get hsmall
  have hil : (if useLeftOf (Cfg.java b G H) s es ix then ix - 1 else ix) = ix ∨
      (if useLeftOf (Cfg.java b G H) s es ix then ix - 1 else ix) + 1 = ix := by
    by_cases h0 : ix = 0
    · subst h0; simp [useLeftOf, hx]
    · split <;> omega
  rw [joinAt_eq] at hj
  generalize hi : (if useLeftOf (Cfg.java b G H) s es ix then ix - 1 else ix) = il at hj hil
  unfold joinAtIl at hj
  split at hj
  · rename_i l r hl hr
    have hls := hes l (List.mem_of_getElem? hl)
    have hrs := hes r (List.mem_of_getElem? hr)
    have hs : smallLeaf (Cfg.java b G H) l.2 = true ∨ smallLeaf (Cfg.java b G H) r.2 = true := by
      rcases hil with rfl | hh
      · rw [hx] at hl; cases hl; exact Or.inl hxs
      · rw [hh, hx] at hr; cases hr; exact Or.inr hxs
    split at hj
    · rename_i L R hoL hoR
      simp only [Nat.one_ne_zero, beq_iff_eq, ↓reduceIte] at hj
      cases hd : rebalance (Cfg.java b G H) i s f g 0 (L ++ renameHead r.1 R) with
      | none => rw [hd] at hj; cases hj
      | some J =>
        rw [hd] at hj
        simp only at hj
        cases hm : mkNode (Cfg.java b G H) i s none g 1 true J with
        | none => rw [hm] at hj; cases hj
        | some v =>
          rw [hm] at hj
          simp only [Option.some.injEq] at hj
          subst hj
          obtain ⟨hv, hw, hn, hp⟩ := inner_leaf_join_pair hb hls hrs hoL hoR hs hd hm
            (cL := l.1)
          have hsplit := split_at2 hl hr
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · intro e he
            simp only [List.mem_append, List.mem_singleton] at he
            rcases he with (he | rfl) | he
            · exact hes e (List.mem_of_mem_take he)
            · exact hv
            · exact hes e (List.mem_of_mem_drop he)
          · conv_rhs => rw [hsplit, vcostL_append]
            simp only [vcostL_append, vcostL, Nat.add_zero]
            omega
          · conv_rhs => rw [hsplit, newEntries_append]
            simp only [newEntries_append, newEntries_cons]
            have h0 : newEntries [] = 0 := rfl
            rw [h0]
            omega
          · have hlt := (List.getElem?_eq_some_iff.mp hr).1
            simp only [List.length_append, List.length_take, List.length_cons, List.length_nil,
              List.length_drop]
            omega
          · conv_rhs => rw [hsplit, innerPotentials_append]
            simp only [innerPotentials_append, innerPotentials_cons]
            have h0 : innerPotentials (Cfg.java b G H) s [] = 0 := rfl
            rw [h0]
            omega
          · conv_rhs => rw [hsplit]
            simp only [List.map_append, List.map_cons, List.append_assoc, List.singleton_append]
            exact List.Sublist.append (.refl _) (.cons_cons _ (.cons _ (.refl _)))
          · conv_rhs => rw [hsplit]
            simp only [List.append_assoc, List.singleton_append]
            exact head_fst_eq _ _ _ _ _ _
          · intro lb
            have hnl := noneCount_le_added lb l.1 l.2
            have hnr := noneCount_le_added lb r.1 r.2
            have hnnew := mkNode_none_added_inner hm lb l.1
            conv_rhs => rw [hsplit, addedEntries_append]
            simp only [addedEntries_append, addedEntries_cons]
            have h0 : addedEntries lb [] = 0 := rfl
            rw [h0, hnnew]
            omega
    · cases hj
  · cases hj

/-- Any number of joins of nodes immediately above leaves. Their recursive
leaf rebalances are included. The witness j counts the inner joins and is
bounded by the initial combined potential, including pending small leaves. -/
theorem joinLoop_inner_leaf_account {b G H : Nat} (hb : 8 ≤ b) {f g : Nat} :
    ∀ (n : Nat) (es es' : List (Nat × VN)),
      (∀ e ∈ es, JoinInner b G H i s e.2) →
      joinLoop (Cfg.java b G H) i s g 1
        (fun J => rebalance (Cfg.java b G H) i s f g 0 J) n es = some es' →
      ∃ j, (∀ e ∈ es', JoinInner b G H i s e.2) ∧
        vcostL es' ≤ vcostL es + 4 * j ∧ newEntries es' ≤ newEntries es + 3 * j ∧
        es'.length + j = es.length ∧
        innerPotentials (Cfg.java b G H) s es' + j ≤ innerPotentials (Cfg.java b G H) s es ∧
        (es'.map (·.1)).Sublist (es.map (·.1)) ∧
        es'.head?.map (·.1) = es.head?.map (·.1) ∧
        ∀ lb, addedEntries lb es' ≤ addedEntries lb es + 3 * j
  | 0, es, es', hes, hj => by
    simp only [joinLoop, Option.some.injEq] at hj
    subst hj
    exact ⟨0, hes, by omega, by omega, by omega, by omega, .refl _, rfl, fun _ => by omega⟩
  | n + 1, es, es', hes, hj => by
    rw [joinLoop] at hj
    split at hj
    · cases hj
      exact ⟨0, hes, by omega, by omega, by omega, by omega, .refl _, rfl, fun _ => by omega⟩
    · cases hs : findSmall (Cfg.java b G H) es with
      | none =>
        rw [hs] at hj; cases hj
        exact ⟨0, hes, by omega, by omega, by omega, by omega, .refl _, rfl, fun _ => by omega⟩
      | some ix =>
        rw [hs] at hj
        simp only at hj
        cases hstep : joinAt (Cfg.java b G H) i s g 1
            (fun J => rebalance (Cfg.java b G H) i s f g 0 J) es ix with
        | none => rw [hstep] at hj; cases hj
        | some es1 =>
          rw [hstep] at hj
          obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := joinAt_inner_leaf_account hb hs hes hstep
          obtain ⟨j, k1, k2, k3, k4, k5, k6, k7, k8⟩ := joinLoop_inner_leaf_account hb n es1 es' h1 hj
          exact ⟨j + 1, k1, by omega, by omega, by omega, by omega, k6.trans h6, k7.trans h7,
            fun lb => by have := h8 lb; have := k8 lb; omega⟩

end Contract.PE
