/-
bergdb 030-37: rebalance of nodes immediately above leaves against the
parent's delete and entry allowances. The reserve consumed is four nodes
per counted delete, including all leaf rebalances inside the inner loop.
-/
import Contract.Proof.DnbInnerLoop

namespace Contract.PE

open DNB PeProof

variable {i : Time} {s : Tree}

theorem innerPotentials_mem {cf : Cfg} {s : Tree} {e : Nat × VN} :
    ∀ {es : List (Nat × VN)}, e ∈ es → innerPotential cf s e.2 ≤ innerPotentials cf s es
  | [], he => by cases he
  | a :: es, he => by
    rw [innerPotentials_cons]
    rcases List.mem_cons.mp he with rfl | he
    · omega
    · have := innerPotentials_mem (cf := cf) (s := s) he; omega

theorem entries_length_le_none_inner {b G H : Nat} (hb : 8 ≤ b) {es : List (Nat × VN)}
    (hv : ∀ e ∈ es, JoinInner b G H i s e.2) :
    (entries es).length ≤ es.length + newEntries es := by
  induction es with
  | nil => simp [entries, newEntries]
  | cons e es ih =>
    have he := (hv e List.mem_cons_self).cost hb e.1 |>.2.2.2
    have ht := ih (fun e he => hv e (List.mem_cons_of_mem _ he))
    rw [entries_cons, List.length_append, newEntries_cons]
    simp only [List.length_cons]
    omega

/-- Full accounting for the inner loop, conditional on its structural
forms and the initial delete potential. The latter is supplied by the
leaf planning proof; it is not a bound on writes. -/
theorem rebalance_inner_leaf_budget {b G H : Nat} (hb : 8 ≤ b) {f g nd U : Nat}
    {es es2 : List (Nat × VN)} {lv : List (Nat × NodeId)}
    (hv : ∀ e ∈ es, JoinInner b G H i s e.2)
    (hcvs : es.map (·.1) = lv.map (·.1))
    (hbudget : lv.length + innerPotentials (Cfg.java b G H) s (kept es) ≤ (kept es).length + nd)
    (hadded : addedEntries lv (kept es) ≤ U)
    (hsame : nd = 0 → addedEntries lv (kept es) = 0 →
      entries (kept es) = lv.map (fun q => (q.1, some q.2)))
    (hhead : lv.head?.map (·.1) = some 0) (hsort : lv.Pairwise CvLtA)
    (hr : rebalance (Cfg.java b G H) i s (f + 1) g 1 es = some es2) :
    vcostL es2 ≤ vcostL (kept es) + 4 * nd ∧
      lv.length ≤ (renameHead 0 (entries es2)).length + nd ∧
      (removedCvs lv (renameHead 0 (entries es2))).length +
        ((renameHead 0 (entries es2)).filter (isAdded lv)).length ≤ 4 * nd + U ∧
      (renameHead 0 (entries es2)).length ≤ lv.length +
        ((renameHead 0 (entries es2)).filter (isAdded lv)).length ∧
      (4 * nd + U = 0 → lv.map (fun q => (q.1, some q.2)) = renameHead 0 (entries es2)) := by
  have hm := (java_params (G := G) (H := H) hb).2.2.2.2.2.2
  change (if !(Cfg.java b G H).merges then some (kept es) else
    joinLoop (Cfg.java b G H) i s g 1 (fun J => rebalance (Cfg.java b G H) i s f g 0 J)
      ((kept es).length + 1) (kept es)) = some es2 at hr
  simp only [hm, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hr
  have hkv : ∀ e ∈ kept es, JoinInner b G H i s e.2 :=
    fun e he => hv e (List.mem_of_mem_filter he)
  obtain ⟨j, hv2, hcost, _, hlen, hsm, hcsub, hhd, hA⟩ := joinLoop_inner_leaf_account hb _ _ _ hkv hr
  have hsub : (es2.map (·.1)).Sublist (lv.map (·.1)) := by
    have hke : (kept es).Sublist es := List.filter_sublist
    rw [← hcvs]
    exact hcsub.trans (hke.map (·.1))
  have heslen : es.length = lv.length := by
    have := congrArg List.length hcvs
    simpa only [List.length_map] using this
  have hkeepLen : (kept es).length ≤ lv.length := by
    rw [← heslen]; exact List.length_filter_le _ _
  have hj : j ≤ nd := by omega
  have hR := removed_le_of_sublist hsub (fun c hc => entries_any_cv hc)
  simp only [List.length_map] at hR
  have hAe := hA lv
  have hAlen : addedEntries lv es2 ≤ U + 3 * j := by omega
  have hElen := entries_length_le_none_inner hb hv2
  have hnone := none_entries_le_added lv (renameHead 0 (entries es2))
  rw [none_renameHead] at hnone
  have hEntge := flatMap_ents_length_ge es2
  change es2.length ≤ (entries es2).length at hEntge
  have hLlen : (renameHead 0 (entries es2)).length = (entries es2).length := renameHead_length _ _
  have hnoDrop : lv.length = (kept es).length → renameHead 0 (entries es2) = entries es2 := by
    intro hlen0
    have hke : kept es = es := (List.filter_sublist (p := fun e : Nat × VN => !e.2.isEmpty)).eq_of_length
      (by change (kept es).length = es.length; omega)
    apply renameHead_of_head
    rw [entries_head, hhd, hke]
    have hh := congrArg List.head? hcvs
    simpa only [List.head?_map, Option.map_map] using hh.trans (by simpa [List.head?_map] using hhead)
  refine ⟨by omega, by omega, ?_, ?_, ?_⟩
  · by_cases hdrop : lv.length = (kept es).length
    · rw [hnoDrop hdrop]
      change (removedCvs lv (entries es2)).length + addedEntries lv es2 ≤ 4 * nd + U
      omega
    · have hR' := removed_renameHead_le hsort 0 (entries es2)
      have hA' := added_renameHead_le (lb := lv) 0 (entries es2)
      change ((renameHead 0 (entries es2)).filter (isAdded lv)).length ≤ addedEntries lv es2 + 1 at hA'
      omega
  · change (entries es2).length ≤ es2.length +
      ((entries es2).filter (fun e => e.2.isNone)).length at hElen
    omega
  · intro hz
    have hnd : nd = 0 := by omega
    have hkeepEq : lv.length = (kept es).length := by omega
    rw [hnoDrop hkeepEq]
    have hsmall0 : innerPotentials (Cfg.java b G H) s (kept es) = 0 := by omega
    have hfind : findSmall (Cfg.java b G H) (kept es) = none := by
      cases hf : findSmall (Cfg.java b G H) (kept es) with
      | none => rfl
      | some ix =>
        obtain ⟨e, he, hs⟩ := findSmall_get hf
        have hpot := innerPotentials_mem (cf := Cfg.java b G H) (s := s) (List.mem_of_getElem? he)
        have hpos : 1 ≤ innerPotential (Cfg.java b G H) s e.2 := by
          simp only [innerPotential, hs, ↓reduceIte]; omega
        omega
    have hstop : es2 = kept es := by
      rw [joinLoop] at hr
      split at hr
      · exact (Option.some.inj hr).symm
      · rw [hfind] at hr
        exact (Option.some.inj hr).symm
    rw [hstop]
    exact (hsame hnd (by omega)).symm

end Contract.PE
