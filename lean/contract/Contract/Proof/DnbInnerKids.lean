/-
bergdb 030-37: collect the one-level inner resources through planKids.
Dropping an empty child and retaining a group's pending joins use
disjoint parts of the delete budget.
-/
import Contract.Proof.DnbInnerResources

namespace Contract.PE

open DNB PeProof

variable {i : Time} {s : Tree}

theorem kids_inner_leaf_resources {b G H g F0 fs : Nat} (hb : 8 ≤ b)
    {lvAll : List (Nat × NodeId)} (P : Nat → NodeId → List Op → Prop)
    (hchild : ∀ f < F0, ∀ c y o acc w acc', (c, y) ∈ lvAll → o ≠ [] → P c y o →
      plan (Cfg.java b G H) i s f y g 1 o acc = some (w, acc') →
      JoinInner b G H i s w ∧ (w.isEmpty = true → 1 ≤ (sbPlan b s fs y g o false).nd) ∧
        innerPotential (Cfg.java b G H) s w ≤ (sbPlan b s fs y g o false).nd)
    (hold : ∀ c y, (c, y) ∈ lvAll → ∃ n, getKey s y = some n ∧ n.ks.length ≤ b ∧
      (Cfg.java b G H).m ≤ (live n.ks).length ∧
        LeafReady b G H i s ((live n.ks).map (fun q => (q.1, VN.old q.2)))) :
    ∀ (lv : List (Nat × NodeId)) (os : List (List Op)) (f : Nat) (acc : Acc)
      (es : List (Nat × VN)) (acc1 : Acc), lv ⊆ lvAll →
      (∀ cy o, (cy, o) ∈ lv.zip os → P cy.1 cy.2 o) → f ≤ F0 →
      planKids (Cfg.java b G H) i s f g 2 lv os acc = some (es, acc1) →
      (∀ e ∈ es, JoinInner b G H i s e.2) ∧ es.map (·.1) = lv.map (·.1) ∧
      lv.length + innerPotentials (Cfg.java b G H) s (kept es) ≤ (kept es).length +
        ((childRs b s fs g lv os).map (·.nd)).sum
  | _, _, 0, _, _, _, _, _, _, hp => by simp [planKids] at hp
  | [], os, f + 1, acc, es, acc1, _, _, _, hp => by
    simp only [planKids, Option.some.injEq, Prod.mk.injEq] at hp
    obtain ⟨rfl, rfl⟩ := hp
    exact ⟨by simp, rfl, by simp [kept, childRs, innerPotentials]⟩
  | (c, y) :: rest, [], f + 1, acc, es, acc1, _, _, _, hp => by simp [planKids] at hp
  | (c, y) :: rest, o :: os, f + 1, acc, es, acc1, hsub, hos, hf, hp => by
    have hmem : (c, y) ∈ lvAll := hsub List.mem_cons_self
    have hsub' : rest ⊆ lvAll := fun q hq => hsub (List.mem_cons_of_mem _ hq)
    have hos' : ∀ cy o', (cy, o') ∈ rest.zip os → P cy.1 cy.2 o' :=
      fun cy o' ho => hos cy o' (List.mem_cons_of_mem _ ho)
    obtain ⟨n, hk, hks, hfill, hready⟩ := hold c y hmem
    simp only [planKids] at hp
    split at hp
    · rename_i hoe
      cases ht : planKids (Cfg.java b G H) i s f g 2 rest os acc with
      | none => rw [ht] at hp; cases hp
      | some q =>
        obtain ⟨es', acc2⟩ := q
        rw [ht] at hp
        simp only [Option.some.injEq, Prod.mk.injEq] at hp
        obtain ⟨rfl, rfl⟩ := hp
        obtain ⟨ih1, ih2, ih3⟩ := kids_inner_leaf_resources hb P hchild hold rest os f acc es' acc2
          hsub' hos' (by omega) ht
        refine ⟨?_, by simpa using congrArg (List.cons c) ih2, ?_⟩
        · intro e he
          rcases List.mem_cons.mp he with rfl | he
          · exact JoinInner.old hk hks hfill hready
          · exact ih1 e he
        · have hz : childRs b s fs g ((c, y) :: rest) (o :: os) = childRs b s fs g rest os := by
            simp [childRs, hoe]
          have hke : kept ((c, VN.old y) :: es') = (c, VN.old y) :: kept es' := by simp [kept, VN.isEmpty]
          rw [hke, innerPotentials_cons, innerPotential_old hk, hz]
          simp only [List.length_cons]
          omega
    · rename_i hoe
      have hone : o ≠ [] := by simpa using hoe
      cases hpl : plan (Cfg.java b G H) i s f y g 1 o acc with
      | none => rw [hpl] at hp; cases hp
      | some q0 =>
        obtain ⟨w, acc2⟩ := q0
        rw [hpl] at hp
        simp only at hp
        cases ht : planKids (Cfg.java b G H) i s f g 2 rest os acc2 with
        | none => rw [ht] at hp; cases hp
        | some q =>
          obtain ⟨es', acc3⟩ := q
          rw [ht] at hp
          simp only [Option.some.injEq, Prod.mk.injEq] at hp
          obtain ⟨rfl, rfl⟩ := hp
          obtain ⟨ih1, ih2, ih3⟩ := kids_inner_leaf_resources hb P hchild hold rest os f acc2 es' acc3
            hsub' hos' (by omega) ht
          obtain ⟨hw, hemp, hpot⟩ := hchild f (by omega) c y o acc w acc2 hmem hone
            (hos (c,y) o List.mem_cons_self) hpl
          refine ⟨?_, by simpa using congrArg (List.cons c) ih2, ?_⟩
          · intro e he
            rcases List.mem_cons.mp he with rfl | he
            · exact hw
            · exact ih1 e he
          · have hz : childRs b s fs g ((c, y) :: rest) (o :: os) =
                sbPlan b s fs y g o false :: childRs b s fs g rest os := by simp [childRs, hoe]
            rw [hz]
            simp only [List.map_cons, List.sum_cons]
            by_cases hem : w.isEmpty = true
            · have hnd1 := hemp hem
              simp only [kept, List.filter_cons, hem, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
              change rest.length + 1 + innerPotentials (Cfg.java b G H) s (kept es') ≤
                (kept es').length + ((sbPlan b s fs y g o false).nd +
                  ((childRs b s fs g rest os).map (·.nd)).sum)
              omega
            · have hem0 : w.isEmpty = false := by simpa using hem
              have hke : kept ((c, w) :: es') = (c, w) :: kept es' := by simp [kept, hem0]
              rw [hke, innerPotentials_cons]
              simp only [List.length_cons]
              omega

end Contract.PE
