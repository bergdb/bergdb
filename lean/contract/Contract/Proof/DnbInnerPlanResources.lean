/-
bergdb 030-37: expose the inner resources of an actual successful plan.
The child induction supplies the leaf plans. The unchanged tree supplies
the fill and size bounds; no extra condition on a join's write count is
assumed.
-/
import Contract.Proof.DnbInnerKids

namespace Contract.PE

open DNB PeProof

variable {i : Time} {s : Tree}

theorem plan_inner_leaf_resources {b G H F fs x g : Nat} (hb : 8 ≤ b) (hks : KsOk b s)
    {n : KNode} {ops : List Op} {acc acc' : Acc} {v : VN}
    (hsh : Shaped (Cfg.java b G H) s g 1 x) (hobj : s.obj x = some (.key n))
    (hf : Filled (Cfg.java b G H) s false x)
    (P : Nat → NodeId → List Op → Prop)
    (hchild : ∀ f < F, ∀ c y o acc0 w acc2, (c, y) ∈ live n.ks → o ≠ [] → P c y o →
      plan (Cfg.java b G H) i s f y g 0 o acc0 = some (w, acc2) →
      PlanSpecD b s g 0 y false w acc0 acc2 (sbPlan b s fs y g o false))
    (hos : ∀ cy o, (cy, o) ∈ (live n.ks).zip (route (segAt g) (live n.ks) ops) → P cy.1 cy.2 o)
    (hp : plan (Cfg.java b G H) i s (F + 1) x g 1 ops acc = some (v, acc'))
    (hc : PlanSpecD b s g 1 x false v acc acc' (sbPlan b s (fs + 1) x g ops false)) :
    JoinInner b G H i s v ∧ (v.isEmpty = true → 1 ≤ (sbPlan b s (fs + 1) x g ops false).nd) ∧
      innerPotential (Cfg.java b G H) s v ≤ (sbPlan b s (fs + 1) x g ops false).nd := by
  have hk : getKey s x = some n := by simp [getKey, hobj]
  have hkD : DNB.getKey s x = some n := hk
  have hleaf : n.leaf = false := by
    obtain ⟨n', ho', _, _, hl, _, _⟩ := shaped_getKey hsh
    rw [hobj] at ho'; cases ho'; simpa using hl
  have hfn := filled_key hf hobj
  have hm2 := (java_params (G := G) (H := H) hb).1
  have hfill : (Cfg.java b G H).m ≤ (live n.ks).length := hfn.2.1 hm2 rfl
  have hfillKids : ∀ c y, (c, y) ∈ live n.ks → ∃ m, getKey s y = some m ∧
      (Cfg.java b G H).m ≤ (live m.ks).length := by
    intro c y hmem
    have hs := (shaped_inner hsh hobj).2 c y hmem
    obtain ⟨m, hm, hmk, _, _, _, _⟩ := shaped_getKey hs
    exact ⟨m, hmk, (filled_key (hfn.2.2.2 c y hmem hleaf) hm).2.1 hm2 rfl⟩
  rw [plan.eq_def] at hp
  simp only at hp
  rw [hk] at hp
  simp only [Nat.one_ne_zero, beq_iff_eq, ↓reduceIte, Nat.sub_self] at hp
  cases hpk : planKids (Cfg.java b G H) i s F g 1 (live n.ks)
      (route (segAt g) (live n.ks) ops) acc with
  | none => rw [hpk] at hp; cases hp
  | some q =>
    obtain ⟨es, acc1⟩ := q
    rw [hpk] at hp
    simp only at hp
    have hres := kids_leaf_resources hb P hchild
      (fun c y _ m hm => (hks y m (by
        unfold getKey at hm; split at hm <;> simp_all)).2) hfillKids
      (live n.ks) (route (segAt g) (live n.ks) ops) F acc es acc1 (fun _ h => h) hos le_rfl hpk
    cases hr : rebalance (Cfg.java b G H) i s (F + 1) g 0 es with
    | none => rw [hr] at hp; cases hp
    | some es2 =>
      rw [hr] at hp
      simp only at hp
      have hnd : (sbPlan b s (fs + 1) x g ops false).nd =
          ((childRs b s fs g (live n.ks) (route (segAt g) (live n.ks) ops)).map (·.nd)).sum := by
        rw [sbPlan.eq_def]
        simp only [hkD, hleaf, Bool.false_eq_true, ↓reduceIte]
        rfl
      cases hm : mkNode (Cfg.java b G H) i s (some x) g 1 false es2 with
      | none => rw [hm] at hp; cases hp
      | some w =>
        rw [hm] at hp
        simp only [Option.some.injEq, Prod.mk.injEq] at hp
        obtain ⟨rfl, rfl⟩ := hp
        have hdone := planned_inner_leaf_resources hb hk (hks x n hobj).2 hfill hres.1 hres.2.2
          hr hm hc hnd
        simpa only [hnd] using hdone

end Contract.PE
