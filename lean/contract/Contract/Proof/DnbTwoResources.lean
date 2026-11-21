/-
bergdb 030-37: the node induction supplies the inner resources whenever
a planned child is immediately above leaves.
-/
import Contract.Proof.DnbTwoDefs

namespace Contract.PE

open DNB PeProof

variable {i : Time} {s : Tree}

theorem plan_inner_resourcesTwo {b G H F : Nat} (hb : 8 ≤ b) (hks : KsOk b s)
    (IHp : ∀ f < F, PlanTwo b (Cfg.java b G H) i s f)
    {x g fs : Nat} {ops : List Op} {acc acc' : Acc} {v : VN}
    (hsh : Shaped (Cfg.java b G H) s g 1 x) (hgood : ∃ lo hi, Good s x lo hi)
    (hfill : Filled (Cfg.java b G H) s false x) (hops : OpsD g ops)
    (hfs : s.fuel x ≤ fs) (hNo : NoHigherJoinsAt (Cfg.java b G H) i s fs x g ops)
    (hp : plan (Cfg.java b G H) i s F x g 1 ops acc = some (v, acc'))
    (hc : PlanSpecD b s g 1 x false v acc acc' (sbPlan b s fs x g ops false)) :
    JoinInner b G H i s v ∧ (v.isEmpty = true → 1 ≤ (sbPlan b s fs x g ops false).nd) ∧
      innerPotential (Cfg.java b G H) s v ≤ (sbPlan b s fs x g ops false).nd := by
  cases F with
  | zero => simp [plan] at hp
  | succ F =>
    obtain ⟨n, hobj, hgk, hlev, hleaf, _, _⟩ := shaped_getKey hsh
    have hgkD : DNB.getKey s x = some n := hgk
    have hleaf' : n.leaf = false := by simpa using hleaf
    obtain ⟨_, hkids⟩ := shaped_inner hsh hobj
    obtain ⟨lo, hi, hg⟩ := hgood
    obtain ⟨_, hkey⟩ := good_key hg hobj
    have hfuel : s.fuel x = n.level + 1 := by simp [Tree.fuel, hobj]
    obtain ⟨fs', rfl⟩ : ∃ fs', fs = fs' + 1 := ⟨fs - 1, by omega⟩
    simp only [NoHigherJoinsAt, hgkD, hleaf', Bool.false_eq_true, ↓reduceIte] at hNo
    obtain ⟨hNoKids, _⟩ := hNo
    let P : Nat → NodeId → List Op → Prop := fun c y o => OpsD g o ∧
      ((c, y), o) ∈ (live n.ks).zip (route (segAt g) (live n.ks) ops)
    have childSpec : ∀ f < F, ∀ c y o acc0 w acc2, (c, y) ∈ live n.ks → o ≠ [] → P c y o →
        plan (Cfg.java b G H) i s f y g 0 o acc0 = some (w, acc2) →
        PlanSpecD b s g 0 y false w acc0 acc2 (sbPlan b s fs' y g o false) := by
      intro f hf c y o acc0 w acc2 hmem hone hPP hpl
      obtain ⟨hP, hpair⟩ := hPP
      obtain ⟨m, hm, hmlev, _⟩ := hkey c y hmem (by simp [hleaf'])
      have hgood' : ∃ lo hi, Good s y lo hi := by
        rcases good_kids hg hobj c y hmem with ⟨m', hm', _, lo', hi', hg'⟩ | ⟨v', hv'⟩
        · exact ⟨lo', hi', hg'⟩
        · rw [hm] at hv'; cases hv'
      have hfy : s.fuel y ≤ fs' := by simp [Tree.fuel, hm]; omega
      have hfill' := (filled_key hfill hobj).2.2.2 c y hmem hleaf'
      have hn := hNoKids ((c, y), o) hpair hone
      exact IHp f (by omega) y g 0 o acc0 w acc2 false fs' (hkids c y hmem) hgood'
        hfill' hP hone hfy hn hpl
    exact plan_inner_leaf_resources hb hks hsh hobj hfill P childSpec
      (fun cy o ho => ⟨fun op hop => hops op
        ((route_sub (segAt g) (live n.ks) ops o (List.of_mem_zip ho).2).subset hop), ho⟩) hp hc

end Contract.PE
