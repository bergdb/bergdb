/-
bergdb 030-37: the node induction with arbitrary joins of segment leaves.
Joins of inner nodes are excluded by `NoInnerJoinsAt`; the other mechanisms
are all included, at every depth and through every key segment.
-/
import Contract.Proof.DnbLeavesLocal
import Contract.Proof.DnbRebalanceBudget

namespace Contract.PE

open DNB PeProof

variable {i : Time} {s : Tree}

/-- **An inner node**, given plan at lower fuels. -/
theorem inner_stepLeaves {b G H F : Nat} (hb : 8 ≤ b) (hks : KsOk b s)
    (IHp : ∀ f < F, PlanLeaves b (Cfg.java b G H) i s f) :
    ∀ (x : NodeId) (g h : Nat) (ops : List Op) (acc : Acc) (v : VN) (acc' : Acc) (isRoot : Bool)
      (fs : Nat), Shaped (Cfg.java b G H) s g (h + 1) x → (∃ lo hi, Good s x lo hi) →
      Filled (Cfg.java b G H) s isRoot x → OpsD g ops → ops ≠ [] → s.fuel x ≤ fs → NoInnerJoinsAt (Cfg.java b G H) i s fs x g ops →
      plan (Cfg.java b G H) i s (F + 1) x g (h + 1) ops acc = some (v, acc') →
      PlanSpecD b s g (h + 1) x isRoot v acc acc' (sbPlan b s fs x g ops isRoot) := by
  intro x g h ops acc v acc' isRoot fs hsh hgood hfill hops hne hfs hNo hpl
  obtain ⟨n, hobj, hgk, hlev, hleaf, _, _⟩ := shaped_getKey hsh
  have hgkD : DNB.getKey s x = some n := hgk
  have hleaf' : n.leaf = false := by simpa using hleaf
  obtain ⟨hhead, hkids⟩ := shaped_inner hsh hobj
  obtain ⟨lo, hi, hg⟩ := hgood
  obtain ⟨hwf, hkey⟩ := good_key hg hobj
  have hfuel : s.fuel x = n.level + 1 := by simp [Tree.fuel, hobj]
  obtain ⟨fs', rfl⟩ : ∃ fs', fs = fs' + 1 := ⟨fs - 1, by omega⟩
  simp only [NoInnerJoinsAt, hgkD, hleaf', Bool.false_eq_true, ↓reduceIte] at hNo
  obtain ⟨hNoKids, hNoHere⟩ := hNo
  have hlvne : (live n.ks) ≠ [] := by intro h0; rw [h0] at hhead; simp at hhead
  rw [plan.eq_def] at hpl
  simp only at hpl
  rw [hgk] at hpl
  simp only [Nat.add_one_ne_zero, beq_iff_eq, ↓reduceIte, Nat.add_sub_cancel] at hpl
  cases hk : planKids (Cfg.java b G H) i s F g (h + 1) (live n.ks) (route (segAt g) (live n.ks) ops) acc with
  | none => rw [hk] at hpl; cases hpl
  | some q =>
    obtain ⟨es, acc1⟩ := q
    rw [hk] at hpl
    simp only at hpl
    let P : Nat → NodeId → List Op → Prop := fun c y o => OpsD g o ∧
      ((c, y), o) ∈ (live n.ks).zip (route (segAt g) (live n.ks) ops)
    have childSpec : ∀ f < F, ∀ c y o acc0 w acc2, (c, y) ∈ live n.ks → o ≠ [] → P c y o →
      plan (Cfg.java b G H) i s f y g h o acc0 = some (w, acc2) →
      PlanSpecD b s g h y false w acc0 acc2 (sbPlan b s fs' y g o false) := by
      intro f hf c y o acc0 w acc2 hmem hone hPP hp
      obtain ⟨hP, hpair⟩ := hPP
      obtain ⟨m, hm, hmlev, _⟩ := hkey c y hmem (by simp [hleaf'])
      have hgood' : ∃ lo hi, Good s y lo hi := by
        rcases good_kids hg hobj c y hmem with ⟨m', hm', _, lo', hi', hg'⟩ | ⟨v', hv'⟩
        · exact ⟨lo', hi', hg'⟩
        · rw [hm] at hv'; cases hv'
      have hfy : s.fuel y ≤ fs' := by simp [Tree.fuel, hm]; omega
      have hfill' := (filled_key hfill hobj).2.2.2 c y hmem hleaf'
      have hn := hNoKids ((c, y), o) hpair hone
      exact IHp f hf y g h o acc0 w acc2 false fs' (hkids c y hmem) hgood'
        hfill' hP hone hfy hn hp
    have hfillKids : ∀ c y, (c, y) ∈ live n.ks → ∀ n', getKey s y = some n' →
        (Cfg.java b G H).m ≤ (live n'.ks).length := by
      intro c y hmem n' hk'
      have hobj' : s.obj y = some (.key n') := by
        unfold getKey at hk'; split at hk' <;> simp_all
      exact (filled_key ((filled_key hfill hobj).2.2.2 c y hmem hleaf') hobj').2.1
        (java_params hb).1 rfl
    have hout := kids_drop P childSpec (java_params hb).1 hfillKids
      (fun c y hmem => lookup_live hmem)
      (live n.ks) (route (segAt g) (live n.ks) ops) F acc es acc1 (fun _ h => h)
      (fun cy o ho => ⟨fun op hop => hops op
        ((route_sub (segAt g) (live n.ks) ops o (List.of_mem_zip ho).2).subset hop), ho⟩) le_rfl hk
    cases hrb : rebalance (Cfg.java b G H) i s (F + 1) g h es with
    | none => rw [hrb] at hpl; cases hpl
    | some es2 =>
      rw [hrb] at hpl
      simp only at hpl
      have hbudgetRb :
          vcostL es2 ≤ vcostL (kept es) + 2 * ((childRs b s fs' g (live n.ks)
            (route (segAt g) (live n.ks) ops)).map (·.nd)).sum ∧
          (live n.ks).length ≤ (renameHead 0 (entries es2)).length +
            ((childRs b s fs' g (live n.ks) (route (segAt g) (live n.ks) ops)).map (·.nd)).sum ∧
          (removedCvs (live n.ks) (renameHead 0 (entries es2))).length +
            ((renameHead 0 (entries es2)).filter (isAdded (live n.ks))).length ≤
              4 * ((childRs b s fs' g (live n.ks) (route (segAt g) (live n.ks) ops)).map (·.nd)).sum +
                ((childRs b s fs' g (live n.ks) (route (segAt g) (live n.ks) ops)).map (·.up)).sum ∧
          (renameHead 0 (entries es2)).length ≤ (live n.ks).length +
            ((renameHead 0 (entries es2)).filter (isAdded (live n.ks))).length ∧
          (4 * ((childRs b s fs' g (live n.ks) (route (segAt g) (live n.ks) ops)).map (·.nd)).sum +
            ((childRs b s fs' g (live n.ks) (route (segAt g) (live n.ks) ops)).map (·.up)).sum = 0 →
              (live n.ks).map (fun q => (q.1, some q.2)) = renameHead 0 (entries es2)) := by
        cases h with
        | zero =>
          have hres := kids_leaf_resources hb P childSpec
            (fun c y hmem n' hk' => hks y n' (by
              unfold getKey at hk'; split at hk' <;> simp_all) |>.2)
            (fun c y hmem => by
              obtain ⟨m, hm, _, _⟩ := hkey c y hmem (by simp [hleaf'])
              have hgk' : getKey s y = some m := by simp [getKey, hm]
              exact ⟨m, hgk', hfillKids c y hmem m hgk'⟩)
            (live n.ks) (route (segAt g) (live n.ks) ops) F acc es acc1 (fun _ h => h)
            (fun cy o ho => ⟨fun op hop => hops op
              ((route_sub (segAt g) (live n.ks) ops o (List.of_mem_zip ho).2).subset hop), ho⟩) le_rfl hk
          exact rebalance_leaf_budget hb hres.1 hres.2.1 hres.2.2 hout.added hout.same0 hhead
            (live_sorted n.ks) hrb
        | succ h =>
          apply rebalance_noJoin_budget hout hhead (live_sorted n.ks) ?_ hrb
          rcases hNoHere F (h + 1) acc es acc1 hsh hk with hzero | hstop
          · omega
          · exact hstop
      obtain ⟨hjoinCost, hjoinLoss, hjoinCounts, hjoinUpper, hjoinZero⟩ := hbudgetRb
      let E := entries es2
      let L := renameHead 0 E
      have hEF : (renameHead 0 es2).flatMap (fun e => ents e.1 e.2) = renameHead 0 E :=
        entries_renameHead 0 es2
      unfold mkNode at hpl
      simp only [Nat.add_one_ne_zero, beq_iff_eq, ↓reduceIte] at hpl
      rw [hgk, hEF, renameHead_renameHead] at hpl
      simp only [Option.some.injEq, Prod.mk.injEq] at hpl
      obtain ⟨rfl, rfl⟩ := hpl
      have hsb : sbPlan b s (fs' + 1) x g ops isRoot = sbNode b n isRoot
          (4 * ((kidsRs b s fs' g (live n.ks) ops).map (·.nd)).sum +
            ((kidsRs b s fs' g (live n.ks) ops).map (·.up)).sum)
          ((kidsRs b s fs' g (live n.ks) ops).map (·.nd)).sum
          (if ((kidsRs b s fs' g (live n.ks) ops).map (·.nd)).sum = 0 then 0
            else 1 + (((kidsRs b s fs' g (live n.ks) ops).filter (fun r => 0 < r.nd)).map (·.ci)).foldl
              max 0)
          ((kidsRs b s fs' g (live n.ks) ops).map (·.cnt)).sum := by
        rw [sbPlan.eq_def]
        simp only [hgkD, hleaf', Bool.false_eq_true, ↓reduceIte]
        rfl
      have hkw0 : kw acc1 + vcostL es2 ≤ kw acc +
          ((kidsRs b s fs' g (live n.ks) ops).map (·.cnt)).sum := by
        have hk0 := hout.kw
        change kw acc1 + vcostL (kept es) +
          4 * ((kidsRs b s fs' g (live n.ks) ops).map (·.nd)).sum ≤ kw acc +
            ((kidsRs b s fs' g (live n.ks) ops).map (·.cnt)).sum at hk0
        change vcostL es2 ≤ vcostL (kept es) +
          2 * ((kidsRs b s fs' g (live n.ks) ops).map (·.nd)).sum at hjoinCost
        omega
      rw [hsb]
      generalize hnd : ((kidsRs b s fs' g (live n.ks) ops).map (·.nd)).sum = nd at hkw0 ⊢
      generalize hU : ((kidsRs b s fs' g (live n.ks) ops).map (·.up)).sum = U at hkw0 ⊢
      let K := 4 * nd + U
      generalize ((kidsRs b s fs' g (live n.ks) ops).map (·.cnt)).sum = below at hkw0 ⊢
      generalize hci : (if nd = 0 then 0 else
          1 + List.foldl max 0 (List.map SR.ci (List.filter (fun r => decide (0 < r.nd))
            (kidsRs b s fs' g (live n.ks) ops)))) = ci
      change PlanSpecD b s g (h + 1) x isRoot _ acc acc1 (sbNode b n isRoot K nd ci below)
      obtain ⟨fnd, fci, fup, fparts, fov, fp⟩ := sbNode_factsD b n isRoot K nd ci below
      have hcounts : (removedCvs (live n.ks) L).length +
          (L.filter (isAdded (live n.ks))).length ≤ K := by
        change _ ≤ 4 * ((kidsRs b s fs' g (live n.ks) ops).map (·.nd)).sum +
          ((kidsRs b s fs' g (live n.ks) ops).map (·.up)).sum at hjoinCounts
        simpa only [hnd, hU] using hjoinCounts
      have hFlen : L.length ≤ n.ks.length + K := by
        have hlvl := live_length_le n.ks
        change L.length ≤ (live n.ks).length + (L.filter (isAdded (live n.ks))).length at hjoinUpper
        omega
      have hzero : K = 0 → (live n.ks).map (fun q => (q.1, some q.2)) = L := by
        intro hz
        apply hjoinZero
        change 4 * ((kidsRs b s fs' g (live n.ks) ops).map (·.nd)).sum +
          ((kidsRs b s fs' g (live n.ks) ops).map (·.up)).sum = 0
        simpa only [hnd, hU] using hz
      have hdec : ∀ k, decideNode (Cfg.java b G H) i (some n) false L = .parts k →
          0 < (sbNode b n isRoot K nd ci below).ov ∧ k ≤ (sbNode b n isRoot K nd ci below).parts := by
        intro k hkd
        obtain ⟨d1, d2⟩ := dec_parts_ov_of_zero (K := K) (merged := decide (0 < nd))
          hwf hcounts hzero hFlen hkd
        rw [fov]
        refine ⟨d1, ?_⟩
        rw [fp, fov, ite_eq_right (by omega)]
        exact d2
      have hUpper : L.length ≤ (live n.ks).length + (L.filter (isAdded (live n.ks))).length := hjoinUpper
      refine ⟨⟨n, _, L, _, hgkD, rfl, hdec, ?_, hUpper⟩,
        ⟨nd, by rw [fnd], ?_⟩, fup, fparts, ?_⟩
      · change (live n.ks).length ≤ L.length +
          ((kidsRs b s fs' g (live n.ks) ops).map (·.nd)).sum at hjoinLoss
        rw [fnd]
        simpa only [hnd] using hjoinLoss
      · have hc := dcost_le hdec
        have hcnt := sbNode_cnt b n isRoot K nd ci below
        simp only [vcost, vcostL_renameHead]
        change kw acc1 + (dcost (decideNode (Cfg.java b G H) i (some n) false L) + vcostL es2) +
          rootT b (sbNode b n isRoot K nd ci below) isRoot + 4 * nd ≤
          kw acc + (sbNode b n isRoot K nd ci below).cnt
        omega
      · intro hnd0 _
        rw [fci, ← hci]
        have hnd0' : nd ≠ 0 := by rw [fnd] at hnd0; exact hnd0
        rw [ite_eq_right hnd0']
        omega


/-- Mixed-operation plans against Java's count, with all leaf joins and
no joins of inner nodes, through every level and key segment. -/
theorem plan_tree_leafJoins {b G H : Nat} (hb : 8 ≤ b) (hks : KsOk b s) :
    ∀ F, PlanLeaves b (Cfg.java b G H) i s F ∧ TreeLeaves b (Cfg.java b G H) i s F := by
  intro F
  induction F using Nat.strong_induction_on with
  | _ F IH =>
    cases F with
    | zero =>
      refine ⟨?_, ?_⟩
      · intro x g h ops acc v acc' isRoot fs _ _ _ _ _ _ _ hp
        simp [plan] at hp
      · intro y g ops acc res acc' fs _ _ _ _ _ _ _ _ hp
        simp [planTree] at hp
    | succ F =>
      refine ⟨?_, tree_stepLeaves hb (IH F (by omega)).1⟩
      intro x g h ops acc v acc' isRoot fs hsh hgood hfill hops hne hfs hNo hp
      cases h with
      | zero =>
        exact leaf_stepLeaves hb (fun f hf => (IH f (by omega)).2) x g ops acc v acc' isRoot fs hsh
          hgood hfill hops hne hfs hNo hp
      | succ h =>
        exact inner_stepLeaves hb hks (fun f hf => (IH f (by omega)).1) x g h ops acc v acc' isRoot fs hsh
          hgood hfill hops hne hfs hNo hp

end Contract.PE
