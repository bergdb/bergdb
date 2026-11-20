/-
bergdb 030-36: mixed-operation plans in the no-join case. Empty child plans
are dropped and no retained changed child is small. Leaves may delete
entries or empty segment trees; roots may collapse.
-/
import Contract.Proof.DnbDelEntries

namespace Contract.PE

open DNB PeProof

variable {cf : Cfg} {i : Time} {s : Tree}

/-- **An inner node**, given plan at lower fuels. -/
theorem inner_stepD {b G H F : Nat} (hb : 8 ≤ b)
    (IHp : ∀ f < F, PlanPD b (Cfg.java b G H) i s f) :
    ∀ (x : NodeId) (g h : Nat) (ops : List Op) (acc : Acc) (v : VN) (acc' : Acc) (isRoot : Bool)
      (fs : Nat), Shaped (Cfg.java b G H) s g (h + 1) x → (∃ lo hi, Good s x lo hi) →
      Filled (Cfg.java b G H) s isRoot x → OpsD g ops → ops ≠ [] → s.fuel x ≤ fs → NoJoinsAt (Cfg.java b G H) i s fs x g ops →
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
  simp only [NoJoinsAt, hgkD, hleaf', Bool.false_eq_true, ↓reduceIte] at hNo
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
    have hout := kids_drop (fun c y o => OpsD g o ∧
      ((c, y), o) ∈ (live n.ks).zip (route (segAt g) (live n.ks) ops)) (F0 := F) (fs := fs') (lvAll := live n.ks)
      (fun f hf c y o acc0 w acc2 hmem hone hPP hp => by
        obtain ⟨hP, hpair⟩ := hPP
        have hn := hNoKids ((c, y), o) hpair hone
        obtain ⟨m, hm, hmlev, _⟩ := hkey c y hmem (by simp [hleaf'])
        have hgood' : ∃ lo hi, Good s y lo hi := by
          rcases good_kids hg hobj c y hmem with ⟨m', hm', _, lo', hi', hg'⟩ | ⟨v', hv'⟩
          · exact ⟨lo', hi', hg'⟩
          · rw [hm] at hv'; cases hv'
        have hfy : s.fuel y ≤ fs' := by simp [Tree.fuel, hm]; omega
        have hfill' := (filled_key hfill hobj).2.2.2 c y hmem hleaf'
        exact IHp f hf y g h o acc0 w acc2 false fs' (hkids c y hmem) hgood'
          hfill' hP hone hfy hn hp)
      (by simp [Cfg.java, DNB.minFill, show ¬ b < 8 from by omega])
      (fun c y hmem n' hgk' => by
        have hobj' : s.obj y = some (.key n') := by
          unfold DNB.getKey at hgk'; split at hgk' <;> simp_all
        exact (filled_key ((filled_key hfill hobj).2.2.2 c y hmem hleaf') hobj').2.1 (by simp [Cfg.java, DNB.minFill, show ¬ b < 8 from by omega]) rfl)
      (fun c y hmem => lookup_live hmem)
      (live n.ks) (route (segAt g) (live n.ks) ops) F acc es acc1 (fun _ h => h)
      (fun cy o ho => ⟨fun op hop => hops op
        ((route_sub (segAt g) (live n.ks) ops o (List.of_mem_zip ho).2).subset hop), ho⟩) le_rfl hk
    cases hrb : rebalance (Cfg.java b G H) i s (F + 1) g h es with
    | none => rw [hrb] at hpl; cases hpl
    | some es2 =>
      rw [hrb] at hpl
      simp only at hpl
      have hes2 : es2 = kept es := rebalance_filter_only (hNoHere F h acc es acc1 hsh hk) hrb
      subst hes2
      let E := entries (kept es)
      let L := renameHead 0 E
      have hEF : (renameHead 0 (kept es)).flatMap (fun e => ents e.1 e.2) = renameHead 0 E :=
        entries_renameHead 0 (kept es)
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
      have hA0 : (E.filter (isAdded (live n.ks))).length ≤
          ((kidsRs b s fs' g (live n.ks) ops).map (·.up)).sum := hout.added
      have hkw0 : kw acc1 + vcostL (kept es) +
          4 * ((kidsRs b s fs' g (live n.ks) ops).map (·.nd)).sum ≤
          kw acc + ((kidsRs b s fs' g (live n.ks) ops).map (·.cnt)).sum := hout.kw
      rw [hsb]
      generalize hnd : ((kidsRs b s fs' g (live n.ks) ops).map (·.nd)).sum = nd at hkw0 ⊢
      generalize hU : ((kidsRs b s fs' g (live n.ks) ops).map (·.up)).sum = U at hA0 ⊢
      let K := 4 * nd + U
      generalize ((kidsRs b s fs' g (live n.ks) ops).map (·.cnt)).sum = below at hkw0 ⊢
      generalize hci : (if nd = 0 then 0 else
          1 + List.foldl max 0 (List.map SR.ci (List.filter (fun r => decide (0 < r.nd))
            (kidsRs b s fs' g (live n.ks) ops)))) = ci
      change PlanSpecD b s g (h + 1) x isRoot _ acc acc1 (sbNode b n isRoot K nd ci below)
      obtain ⟨fnd, fci, fup, fparts, fov, fp⟩ := sbNode_factsD b n isRoot K nd ci below
      have hnd' : ((childRs b s fs' g (live n.ks) (route (segAt g) (live n.ks) ops)).map (·.nd)).sum = nd := hnd
      have hR0 : (removedCvs (live n.ks) E).length ≤ nd := by rw [← hnd']; exact hout.removed
      have hL0 : E.length ≤ (live n.ks).length + (E.filter (isAdded (live n.ks))).length := hout.len
      have hhead0 : nd = 0 → L = E := by
        intro hn
        apply renameHead_of_head
        rw [hout.head0 (by rw [hnd', hn]), hhead]
      have hcounts : (removedCvs (live n.ks) L).length +
          (L.filter (isAdded (live n.ks))).length ≤ K := by
        by_cases hn : nd = 0
        · rw [hhead0 hn]
          dsimp [K]
          omega
        · have hR := removed_renameHead_le (live_sorted n.ks) 0 E
          have hA := added_renameHead_le (lb := live n.ks) 0 E
          change (removedCvs (live n.ks) L).length ≤ (removedCvs (live n.ks) E).length + 1 at hR
          change (L.filter (isAdded (live n.ks))).length ≤ (E.filter (isAdded (live n.ks))).length + 1 at hA
          dsimp [K]
          omega
      have hFlen : L.length ≤ n.ks.length + K := by
        have hlvl := live_length_le n.ks
        have hLen : L.length = E.length := renameHead_length 0 E
        dsimp [K]
        omega
      have hzero : K = 0 → (live n.ks).map (fun q => (q.1, some q.2)) = L := by
        intro hz
        have hn : nd = 0 := by dsimp [K] at hz; omega
        rw [hhead0 hn]
        exact (hout.same0 (by rw [hnd', hn]) (by
          change (E.filter (isAdded (live n.ks))).length = 0
          dsimp [K] at hz; omega)).symm
      have hdec : ∀ k, decideNode (Cfg.java b G H) i (some n) false L = .parts k →
          0 < (sbNode b n isRoot K nd ci below).ov ∧ k ≤ (sbNode b n isRoot K nd ci below).parts := by
        intro k hkd
        obtain ⟨d1, d2⟩ := dec_parts_ov_of_zero (K := K) (merged := decide (0 < nd))
          hwf hcounts hzero hFlen hkd
        rw [fov]
        refine ⟨d1, ?_⟩
        rw [fp, fov, ite_eq_right (by omega)]
        exact d2
      have hUpper : L.length ≤ (live n.ks).length + (L.filter (isAdded (live n.ks))).length := by
        have hAge := added_renameHead_ge (lb := live n.ks) 0 E hout.own
        have hLen : L.length = E.length := renameHead_length 0 E
        change (E.filter (isAdded (live n.ks))).length ≤ (L.filter (isAdded (live n.ks))).length at hAge
        omega
      refine ⟨⟨n, _, L, _, hgkD, rfl, hdec, ?_, hUpper⟩,
        ⟨nd, by rw [fnd], ?_⟩, fup, fparts, ?_⟩
      · have hlen := hout.lost
        rw [hnd'] at hlen
        have hents := flatMap_ents_length_ge (kept es)
        have hLen : L.length = E.length := renameHead_length 0 E
        change (kept es).length ≤ E.length at hents
        rw [fnd]
        omega
      · have hc := dcost_le hdec
        have hcnt := sbNode_cnt b n isRoot K nd ci below
        simp only [vcost, vcostL_renameHead]
        change kw acc1 + (dcost (decideNode (Cfg.java b G H) i (some n) false L) + vcostL (kept es)) +
          rootT b (sbNode b n isRoot K nd ci below) isRoot + 4 * nd ≤
          kw acc + (sbNode b n isRoot K nd ci below).cnt
        omega
      · intro hnd0 _
        rw [fci, ← hci]
        have hnd0' : nd ≠ 0 := by rw [fnd] at hnd0; exact hnd0
        rw [ite_eq_right hnd0']
        omega

/-- Mixed-operation plans against Java's count when no child underflows. -/
theorem plan_tree_noJoins {b G H : Nat} (hb : 8 ≤ b) :
    ∀ F, PlanPD b (Cfg.java b G H) i s F ∧ TreePPD b (Cfg.java b G H) i s F := by
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
      refine ⟨?_, tree_stepD hb (IH F (by omega)).1⟩
      intro x g h ops acc v acc' isRoot fs hsh hgood hfill hops hne hfs hNo hp
      cases h with
      | zero =>
        exact leaf_stepD hb (fun f hf => (IH f (by omega)).2) x g ops acc v acc' isRoot fs hsh
          hgood hfill hops hne hfs hNo hp
      | succ h =>
        exact inner_stepD hb (fun f hf => (IH f (by omega)).1) x g h ops acc v acc' isRoot fs hsh
          hgood hfill hops hne hfs hNo hp

end Contract.PE
