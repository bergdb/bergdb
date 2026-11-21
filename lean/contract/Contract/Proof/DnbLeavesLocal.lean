/-
bergdb 030-37: leaves and segment roots in the induction with arbitrary
leaf joins. These use the mixed-operation counts and root-collapse
arguments of 030-36, with the recursive calls under `NoInnerJoinsAt`.
-/
import Contract.Proof.DnbLeavesDefs

namespace Contract.PE

open DNB PeProof

variable {i : Time} {s : Tree}

theorem leaf_stepLeaves {b G H F : Nat} (hb : 8 ≤ b)
    (IHt : ∀ f < F, TreeLeaves b (Cfg.java b G H) i s f) :
    ∀ (x : NodeId) (g : Nat) (ops : List Op) (acc : Acc) (v : VN) (acc' : Acc) (isRoot : Bool)
      (fs : Nat), Shaped (Cfg.java b G H) s g 0 x → (∃ lo hi, Good s x lo hi) →
      Filled (Cfg.java b G H) s isRoot x → OpsD g ops → ops ≠ [] → s.fuel x ≤ fs → NoInnerJoinsAt (Cfg.java b G H) i s fs x g ops →
      plan (Cfg.java b G H) i s (F + 1) x g 0 ops acc = some (v, acc') →
      PlanSpecD b s g 0 x isRoot v acc acc' (sbPlan b s fs x g ops isRoot) := by
  intro x g ops acc v acc' isRoot fs hsh hgood hfill hops hne hfs hNo hpl
  obtain ⟨n, hobj, hgk, hlev, hleaf, _, _⟩ := shaped_getKey hsh
  have hgkD : DNB.getKey s x = some n := hgk
  simp only [beq_self_eq_true] at hleaf
  obtain ⟨lo, hi, hg⟩ := hgood
  obtain ⟨hwf, hkey⟩ := good_key hg hobj
  have hfuel : s.fuel x = n.level + 1 := by simp [Tree.fuel, hobj]
  obtain ⟨fs', rfl⟩ : ∃ fs', fs = fs' + 1 := ⟨fs - 1, by omega⟩
  simp only [NoInnerJoinsAt, hgkD, hleaf, ↓reduceIte] at hNo
  have hend : ∀ op ∈ ops, endsAt g op = !isLong (segAt g op) :=
    fun op hop => endsAt_isLong (hops op hop).1 (hops op hop).2
  set lv := live n.ks with hlv
  set child : NodeId → List Op → SR := fun y subs => sbPlan b s fs' y (g + 1) subs true
  set SG := fun cv => sbGroup b g lv (grpOf g ops cv) child cv with hSG
  -- plan's leaf
  rw [plan.eq_def] at hpl
  simp only at hpl
  rw [hgk] at hpl
  simp only [beq_self_eq_true, ↓reduceIte] at hpl
  cases hag : applyGroups (Cfg.java b G H) i s F g lv (List.map (segAt g) ops).eraseDups ops acc with
  | none => rw [hag] at hpl; cases hpl
  | some q =>
    obtain ⟨es, acc1⟩ := q
    rw [hag] at hpl
    simp only at hpl
    unfold mkNode at hpl
    simp only [beq_self_eq_true, ↓reduceIte] at hpl
    rw [hgk] at hpl
    simp only [Option.some.injEq, Prod.mk.injEq] at hpl
    obtain ⟨rfl, rfl⟩ := hpl
    rw [flatMap_ents_old]
    -- the groups
    set Q : Nat → Option NodeId → Prop := fun cv res =>
      (lv.lookup cv ≠ res → 1 ≤ 4 * (SG cv).2.2 + (SG cv).1) ∧
      (res = none → lv.lookup cv ≠ none → 1 ≤ (SG cv).2.2) with hQ
    have hT : ∀ f, f < F → ∀ cv acc0 res acc1', subsOf g ops cv ≠ [] →
        planTree (Cfg.java b G H) i s f (lv.lookup cv) (g + 1) (subsOf g ops cv) acc0 =
          some (res, acc1') →
        kw acc1' ≤ kw acc0 + (SG cv).2.1 ∧ Q cv res := by
      intro f hf cv acc0 res acc1' hsne hpt
      simp only [hQ, hSG]
      have hSGs := sbGroup_sub (b := b) (lv := lv) (cv := cv) (child := child) hend hsne
      obtain ⟨op, hop⟩ := List.exists_mem_of_ne_nil _ hsne
      have hop' := hop
      unfold subsOf grpOf at hop'
      simp only [List.mem_filter, beq_iff_eq, Bool.not_eq_eq_eq_not, Bool.not_true] at hop'
      have hlong : isLong cv = true := by
        have := hend op hop'.1.1
        rw [hop'.2, hop'.1.2] at this
        simpa using this.symm
      have hsops : ∀ o ∈ subsOf g ops cv, keyWf o.key = true ∧ g + 1 < o.key.length := by
        intro o ho
        have ho' := ho
        unfold subsOf grpOf at ho'
        simp only [List.mem_filter, beq_iff_eq, Bool.not_eq_eq_eq_not, Bool.not_true] at ho'
        obtain ⟨h1, h2⟩ := hops o ho'.1.1
        refine ⟨h1, ?_⟩
        have := ho'.2; simp only [endsAt, beq_eq_false_iff_ne] at this; omega
      cases hl : lv.lookup cv with
      | some y =>
        rw [hl] at hpt hSGs
        simp only at hSGs
        have hmem : (cv, y) ∈ lv := lookup_mem hl
        obtain ⟨m, hm, hmlev, hmne⟩ := hkey cv y hmem (fun _ => hlong)
        have hsh' := shaped_kid_leaf hsh hobj (by simpa using hleaf) hmem hlong
        have hgood' : ∃ lo hi, Good s y lo hi := by
          rcases good_kids hg hobj cv y hmem with ⟨m', hm', _, lo', hi', hg'⟩ | ⟨v', hv'⟩
          · exact ⟨lo', hi', hg'⟩
          · rw [hm] at hv'; cases hv'
        have hfill' := (filled_key hfill hobj).2.2.1 cv y hmem (by simpa using hleaf) hlong
        have hfy : s.fuel y ≤ fs' := by simp [Tree.fuel, hm]; omega
        have hlive : ∀ n', DNB.getKey s y = some n' → live n'.ks ≠ [] := by
          intro n' hn'
          have : n' = m := by
            unfold DNB.getKey at hn'; rw [hm] at hn'; simpa using hn'.symm
          rw [this]; exact hmne
        have ht := IHt f hf y (g + 1) _ acc0 res acc1' fs' hsh' hgood' hfill' hlive hsops
          hsne hfy (by
            have hcv : cv ∈ touched g ops := mem_touched.mpr ⟨op, hop'.1.1, hop'.1.2⟩
            have hn := hNo cv hcv
            change (match lv.lookup cv with
              | none => True
              | some y => subsOf g ops cv ≠ [] →
                NoInnerJoinsAt (Cfg.java b G H) i s fs' y (g + 1) (subsOf g ops cv)) at hn
            rw [hl] at hn
            exact hn hsne) hpt
        change TreePD y res acc0 acc1' (child y (subsOf g ops cv)) at ht
        obtain ⟨t1, t2, t3⟩ := ht
        rw [hSGs]
        dsimp only
        refine ⟨t1, fun hne' => ?_, fun hn _ => ?_⟩
        · cases res with
          | none => have := t2 rfl; omega
          | some y' =>
            rcases t3 y' rfl with rfl | h1
            · exact absurd rfl hne'
            · omega
        · have := t2 hn; omega
      | none =>
        rw [hl] at hpt hSGs
        simp only at hSGs
        obtain ⟨t1, t2⟩ := fresh_le_del_ftb (i := i) (s := s) (G := G) (H := H) hb hsops hpt
        rw [hSGs]
        cases hP : ((subsOf g ops cv).filter (fun op => !opDel op)).isEmpty
        · simp only [hP, Bool.false_eq_true, ↓reduceIte] at t1 ⊢
          exact ⟨t1, fun _ => le_refl _, fun _ hn => absurd rfl hn⟩
        · simp only [hP, ↓reduceIte] at t1 t2 ⊢
          refine ⟨by omega, fun hne' => ?_, fun _ hn => absurd rfl hn⟩
          cases res with
          | none => exact absurd rfl hne'
          | some y' => have := t2 (by simp); cases this
    obtain ⟨a1, a2, a3, a4⟩ := agl_loop (cf := Cfg.java b G H) (i := i) (s := s) (lb := lv) hend
      (fun cv => (SG cv).2.1) Q F hT (touched g ops) F lv acc es acc1 le_rfl (nodup_touched g ops)
      (fun _ _ => rfl) (live_sorted n.ks) hag
    -- each compare value
    have hon : ∀ cv ∈ touched g ops,
        (es.lookup cv ≠ lv.lookup cv → 1 ≤ 4 * (SG cv).2.2 + (SG cv).1) ∧
        (es.lookup cv = none → lv.lookup cv ≠ none → 1 ≤ (SG cv).2.2) := by
      intro cv hcv
      rcases a4 cv hcv with ⟨hs, hch⟩ | ⟨_, hq⟩
      · have hSGe := sbGroup_end (b := b) (lv := lv) (child := child) hs
        have hdel : ∀ op ∈ grpOf g ops cv, opDel op = true →
            1 ≤ ((grpOf g ops cv).filter opDel).length :=
          fun op hop hp => List.length_pos_of_mem (List.mem_filter.mpr ⟨hop, hp⟩)
        have hput : ∀ op ∈ grpOf g ops cv, opDel op = false →
            1 ≤ ((grpOf g ops cv).filter (fun op => !opDel op)).length :=
          fun op hop hp => List.length_pos_of_mem (List.mem_filter.mpr ⟨hop, by simp [hp]⟩)
        simp only [SG, hSGe]
        refine ⟨fun hne' => ?_, fun hn hl => ?_⟩
        · obtain ⟨hA, hB⟩ := hch hne'
          by_cases hn : es.lookup cv = none
          · obtain ⟨op, hop, hp⟩ := hB hn
            have := hdel op hop hp; omega
          · obtain ⟨op, hop, hp⟩ := hA hn
            have := hput op hop hp; omega
        · have hne' : es.lookup cv ≠ lv.lookup cv := by rw [hn]; exact fun h => hl h.symm
          obtain ⟨op, hop, hp⟩ := (hch hne').2 hn
          exact hdel op hop hp
      · obtain ⟨q1, q2⟩ := hq
        exact ⟨fun h => q1 (fun h' => h h'.symm), q2⟩
    obtain ⟨l1, l2, l3⟩ := leaf_countsD (fun cv => 4 * (SG cv).2.2 + (SG cv).1) (live_sorted n.ks) a2
      a3 (fun cv hcv => (hon cv hcv).1)
    -- Java's count of the leaf
    have hsb : sbPlan b s (fs' + 1) x g ops isRoot = sbNode b n isRoot
        (4 * ((touched g ops).map (fun cv => (SG cv).2.2)).sum +
          ((touched g ops).map (fun cv => (SG cv).1)).sum)
        ((touched g ops).map (fun cv => (SG cv).2.2)).sum 0
        ((touched g ops).map (fun cv => (SG cv).2.1)).sum := by
      rw [sbPlan.eq_def]
      simp only [hgkD, hleaf, ↓reduceIte, List.map_map]
      rfl
    rw [sum_map_four_add] at l1
    rw [hsb]
    set nd := ((touched g ops).map (fun cv => (SG cv).2.2)).sum with hnd
    set K := 4 * nd + ((touched g ops).map (fun cv => (SG cv).1)).sum with hK
    set below := ((touched g ops).map (fun cv => (SG cv).2.1)).sum with hbelow
    obtain ⟨f1, f2, f3, f4, f5, f6⟩ := sbNode_factsD b n isRoot K nd 0 below
    have hlvl : (live n.ks).length ≤ n.ks.length := live_length_le n.ks
    have hdec : ∀ k, decideNode (Cfg.java b G H) i (some n) false (es.map (fun e => (e.1, some e.2))) =
        .parts k → 0 < (sbNode b n isRoot K nd 0 below).ov ∧
          k ≤ (sbNode b n isRoot K nd 0 below).parts := by
      intro k hk
      obtain ⟨d1, d2⟩ := dec_parts_ov (F := es.map (fun e => (e.1, some e.2))) (K := K)
        (merged := decide (0 < nd)) hwf (by omega) l3 (by omega) hk
      rw [f5]
      refine ⟨d1, ?_⟩
      rw [f6, f5, ite_eq_right (by omega)]
      exact d2
    have hbel : kw acc1 ≤ kw acc + below := by
      refine le_trans a1 (Nat.add_le_add_left (sum_map_le_pointwise (fun cv _ => ?_)) _)
      split
      · exact Nat.zero_le _
      · exact le_refl _
    refine ⟨⟨n, _, _, _, hgkD, rfl, hdec, ?_, by simpa using l2⟩,
      ⟨nd, le_refl _, ?_⟩, f3, f4, fun _ h0 => absurd rfl h0⟩
    · -- each live entry lost has a delete
      rw [f1, List.length_map]
      change lv.length ≤ es.length + nd
      have hA : (lv.filter (fun q => (es.lookup q.1).isSome)).length ≤ es.length := by
        apply len_le_of_lookup ((live_sorted n.ks).filter _)
        intro q hq
        rw [List.mem_filter] at hq
        exact Option.isSome_iff_exists.mp hq.2
      have hB : (lv.filter (fun q => !(es.lookup q.1).isSome)).length ≤ nd := by
        have hnd1 : ((lv.filter (fun q => !(es.lookup q.1).isSome)).map (·.1)).Nodup := by
          rw [List.Nodup, List.pairwise_map]
          exact ((live_sorted n.ks).filter _).imp (fun h => Nat.ne_of_lt h)
        have hsub : (lv.filter (fun q => !(es.lookup q.1).isSome)).map (·.1) ⊆
            (touched g ops).filter (fun cv => decide (1 ≤ (SG cv).2.2)) := by
          intro c hc
          rw [List.mem_map] at hc
          obtain ⟨q, hq, rfl⟩ := hc
          rw [List.mem_filter] at hq
          have hy : es.lookup q.1 = none := by simpa using hq.2
          have hct : q.1 ∈ touched g ops := by
            by_contra hn
            rw [a3 q.1 hn, lookup_live hq.1] at hy; cases hy
          refine List.mem_filter.mpr ⟨hct, ?_⟩
          have := (hon q.1 hct).2 hy (by rw [lookup_live hq.1]; simp)
          simpa using this
        have h1 := (List.subperm_of_subset hnd1 hsub).length_le
        rw [List.length_map] at h1
        have h2 := filter_len_le_sum (fun cv => decide (1 ≤ (SG cv).2.2)) (fun cv => (SG cv).2.2)
          (touched g ops) (fun c _ hp => by simpa using hp)
        change (lv.filter (fun q => !(es.lookup q.1).isSome)).length ≤
          ((touched g ops).map (fun cv => (SG cv).2.2)).sum
        exact le_trans h1 h2
      have hsplit : lv.length = (lv.filter (fun q => (es.lookup q.1).isSome)).length +
          (lv.filter (fun q => !(es.lookup q.1).isSome)).length :=
        List.length_eq_length_filter_add _
      omega
    · have hc := dcost_le hdec
      have hcnt := sbNode_cnt b n isRoot K nd 0 below
      simp only [vcost, vcostL_old, add_zero]
      omega


theorem tree_stepLeaves {b G H F : Nat} (hb : 8 ≤ b) (IH : PlanLeaves b (Cfg.java b G H) i s F) :
    TreeLeaves b (Cfg.java b G H) i s (F + 1) := by
  intro y g ops acc res acc' fs hsh hgood hfill hlive hops hne hfs hNo hpt
  obtain ⟨n, hobj, hgk, hlev, hleaf, _, _⟩ := shaped_getKey hsh
  have hgkD : DNB.getKey s y = some n := hgk
  rw [planTree.eq_def] at hpt
  simp only at hpt
  rw [hgk] at hpt
  simp only at hpt
  rw [show (Cfg.java b G H).htOf n.level = htIn (Cfg.java b G H) s y by simp [htIn, hobj]] at hpt
  cases hpl : plan (Cfg.java b G H) i s F y g (htIn (Cfg.java b G H) s y) ops acc with
  | none => rw [hpl] at hpt; cases hpt
  | some q =>
    obtain ⟨v, acc1⟩ := q
    rw [hpl] at hpt
    simp only at hpt
    have hp := IH y g _ ops acc v acc1 true fs hsh hgood hfill hops hne hfs hNo hpl
    obtain ⟨lo, hi, hg⟩ := hgood
    obtain ⟨_, _, _, hvok⟩ := plan_inst (cfgOk_java8 hb) hpl hsh hg
    obtain ⟨n', es, Fl, dec, hgk', rfl, hdec, hlen, _⟩ := hp.shape
    rw [hgkD] at hgk'
    obtain rfl : n = n' := by injection hgk'
    obtain ⟨T, hTn, hkw⟩ := hp.kw
    have hlne := hlive n hgkD
    have hlne' : 1 ≤ (live n.ks).length := by
      cases h0 : live n.ks with
      | nil => exact absurd h0 hlne
      | cons _ _ => simp
    by_cases hFe : Fl = []
    · -- the root emptied: a delete passes it
      subst hFe
      obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := by
        cases F with
        | zero => simp [settleRoot] at hpt
        | succ F' => exact ⟨F', rfl⟩
      rw [settleRoot.eq_def] at hpt
      simp at hpt
      obtain ⟨rfl, rfl⟩ := hpt
      refine ⟨by omega, fun _ => ?_, fun _ h => by cases h⟩
      by_contra h0
      simp only [List.length_nil] at hlen
      omega
    · by_cases hcol : htIn (Cfg.java b G H) s y ≠ 0 ∧ Fl.length = 1
      · -- a collapse: a delete passes the root, and the leaf above gets a klong
        have hleaf' : n.leaf = false := by rw [hleaf]; simpa using hcol.1
        have h2 := (filled_key hfill hobj).1 hleaf' rfl
        have hnd : (sbPlan b s fs y g ops true).nd ≠ 0 := fun h0 => by
          rw [h0] at hlen; omega
        have hci := hp.ci hnd hcol.1
        have hup : 1 ≤ (sbPlan b s fs y g ops true).up := by
          rw [hp.up]
          simp only [true_and]
          rw [ite_eq_left (by omega)]
          omega
        split at hpt
        · cases hpt
        · simp only [Option.some.injEq, Prod.mk.injEq] at hpt
          obtain ⟨rfl, rfl⟩ := hpt
          exact ⟨by omega, fun _ => by omega, fun _ h => by cases h⟩
        · rename_i v1 hset
          have hv1 := settle_one F _ _ v1 (Or.inr ⟨hvok, by simpa [VN.isEmpty] using hFe⟩)
            (one_of_dec hvok (by omega)) hset
          split at hpt
          · rename_i c y' acc2 hem
            simp only [Option.some.injEq, Prod.mk.injEq] at hpt
            obtain ⟨rfl, rfl⟩ := hpt
            have hkw2 := emit_kw v1 acc1 _ acc2 hem
            exact ⟨by omega, fun h => (by cases h), fun _ _ => Or.inr hup⟩
          · cases hpt
      · -- settled as for puts
        have hF1 : htIn (Cfg.java b G H) s y ≠ 0 → Fl.length ≠ 1 := fun h0 h1 => hcol ⟨h0, h1⟩
        split at hpt
        · cases hpt
        · rename_i hset
          obtain ⟨v', hv, _⟩ := settle_chain (i := i) (s := s) hb F (some y) _ false es Fl dec _ hFe
            hF1 hset
          cases hv
        · rename_i v1 hset
          obtain ⟨v', hv, hv', hsame⟩ := settle_chain (i := i) (s := s) hb F (some y) _ false es Fl dec _
            hFe hF1 hset
          cases hv
          split at hpt
          · rename_i c y' acc2 hem
            simp only [Option.some.injEq, Prod.mk.injEq] at hpt
            obtain ⟨rfl, rfl⟩ := hpt
            have hkw2 := emit_kw v1 acc1 _ acc2 hem
            have hra := raOf_le_rootT hb hdec
            refine ⟨by omega, fun h => (by cases h), fun y'' hy'' => ?_⟩
            cases hy''
            by_cases hov : (sbPlan b s fs y g ops true).ov = 0
            · left
              have hnp : ∀ k, dec ≠ .parts k := by
                intro k hk'; have := (hdec k hk').1; omega
              rw [hsame (fun k _ => hnp k)] at hem
              have := emit_base hnp hem
              simp only [List.cons.injEq, Prod.mk.injEq, and_true] at this
              exact this.2
            · right
              rw [hp.up]
              simp only [hov, ↓reduceIte]
              omega
          · cases hpt

end Contract.PE
